// Monomorphic wrappers for the covered generic functions of a project.
//
// `--emit-lean` leaves generic functions out (the IR is monomorphic and a partial program has no
// call sites that fix the type arguments). For every covered, exported, generic top-level
// function of a coverage report, this writes a one-line wrapper that calls it at one instance
// (each type parameter := number; `extends PropertyKey` := string; `extends string|number` := the
// same; other constraints are skipped), one wrapper per file (a file with a TypeScript error
// would hide the others), and a tsconfig.json that extends the project's. The coverage run on
// that tsconfig emits the wrappers together with the instances they call.
//
// With --callbacks, the wrappers are written instead for the covered functions (generic or not)
// that take a callback: each parameter of function type is replaced by one fixed pure function
// of that type (a number or string predicate `x > 0` / `x !== ''`, the identity on numbers,
// `String(x)` from numbers to strings, a constant otherwise), so that the proof attempt is about
// the function's own loop rather than an arbitrary callback (cb_<name>).
//
//   node tools/public/mono.js PROJECT_DIR REPORT.json OUTDIR [--callbacks]
'use strict';
const path = require('path');
const fs = require('fs');
const ts = require(path.join(__dirname, '..', '..', 'frontend', 'node_modules', 'typescript'));

const argv = process.argv.slice(2);
const callbacks = argv.includes('--callbacks');
const [projectDir, reportPath, outDir] = argv.filter(a => a !== '--callbacks').map(p => path.resolve(p));
const cfgPath = path.join(projectDir, 'tsconfig.strictts.json');
const cfg = ts.getParsedCommandLineOfConfigFile(cfgPath, {}, { ...ts.sys, onUnRecoverableConfigFileDiagnostic: d => { throw new Error(String(d.messageText)); } });
const keepExt = !!cfg.options.allowImportingTsExtensions;
const report = JSON.parse(fs.readFileSync(reportPath, 'utf8'));
const instOf = c => {
  if (!c) return 'number';
  const t = c.getText().replace(/\s+/g, ' ');
  return { PropertyKey: 'string', string: 'string', number: 'number' }[t];
};
fs.mkdirSync(outDir, { recursive: true });
const skipped = {};
const skip = (why) => { skipped[why] = (skipped[why] ?? 0) + 1; };
const used = new Set();
let written = 0;
const files = new Map();
for (const r of report.rows) {
  if (r.status !== 'covered' || (r.kind !== 'function' && r.kind !== 'arrow')) continue;
  const file = path.join(projectDir, r.file);
  let sf = files.get(file);
  if (!sf) { sf = ts.createSourceFile(file, fs.readFileSync(file, 'utf8'), ts.ScriptTarget.Latest, true); files.set(file, sf); }
  const lineOf = n => sf.getLineAndCharacterOfPosition(n.getStart(sf)).line + 1;
  // the declaration (top-level function, or the arrow / function expression of `const f = …`) and
  // the statement whose modifiers say whether it is exported
  let decl, stmt;
  for (const s of sf.statements) {
    if (r.kind === 'function' && ts.isFunctionDeclaration(s) && s.body && s.name?.text === r.name && lineOf(s) === r.line) { decl = s; stmt = s; }
    if (r.kind === 'arrow' && ts.isVariableStatement(s)) {
      for (const d of s.declarationList.declarations) {
        let init = d.initializer;
        while (init && (ts.isParenthesizedExpression(init) || ts.isAsExpression(init) || ts.isSatisfiesExpression(init))) init = init.expression;
        if (ts.isIdentifier(d.name) && d.name.text === r.name && init && (ts.isArrowFunction(init) || ts.isFunctionExpression(init)) && lineOf(init) === r.line) { decl = init; stmt = s; }
      }
    }
  }
  if (!decl) { skip('declaration not found'); continue; }
  const unwrapType = t => { while (t && ts.isParenthesizedTypeNode(t)) t = t.type; return t; };
  const fnParams = decl.parameters.filter(p => p.type && ts.isFunctionTypeNode(unwrapType(p.type)));
  if (callbacks ? !fnParams.length : !decl.typeParameters?.length) continue;   // (else emitted by the coverage run itself)
  if (!ts.getModifiers(stmt)?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) { skip('not exported'); continue; }
  if (ts.getModifiers(stmt)?.some(m => m.kind === ts.SyntaxKind.DefaultKeyword)) { skip('default export'); continue; }
  const sub = new Map();
  let ok = true;
  for (const tp of decl.typeParameters ?? []) {
    const t = instOf(tp.constraint);
    if (!t) { ok = false; break; }
    sub.set(tp.name.text, t);
  }
  if (!ok) { skip('constrained type parameter'); continue; }
  const inst = (n) => {
    let s = n.getText(sf);
    for (const [k, v] of sub) s = s.replace(new RegExp(`\\b${k}\\b`, 'g'), v);
    return s;
  };
  // one fixed pure function of a callback type, or undefined
  const pureFn = (ft) => {
    const ret = inst(ft.type).trim();
    const p0 = ft.parameters[0]?.type ? inst(ft.parameters[0].type).trim() : undefined;
    const body = ret === 'boolean' ? (p0 === 'number' ? 'a0 > 0' : p0 === 'string' ? "a0 !== ''" : 'true') :
      ret === 'number' ? (p0 === 'number' ? 'a0' : '0') :
      ret === 'string' ? (p0 === 'number' ? 'String(a0)' : p0 === 'string' ? 'a0' : "''") :
      ret === 'unknown' ? (p0 ? 'a0' : 'undefined') :
      ret === 'void' || ret === 'undefined' ? 'undefined' : ret === 'bigint' ? '0n' : undefined;
    if (body === undefined) return undefined;
    return body.includes('a0') ? `(a0: ${p0}) => ${body}` : `() => ${body}`;
  };
  const params = [], argNames = [];
  for (const p of decl.parameters) {
    if (!ts.isIdentifier(p.name) || p.name.text === 'this' || p.dotDotDotToken || !p.type) { ok = false; break; }
    if (callbacks && fnParams.includes(p)) {
      const f = pureFn(unwrapType(p.type));
      if (!f) { ok = false; break; }
      argNames.push(f);
      continue;
    }
    params.push(`${p.name.text}${p.questionToken || p.initializer ? '?' : ''}: ${inst(p.type)}`);
    argNames.push(p.name.text);
  }
  if (!ok) { skip('parameter without a plain annotated name (rest, destructuring, this, no type), or a callback type without a fixed function'); continue; }
  const prefix = callbacks ? 'cb' : 'mono';
  let wname = `${prefix}_${r.name}`;
  for (let k = 2; used.has(wname); k++) wname = `${prefix}_${r.name}_${k}`;
  used.add(wname);
  let rel = path.relative(outDir, file).split(path.sep).join('/');
  if (!rel.startsWith('.')) rel = './' + rel;
  if (!keepExt) rel = rel.replace(/\.ts$/, '');
  const targs = (decl.typeParameters ?? []).map(tp => sub.get(tp.name.text)).join(', ');
  const ret = decl.type ? `: ${inst(decl.type)}` : '';
  const text = `// wrapper of ${r.file}:${r.line} ${r.name} at <${targs}>\nimport { ${r.name} as target } from '${rel}';\n\n` +
    `export function ${wname}(${params.join(', ')})${ret} {\n  return target${targs ? `<${targs}>` : ''}(${argNames.join(', ')});\n}\n`;
  fs.writeFileSync(path.join(outDir, `${wname}.ts`), text);
  written++;
}
const relCfg = path.relative(outDir, cfgPath).split(path.sep).join('/');
fs.writeFileSync(path.join(outDir, 'tsconfig.json'), JSON.stringify({ extends: relCfg, include: ['*.ts'], exclude: [] }, null, 2) + '\n');
console.log(`${written} wrappers in ${outDir}; skipped: ${JSON.stringify(skipped)}`);

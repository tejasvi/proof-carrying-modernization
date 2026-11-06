// Node side of the NoPanic counterexample check: an instrumented transpilation of a project.
//
//   node tools/public/node/build.js TSCONFIG OUTDIR ROOTDIR
//
// Emits every source file of the program as CommonJS into OUTDIR (paths relative to ROOTDIR),
// with checks that throw a type violation when a value reaches a place whose TypeScript type
// excludes it:
//   * a read `a[i]` whose type excludes undefined (or is a type parameter: the functions are run
//     at instances such as T := number) out of bounds (arrays, typed arrays, strings) or at a
//     missing key (dictionaries);
//   * `x!` on undefined or null;
//   * a read of a declared class field whose type excludes undefined (an uninitialised field).
// Each module also exports its top-level declarations as `__strictts` (so that functions that the
// project does not export can be called). OUTDIR/index.json lists, per file, the top-level
// functions, arrows, classes and their members with parameter names and types, for matching the
// emitted Lean functions. Nothing of the project is run here.
'use strict';
const path = require('path');
const fs = require('fs');
const ts = require(path.join(__dirname, '..', '..', '..', 'frontend', 'node_modules', 'typescript'));

const [cfgPath, outDir, rootDir] = process.argv.slice(2).map(p => path.resolve(p));
const cfg = ts.getParsedCommandLineOfConfigFile(cfgPath, {}, {
  ...ts.sys, onUnRecoverableConfigFileDiagnostic: d => { throw new Error(ts.flattenDiagnosticMessageText(d.messageText, ' ')); },
});
const options = {
  ...cfg.options, module: ts.ModuleKind.CommonJS, moduleResolution: ts.ModuleResolutionKind.Node10,
  target: ts.ScriptTarget.ES2022, noEmit: false, emitDeclarationOnly: false, declaration: false,
  declarationMap: false, sourceMap: false, composite: false, incremental: false, noEmitOnError: false,
  rewriteRelativeImportExtensions: true, esModuleInterop: true, skipLibCheck: true, outDir, rootDir,
};
delete options.tsBuildInfoFile;
delete options.outFile;
const program = ts.createProgram(cfg.fileNames, options);
const checker = program.getTypeChecker();
const own = program.getSourceFiles().filter(sf => !sf.isDeclarationFile && !sf.fileName.includes('/node_modules/'));

const BAD = ts.TypeFlags.Undefined | ts.TypeFlags.Void | ts.TypeFlags.Any | ts.TypeFlags.Unknown | ts.TypeFlags.Null;
function excludesUndefined(node, typeParamsToo = false) {
  const t = checker.getTypeAtLocation(node);
  const parts = t.isUnion() ? t.types : [t];
  return !parts.some(p => (p.flags & BAD) || (!typeParamsToo && (p.flags & ts.TypeFlags.TypeParameter)));
}
const ASSIGN = new Set([ts.SyntaxKind.EqualsToken, ts.SyntaxKind.PlusEqualsToken, ts.SyntaxKind.MinusEqualsToken,
  ts.SyntaxKind.AsteriskEqualsToken, ts.SyntaxKind.SlashEqualsToken, ts.SyntaxKind.PercentEqualsToken,
  ts.SyntaxKind.AsteriskAsteriskEqualsToken, ts.SyntaxKind.LessThanLessThanEqualsToken,
  ts.SyntaxKind.GreaterThanGreaterThanEqualsToken, ts.SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken,
  ts.SyntaxKind.AmpersandEqualsToken, ts.SyntaxKind.BarEqualsToken, ts.SyntaxKind.CaretEqualsToken,
  ts.SyntaxKind.AmpersandAmpersandEqualsToken, ts.SyntaxKind.BarBarEqualsToken, ts.SyntaxKind.QuestionQuestionEqualsToken]);
/** Is `n` written (an assignment target, also inside a destructuring pattern), deleted, or called? */
function notARead(n) {
  let c = n, p = n.parent;
  while (p && (ts.isParenthesizedExpression(p) || ts.isArrayLiteralExpression(p) || ts.isObjectLiteralExpression(p)
      || ts.isPropertyAssignment(p) || ts.isShorthandPropertyAssignment(p) || ts.isSpreadElement(p) || ts.isSpreadAssignment(p))) {
    if (ts.isBinaryExpression(p.parent) && p.parent.left === p && p.parent.operatorToken.kind === ts.SyntaxKind.EqualsToken) return true;
    c = p; p = p.parent;
  }
  if (!p) return false;
  if (ts.isBinaryExpression(p) && p.left === c && ASSIGN.has(p.operatorToken.kind)) return true;
  if ((ts.isPrefixUnaryExpression(p) || ts.isPostfixUnaryExpression(p))
      && (p.operator === ts.SyntaxKind.PlusPlusToken || p.operator === ts.SyntaxKind.MinusMinusToken)) return true;
  if (ts.isDeleteExpression(p) || ts.isTypeOfExpression(p)) return true;
  if (ts.isCallExpression(p) && p.expression === c) return true;
  if ((ts.isForOfStatement(p) || ts.isForInStatement(p)) && p.initializer === c) return true;
  return false;
}
function isClassField(n) {
  const sym = checker.getSymbolAtLocation(n.name);
  const d = sym && sym.valueDeclaration;
  return !!d && (ts.isPropertyDeclaration(d) || (ts.isParameter(d) && ts.isConstructorDeclaration(d.parent)));
}

function instrument(sf) {
  return (ctx) => (root) => {
    const f = ctx.factory;
    const where = (n) => {
      const p = sf.getLineAndCharacterOfPosition(n.getStart(sf));
      return `${path.relative(rootDir, sf.fileName)}:${p.line + 1}:${p.character + 1} ${n.getText(sf).replace(/\s+/g, ' ').slice(0, 80)}`;
    };
    const check = (fn, inner, n) => f.createCallExpression(f.createIdentifier(fn), undefined, [inner, f.createStringLiteral(where(n))]);
    const visit = (n) => {
      if (ts.isElementAccessExpression(n) && !n.questionDotToken && !notARead(n) && excludesUndefined(n, true)) {
        return f.createCallExpression(f.createIdentifier('__strictts_ix'), undefined,
          [ts.visitNode(n.expression, visit), ts.visitNode(n.argumentExpression, visit), f.createStringLiteral(where(n))]);
      }
      if (ts.isNonNullExpression(n) && !notARead(n)) {
        return check('__strictts_nn', ts.visitNode(n.expression, visit), n);
      }
      if (ts.isPropertyAccessExpression(n) && !n.questionDotToken && !notARead(n) && isClassField(n) && excludesUndefined(n)) {
        return check('__strictts_ck', ts.visitEachChild(n, visit, ctx), n);
      }
      return ts.visitEachChild(n, visit, ctx);
    };
    const body = ts.visitEachChild(root, visit, ctx);
    // the top-level declarations, exported for the harness
    const names = [];
    for (const st of root.statements) {
      if ((ts.isFunctionDeclaration(st) || ts.isClassDeclaration(st)) && st.name) names.push(st.name.text);
      if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name)) names.push(d.name.text);
    }
    const prologue = ['__strictts_ck', '__strictts_nn', '__strictts_ix'].map(k => f.createVariableStatement(undefined,
      f.createVariableDeclarationList([f.createVariableDeclaration(k, undefined, undefined,
        f.createPropertyAccessExpression(f.createIdentifier('globalThis'), k))], ts.NodeFlags.Const)));
    const exp = f.createExpressionStatement(f.createAssignment(
      f.createPropertyAccessExpression(f.createIdentifier('exports'), '__strictts'),
      f.createObjectLiteralExpression(names.map(n => f.createShorthandPropertyAssignment(n)))));
    return f.updateSourceFile(body, [...prologue, ...body.statements, exp]);
  };
}

const index = {};
const retOf = (decl) => {
  const sg = checker.getSignatureFromDeclaration(decl);
  return sg ? checker.typeToString(checker.getReturnTypeOfSignature(sg)) : '';
};
const sig = (decl) => decl.parameters.filter(p => !(ts.isIdentifier(p.name) && p.name.text === 'this')).map(p => ({
  name: ts.isIdentifier(p.name) ? p.name.text : '<pattern>',
  type: checker.typeToString(checker.getTypeAtLocation(p)),
}));
for (const sf of own) {
  const rel = path.relative(rootDir, sf.fileName);
  const items = [];
  const line = (n) => sf.getLineAndCharacterOfPosition(n.getStart(sf)).line + 1;
  const exported = (n) => !!ts.getModifiers(n)?.some(x => x.kind === ts.SyntaxKind.ExportKeyword);
  const isPrivate = (m) => (m.name && ts.isPrivateIdentifier(m.name)) || !!ts.getModifiers(m)?.some(x => x.kind === ts.SyntaxKind.PrivateKeyword || x.kind === ts.SyntaxKind.ProtectedKeyword);
  for (const st of sf.statements) {
    if (ts.isFunctionDeclaration(st) && st.name && st.body) items.push({ name: st.name.text, kind: 'function', line: line(st), params: sig(st), ret: retOf(st), typeParams: (st.typeParameters ?? []).map(t => t.name.text), exported: exported(st) });
    if (ts.isVariableStatement(st)) {
      for (const d of st.declarationList.declarations) {
        let init = d.initializer;
        while (init && (ts.isParenthesizedExpression(init) || ts.isAsExpression(init) || ts.isSatisfiesExpression(init))) init = init.expression;
        if (ts.isIdentifier(d.name) && init && (ts.isArrowFunction(init) || ts.isFunctionExpression(init))) {
          items.push({ name: d.name.text, kind: 'arrow', line: line(init), params: sig(init), ret: retOf(init), typeParams: (init.typeParameters ?? []).map(t => t.name.text), exported: exported(st) });
        }
      }
    }
    if (ts.isClassDeclaration(st) && st.name) {
      items.push({ name: st.name.text, cls: st.name.text, kind: 'class', line: line(st), params: [], exported: exported(st) });
      for (const m of st.members) {
        const mn = m.name && (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name)) ? m.name.text : undefined;
        const api = exported(st) && !isPrivate(m);
        if (ts.isConstructorDeclaration(m)) items.push({ name: `${st.name.text}.constructor`, cls: st.name.text, kind: 'constructor', line: line(m), params: sig(m), exported: api });
        else if (ts.isMethodDeclaration(m) && mn) {
          const isStatic = !!ts.getModifiers(m)?.some(x => x.kind === ts.SyntaxKind.StaticKeyword);
          items.push({ name: `${st.name.text}.${mn}`, cls: st.name.text, member: mn, kind: isStatic ? 'static' : 'method', line: line(m), params: sig(m), ret: retOf(m), typeParams: [...(st.typeParameters ?? []), ...(m.typeParameters ?? [])].map(t => t.name.text), exported: api });
        } else if (ts.isGetAccessorDeclaration(m) && mn) items.push({ name: `${st.name.text}.get ${mn}`, cls: st.name.text, member: mn, kind: 'getter', line: line(m), params: [], ret: retOf(m), exported: api });
      }
    }
  }
  index[rel.replace(/\.ts$/, '.js')] = items;
}

fs.mkdirSync(outDir, { recursive: true });
let n = 0;
for (const sf of own) {
  const r = program.emit(sf, (file, text) => {
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, text);
    n++;
  }, undefined, false, { before: [instrument(sf)] });
  if (r.emitSkipped) console.error(`emit skipped: ${sf.fileName}`);
}
fs.writeFileSync(path.join(outDir, 'index.json'), JSON.stringify(index, null, 1));
console.log(`${n} files emitted into ${outDir}; ${Object.values(index).reduce((a, x) => a + x.length, 0)} functions indexed`);

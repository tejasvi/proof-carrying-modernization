// Test cases of vitest spec files as StrictTS-subset functions (deterministic rewrite; no model).
// usage: node extract_tests.js OUT_DIR spec.spec.ts ...  ->  JSON [{spec, index, title, name, line, text, gap}]
//
// Each `it(title, () => { ... })` / `test(...)` (inside any `describe` nesting) becomes one file with
// `export function <name>(): void`, whose body is the test body with every expectation rewritten into a check
// that throws when the matcher fails (helpers in vo_expect.ts, written next to the generated files):
//   expect(a).toBe(b), expect(a).toEqual(b)   number: vo_check(vo_is_num(a, b))   (Object.is, as vitest)
//                                             string/boolean: vo_check(a === b)
//   expect(a).toEqual(b)                      number[]: vo_check(vo_eq_num_arr(a, b)) (length + Object.is)
//   expect(a).toBeCloseTo(b[, p])             vo_check(vo_close(a, b, p ?? 2))   (vitest's formula)
//   expect(a).toBeNaN()                       vo_check(Number.isNaN(a))
//   expect(() => e).toThrow()                 try { e; } catch { thrown = true }; vo_check(thrown)
//   expect(() => e).toThrow('s')              ... and the error's message includes 's'
// Local type aliases of a test body are hoisted to the file (types have no run-time effect); declarations in
// enclosing `describe` bodies and top-level declarations of the spec are copied in front of the body. A case
// that uses anything else (other matchers, `.not`, hooks, `vi`, async bodies, test context) is reported as a
// gap with the reason, so the theorem of every emitted case is exactly the test as written.
"use strict";
const fs = require("fs");
const path = require("path");
const ts = require("typescript");

const outDir = path.resolve(process.argv[2]);
const specs = process.argv.slice(3).map((f) => path.resolve(f));

function resolveImport(fromFile, spec) {
  if (!spec.startsWith(".")) return null;
  const base = path.resolve(path.dirname(fromFile), spec);
  for (const c of [base, base + ".ts", base + ".tsx", path.join(base, "index.ts")]) {
    if (fs.existsSync(c) && fs.statSync(c).isFile()) return c;
  }
  return null;
}

function relImport(target) {
  let r = path.relative(outDir, target).replace(/\.tsx?$/, "");
  if (!r.startsWith(".")) r = "./" + r;
  return r.split(path.sep).join("/");
}

// one program over all specs (and, through their imports, the sources) for the static types of expectations
const program = ts.createProgram(specs, {
  target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler,
  strict: true, noEmit: true, skipLibCheck: true, allowImportingTsExtensions: true,
});
const checker = program.getTypeChecker();

function kindOf(node) {
  const t = checker.getTypeAtLocation(node);
  const s = checker.typeToString(checker.getBaseTypeOfLiteralType(t));
  if (s === "number") return "num";
  if (s === "string") return "str";
  if (s === "boolean") return "bool";
  if (s === "number[]" || s === "readonly number[]") return "num[]";
  return "other:" + s;
}

const TEST_FNS = new Set(["it", "test"]);
const HOOKS = new Set(["beforeEach", "afterEach", "beforeAll", "afterAll"]);

function calleeName(call) {
  const e = call.expression;
  if (ts.isIdentifier(e)) return e.text;
  if (ts.isPropertyAccessExpression(e) && ts.isIdentifier(e.expression)) return e.expression.text + "." + e.name.text;
  return null;
}

const out = [];
for (const spec of specs) {
  const sf = program.getSourceFile(spec);
  const stem = path.basename(spec).replace(/\.(spec|test)\.tsx?$/, "").replace(/[^A-Za-z0-9_]/g, "_");
  const imports = [];       // rewritten import declarations (vitest dropped)
  const importFiles = [];   // the source files they name
  const topDecls = [];      // other top-level declarations of the spec
  let fileGap = null;
  for (const st of sf.statements) {
    if (ts.isImportDeclaration(st)) {
      const m = st.moduleSpecifier.text;
      if (m === "vitest") continue;
      const target = resolveImport(spec, m);
      if (!target) { fileGap = `import of '${m}' is not a relative source file`; continue; }
      imports.push(st.getText(sf).replace(st.moduleSpecifier.getText(sf), `'${relImport(target)}'`));
      importFiles.push(target);
    } else if (ts.isExpressionStatement(st) && ts.isCallExpression(st.expression)
               && ["describe", "it", "test"].includes(calleeName(st.expression))) {
      // collected below
    } else {
      topDecls.push(st.getText(sf));
    }
  }
  let index = 0;
  const visit = (stmts, prefix, titles, hookGap) => {
    // statements of a describe body: declarations are shared by its cases; nested describes and cases recurse
    const local = [];
    for (const st of stmts) {
      if (ts.isExpressionStatement(st) && ts.isCallExpression(st.expression)) {
        const call = st.expression;
        const name = calleeName(call);
        const base = name && name.split(".")[0];
        const mod = name && name.includes(".") ? name.split(".")[1] : null;
        if (base === "describe") {
          if (mod === "skip" || mod === "todo") continue;
          const t = call.arguments[0], fn = call.arguments[1];
          const title = t && ts.isStringLiteralLike(t) ? t.text : "?";
          if (fn && (ts.isArrowFunction(fn) || ts.isFunctionExpression(fn)) && fn.body && ts.isBlock(fn.body)) {
            visit(fn.body.statements, prefix.concat(local), titles.concat([title]),
                  hookGap || (mod && mod !== "only" ? `describe.${mod}` : null));
          }
          continue;
        }
        if (TEST_FNS.has(base)) {
          if (mod === "skip" || mod === "todo") continue;
          index += 1;
          emitCase(spec, stem, index, call, prefix.concat(local), titles, hookGap || (mod && mod !== "only" ? `${base}.${mod}` : null));
          continue;
        }
        if (HOOKS.has(base)) { hookGap = hookGap || `hook ${base}`; continue; }
      }
      if (titles.length) local.push(st);   // top-level statements: imports and topDecls above
    }
  };
  const emitCase = (spec, stem, index, call, prefix, titles, gap) => {
    const t = call.arguments[0], fn = call.arguments[1];
    const title = titles.concat([t && ts.isStringLiteralLike(t) ? t.text : "?"]).join(" > ");
    const name = `vo_test_${stem}_${index}`;
    const line = sf.getLineAndCharacterOfPosition(call.getStart(sf)).line + 1;
    const rec = { spec, index, title, name, line, text: "", gap: gap || fileGap, imports: importFiles };
    out.push(rec);
    if (rec.gap) return;
    if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn))) { rec.gap = "test body is not a function literal"; return; }
    if (fn.parameters.length) { rec.gap = "test body uses the test context"; return; }
    if (fn.modifiers && fn.modifiers.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) { rec.gap = "async test body"; return; }
    if (call.arguments.length > 2) { rec.gap = "test options/timeout argument"; return; }
    const body = fn.body;
    const hoisted = [];
    const edits = [];        // [start, end, replacement] within the body text
    let gapReason = null;
    const bodyStart = ts.isBlock(body) ? body.getStart(sf) + 1 : body.getStart(sf);
    const bodyEnd = ts.isBlock(body) ? body.getEnd() - 1 : body.getEnd();
    const rewriteExpect = (node) => {
      // node: CallExpression `expect(a).matcher(args)`
      const pa = node.expression;
      const matcher = pa.name.text;
      const inner = pa.expression;      // expect(a) or expect(a).not
      if (!ts.isCallExpression(inner) || calleeName(inner) !== "expect" || inner.arguments.length !== 1) {
        return { gap: `unsupported expectation form '${node.getText(sf).slice(0, 60)}'` };
      }
      const a = inner.arguments[0];
      const A = a.getText(sf);
      const args = node.arguments.map((x) => x.getText(sf));
      const ka = kindOf(a);
      if (matcher === "toBe" || matcher === "toEqual" || matcher === "toStrictEqual") {
        if (args.length !== 1) return { gap: `${matcher} with ${args.length} arguments` };
        if (ka === "num") return { text: `vo_check(vo_is_num(${A}, ${args[0]}))` };
        if (ka === "str" || ka === "bool") return { text: `vo_check(${A} === ${args[0]})` };
        if (ka === "num[]" && matcher !== "toBe") return { text: `vo_check(vo_eq_num_arr(${A}, ${args[0]}))` };
        return { gap: `${matcher} on a value of type ${ka.replace(/^other:/, "")}` };
      }
      if (matcher === "toBeCloseTo") {
        if (ka !== "num" || args.length < 1 || args.length > 2) return { gap: "toBeCloseTo form" };
        return { text: `vo_check(vo_close(${A}, ${args[0]}, ${args.length === 2 ? args[1] : "2"}))` };
      }
      if (matcher === "toBeNaN") {
        if (ka !== "num" || args.length) return { gap: "toBeNaN form" };
        return { text: `vo_check(Number.isNaN(${A}))` };
      }
      if (matcher === "toThrow" || matcher === "toThrowError") {
        if (!(ts.isArrowFunction(a) && a.parameters.length === 0)) return { gap: "toThrow on a non-arrow" };
        if (args.length > 1) return { gap: "toThrow with several arguments" };
        let run;
        if (ts.isBlock(a.body)) run = a.body.statements.map((s) => s.getText(sf)).join("\n");
        else run = a.body.getText(sf) + ";";
        let cond = "vo_thrown = true;";
        if (args.length === 1) {
          if (!ts.isStringLiteralLike(node.arguments[0])) return { gap: "toThrow with a non-string argument" };
          cond = `if (vo_e instanceof Error && vo_e.message.includes(${args[0]})) {\n      vo_thrown = true;\n    }`;
        }
        return { text: `{\n  let vo_thrown = false;\n  try {\n    ${run}\n  } catch (vo_e) {\n    ${cond}\n  }\n  vo_check(vo_thrown);\n}`, stmt: true };
      }
      return { gap: `matcher ${matcher}` };
    };
    const walk = (node) => {
      if (gapReason) return;
      if (ts.isTypeAliasDeclaration(node) || ts.isInterfaceDeclaration(node)) {
        hoisted.push(node.getText(sf));
        edits.push([node.getFullStart(), node.getEnd(), ""]);
        return;
      }
      if (ts.isCallExpression(node)) {
        const n = calleeName(node);
        if (n && (n.startsWith("vi.") || n === "vi" || HOOKS.has(n))) { gapReason = `uses ${n}`; return; }
        if (ts.isPropertyAccessExpression(node.expression)) {
          // the outermost call of an `expect(...)...` chain
          let root = node.expression.expression;
          while (ts.isPropertyAccessExpression(root)) root = root.expression;
          if (ts.isCallExpression(root) && calleeName(root) === "expect") {
            if (!ts.isExpressionStatement(node.parent)) { gapReason = "expectation used as a value"; return; }
            const r = rewriteExpect(node);
            if (r.gap) { gapReason = r.gap; return; }
            edits.push([node.parent.getStart(sf), node.parent.getEnd(), r.stmt ? r.text : r.text + ";"]);
            return;
          }
        }
        if (ts.isIdentifier(node.expression) && node.expression.text === "expect") {
          gapReason = "bare expect(...) without a matcher"; return;
        }
      }
      ts.forEachChild(node, walk);
    };
    ts.forEachChild(body, walk);
    if (gapReason) { rec.gap = gapReason; return; }
    let text = sf.text.slice(bodyStart, bodyEnd);
    edits.sort((x, y) => y[0] - x[0]);
    for (const [s, e, r] of edits) {
      const s0 = Math.max(s, bodyStart) - bodyStart, e0 = e - bodyStart;
      text = text.slice(0, s0) + r + text.slice(e0);
    }
    if (!ts.isBlock(body)) text = text + ";";
    const lines = [
      `// Generated by verif-orchestrator (adapters/strictts/extract_tests.js) from ${path.basename(spec)}:${line}.`,
      `// The vitest case "${title.replace(/\n/g, " ")}" with its expectations as checks (vo_expect.ts).`,
      `import { ${["vo_check", "vo_is_num", "vo_eq_num_arr", "vo_close"].filter((h) => h === "vo_check" || new RegExp("\\b" + h + "\\(").test(text)).join(", ")} } from './vo_expect';`,
      ...imports, "", ...topDecls, ...hoisted, "",
      `/** ${title.replace(/\*\//g, "* /")} */`,
      `export function ${name}(): void {`,
      ...prefix.map((s) => "  " + s.getText(sf)),
      text.replace(/^\n/, ""),
      `}`, "",
    ];
    rec.text = lines.join("\n");
  };
  visit(sf.statements, [], [], null);
}
process.stdout.write(JSON.stringify(out));

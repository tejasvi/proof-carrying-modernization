// List the top-level functions of TypeScript files (TypeScript compiler API, no type checking).
// usage: node list_functions.js file.ts ...  ->  JSON [{file, name, exported, line, endLine, text}]
"use strict";
const fs = require("fs");
const ts = require("typescript");

const out = [];
for (const file of process.argv.slice(2)) {
  const text = fs.readFileSync(file, "utf8");
  const sf = ts.createSourceFile(file, text, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS);
  const seen = new Set();
  const add = (name, node, exported) => {
    const start = sf.getLineAndCharacterOfPosition(node.getStart(sf)).line + 1;
    const end = sf.getLineAndCharacterOfPosition(node.getEnd()).line + 1;
    const key = `${name}:${start}`;
    if (seen.has(key)) return;
    seen.add(key);
    out.push({ file, name, exported, line: start, endLine: end, text: node.getText(sf), hasBody: !!node.body });
  };
  for (const st of sf.statements) {
    const exported = !!(ts.getCombinedModifierFlags(st) & ts.ModifierFlags.Export);
    if (ts.isFunctionDeclaration(st) && st.name) {
      add(st.name.text, st, exported);
    } else if (ts.isVariableStatement(st)) {
      for (const d of st.declarationList.declarations) {
        if (ts.isIdentifier(d.name) && d.initializer &&
            (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer))) {
          add(d.name.text, st, exported);
        }
      }
    } else if (ts.isClassDeclaration(st) && st.name) {
      for (const m of st.members) {
        if ((ts.isMethodDeclaration(m) || ts.isConstructorDeclaration(m)) && m.body) {
          const mname = ts.isConstructorDeclaration(m) ? "new" : (m.name && m.name.getText(sf));
          add(`${st.name.text}_${mname}`, m, exported);
        }
      }
    }
  }
}
process.stdout.write(JSON.stringify(out));

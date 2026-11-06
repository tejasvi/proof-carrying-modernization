// Thrift T1, TypeScript: the function-like declarations of .ts/.d.ts files, with or without a body (thrift.d.ts
// declares the browser library's API without bodies). Parses only (TypeScript's parser from the pinned StrictTS's
// node_modules, found through NODE_PATH); nothing of the files runs.
//   node tools/thrift_rsts/list_decls.js FILE...   -> JSON [{file, name, kind, line, hasBody, container}]
'use strict';
const ts = require('typescript');
const fs = require('fs');
const out = [];
for (const file of process.argv.slice(2)) {
  const sf = ts.createSourceFile(file, fs.readFileSync(file, 'utf8'), ts.ScriptTarget.Latest, true);
  const line = (n) => sf.getLineAndCharacterOfPosition(n.getStart(sf)).line + 1;
  const nameOf = (n) => (n.name && (ts.isIdentifier(n.name) || ts.isStringLiteral(n.name) || ts.isPrivateIdentifier(n.name)) ? n.name.text : '<anon>');
  const visit = (n, container) => {
    let kind = null;
    if (ts.isFunctionDeclaration(n)) kind = 'function';
    else if (ts.isMethodDeclaration(n) || ts.isMethodSignature(n)) kind = 'method';
    else if (ts.isConstructorDeclaration(n) || ts.isConstructSignatureDeclaration(n)) kind = 'constructor';
    else if (ts.isGetAccessorDeclaration(n) || ts.isSetAccessorDeclaration(n)) kind = 'accessor';
    else if (ts.isArrowFunction(n) || ts.isFunctionExpression(n)) kind = 'function-expression';
    if (kind) {
      const nm = kind === 'constructor' ? 'constructor' : (kind === 'function-expression' ? '<expr>' : nameOf(n));
      out.push({ file, name: container ? `${container}.${nm}` : nm, kind, line: line(n), hasBody: !!n.body, container: container || '' });
    }
    let c = container;
    if ((ts.isClassDeclaration(n) || ts.isInterfaceDeclaration(n)) && n.name) c = n.name.text;
    ts.forEachChild(n, (k) => visit(k, c));
  };
  visit(sf, '');
}
process.stdout.write(JSON.stringify(out, null, 1) + '\n');

// R6d: for every pair whose proof has the statement old-no-panic, the declared return type of the
// function in the old and in the new source (TypeScript's parser on the pair's slices; "(none)" when
// the return type is inferred) and the translated return types from the run's note.
//   node np_returns.js RUN_DIR PAIRS_ROOT > RUN_DIR/np_returns.tsv
'use strict';
const fs = require('fs');
const path = require('path');
const ts = require('/home/user/strictts/frontend/node_modules/typescript');
const [run, pairsRoot] = process.argv.slice(2).map(p => path.resolve(p));
const tsv = f => { const [h, ...rs] = fs.readFileSync(f, 'utf8').split('\n').filter(Boolean); const ks = h.split('\t'); return rs.map(r => Object.fromEntries(r.split('\t').map((v, i) => [ks[i], v]))); };
const rows = tsv(path.join(run, process.env.TABLE_NAME || 'r6d_table.tsv')).filter(r => r.statement === 'old-no-panic');
const byId = new Map();
for (const f of fs.readdirSync(path.join(run, 'chunks')).filter(x => x.endsWith('.json')))
  for (const p of JSON.parse(fs.readFileSync(path.join(run, 'chunks', f), 'utf8'))) byId.set(p.id, p);
const pairDir = id => fs.readdirSync(pairsRoot).map(d => path.join(pairsRoot, d, id)).find(d => fs.existsSync(path.join(d, 'meta.json')));
const declaredReturn = (file, name) => {
  if (!fs.existsSync(file)) return '(no file)';
  const sf = ts.createSourceFile(file, fs.readFileSync(file, 'utf8'), ts.ScriptTarget.Latest, true);
  let out = '(not found)';
  const visit = n => {
    if (ts.isFunctionDeclaration(n) && n.name?.text === name && n.body) out = n.type ? n.type.getText(sf) : '(none)';
    if (ts.isVariableDeclaration(n) && ts.isIdentifier(n.name) && n.name.text === name && n.initializer &&
        (ts.isArrowFunction(n.initializer) || ts.isFunctionExpression(n.initializer))) out = n.initializer.type ? n.initializer.type.getText(sf) : '(none)';
    ts.forEachChild(n, visit);
  };
  visit(sf);
  return out.replace(/\s+/g, ' ');
};
console.log(['pair', 'commit', 'type', 'fn', 'old declared return', 'new declared return', 'translated (note)'].join('\t'));
for (const r of rows) {
  const d = pairDir(r.id);
  const meta = JSON.parse(fs.readFileSync(path.join(d, 'meta.json'), 'utf8'));
  const fn = byId.get(r.id)?.functions.find(x => x.status === 'changed');
  const note = (fn?.notes ?? []).find(n => /the return type changed|the signature widened/.test(n)) ?? '';
  const m = /\(([^()]*(?:\([^()]*\)[^()]*)*) vs ([^()]*(?:\([^()]*\)[^()]*)*)\)\s*$/.exec(note);
  console.log([r.id, meta.commit.slice(0, 10), r.type, meta.function, declaredReturn(path.join(d, 'old', meta.file), meta.function),
    declaredReturn(path.join(d, 'new', meta.file), meta.function), m ? `${m[1]} -> ${m[2]}` : (note ? note.slice(0, 160) : '(no wrapper)')].join('\t'));
}

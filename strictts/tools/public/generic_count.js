// Covered units of a coverage report that are generic (a type parameter on the function or on
// its class): `--emit-lean` leaves these out by design (src/partial.ts), so they explain part of
// the gap between covered and emitted units.
//   node tools/public/generic_count.js PROJECT_DIR REPORT.json
'use strict';
const path = require('path');
const fs = require('fs');
const ts = require(path.join(__dirname, '..', '..', 'frontend', 'node_modules', 'typescript'));
const [projectDir, reportPath] = process.argv.slice(2).map(p => path.resolve(p));
const report = JSON.parse(fs.readFileSync(reportPath, 'utf8'));
const files = new Map();
let covered = 0, generic = 0;
for (const r of report.rows) {
  if (r.status !== 'covered') continue;
  covered++;
  const file = path.join(projectDir, r.file);
  let sf = files.get(file);
  if (!sf) { sf = ts.createSourceFile(file, fs.readFileSync(file, 'utf8'), ts.ScriptTarget.Latest, true); files.set(file, sf); }
  let hit = false;
  const visit = (n) => {
    if (hit) return;
    if ((ts.isFunctionLike(n)) && sf.getLineAndCharacterOfPosition(n.getStart(sf)).line + 1 === r.line) {
      const cls = n.parent && ts.isClassLike(n.parent) ? n.parent : undefined;
      if (n.typeParameters?.length || cls?.typeParameters?.length) hit = true;
      return;
    }
    ts.forEachChild(n, visit);
  };
  visit(sf);
  if (hit) generic++;
}
console.log(JSON.stringify({ report: path.basename(reportPath), covered, generic }));

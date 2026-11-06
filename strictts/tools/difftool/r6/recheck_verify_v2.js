// R6 (v2): after recheck.sh, verify for every row of evidence/proofs.tsv (PROVED pairs only) that the
// recheck output of its batch file prints "'<theorem>' depends on axioms: [propext, Classical.choice,
// Quot.sound]". Also compare, per batch file, the theorems' axiom lines of the recheck with those of
// the run's stored output: the difftool truncates stored outputs and names files by their run path,
// so whole outputs are not comparable; the axiom lines are, for every theorem whose line the stored
// output still holds.
//   node scratch/r6/recheck_verify_v2.js EVIDENCE_DIR
'use strict';
const fs = require('fs');
const path = require('path');
const ev = path.resolve(process.argv[2]);
const STD = ['propext', 'Classical.choice', 'Quot.sound'];
const [, ...rows] = fs.readFileSync(path.join(ev, 'proofs.tsv'), 'utf8').split('\n').filter(Boolean);
let ok = 0;
const bad = [];
for (const r of rows) {
  const [pair, thm, , , file] = r.split('\t');
  const out = fs.readFileSync(path.join(ev, file.replace(/\.lean$/, '.recheck.out')), 'utf8');
  const m = out.match(new RegExp(`'${thm}' depends on axioms: \\[([^\\]]*)\\]`));
  const ax = m ? m[1].split(',').map(s => s.trim()) : null;
  if (ax && ax.length === STD.length && STD.every(a => ax.includes(a))) ok++;
  else bad.push(`${pair} ${thm}: ${ax ? ax.join(', ') : 'no axioms line'}`);
}
const axLines = s => new Map([...s.matchAll(/'([^']+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)/g)].map(m => [m[1], m[2]]));
let compared = 0, agreeing = 0;
const differ = [];
for (const f of fs.readdirSync(ev).filter(x => x.endsWith('.lean'))) {
  const a = path.join(ev, f.replace(/\.lean$/, '.out')), b = path.join(ev, f.replace(/\.lean$/, '.recheck.out'));
  if (!fs.existsSync(a) || !fs.existsSync(b)) continue;
  const ra = axLines(fs.readFileSync(a, 'utf8')), rb = axLines(fs.readFileSync(b, 'utf8'));
  for (const [t, v] of ra) { compared++; if (rb.get(t) === v) agreeing++; else differ.push(`${f} ${t}: run ${v} | recheck ${rb.get(t)}`); }
}
console.log(`verify: ${ok}/${rows.length} PROVED theorems print exactly the standard axioms on recheck; ` +
  `axiom lines of the run's stored outputs reproduced: ${agreeing}/${compared}`);
for (const x of bad) console.log(`  NOT OK ${x}`);
for (const x of differ) console.log(`  DIFFERS ${x}`);

// no error inside a PROVED theorem: its lines run from `theorem <name>` to `#print axioms <name>`
let clean = 0;
const errs = [];
for (const r of rows) {
  const [pair, thm, , , file] = r.split('\t');
  const src = fs.readFileSync(path.join(ev, file), 'utf8').split('\n');
  const a = src.findIndex(l => new RegExp(`^theorem ${thm} `).test(l)) + 1;
  const b = src.findIndex(l => l.trim() === `#print axioms ${thm}`) + 1;
  const out = fs.readFileSync(path.join(ev, file.replace(/\.lean$/, '.recheck.out')), 'utf8');
  const bad = [...out.matchAll(/\.lean:(\d+):\d+: error/g)].map(m => +m[1]).filter(n => a > 0 && b > 0 && n >= a - 1 && n <= b);
  if (a > 0 && b > 0 && bad.length === 0) clean++; else errs.push(`${pair} ${thm}: lines ${a}-${b}, errors at ${bad.join(',') || '(theorem not located)'}`);
}
console.log(`verify: ${clean}/${rows.length} PROVED theorems have no error inside their lines on recheck`);
for (const x of errs) console.log(`  ERROR ${x}`);

// R6e evidence (R6's collect.js; also the old-no-panic proofs, which the tool now reports with verdict
// UNKNOWN): copy the Lean batch files that the proofs of the chunk JSONs name (and their
// outputs) into evidence/, under names unique across chunks, and write proofs.tsv:
// pair, theorem, statement, axioms, evidence file.
//   node scratch/r6e/collect_v2.js CHUNKS_DIR EVIDENCE_DIR
'use strict';
const fs = require('fs');
const path = require('path');
const [chunks, ev] = process.argv.slice(2).map(p => path.resolve(p));
fs.mkdirSync(ev, { recursive: true });
const rows = [];
const copied = new Map();
for (const f of fs.readdirSync(chunks).filter(x => x.endsWith('.json')).sort()) {
  for (const p of JSON.parse(fs.readFileSync(path.join(chunks, f), 'utf8'))) {
    for (const fn of p.functions) {
      const np = fn.verdict === 'UNKNOWN' && fn.proof?.statement === 'old-no-panic' && fn.proof?.np?.ok;
      if (fn.status !== 'changed' || (fn.verdict !== 'PROVED' && !np) || !fn.proof) continue;
      const src = fn.proof.file;
      let dst = copied.get(src);
      if (!dst) {
        dst = `${path.basename(path.dirname(path.dirname(src)))}__${path.basename(src)}`;
        fs.copyFileSync(src, path.join(ev, dst));
        const out = src.replace(/\.lean$/, '.out');
        if (fs.existsSync(out)) fs.copyFileSync(out, path.join(ev, dst.replace(/\.lean$/, '.out')));
        copied.set(src, dst);
      }
      rows.push([p.id, fn.proof.theorem, fn.proof.statement, fn.proof.axioms.join(' '), dst].join('\t'));
    }
  }
}
fs.writeFileSync(path.join(ev, 'proofs.tsv'), ['pair\ttheorem\tstatement\taxioms\tfile', ...rows].join('\n') + '\n');
console.log(`collect: ${rows.length} proofs in ${copied.size} batch files`);

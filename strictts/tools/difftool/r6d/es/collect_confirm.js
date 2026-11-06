// Freeze the Lean confirmation files of a history run: every Lean file in the run's difftool work
// directories (history-<time>-<pid>, created at or after FROM) that holds a confirmation block
// (`namespace OldC_h<i>u<j>`) is copied to OUT_DIR with its output, and confirmations.tsv maps each block
// to its pair: block h<i> is the i-th pair (by sorted id) of that work directory, which holds one
// subdirectory per pair it ran.
//   node collect_confirm.js DIFFTOOL_SCRATCH FROM_STAMP OUT_DIR [TO_STAMP]      e.g. FROM_STAMP 20261027T023425Z
// (R6d: TO_STAMP, exclusive, ends the window when another run started later in the same checkout)
'use strict';
const fs = require('fs');
const path = require('path');
const [root, from, out, to] = process.argv.slice(2).map((p, i) => i === 1 || i === 3 ? p : path.resolve(p));
fs.mkdirSync(out, { recursive: true });
const rows = ['pair\tconfirmation\tfile'];
for (const w of fs.readdirSync(root).filter(d => /^history-\d{8}T\d{6}Z-\d+$/.test(d) && d.slice(8, 24) >= from && (!to || d.slice(8, 24) < to)).sort()) {
  const wd = path.join(root, w);
  const pairs = fs.readdirSync(wd).filter(d => /^\d{4}-\d{2}-\d{2}_/.test(d) && fs.statSync(path.join(wd, d)).isDirectory()).sort();
  const ld = path.join(wd, 'lean');
  if (!fs.existsSync(ld)) continue;
  for (const f of fs.readdirSync(ld).filter(x => x.endsWith('.lean')).sort()) {
    const text = fs.readFileSync(path.join(ld, f), 'utf8');
    const ns = [...new Set([...text.matchAll(/^namespace (OldC_h(\d+)u\d+)$/gm)].map(m => m[1] + ' ' + m[2]))];
    if (!ns.length) continue;
    const dst = `${w}__${f}`;
    fs.copyFileSync(path.join(ld, f), path.join(out, dst));
    const o = path.join(ld, f.replace(/\.lean$/, '.out'));
    if (fs.existsSync(o)) fs.copyFileSync(o, path.join(out, dst.replace(/\.lean$/, '.out')));
    for (const s of ns) {
      const [name, idx] = s.split(' ');
      rows.push([pairs[Number(idx)] ?? `?index ${idx}`, name, dst].join('\t'));
    }
  }
}
fs.writeFileSync(path.join(out, 'confirmations.tsv'), rows.join('\n') + '\n');
console.log(`collect_confirm: ${rows.length - 1} confirmation blocks`);

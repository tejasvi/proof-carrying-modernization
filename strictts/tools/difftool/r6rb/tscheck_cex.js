// For every R6 refutation: does the counterexample call type-check against the function's public
// TypeScript signatures (its overloads, or its declaration)? For each version, the pair's slice is
// copied, a file `check.ts` with `import { f } from './entry'; <the counterexample call>;` is added,
// and the TypeScript checker (strict) reports the diagnostics of check.ts only.
//   node tscheck_cex.js CHUNKS_DIR PAIRS_ROOT WORK_DIR > tscheck.tsv
'use strict';
const fs = require('fs');
const path = require('path');
const ts = require('/home/user/strictts/frontend/node_modules/typescript');
const [chunks, pairsRoot, work] = process.argv.slice(2).map(p => path.resolve(p));
const copy = (src, dst) => { for (const e of fs.readdirSync(src, { withFileTypes: true })) { const s = path.join(src, e.name), d = path.join(dst, e.name); if (e.isDirectory()) copy(s, d); else { fs.mkdirSync(dst, { recursive: true }); fs.copyFileSync(s, d); } } };
const opts = { strict: true, noEmit: true, skipLibCheck: true, target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext,
  moduleResolution: ts.ModuleResolutionKind.Bundler, lib: ['lib.es2023.d.ts', 'lib.dom.d.ts'], allowImportingTsExtensions: true, types: [] };
console.log('pair\tversion\tvalid\tfirst diagnostic');
for (const f of fs.readdirSync(chunks).filter(x => x.endsWith('.json')).sort()) {
  for (const p of JSON.parse(fs.readFileSync(path.join(chunks, f), 'utf8'))) {
    const fn = p.functions.find(x => x.status === 'changed');
    if (!fn || fn.verdict !== 'REFUTED') continue;
    const pd = ['scan'].map(d => path.join(pairsRoot, d, p.id)).find(d => fs.existsSync(path.join(d, 'meta.json')));
    const meta = JSON.parse(fs.readFileSync(path.join(pd, 'meta.json'), 'utf8'));
    for (const v of ['old', 'new']) {
      const d = path.join(work, p.id, v);
      fs.rmSync(d, { recursive: true, force: true });
      copy(path.join(pd, v), d);
      const entry = './' + meta.entry.replace(/\.tsx?$/, '');
      const check = path.join(d, 'check.ts');
      fs.writeFileSync(check, `import { ${meta.function} } from ${JSON.stringify(entry)};\n${fn.cex.inputText};\n`);
      const prog = ts.createProgram([check], opts);
      const diags = [...prog.getSyntacticDiagnostics(prog.getSourceFile(check)), ...prog.getSemanticDiagnostics(prog.getSourceFile(check))];
      const first = diags.length ? ts.flattenDiagnosticMessageText(diags[0].messageText, ' ').replace(/\s+/g, ' ').slice(0, 160) : '';
      console.log([p.id, v, diags.length ? 'no' : 'yes', first].join('\t'));
    }
  }
}

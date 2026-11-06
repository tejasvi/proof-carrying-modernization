// R6d report (R6r's r6r_report.js, plus a statement column, the return-type wrapper in the domain column, and
// old-no-panic proofs counted in their own column, never as PROVED; R6r's r6r_report.js: the designed-panic reason no longer claims the read is outside the
// types, which is false for unknown[]): one row per pair of the frozen testable list, from the chunk
// JSONs of the full run, the pair metadata, the evidence index (proofs.tsv) and the independent Node
// replay (replay.tsv). Reads R6_DIR/r6_testable.txt and r6_provable.txt (copies of the frozen lists).
//   TABLE_NAME=r6r_table.tsv DRAFT_NAME=R6R_draft.md node r6r_report.js R6_DIR PAIRS_ROOT
// Writes R6_DIR/$TABLE_NAME and R6_DIR/$DRAFT_NAME (summary tables; the prose is added by hand).
'use strict';
const fs = require('fs');
const path = require('path');
const [r6, pairsRoot] = process.argv.slice(2).map(p => path.resolve(p));
const lines = f => fs.readFileSync(f, 'utf8').split('\n').filter(Boolean);
const testable = lines(path.join(r6, 'r6_testable.txt'));
const provable = new Set(lines(path.join(r6, 'r6_provable.txt')));
const byId = new Map();
for (const f of fs.readdirSync(path.join(r6, 'chunks')).filter(x => x.endsWith('.json')).sort())
  for (const p of JSON.parse(fs.readFileSync(path.join(r6, 'chunks', f), 'utf8'))) byId.set(p.id, p);
const tsv = f => { const [h, ...rs] = lines(f); const ks = h.split('\t'); return rs.map(r => Object.fromEntries(r.split('\t').map((v, i) => [ks[i], v]))); };
const proofs = new Map(fs.existsSync(path.join(r6, 'evidence', 'proofs.tsv')) ? tsv(path.join(r6, 'evidence', 'proofs.tsv')).map(r => [r.pair, r]) : []);
const replay = new Map(fs.existsSync(path.join(r6, 'replay_v2', 'replay.tsv')) ? tsv(path.join(r6, 'replay_v2', 'replay.tsv')).map(r => [r.pair, r]) : []);
const intent = t => ['refactor', 'perf', 'style', 'chore'].includes(t) ? 'preserve' : ['fix', 'feat', 'revert'].includes(t) ? 'change' : 'other';
const clean = s => String(s ?? '').replace(/[\t\n]+/g, ' ').slice(0, 300);

const rows = [];
for (const line of testable) {
  const [dir, id] = line.split('/');
  const meta = JSON.parse(fs.readFileSync(path.join(pairsRoot, dir, id, 'meta.json'), 'utf8'));
  const type = (/^(\w+)(\([^)]*\))?!?:/.exec(meta.subject) ?? [, 'other'])[1].toLowerCase();
  const p = byId.get(id);
  const fn = p?.functions.find(x => x.status === 'changed');
  let cat, evidence = '', reason = '';
  if (!p) { cat = 'NO RESULT'; reason = 'no record from the run'; }
  else if (!fn) { cat = 'UNCHANGED'; reason = 'the run found no change in the target function'; }
  else if (fn.verdict === 'PROVED') { cat = `PROVED (${fn.proof.statement})`; const e = proofs.get(id); evidence = `${fn.proof.theorem} in ${e ? e.file : path.basename(fn.proof.file)}; axioms ${fn.proof.axioms.join(', ')}`; }
  else if (fn.verdict === 'REFUTED') {
    cat = (fn.confirmedBy ?? []).includes('lean') ? 'REFUTED (Lean-confirmed)' : 'REFUTED (Node only)';
    const rp = replay.get(id);
    const parts = fn.cex.parts ?? ['outcome'];
    const pv = (o, pt) => pt === 'outcome' ? o.outcome : /arg/.test(pt) ? `args ${o.args.join(' | ')}` : pt === 'console' ? `console ${JSON.stringify(o.console)}` : pt;
    evidence = `${fn.cex.inputText}: differs in ${parts.join(', ')}: old ${parts.map(pt => pv(fn.cex.oldObs, pt)).join('; ')} | new ${parts.map(pt => pv(fn.cex.newObs, pt)).join('; ')}; plain-node replay ${rp ? rp.agree : 'missing'}`;
    if (!(fn.confirmedBy ?? []).includes('lean')) {
      const mm = (fn.notes ?? []).find(n => /LEAN\/NODE MISMATCH/.test(n));
      const panic = mm && /\[PANIC ([^\]]*)\]/.exec(mm);
      reason = clean(!provable.has(line) ? 'outside the subset (not provable)'
        : panic ? `Lean: designed panic (${panic[1]}) where Node goes on`
        : mm && /external call/.test(mm) ? 'Lean: external call without a recorded answer in the confirmation run'
        : (fn.notes ?? []).find(n => /Lean confirmation/.test(n)) ?? 'no Lean confirmation recorded');
    }
  } else { cat = 'UNKNOWN'; reason = clean([...(fn.reasons ?? [])].join('; ')); }
  const inst = clean((fn?.notes ?? []).find(n => /^generic: compared at/.test(n)) ?? '');
  const domain = [(fn?.notes ?? []).some(n => /__difftool_compat/.test(n)) ? "old version's parameter types (compat wrapper)" : '',
    (fn?.notes ?? []).some(n => /__difftool_ret/.test(n)) ? `${(fn?.notes ?? []).some(n => /around the old version/.test(n)) ? 'new' : 'old'} version's return type (return wrapper)` : ''].filter(Boolean).join('; ');
  const statement = fn?.verdict === 'PROVED' ? fn.proof.statement : '';
  rows.push({ id, dir, commit: meta.commit.slice(0, 10), date: meta.date, type, intent: intent(type), fn: meta.function, file: meta.file, provable: provable.has(line) ? 'yes' : 'no', cat, statement, evidence: String(evidence).replace(/[\t\n]+/g, ' '), reason, inst, domain, subject: clean(meta.subject) });
}
const cols = ['id', 'commit', 'date', 'type', 'intent', 'fn', 'file', 'provable', 'cat', 'statement', 'evidence', 'reason', 'inst', 'domain', 'subject'];
fs.writeFileSync(path.join(r6, process.env.TABLE_NAME || 'r6_table.tsv'), [cols.join('\t'), ...rows.map(r => cols.map(c => r[c]).join('\t'))].join('\n') + '\n');

const count = (rs, f) => rs.reduce((m, r) => (m[f(r)] = (m[f(r)] ?? 0) + 1, m), {});
const cats = ['PROVED', 'OLD-NO-PANIC (not an equivalence)', 'REFUTED (Lean-confirmed)', 'REFUTED (Node only)', 'UNKNOWN', 'UNCHANGED', 'NO RESULT'];
const catOf = r => r.statement === 'old-no-panic' ? 'OLD-NO-PANIC (not an equivalence)' : r.cat.startsWith('PROVED') ? 'PROVED' : r.cat;
const table = (rs, title) => {
  const out = [`### ${title}`, '', `| intent | pairs | ${cats.join(' | ')} |`, `|---|---:|${cats.map(() => '---:').join('|')}|`];
  for (const it of ['preserve', 'change', 'other', 'all']) {
    const sub = it === 'all' ? rs : rs.filter(r => r.intent === it);
    const c = count(sub, catOf);
    out.push(`| ${it} | ${sub.length} | ${cats.map(k => c[k] ?? 0).join(' | ')} |`);
  }
  return out.join('\n');
};
const md = ['# R6 draft tables', '',
  table(rows, `All ${rows.length} testable pairs`), '',
  table(rows.filter(r => r.provable === 'yes'), `The ${rows.filter(r => r.provable === 'yes').length} provable pairs`), '',
  '### PROVED by statement', '', ...Object.entries(count(rows.filter(r => r.cat.startsWith('PROVED')), r => r.cat)).map(([k, v]) => `- ${k}: ${v}`), '',
  '### UNKNOWN reasons (provable pairs)', '', ...Object.entries(count(rows.filter(r => r.provable === 'yes' && r.cat === 'UNKNOWN'), r => r.reason.replace(/\(.*$/, '').slice(0, 90))).sort((a, b) => b[1] - a[1]).map(([k, v]) => `- ${v}: ${k}`), '',
  '### Refutations in commits whose type promises the same behaviour (refactor/perf/style/chore)', '',
  ...rows.filter(r => r.intent === 'preserve' && r.cat.startsWith('REFUTED')).map(r => `- ${r.commit} ${r.type} \`${r.fn}\` (${r.cat}): ${r.evidence} — "${r.subject}"`), ''];
fs.writeFileSync(path.join(r6, process.env.DRAFT_NAME || 'R6_RESULTS_draft.md'), md.join('\n') + '\n');
console.log(`report: ${rows.length} rows; ${JSON.stringify(count(rows, catOf))}`);

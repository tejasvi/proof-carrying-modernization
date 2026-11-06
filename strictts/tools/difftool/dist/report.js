"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.toJSON = toJSON;
exports.diffWindow = diffWindow;
exports.evidence = evidence;
exports.table = table;
exports.details = details;
const util_1 = require("./util");
function toJSON(reports) {
    return reports.map(r => {
        const { ctx, ...rest } = r;
        void ctx;
        return rest;
    });
}
function pad(s, n) { return s.length >= n ? s : s + ' '.repeat(n - s.length); }
/** Windows of two long texts around their first difference. */
function diffWindow(a, b, width = 110) {
    if (a.length <= width && b.length <= width)
        return [a, b];
    let i = 0;
    while (i < a.length && i < b.length && a[i] === b[i])
        i++;
    const from = Math.max(0, i - 40);
    const cut = (s) => (from > 0 ? '…' : '') + s.slice(from, from + width) + (s.length > from + width ? '…' : '');
    return [cut(a), cut(b)];
}
function evidence(r) {
    if (r.status !== 'changed')
        return '';
    if (r.verdict === 'REFUTED' && r.cex) {
        const conf = (r.confirmedBy ?? []).includes('lean') ? 'confirmed by Lean' : 'Node only';
        const [o, n] = diffWindow(r.cex.old, r.cex.new);
        return `${(0, util_1.truncate)(r.cex.inputText, 100)}: old ${o} | new ${n} [${r.cex.parts.join(', ')}; ${conf}]`;
    }
    if (r.verdict === 'PROVED' && r.proof)
        return `${r.proof.theorem} in ${r.proof.file}${r.proof.statement === 'observational' ? ' (observational: equal up to fresh cells)' : ''}`;
    return r.reasons.join('; ');
}
function table(reports) {
    const rows = reports.filter(r => r.status === 'changed');
    const w = Math.min(48, Math.max(8, ...rows.map(r => r.key.length)));
    const out = [];
    out.push(`${pad('function', w)}  ${pad('verdict', 9)}  evidence`);
    out.push(`${'-'.repeat(w)}  ${'-'.repeat(9)}  ${'-'.repeat(40)}`);
    for (const r of rows) {
        const v = (r.verdict ?? 'UNKNOWN') + (r.verdict === 'REFUTED' && !(r.confirmedBy ?? []).includes('lean') ? '*' : '');
        out.push(`${pad((0, util_1.truncate)(r.key, w), w)}  ${pad(v, 9)}  ${evidence(r)}`);
    }
    const added = reports.filter(r => r.status === 'added').map(r => r.key);
    const removed = reports.filter(r => r.status === 'removed').map(r => r.key);
    if (added.length)
        out.push(`added: ${added.join(', ')}`);
    if (removed.length)
        out.push(`removed: ${removed.join(', ')}`);
    const cnt = (v) => rows.filter(r => r.verdict === v).length;
    out.push(`${rows.length} changed: ${cnt('PROVED')} PROVED, ${cnt('REFUTED')} REFUTED (${rows.filter(r => r.verdict === 'REFUTED' && (r.confirmedBy ?? []).includes('lean')).length} confirmed by Lean), ${cnt('UNKNOWN')} UNKNOWN` +
        (rows.some(r => r.verdict === 'REFUTED' && !(r.confirmedBy ?? []).includes('lean')) ? '   (* = counterexample confirmed in Node only)' : ''));
    return out.join('\n');
}
function details(reports) {
    const out = [];
    for (const r of reports.filter(x => x.status === 'changed')) {
        out.push(`\n== ${r.key}: ${r.verdict}`);
        if (r.cex) {
            out.push(`  input:  ${r.cex.inputText}`);
            out.push(`  old:    ${r.cex.old}`);
            out.push(`  new:    ${r.cex.new}`);
            if (r.cex.lean) {
                out.push(`  lean old: ${JSON.stringify(r.cex.lean.old)}`);
                out.push(`  lean new: ${JSON.stringify(r.cex.lean.new)}`);
            }
        }
        if (r.proof)
            out.push(`  theorem ${r.proof.theorem} (${r.proof.file}); axioms: ${r.proof.axioms.join(', ') || 'none'}`);
        for (const x of r.reasons)
            out.push(`  reason: ${x}`);
        for (const x of r.notes)
            out.push(`  note:   ${x}`);
        if (r.fuzz)
            out.push(`  fuzz:   ${r.fuzz.runs} runs, ${r.fuzz.inconclusive} inconclusive, ${(r.fuzz.ms / 1000).toFixed(1)} s`);
    }
    return out.join('\n');
}

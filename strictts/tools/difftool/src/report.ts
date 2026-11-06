// Human-readable table and JSON output.
import { FnReport } from './diff';
import { truncate } from './util';

export function toJSON(reports: FnReport[]): unknown[] {
  return reports.map(r => {
    const { ctx, ...rest } = r;
    void ctx;
    return rest;
  });
}

function pad(s: string, n: number): string { return s.length >= n ? s : s + ' '.repeat(n - s.length); }

/** Windows of two long texts around their first difference. */
export function diffWindow(a: string, b: string, width = 110): [string, string] {
  if (a.length <= width && b.length <= width) return [a, b];
  let i = 0;
  while (i < a.length && i < b.length && a[i] === b[i]) i++;
  const from = Math.max(0, i - 40);
  const cut = (s: string) => (from > 0 ? '…' : '') + s.slice(from, from + width) + (s.length > from + width ? '…' : '');
  return [cut(a), cut(b)];
}

export function evidence(r: FnReport): string {
  if (r.status !== 'changed') return '';
  if (r.verdict === 'REFUTED' && r.cex) {
    const conf = (r.confirmedBy ?? []).includes('lean') ? 'confirmed by Lean' : 'Node only';
    const [o, n] = diffWindow(r.cex.old, r.cex.new);
    return `${truncate(r.cex.inputText, 100)}: old ${o} | new ${n} [${r.cex.parts.join(', ')}; ${conf}]`;
  }
  if (r.verdict === 'PROVED' && r.proof) return `${r.proof.theorem} in ${r.proof.file}${r.proof.statement === 'observational' ? ' (observational: equal up to fresh cells)' : ''}`;
  return r.reasons.join('; ');
}

export function table(reports: FnReport[]): string {
  const rows = reports.filter(r => r.status === 'changed');
  const w = Math.min(48, Math.max(8, ...rows.map(r => r.key.length)));
  const out: string[] = [];
  out.push(`${pad('function', w)}  ${pad('verdict', 9)}  evidence`);
  out.push(`${'-'.repeat(w)}  ${'-'.repeat(9)}  ${'-'.repeat(40)}`);
  for (const r of rows) {
    const v = (r.verdict ?? 'UNKNOWN') + (r.verdict === 'REFUTED' && !(r.confirmedBy ?? []).includes('lean') ? '*' : '');
    out.push(`${pad(truncate(r.key, w), w)}  ${pad(v, 9)}  ${evidence(r)}`);
  }
  const added = reports.filter(r => r.status === 'added').map(r => r.key);
  const removed = reports.filter(r => r.status === 'removed').map(r => r.key);
  if (added.length) out.push(`added: ${added.join(', ')}`);
  if (removed.length) out.push(`removed: ${removed.join(', ')}`);
  const cnt = (v: string) => rows.filter(r => r.verdict === v).length;
  out.push(`${rows.length} changed: ${cnt('PROVED')} PROVED, ${cnt('REFUTED')} REFUTED (${rows.filter(r => r.verdict === 'REFUTED' && (r.confirmedBy ?? []).includes('lean')).length} confirmed by Lean), ${cnt('UNKNOWN')} UNKNOWN` +
    (rows.some(r => r.verdict === 'REFUTED' && !(r.confirmedBy ?? []).includes('lean')) ? '   (* = counterexample confirmed in Node only)' : ''));
  return out.join('\n');
}

export function details(reports: FnReport[]): string {
  const out: string[] = [];
  for (const r of reports.filter(x => x.status === 'changed')) {
    out.push(`\n== ${r.key}: ${r.verdict}`);
    if (r.cex) {
      out.push(`  input:  ${r.cex.inputText}`);
      out.push(`  old:    ${r.cex.old}`);
      out.push(`  new:    ${r.cex.new}`);
      if (r.cex.lean) { out.push(`  lean old: ${JSON.stringify(r.cex.lean.old)}`); out.push(`  lean new: ${JSON.stringify(r.cex.lean.new)}`); }
    }
    if (r.proof) out.push(`  theorem ${r.proof.theorem} (${r.proof.file}); axioms: ${r.proof.axioms.join(', ') || 'none'}`);
    for (const x of r.reasons) out.push(`  reason: ${x}`);
    for (const x of r.notes) out.push(`  note:   ${x}`);
    if (r.fuzz) out.push(`  fuzz:   ${r.fuzz.runs} runs, ${r.fuzz.inconclusive} inconclusive, ${(r.fuzz.ms / 1000).toFixed(1)} s`);
  }
  return out.join('\n');
}

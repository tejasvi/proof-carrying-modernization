// Equivalence benchmark: DIR/NN_name/{old.ts,new.ts,expected} where `expected` starts with
// `equivalent` or `different`. All pairs are fuzzed first, then one shared Lean phase runs.
import * as fs from 'fs';
import * as path from 'path';
import { analyzePair, leanPhase, finalize, PipelineOpts, Analysis } from './pipeline';
import { evidence, toJSON } from './report';
import { truncate, writeFile } from './util';

interface BenchRow { name: string; expected: string; desc: string; verdict: string; leanConfirmed: boolean; ok: 'correct' | 'unknown' | 'WRONG'; evidence: string; a: Analysis }

function pairVerdict(a: Analysis): { verdict: string; lean: boolean; ev: string } {
  const ch = a.reports.filter(r => r.status === 'changed');
  if (!ch.length) return { verdict: 'UNCHANGED', lean: false, ev: 'no changed function' };
  const ref = ch.find(r => r.verdict === 'REFUTED');
  if (ref) return { verdict: 'REFUTED', lean: (ref.confirmedBy ?? []).includes('lean'), ev: `${ref.name}: ${evidence(ref)}` };
  if (ch.every(r => r.verdict === 'PROVED')) return { verdict: 'PROVED', lean: false, ev: ch.map(r => `${r.name}: ${evidence(r)}`).join('; ') };
  return { verdict: 'UNKNOWN', lean: false, ev: ch.filter(r => r.verdict !== 'PROVED').map(r => `${r.name}: ${evidence(r)}`).join('; ') };
}

export async function runBench(dir: string, opts: PipelineOpts, json?: string): Promise<number> {
  const root = path.resolve(dir);
  const names = fs.readdirSync(root).filter(d => /^\d+_/.test(d) && fs.existsSync(path.join(root, d, 'old.ts')) && fs.existsSync(path.join(root, d, 'new.ts'))).sort();
  const only = opts.only;
  const rows: BenchRow[] = [];
  const pend: Analysis['pend'] = [];
  for (const [i, name] of names.entries()) {
    if (only && !only.test(name)) continue;
    const exp = fs.readFileSync(path.join(root, name, 'expected'), 'utf8').trim();
    const expected = exp.split(/\s+/)[0];
    const pOpts: PipelineOpts = { ...opts, only: undefined, work: path.join(opts.work, name), log: s => opts.log(`[${name}] ${s}`) };
    const a = await analyzePair(path.join(root, name, 'old.ts'), path.join(root, name, 'new.ts'), pOpts, `b${String(i).padStart(2, '0')}u`);
    pend.push(...a.pend);
    rows.push({ name, expected, desc: exp.slice(expected.length).trim(), verdict: '', leanConfirmed: false, ok: 'unknown', evidence: '', a });
  }
  leanPhase(pend, opts, path.join(opts.work, 'lean'));
  for (const r of rows) {
    finalize(r.a.reports);
    const v = pairVerdict(r.a);
    r.verdict = v.verdict; r.leanConfirmed = v.lean; r.evidence = v.ev;
    if (v.verdict === 'UNKNOWN' || v.verdict === 'UNCHANGED') r.ok = 'unknown';
    else if ((v.verdict === 'PROVED') === (r.expected === 'equivalent')) r.ok = 'correct';
    else r.ok = 'WRONG';
  }
  // table
  const out: string[] = [];
  out.push(`${'pair'.padEnd(34)} ${'expected'.padEnd(10)} ${'verdict'.padEnd(9)} result   evidence`);
  for (const r of rows) {
    const v = r.verdict + (r.verdict === 'REFUTED' && !r.leanConfirmed ? '*' : '');
    out.push(`${r.name.padEnd(34)} ${r.expected.padEnd(10)} ${v.padEnd(9)} ${r.ok.padEnd(8)} ${truncate(r.evidence, 160)}`);
  }
  const eq = rows.filter(r => r.expected === 'equivalent'), ne = rows.filter(r => r.expected === 'different');
  const c = (xs: BenchRow[], v: string) => xs.filter(r => r.verdict === v).length;
  out.push('');
  out.push(`equivalent pairs: ${eq.length}: PROVED ${c(eq, 'PROVED')}, UNKNOWN ${eq.length - c(eq, 'PROVED') - c(eq, 'REFUTED')}, REFUTED (wrong) ${c(eq, 'REFUTED')}`);
  // the statements of the proofs, strongest first (a pair counts under its weakest function)
  const order = ['all-worlds', 'allocated-arguments', 'allocated-arguments-strlen', 'allocated-arguments-objects', 'observational', 'old-no-panic'];
  const stmt = (r: BenchRow) => order[Math.max(...r.a.reports.filter(x => x.status === 'changed').map(x => order.indexOf(x.proof?.statement ?? 'all-worlds')))];
  const proved = eq.filter(r => r.verdict === 'PROVED');
  out.push(`  PROVED by statement: ${order.map(k => `${k} ${proved.filter(r => stmt(r) === k).length}`).join(', ')}`);
  out.push(`non-equivalent pairs: ${ne.length}: REFUTED ${c(ne, 'REFUTED')} (${ne.filter(r => r.verdict === 'REFUTED' && r.leanConfirmed).length} confirmed by Lean), UNKNOWN ${ne.length - c(ne, 'REFUTED') - c(ne, 'PROVED')}, PROVED (wrong) ${c(ne, 'PROVED')}`);
  const wrong = rows.filter(r => r.ok === 'WRONG');
  const decided = rows.filter(r => r.ok !== 'unknown');
  out.push(`precision ${decided.length ? ((decided.length - wrong.length) / decided.length * 100).toFixed(1) : '-'}% (${decided.length - wrong.length}/${decided.length} decided verdicts correct); ` +
    `recall: equivalences ${eq.length ? (c(eq, 'PROVED') / eq.length * 100).toFixed(1) : '-'}%, differences ${ne.length ? (c(ne, 'REFUTED') / ne.length * 100).toFixed(1) : '-'}%; WRONG verdicts: ${wrong.length}${wrong.length ? ' (' + wrong.map(r => r.name).join(', ') + ')' : ''}`);
  process.stdout.write(out.join('\n') + '\n');
  if (json) writeFile(json, JSON.stringify(rows.map(r => ({ name: r.name, expected: r.expected, desc: r.desc, verdict: r.verdict, leanConfirmed: r.leanConfirmed, result: r.ok, evidence: r.evidence, functions: toJSON(r.a.reports) })), null, 2) + '\n');
  return wrong.length ? 1 : 0;
}

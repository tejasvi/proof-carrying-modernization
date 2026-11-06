// `strictts-diff selftest`: runs the interface fixture (test/fixture/{old,new}/lib.ts), checks the
// result against the strictts-diff/v1 schema (validator in interface.ts, enums of
// schema/strictts-diff-v1.schema.json) and against the stable projection test/fixture/expected.json.
import * as fs from 'fs';
import * as path from 'path';
import { runPipeline, PipelineOpts } from './pipeline';
import { toResultV1, validateResultV1, REASON_CODES } from './interface';
import { SCRATCH, timestamp, writeFile } from './util';

const HERE = path.resolve(__dirname, '..');

interface Expected {
  summary: Record<string, number>;
  functions: { key: string; status: string; verdict: string | null; statement?: string; leanConfirmed?: boolean; differs?: string[]; reasonCodes?: string[] }[];
}

export async function runSelftest(opts: PipelineOpts): Promise<number> {
  const fx = path.join(HERE, 'test', 'fixture');
  const work = path.join(SCRATCH, `selftest-${timestamp()}-${process.pid}`);
  const errs: string[] = [];
  // 1. the schema file's enums agree with the validator
  const schema = JSON.parse(fs.readFileSync(path.join(HERE, 'schema', 'strictts-diff-v1.schema.json'), 'utf8'));
  const codes: string[] = schema.$defs?.reasonCode?.enum ?? [];
  if (JSON.stringify([...codes].sort()) !== JSON.stringify([...REASON_CODES].sort())) errs.push('schema file: reasonCode enum differs from interface.ts REASON_CODES');
  const verdicts: unknown[] = schema.$defs?.function?.properties?.verdict?.enum ?? [];
  if (JSON.stringify(verdicts) !== JSON.stringify(['PROVED', 'REFUTED', 'REFUTED*', 'UNKNOWN', null])) errs.push('schema file: verdict enum differs');
  // 2. run the fixture
  const { reports } = await runPipeline(path.join(fx, 'old', 'lib.ts'), path.join(fx, 'new', 'lib.ts'), { ...opts, work, only: undefined });
  const res = toResultV1(reports, { old: 'old/lib.ts', new: 'new/lib.ts', seed: opts.seed, runs: opts.runs, lean: opts.lean, tactic: 'default', tacticWf: 'default' });
  writeFile(path.join(work, 'result.json'), JSON.stringify(res, null, 2) + '\n');
  for (const e of validateResultV1(res)) errs.push(`schema: ${e}`);
  // 3. the stable projection
  const exp: Expected = JSON.parse(fs.readFileSync(path.join(fx, 'expected.json'), 'utf8'));
  for (const [k, n] of Object.entries(exp.summary)) {
    const got = (res.summary as Record<string, number>)[k];
    if (got !== n) errs.push(`summary.${k}: expected ${n}, got ${got}`);
  }
  for (const ef of exp.functions) {
    const f = res.functions.find(x => x.key === ef.key);
    if (!f) { errs.push(`${ef.key}: missing`); continue; }
    if (f.status !== ef.status) errs.push(`${ef.key}: status ${f.status}, expected ${ef.status}`);
    if (f.verdict !== ef.verdict) errs.push(`${ef.key}: verdict ${f.verdict}, expected ${ef.verdict} (${f.reasons.join('; ').slice(0, 200)})`);
    if (ef.statement && f.proof?.statement !== ef.statement) errs.push(`${ef.key}: proof statement ${f.proof?.statement}, expected ${ef.statement}`);
    if (ef.leanConfirmed !== undefined && f.counterexample?.leanConfirmed !== ef.leanConfirmed) errs.push(`${ef.key}: leanConfirmed ${f.counterexample?.leanConfirmed}, expected ${ef.leanConfirmed}`);
    for (const d of ef.differs ?? []) if (!f.counterexample?.differs.includes(d)) errs.push(`${ef.key}: counterexample should differ in ${d}`);
    for (const c of ef.reasonCodes ?? []) if (!f.reasonCodes.includes(c)) errs.push(`${ef.key}: reason code ${c} missing (got ${f.reasonCodes.join(', ')})`);
  }
  const out = errs.length ? `selftest FAIL (${errs.length})\n${errs.map(e => '  ' + e).join('\n')}` : `selftest PASS: ${res.functions.length} functions, schema ${res.schema}, result ${path.join(work, 'result.json')}`;
  process.stdout.write(out + '\n');
  return errs.length ? 1 : 0;
}

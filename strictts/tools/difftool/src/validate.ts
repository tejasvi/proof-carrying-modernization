// Translator validation: every function of a file runs on random inputs under Node and under
// the Lean semantics (the same driver, translated); any difference in the printed output is a
// translator or semantics bug. Mismatches are reduced to a single, shrunk input.
import * as path from 'path';
import { materialize } from './spec';
import { makeProject } from './project';
import { unitsOf, Unit } from './units';
import { sliceUnit, Slice } from './slice';
import { signatureOf, Signature, unsupportedIn } from './typedesc';
import { GenCtx, Input, genInput, boundaryInputs, shrinkInput, inputSize } from './gen';
import { mineLiterals, Runner, initMsg, Obs, conclusive } from './fuzz';
import { driverSlice, runProgramNode, PipelineOpts } from './pipeline';
import { translateSlice, runLeanBatch, EvalJob, Translation } from './lean';
import { callText } from './literal';
import { Rng, mkdirp, writeFile, truncate } from './util';

export interface ValRow {
  file: string;
  name: string;
  status: 'match' | 'MISMATCH' | 'skipped' | 'error';
  inputs: number;
  reason?: string;
  notes?: string;
  repro?: { input: string; node: string; lean: string };
}

interface Job { u: Unit; sl: Slice; sig: Signature; g: GenCtx; inputs: Input[]; dir: string; id: string; nodeBlocks?: string[]; t?: Translation; row: ValRow }

/** Split driver output into per-input blocks (`#k` headers); the final status line is appended to the last block. */
function blocks(out: string): string[] {
  const res: string[] = [];
  let cur: string[] | null = null;
  for (const l of out.replace(/\r/g, '').split('\n')) {
    if (/^#\d+$/.test(l)) { if (cur) res.push(cur.join('\n')); cur = []; continue; }
    if (cur) cur.push(l); else { cur = [l]; }
  }
  if (cur) res.push(cur.join('\n').replace(/\n+$/, ''));
  return res;
}

async function nodeRun(j: Job, inputs: Input[], tag: string): Promise<{ sl: Slice; out: string }> {
  const ds = driverSlice(j.sl, path.join(j.dir, `drv_${tag}`), j.u, j.sig, inputs);
  return { sl: ds, out: await runProgramNode(ds, 20000) };
}

export async function runValidate(files: string[], opts: PipelineOpts, json?: string): Promise<number> {
  const rows: ValRow[] = [];
  const jobs: Job[] = [];
  const perFn = Math.max(5, Math.min(opts.runs, 40));
  let n = 0;
  for (const f of files) {
    const work = path.join(opts.work, path.basename(f).replace(/\.ts$/, '') + '_' + (++n));
    mkdirp(work);
    let set;
    try { set = materialize(f, path.join(work, 'src'), { repo: opts.repo }); }
    catch (e) { rows.push({ file: f, name: '*', status: 'error', inputs: 0, reason: (e as Error).message }); continue; }
    const p = makeProject(set);
    for (const u of set.roots.flatMap(r => unitsOf(p, r, r))) {
      const row: ValRow = { file: f, name: u.name, status: 'skipped', inputs: 0 };
      rows.push(row);
      if (opts.only && !opts.only.test(u.name)) { rows.pop(); continue; }
      if (u.isGeneric) { row.reason = 'generic function'; continue; }
      if (u.isPrivate) { row.reason = 'private method (not callable from a driver)'; continue; }
      const dir = path.join(work, 'units', u.name.replace(/[^A-Za-z0-9_]/g, '_'));
      try {
        const sl = sliceUnit(p, u, path.join(dir, 'slice'));
        if (!sl.ok) { row.reason = sl.reason; continue; }
        const sig = signatureOf(p, u);
        const bad = [...sig.params, ...(sig.self?.ctor ?? [])].map(q => unsupportedIn(q.rest && q.t.k === 'arr' ? q.t.t : q.t, sig.table)).find(x => x);
        if (bad) { row.reason = `inputs not generated (${bad})`; continue; }
        const lits = mineLiterals([...sl.files.values()]);
        const g: GenCtx = { rng: new Rng(opts.seed * 7919 + jobs.length), table: sig.table, nums: lits.nums, strs: lits.strs };
        const inputs: Input[] = [];
        const seen = new Set<string>();
        const add = (i: Input) => { const k = JSON.stringify(i); if (!seen.has(k)) { seen.add(k); inputs.push(i); } };
        try { boundaryInputs(sig, g).slice(0, perFn >> 1).forEach(add); } catch { /* none */ }
        for (let k = 0; inputs.length < perFn && k < perFn * 5; k++) add(genInput(sig, g));
        // keep inputs that finish quickly under Node (the Lean interpreter is much slower; deep
        // recursion and exponential cases would only time out there)
        const runner = new Runner(initMsg({ files: sl.files, entry: sl.entry, exportName: sl.exportName, kind: u.kind, method: u.cls ? u.name.slice(u.cls.length + 1) : undefined }, 500));
        let obs: Obs[];
        try { obs = await runner.run(inputs); } finally { runner.kill(); }
        // resource limits of the engine (V8's maximal string and array lengths) are not part of the semantics
        const limit = (o: Obs) => /Invalid (string|array) length|Array buffer allocation failed/.test(o.o);
        const kept = inputs.filter((_, k) => conclusive(obs[k]) && (obs[k].ms ?? 0) < 50 && !limit(obs[k]));
        const limited = obs.filter(limit).length;
        if (limited) row.notes = `${limited} input(s) hit an engine length limit in Node (not sent to Lean)`;
        if (!kept.length) { row.reason = `no input finishes quickly under Node (${obs[0]?.o ?? '?'})`; continue; }
        jobs.push({ u, sl, sig, g, inputs: kept, dir, id: `v${String(jobs.length).padStart(3, '0')}`, row });
      } catch (e) { row.status = 'error'; row.reason = (e as Error).message; }
    }
  }
  // Node runs and translations
  for (const j of jobs) {
    const r = await nodeRun(j, j.inputs, 'all');
    j.nodeBlocks = blocks(r.out);
    j.t = translateSlice(r.sl.dir, r.sl.entry, `Val_${j.id}`, true);
    if (!j.t.ok) { j.row.status = 'skipped'; j.row.reason = `outside the subset [${j.t.rules.join(', ')}]: ${truncate(j.t.diagnostics.split('\n')[0] ?? '', 160)}`; }
  }
  const ready = jobs.filter(j => j.t?.ok);
  for (let i = 0; i < ready.length; i += opts.leanBatch) {
    const chunk = ready.slice(i, i + opts.leanBatch);
    const evals: EvalJob[] = chunk.map(j => ({ id: j.id, t: j.t! }));
    opts.log(`Lean batch ${i / opts.leanBatch + 1}/${Math.ceil(ready.length / opts.leanBatch)} (${chunk.length} functions)`);
    const res = runLeanBatch(path.join(opts.work, 'lean', `val_${String(i / opts.leanBatch).padStart(2, '0')}.lean`), [], evals, opts.leanTimeoutS);
    if (chunk.length > 1 && chunk.some(j => !res.evals.get(j.id)?.ok)) {
      // a crashed or timed-out batch: one Lean process per function
      for (const j of chunk) {
        const r1 = runLeanBatch(path.join(opts.work, 'lean', `val_${j.id}.lean`), [], [{ id: j.id, t: j.t! }], opts.leanTimeoutS);
        res.evals.set(j.id, r1.evals.get(j.id) ?? { ok: false, out: '', errors: ['no result'] });
      }
    }
    for (const j of chunk) {
      const e = res.evals.get(j.id);
      j.row.inputs = j.inputs.length;
      if (!e || !e.ok) { j.row.status = 'error'; j.row.reason = `lean: ${(e?.errors ?? ['no result']).join(' / ').slice(0, 300)}`; continue; }
      const lb = blocks(e.out);
      const nb = j.nodeBlocks!;
      const k = firstMismatch(nb, lb);
      if (k < 0) { j.row.status = 'match'; continue; }
      j.row.status = 'MISMATCH';
      const bad = j.inputs[Math.min(k, j.inputs.length - 1)];
      j.row.repro = { input: callText(j.u.name, bad.args, bad.self, j.u.cls, j.u.kind), node: nb[k] ?? '<missing>', lean: lb[k] ?? '<missing>' };
      // minimize (a few Lean rounds)
      try { await minimize(j, bad, opts); } catch (err) { j.row.reason = `minimization failed: ${(err as Error).message}`; }
    }
  }
  // report
  const out: string[] = [];
  for (const r of rows) {
    if (r.status === 'MISMATCH') {
      out.push(`MISMATCH ${r.file} ${r.name} (${r.inputs} inputs)\n  input: ${r.repro!.input}\n  node:  ${JSON.stringify(r.repro!.node)}\n  lean:  ${JSON.stringify(r.repro!.lean)}`);
    } else out.push(`${r.status.padEnd(8)} ${r.file} ${r.name}${r.status === 'match' ? ` (${r.inputs} inputs)` : ''}${r.reason ? ' — ' + r.reason : ''}`);
  }
  const cnt = (s: string) => rows.filter(r => r.status === s).length;
  out.push(`\n${rows.length} functions: ${cnt('match')} match, ${cnt('MISMATCH')} MISMATCH, ${cnt('skipped')} skipped, ${cnt('error')} error; ${rows.filter(r => r.status === 'match' || r.status === 'MISMATCH').reduce((s, r) => s + r.inputs, 0)} inputs compared`);
  process.stdout.write(out.join('\n') + '\n');
  if (json) writeFile(json, JSON.stringify(rows, null, 2) + '\n');
  return cnt('MISMATCH') ? 1 : 0;
}

function firstMismatch(a: string[], b: string[]): number {
  for (let k = 0; k < Math.max(a.length, b.length); k++) if ((a[k] ?? '') !== (b[k] ?? '')) return k;
  return -1;
}

async function minimize(j: Job, start: Input, opts: PipelineOpts): Promise<void> {
  let best = start;
  for (let round = 0; round < 6; round++) {
    const cands = shrinkInput(j.sig, best, j.g).filter(c => inputSize(c) < inputSize(best)).slice(0, 24);
    if (!cands.length) break;
    const r = await nodeRun(j, cands, `min${round}`);
    const t = translateSlice(r.sl.dir, r.sl.entry, `ValMin_${j.id}_${round}`, true);
    if (!t.ok) break;
    const res = runLeanBatch(path.join(opts.work, 'lean', `min_${j.id}_${round}.lean`), [], [{ id: 'm', t }], opts.leanTimeoutS);
    const e = res.evals.get('m');
    if (!e?.ok) break;
    const nb = blocks(r.out), lb = blocks(e.out);
    let found = -1;
    for (let k = 0; k < cands.length; k++) if ((nb[k] ?? '') !== (lb[k] ?? '')) { found = k; break; }
    if (found < 0) break;
    best = cands[found];
    j.row.repro = { input: callText(j.u.name, best.args, best.self, j.u.cls, j.u.kind), node: nb[found], lean: lb[found] };
  }
}

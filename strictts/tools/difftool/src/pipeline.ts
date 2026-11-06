// End-to-end: materialize OLD and NEW, pair functions, fuzz each changed one, then a batched
// Lean stage (confirmation runs for counterexamples, equivalence theorems otherwise).
import * as fs from 'fs';
import * as path from 'path';
import { materialize, FileSet } from './spec';
import { makeProject } from './project';
import { pairUnits, prepare, fuzzUnit, proofSlices, monoWrapper, MONO_NAME, compatWrapper, COMPAT_NAME, retWrapper, RET_NAME, FnReport, DiffOpts, ObsView } from './diff';
import { signatureOf, Signature } from './typedesc';
import { driverSource } from './driver';
import { callText } from './literal';
import { Runner, initMsg, Obs } from './fuzz';
import { translateSlice, runLeanBatch, theoremFor, aliasNewTypes, DEFAULT_SCRIPT, DEFAULT_SCRIPT_WF, OBS_SCRIPT, Translation, EvalJob, LeanBatchResult, leanAvailable } from './lean';
import { mkdirp, writeFile } from './util';
import { Slice } from './slice';
import { Unit } from './units';
import { Input, Tagged } from './gen';

export interface PipelineOpts extends DiffOpts {
  repo: string;
  lean: boolean;
  script: string;
  /** proof script of the allocated-arguments statement */
  scriptWf: string;
  heartbeats: number;
  leanTimeoutS: number;
  leanBatch: number;
  log: (s: string) => void;
}

export const DEFAULTS = {
  runs: 1500, seed: 1, timeoutMs: 1000, shrinkBudget: 400, lean: true, script: DEFAULT_SCRIPT, scriptWf: DEFAULT_SCRIPT_WF, heartbeats: 400000,
  leanTimeoutS: 400, leanBatch: 8,
};

/** Copy of a slice with a driver appended to its entry file. */
/** Class names used by tagged input values. */
function classesIn(t: Tagged | null, out: Set<string>): void {
  if (!t) return;
  switch (t.t) {
    case 'c': out.add(t.cls); t.args.forEach(a => classesIn(a, out)); break;
    case 'a': case 'S': case 'ta': t.v.forEach(a => classesIn(a, out)); break;
    case 'o': t.v.forEach(([, a]) => classesIn(a, out)); break;
    case 'm': t.v.forEach(([k, a]) => { classesIn(k, out); classesIn(a, out); }); break;
    case 'p': classesIn(t.v, out); break;
  }
}

export function driverSlice(sl: Slice, dir: string, u: Unit, sig: Signature, inputs: Input[]): Slice {
  fs.rmSync(dir, { recursive: true, force: true });
  const files = new Map(sl.files);
  const entryText = files.get(sl.entry) ?? '';
  // classes built by the inputs but declared in another file of the slice are imported
  const cls = new Set<string>();
  for (const inp of inputs) { inp.args.forEach(a => classesIn(a, cls)); (inp.self ?? []).forEach(a => classesIn(a, cls)); }
  const imports: string[] = [];
  for (const c of cls) {
    const decl = new RegExp(`\\bclass\\s+${c}\\b`);
    if (decl.test(entryText)) continue;
    const home = [...files.keys()].find(f => decl.test(files.get(f)!));
    if (!home) continue;
    let rel = path.posix.relative(path.posix.dirname(sl.entry), home).replace(/\.tsx?$/, '');
    if (!rel.startsWith('.')) rel = './' + rel;
    imports.push(`import { ${c} } from ${JSON.stringify(rel)};`);
  }
  files.set(sl.entry, entryText + imports.map(i => '\n' + i).join('') + driverSource(u, sig, inputs));
  for (const [rel, text] of files) writeFile(path.join(dir, rel), text);
  return { ...sl, dir, files };
}

export async function runProgramNode(sl: Slice, timeoutMs = 5000): Promise<string> {
  const r = new Runner(initMsg({ files: sl.files, entry: sl.entry, exportName: '', kind: 'program' }, timeoutMs));
  try {
    const [o] = await r.run([{ args: [] }]);
    return programText(o);
  } finally { r.kill(); }
}

export function programText(o: Obs): string {
  if (o.kind !== 'ok') return [...o.out, `[${o.o}]`].join('\n');
  const st = o.unhandled.length && o.o === '[ok]' ? `[uncaught ${o.unhandled[0]}]` : o.o;
  return [...o.out, st].join('\n');
}

function lines(s: string): string[] {
  return s.replace(/\r/g, '').split('\n').filter((l, i, a) => !(i === a.length - 1 && l === ''));
}

export interface Pending {
  r: FnReport;
  kind: 'confirm' | 'proof';
  oldT?: Translation;
  newT?: Translation;
  nodeOld?: string;
  nodeNew?: string;
  theorem?: string;
  /** the statement for worlds with allocated argument arrays (when the function takes some) */
  theoremWf?: string;
  /** the same with string arguments within the maximum String length (when it takes strings) */
  theoremWfs?: string;
  /** the same with allocated object arguments and their array fields (when it takes objects) */
  theoremWfo?: string;
  /** the observational statement (results without references or arrays of such values; no async work) */
  theoremObs?: string;
  /** the statement where the old version does not panic (equal runs, or the old run panics) */
  theoremNp?: string;
}

export interface Analysis { reports: FnReport[]; pend: (Pending & { id: string })[]; oldSet: FileSet; newSet: FileSet }

/** Materialize, pair, slice, fuzz and prepare the Lean jobs of one OLD/NEW pair. */
export async function analyzePair(oldSpec: string, newSpec: string, opts: PipelineOpts, idPrefix = 'u'): Promise<Analysis> {
  mkdirp(opts.work);
  const oldSet = materialize(oldSpec, path.join(opts.work, 'src_old'), { repo: opts.repo });
  const newSet = materialize(newSpec, path.join(opts.work, 'src_new'), { repo: opts.repo });
  const oldP = makeProject(oldSet), newP = makeProject(newSet);
  const reports = pairUnits(oldP, newP, opts);
  const changed = reports.filter(r => r.status === 'changed');
  opts.log(`${changed.length} changed function(s), ${reports.filter(r => r.status === 'added').length} added, ${reports.filter(r => r.status === 'removed').length} removed`);
  const pend: (Pending & { id: string })[] = [];
  const useLean = opts.lean && leanAvailable();
  if (opts.lean && !useLean) opts.log('Lean build not found (lake build StrictTS): Lean stage skipped');
  let idx = 0;
  for (const r of changed) {
    idx++;
    const c = r.ctx!;
    const id = `${idPrefix}${String(idx).padStart(3, '0')}`;
    opts.log(`[${idx}/${changed.length}] ${r.key}`);
    let canFuzz = false;
    try { canFuzz = prepare(r, oldP, newP); }
    catch (e) { r.reasons.push(`slicing: ${(e as Error).message}`); }
    if (canFuzz) await fuzzUnit(r, opts);
    const f = c.fuzz;
    if (f?.status === 'diff' && f.cex) {
      const cx = f.cex;
      r.cex = {
        input: cx.input, inputText: callText(r.name, cx.input.args, cx.input.self, c.oldUnit.cls, c.oldUnit.kind),
        old: describeObs(cx.old, cx.new), new: describeObs(cx.new, cx.old), parts: cx.parts,
        oldObs: obsView(cx.old), newObs: obsView(cx.new),
      };
      r.verdict = 'REFUTED';
      r.confirmedBy = ['node'];
      if (useLean) {
        // confirmation: the same call through a driver, under Node and under the Lean semantics
        try {
          const newSig = signatureOf(newP, c.newUnit);
          const od = driverSlice(c.oldSlice!, path.join(c.dir, 'old_drv'), c.oldUnit, c.sig!, [cx.input]);
          const nd = driverSlice(c.newSlice!, path.join(c.dir, 'new_drv'), c.newUnit, newSig, [cx.input]);
          const p: Pending & { id: string } = { r, kind: 'confirm', id };
          p.nodeOld = await runProgramNode(od);
          p.nodeNew = await runProgramNode(nd);
          p.oldT = translateSlice(od.dir, od.entry, `OldC_${id}`, true);
          p.newT = translateSlice(nd.dir, nd.entry, `NewC_${id}`, true);
          if (p.oldT.ok && p.newT.ok) pend.push(p);
          else r.notes.push(`Lean confirmation not run: ${!p.oldT.ok ? 'old' : 'new'} driver outside the subset [${(!p.oldT.ok ? p.oldT : p.newT).rules.join(', ')}]: ${firstDiag((!p.oldT.ok ? p.oldT : p.newT).diagnostics)}`);
        } catch (e) { r.notes.push(`Lean confirmation not run: ${(e as Error).message}`); }
      }
      continue;
    }
    // no counterexample: attempt a proof
    if (!c.oldSlice?.ok || !c.newSlice?.ok) { r.verdict = 'UNKNOWN'; continue; }
    if (!useLean) { r.verdict = 'UNKNOWN'; r.reasons.push('no counterexample found; Lean stage disabled'); continue; }
    try {
      proofSlices(r);
      let target = c.oldUnit.name;
      if (c.oldUnit.isGeneric || c.newUnit.isGeneric) {
        const mo = monoWrapper(c.oldUnit, c.oldProof!), mn = monoWrapper(c.newUnit, c.newProof!);
        if ('error' in mo || 'error' in mn) { r.reasons.push(('error' in mo ? mo : mn as { error: string }).error); r.verdict = 'UNKNOWN'; continue; }
        // instances that differ in their type parameters (or one version not generic) are compared when
        // the two wrappers' translated signatures agree; otherwise the compat wrappers below are tried
        r.notes.push(`generic: compared at the instance ${mo.inst === mn.inst ? mo.inst : !mn.inst ? `${mo.inst}; the new version is not generic` : !mo.inst ? `${mn.inst}; the old version is not generic` : `${mo.inst} (old) and ${mn.inst} (new)`} (wrapper ${MONO_NAME})`);
        target = MONO_NAME;
      }
      const oldT = translateSlice(c.oldProof!.dir, c.oldProof!.entry, `Old_${id}`, false);
      const newT = translateSlice(c.newProof!.dir, c.newProof!.entry, `New_${id}`, false);
      if (c.oldProof!.inlined.length || c.newProof!.inlined.length) r.notes.push(`inlined module constants: ${[...new Set([...c.oldProof!.inlined, ...c.newProof!.inlined])].join(', ')}`);
      if (!oldT.ok || !newT.ok) {
        const rules = [...new Set([...oldT.rules, ...newT.rules])];
        r.reasons.push(`outside the StrictTS subset: ${rules.join(', ')}${!oldT.ok ? ` (old: ${firstDiag(oldT.diagnostics)})` : ''}${!newT.ok ? ` (new: ${firstDiag(newT.diagnostics)})` : ''}`);
        r.verdict = 'UNKNOWN';
        continue;
      }
      if (oldT.moduleState !== newT.moduleState) { r.reasons.push('module-level state (globals or their initialisers) differs between the versions; no ∀-world theorem'); r.verdict = 'UNKNOWN'; continue; }
      let thm = theoremFor({ id, oldT, newT, target, script: opts.script, scriptWf: opts.scriptWf, heartbeats: opts.heartbeats });
      let newTp = newT;
      // a widened parameter list: compare on the old version's inputs, through a wrapper in the new slice
      // (for a generic function: the old wrapper's instance against the new version called at it)
      if ('error' in thm && /^translated signatures differ/.test(thm.error)) {
        const why = thm.error;
        const cw = compatWrapper(c.oldUnit, c.newUnit.name, c.newProof!);
        const t2 = 'error' in cw ? null : translateSlice(c.newProof!.dir, c.newProof!.entry, `New_${id}`, false);
        if (t2 && t2.ok && t2.moduleState === oldT.moduleState) {
          const thm2 = theoremFor({ id, oldT, newT: t2, target, targetNew: COMPAT_NAME, script: opts.script, scriptWf: opts.scriptWf, heartbeats: opts.heartbeats });
          if (!('error' in thm2)) {
            thm = thm2; newTp = t2;
            r.notes.push(`compared on the old version's inputs (wrapper ${COMPAT_NAME}): ${why.replace(/^translated signatures differ/, 'the signature widened')}`);
          }
        }
      }
      let oldTp = oldT;
      // a changed return type (T to T | undefined, a type widened to unknown): compare at the other
      // version's return type, through a wrapper of one version declared with it (first the old one)
      if ('error' in thm && /^translated signatures differ/.test(thm.error)) {
        const why = thm.error;
        for (const side of ['old', 'new'] as const) {
          const [u, other, sl] = side === 'old' ? [c.oldUnit, c.newUnit, c.oldProof!] : [c.newUnit, c.oldUnit, c.newProof!];
          if ('error' in retWrapper(u, other, sl)) continue;
          const tw = translateSlice(sl.dir, sl.entry, `${side === 'old' ? 'Old' : 'New'}_${id}`, false);
          const [o, n] = side === 'old' ? [tw, newT] : [oldT, tw];
          if (!tw.ok || o.moduleState !== n.moduleState) continue;
          const thm3 = theoremFor({ id, oldT: o, newT: n, target: side === 'old' ? RET_NAME : target, targetNew: side === 'old' ? target : RET_NAME, script: opts.script, scriptWf: opts.scriptWf, heartbeats: opts.heartbeats });
          if ('error' in thm3) continue;
          thm = thm3; oldTp = o; newTp = n;
          r.notes.push(`compared at the ${side === 'old' ? 'new' : 'old'} version's return type (wrapper ${RET_NAME} around the ${side} version): ${why.replace(/^translated signatures differ/, 'the return type changed')}`);
          break;
        }
      }
      if ('error' in thm) { r.reasons.push(thm.error); r.verdict = 'UNKNOWN'; continue; }
      pend.push({ r, kind: 'proof', oldT: oldTp, newT: newTp, theorem: thm.main, theoremWf: thm.wf, theoremWfs: thm.wfs, theoremWfo: thm.wfo, theoremObs: thm.obs, theoremNp: thm.np, id });
    } catch (e) { r.reasons.push(`Lean preparation: ${(e as Error).message}`); r.verdict = 'UNKNOWN'; }
  }
  return { reports, pend, oldSet, newSet };
}

/** Lean blocks of a proof job: the translations with the main theorem, then the allocated-arguments
theorems (without and with the string-length hypotheses). */
function proofBlocks(p: Pending & { id: string }): { id: string; text: string }[] {
  const out = [{ id: p.id, text: p.oldT!.body + '\n' + aliasNewTypes(p.oldT!.body, p.newT!.body, p.oldT!.ns) + '\n' + p.theorem! }];
  if (p.theoremWf) out.push({ id: p.id + '_wf', text: p.theoremWf });
  if (p.theoremWfs) out.push({ id: p.id + '_wfs', text: p.theoremWfs });
  if (p.theoremWfo) out.push({ id: p.id + '_wfo', text: p.theoremWfo });
  return out;
}

/** Lean blocks of the weaker statements (second pass): the observational statement and the one where
the old version does not panic, each with the translations. */
function weakBlocks(p: Pending & { id: string }): { id: string; text: string }[] {
  const tr = p.oldT!.body + '\n' + aliasNewTypes(p.oldT!.body, p.newT!.body, p.oldT!.ns) + '\n';
  // the translations once, in the first block (a later block uses them)
  return [...(p.theoremObs ? [{ id: p.id + '_obs', text: tr + p.theoremObs }] : []),
    ...(p.theoremNp ? [{ id: p.id + '_np', text: (p.theoremObs ? '' : tr) + p.theoremNp }] : [])];
}

/** Ids of the equality statements of a proof job. */
function eqIds(p: Pending & { id: string }): string[] {
  return [p.id, ...(p.theoremWf ? [p.id + '_wf'] : []), ...(p.theoremWfs ? [p.id + '_wfs'] : []), ...(p.theoremWfo ? [p.id + '_wfo'] : [])];
}

const lost = (res: LeanBatchResult, id: string) => (res.proofs.get(id)?.errors ?? ['no result']).some(e => /theorem not checked|no output|timed out/.test(e));

/** Run the Lean jobs in batches (one Lean process per batch; a timed-out batch is retried unit by
unit), then, in a second pass, the observational statements of the functions for which no
equality statement was proved. */
export function leanPhase(pend: (Pending & { id: string })[], opts: PipelineOpts, leanDir: string): void {
  const later: { p: Pending & { id: string }; res: LeanBatchResult }[] = [];
  const finish = (p: Pending & { id: string }, res: LeanBatchResult) => {
    if (p.kind === 'proof' && (p.theoremObs || p.theoremNp) && !eqIds(p).some(id => res.proofs.get(id)?.ok)) later.push({ p, res });
    else finishPending(p, res, opts);
  };
  for (let i = 0; i < pend.length; i += opts.leanBatch) {
    const chunk = pend.slice(i, i + opts.leanBatch);
    const evals: EvalJob[] = [];
    const proofs: { id: string; text: string }[] = [];
    for (const p of chunk) {
      if (p.kind === 'confirm') { evals.push({ id: p.id + 'o', t: p.oldT! }, { id: p.id + 'n', t: p.newT! }); }
      else proofs.push(...proofBlocks(p));
    }
    const file = path.join(leanDir, `batch_${String(i / opts.leanBatch).padStart(2, '0')}.lean`);
    opts.log(`Lean batch ${i / opts.leanBatch + 1}/${Math.ceil(pend.length / opts.leanBatch)}: ${evals.length / 2} confirmation(s), ${proofs.length} proof(s)`);
    const res = runLeanBatch(file, proofs, evals, opts.leanTimeoutS);
    opts.log(`  ${res.secs.toFixed(1)} s${res.timedOut ? ' (timed out)' : ''}`);
    // a timed-out or crashed batch (e.g. Lean out of memory) is retried unit by unit
    const crashed = chunk.some(p => p.kind === 'confirm'
      ? !(res.evals.get(p.id + 'o')?.ok && res.evals.get(p.id + 'n')?.ok)
      : eqIds(p).some(id => lost(res, id)));
    if ((res.timedOut || crashed) && chunk.length > 1) {
      for (const p of chunk) {
        const f1 = path.join(leanDir, `unit_${p.id}.lean`);
        const r1 = p.kind === 'confirm'
          ? runLeanBatch(f1, [], [{ id: p.id + 'o', t: p.oldT! }, { id: p.id + 'n', t: p.newT! }], opts.leanTimeoutS)
          : runLeanBatch(f1, proofBlocks(p), [], opts.leanTimeoutS);
        for (const [k, v] of r1.proofs) res.proofs.set(k, v);
        for (const [k, v] of r1.evals) res.evals.set(k, v);
        if (p.kind === 'proof') res.file = f1;
        finish(p, { ...res, file: f1 });
      }
      continue;
    }
    for (const p of chunk) finish(p, res);
  }
  for (let i = 0; i < later.length; i += opts.leanBatch) {
    const chunk = later.slice(i, i + opts.leanBatch);
    const file = path.join(leanDir, `obs_${String(i / opts.leanBatch).padStart(2, '0')}.lean`);
    opts.log(`Lean observational batch ${i / opts.leanBatch + 1}/${Math.ceil(later.length / opts.leanBatch)}: ${chunk.length} proof(s)`);
    const res = runLeanBatch(file, chunk.flatMap(x => weakBlocks(x.p)), [], opts.leanTimeoutS);
    opts.log(`  ${res.secs.toFixed(1)} s${res.timedOut ? ' (timed out)' : ''}`);
    for (const x of chunk) {
      let r1 = res;
      const ids = weakBlocks(x.p).map(b => b.id);
      // a unit lost in a timed-out or crashed batch is retried alone
      if (chunk.length > 1 && ids.some(id => lost(res, id))) {
        const f1 = path.join(leanDir, `unit_${x.p.id}_obs.lean`);
        r1 = runLeanBatch(f1, weakBlocks(x.p), [], opts.leanTimeoutS);
      }
      for (const id of ids) {
        const o = r1.proofs.get(id);
        if (o) x.res.proofs.set(id, o);
      }
      finishPending(x.p, x.res, opts, r1.file);
    }
  }
}

export function finalize(reports: FnReport[]): void {
  for (const r of reports.filter(x => x.status === 'changed')) {
    if (!r.verdict) r.verdict = 'UNKNOWN';
    if (r.verdict === 'UNKNOWN' && !r.reasons.length && r.ctx?.fuzz?.status === 'same') r.reasons.push(`no counterexample in ${r.ctx.fuzz.runs} runs; no proof`);
  }
}

export async function runPipeline(oldSpec: string, newSpec: string, opts: PipelineOpts): Promise<Analysis> {
  const a = await analyzePair(oldSpec, newSpec, opts);
  leanPhase(a.pend, opts, path.join(opts.work, 'lean'));
  finalize(a.reports);
  return a;
}

function firstDiag(d: string): string {
  const l = d.split('\n').find(x => x.trim()) ?? '';
  return l.length > 200 ? l.slice(0, 200) + '…' : l;
}

function obsView(o: Obs): ObsView {
  return { outcome: o.o, console: o.out, args: o.args, receiver: o.self ?? null, unhandled: o.unhandled };
}

/** The observation, restricted to the outcome and the parts that differ from `other`. */
function describeObs(o: Obs, other: Obs): string {
  const parts = [o.o];
  if (o.out.join('\n') !== other.out.join('\n')) parts.push(`console ${JSON.stringify(o.out)}`);
  if (o.args.join('\u0001') !== other.args.join('\u0001')) parts.push(`args after (${o.args.join(', ')})`);
  if ((o.self ?? '') !== (other.self ?? '')) parts.push(`this after ${o.self}`);
  if (o.unhandled.join('\n') !== other.unhandled.join('\n')) parts.push(`unhandled ${o.unhandled.join('; ') || 'none'}`);
  return parts.join('; ');
}

function finishPending(p: Pending & { id: string }, res: ReturnType<typeof runLeanBatch>, opts: PipelineOpts, obsFile?: string): void {
  const r = p.r;
  if (p.kind === 'confirm') {
    const eo = res.evals.get(p.id + 'o'), en = res.evals.get(p.id + 'n');
    if (!eo?.ok || !en?.ok) { r.notes.push(`Lean confirmation failed to run: ${(eo?.errors ?? en?.errors ?? ['?']).join(' / ').slice(0, 300)}`); return; }
    const lo = lines(eo.out).join('\n'), ln = lines(en.out).join('\n');
    const no = lines(p.nodeOld!).join('\n'), nn = lines(p.nodeNew!).join('\n');
    r.cex!.lean = { old: lo, new: ln };
    if (lo !== no || ln !== nn) {
      r.notes.push(`LEAN/NODE MISMATCH on the driver (translator or semantics bug): ${lo !== no ? `old: node ${JSON.stringify(no)} lean ${JSON.stringify(lo)}` : `new: node ${JSON.stringify(nn)} lean ${JSON.stringify(ln)}`}`);
      return;
    }
    if (lo === ln) { r.notes.push('Lean confirmation inconclusive: the driver does not print the differing part (e.g. object identity or private state)'); return; }
    r.confirmedBy = ['node', 'lean'];
    return;
  }
  const pr = res.proofs.get(p.id);
  if (!pr) { r.reasons.push('proof: no result'); r.verdict = 'UNKNOWN'; return; }
  const pw = p.theoremWf ? res.proofs.get(p.id + '_wf') : undefined;
  const ps = p.theoremWfs ? res.proofs.get(p.id + '_wfs') : undefined;
  const po = p.theoremWfo ? res.proofs.get(p.id + '_wfo') : undefined;
  const pb = p.theoremObs ? res.proofs.get(p.id + '_obs') : undefined;
  const pn = p.theoremNp ? res.proofs.get(p.id + '_np') : undefined;
  const residual = (x: typeof pr) => (x.errors.find(e => e.includes('difftool: residual goal')) ?? x.goals[0] ?? '').slice(0, 4000) || undefined;
  // the strongest statement checked: every world, allocated arguments, then also string lengths,
  // object arguments; then the observational statement (weaker: equality up to fresh cells), last
  // equality where the old version does not panic
  const kind: NonNullable<FnReport['proof']>['statement'] & string =
    pr.ok ? 'all-worlds' : pw?.ok ? 'allocated-arguments' : ps?.ok ? 'allocated-arguments-strlen' :
    po?.ok ? 'allocated-arguments-objects' : pb?.ok ? 'observational' : pn?.ok ? 'old-no-panic' : 'all-worlds';
  const best = kind === 'allocated-arguments' ? pw! : kind === 'allocated-arguments-strlen' ? ps! :
    kind === 'allocated-arguments-objects' ? po! : kind === 'observational' ? pb! : kind === 'old-no-panic' ? pn! : pr;
  const suffix = kind === 'allocated-arguments' ? '_wf' : kind === 'allocated-arguments-strlen' ? '_wfs' :
    kind === 'allocated-arguments-objects' ? '_wfo' : kind === 'observational' ? '_obs' : kind === 'old-no-panic' ? '_np' : '';
  const second = kind === 'observational' || kind === 'old-no-panic';
  r.proof = { file: second ? obsFile! : res.file, theorem: `equiv_${p.id}${suffix}`, axioms: best.axioms,
    script: kind === 'observational' ? OBS_SCRIPT : kind === 'old-no-panic' ? opts.script : suffix ? opts.scriptWf : opts.script, residual: best.ok ? undefined : residual(pr),
    statement: kind, wf: pw ? { ok: pw.ok, residual: pw.ok ? undefined : residual(pw) } : undefined,
    wfs: ps ? { ok: ps.ok, residual: ps.ok ? undefined : residual(ps) } : undefined,
    wfo: po ? { ok: po.ok, residual: po.ok ? undefined : residual(po) } : undefined,
    obs: pb ? { ok: pb.ok, residual: pb.ok ? undefined : residual(pb) } : undefined,
    np: pn ? { ok: pn.ok, residual: pn.ok ? undefined : residual(pn) } : undefined };
  if (best.ok) {
    if (r.ctx?.fuzz?.status === 'diff') { r.verdict = 'UNKNOWN'; r.reasons.push('SOUNDNESS ALERT: proof checked although fuzzing found a difference'); return; }
    // the old-no-panic statement is not an equivalence: verdict UNKNOWN, with that proof attached
    r.verdict = kind === 'old-no-panic' ? 'UNKNOWN' : 'PROVED';
    if (kind === 'old-no-panic') r.reasons.push('only the weaker old-no-panic statement was proved (equal runs, or the old run panics); no equivalence statement was proved');
    if (kind === 'allocated-arguments') r.notes.push('proved for every world in which the argument arrays, maps and sets are allocated cells (hw: the cell exists, hn: its address is below the allocation counter), as in every state a run reaches; the statement over all worlds was not proved');
    if (kind === 'allocated-arguments-objects') r.notes.push('proved for every world in which the argument arrays, maps and sets and the object arguments are allocated cells, the objects\' fields initialised and their array fields allocated cells with fewer than 2^32 - 1 elements (JavaScript arrays stay below 2^32 elements), as in every state a run reaches; no statement without the object hypotheses was proved');
    if (kind === 'allocated-arguments-strlen') r.notes.push('proved for every world in which the argument arrays, maps and sets are allocated cells and the string arguments have at most 2^53 - 1 code units (the maximum length of an ECMAScript String, ECMA-262 6.1.4), as in every state a run reaches; neither the statement over all worlds nor the one without the string lengths was proved');
    if (kind === 'observational') r.notes.push(`proved only up to observation (statement observational, WEAKER than equality of worlds): in every world in which the argument arrays, maps and sets are allocated cells and the string arguments have at most 2^53 - 1 code units, the two runs both fail to terminate, or end with ${/Obs\.ArrObs/.test(p.theoremObs!) ? 'the same error, or with the same caller array or two fresh arrays with equal contents' : 'the same result'}, the same console output, the same cells below the caller's allocation counter and the same numbers of Math.random/Date.now/external-call answers consumed; the cells the callee allocated (other than a returned array) and the allocation counter are not compared (the functions schedule no asynchronous work); no equality statement was proved`);
    if (kind === 'old-no-panic') r.notes.push('proved only where the old version does not panic (statement old-no-panic, WEAKER than equality of worlds): for every argument list and every world, the two runs are equal or the old run panics (a read the TypeScript types exclude, a non-null assertion on undefined, or another designed panic); where the old version panics, the new one may do anything; no other statement was proved');
    if (best.axioms.some(a => /ofReduceBool|trustCompiler/.test(a))) r.notes.push(`proof uses the native-code axiom (${best.axioms.filter(a => /ofReduceBool|trustCompiler/.test(a)).join(', ')}) via bv_decide`);
  } else {
    r.verdict = 'UNKNOWN';
    r.reasons.push(`no proof: ${classifyProofFailure(pr.errors, pr.goals)}${pw ? `; allocated-arguments statement: ${classifyProofFailure(pw.errors, pw.goals)}` : ''}${ps ? `; allocated-arguments-strlen statement: ${classifyProofFailure(ps.errors, ps.goals)}` : ''}${po ? `; allocated-arguments-objects statement: ${classifyProofFailure(po.errors, po.goals)}` : ''}${pb ? `; observational statement: ${classifyProofFailure(pb.errors, pb.goals)}` : ''}${pn ? `; old-no-panic statement: ${classifyProofFailure(pn.errors, pn.goals)}` : ''}`);
  }
}

export function classifyProofFailure(errors: string[], goals: string[] = []): string {
  const all = errors.join('\n');
  if (/maximum number of heartbeats|deterministic\) timeout/.test(all)) return 'proof search timed out (heartbeats)';
  if (/lean timed out/.test(all)) return 'Lean process timed out';
  if (/theorem not checked/.test(all)) return 'theorem not checked (elaboration error)';
  const g = [...goals, ...errors].join('\n');
  const hints: string[] = [];
  if (/evalLoop|evalForOf|evalDo|forOfA|loopA|evalForOfStr|evalForOfMap|evalForOfSet/.test(g)) hints.push('loops (needs loop summarization or a lockstep rule)');
  if (/arrReduce|arrMap|arrFilter|arrSome|arrEvery|arrFind|arrForEach|sortL|arrSort|arrFromFn|arrFlatMap/.test(g)) hints.push('array library calls with callbacks');
  if (/mapForEachL|readMap|JSMap|mapGet|mapSet/.test(g)) hints.push('Map operations');
  if (/drain|runJob|eventLoop|PromiseCell|settle|newPromise|handleStep|execAB|applyK/.test(g)) hints.push('async/promise machinery');
  if (/callFun|applyLam|applyFn/.test(g)) hints.push('a call that was not unfolded (recursion or closure)');
  if (/next := |\.next \+|alloc/.test(g)) hints.push('allocation differs (equivalence modulo fresh allocation)');
  if (!hints.length && /JSStr|strConcat|toJSString|strSlice|startsWith|indexOf|strIncludes/.test(g)) hints.push('string-library reasoning left open');
  if (!hints.length && /F64|\.lt |\.le |\.min|\.max|floor|\.add|\.mul|\.div/.test(g)) hints.push('number (F64) reasoning left open');
  if (!hints.length && g) hints.push('residual goal');
  if (!hints.length) hints.push('proof failed: ' + (errors[0] ?? '').split('\n')[0].slice(0, 160));
  return hints.join('; ');
}

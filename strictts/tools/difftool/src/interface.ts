// The frozen result format of `strictts-diff diff` (schema strictts-diff/v1, see INTERFACE.md and
// schema/strictts-diff-v1.schema.json): conversion from the internal reports, stable reason codes,
// and a dependency-free validator used by the fixture test.
import { FnReport, ObsView } from './diff';

export const SCHEMA_ID = 'strictts-diff/v1';

export type VerdictV1 = 'PROVED' | 'REFUTED' | 'REFUTED*' | 'UNKNOWN';

export interface FunctionV1 {
  key: string;
  file: string;
  name: string;
  kind: string;
  status: 'changed' | 'added' | 'removed';
  verdict: VerdictV1 | null;
  reasonCodes: string[];
  reasons: string[];
  notes: string[];
  counterexample: null | {
    call: string;
    inputs: unknown[];
    receiverArgs: unknown[] | null;
    old: ObsView;
    new: ObsView;
    differs: string[];
    leanConfirmed: boolean;
    lean: null | { old: string; new: string };
  };
  proof: null | {
    file: string;
    theorem: string;
    statement: 'all-worlds' | 'allocated-arguments' | 'allocated-arguments-strlen' | 'allocated-arguments-objects' | 'observational' | 'old-no-panic';
    checked: boolean;
    axioms: string[];
    axiomsOk: boolean;
    nativeAxiom: boolean;
  };
  fuzz: null | { runs: number; inconclusive: number; ms: number };
}

export interface ResultV1 {
  schema: typeof SCHEMA_ID;
  command: 'diff';
  old: string;
  new: string;
  options: { seed: number; runs: number; lean: boolean; tactic: 'default' | 'custom'; tacticWf: 'default' | 'custom' };
  summary: { changed: number; proved: number; refuted: number; refutedNodeOnly: number; unknown: number; added: number; removed: number };
  functions: FunctionV1[];
}

/** Stable reason codes (INTERFACE.md lists them); derived from the reports' reasons and notes. */
export const REASON_CODES = [
  'outside-subset', 'external-module', 'signature-changed', 'kind-changed', 'inputs-not-generated', 'fuzz-error',
  'slice-error', 'module-state-differs', 'translated-signatures-differ', 'target-not-translated', 'no-counterexample',
  'no-proof', 'proof:loops', 'proof:callbacks', 'proof:map', 'proof:async', 'proof:call', 'proof:allocation',
  'proof:strings', 'proof:numbers', 'proof:timeout', 'proof:other', 'lean-disabled', 'lean-error', 'soundness-alert',
  'node-only:driver-outside-subset', 'node-only:lean-mismatch', 'node-only:not-observable', 'node-only:lean-failed',
  'node-only:lean-disabled', 'other',
] as const;

const STANDARD_AXIOMS = new Set(['propext', 'Classical.choice', 'Quot.sound']);
const NATIVE_AXIOMS = new Set(['Lean.ofReduceBool', 'Lean.trustCompiler']);

function proofCodes(text: string): string[] {
  const out: string[] = [];
  if (/timed out/.test(text)) out.push('proof:timeout');
  if (/loops/.test(text)) out.push('proof:loops');
  if (/array library calls/.test(text)) out.push('proof:callbacks');
  if (/Map operations/.test(text)) out.push('proof:map');
  if (/async/.test(text)) out.push('proof:async');
  if (/call that was not unfolded/.test(text)) out.push('proof:call');
  if (/allocation differs/.test(text)) out.push('proof:allocation');
  if (/string-library/.test(text)) out.push('proof:strings');
  if (/number \(F64\)/.test(text)) out.push('proof:numbers');
  if (!out.length) out.push('proof:other');
  return out;
}

export function reasonCodes(r: FnReport): string[] {
  const codes = new Set<string>();
  if (r.status !== 'changed') return [];
  for (const t of r.reasons) {
    if (/outside the StrictTS subset/.test(t)) codes.add('outside-subset');
    else if (/uses external module/.test(t)) codes.add('external-module');
    else if (/signature changed|constructor of the receiver class changed/.test(t)) codes.add('signature-changed');
    else if (/^kind changed/.test(t)) codes.add('kind-changed');
    else if (/inputs of this type are not generated|input generation/.test(t)) codes.add('inputs-not-generated');
    else if (/^fuzzing:/.test(t)) codes.add('fuzz-error');
    else if (/^(slicing|signature|old slice|new slice):/.test(t)) codes.add('slice-error');
    else if (/module-level state/.test(t)) codes.add('module-state-differs');
    else if (/translated signatures differ/.test(t)) codes.add('translated-signatures-differ');
    else if (/not found in the translation/.test(t)) codes.add('target-not-translated');
    else if (/no counterexample in \d+ runs/.test(t)) codes.add('no-counterexample');
    else if (/^no proof:/.test(t)) { codes.add('no-proof'); for (const c of proofCodes(t)) codes.add(c); }
    else if (/Lean stage disabled/.test(t)) codes.add('lean-disabled');
    else if (/^(Lean preparation|proof):/.test(t)) codes.add('lean-error');
    else if (/SOUNDNESS ALERT/.test(t)) codes.add('soundness-alert');
    else codes.add('other');
  }
  if (r.verdict === 'UNKNOWN' && r.fuzz && !r.cex && !codes.has('fuzz-error')) codes.add('no-counterexample');
  if (r.verdict === 'REFUTED' && !(r.confirmedBy ?? []).includes('lean')) {
    const n = r.notes.join('\n');
    if (/LEAN\/NODE MISMATCH/.test(n)) codes.add('node-only:lean-mismatch');
    else if (/Lean confirmation not run: .*outside the subset/.test(n)) codes.add('node-only:driver-outside-subset');
    else if (/Lean confirmation inconclusive/.test(n)) codes.add('node-only:not-observable');
    else if (/Lean confirmation (failed|not run)/.test(n)) codes.add('node-only:lean-failed');
    else codes.add('node-only:lean-disabled');
  }
  return [...codes];
}

export function verdictV1(r: FnReport): VerdictV1 | null {
  if (r.status !== 'changed') return null;
  const v = r.verdict ?? 'UNKNOWN';
  if (v === 'REFUTED' && !(r.confirmedBy ?? []).includes('lean')) return 'REFUTED*';
  return v;
}

export function functionV1(r: FnReport): FunctionV1 {
  const v = verdictV1(r);
  const p = r.proof;
  return {
    key: r.key, file: r.file, name: r.name, kind: r.kind ?? 'function', status: r.status, verdict: v,
    reasonCodes: v === 'PROVED' || v === 'REFUTED' ? [] : reasonCodes(r),
    reasons: r.reasons, notes: r.notes,
    counterexample: r.cex && r.cex.oldObs && r.cex.newObs ? {
      call: r.cex.inputText, inputs: r.cex.input.args, receiverArgs: r.cex.input.self ?? null,
      old: r.cex.oldObs, new: r.cex.newObs, differs: r.cex.parts,
      leanConfirmed: (r.confirmedBy ?? []).includes('lean'), lean: r.cex.lean ?? null,
    } : null,
    proof: p ? {
      file: p.file, theorem: p.theorem, statement: p.statement ?? 'all-worlds', checked: v === 'PROVED', axioms: p.axioms,
      axiomsOk: !p.axioms.includes('sorryAx') && p.axioms.every(a => STANDARD_AXIOMS.has(a) || NATIVE_AXIOMS.has(a)),
      nativeAxiom: p.axioms.some(a => NATIVE_AXIOMS.has(a)),
    } : null,
    fuzz: r.fuzz ?? null,
  };
}

export function toResultV1(reports: FnReport[], meta: { old: string; new: string; seed: number; runs: number; lean: boolean; tactic: 'default' | 'custom'; tacticWf: 'default' | 'custom' }): ResultV1 {
  const fns = reports.map(functionV1);
  const ch = fns.filter(f => f.status === 'changed');
  return {
    schema: SCHEMA_ID, command: 'diff', old: meta.old, new: meta.new,
    options: { seed: meta.seed, runs: meta.runs, lean: meta.lean, tactic: meta.tactic, tacticWf: meta.tacticWf },
    summary: {
      changed: ch.length, proved: ch.filter(f => f.verdict === 'PROVED').length, refuted: ch.filter(f => f.verdict === 'REFUTED').length,
      refutedNodeOnly: ch.filter(f => f.verdict === 'REFUTED*').length, unknown: ch.filter(f => f.verdict === 'UNKNOWN').length,
      added: fns.filter(f => f.status === 'added').length, removed: fns.filter(f => f.status === 'removed').length,
    },
    functions: fns,
  };
}

// ---------------------------------------------------------------------------------------
// Validation against the schema (the same constraints as schema/strictts-diff-v1.schema.json).

type Check = (v: unknown, path: string, errs: string[]) => void;
const isObj = (v: unknown): v is Record<string, unknown> => typeof v === 'object' && v !== null && !Array.isArray(v);
const str: Check = (v, p, e) => { if (typeof v !== 'string') e.push(`${p}: expected string`); };
const int: Check = (v, p, e) => { if (typeof v !== 'number' || !Number.isInteger(v) || v < 0) e.push(`${p}: expected a non-negative integer`); };
const bool: Check = (v, p, e) => { if (typeof v !== 'boolean') e.push(`${p}: expected boolean`); };
const oneOf = (vals: readonly unknown[]): Check => (v, p, e) => { if (!vals.includes(v)) e.push(`${p}: expected one of ${vals.map(x => JSON.stringify(x)).join(', ')}, got ${JSON.stringify(v)}`); };
const arr = (item: Check): Check => (v, p, e) => { if (!Array.isArray(v)) e.push(`${p}: expected array`); else v.forEach((x, i) => item(x, `${p}[${i}]`, e)); };
const nullable = (c: Check): Check => (v, p, e) => { if (v !== null) c(v, p, e); };
const any: Check = () => {};
const obj = (fields: Record<string, Check>, extra = true): Check => (v, p, e) => {
  if (!isObj(v)) { e.push(`${p}: expected object`); return; }
  for (const [k, c] of Object.entries(fields)) { if (!(k in v)) e.push(`${p}.${k}: missing`); else c(v[k], `${p}.${k}`, e); }
  if (!extra) for (const k of Object.keys(v)) if (!(k in fields)) e.push(`${p}.${k}: unexpected field`);
};

const obsCheck = obj({ outcome: str, console: arr(str), args: arr(str), receiver: nullable(str), unhandled: arr(str) });
const fnCheck: Check = (v, p, e) => {
  obj({
    key: str, file: str, name: str, kind: oneOf(['function', 'arrow', 'method', 'static', 'ctor']),
    status: oneOf(['changed', 'added', 'removed']), verdict: nullable(oneOf(['PROVED', 'REFUTED', 'REFUTED*', 'UNKNOWN'])),
    reasonCodes: arr(oneOf(REASON_CODES)), reasons: arr(str), notes: arr(str),
    counterexample: nullable(obj({ call: str, inputs: arr(any), receiverArgs: nullable(arr(any)), old: obsCheck, new: obsCheck,
      differs: arr(str), leanConfirmed: bool, lean: nullable(obj({ old: str, new: str })) })),
    proof: nullable(obj({ file: str, theorem: str, statement: oneOf(['all-worlds', 'allocated-arguments', 'allocated-arguments-strlen', 'allocated-arguments-objects', 'observational', 'old-no-panic']), checked: bool,
      axioms: arr(str), axiomsOk: bool, nativeAxiom: bool })),
    fuzz: nullable(obj({ runs: int, inconclusive: int, ms: int })),
  })(v, p, e);
  if (!isObj(v)) return;
  // cross-field rules
  if ((v.status === 'changed') !== (v.verdict !== null)) e.push(`${p}: verdict is set exactly for changed functions`);
  if ((v.verdict === 'REFUTED' || v.verdict === 'REFUTED*') && v.counterexample === null) e.push(`${p}: a refutation carries its counterexample`);
  if (isObj(v.counterexample) && (v.verdict === 'REFUTED') !== (v.counterexample.leanConfirmed === true)) e.push(`${p}: REFUTED iff the counterexample is Lean-confirmed`);
  if (v.verdict === 'PROVED' && !(isObj(v.proof) && v.proof.checked === true && v.proof.axiomsOk === true)) e.push(`${p}: PROVED carries a checked proof with an accepted axiom set`);
  if (isObj(v.proof) && v.proof.checked === true && v.verdict !== 'PROVED') e.push(`${p}: a checked proof means PROVED`);
};

export function validateResultV1(v: unknown): string[] {
  const e: string[] = [];
  obj({
    schema: oneOf([SCHEMA_ID]), command: oneOf(['diff']), old: str, new: str,
    options: obj({ seed: int, runs: int, lean: bool, tactic: oneOf(['default', 'custom']), tacticWf: oneOf(['default', 'custom']) }),
    summary: obj({ changed: int, proved: int, refuted: int, refutedNodeOnly: int, unknown: int, added: int, removed: int }),
    functions: arr(fnCheck),
  })(v, '$', e);
  if (isObj(v) && isObj(v.summary) && Array.isArray(v.functions)) {
    const fs = v.functions.filter(isObj);
    const count = (pred: (f: Record<string, unknown>) => boolean) => fs.filter(pred).length;
    const s = v.summary;
    const want: Record<string, number> = {
      changed: count(f => f.status === 'changed'), proved: count(f => f.verdict === 'PROVED'), refuted: count(f => f.verdict === 'REFUTED'),
      refutedNodeOnly: count(f => f.verdict === 'REFUTED*'), unknown: count(f => f.verdict === 'UNKNOWN'),
      added: count(f => f.status === 'added'), removed: count(f => f.status === 'removed'),
    };
    for (const [k, n] of Object.entries(want)) if (s[k] !== n) e.push(`$.summary.${k}: ${String(s[k])} but ${n} functions`);
  }
  return e;
}

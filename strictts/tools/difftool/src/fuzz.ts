// Differential fuzzing in Node: both versions of a slice run in their own child process on
// the same type-directed inputs; differing observations are shrunk and re-checked in fresh
// processes before they count as a counterexample.
import * as path from 'path';
import * as ts from 'typescript';
import { fork, ChildProcess } from 'child_process';
import type { InitMsg, Obs } from './child';
import { Input, GenCtx, genInput, boundaryInputs, shrinkInput, inputSize } from './gen';
import { Signature } from './typedesc';
import { Rng } from './util';

export type { Obs };

export interface Version {
  /** relative path -> TypeScript source */
  files: Map<string, string>;
  entry: string;
  exportName: string;
  kind: string;
  method?: string;
  /** unresolved globals of the slice (see InitMsg.hostGlobals) */
  hostGlobals?: string[];
}

/** Globals the runner's sandbox provides itself. */
const SANDBOX_GLOBALS = new Set(['console', 'setTimeout', 'setInterval', 'setImmediate', 'clearTimeout', 'clearInterval', 'clearImmediate',
  'queueMicrotask', 'structuredClone', 'URL', 'URLSearchParams', 'TextEncoder', 'TextDecoder', 'atob', 'btoa', 'performance']);

export function transpile(files: Map<string, string>): Record<string, string> {
  const out: Record<string, string> = {};
  for (const [rel, text] of files) {
    if (rel.endsWith('.d.ts')) continue;
    out[rel] = ts.transpileModule(text, {
      compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.CommonJS, alwaysStrict: true, esModuleInterop: false, jsx: ts.JsxEmit.React },
      fileName: rel,
    }).outputText;
  }
  return out;
}

export class Runner {
  private proc: ChildProcess | null = null;
  private seq = 0;
  private waiters = new Map<number, { resolve: (o: Obs[]) => void; reject: (e: Error) => void }>();
  private readyP: Promise<void> | null = null;
  constructor(private init: InitMsg) {}

  private start(): Promise<void> {
    if (this.readyP) return this.readyP;
    this.readyP = new Promise<void>((resolve, reject) => {
      const p = fork(path.join(__dirname, 'child.js'), [], {
        execArgv: ['--max-old-space-size=1024', '--stack-size=984'],
        stdio: ['ignore', 'ignore', 'pipe', 'ipc'],
      });
      this.proc = p;
      let stderr = '';
      p.stderr?.on('data', d => { stderr += String(d); if (stderr.length > 20000) stderr = stderr.slice(-20000); });
      p.on('message', (m: { type: string; id?: number; obs?: Obs[]; message?: string }) => {
        if (m.type === 'ready') resolve();
        else if (m.type === 'result') { const w = this.waiters.get(m.id!); this.waiters.delete(m.id!); w?.resolve(m.obs!); }
        else if (m.type === 'error') { const e = new Error(`runner: ${m.message}`); reject(e); for (const [, w] of this.waiters) w.reject(e); this.waiters.clear(); }
      });
      p.on('exit', (code, sig) => {
        const e = new Error(`runner exited (${code ?? sig})${stderr ? ': ' + stderr.trim().split('\n').slice(-3).join(' / ') : ''}`);
        reject(e);
        for (const [, w] of this.waiters) w.reject(e);
        this.waiters.clear();
        this.proc = null; this.readyP = null;
      });
      p.send(this.init);
    });
    return this.readyP;
  }

  private async batch(inputs: Input[]): Promise<Obs[]> {
    await this.start();
    const id = ++this.seq;
    const limit = 15000 + inputs.length * this.init.timeoutMs * 3;
    return new Promise<Obs[]>((resolve, reject) => {
      const timer = setTimeout(() => { this.kill(); reject(new Error('runner batch timed out')); }, limit);
      this.waiters.set(id, { resolve: o => { clearTimeout(timer); resolve(o); }, reject: e => { clearTimeout(timer); reject(e); } });
      this.proc!.send({ type: 'run', id, inputs });
    });
  }

  /** Run inputs; a crash (out of memory, …) is isolated to the input that caused it. */
  async run(inputs: Input[]): Promise<Obs[]> {
    try { return await this.batch(inputs); }
    catch (e) {
      if (inputs.length === 1) return [{ kind: 'crash', o: `crash: ${(e as Error).message}`, out: [], args: [], strict: '', unhandled: [] }];
      const out: Obs[] = [];
      for (const inp of inputs) out.push(...await this.run([inp]));
      return out;
    }
  }

  kill(): void { if (this.proc) { this.proc.kill('SIGKILL'); this.proc = null; this.readyP = null; } }
}

export function initMsg(v: Version, timeoutMs: number): InitMsg {
  return { type: 'init', files: transpile(v.files), entry: v.entry, exportName: v.exportName, kind: v.kind, method: v.method, timeoutMs,
    hostGlobals: (v.hostGlobals ?? []).filter(g => !SANDBOX_GLOBALS.has(g)) };
}

export function sameObs(a: Obs, b: Obs): boolean {
  return a.o === b.o && a.out.join('\n') === b.out.join('\n') && a.args.join('\u0001') === b.args.join('\u0001') &&
    (a.self ?? '') === (b.self ?? '') && a.unhandled.join('\n') === b.unhandled.join('\n');
}

export const conclusive = (o: Obs) => o.kind === 'ok' && !(o.host && o.host.length);

/** Which parts of two observations differ. */
export function diffParts(a: Obs, b: Obs): string[] {
  const d: string[] = [];
  if (a.o !== b.o) d.push('outcome');
  if (a.out.join('\n') !== b.out.join('\n')) d.push('console');
  if (a.args.join('\u0001') !== b.args.join('\u0001')) d.push('arguments after the call');
  if ((a.self ?? '') !== (b.self ?? '')) d.push('receiver after the call');
  if (a.unhandled.join('\n') !== b.unhandled.join('\n')) d.push('unhandled rejections');
  return d;
}

export interface Cex { input: Input; old: Obs; new: Obs; parts: string[]; shrinkSteps: number }

export interface FuzzResult {
  status: 'diff' | 'same' | 'error';
  error?: string;
  runs: number;
  inconclusive: number;
  cex?: Cex;
  /** observations equal only up to key order / undefined-valued keys */
  strictOnly?: Cex;
  notes: string[];
  ms: number;
}

export interface FuzzOpts { runs: number; seed: number; timeoutMs: number; shrinkBudget: number; nums: number[]; strs: string[]; props?: string[] }

/** Literals of the sources (for input generation). */
/** Method names of the standard library (not used as candidate keys of client objects). */
const LIB_MEMBERS = new Set(['length', 'push', 'pop', 'shift', 'unshift', 'slice', 'splice', 'concat', 'join', 'map', 'filter', 'reduce', 'forEach',
  'find', 'findIndex', 'some', 'every', 'includes', 'indexOf', 'lastIndexOf', 'sort', 'reverse', 'flat', 'flatMap', 'fill', 'keys', 'values',
  'entries', 'get', 'set', 'has', 'delete', 'clear', 'add', 'size', 'trim', 'trimStart', 'trimEnd', 'toLowerCase', 'toUpperCase', 'split', 'replace',
  'replaceAll', 'startsWith', 'endsWith', 'charAt', 'charCodeAt', 'codePointAt', 'padStart', 'padEnd', 'repeat', 'substring', 'match', 'test',
  'toString', 'toFixed', 'then', 'catch', 'finally', 'log', 'floor', 'ceil', 'round', 'min', 'max', 'abs', 'now', 'isArray', 'from', 'of', 'assign',
  'hasOwn', 'is', 'parse', 'stringify', 'normalize', 'at', 'exec', 'apply', 'call', 'bind']);

export function mineLiterals(texts: string[]): { nums: number[]; strs: string[]; props: string[] } {
  const nums = new Set<number>(), strs = new Set<string>();
  const props = new Map<string, number>();
  for (const text of texts) {
    const sf = ts.createSourceFile('x.ts', text, ts.ScriptTarget.ES2022, false);
    const walk = (n: ts.Node) => {
      if (ts.isNumericLiteral(n)) { const v = Number(n.text); if (Number.isFinite(v)) nums.add(v); }
      else if (ts.isStringLiteral(n) || ts.isNoSubstitutionTemplateLiteral(n)) { if (n.text.length <= 40 && !(n.parent && (ts.isImportDeclaration(n.parent) || ts.isExportDeclaration(n.parent)))) strs.add(n.text); }
      else if (ts.isTemplateHead(n) || ts.isTemplateMiddle(n) || ts.isTemplateTail(n)) { if (n.text && n.text.length <= 40) strs.add(n.text); }
      else if (ts.isPropertyAccessExpression(n) && ts.isIdentifier(n.name) && !LIB_MEMBERS.has(n.name.text)) props.set(n.name.text, (props.get(n.name.text) ?? 0) + 1);
      else if (ts.isElementAccessExpression(n) && ts.isStringLiteral(n.argumentExpression)) props.set(n.argumentExpression.text, (props.get(n.argumentExpression.text) ?? 0) + 1);
      ts.forEachChild(n, walk);
    };
    walk(sf);
  }
  return { nums: [...nums].slice(0, 300), strs: [...strs].slice(0, 300), props: [...props].sort((a, b) => b[1] - a[1]).map(e => e[0]).slice(0, 16) };
}

export async function fuzzPair(oldV: Version, newV: Version, sig: Signature, opts: FuzzOpts): Promise<FuzzResult> {
  const t0 = Date.now();
  const res: FuzzResult = { status: 'same', runs: 0, inconclusive: 0, notes: [], ms: 0 };
  const g: GenCtx = { rng: new Rng(opts.seed), table: sig.table, nums: opts.nums, strs: opts.strs, props: opts.props };
  const ro = new Runner(initMsg(oldV, opts.timeoutMs));
  const rn = new Runner(initMsg(newV, opts.timeoutMs));
  const both = async (inputs: Input[]) => Promise.all([ro.run(inputs), rn.run(inputs)]);
  try {
    let inputs: Input[];
    try { inputs = boundaryInputs(sig, g); }
    catch { inputs = []; }
    const seen = new Set<string>();
    const fresh = (inp: Input) => { const k = JSON.stringify(inp); if (seen.has(k)) return false; seen.add(k); return true; };
    inputs = inputs.filter(fresh);
    const diffs: Cex[] = [];
    let strictOnly: Cex | undefined;
    let sameThrow: string | null | undefined;
    let harness = 0;
    let genFail = 0;
    let hostRuns = 0;
    const hostNames = new Set<string>();
    // budget: slow or hanging functions (every run times out) must not stall a whole history run
    const budgetMs = 60000;
    while (res.runs < opts.runs && !diffs.length) {
      if (Date.now() - t0 > budgetMs || res.inconclusive >= 50) {
        res.notes.push(`fuzzing stopped after ${res.runs} runs (${res.inconclusive >= 50 ? 'too many inconclusive runs' : 'time budget'})`);
        break;
      }
      while (inputs.length < 100 && res.runs + inputs.length < opts.runs && genFail < 20 * opts.runs) {
        try { const inp = genInput(sig, g); if (fresh(inp)) inputs.push(inp); else genFail++; }
        catch (e) { res.status = 'error'; res.error = `input generation: ${(e as Error).message}`; return res; }
      }
      if (!inputs.length) break;
      const batch = inputs.splice(0, res.inconclusive > 0 ? 20 : 100);
      const [oo, on] = await both(batch);
      res.runs += batch.length;
      batch.forEach((inp, i) => {
        const a = oo[i], b = on[i];
        if (a.kind === 'harness' || b.kind === 'harness') { harness++; if (harness === 1) res.notes.push(a.kind === 'harness' ? a.o : b.o); return; }
        if ((a.host ?? []).length || (b.host ?? []).length) { hostRuns++; for (const x of [...(a.host ?? []), ...(b.host ?? [])]) hostNames.add(x); }
        if (!conclusive(a) || !conclusive(b)) { res.inconclusive++; return; }
        if (!sameObs(a, b)) diffs.push({ input: inp, old: a, new: b, parts: diffParts(a, b), shrinkSteps: 0 });
        else if (a.strict !== b.strict && !strictOnly) strictOnly = { input: inp, old: a, new: b, parts: ['key order or undefined-valued keys'], shrinkSteps: 0 };
        const thr = a.o.startsWith('throw ') ? a.o : null;
        sameThrow = sameThrow === undefined ? thr : (sameThrow === thr ? sameThrow : null);
      });
      if (genFail >= 20 * opts.runs && !inputs.length) break;
    }
    if (harness && harness === res.runs) { res.status = 'error'; res.error = res.notes[0] ?? 'harness error'; return res; }
    if (sameThrow) res.notes.push(`every run threw ${sameThrow.slice(6)} in both versions`);
    if (hostRuns) res.notes.push(`${hostRuns} run(s) touched host globals not modelled by the sandbox (${[...hostNames].join(', ')}); inconclusive`);
    if (res.inconclusive > hostRuns) res.notes.push(`${res.inconclusive - hostRuns} inconclusive run(s) (timeout, stack overflow or crash)`);
    if (strictOnly && !diffs.length) { res.strictOnly = strictOnly; res.notes.push('results differ only in object key order or undefined-valued keys (not observable in StrictTS)'); }
    if (!diffs.length) return res;
    // shrink the smallest counterexample
    diffs.sort((x, y) => inputSize(x.input) - inputSize(y.input));
    let best = diffs[0];
    let budget = opts.shrinkBudget;
    let improved = true;
    while (improved && budget > 0) {
      improved = false;
      const cands = shrinkInput(sig, best.input, g).filter(c => inputSize(c) < inputSize(best.input) || JSON.stringify(c).length < JSON.stringify(best.input).length);
      for (let i = 0; i < cands.length && budget > 0 && !improved; i += 25) {
        const chunk = cands.slice(i, i + 25);
        budget -= chunk.length;
        const [oo, on] = await both(chunk);
        for (let j = 0; j < chunk.length; j++) {
          if (conclusive(oo[j]) && conclusive(on[j]) && !sameObs(oo[j], on[j])) {
            best = { input: chunk[j], old: oo[j], new: on[j], parts: diffParts(oo[j], on[j]), shrinkSteps: best.shrinkSteps + 1 };
            improved = true;
            break;
          }
        }
      }
    }
    // determinism: re-run in fresh processes
    ro.kill(); rn.kill();
    const fo = new Runner(initMsg(oldV, opts.timeoutMs)), fn = new Runner(initMsg(newV, opts.timeoutMs));
    try {
      const [[o1], [n1]] = await Promise.all([fo.run([best.input]), fn.run([best.input])]);
      if (!sameObs(o1, best.old) || !sameObs(n1, best.new)) {
        res.notes.push('a difference was observed but did not reproduce in a fresh process (nondeterminism); not reported');
        return res;
      }
    } finally { fo.kill(); fn.kill(); }
    res.status = 'diff';
    res.cex = best;
    return res;
  } catch (e) {
    res.status = 'error';
    res.error = (e as Error).message;
    return res;
  } finally {
    ro.kill(); rn.kill();
    res.ms = Date.now() - t0;
  }
}

// Small shared helpers: paths, hashing, process execution, deterministic PRNG.
import * as fs from 'fs';
import * as path from 'path';
import * as crypto from 'crypto';
import { spawnSync } from 'child_process';
import { ROOT } from './boot';

export { ROOT };
export const SCRATCH = path.join(ROOT, 'scratch', 'difftool');

export function sha1(s: string): string {
  return crypto.createHash('sha1').update(s).digest('hex');
}

export function mkdirp(d: string): string {
  fs.mkdirSync(d, { recursive: true });
  return d;
}

export function writeFile(f: string, text: string): void {
  mkdirp(path.dirname(f));
  fs.writeFileSync(f, text);
}

export function readFile(f: string): string {
  return fs.readFileSync(f, 'utf8');
}

export interface RunResult { status: number | null; stdout: string; stderr: string; timedOut: boolean; secs: number }

/** Run a command synchronously (no shell), with a timeout; the child is killed with SIGKILL. */
export function run(cmd: string, args: string[], opts: { cwd?: string; env?: NodeJS.ProcessEnv; timeoutS?: number; input?: string } = {}): RunResult {
  const t0 = Date.now();
  const r = spawnSync(cmd, args, {
    cwd: opts.cwd ?? ROOT, env: opts.env ?? process.env, encoding: 'utf8', input: opts.input,
    timeout: (opts.timeoutS ?? 600) * 1000, killSignal: 'SIGKILL', maxBuffer: 256 << 20,
  });
  const timedOut = !!r.error && /ETIMEDOUT/.test(String((r.error as NodeJS.ErrnoException).code ?? r.error.message));
  return { status: r.status, stdout: r.stdout ?? '', stderr: (r.stderr ?? '') + (r.error && !timedOut ? `\n${r.error.message}` : ''), timedOut, secs: (Date.now() - t0) / 1000 };
}

/** splitmix64-style PRNG on two 32-bit halves (deterministic across runs). */
export class Rng {
  private s: bigint;
  constructor(seed: number | bigint) { this.s = BigInt.asUintN(64, BigInt(seed)); }
  nextU64(): bigint {
    this.s = BigInt.asUintN(64, this.s + 0x9E3779B97F4A7C15n);
    let z = this.s;
    z = BigInt.asUintN(64, (z ^ (z >> 30n)) * 0xBF58476D1CE4E5B9n);
    z = BigInt.asUintN(64, (z ^ (z >> 27n)) * 0x94D049BB133111EBn);
    return z ^ (z >> 31n);
  }
  /** uniform in [0, 1) */
  float(): number { return Number(this.nextU64() >> 11n) / 2 ** 53; }
  /** uniform integer in [0, n) */
  below(n: number): number { return n <= 0 ? 0 : Math.floor(this.float() * n); }
  int(lo: number, hi: number): number { return lo + this.below(hi - lo + 1); }
  chance(p: number): boolean { return this.float() < p; }
  pick<T>(xs: readonly T[]): T { return xs[this.below(xs.length)]; }
}

export function timestamp(): string {
  return new Date().toISOString().replace(/[-:]/g, '').replace(/\.\d+Z$/, 'Z');
}

/** Lean's library path (computed once through `lake env`). */
let leanPath: string | null = null;
export function leanEnv(): NodeJS.ProcessEnv {
  if (leanPath === null) {
    const home = process.env.HOME ?? '';
    const env = { ...process.env, PATH: `${home}/.elan/bin:${process.env.PATH}` };
    const r = spawnSync('lake', ['env', 'printenv', 'LEAN_PATH'], { cwd: ROOT, env, encoding: 'utf8' });
    leanPath = (r.stdout || '').trim();
    if (!leanPath) throw new Error(`cannot determine LEAN_PATH (lake env): ${r.stderr}`);
  }
  const home = process.env.HOME ?? '';
  return { ...process.env, PATH: `${home}/.elan/bin:${process.env.PATH}`, LEAN_PATH: leanPath };
}

export function truncate(s: string, n: number): string {
  return s.length <= n ? s : s.slice(0, n) + `… (${s.length - n} more chars)`;
}

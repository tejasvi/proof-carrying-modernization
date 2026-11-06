// Runner process: executes one version of a slice on batches of inputs inside a `vm` context
// (fresh module instances per input, virtual timers, fixed Math.random/Date oracles, captured
// console) and reports a canonical observation per input. Started by fuzz.ts with
// child_process.fork; never touches the network or the file system.
import * as vm from 'vm';
import * as util from 'util';

export interface InitMsg {
  type: 'init';
  /** relative path -> CommonJS code */
  files: Record<string, string>;
  entry: string;
  exportName: string;
  /** function | arrow | method | static | ctor */
  kind: string;
  /** method name (methods, static methods) */
  method?: string;
  timeoutMs: number;
  /** globals the code uses that the sandbox does not provide (any access makes the run inconclusive) */
  hostGlobals?: string[];
}

export interface RunMsg { type: 'run'; id: number; inputs: unknown[] }

export interface Obs {
  /** ok: a normal observation; timeout / stack / crash / harness: inconclusive */
  kind: 'ok' | 'timeout' | 'stack' | 'crash' | 'harness';
  /** outcome: `return V`, `throw Name: msg`, `resolve V`, `reject Name: msg`, `pending` */
  o: string;
  out: string[];
  /** arguments after the call (canonical) */
  args: string[];
  self?: string;
  /** strict variant (key order, undefined-valued keys) of outcome + args + self */
  strict: string;
  unhandled: string[];
  /** host globals the run touched (the run says nothing about the real host) */
  host?: string[];
  /** wall time of the call in ms */
  ms?: number;
}

// Code evaluated inside the context. It defines the module loader, the decoder of tagged
// values, the canonical printer and the per-input driver.
const CONTEXT_JS = String.raw`
(function (host) {
  'use strict';
  const G = globalThis;
  let OUT = [];
  const con = {};
  for (const k of ['log', 'info', 'warn', 'error', 'debug', 'trace']) con[k] = (...a) => { OUT.push(host.format(...a)); };
  G.console = con;
  let timers = [], clock = 0, seq = 0, uncaught = [];
  const delay = (ms) => { let d = Number(ms); if (!(d >= 1 && d <= 2147483647)) d = 1; return Math.floor(d); };
  G.setTimeout = (cb, ms, ...args) => { const id = ++seq; timers.push({ id, due: clock + delay(ms), cb, args, rep: 0 }); return id; };
  G.setInterval = (cb, ms, ...args) => { const id = ++seq; const d = delay(ms); timers.push({ id, due: clock + d, cb, args, rep: d }); return id; };
  G.setImmediate = (cb, ...args) => { const id = ++seq; timers.push({ id, due: clock, cb, args, rep: 0 }); return id; };
  G.clearTimeout = G.clearInterval = G.clearImmediate = (id) => { timers = timers.filter(t => t.id !== id); };
  G.queueMicrotask = (f) => { Promise.resolve().then(f); };
  G.structuredClone = (v) => host.structuredCloneIn(v);
  for (const k of ['URL', 'URLSearchParams', 'TextEncoder', 'TextDecoder', 'atob', 'btoa']) if (host.globals[k]) G[k] = host.globals[k];
  Math.random = () => 0;
  const RealDate = Date;
  class FakeDate extends RealDate { constructor(...a) { if (a.length === 0) super(0); else super(...a); } static now() { return 0; } }
  G.Date = FakeDate;
  if (G.performance) G.performance.now = () => 0;

  let FACT = {}, ENTRY = '', EXPORT = '', KIND = '', METHOD = '';
  let HOSTACC = [];
  const norm = (p) => { const out = []; for (const s of p.split('/')) { if (s === '' || s === '.') continue; if (s === '..') out.pop(); else out.push(s); } return out.join('/'); };
  const dirOf = (p) => p.includes('/') ? p.slice(0, p.lastIndexOf('/')) : '';
  function resolveMod(from, spec) {
    if (!(spec.startsWith('./') || spec.startsWith('../'))) throw new Error('external module ' + spec);
    const base = norm(dirOf(from) + '/' + spec);
    const m = base.match(/^(.*)\.(js|jsx|mjs|cjs)$/);
    const cands = [base, ...(m ? [m[1] + '.ts', m[1] + '.tsx', m[1] + '.mts', m[1] + '.cts'] : []), base + '.ts', base + '.tsx', base + '/index.ts', base + '/index.tsx'];
    for (const c of cands) if (Object.prototype.hasOwnProperty.call(FACT, c)) return c;
    throw new Error('module not found: ' + spec + ' from ' + from);
  }
  function load() {
    const cache = new Map();
    const req = (from) => (spec) => {
      const rel = resolveMod(from, spec);
      if (cache.has(rel)) return cache.get(rel).exports;
      const module = { exports: {} };
      cache.set(rel, module);
      FACT[rel](module.exports, req(rel), module);
      return module.exports;
    };
    const module = { exports: {} };
    cache.set(ENTRY, module);
    FACT[ENTRY](module.exports, req(ENTRY), module);
    return { exports: module.exports, cache, req };
  }
  let CLASSES = new Map();
  function decode(t) {
    switch (t.t) {
      case 'n': switch (t.v) { case 'NaN': return NaN; case 'Inf': return Infinity; case '-Inf': return -Infinity; case '-0': return -0; default: return Number(t.v); }
      case 's': return t.v;
      case 'b': return BigInt(t.v);
      case 'B': return t.v;
      case 'u': return undefined;
      case 'z': return null;
      case 'a': return t.v.map(decode);
      case 'o': { const o = {}; for (const [k, v] of t.v) Object.defineProperty(o, k, { value: decode(v), enumerable: true, writable: true, configurable: true }); return o; }
      case 'm': return new Map(t.v.map(([k, v]) => [decode(k), decode(v)]));
      case 'S': return new Set(t.v.map(decode));
      case 'c': { const C = CLASSES.get(t.cls); if (!C) throw new Error('harness: class ' + t.cls + ' is not reachable'); return new C(...t.args.map(decode)); }
      case 'ta': { const C = G[t.kind]; return new C(t.v.map(decode)); }
      case 'd': return new FakeDate(t.v);
      case 'p': return Promise.resolve(decode(t.v));
    }
    throw new Error('harness: bad tagged value');
  }
  const isPlain = (v) => { const p = Object.getPrototypeOf(v); return p === Object.prototype || p === null; };
  function errStr(e) {
    if (e instanceof Error || (e && typeof e === 'object' && typeof e.name === 'string' && typeof e.message === 'string' && 'stack' in e)) return String(e.name) + ': ' + String(e.message);
    return 'value ' + canon([e], false)[0];
  }
  // canonical printing; objects referenced more than once get ids (#1=…, #1)
  function canon(vals, strict) {
    const count = new Map();
    const pass1 = (v, d) => {
      if (v === null || typeof v !== 'object' || d > 40) return;
      if (isPlain(v)) { if (count.get(v) === -1) return; count.set(v, -1); try { for (const k of Object.keys(v)) pass1(v[k], d + 1); } finally { count.delete(v); } return; }
      const c = count.get(v) || 0; count.set(v, c + 1);
      if (c > 0) return;
      if (Array.isArray(v)) for (const x of v) pass1(x, d + 1);
      else if (v instanceof Map) for (const [k, x] of v) { pass1(k, d + 1); pass1(x, d + 1); }
      else if (v instanceof Set) for (const x of v) pass1(x, d + 1);
      else if (!ArrayBuffer.isView(v) && !(v instanceof Date) && !(v instanceof Error)) for (const k of Object.keys(v)) pass1(v[k], d + 1);
    };
    for (const v of vals) pass1(v, 0);
    const ids = new Map(); let next = 0; const onStack = new Set(); let budget = 200000;
    const str = (s) => JSON.stringify(s);
    const p = (v, d) => {
      if (--budget < 0) return '…';
      switch (typeof v) {
        case 'number': return Object.is(v, -0) ? '-0' : String(v);
        case 'string': return str(v);
        case 'bigint': return v + 'n';
        case 'boolean': return String(v);
        case 'undefined': return 'undefined';
        case 'symbol': return 'Symbol(' + String(v.description) + ')';
        case 'function': return '<function>';
      }
      if (v === null) return 'null';
      if (d > 40) return '<deep>';
      if (isPlain(v)) {
        if (onStack.has(v)) return '<cycle>';
        onStack.add(v);
        try {
          let ks = Object.keys(v);
          if (!strict) ks = ks.filter(k => v[k] !== undefined).sort();
          return '{' + ks.map(k => (/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(k) ? k : str(k)) + ': ' + p(v[k], d + 1)).join(', ') + '}';
        } finally { onStack.delete(v); }
      }
      const shared = (count.get(v) || 0) > 1;
      if (shared && ids.has(v)) return '#' + ids.get(v);
      let pre = '';
      if (shared) { ids.set(v, ++next); pre = '#' + next + '='; }
      let s;
      if (Array.isArray(v)) {
        const parts = [];
        for (let i = 0; i < v.length; i++) parts.push(i in v ? p(v[i], d + 1) : '<hole>');
        s = '[' + parts.join(', ') + ']';
      } else if (v instanceof Map) s = 'Map{' + [...v].map(([k, x]) => p(k, d + 1) + ' => ' + p(x, d + 1)).join(', ') + '}';
      else if (v instanceof Set) s = 'Set{' + [...v].map(x => p(x, d + 1)).join(', ') + '}';
      else if (ArrayBuffer.isView(v)) s = (v.constructor && v.constructor.name) + '[' + Array.from(v, x => p(x, d + 1)).join(', ') + ']';
      else if (v instanceof ArrayBuffer) s = 'ArrayBuffer(' + v.byteLength + ')';
      else if (v instanceof Date) s = 'Date(' + v.getTime() + ')';
      else if (v instanceof Error) s = 'Error(' + errStr(v) + ')';
      else if (v instanceof Promise) s = '<promise>';
      else {
        const proto = Object.getPrototypeOf(v);
        const name = proto && proto.constructor && typeof proto.constructor.name === 'string' ? proto.constructor.name : '?';
        let ks = Object.keys(v);
        if (!strict) ks = ks.filter(k => v[k] !== undefined).sort();
        s = name + '{' + ks.map(k => k + ': ' + p(v[k], d + 1)).join(', ') + '}';
      }
      return pre + s;
    };
    return vals.map(v => p(v, 0));
  }
  let ST = null;
  host.api.init = (fact, entry, exportName, kind, method, hostGlobals) => {
    FACT = fact; ENTRY = entry; EXPORT = exportName; KIND = kind; METHOD = method;
    for (const name of hostGlobals || []) {
      if (name in G) continue;
      Object.defineProperty(G, name, { configurable: true, get() { HOSTACC.push(name); throw new ReferenceError(name + ' is not defined'); }, set(v) { HOSTACC.push(name); } });
    }
  };
  host.api.run = (inpJSON) => {
    const inp = JSON.parse(inpJSON);
    OUT = []; timers = []; clock = 0; seq = 0; uncaught = []; HOSTACC = [];
    ST = { args: [], self: undefined, result: undefined, threw: false, err: undefined, isP: false, settled: null, harness: null };
    let mod;
    if (KIND === 'program') {
      try { load(); } catch (e) { ST.threw = true; ST.err = e; }
      return;
    }
    try {
      mod = load();
      // every module of the slice (a class used only as a parameter type is not imported at run time)
      for (const rel of Object.keys(FACT)) {
        if (mod.cache.has(rel)) continue;
        try { mod.req('')('./' + rel); } catch (e) { /* not needed */ }
      }
      CLASSES = new Map();
      for (const [, m] of mod.cache) { const ex = m.exports; if (ex && typeof ex === 'object') for (const k of Object.keys(ex)) { const v = ex[k]; if (typeof v === 'function' && v.prototype && /^class\b/.test(Function.prototype.toString.call(v))) CLASSES.set(v.name, v); } }
      ST.args = inp.args.map(decode);
    } catch (e) { ST.harness = 'harness: ' + errStr(e); return; }
    const target = mod.exports[EXPORT];
    try {
      if (KIND === 'function' || KIND === 'arrow') ST.result = target(...ST.args);
      else if (KIND === 'method') { ST.self = new target(...(inp.self || []).map(decode)); ST.result = ST.self[METHOD](...ST.args); }
      else if (KIND === 'static') ST.result = target[METHOD](...ST.args);
      else if (KIND === 'ctor') ST.result = new target(...ST.args);
    } catch (e) { ST.threw = true; ST.err = e; }
    if (!ST.threw && ST.result instanceof Promise) {
      ST.isP = true;
      ST.result.then(v => { ST.settled = { ok: true, v }; }, e => { ST.settled = { ok: false, e }; });
    }
  };
  host.api.pending = () => timers.length > 0 && !(KIND === 'program' && (ST.threw || uncaught.length));
  host.api.tick = () => {
    if (!timers.length) return false;
    timers.sort((a, b) => a.due - b.due || a.id - b.id);
    const t = timers.shift();
    clock = Math.max(clock, t.due);
    if (t.rep) timers.push({ ...t, due: clock + t.rep });
    try { t.cb(...t.args); } catch (e) { uncaught.push(errStr(e)); }
    return true;
  };
  host.api.finish = () => {
    if (ST.harness) return JSON.stringify({ kind: 'harness', o: ST.harness, out: OUT, args: [], strict: '', unhandled: [] });
    if (KIND === 'program') {
      const st = ST.threw ? '[uncaught ' + errStr(ST.err) + ']' : uncaught.length ? '[uncaught ' + uncaught[0] + ']' : '[ok]';
      return JSON.stringify({ kind: 'ok', o: st, out: OUT, args: [], strict: '', unhandled: [] });
    }
    let o, rv = [];
    if (ST.threw) o = 'throw ' + errStr(ST.err);
    else if (ST.isP) {
      if (!ST.settled) o = 'pending';
      else if (ST.settled.ok) { o = 'resolve '; rv = [ST.settled.v]; }
      else o = 'reject ' + errStr(ST.settled.e);
    } else { o = 'return '; rv = [ST.result]; }
    const vals = [...rv, ...ST.args, ...(KIND === 'method' ? [ST.self] : [])];
    const c = canon(vals, false), s = canon(vals, true);
    if (rv.length) o += c[0];
    const args = c.slice(rv.length, rv.length + ST.args.length);
    const self = KIND === 'method' ? c[c.length - 1] : undefined;
    const stack = ST.threw && /Maximum call stack size exceeded/.test(errStr(ST.err));
    return JSON.stringify({ kind: stack ? 'stack' : 'ok', o, out: OUT.concat(uncaught.map(u => '<uncaught ' + u + '>')), args, self, strict: s.join(' | '), unhandled: [], host: [...new Set(HOSTACC)] });
  };
})
`;

let ctx: vm.Context | null = null;
let init: InitMsg | null = null;
const api: Record<string, (...a: unknown[]) => unknown> = {};
let unhandled: string[] = [];

process.on('unhandledRejection', (reason: unknown) => {
  const r = reason as { name?: unknown; message?: unknown } | null;
  unhandled.push(r && typeof r === 'object' && typeof r.name === 'string' ? `${r.name}: ${String(r.message)}` : `value ${String(reason)}`);
});

function setup(m: InitMsg): void {
  init = m;
  ctx = vm.createContext({}, { name: 'difftool', microtaskMode: 'afterEvaluate', codeGeneration: { strings: true, wasm: false } });
  const host = {
    format: (...a: unknown[]) => util.format(...a),
    structuredCloneIn: (v: unknown) => structuredClone(v),
    globals: { URL, URLSearchParams, TextEncoder, TextDecoder, atob, btoa },
    api,
  };
  vm.runInContext(CONTEXT_JS, ctx, { filename: 'difftool-context.js' })(host);
  // module factories (compiled once; every input re-runs them for fresh module state)
  const fact: Record<string, unknown> = {};
  for (const [rel, code] of Object.entries(m.files)) {
    fact[rel] = vm.runInContext(`(function (exports, require, module) {${code}\n})`, ctx, { filename: rel });
  }
  api.init(fact, m.entry, m.exportName, m.kind, m.method ?? '', m.hostGlobals ?? []);
}

function runOne(inp: unknown): Obs {
  const t = init!.timeoutMs;
  try {
    // run the call (microtasks drain at the end of each evaluation, within the timeout)
    ctx!.__inp = JSON.stringify(inp);
    ctx!.__api = api;
    vm.runInContext('__api.run(__inp)', ctx!, { timeout: t });
    let ticks = 0;
    while (ticks < 2000 && (vm.runInContext('__api.pending()', ctx!, { timeout: t }) as boolean)) {
      vm.runInContext('__api.tick()', ctx!, { timeout: t });
      ticks++;
    }
    const obs = JSON.parse(vm.runInContext('__api.finish()', ctx!, { timeout: t }) as string) as Obs;
    // a whole program writes to stdout: UTF-8 encoding replaces lone surrogates (as in Lean's runMain)
    if (init!.kind === 'program') obs.out = obs.out.map(l => Buffer.from(l, 'utf8').toString('utf8'));
    if (ticks >= 2000) obs.kind = 'timeout';
    return obs;
  } catch (e) {
    const msg = (e as Error).message ?? String(e);
    if (/timed out/.test(msg)) return { kind: 'timeout', o: 'timeout', out: [], args: [], strict: '', unhandled: [] };
    if (/Maximum call stack/.test(msg)) return { kind: 'stack', o: 'stack overflow', out: [], args: [], strict: '', unhandled: [] };
    return { kind: 'harness', o: `harness: ${msg}`, out: [], args: [], strict: '', unhandled: [] };
  }
}

const tick = () => new Promise<void>(r => setImmediate(r));

process.on('message', async (m: InitMsg | RunMsg) => {
  try {
    if (m.type === 'init') { setup(m); process.send!({ type: 'ready' }); return; }
    if (m.type === 'run') {
      const out: Obs[] = [];
      for (const inp of m.inputs) {
        unhandled = [];
        const t0 = performance.now();
        const obs = runOne(inp);
        obs.ms = performance.now() - t0;
        await tick(); // lets 'unhandledRejection' fire for this input
        obs.unhandled = unhandled.slice();
        out.push(obs);
      }
      process.send!({ type: 'result', id: m.id, obs: out });
    }
  } catch (e) {
    process.send!({ type: 'error', message: (e as Error).stack ?? String(e) });
  }
});

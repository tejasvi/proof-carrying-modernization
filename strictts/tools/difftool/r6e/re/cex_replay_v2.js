// R6 counterexample replay (v2), independent of the difftool's runner: for every refutation in the
// chunk JSONs, transpile the pair's old and new slices to plain ES modules (TypeScript's
// transpileModule: type annotations removed, relative imports given the .mjs extension), write one
// driver per version, run it with plain `node`, and compare with what the difftool recorded.
// The driver decodes the recorded tagged input itself (object keys as own properties, so a key
// `__proto__` stays a key; -0, NaN and ±Infinity exact), fixes Math.random to 0 as the difftool's
// runner does, awaits a returned promise, waits 50 ms for timers, collects console output and
// uncaught exceptions, and prints the outcome and the final arguments in the runner's canonical
// form (objects other than plain ones that occur twice among result and arguments get #n labels,
// holes print as <hole>, plain objects' keys sorted without undefined values).
//   node scratch/r6/cex_replay_v2.js CHUNKS_DIR PAIRS_ROOT REPLAY_DIR
// Output: REPLAY_DIR/<pair>/{old,new}/(transpiled slice, driver.mjs, out.json); REPLAY_DIR/replay.tsv.
'use strict';
const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');
const ts = require('/home/user/strictts/frontend/node_modules/typescript'); // R6d: absolute (the script sits one level deeper than in R6)
const [chunks, pairsRoot, outDir] = process.argv.slice(2).map(p => path.resolve(p));

const RUNTIME = String.raw`
Math.random = () => 0;
const __log = console.log.bind(console);
const OUT = [];
console.log = (...a) => { OUT.push(a.map(x => typeof x === 'string' ? x : canon([x])[0]).join(' ')); };
const uncaught = [];
function errStr(e) {
  if (e && typeof e === 'object' && typeof e.name === 'string' && typeof e.message === 'string') return e.name + ': ' + e.message;
  return 'value ' + canon([e])[0];
}
process.on('uncaughtException', e => uncaught.push(errStr(e)));
process.on('unhandledRejection', e => uncaught.push(errStr(e)));
function decode(t) {
  switch (t.t) {
    case 'n': return t.v === 'NaN' ? NaN : t.v === 'Inf' ? Infinity : t.v === '-Inf' ? -Infinity : t.v === '-0' ? -0 : Number(t.v);
    case 's': return t.v;
    case 'b': return BigInt(t.v);
    case 'B': return t.v;
    case 'u': return undefined;
    case 'z': return null;
    case 'a': return t.v.map(decode);
    case 'o': { const o = {}; for (const [k, v] of t.v) Object.defineProperty(o, k, { value: decode(v), enumerable: true, writable: true, configurable: true }); return o; }
    case 'm': return new Map(t.v.map(([k, v]) => [decode(k), decode(v)]));
    case 'S': return new Set(t.v.map(decode));
    case 'ta': return new globalThis[t.kind](t.v.map(decode));
    case 'p': return Promise.resolve(decode(t.v));
  }
  throw new Error('replay: tagged value kind ' + t.t + ' not supported');
}
const isPlain = v => { const p = Object.getPrototypeOf(v); return p === Object.prototype || p === null; };
const str = s => JSON.stringify(s);
function canon(vals) {
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
  const ids = new Map(); let next = 0; const onStack = new Set();
  const p = (v, d) => {
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
        const ks = Object.keys(v).filter(k => v[k] !== undefined).sort();
        return '{' + ks.map(k => (/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(k) ? k : str(k)) + ': ' + p(v[k], d + 1)).join(', ') + '}';
      } finally { onStack.delete(v); }
    }
    const shared = (count.get(v) || 0) > 1;
    if (shared && ids.has(v)) return '#' + ids.get(v);
    let pre = '';
    if (shared) { ids.set(v, ++next); pre = '#' + next + '='; }
    let s;
    if (Array.isArray(v)) { const parts = []; for (let i = 0; i < v.length; i++) parts.push(i in v ? p(v[i], d + 1) : '<hole>'); s = '[' + parts.join(', ') + ']'; }
    else if (v instanceof Map) s = 'Map{' + [...v].map(([k, x]) => p(k, d + 1) + ' => ' + p(x, d + 1)).join(', ') + '}';
    else if (v instanceof Set) s = 'Set{' + [...v].map(x => p(x, d + 1)).join(', ') + '}';
    else if (ArrayBuffer.isView(v)) s = (v.constructor && v.constructor.name) + '[' + Array.from(v, x => p(x, d + 1)).join(', ') + ']';
    else if (v instanceof Date) s = 'Date(' + v.getTime() + ')';
    else if (v instanceof Error) s = 'Error(' + errStr(v) + ')';
    else if (v instanceof Promise) s = '<promise>';
    else {
      const proto = Object.getPrototypeOf(v);
      const name = proto && proto.constructor && typeof proto.constructor.name === 'string' ? proto.constructor.name : '?';
      const ks = Object.keys(v).filter(k => v[k] !== undefined).sort();
      s = name + '{' + ks.map(k => k + ': ' + p(v[k], d + 1)).join(', ') + '}';
    }
    return pre + s;
  };
  return vals.map(v => p(v, 0));
}
`;

function transpileTree(src, dst) {
  for (const ent of fs.readdirSync(src, { withFileTypes: true })) {
    const s = path.join(src, ent.name);
    if (ent.isDirectory()) { transpileTree(s, path.join(dst, ent.name)); continue; }
    if (!/\.tsx?$/.test(ent.name)) continue;
    let js = ts.transpileModule(fs.readFileSync(s, 'utf8'), { compilerOptions: { module: ts.ModuleKind.ESNext, target: ts.ScriptTarget.ES2022 } }).outputText;
    js = js.replace(/(from\s+|import\s*\(\s*)(['"])(\.{1,2}\/[^'"]+?)(\.tsx?)?\2/g, (m, a, q, p) => `${a}${q}${p}.mjs${q}`);
    fs.mkdirSync(dst, { recursive: true });
    fs.writeFileSync(path.join(dst, ent.name.replace(/\.tsx?$/, '.mjs')), js);
  }
}

const pairDir = id => ['scan'].map(d => path.join(pairsRoot, d, id)).find(d => fs.existsSync(path.join(d, 'meta.json')));
const rows = ['pair\tcall\tparts\trecorded_old\trecorded_new\treplayed_old\treplayed_new\tagree'];
let n = 0, agree = 0;
for (const f of fs.readdirSync(chunks).filter(x => x.endsWith('.json')).sort()) {
  for (const p of JSON.parse(fs.readFileSync(path.join(chunks, f), 'utf8'))) {
    for (const fn of p.functions) {
      if (fn.status !== 'changed' || fn.verdict !== 'REFUTED' || !fn.cex) continue;
      const pd = pairDir(p.id);
      if (!pd) continue;
      const meta = JSON.parse(fs.readFileSync(path.join(pd, 'meta.json'), 'utf8'));
      const parts = fn.cex.parts ?? ['outcome'];
      const res = {};
      for (const v of ['old', 'new']) {
        const d = path.join(outDir, p.id, v);
        fs.rmSync(d, { recursive: true, force: true });
        transpileTree(path.join(pd, v), d);
        const entry = './' + meta.entry.replace(/\.tsx?$/, '.mjs');
        const driver = RUNTIME + `
// counterexample of the difftool: ${fn.cex.inputText.replace(/\n/g, ' ').slice(0, 300)}
const INPUT = ${JSON.stringify(fn.cex.input)};
const args = INPUT.args.map(decode);
const mod = await import(${JSON.stringify(entry)});
const f = mod[${JSON.stringify(meta.function)}];
let o, rv = [];
try {
  const r = f(...args);
  if (r instanceof Promise) { try { const x = await r; o = 'resolve '; rv = [x]; } catch (e) { o = 'reject ' + errStr(e); } }
  else { o = 'return '; rv = [r]; }
} catch (e) { o = 'throw ' + errStr(e); }
await new Promise(res => setTimeout(res, 50));
const c = canon([...rv, ...args]);
if (rv.length) o += c[0];
__log(JSON.stringify({ outcome: o, args: c.slice(rv.length), console: OUT.concat(uncaught.map(u => '<uncaught ' + u + '>')) }));
`;
        fs.writeFileSync(path.join(d, 'driver.mjs'), driver);
        try {
          const out = execFileSync(process.execPath, [path.join(d, 'driver.mjs')], { encoding: 'utf8', timeout: 15000 });
          fs.writeFileSync(path.join(d, 'out.json'), out);
          res[v] = JSON.parse(out.trim().split('\n').pop());
        } catch (e) { res[v] = { error: String(e.message).split('\n').slice(0, 2).join(' ') }; }
      }
      const pick = (o, part) => part === 'outcome' ? o.outcome : part === 'args' ? JSON.stringify(o.args) : part === 'console' ? JSON.stringify(o.console) : undefined;
      const recPick = (o, part) => part === 'outcome' ? o.outcome : part === 'args' ? JSON.stringify(o.args) : part === 'console' ? JSON.stringify(o.console) : undefined;
      const ok = !res.old.error && !res.new.error &&
        parts.every(pt => pick(res.old, pt) === recPick(fn.cex.oldObs, pt) && pick(res.new, pt) === recPick(fn.cex.newObs, pt));
      n++; if (ok) agree++;
      const show = (o, pts) => o.error ? `error: ${o.error}` : pts.map(pt => `${pt}=${pick(o, pt)}`).join(' ; ');
      const showR = (o, pts) => pts.map(pt => `${pt}=${recPick(o, pt)}`).join(' ; ');
      rows.push([p.id, fn.cex.inputText.replace(/[\t\n]/g, ' ').slice(0, 300), parts.join(','), showR(fn.cex.oldObs, parts), showR(fn.cex.newObs, parts), show(res.old, parts), show(res.new, parts), ok ? 'yes' : 'NO'].join('\t'));
    }
  }
}
fs.mkdirSync(outDir, { recursive: true });
fs.writeFileSync(path.join(outDir, 'replay.tsv'), rows.join('\n') + '\n');
console.log(`replay: ${agree}/${n} refutations reproduced in plain node`);

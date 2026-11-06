// Type-directed random inputs and shrinking. Values are "tagged" JSON (numbers keep NaN, ±0
// and ±Infinity, bigints are decimal strings, objects keep their key order), decoded into real
// JavaScript values inside the runner's context.
import { Desc, Lit, Param, Signature, unsupportedIn } from './typedesc';
import { Rng } from './util';

export type Tagged =
  | { t: 'n'; v: number | string }
  | { t: 's'; v: string }
  | { t: 'b'; v: string }
  | { t: 'B'; v: boolean }
  | { t: 'u' } | { t: 'z' }
  | { t: 'a'; v: Tagged[] }
  | { t: 'o'; v: [string, Tagged][] }
  | { t: 'm'; v: [Tagged, Tagged][] }
  | { t: 'S'; v: Tagged[] }
  | { t: 'c'; cls: string; args: (Tagged | null)[] }
  | { t: 'ta'; kind: string; v: Tagged[] }
  | { t: 'd'; v: number }
  | { t: 'p'; v: Tagged };

/** Arguments of one call: `null` = argument omitted. */
export interface Input { args: (Tagged | null)[]; self?: (Tagged | null)[] }

export function num(x: number): Tagged {
  if (Number.isNaN(x)) return { t: 'n', v: 'NaN' };
  if (x === Infinity) return { t: 'n', v: 'Inf' };
  if (x === -Infinity) return { t: 'n', v: '-Inf' };
  if (Object.is(x, -0)) return { t: 'n', v: '-0' };
  return { t: 'n', v: x };
}

export function numVal(t: { v: number | string }): number {
  switch (t.v) { case 'NaN': return NaN; case 'Inf': return Infinity; case '-Inf': return -Infinity; case '-0': return -0; default: return Number(t.v); }
}

const SPECIAL_NUMS = [0, -0, 1, -1, 2, -2, 0.5, -0.5, 1.5, -1.5, 2.5, 0.1, 0.2, 0.3, 3, 7, 10, 100, 255, 256, 1000, 1e21, 1e-7, 123.456,
  -123.456, 2 ** 31 - 1, 2 ** 31, -(2 ** 31), -(2 ** 31) - 1, 2 ** 32 - 1, 2 ** 32, 2 ** 53 - 1, 2 ** 53, 2 ** 53 + 2, -(2 ** 53 - 1),
  -(2 ** 53), Number.MAX_VALUE, Number.MIN_VALUE, Number.EPSILON, NaN, Infinity, -Infinity, 4294967295.5, -1e-6, 0.000001];

const ALPHABET = ['a', 'b', 'c', 'x', 'A', 'Z', '0', '1', '9', ' ', ' ', '-', '_', '.', ',', '/', ':', '"', '\'', '\\', '\t', '\n',
  'é', 'ß', 'İ', 'K', ' ', '﻿', ' ', '\u0000', '😀', '\ud800', '\udc00', '\u{1f468}‍\u{1f469}'];

const SPECIAL_STRS = ['', ' ', 'a', 'abc', 'A', 'aA', '0', '1', '-1', '1.5', '10', '1e3', '0x1f', ' 42 ', 'NaN', 'Infinity', '-Infinity',
  'true', 'false', 'null', 'undefined', '__proto__', 'constructor', 'toString', 'hasOwnProperty', 'a,b', 'a b', '😀', '\ud800',
  'x'.repeat(40), '  ', '\t', 'ab'.repeat(3), 'é', 'İ'];

export interface GenCtx {
  rng: Rng;
  table: Map<number, Desc>;
  nums: number[];
  strs: string[];
  /** property names the code reads (candidate keys of client objects) */
  props?: string[];
  /** primitives generated so far for the current input (re-used to correlate parameters and elements) */
  pool?: { n: number[]; s: string[]; b: string[] };
}

function pooled<T>(g: GenCtx, key: 'n' | 's' | 'b', fresh: () => T): T {
  const pool = g.pool;
  if (pool) {
    const xs = pool[key] as unknown as T[];
    if (xs.length && g.rng.chance(0.3)) return g.rng.pick(xs);
    const v = fresh();
    xs.push(v);
    return v;
  }
  return fresh();
}

function genNum(g: GenCtx): number {
  const r = g.rng.float();
  if (r < 0.25) return g.rng.pick(SPECIAL_NUMS);
  if (r < 0.5) return g.rng.int(-10, 10);
  if (r < 0.62) return g.rng.int(-1000, 1000);
  if (r < 0.75 && g.nums.length) { const b = g.rng.pick(g.nums); return g.rng.pick([b, b, b + 1, b - 1, -b, b + 0.5]); }
  if (r < 0.85) return g.rng.int(-200, 200) / g.rng.pick([2, 4, 8, 10, 3]);
  if (r < 0.9) {
    const buf = new DataView(new ArrayBuffer(8));
    buf.setUint32(0, Number(g.rng.nextU64() & 0xffffffffn)); buf.setUint32(4, Number(g.rng.nextU64() & 0xffffffffn));
    return buf.getFloat64(0);
  }
  return g.rng.pick([2 ** 31, 2 ** 32, 2 ** 53, 2 ** 30]) + g.rng.int(-3, 3);
}

function genStr(g: GenCtx): string {
  const r = g.rng.float();
  if (r < 0.25) return g.rng.pick(SPECIAL_STRS);
  if (r < 0.55 && g.strs.length) {
    const b = g.rng.pick(g.strs);
    const k = g.rng.below(6);
    if (k === 0) return b + g.rng.pick(ALPHABET);
    if (k === 1) return g.rng.pick(ALPHABET) + b;
    if (k === 2) return b.toUpperCase();
    if (k === 3) return ' ' + b + ' ';
    if (k === 4 && g.strs.length > 1) return b + g.rng.pick(g.strs);
    return b;
  }
  const len = g.rng.pick([0, 1, 1, 2, 3, 3, 4, 5, 6, 8, 12]);
  let s = '';
  const simple = g.rng.chance(0.5);
  for (let i = 0; i < len; i++) s += simple ? g.rng.pick(['a', 'b', 'c', 'x', 'y', ' ', '1', '0']) : g.rng.pick(ALPHABET);
  return s;
}

function genBig(g: GenCtx): string {
  const r = g.rng.float();
  if (r < 0.3) return g.rng.pick(['0', '1', '-1', '2', '10', '9007199254740993', '18446744073709551616', '-9223372036854775808', '9223372036854775807', '4294967296']);
  if (r < 0.45 && g.nums.length) { const b = g.rng.pick(g.nums); if (Number.isInteger(b)) return String(BigInt(b)); }
  return String(g.rng.int(-1000, 1000));
}

function litTagged(v: Lit): Tagged {
  return v as Tagged;
}

function arrLen(g: GenCtx, depth: number): number {
  if (depth > 3) return g.rng.chance(0.7) ? 0 : 1;
  return g.rng.pick([0, 0, 1, 1, 1, 2, 2, 3, 3, 4, 5, 6, 8, 12]);
}

/** Does `d` (transitively) need recursion through required positions? (used to pick finite union members) */
function isRecursive(d: Desc, g: GenCtx, seen = new Set<number>()): boolean {
  switch (d.k) {
    case 'ref': { if (seen.has(d.id)) return true; const t = g.table.get(d.id); if (!t) return false; seen.add(d.id); const r = isRecursive(t, g, seen); seen.delete(d.id); return r; }
    case 'obj': return d.fields.some(f => !f.opt && isRecursive(f.t, g, seen));
    case 'tup': return d.ts.slice(0, d.req).some(x => isRecursive(x, g, seen));
    case 'union': return d.ts.every(x => isRecursive(x, g, seen));
    case 'class': return d.ctor.some(p => !p.opt && isRecursive(p.t, g, seen));
    default: return false;
  }
}

export function gen(d: Desc, g: GenCtx, depth = 0): Tagged {
  if (depth > 12) throw new Error('cannot generate a finite value (recursive type)');
  switch (d.k) {
    case 'num': return num(pooled(g, 'n', () => genNum(g)));
    case 'str': return { t: 's', v: pooled(g, 's', () => genStr(g)) };
    case 'bool': return { t: 'B', v: g.rng.chance(0.5) };
    case 'big': return { t: 'b', v: pooled(g, 'b', () => genBig(g)) };
    case 'undef': return { t: 'u' };
    case 'null': return { t: 'z' };
    case 'lit': return litTagged(d.v);
    case 'arr': {
      const n = arrLen(g, depth);
      const v: Tagged[] = [];
      for (let i = 0; i < n; i++) v.push(i > 0 && g.rng.chance(0.2) ? v[g.rng.below(i)] : gen(d.t, g, depth + 1));
      return { t: 'a', v };
    }
    case 'tup': {
      const v: Tagged[] = [];
      const n = d.req + g.rng.below(d.ts.length - d.req + 1);
      for (let i = 0; i < n; i++) v.push(gen(d.ts[i], g, depth + 1));
      if (d.rest && n === d.ts.length) { const m = arrLen(g, depth); for (let i = 0; i < m; i++) v.push(gen(d.rest, g, depth + 1)); }
      return { t: 'a', v };
    }
    case 'obj': {
      const v: [string, Tagged][] = [];
      for (const f of d.fields) {
        if (f.opt && (depth > 3 ? g.rng.chance(0.8) : g.rng.chance(0.4))) continue;
        if (f.opt && unsupportedIn(f.t, g.table)) continue; // optional fields of types that are not generated stay absent
        v.push([f.name, gen(f.t, g, depth + 1)]);
      }
      if (d.index) {
        const n = depth > 3 ? 0 : g.rng.pick([0, 1, 2, 3, 4]);
        const used = new Set(v.map(e => e[0]));
        for (let i = 0; i < n; i++) {
          const k = d.index.key === 'num' ? String(g.rng.pick([0, 1, 2, 10, 3])) :
            g.rng.chance(0.3) ? String(g.rng.pick([0, 1, 2, 10, 3])) : g.rng.chance(0.5) && g.strs.length ? g.rng.pick(g.strs) : g.rng.pick(['a', 'b', 'key', 'x', 'B', '_']);
          if (used.has(k)) continue;
          used.add(k);
          v.push([k, gen(d.index.t, g, depth + 1)]);
        }
      }
      return { t: 'o', v };
    }
    case 'union': {
      let ms = d.ts.filter(m => !unsupportedIn(m, g.table));
      if (!ms.length) ms = d.ts;
      if (depth > 3) {
        // deep inside a recursive type: only members with the shallowest finite values
        const ds = ms.map(m => minDepth(m, g));
        const best = Math.min(...ds);
        if (Number.isFinite(best)) ms = ms.filter((_, i) => ds[i] === best);
      }
      return gen(g.rng.pick(ms), g, depth + 1);
    }
    case 'map': {
      const n = depth > 3 ? 0 : g.rng.pick([0, 1, 1, 2, 3, 4]);
      const v: [Tagged, Tagged][] = [];
      for (let i = 0; i < n; i++) v.push([gen(d.key, g, depth + 1), gen(d.val, g, depth + 1)]);
      return { t: 'm', v };
    }
    case 'set': {
      const n = depth > 3 ? 0 : g.rng.pick([0, 1, 2, 3, 4, 5]);
      const v: Tagged[] = [];
      for (let i = 0; i < n; i++) v.push(gen(d.t, g, depth + 1));
      return { t: 'S', v };
    }
    case 'class': return { t: 'c', cls: d.name, args: genParams(d.ctor, g, depth + 1) };
    case 'ta': {
      const n = arrLen(g, depth);
      const v: Tagged[] = [];
      const big = d.kind.startsWith('Big');
      for (let i = 0; i < n; i++) v.push(big ? { t: 'b', v: genBig(g) } : num(g.rng.chance(0.5) ? g.rng.int(-300, 300) : genNum(g)));
      return { t: 'ta', kind: d.kind, v };
    }
    case 'date': return { t: 'd', v: g.rng.pick([0, 1e12, -1, 1700000000000, 1761177600000 + g.rng.int(-1e9, 1e9), 8.64e15]) };
    case 'promise': return { t: 'p', v: gen(d.t, g, depth + 1) };
    case 'ref': {
      const t = g.table.get(d.id);
      if (!t) throw new Error('unresolved type reference');
      return gen(t, g, depth + 1);
    }
    case 'unknown': return genUnknown(g, depth, !!d.objOnly);
    case 'fn': throw new Error('function-typed values are not generated');
    case 'unsupported': throw new Error(`unsupported type: ${d.why}`);
  }
}

const DANGER_KEYS = ['constructor', 'toString', '__proto__', 'valueOf', 'hasOwnProperty', '', '__name__', 'prototype', 'then', 'length'];
/** keys that break naive key handling (prototype members, the empty key, Firestore-reserved names) */
const DANGER_AS_KEYS = DANGER_KEYS.slice(0, 7);

function unknownKey(g: GenCtx): string {
  const props = g.props ?? [];
  const r = g.rng.float();
  if (props.length && r < 0.65) return g.rng.pick(props);
  if (r < 0.8) return g.rng.pick(DANGER_AS_KEYS);
  if (g.strs.length && r < 0.9) return g.rng.pick(g.strs);
  return g.rng.pick(['a', 'b', 'id', 'name', 'type', 'x', '0']);
}

/** Arbitrary JSON-like values (client data): every type; objects keyed by the property names the
 * code reads, prototype-related names and mined literals; strings often prototype member names. */
function genUnknown(g: GenCtx, depth: number, objOnly: boolean): Tagged {
  const r = g.rng.float();
  if (!objOnly && depth < 6) {
    if (r < 0.08) return { t: 'u' };
    if (r < 0.14) return { t: 'z' };
    if (r < 0.2) return { t: 'B', v: g.rng.chance(0.5) };
    if (r < 0.3) return num(genNum(g));
    if (r < 0.5) return { t: 's', v: g.rng.chance(0.4) ? g.rng.pick(DANGER_KEYS.slice(0, 5)) : genStr(g) };
    if (r < 0.58) { const n = depth > 3 ? 0 : g.rng.pick([0, 1, 2, 3]); const v: Tagged[] = []; for (let i = 0; i < n; i++) v.push(genUnknown(g, depth + 1, false)); return { t: 'a', v }; }
  }
  const n = depth > 3 ? g.rng.pick([0, 1]) : g.rng.pick([0, 1, 1, 2, 2, 3, 4]);
  const v: [string, Tagged][] = [];
  const used = new Set<string>();
  for (let i = 0; i < n; i++) {
    const k = unknownKey(g);
    if (used.has(k)) continue;
    used.add(k);
    v.push([k, genUnknown(g, depth + 1, false)]);
  }
  return { t: 'o', v };
}

/** Prototype-pollution sweep for `unknown` parameters: prototype member names as values at one
 * and two levels of the property names the code reads, and as keys. */
export function poisonValues(g: GenCtx): Tagged[] {
  const props = (g.props ?? []).slice(0, 10);
  const out: Tagged[] = [];
  for (const d of DANGER_KEYS.slice(0, 5)) {
    const s: Tagged = { t: 's', v: d };
    out.push(s);
    for (const k of props) {
      out.push({ t: 'o', v: [[k, s]] });
      for (const k2 of props) out.push({ t: 'o', v: [[k, { t: 'o', v: [[k2, s]] }]] });
    }
  }
  for (const d of DANGER_AS_KEYS) {
    out.push({ t: 'o', v: [[d, { t: 's', v: 'x' }]] });
    for (const k of props) out.push({ t: 'o', v: [[k, { t: 'o', v: [[d, { t: 's', v: 'x' }]] }]] });
  }
  return out;
}

function containsRef(d: Desc): boolean {
  switch (d.k) {
    case 'ref': return true;
    case 'arr': case 'set': case 'promise': return false;
    case 'tup': return d.ts.slice(0, d.req).some(containsRef);
    case 'union': return d.ts.every(containsRef);
    default: return false;
  }
}

export function genParams(ps: Param[], g: GenCtx, depth = 0): (Tagged | null)[] {
  const out: (Tagged | null)[] = [];
  for (const p of ps) {
    if (p.rest) {
      const ad = p.t.k === 'arr' ? p.t.t : p.t.k === 'ref' ? null : null;
      const n = g.rng.pick([0, 1, 2, 3]);
      if (ad) for (let i = 0; i < n; i++) out.push(gen(ad, g, depth + 1));
      break;
    }
    if (p.opt && g.rng.chance(0.3)) { out.push(null); continue; }
    out.push(gen(p.t, g, depth));
  }
  // omitted trailing arguments are dropped; omitted middle ones are passed as undefined
  while (out.length && out[out.length - 1] === null) out.pop();
  return out.map(x => x === null ? { t: 'u' } as Tagged : x);
}

export function genInput(sig: Signature, g: GenCtx): Input {
  g.pool = { n: [], s: [], b: [] };
  try {
    const inp: Input = { args: genParams(sig.params, g) };
    if (sig.self) inp.self = genParams(sig.self.ctor, g);
    return inp;
  } finally { g.pool = undefined; }
}

/** A fixed set of boundary inputs: every parameter at a few special values, the others at simple ones. */
export function boundaryInputs(sig: Signature, g: GenCtx): Input[] {
  const simple = (d: Desc): Tagged | null => {
    switch (d.k) {
      case 'num': return num(1); case 'str': return { t: 's', v: 'a' }; case 'bool': return { t: 'B', v: true };
      case 'big': return { t: 'b', v: '1' }; case 'undef': return { t: 'u' }; case 'null': return { t: 'z' }; case 'lit': return litTagged(d.v);
      case 'arr': return { t: 'a', v: [] }; case 'map': return { t: 'm', v: [] }; case 'set': return { t: 'S', v: [] };
      case 'unknown': return d.objOnly ? { t: 'o', v: [] } : { t: 'u' };
      default: return null;
    }
  };
  const specials = (d: Desc): Tagged[] => {
    switch (d.k) {
      case 'num': return [0, -0, NaN, Infinity, -Infinity, -1, 0.5, -0.5, 2 ** 31, 2 ** 32, 2 ** 53, -(2 ** 31) - 1, 1e21].map(num);
      case 'str': return ['', ' ', '😀', '\ud800', 'NaN', '0', ' 1 ', 'A', '__proto__'].map(v => ({ t: 's', v }) as Tagged);
      case 'big': return ['0', '-1', '9007199254740993', '18446744073709551616'].map(v => ({ t: 'b', v }) as Tagged);
      case 'bool': return [{ t: 'B', v: false }, { t: 'B', v: true }];
      case 'arr': { const e = specials(d.t); return [{ t: 'a', v: [] }, ...(e.length ? [{ t: 'a', v: e.slice(0, 4) } as Tagged, { t: 'a', v: [e[0], e[0]] } as Tagged] : [])]; }
      case 'union': return d.ts.flatMap(m => { const s = simple(m); return s ? [s] : []; });
      default: return [];
    }
  };
  const out: Input[] = [];
  const base: (Tagged | null)[] = sig.params.filter(p => !p.rest).map(p => { const s = simple(p.t); return s ?? safeGen(p.t, g); });
  if (base.some(b => b === null)) return out;
  sig.params.filter(p => !p.rest).forEach((p, i) => {
    for (const s of specials(p.t)) {
      const args = base.slice() as Tagged[];
      args[i] = s;
      const inp: Input = { args };
      if (sig.self) inp.self = genParams(sig.self.ctor, g);
      out.push(inp);
    }
  });
  // prototype-pollution sweep for unknown parameters (other parameters at simple values)
  sig.params.filter(p => !p.rest).forEach((p, i) => {
    if (p.t.k !== 'unknown') return;
    for (const v of poisonValues(g)) {
      const args = base.slice() as Tagged[];
      args[i] = v;
      const inp: Input = { args };
      if (sig.self) inp.self = genParams(sig.self.ctor, g);
      out.push(inp);
    }
  });
  // the same special number (or string) everywhere: membership and equality corner cases
  const fill = (d: Desc, v: Tagged, s: Tagged): Tagged | null => {
    switch (d.k) {
      case 'num': return v; case 'str': return s;
      case 'arr': { const e = fill(d.t, v, s); return e ? { t: 'a', v: [e] } : { t: 'a', v: [] }; }
      case 'set': { const e = fill(d.t, v, s); return { t: 'S', v: e ? [e] : [] }; }
      case 'map': { const k = fill(d.key, v, s), x = fill(d.val, v, s); return { t: 'm', v: k && x ? [[k, x]] : [] }; }
      default: return simple(d);
    }
  };
  for (const [v, s] of [[NaN, ''], [-0, ' '], [0, 'a'], [Infinity, '0']] as const) {
    const args = sig.params.filter(p => !p.rest).map(p => fill(p.t, num(v), { t: 's', v: s }));
    if (args.some(a => a === null)) continue;
    const inp: Input = { args: args as Tagged[] };
    if (sig.self) inp.self = genParams(sig.self.ctor, g);
    out.push(inp);
  }
  return out;
}

function safeGen(d: Desc, g: GenCtx): Tagged | null {
  try { return gen(d, g); } catch { return null; }
}

// ---------------------------------------------------------------------------------------
// Shrinking: candidate simplifications of one value, most aggressive first.

export function size(t: Tagged | null): number {
  return t === null ? 0 : JSON.stringify(t).length;
}

function shrinkNum(x: number): number[] {
  const out: number[] = [];
  if (Number.isNaN(x) || !Number.isFinite(x)) return [0, 1, -1];
  if (Object.is(x, -0)) return [0];
  if (x === 0) return [];
  out.push(0);
  if (x < 0) out.push(-x);
  if (!Number.isInteger(x)) out.push(Math.trunc(x), Math.round(x));
  if (Math.abs(x) > 2) out.push(Math.trunc(x / 2));
  if (Math.abs(x) > 1 && Number.isInteger(x)) out.push(x - Math.sign(x));
  if (x !== 1 && x !== -1) out.push(x > 0 ? 1 : -1);
  return out.filter((v, i, a) => !Object.is(v, x) && a.findIndex(w => Object.is(w, v)) === i);
}

function shrinkStr(s: string): string[] {
  const out: string[] = [];
  if (s === '') return out;
  out.push('');
  if (s.length > 1) out.push(s.slice(0, s.length >> 1), s.slice(s.length >> 1));
  for (let i = 0; i < s.length && i < 12; i++) out.push(s.slice(0, i) + s.slice(i + 1));
  const simple = s.replace(/[^a-z0-9 ]/g, 'a');
  if (simple !== s) out.push(simple);
  return [...new Set(out)].filter(v => v !== s);
}

function minimal(d: Desc, g: GenCtx, depth = 0): Tagged | null {
  if (depth > 8) return null;
  switch (d.k) {
    case 'num': return num(0); case 'str': return { t: 's', v: '' }; case 'bool': return { t: 'B', v: false };
    case 'big': return { t: 'b', v: '0' }; case 'undef': return { t: 'u' }; case 'null': return { t: 'z' }; case 'lit': return litTagged(d.v);
    case 'arr': return { t: 'a', v: [] }; case 'map': return { t: 'm', v: [] }; case 'set': return { t: 'S', v: [] };
    case 'ta': return { t: 'ta', kind: d.kind, v: [] };
    case 'ref': { const t = g.table.get(d.id); return t ? minimal(t, g, depth + 1) : null; }
    case 'obj': {
      const v: [string, Tagged][] = [];
      for (const f of d.fields) { if (f.opt) continue; const m = minimal(f.t, g, depth + 1); if (!m) return null; v.push([f.name, m]); }
      return { t: 'o', v };
    }
    case 'union': { for (const m of d.ts) { const x = minimal(m, g, depth + 1); if (x) return x; } return null; }
    case 'tup': { const v: Tagged[] = []; for (const x of d.ts.slice(0, d.req)) { const m = minimal(x, g, depth + 1); if (!m) return null; v.push(m); } return { t: 'a', v }; }
    default: return null;
  }
}

function resolve(d: Desc, g: { table: Map<number, Desc> }): Desc {
  let x = d;
  for (let i = 0; x.k === 'ref' && i < 50; i++) x = g.table.get(x.id) ?? { k: 'unsupported', why: 'ref' };
  return x;
}

/** Which union member a value belongs to (by its tag; the first compatible member). */
/** Depth of the shallowest finite value of a type (arrays, maps, sets and optional fields can be empty). */
export function minDepth(d: Desc, g: { table: Map<number, Desc> }, memo = new Map<number, number>()): number {
  switch (d.k) {
    case 'ref': {
      if (memo.has(d.id)) return memo.get(d.id)!;
      memo.set(d.id, Infinity);
      const t = g.table.get(d.id);
      // iterate to a fixpoint (recursive types)
      let v = Infinity;
      for (let i = 0; i < 8 && t; i++) { const nv = minDepth(t, g, memo); memo.set(d.id, nv); if (nv === v) break; v = nv; }
      return v;
    }
    case 'obj': return 1 + Math.max(0, ...d.fields.filter(f => !f.opt).map(f => minDepth(f.t, g, memo)));
    case 'tup': return 1 + Math.max(0, ...d.ts.slice(0, d.req).map(x => minDepth(x, g, memo)));
    case 'union': return Math.min(...d.ts.map(x => minDepth(x, g, memo)));
    case 'class': return 1 + Math.max(0, ...d.ctor.filter(p => !p.opt).map(p => minDepth(p.t, g, memo)));
    case 'promise': return 1 + minDepth(d.t, g, memo);
    case 'unsupported': case 'fn': return Infinity;
    default: return 0;
  }
}

export function memberFor(d: Desc & { k: 'union' }, v: Tagged, g: { table: Map<number, Desc> }): Desc | undefined {
  for (const m0 of d.ts) {
    const m = resolve(m0, g);
    if (m.k === 'lit' && JSON.stringify(m.v) === JSON.stringify(v)) return m;
    if ((m.k === 'num' && v.t === 'n') || (m.k === 'str' && v.t === 's') || (m.k === 'big' && v.t === 'b') || (m.k === 'bool' && v.t === 'B') ||
        (m.k === 'undef' && v.t === 'u') || (m.k === 'null' && v.t === 'z') || ((m.k === 'arr' || m.k === 'tup') && v.t === 'a') ||
        (m.k === 'obj' && v.t === 'o') || (m.k === 'map' && v.t === 'm') || (m.k === 'set' && v.t === 'S') || (m.k === 'class' && v.t === 'c')) return m;
  }
  return undefined;
}

export function shrinkValue(d0: Desc, v: Tagged, g: GenCtx, depth = 0): Tagged[] {
  const d = resolve(d0, g);
  if (depth > 6) return [];
  switch (d.k) {
    case 'num': return v.t === 'n' ? shrinkNum(numVal(v)).map(num) : [];
    case 'str': return v.t === 's' ? shrinkStr(v.v).map(s => ({ t: 's', v: s }) as Tagged) : [];
    case 'big': return v.t === 'b' && v.v !== '0' ? [{ t: 'b', v: '0' }, ...(BigInt(v.v) > 1n || BigInt(v.v) < -1n ? [{ t: 'b', v: String(BigInt(v.v) / 2n) } as Tagged] : [])] : [];
    case 'bool': return v.t === 'B' && v.v ? [{ t: 'B', v: false }] : [];
    case 'arr': case 'ta': {
      if (v.t !== 'a' && v.t !== 'ta') return [];
      const xs = v.v;
      const mk = (ys: Tagged[]): Tagged => v.t === 'ta' ? { t: 'ta', kind: v.kind, v: ys } : { t: 'a', v: ys };
      const out: Tagged[] = [];
      if (xs.length) out.push(mk([]));
      if (xs.length > 2) out.push(mk(xs.slice(0, xs.length >> 1)), mk(xs.slice(xs.length >> 1)));
      for (let i = 0; i < xs.length && i < 10; i++) out.push(mk([...xs.slice(0, i), ...xs.slice(i + 1)]));
      const et: Desc = d.k === 'arr' ? d.t : (d.kind.startsWith('Big') ? { k: 'big' } : { k: 'num' });
      for (let i = 0; i < xs.length && i < 6; i++) for (const s of shrinkValue(et, xs[i], g, depth + 1).slice(0, 3)) out.push(mk([...xs.slice(0, i), s, ...xs.slice(i + 1)]));
      return out;
    }
    case 'tup': {
      if (v.t !== 'a') return [];
      const out: Tagged[] = [];
      if (v.v.length > d.req) out.push({ t: 'a', v: v.v.slice(0, d.req) });
      v.v.forEach((x, i) => { const et = i < d.ts.length ? d.ts[i] : d.rest; if (et) for (const s of shrinkValue(et, x, g, depth + 1).slice(0, 4)) out.push({ t: 'a', v: [...v.v.slice(0, i), s, ...v.v.slice(i + 1)] }); });
      return out;
    }
    case 'obj': {
      if (v.t !== 'o') return [];
      const out: Tagged[] = [];
      v.v.forEach(([k], i) => {
        const f = d.fields.find(f => f.name === k);
        if (!f || f.opt) out.push({ t: 'o', v: [...v.v.slice(0, i), ...v.v.slice(i + 1)] });
      });
      v.v.forEach(([k, x], i) => {
        const f = d.fields.find(f => f.name === k);
        const ft = f ? f.t : d.index?.t;
        if (ft) for (const s of shrinkValue(ft, x, g, depth + 1).slice(0, 4)) out.push({ t: 'o', v: [...v.v.slice(0, i), [k, s], ...v.v.slice(i + 1)] });
      });
      return out;
    }
    case 'union': {
      const out: Tagged[] = [];
      const m = memberFor(d, v, g);
      for (const o of d.ts) { const x = minimal(o, g); if (x && JSON.stringify(x) !== JSON.stringify(v) && size(x) < size(v)) out.push(x); }
      if (m) out.push(...shrinkValue(m, v, g, depth + 1));
      return out;
    }
    case 'map': {
      if (v.t !== 'm') return [];
      const out: Tagged[] = [];
      if (v.v.length) out.push({ t: 'm', v: [] });
      for (let i = 0; i < v.v.length; i++) out.push({ t: 'm', v: [...v.v.slice(0, i), ...v.v.slice(i + 1)] });
      v.v.forEach(([k, x], i) => {
        for (const s of shrinkValue(d.key, k, g, depth + 1).slice(0, 3)) out.push({ t: 'm', v: [...v.v.slice(0, i), [s, x], ...v.v.slice(i + 1)] });
        for (const s of shrinkValue(d.val, x, g, depth + 1).slice(0, 3)) out.push({ t: 'm', v: [...v.v.slice(0, i), [k, s], ...v.v.slice(i + 1)] });
      });
      return out;
    }
    case 'set': {
      if (v.t !== 'S') return [];
      const out: Tagged[] = [];
      if (v.v.length) out.push({ t: 'S', v: [] });
      for (let i = 0; i < v.v.length; i++) out.push({ t: 'S', v: [...v.v.slice(0, i), ...v.v.slice(i + 1)] });
      v.v.forEach((x, i) => { for (const s of shrinkValue(d.t, x, g, depth + 1).slice(0, 3)) out.push({ t: 'S', v: [...v.v.slice(0, i), s, ...v.v.slice(i + 1)] }); });
      return out;
    }
    case 'class': {
      if (v.t !== 'c') return [];
      return shrinkArgs(d.ctor, v.args, g, depth + 1).map(args => ({ t: 'c', cls: v.cls, args }) as Tagged);
    }
    case 'promise': return v.t === 'p' ? shrinkValue(d.t, v.v, g, depth + 1).map(x => ({ t: 'p', v: x }) as Tagged) : [];
    case 'unknown': {
      const out: Tagged[] = [];
      if (!d.objOnly && v.t !== 'u') out.push({ t: 'u' });
      if (d.objOnly && !(v.t === 'o' && v.v.length === 0)) out.push({ t: 'o', v: [] });
      const any: Desc = { k: 'unknown' };
      if (v.t === 'a') { for (let i = 0; i < v.v.length && i < 8; i++) out.push({ t: 'a', v: [...v.v.slice(0, i), ...v.v.slice(i + 1)] }); v.v.forEach((x, i) => { for (const s of shrinkValue(any, x, g, depth + 1).slice(0, 3)) out.push({ t: 'a', v: [...v.v.slice(0, i), s, ...v.v.slice(i + 1)] }); }); }
      else if (v.t === 'o') { for (let i = 0; i < v.v.length; i++) out.push({ t: 'o', v: [...v.v.slice(0, i), ...v.v.slice(i + 1)] }); v.v.forEach(([k, x], i) => { for (const s of shrinkValue(any, x, g, depth + 1).slice(0, 3)) out.push({ t: 'o', v: [...v.v.slice(0, i), [k, s], ...v.v.slice(i + 1)] }); }); }
      else if (v.t === 'n') out.push(...shrinkNum(numVal(v)).map(num));
      else if (v.t === 's') out.push(...shrinkStr(v.v).map(s => ({ t: 's', v: s }) as Tagged));
      return out;
    }
    default: return [];
  }
}

export function shrinkArgs(ps: Param[], args: (Tagged | null)[], g: GenCtx, depth = 0): (Tagged | null)[][] {
  const out: (Tagged | null)[][] = [];
  // drop trailing optional / rest arguments
  for (let n = args.length - 1; n >= 0; n--) {
    const p = ps[Math.min(n, ps.length - 1)];
    if (p && (p.opt || p.rest)) out.push(args.slice(0, n)); else break;
  }
  args.forEach((a, i) => {
    if (a === null) return;
    const p = ps[Math.min(i, ps.length - 1)];
    if (!p) return;
    const pd: Desc = p.rest ? (p.t.k === 'arr' ? p.t.t : p.t) : p.t;
    for (const s of shrinkValue(pd, a, g, depth)) out.push([...args.slice(0, i), s, ...args.slice(i + 1)]);
  });
  return out;
}

export function shrinkInput(sig: Signature, inp: Input, g: GenCtx): Input[] {
  const out: Input[] = shrinkArgs(sig.params, inp.args, g).map(args => ({ ...inp, args }));
  if (sig.self && inp.self) for (const self of shrinkArgs(sig.self.ctor, inp.self, g)) out.push({ ...inp, self });
  return out;
}

export function inputSize(inp: Input): number {
  return inp.args.reduce((s, a) => s + size(a), 0) + (inp.self ? inp.self.reduce((s, a) => s + size(a), 0) : 0);
}

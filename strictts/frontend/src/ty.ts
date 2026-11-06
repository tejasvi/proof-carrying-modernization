// StrictTS types (mirror of `StrictTS/Core/Ty.lean`), printing to Lean, canonical order.

export type TAKind = 'i8' | 'u8' | 'u8c' | 'i16' | 'u16' | 'i32' | 'u32' | 'f32' | 'f64' | 'bi64' | 'bu64';

export type Ty =
  | { k: 'num' } | { k: 'bigint' } | { k: 'bool' } | { k: 'str' } | { k: 'undef' } | { k: 'null' } | { k: 'err' }
  | { k: 'arr'; t: Ty }
  | { k: 'tarr'; kind: TAKind }
  | { k: 'map'; key: Ty; val: Ty }
  | { k: 'set'; t: Ty }
  | { k: 'tup'; ts: Ty[] }
  | { k: 'record'; fs: Field[] }
  | { k: 'obj'; c: string }
  | { k: 'named'; n: string }
  | { k: 'opt'; t: Ty }
  | { k: 'union'; ts: Ty[] }
  | { k: 'enum'; cases: string[] }
  | { k: 'fn'; args: Ty[]; ret: Ty }
  | { k: 'promise'; t: Ty }
  | { k: 'box'; t: Ty }
  /** an object of an external (library / host) type: an opaque handle with identity */
  | { k: 'ext'; name: string }
  /** an object used as a dictionary (`{ [k: string]: T }`, `Record<string, T>`) */
  | { k: 'dict'; t: Ty }
  /** a value of type `unknown`: any value with its runtime type */
  | { k: 'dyn' };

export interface Field { name: string; ty: Ty }

export const T = {
  num: { k: 'num' } as Ty,
  bigint: { k: 'bigint' } as Ty,
  bool: { k: 'bool' } as Ty,
  str: { k: 'str' } as Ty,
  undef: { k: 'undef' } as Ty,
  null: { k: 'null' } as Ty,
  err: { k: 'err' } as Ty,
  arr: (t: Ty): Ty => ({ k: 'arr', t }),
  tarr: (kind: TAKind): Ty => ({ k: 'tarr', kind }),
  map: (key: Ty, val: Ty): Ty => ({ k: 'map', key, val }),
  set: (t: Ty): Ty => ({ k: 'set', t }),
  tup: (ts: Ty[]): Ty => ({ k: 'tup', ts }),
  record: (fs: Field[]): Ty => ({ k: 'record', fs }),
  obj: (c: string): Ty => ({ k: 'obj', c }),
  named: (n: string): Ty => ({ k: 'named', n }),
  opt: (t: Ty): Ty => ({ k: 'opt', t }),
  union: (ts: Ty[]): Ty => ({ k: 'union', ts }),
  enum: (cases: string[]): Ty => ({ k: 'enum', cases }),
  fn: (args: Ty[], ret: Ty): Ty => ({ k: 'fn', args, ret }),
  promise: (t: Ty): Ty => ({ k: 'promise', t }),
  box: (t: Ty): Ty => ({ k: 'box', t }),
  ext: (name: string): Ty => ({ k: 'ext', name }),
  dict: (t: Ty): Ty => ({ k: 'dict', t }),
  dyn: { k: 'dyn' } as Ty,
};

/** A `RegExp` value: the record of its flags and source (regex.ts). Its `lastIndex` is not
 * modelled: `test` / `exec` on a global or sticky one are rejected or panic. */
export const REGEXP_TY: Ty = T.record([{ name: 'flags', ty: T.str }, { name: 'source', ty: T.str }]);

/** Node's timer handle (`NodeJS.Timeout`, an object in Node) holding the number the semantics'
 * `setTimeout` returns: it can be stored, passed, tested for `null` / `undefined` and for
 * truthiness (an object: always true); its number (Node's `Symbol.toPrimitive`) is not
 * observable (no strings, arithmetic, comparisons, methods or unknown values: `timer-handle`). */
export const TIMER_TY: Ty = T.record([{ name: '$timer', ty: T.num }]);

/** A Lean string literal. Lean strings cannot hold lone surrogates; callers that may meet
 * them use `leanJSStr`. */
export function leanStrLit(s: string): string {
  let out = '"';
  for (const ch of s) {
    const c = ch.codePointAt(0)!;
    if (ch === '"') out += '\\"';
    else if (ch === '\\') out += '\\\\';
    else if (ch === '\n') out += '\\n';
    else if (ch === '\t') out += '\\t';
    else if (ch === '\r') out += '\\r';
    else if (c < 0x20 || c === 0x7f) out += '\\x' + c.toString(16).padStart(2, '0');
    else if (c >= 0xd800 && c < 0xe000) throw new Error('lone surrogate in Lean string');
    else out += ch;
  }
  return out + '"';
}

export function hasLoneSurrogate(s: string): boolean {
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c >= 0xd800 && c < 0xdc00) {
      const d = i + 1 < s.length ? s.charCodeAt(i + 1) : 0;
      if (d >= 0xdc00 && d < 0xe000) { i++; continue; }
      return true;
    }
    if (c >= 0xdc00 && c < 0xe000) return true;
  }
  return false;
}

/** A `JSStr` term for a JavaScript string (UTF-16 units). */
export function leanJSStr(s: string): string {
  if (hasLoneSurrogate(s)) {
    const units: number[] = [];
    for (let i = 0; i < s.length; i++) units.push(s.charCodeAt(i));
    return `(⟨[${units.join(', ')}]⟩ : JSStr)`;
  }
  return `(js! ${leanStrLit(s)})`;
}

export function tyEq(a: Ty, b: Ty): boolean {
  return tyKey(a) === tyKey(b);
}

/** Canonical key of a type (also its Lean printing). */
export function tyKey(t: Ty): string {
  return showTy(t);
}

function showTys(ts: Ty[]): string {
  return `tys[${ts.map(showTy).join(', ')}]`;
}

export function showFields(fs: Field[]): string {
  return `flds[${fs.map(f => `${leanStrLit(f.name)} : ${showTy(f.ty)}`).join(', ')}]`;
}

/** Lean term of type `Ty`, always self-delimiting (atomic or parenthesised). */
export function showTy(t: Ty): string {
  switch (t.k) {
    case 'num': case 'bigint': case 'bool': case 'str': case 'undef': case 'null': case 'err':
      return '.' + t.k;
    case 'arr': return `(.arr ${showTy(t.t)})`;
    case 'tarr': return `(.tarr .${t.kind})`;
    case 'map': return `(.map ${showTy(t.key)} ${showTy(t.val)})`;
    case 'set': return `(.set ${showTy(t.t)})`;
    case 'tup': return `(.tup ${showTys(t.ts)})`;
    case 'record': return `(.record ${showFields(t.fs)})`;
    case 'obj': return `(.obj ${leanStrLit(t.c)})`;
    case 'named': return `(.named ${leanStrLit(t.n)})`;
    case 'opt': return `(.opt ${showTy(t.t)})`;
    case 'union': return `(.union ${showTys(t.ts)})`;
    case 'enum': return `(.enum [${t.cases.map(leanStrLit).join(', ')}])`;
    case 'fn': return `(.fn ${showTys(t.args)} ${showTy(t.ret)})`;
    case 'promise': return `(.promise ${showTy(t.t)})`;
    case 'box': return `(.box ${showTy(t.t)})`;
    case 'ext': return `(.ext ${leanStrLit(t.name)})`;
    case 'dict': return `(.dict ${showTy(t.t)})`;
    case 'dyn': return '.dyn';
  }
}

export { showTys };

/** Human-readable TypeScript-like rendering (diagnostics). */
export function prettyTy(t: Ty): string {
  if (t.k === 'record' && t.fs.length === 1 && t.fs[0].name === '$timer') return 'NodeJS.Timeout';
  switch (t.k) {
    case 'num': return 'number';
    case 'bigint': return 'bigint';
    case 'bool': return 'boolean';
    case 'str': return 'string';
    case 'undef': return 'undefined';
    case 'null': return 'null';
    case 'err': return 'Error';
    case 'arr': return `${prettyTy(t.t)}[]`;
    case 'tarr': return `TypedArray<${t.kind}>`;
    case 'map': return `Map<${prettyTy(t.key)}, ${prettyTy(t.val)}>`;
    case 'set': return `Set<${prettyTy(t.t)}>`;
    case 'tup': return `[${t.ts.map(prettyTy).join(', ')}]`;
    case 'record': return `{ ${t.fs.map(f => `${f.name}: ${prettyTy(f.ty)}`).join('; ')} }`;
    case 'obj': return t.c;
    case 'named': return t.n;
    case 'opt': return `${prettyTy(t.t)} | undefined`;
    case 'union': return t.ts.map(prettyTy).join(' | ');
    case 'enum': return t.cases.map(c => JSON.stringify(c)).join(' | ');
    case 'fn': return `(${t.args.map(prettyTy).join(', ')}) => ${prettyTy(t.ret)}`;
    case 'promise': return `Promise<${prettyTy(t.t)}>`;
    case 'box': return `Box<${prettyTy(t.t)}>`;
    case 'ext': return t.name;
    case 'dict': return `Record<string, ${prettyTy(t.t)}>`;
    case 'dyn': return 'unknown';
  }
}

/** The type with every `box (fn …)` / `box (record …)` (a function or object with identity, see
 * identity.ts) replaced by the function or record type: the key for the identity analysis. */
export function stripIdBoxes(t: Ty): Ty {
  switch (t.k) {
    case 'box': return t.t.k === 'fn' || t.t.k === 'record' ? stripIdBoxes(t.t) : T.box(stripIdBoxes(t.t));
    case 'fn': return T.fn(t.args.map(stripIdBoxes), stripIdBoxes(t.ret));
    case 'arr': return T.arr(stripIdBoxes(t.t));
    case 'set': return T.set(stripIdBoxes(t.t));
    case 'opt': return T.opt(stripIdBoxes(t.t));
    case 'promise': return T.promise(stripIdBoxes(t.t));
    case 'dict': return T.dict(stripIdBoxes(t.t));
    case 'map': return T.map(stripIdBoxes(t.key), stripIdBoxes(t.val));
    case 'tup': return T.tup(t.ts.map(stripIdBoxes));
    case 'union': return T.union(t.ts.map(stripIdBoxes));
    case 'record': return T.record(t.fs.map(f => ({ name: f.name, ty: stripIdBoxes(f.ty) })));
    default: return t;
  }
}

/** `Ty.eqable` of the Lean development. */
export function eqable(t: Ty): boolean {
  switch (t.k) {
    case 'num': case 'bigint': case 'bool': case 'str': case 'undef': case 'null': return true;
    case 'arr': case 'tarr': case 'map': case 'set': case 'obj': case 'promise': case 'box': case 'ext': case 'dict': return true;
    case 'enum': return true;
    case 'opt': return eqable(t.t);
    case 'union': return t.ts.every(eqable);
    default: return false;
  }
}

/** Canonical order of union members. */
export function sortTys(ts: Ty[]): Ty[] {
  const seen = new Map<string, Ty>();
  for (const t of ts) seen.set(tyKey(t), t);
  return [...seen.keys()].sort().map(k => seen.get(k)!);
}

export function sortFields(fs: Field[]): Field[] {
  return [...fs].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}

/** Types that are object-like for truthiness (pure null tests). */
export function isObjectLike(t: Ty): boolean {
  switch (t.k) {
    case 'arr': case 'tarr': case 'map': case 'set': case 'obj': case 'record': case 'tup':
    case 'fn': case 'promise': case 'err': case 'named': case 'ext': case 'dict': case 'box':
      return true;
    case 'union': return t.ts.every(isObjectLike);
    default: return false;
  }
}

export const TA_ELEM_BIG = new Set<TAKind>(['bi64', 'bu64']);
export function taElem(k: TAKind): Ty {
  return TA_ELEM_BIG.has(k) ? T.bigint : T.num;
}

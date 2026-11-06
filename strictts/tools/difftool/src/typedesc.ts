// Type descriptors: the parameter types of a function (from the TypeScript checker) in a
// small structural language that drives random input generation, shrinking and the Lean
// driver. Recursive types are table entries referenced by id.
import * as ts from 'typescript';
import { Project } from './project';
import { Unit } from './units';

export type Lit = { t: 'n'; v: number | string } | { t: 's'; v: string } | { t: 'b'; v: string } | { t: 'B'; v: boolean } | { t: 'u' } | { t: 'z' };

export type Desc =
  | { k: 'num' } | { k: 'str' } | { k: 'bool' } | { k: 'big' } | { k: 'undef' } | { k: 'null' }
  | { k: 'lit'; v: Lit }
  | { k: 'arr'; t: Desc }
  | { k: 'tup'; ts: Desc[]; req: number; rest?: Desc }
  | { k: 'obj'; name?: string; fields: Field[]; index?: { key: 'str' | 'num'; t: Desc } }
  | { k: 'union'; ts: Desc[] }
  | { k: 'map'; key: Desc; val: Desc }
  | { k: 'set'; t: Desc }
  | { k: 'class'; name: string; ctor: Param[]; fields: Field[] }
  | { k: 'ta'; kind: string }
  | { k: 'date' }
  | { k: 'promise'; t: Desc }
  | { k: 'fn'; params: Desc[]; ret: Desc }
  | { k: 'ref'; id: number }
  /** any value (`unknown`, `any`), or any object (`object`, `{}`) */
  | { k: 'unknown'; objOnly?: boolean }
  | { k: 'unsupported'; why: string };

export interface Field { name: string; t: Desc; opt: boolean }
export interface Param { name: string; t: Desc; opt: boolean; rest: boolean; text: string }

export interface Signature {
  params: Param[];
  ret: Desc;
  retText: string;
  isAsync: boolean;
  /** receiver class (methods) */
  self?: { name: string; ctor: Param[] };
  /** instance type of the class (methods and constructors) */
  selfDesc?: Desc;
  table: Map<number, Desc>;
  notes: string[];
}

const TYPED_ARRAYS = new Set(['Int8Array', 'Uint8Array', 'Uint8ClampedArray', 'Int16Array', 'Uint16Array', 'Int32Array', 'Uint32Array',
  'Float32Array', 'Float64Array', 'BigInt64Array', 'BigUint64Array']);

export class Describer {
  table = new Map<number, Desc>();
  notes: string[] = [];
  private inProgress = new Set<number>();
  constructor(private p: Project) {}

  private libName(t: ts.Type): string | undefined {
    const s = t.getSymbol() ?? t.aliasSymbol;
    const d = s?.declarations?.[0];
    if (!s || !d) return undefined;
    // (an anonymous type literal of the library, as the mapped type of `Record<K, V>` or
    // `Partial<T>`: structural)
    if (s.getName() === '__type') return undefined;
    return this.p.program.isSourceFileDefaultLibrary(d.getSourceFile()) ? s.getName() : undefined;
  }

  private typeId(t: ts.Type): number { return (t as unknown as { id: number }).id; }

  desc(t: ts.Type, where: ts.Node, depth = 0): Desc {
    const c = this.p.checker;
    const F = ts.TypeFlags;
    if (depth > 30) return { k: 'unsupported', why: 'type too deep' };
    if (t.flags & (F.Any | F.Unknown)) { this.notes.push(`${c.typeToString(t)} parameters get arbitrary JSON-like values`); return { k: 'unknown' }; }
    if (t.flags & F.Never) return { k: 'unsupported', why: 'never' };
    if (t.flags & F.NumberLiteral) return { k: 'lit', v: numLit((t as ts.NumberLiteralType).value) };
    if (t.flags & F.StringLiteral) return { k: 'lit', v: { t: 's', v: (t as ts.StringLiteralType).value } };
    if (t.flags & F.BigIntLiteral) { const v = (t as ts.BigIntLiteralType).value; return { k: 'lit', v: { t: 'b', v: (v.negative ? '-' : '') + v.base10Value } }; }
    if (t.flags & F.BooleanLiteral) return { k: 'lit', v: { t: 'B', v: c.typeToString(t) === 'true' } };
    if (t.flags & F.Number) return { k: 'num' };
    if (t.flags & F.String) return { k: 'str' };
    if (t.flags & F.BigInt) return { k: 'big' };
    if (t.flags & F.Boolean) return { k: 'bool' };
    if (t.flags & (F.Undefined | F.Void)) return { k: 'undef' };
    if (t.flags & F.Null) return { k: 'null' };
    if (t.flags & F.ESSymbolLike) return { k: 'unsupported', why: 'symbol' };
    if (t.flags & F.TemplateLiteral) return { k: 'unsupported', why: `template literal type ${c.typeToString(t)}` };
    if (t.flags & F.TypeParameter) {
      const con = c.getBaseConstraintOfType(t);
      if (con && !(con.flags & (F.Unknown | F.Any))) return this.desc(con, where, depth + 1);
      this.notes.push(`type parameter ${c.typeToString(t)} instantiated with number`);
      return { k: 'num' };
    }
    if (t.isUnion()) {
      const ms: Desc[] = [];
      let hasT = false, hasF = false;
      for (const m of t.types) {
        if (m.flags & F.BooleanLiteral) { if (c.typeToString(m) === 'true') hasT = true; else hasF = true; continue; }
        ms.push(this.desc(m, where, depth + 1));
      }
      if (hasT && hasF) ms.push({ k: 'bool' });
      else if (hasT) ms.push({ k: 'lit', v: { t: 'B', v: true } });
      else if (hasF) ms.push({ k: 'lit', v: { t: 'B', v: false } });
      const bad = ms.find(m => m.k === 'unsupported');
      if (bad) return bad;
      return ms.length === 1 ? ms[0] : { k: 'union', ts: ms };
    }
    if (t.flags & F.NonPrimitive) return { k: 'unknown', objOnly: true };
    if (!(t.flags & F.Object) && !t.isIntersection()) return { k: 'unsupported', why: c.typeToString(t) };
    // object types
    if (c.isArrayType(t)) return { k: 'arr', t: this.desc(c.getTypeArguments(t as ts.TypeReference)[0], where, depth + 1) };
    if (c.isTupleType(t)) {
      const ref = t as ts.TupleTypeReference;
      const args = c.getTypeArguments(ref);
      const flags = ref.target.elementFlags;
      const tsd: Desc[] = [];
      let req = 0, rest: Desc | undefined;
      args.forEach((a, i) => {
        const f = flags[i];
        if (f & ts.ElementFlags.Rest || f & ts.ElementFlags.Variadic) rest = this.desc(a, where, depth + 1);
        else { tsd.push(this.desc(a, where, depth + 1)); if (f & ts.ElementFlags.Required) req = tsd.length; }
      });
      return { k: 'tup', ts: tsd, req, rest };
    }
    const lib = this.libName(t);
    if (lib) {
      const targs = (t as ts.TypeReference).target ? c.getTypeArguments(t as ts.TypeReference) : [];
      if ((lib === 'Map' || lib === 'ReadonlyMap') && targs.length === 2) return { k: 'map', key: this.desc(targs[0], where, depth + 1), val: this.desc(targs[1], where, depth + 1) };
      if ((lib === 'Set' || lib === 'ReadonlySet') && targs.length === 1) return { k: 'set', t: this.desc(targs[0], where, depth + 1) };
      if ((lib === 'Promise' || lib === 'PromiseLike') && targs.length === 1) return { k: 'promise', t: this.desc(targs[0], where, depth + 1) };
      if (lib === 'Date') return { k: 'date' };
      if (TYPED_ARRAYS.has(lib)) return { k: 'ta', kind: lib };
      if (lib === 'Record' || lib === 'Partial' || lib === 'Readonly' || lib === 'Required' || lib === 'Pick' || lib === 'Omit') { /* structural, below */ }
      else if (lib !== 'Object') return { k: 'unsupported', why: lib };
    }
    // functions
    const calls = t.getCallSignatures();
    if (calls.length && c.getPropertiesOfType(t).length === 0) {
      const sig = calls[0];
      return {
        k: 'fn',
        params: sig.getParameters().map(ps => this.desc(c.getTypeOfSymbolAtLocation(ps, where), where, depth + 1)),
        ret: this.desc(c.getReturnTypeOfSignature(sig), where, depth + 1),
      };
    }
    const id = this.typeId(t);
    if (this.table.has(id) || this.inProgress.has(id)) return { k: 'ref', id };
    // classes declared in the project
    const sym = t.getSymbol();
    if (sym && (sym.flags & ts.SymbolFlags.Class)) {
      const decl = sym.declarations?.find(ts.isClassDeclaration);
      if (!decl || !decl.name) return { k: 'unsupported', why: `class ${sym.getName()}` };
      this.inProgress.add(id);
      const ctorType = c.getTypeOfSymbolAtLocation(sym, decl);
      const cs = c.getSignaturesOfType(ctorType, ts.SignatureKind.Construct);
      const ctor = cs.length ? this.params(cs[0], decl, depth + 1) : [];
      // public data fields (for printing instances in the Lean driver)
      const fields: Field[] = [];
      for (const prop of c.getPropertiesOfType(t)) {
        const pd = prop.valueDeclaration;
        if (!pd || !(ts.isPropertyDeclaration(pd) || ts.isParameter(pd)) || ts.isPrivateIdentifier(pd.name)) continue;
        const mods = ts.getCombinedModifierFlags(pd);
        if (mods & (ts.ModifierFlags.Private | ts.ModifierFlags.Protected | ts.ModifierFlags.Static)) continue;
        const ft = c.getTypeOfSymbolAtLocation(prop, decl);
        if (ft.getCallSignatures().length) continue;
        fields.push({ name: prop.getName(), t: this.desc(ft, decl, depth + 1), opt: !!(prop.flags & ts.SymbolFlags.Optional) });
      }
      const d: Desc = { k: 'class', name: decl.name.text, ctor, fields };
      this.inProgress.delete(id);
      this.table.set(id, d);
      return { k: 'ref', id };
    }
    this.inProgress.add(id);
    const fields: Field[] = [];
    for (const prop of c.getPropertiesOfType(t)) {
      const pt = c.getTypeOfSymbolAtLocation(prop, where);
      const opt = !!(prop.flags & ts.SymbolFlags.Optional);
      let fd = this.desc(pt, where, depth + 1);
      // `f?: T` is present-or-absent; `undefined` as a present value only when written explicitly
      if (opt && !hasExplicitUndefined(prop)) fd = stripUndef(fd);
      fields.push({ name: prop.getName(), t: fd, opt });
    }
    let index: { key: 'str' | 'num'; t: Desc } | undefined;
    const si = c.getIndexInfosOfType(t);
    for (const info of si) {
      if (info.keyType.flags & F.String) index = { key: 'str', t: this.desc(info.type, where, depth + 1) };
      else if (info.keyType.flags & F.Number && !index) index = { key: 'num', t: this.desc(info.type, where, depth + 1) };
    }
    this.inProgress.delete(id);
    const bad = fields.find(f => f.t.k === 'unsupported' && !f.opt);
    const d: Desc = bad ? { k: 'unsupported', why: `field ${bad.name}: ${(bad.t as { why: string }).why}` } :
      { k: 'obj', name: sym && !(sym.flags & ts.SymbolFlags.TypeLiteral) ? sym.getName() : (t.aliasSymbol?.getName()), fields: fields.filter(f => f.t.k !== 'unsupported'), index };
    this.table.set(id, d);
    return { k: 'ref', id };
  }

  params(sig: ts.Signature, where: ts.Node, depth = 0): Param[] {
    const c = this.p.checker;
    return sig.getParameters().map(ps => {
      const decl = ps.valueDeclaration as ts.ParameterDeclaration | undefined;
      const rest = !!decl?.dotDotDotToken;
      const opt = !!(decl && (decl.questionToken || decl.initializer));
      const pt = c.getTypeOfSymbolAtLocation(ps, where);
      const text = decl?.type ? decl.type.getText() : c.typeToString(pt, where, ts.TypeFormatFlags.NoTruncation);
      let d = this.desc(pt, where, depth);
      if (opt) d = stripUndef(d);
      return { name: ps.getName(), t: d, opt, rest, text };
    });
  }
}

/** Remove `undefined` from a union descriptor (optional parameters and fields: absence is generated separately). */
export function stripUndef(d: Desc): Desc {
  if (d.k !== 'union') return d;
  const ms = d.ts.filter(m => m.k !== 'undef');
  if (ms.length === d.ts.length || ms.length === 0) return d;
  return ms.length === 1 ? ms[0] : { k: 'union', ts: ms };
}

function hasExplicitUndefined(prop: ts.Symbol): boolean {
  const d = prop.valueDeclaration;
  if (!d || !(ts.isPropertySignature(d) || ts.isPropertyDeclaration(d)) || !d.type) return false;
  return ts.isUnionTypeNode(d.type) && d.type.types.some(x => x.kind === ts.SyntaxKind.UndefinedKeyword);
}

function numLit(v: number): Lit {
  if (Number.isNaN(v)) return { t: 'n', v: 'NaN' };
  if (v === Infinity) return { t: 'n', v: 'Inf' };
  if (v === -Infinity) return { t: 'n', v: '-Inf' };
  if (Object.is(v, -0)) return { t: 'n', v: '-0' };
  return { t: 'n', v };
}

export function signatureOf(p: Project, u: Unit): Signature {
  const c = p.checker;
  const D = new Describer(p);
  const sig = c.getSignatureFromDeclaration(u.fn);
  if (!sig) throw new Error(`no signature for ${u.name}`);
  const params = D.params(sig, u.fn);
  const rt = c.getReturnTypeOfSignature(sig);
  const res: Signature = {
    params, ret: u.kind === 'ctor' ? { k: 'undef' } : D.desc(rt, u.fn), retText: c.typeToString(rt, u.fn, ts.TypeFormatFlags.NoTruncation),
    isAsync: u.isAsync, table: D.table, notes: D.notes,
  };
  if ((u.kind === 'method' || u.kind === 'ctor') && u.cls) {
    const cls = u.stmt as ts.ClassDeclaration;
    const ctorType = c.getTypeOfSymbolAtLocation(c.getSymbolAtLocation(cls.name!)!, cls);
    const cs = c.getSignaturesOfType(ctorType, ts.SignatureKind.Construct);
    res.selfDesc = D.desc(c.getTypeAtLocation(cls.name!), cls);
    if (u.kind === 'method') res.self = { name: u.cls, ctor: cs.length ? D.params(cs[0], cls) : [] };
  }
  return res;
}

/** First unsupported component of a descriptor (following table references). */
export function unsupportedIn(d: Desc, table: Map<number, Desc>, seen = new Set<number>()): string | null {
  switch (d.k) {
    case 'unsupported': return d.why;
    case 'arr': case 'set': case 'promise': return unsupportedIn(d.t, table, seen);
    case 'tup': for (const x of [...d.ts, ...(d.rest ? [d.rest] : [])]) { const r = unsupportedIn(x, table, seen); if (r) return r; } return null;
    case 'union': { const ok = d.ts.filter(x => !unsupportedIn(x, table, seen)); return ok.length ? null : unsupportedIn(d.ts[0], table, seen); }
    case 'map': return unsupportedIn(d.key, table, seen) ?? unsupportedIn(d.val, table, seen);
    case 'obj': for (const f of d.fields) if (!f.opt) { const r = unsupportedIn(f.t, table, seen); if (r) return `${f.name}: ${r}`; } return d.index ? unsupportedIn(d.index.t, table, seen) : null;
    case 'class': for (const p of d.ctor) if (!p.opt) { const r = unsupportedIn(p.t, table, seen); if (r) return `new ${d.name}(${p.name}): ${r}`; } return null;
    case 'fn': return 'function-typed value';
    case 'ref': { if (seen.has(d.id)) return null; seen.add(d.id); const t = table.get(d.id); return t ? unsupportedIn(t, table, seen) : 'unresolved type'; }
    default: return null;
  }
}

export function showDesc(d: Desc, table: Map<number, Desc>, depth = 0): string {
  if (depth > 4) return '…';
  switch (d.k) {
    case 'lit': return JSON.stringify(d.v);
    case 'arr': return showDesc(d.t, table, depth + 1) + '[]';
    case 'tup': return '[' + d.ts.map(x => showDesc(x, table, depth + 1)).join(', ') + (d.rest ? ', ...' + showDesc(d.rest, table, depth + 1) + '[]' : '') + ']';
    case 'obj': return (d.name ?? '') + '{' + d.fields.map(f => f.name + (f.opt ? '?' : '') + ': ' + showDesc(f.t, table, depth + 1)).join('; ') + '}';
    case 'union': return d.ts.map(x => showDesc(x, table, depth + 1)).join(' | ');
    case 'map': return `Map<${showDesc(d.key, table, depth + 1)}, ${showDesc(d.val, table, depth + 1)}>`;
    case 'set': return `Set<${showDesc(d.t, table, depth + 1)}>`;
    case 'class': return d.name;
    case 'promise': return `Promise<${showDesc(d.t, table, depth + 1)}>`;
    case 'ref': { const t = table.get(d.id); return t ? (t.k === 'obj' && t.name ? t.name : t.k === 'class' ? t.name : showDesc(t, table, depth + 1)) : '?'; }
    case 'unsupported': return `<unsupported ${d.why}>`;
    default: return d.k;
  }
}

function resolveRef(d: Desc, table: Map<number, Desc>): Desc {
  let x = d;
  for (let i = 0; x.k === 'ref' && i < 50; i++) x = table.get(x.id) ?? { k: 'unsupported', why: 'unresolved type' };
  return x;
}

/** Structural key of a descriptor (named types expanded, cycles cut). */
export function descKey(d: Desc, table: Map<number, Desc>, seen: number[] = []): string {
  if (d.k === 'ref') {
    if (seen.includes(d.id)) return `#${seen.length - seen.indexOf(d.id)}`;
    const t = table.get(d.id);
    return t ? descKey(t, table, [...seen, d.id]) : '?';
  }
  switch (d.k) {
    case 'lit': return JSON.stringify(d.v);
    case 'arr': return `${descKey(d.t, table, seen)}[]`;
    case 'set': return `Set<${descKey(d.t, table, seen)}>`;
    case 'promise': return `Promise<${descKey(d.t, table, seen)}>`;
    case 'map': return `Map<${descKey(d.key, table, seen)},${descKey(d.val, table, seen)}>`;
    case 'tup': return `[${d.ts.map(x => descKey(x, table, seen)).join(',')};${d.req}${d.rest ? ';...' + descKey(d.rest, table, seen) : ''}]`;
    case 'union': return d.ts.map(x => descKey(x, table, seen)).sort().join('|');
    case 'obj': return `{${d.fields.map(f => `${f.name}${f.opt ? '?' : ''}:${descKey(f.t, table, seen)}`).sort().join(';')}${d.index ? `;[${d.index.key}]:${descKey(d.index.t, table, seen)}` : ''}}`;
    case 'class': return `class ${d.name}(${d.ctor.map(p => descKey(p.t, table, seen)).join(',')})`;
    case 'fn': return `(${d.params.map(x => descKey(x, table, seen)).join(',')})=>${descKey(d.ret, table, seen)}`;
    case 'unsupported': return `<${d.why}>`;
    default: return d.k;
  }
}

/** Is every value generated from `oldD` (in `ot`) also a value of `newD` (in `nt`)? Conservative. */
export function subsumes(newD: Desc, nt: Map<number, Desc>, oldD: Desc, ot: Map<number, Desc>, seen = new Set<string>()): boolean {
  if (newD.k === 'ref' || oldD.k === 'ref') {
    const key = `${newD.k === 'ref' ? newD.id : 'x'}:${oldD.k === 'ref' ? oldD.id : 'x'}`;
    if (seen.has(key)) return true;
    seen.add(key);
    return subsumes(resolveRef(newD, nt), nt, resolveRef(oldD, ot), ot, seen);
  }
  if (descKey(newD, nt) === descKey(oldD, ot)) return true;
  if (newD.k === 'unknown' && !newD.objOnly) return true;
  if (oldD.k === 'union') return oldD.ts.every(m => subsumes(newD, nt, m, ot, seen));
  if (newD.k === 'union') return newD.ts.some(m => subsumes(m, nt, oldD, ot, seen));
  if (oldD.k === 'lit') {
    const v = oldD.v;
    if (newD.k === 'lit') return JSON.stringify(newD.v) === JSON.stringify(v);
    return (newD.k === 'num' && v.t === 'n') || (newD.k === 'str' && v.t === 's') || (newD.k === 'big' && v.t === 'b') ||
      (newD.k === 'bool' && v.t === 'B') || (newD.k === 'undef' && v.t === 'u') || (newD.k === 'null' && v.t === 'z');
  }
  if (oldD.k === 'bool' && newD.k === 'bool') return true;
  if (newD.k !== oldD.k) return false;
  switch (oldD.k) {
    case 'arr': case 'set': case 'promise': return subsumes((newD as { t: Desc }).t, nt, oldD.t, ot, seen);
    case 'map': { const n = newD as typeof oldD; return subsumes(n.key, nt, oldD.key, ot, seen) && subsumes(n.val, nt, oldD.val, ot, seen); }
    case 'tup': {
      const n = newD as typeof oldD;
      if (n.ts.length < oldD.ts.length || n.req > oldD.req) return false;
      return oldD.ts.every((x, i) => subsumes(n.ts[i], nt, x, ot, seen)) && (!oldD.rest || (!!n.rest && subsumes(n.rest, nt, oldD.rest, ot, seen)));
    }
    case 'obj': {
      const n = newD as typeof oldD;
      for (const f of oldD.fields) {
        const g = n.fields.find(x => x.name === f.name);
        if (!g) { if (!n.index) return false; continue; }
        if (f.opt && !g.opt) return false;
        if (!subsumes(g.t, nt, f.t, ot, seen)) return false;
      }
      for (const g of n.fields) if (!g.opt && !oldD.fields.some(f => f.name === g.name)) return false;
      if (oldD.index && (!n.index || !subsumes(n.index.t, nt, oldD.index.t, ot, seen))) return false;
      return true;
    }
    case 'class': return (newD as typeof oldD).name === oldD.name && descKey(newD, nt) === descKey(oldD, ot);
    default: return true;
  }
}

/** Can inputs generated for the old parameters be passed to the new ones (same values, type-correct)? */
export function compatibleParams(op: Param[], ot: Map<number, Desc>, np: Param[], nt: Map<number, Desc>): { ok: boolean; reason?: string; widened: boolean } {
  let widened = false;
  for (let i = 0; i < Math.max(op.length, np.length); i++) {
    const o = op[i], n = np[i];
    if (!o) { if (n.opt || n.rest) { widened = true; continue; } return { ok: false, reason: `new required parameter ${n.name}`, widened }; }
    if (!n) return { ok: false, reason: `parameter ${o.name} removed`, widened };
    if (o.rest !== n.rest) return { ok: false, reason: `rest parameter changed at ${o.name}`, widened };
    if (o.opt && !n.opt) return { ok: false, reason: `parameter ${n.name} is no longer optional`, widened };
    if (!o.opt && n.opt) widened = true;
    const same = descKey(o.t, ot) === descKey(n.t, nt);
    if (!same) {
      if (!subsumes(n.t, nt, o.t, ot)) return { ok: false, reason: `type of ${n.name} changed: ${o.text} -> ${n.text}`, widened };
      widened = true;
    }
  }
  return { ok: true, widened };
}

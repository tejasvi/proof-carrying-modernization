// TypeScript checker types -> StrictTS types.
import * as ts from 'typescript';
import { Ty, T, Field, sortTys, sortFields, tyKey, TAKind, eqable, prettyTy, stripIdBoxes, REGEXP_TY, TIMER_TY } from './ty';
import { reject } from './diag';
import { Analysis } from './analysis';

/** Substitution of type parameters (monomorphisation). */
export type Subst = Map<ts.Type, Ty>;

export function substKey(s: Subst): string {
  return [...s.entries()].map(([k, v]) => `${(k as { id?: number }).id}=${tyKey(v)}`).join(',');
}

const TYPED_ARRAYS: Record<string, TAKind> = {
  Int8Array: 'i8', Uint8Array: 'u8', Uint8ClampedArray: 'u8c', Int16Array: 'i16', Uint16Array: 'u16',
  Int32Array: 'i32', Uint32Array: 'u32', Float32Array: 'f32', Float64Array: 'f64',
  BigInt64Array: 'bi64', BigUint64Array: 'bu64',
};

const ERROR_TYPES = new Set(['Error', 'TypeError', 'RangeError', 'SyntaxError', 'ReferenceError', 'EvalError', 'URIError']);

/** A class instantiation (a class declaration under a substitution of its type parameters). */
export interface ClassInst {
  name: string;
  decl: ts.ClassLikeDeclaration;
  subst: Subst;
  instType: ts.Type;
  fields: Field[];
  fieldIdx: Map<string, number>;
}

/** A heap object type that comes from an object type (interface / type literal) whose
 * fields are assigned somewhere. Object literals of this type call a generated constructor. */
export interface MutStruct {
  name: string;
  fields: Field[];        // sorted by name
  fieldIdx: Map<string, number>;
  rep: ts.Type;
}

/** The type of values that cannot exist (dropped from unions). */
export const NEVER: Ty = { k: 'undef' };

export function typeId(t: ts.Type): number { return (t as { id?: number }).id ?? -1; }

export function isLibDecl(program: ts.Program, d: ts.Declaration | undefined): boolean {
  if (!d) return false;
  const sf = d.getSourceFile();
  return program.isSourceFileDefaultLibrary(sf) || sf.isDeclarationFile;
}

export class TypeMapper {
  /** the original subset (`--strict`): `unknown` and `any` are rejected, there is no `dyn` */
  strict = false;
  /** function types whose values are compared by identity somewhere in the program (keys of
   * `stripIdBoxes`): their values are `box (fn …)` cells (identity.ts) */
  boxedFns = new Set<string>();
  /** record types whose values are compared by identity (keys of `stripIdBoxes`): their values
   * are `box (record …)` cells (identity.ts) */
  boxedRecs = new Set<string>();
  /** coverage mode: called with the name of an external object type that has no IR type */
  onExternalType: (name: string) => void = () => {};
  aliases = new Map<string, Ty>();
  /** emitted `TT.fields` (classes and mutable structures), in creation order */
  classFields = new Map<string, Field[]>();
  classes = new Map<string, ClassInst>();
  mutStructs: MutStruct[] = [];
  private memo = new Map<string, Ty>();
  private recursive = new Set<number>();
  private recursionScanned = new Set<number>();
  private namedNames = new Map<string, string>(); // type key (id+subst) -> alias name
  private usedNames = new Set<string>();
  private aliasInProgress = new Set<string>();
  /** TypeScript names of record types (for readable names of generic instances) */
  recordNames = new Map<string, string>();

  /** A short identifier-friendly name of a type (generic instance names). */
  shortName(t: Ty): string {
    switch (t.k) {
      case 'num': return 'number';
      case 'str': return 'string';
      case 'bigint': case 'bool': case 'undef': case 'null': case 'err': return t.k;
      case 'arr': return `${this.shortName(t.t)}Arr`;
      case 'set': return `Set_${this.shortName(t.t)}`;
      case 'map': return `Map_${this.shortName(t.key)}_${this.shortName(t.val)}`;
      case 'dict': return `Dict_${this.shortName(t.t)}`;
      case 'opt': return `opt_${this.shortName(t.t)}`;
      case 'promise': return `Promise_${this.shortName(t.t)}`;
      case 'obj': return t.c.replace(/[^A-Za-z0-9_]/g, '_');
      case 'named': return t.n.replace(/[^A-Za-z0-9_]/g, '_');
      case 'record': return this.recordNames.get(tyKey(t)) ?? `rec${t.fs.length}`;
      case 'tup': return `tup${t.ts.length}`;
      case 'union': return `union${t.ts.length}`;
      case 'enum': return `enum${t.cases.length}`;
      case 'fn': return `fn${t.args.length}`;
      default: return t.k;
    }
  }

  constructor(private checker: ts.TypeChecker, private program: ts.Program, private analysis: Analysis) {}

  // -------------------------------------------------------------------------------------
  // Recursion detection over the structural type graph (immutable object types and unions
  // on a cycle become `named`).

  private edges(t: ts.Type): ts.Type[] {
    const out: ts.Type[] = [];
    if (t.isUnion() || t.isIntersection()) return [...t.types];
    if (!(t.flags & ts.TypeFlags.Object)) return out;
    // package and host types are not traversed (they have no IR type; e.g. React, DOM)
    const sym = t.getSymbol() ?? t.aliasSymbol;
    if (sym && sym.name && !sym.name.startsWith('__') && this.isExternalDecl(sym.declarations?.[0]) && !this.knownLib(sym.name)) return out;
    if (this.isClassInstance(t) || this.isMutableStructure(t)) return out;
    const obj = t as ts.ObjectType;
    if (obj.objectFlags & ts.ObjectFlags.Reference) {
      const args = this.checker.getTypeArguments(t as ts.TypeReference);
      const sym = t.getSymbol();
      if (this.checker.isArrayType(t) || this.checker.isTupleType(t) ||
          (sym && ['Map', 'ReadonlyMap', 'Set', 'ReadonlySet', 'Promise'].includes(sym.name) && isLibDecl(this.program, sym.declarations?.[0]))) {
        return [...args];
      }
    }
    for (const sig of t.getCallSignatures()) {
      for (const p of sig.getParameters()) out.push(this.checker.getTypeOfSymbol(p));
      out.push(sig.getReturnType());
    }
    for (const p of this.checker.getPropertiesOfType(t)) out.push(this.checker.getTypeOfSymbol(p));
    return out;
  }

  private scanRecursion(root: ts.Type): void {
    if (this.recursionScanned.has(typeId(root))) return;
    const stack: ts.Type[] = [];
    const onStack = new Set<number>();
    const visit = (t: ts.Type, depth: number) => {
      const id = typeId(t);
      if (onStack.has(id)) {
        for (let i = stack.length - 1; i >= 0; i--) {
          this.recursive.add(typeId(stack[i]));
          if (typeId(stack[i]) === id) break;
        }
        return;
      }
      if (this.recursionScanned.has(id) || depth > 200) return;
      stack.push(t); onStack.add(id);
      for (const e of this.edges(t)) visit(e, depth + 1);
      stack.pop(); onStack.delete(id);
      this.recursionScanned.add(id);
    };
    visit(root, 0);
  }

  private isRecursive(t: ts.Type): boolean {
    this.scanRecursion(t);
    return this.recursive.has(typeId(t));
  }

  // -------------------------------------------------------------------------------------

  /** Declared in a package or in the host library (not the program's own code)? */
  isExternalDecl(d: ts.Declaration | undefined): boolean {
    if (!d) return false;
    const sf = d.getSourceFile();
    return sf.fileName.includes('/node_modules/') || this.program.isSourceFileDefaultLibrary(sf);
  }

  /** The name of an external type: `<package>:<TypeName>`, or the qualified name for host
   * types (`Date`, `NodeJS.Timeout`, `React.JSX.Element`). Type arguments are erased. */
  externalTypeName(sym: ts.Symbol): string {
    const d = sym.declarations?.[0];
    const pkg = d?.getSourceFile().fileName.match(/node_modules\/((?:@[^/]+\/)?[^/]+)\//)?.[1];
    if (pkg && !pkg.startsWith('@types/') && pkg !== 'typescript') return `${pkg}:${sym.name}`;
    return this.externalSymName(sym);
  }

  /** `package:Qualified.Name` (or `Qualified.Name` for the host library and @types). */
  externalSymName(sym: ts.Symbol): string {
    const d = sym.declarations?.[0];
    // `"/abs/path/module".name` -> name;  `"node:fs/promises".mkdir` -> node:fs/promises.mkdir
    let q = this.checker.getFullyQualifiedName(sym);
    const whole = q.match(/^"([^"]*)"$/);
    if (whole) {
      // a module itself: `firebase-functions/lib/logger/index` -> firebase-functions/logger
      const m = whole[1].match(/node_modules\/(.*)$/);
      const p = m ? m[1].replace(/\/(lib|dist|build|cjs|esm)\//g, '/').replace(/\/index$/, '').replace(/\.d\.ts$/, '') : whole[1];
      return p.replace(/^@types\//, '');
    }
    q = q.replace(/"(\/[^"]*)"\./g, '').replace(/"([^"]*)"\./g, '$1.').replace(/^global\./, '');
    const pkg = d?.getSourceFile().fileName.match(/node_modules\/((?:@[^/]+\/)?[^/]+)\//)?.[1];
    if (!pkg || pkg === 'typescript') q = q.replace(/^(\w+)Constructor\./, '$1.');
    return pkg && !pkg.startsWith('@types/') && pkg !== 'typescript' ? `${pkg}:${q}` : q;
  }

  /** Library object types the IR models (others are host types such as Response). */
  knownLib(name: string): boolean {
    // (the results of Promise.allSettled are plain records: Ty.settled)
    return ['Array', 'ReadonlyArray', 'Map', 'ReadonlyMap', 'Set', 'ReadonlySet', 'Promise', 'PromiseLike', 'Error', 'TypeError',
      'RangeError', 'SyntaxError', 'ReferenceError', 'EvalError', 'URIError', 'String', 'Number', 'Boolean', 'BigInt',
      'PromiseFulfilledResult', 'PromiseRejectedResult'].includes(name) || Object.hasOwn(TYPED_ARRAYS, name);
  }

  isClassInstance(t: ts.Type): boolean {
    const sym = t.getSymbol();
    return !!sym && !!(sym.flags & ts.SymbolFlags.Class) && !isLibDecl(this.program, sym.declarations?.[0]);
  }

  /** Is `t` an object type whose fields are assigned somewhere (directly, or through a
   * structurally identical type)? */
  /** A dictionary type with named properties (`{ v: number; [k: string]: unknown }`): its
   * values are not copied into records (later writes through the dictionary would not show). */
  isNamedDict(t: ts.Type): boolean {
    const parts = t.isUnion() ? t.types : [t];
    return parts.some(p => !!(p.flags & ts.TypeFlags.Object) && this.checker.getIndexInfosOfType(p).length > 0 &&
      this.checker.getPropertiesOfType(p).length > 0);
  }

  isMutableStructure(t: ts.Type): boolean {
    if (!(t.flags & ts.TypeFlags.Object) || this.isClassInstance(t)) return false;
    if (this.analysis.isMutatedId(t)) return true;
    for (const m of this.analysis.mutatedTypes) if (this.sameStructure(m, t)) return true;
    return false;
  }

  private sameStructure(a: ts.Type, b: ts.Type): boolean {
    const pa = this.checker.getPropertiesOfType(a).map(p => p.name).sort();
    const pb = this.checker.getPropertiesOfType(b).map(p => p.name).sort();
    if (pa.join('\0') !== pb.join('\0')) return false;
    return this.checker.isTypeAssignableTo(a, b) && this.checker.isTypeAssignableTo(b, a);
  }

  private freshName(base: string): string {
    let n = base, i = 2;
    while (this.usedNames.has(n)) n = `${base}${i++}`;
    this.usedNames.add(n);
    return n;
  }

  typeArgsSuffix(args: readonly ts.Type[], subst: Subst, site: ts.Node): string {
    if (!args.length) return '';
    return `<${args.map(a => prettyTy(this.map(a, subst, site))).join(', ')}>`;
  }

  /** Display name of a named object/union type. */
  private nameOf(t: ts.Type, subst: Subst, site: ts.Node): string {
    const key = `${typeId(t)}|${substKey(subst)}`;
    const known = this.namedNames.get(key);
    if (known) return known;
    let base = 'Anon';
    let args: readonly ts.Type[] = [];
    if (t.aliasSymbol) { base = t.aliasSymbol.name; args = t.aliasTypeArguments ?? []; }
    else {
      const sym = t.getSymbol();
      if (sym && sym.name && !sym.name.startsWith('__')) base = sym.name;
      if ((t as ts.ObjectType).objectFlags & ts.ObjectFlags.Reference) args = this.checker.getTypeArguments(t as ts.TypeReference);
    }
    const n = this.freshName(base + this.typeArgsSuffix(args, subst, site));
    this.namedNames.set(key, n);
    return n;
  }

  private depth = 0;

  map(t: ts.Type, subst: Subst, site: ts.Node): Ty {
    const key = `${typeId(t)}|${substKey(subst)}`;
    const m = this.memo.get(key);
    if (m) return m;
    if (this.depth > 60) reject(site, 'unsupported-type', `type ${this.checker.typeToString(t).slice(0, 80)} is too deeply nested (an unnamed recursive type?)`);
    this.depth++;
    try {
      const r = this.map1(t, subst, site);
      this.memo.set(key, r);
      return r;
    } finally { this.depth--; }
  }

  private map1(t: ts.Type, subst: Subst, site: ts.Node): Ty {
    const F = ts.TypeFlags;
    // `unknown` / `any`: a value with its runtime type (StrictTS/Lib/Dyn.lean), except in the
    // original subset (`--strict`; STRICTTS_ANY_REJECT=1 rejects only `any`, for measurements)
    if (t.flags & (F.Any | F.Unknown) && this.strict) reject(site, 'any-type', `a value of type ${t.flags & F.Any ? 'any' : 'unknown'} (any/unknown are not allowed)`);
    if (t.flags & F.Unknown) return T.dyn;
    if (t.flags & F.Any) {
      if (process.env.STRICTTS_ANY_REJECT) reject(site, 'any-type', 'a value of type any (any is not allowed)');
      return T.dyn;
    }
    if (t.flags & F.TypeParameter) {
      const s = subst.get(t);
      if (!s) reject(site, 'unsupported-generic', `type parameter ${this.checker.typeToString(t)} is not instantiated here`);
      return s;
    }
    if (t.flags & (F.EnumLiteral | F.Enum)) reject(site, 'no-enum-decl', 'TypeScript `enum` declarations are not supported');
    if (t.flags & (F.Number | F.NumberLiteral)) return T.num;
    if (t.flags & (F.BigInt | F.BigIntLiteral)) return T.bigint;
    if (t.flags & (F.Boolean | F.BooleanLiteral)) return T.bool;
    if (t.flags & (F.String | F.StringLiteral | F.TemplateLiteral | F.StringMapping)) return T.str;
    if (t.flags & (F.Undefined | F.Void)) return T.undef;
    if (t.flags & F.Null) return T.null;
    if (t.flags & F.Never) return T.undef;
    if (t.flags & (F.ESSymbol | F.UniqueESSymbol)) reject(site, 'no-symbol', '`symbol` is not supported');
    // `object`: any non-primitive value, kept with its runtime type (not in the strict subset)
    if (t.flags & F.NonPrimitive) {
      if (this.strict) reject(site, 'no-object-type', 'the `object` type is not allowed');
      return T.dyn;
    }
    if ((t.flags & F.Conditional) && t.aliasSymbol?.name === 'Awaited' && t.aliasTypeArguments?.length === 1) {
      // Awaited<T> of a type parameter: the substitution decides
      const inner = this.map(t.aliasTypeArguments[0], subst, site);
      return inner.k === 'promise' ? inner.t : inner;
    }
    if (t.isUnion()) return this.mapUnion(t, subst, site);
    if (t.isIntersection()) {
      if (t.types.every(x => x.flags & F.Object)) return this.mapObjectType(t, subst, site);
      return this.mapIntersection(t, subst, site);
    }
    if (t.flags & F.Object) return this.mapObject(t as ts.ObjectType, subst, site);
    reject(site, 'unsupported-type', `type ${this.checker.typeToString(t)} is not supported`);
  }

  /** `T & {}` (T without undefined/null) and `T & null` (null or nothing), as produced by
   * TypeScript's narrowing of type parameters. */
  private mapIntersection(t: ts.IntersectionType, subst: Subst, site: ts.Node): Ty {
    const F = ts.TypeFlags;
    const isEmptyObj = (x: ts.Type) => !!(x.flags & F.Object) && this.checker.getPropertiesOfType(x).length === 0 &&
      x.getCallSignatures().length === 0 && this.checker.getIndexInfosOfType(x).length === 0;
    const core = t.types.filter(x => !isEmptyObj(x) && !(x.flags & (F.Null | F.Undefined)));
    if (core.length !== 1) reject(site, 'unsupported-type', `intersection type ${this.checker.typeToString(t)} is not supported`);
    let c = this.map(core[0], subst, site);
    if (t.types.some(isEmptyObj)) {
      if (c.k === 'opt') c = c.t;
      if (c.k === 'union') { const r = c.ts.filter(m => m.k !== 'null'); c = r.length === 1 ? r[0] : T.union(r); }
      if (c.k === 'undef' || c.k === 'null') return NEVER;
    }
    if (t.types.some(x => x.flags & F.Null)) {
      const hasNull = c.k === 'null' || (c.k === 'union' && c.ts.some(m => m.k === 'null')) || (c.k === 'opt' && (c.t.k === 'null' || (c.t.k === 'union' && c.t.ts.some(m => m.k === 'null'))));
      return hasNull ? T.null : NEVER;
    }
    if (t.types.some(x => x.flags & F.Undefined)) return c.k === 'opt' || c.k === 'undef' ? T.undef : NEVER;
    return c;
  }

  private mapUnion(t: ts.UnionType, subst: Subst, site: ts.Node): Ty {
    const F = ts.TypeFlags;
    // a recursive union alias is named before its members are mapped
    let recName: string | undefined;
    if (t.aliasSymbol && this.isRecursive(t)) {
      recName = this.nameOf(t, subst, site);
      const undefPart = t.types.some(m => m.flags & (F.Undefined | F.Void));
      if (this.aliasInProgress.has(recName)) return undefPart ? T.opt(T.named(recName)) : T.named(recName);
      this.aliasInProgress.add(recName);
      this.memo.set(`${typeId(t)}|${substKey(subst)}`, undefPart ? T.opt(T.named(recName)) : T.named(recName));
    }
    try {
      return this.mapUnion1(t, subst, site, recName);
    } finally { if (recName) this.aliasInProgress.delete(recName); }
  }

  private mapUnion1(t: ts.UnionType, subst: Subst, site: ts.Node, recName: string | undefined): Ty {
    const F = ts.TypeFlags;
    let hasUndef = false, hasNull = false;
    const lits: string[] = [];
    const rest: ts.Type[] = [];
    for (const m of t.types) {
      if (m.flags & (F.Undefined | F.Void)) hasUndef = true;
      else if (m.flags & F.Null) hasNull = true;
      else if (m.flags & F.StringLiteral) lits.push((m as ts.StringLiteralType).value);
      else rest.push(m);
    }
    const members: Ty[] = [];
    if (lits.length === 1) members.push(T.str);
    else if (lits.length > 1) members.push(T.enum([...new Set(lits)].sort()));
    for (const m of rest) {
      const mt = this.map(m, subst, site);
      if (mt === NEVER) continue;
      // members that are themselves optional/nullable (from narrowed type parameters)
      if (mt.k === 'opt') { hasUndef = true; members.push(mt.t); continue; }
      if (mt.k === 'undef') { hasUndef = true; continue; }
      if (mt.k === 'null') { hasNull = true; continue; }
      members.push(mt);
    }
    let ms = sortTys(members);
    // `string | "a"`-like collapses
    if (ms.some(x => x.k === 'str')) ms = ms.filter(x => x.k !== 'enum');
    if (hasNull) ms = sortTys([...ms, T.null]);
    let core: Ty;
    if (ms.length === 0) core = T.undef;
    else if (ms.length === 1) core = ms[0];
    else core = T.union(ms);
    if (recName) {
      if (core.k === 'undef') reject(site, 'unsupported-type', 'recursive alias of undefined');
      this.aliases.set(recName, core);
      core = T.named(recName);
    }
    if (hasUndef) return ms.length === 0 ? T.undef : T.opt(core);
    return core;
  }

  private namedFor(t: ts.Type, structure: Ty, subst: Subst, site: ts.Node): Ty {
    const n = this.nameOf(t, subst, site);
    this.aliases.set(n, structure);
    return T.named(n);
  }

  private mapObject(t: ts.ObjectType, subst: Subst, site: ts.Node): Ty {
    const sym = t.getSymbol();
    const lib = sym && isLibDecl(this.program, sym.declarations?.[0]);
    if (t.objectFlags & ts.ObjectFlags.Reference) {
      const ref = t as ts.TypeReference;
      const args = this.checker.getTypeArguments(ref);
      if (this.checker.isArrayType(t)) return T.arr(this.map(args[0], subst, site));
      if (this.checker.isTupleType(t)) {
        const target = ref.target as ts.TupleType;
        if (target.elementFlags.some(f => !(f & ts.ElementFlags.Required))) reject(site, 'unsupported-type', 'tuples with optional or rest elements are not supported');
        return T.tup(args.slice(0, target.fixedLength).map(a => this.map(a, subst, site)));
      }
      if (sym && lib) {
        switch (sym.name) {
          case 'Map': case 'ReadonlyMap': {
            const k = this.map(args[0], subst, site), v = this.map(args[1], subst, site);
            if (!eqable(k)) reject(site, 'map-key', `Map keys of type ${prettyTy(k)} are not comparable with SameValueZero`);
            return T.map(k, v);
          }
          case 'Set': case 'ReadonlySet': {
            const e = this.map(args[0], subst, site);
            if (!eqable(e)) reject(site, 'map-key', `Set elements of type ${prettyTy(e)} are not comparable with SameValueZero`);
            return T.set(e);
          }
          case 'Promise': return T.promise(this.map(args[0], subst, site));
        }
      }
    }
    if (sym && lib) {
      if (ERROR_TYPES.has(sym.name)) return T.err;
      if (Object.hasOwn(TYPED_ARRAYS, sym.name)) return T.tarr(TYPED_ARRAYS[sym.name]);
      if (sym.name === 'RegExpMatchArray' || sym.name === 'RegExpExecArray') return T.ext(sym.name);
      if (sym.name === 'RegExp') return REGEXP_TY;
      if (sym.name === 'Function' || sym.name === 'Object') reject(site, 'no-object-type', `the type ${sym.name} is not allowed`);
      if (sym.name === 'Symbol') reject(site, 'no-symbol', '`symbol` is not supported');
      // `Iterator<T, TReturn, TNext>`: the record of its methods, `next` (called without the
      // TNext argument), `return?` and `throw?` (called without the error), returning the union
      // of the yield and return results; the methods are closures (`this` in an object literal
      // method is rejected, so calls through the fields need no receiver). IteratorObject (the
      // Iterator.prototype helpers), iterable iterators (Symbol.iterator), Map / Set / Array
      // iterators and generators stay unsupported.
      if (sym.name === 'Iterator' || sym.name === 'IteratorYieldResult' || sym.name === 'IteratorReturnResult') {
        const args = (t.flags & ts.TypeFlags.Object) ? this.checker.getTypeArguments(t as ts.TypeReference) : [];
        if (sym.name === 'IteratorYieldResult') return T.record([{ name: 'done', ty: T.opt(T.bool) }, { name: 'value', ty: this.map(args[0], subst, site) }]);
        if (sym.name === 'IteratorReturnResult') return T.record([{ name: 'done', ty: T.bool }, { name: 'value', ty: this.iterReturnValue(args[0], subst, site) }]);
        const res = T.union(sortTys([
          T.record([{ name: 'done', ty: T.opt(T.bool) }, { name: 'value', ty: this.map(args[0], subst, site) }]),
          T.record([{ name: 'done', ty: T.bool }, { name: 'value', ty: this.iterReturnValue(args[1], subst, site) }]),
        ]));
        return T.record([
          { name: 'next', ty: T.fn([], res) },
          { name: 'return', ty: T.opt(T.fn([T.opt(this.iterReturnValue(args[1], subst, site))], res)) },
          { name: 'throw', ty: T.opt(T.fn([T.opt(T.undef)], res)) },
        ]);
      }
      if (['IterableIterator', 'MapIterator', 'SetIterator', 'ArrayIterator', 'Generator', 'AsyncGenerator', 'AsyncIterableIterator'].includes(sym.name)) {
        reject(site, 'unsupported-type', `type ${sym.name} is not supported (iterators)`);
      }
    }
    // Node's timer handle (also when a program declares the type itself): TIMER_TY
    if (sym && (sym.name === 'Timeout' || sym.name === 'Timer') && /^(global\.)?NodeJS\.(Timeout|Timer)$/.test(this.checker.getFullyQualifiedName(sym))) return TIMER_TY;
    // a named object type of a package (firebase, express, react, ...) or of the host
    // (DOM, Node): no IR representation
    // (aliases of the default library — Record, Partial, Pick, ... — are type operators that
    // TypeScript resolves to structural types; only package aliases are external API types)
    const asym = !sym || sym.name.startsWith('__') ? t.aliasSymbol : undefined;
    const asymDecl = asym?.declarations?.[0];
    // (plain function types declared outside — `typeof Date.now`, React.Dispatch — stay
    // function types)
    const plainFn = t.getCallSignatures().length === 1 && this.checker.getPropertiesOfType(t).length === 0;
    // an external object type that is only a string index signature (Firestore's
    // `DocumentData`): a plain object used as a dictionary, like `Record<string, …>`
    const infos0 = this.checker.getIndexInfosOfType(t);
    if (infos0.length === 1 && (infos0[0].keyType.flags & ts.TypeFlags.String) && this.checker.getPropertiesOfType(t).length === 0 &&
        t.getCallSignatures().length === 0 && t.getConstructSignatures().length === 0) {
      return T.dict(this.map(infos0[0].type, subst, site));
    }
    const extSym = plainFn ? undefined
      : asym && asymDecl && this.isExternalDecl(asymDecl) && !this.program.isSourceFileDefaultLibrary(asymDecl.getSourceFile()) && !this.knownLib(asym.name) ? asym
      : sym && sym.name && !sym.name.startsWith('__') && this.isExternalDecl(sym.declarations?.[0]) && !this.knownLib(sym.name) ? sym : undefined;
    if (extSym) {
      const name = this.externalTypeName(extSym);
      // (STRICTTS_NO_EXT_TYPES=1: the earlier behaviour, for coverage comparisons)
      if (process.env.STRICTTS_NO_EXT_TYPES) reject(site, 'external-type', `values of the external type ${name} have no StrictTS representation`, name);
      return T.ext(name);
    }
    if (this.isClassInstance(t)) return T.obj(this.classInst(t, subst, site).name);
    // function types
    const calls = t.getCallSignatures();
    const props = this.checker.getPropertiesOfType(t);
    if (calls.length > 0) {
      if (props.length > 0 || calls.length > 1) reject(site, 'unsupported-type', `type ${this.checker.typeToString(t)} (overloaded or with properties) is not supported`);
      return this.mapSignature(calls[0], subst, site);
    }
    if (t.getConstructSignatures().length) reject(site, 'unsupported-type', 'constructor types are not supported');
    return this.mapObjectType(t, subst, site);
  }

  /** The value of an iterator's return result (TReturn): in the strict subset the default `any`
   * is undefined, which no program can observe there (reads at type any are rejected). */
  iterReturnValue(x: ts.Type | undefined, subst: Subst, site: ts.Node): Ty {
    return !x || (this.strict && (x.flags & ts.TypeFlags.Any)) ? T.undef : this.map(x, subst, site);
  }

  mapSignature(sig: ts.Signature, subst: Subst, site: ts.Node): Ty {
    // a method of `Iterator<…>` read as a value (`it.return`): the type of the record's field
    const d = sig.getDeclaration() as ts.SignatureDeclaration | undefined;
    if (d && d.parent && ts.isInterfaceDeclaration(d.parent) && d.parent.name.text === 'Iterator' && isLibDecl(this.program, d.parent)) {
      const res = this.map(sig.getReturnType(), subst, site);
      const name = d.name && ts.isIdentifier(d.name) ? d.name.text : '';
      if (name === 'next') return T.fn([], res);
      if (name === 'throw') return T.fn([T.opt(T.undef)], res);
      if (name === 'return') {
        const p = sig.getParameters()[0];
        return T.fn([T.opt(this.iterReturnValue(p ? this.checker.getTypeOfSymbol(p).getNonNullableType() : undefined, subst, site))], res);
      }
    }
    if (sig.typeParameters?.length) reject(site, 'unsupported-generic', 'generic function values are not supported (only generic functions that are called directly)');
    const args: Ty[] = [];
    for (const p of sig.getParameters()) {
      const d = p.valueDeclaration as ts.ParameterDeclaration | undefined;
      if (d && d.dotDotDotToken) reject(site, 'fn-type-rest', 'rest parameters in function types are not supported');
      if (d && ts.isIdentifier(d.name) && d.name.text === 'this') continue;
      let pt = this.map(this.checker.getTypeOfSymbol(p), subst, site);
      if (d && (d.questionToken || d.initializer) && pt.k !== 'opt') pt = T.opt(pt);
      args.push(pt);
    }
    const f = T.fn(args, this.map(sig.getReturnType(), subst, site));
    return this.boxedFns.size && this.boxedFns.has(tyKey(stripIdBoxes(f))) ? T.box(f) : f;
  }

  /** Records, mutable structures and named recursive object types. */
  private mapObjectType(t: ts.Type, subst: Subst, site: ts.Node): Ty {
    const infos = this.checker.getIndexInfosOfType(t);
    if (infos.length) {
      // an object used as a dictionary: one string index signature, alone or with named
      // properties whose types fit it (TypeScript checks that for interfaces and object literal
      // types, not for intersections); a named property is read as a dictionary entry at the
      // type TypeScript gives it (a checked cast where that is narrower than the index type)
      if (infos.length === 1 && (infos[0].keyType.flags & ts.TypeFlags.String) &&
          this.checker.getPropertiesOfType(t).every(p => this.checker.isTypeAssignableTo(this.checker.getTypeOfSymbol(p), infos[0].type))) {
        return T.dict(this.map(infos[0].type, subst, site));
      }
      reject(site, 'index-signature', `index signatures (${this.checker.typeToString(t)}) are only supported with string keys and named properties of the index type (dictionaries)`);
    }
    if (this.isMutableStructure(t)) return T.obj(this.mutStruct(t, subst, site).name);
    const props = this.checker.getPropertiesOfType(t);
    if (props.length === 0) {
      // `{}` without call signatures: the record without fields (an object literal `{}`; a value
      // given at this type is seen through no properties); not in the strict subset
      if (this.strict || t.getCallSignatures().length || t.getConstructSignatures().length) reject(site, 'no-object-type', `the empty object type ${this.checker.typeToString(t)} is not allowed`);
      return T.record([]);
    }
    // only types with a name (alias or interface) become `named`: every recursive cycle of
    // TypeScript types passes through a named type, so anonymous members expand finitely
    const sym = t.getSymbol();
    const hasName = !!t.aliasSymbol || (!!sym && !!sym.name && !sym.name.startsWith('__'));
    const rec = hasName && this.isRecursive(t);
    let name: string | undefined;
    if (rec) {
      name = this.nameOf(t, subst, site);
      if (this.aliasInProgress.has(name)) return T.named(name);
      this.aliasInProgress.add(name);
      this.memo.set(`${typeId(t)}|${substKey(subst)}`, T.named(name));
    }
    const fs: Field[] = [];
    for (const p of props) {
      if (p.flags & (ts.SymbolFlags.GetAccessor | ts.SymbolFlags.SetAccessor)) reject(site, 'unsupported-type', `accessor ${p.name} in object type`);
      let ft = this.map(this.checker.getTypeOfSymbol(p), subst, site);
      if ((p.flags & ts.SymbolFlags.Optional) && ft.k !== 'opt') ft = T.opt(ft);
      fs.push({ name: p.name, ty: ft });
    }
    const r = T.record(sortFields(fs));
    const disp = t.aliasSymbol?.name ?? (sym && sym.name && !sym.name.startsWith('__') ? sym.name : undefined);
    if (disp && !this.recordNames.has(tyKey(r))) this.recordNames.set(tyKey(r), disp);
    if (name) {
      this.aliases.set(name, r);
      this.aliasInProgress.delete(name);
      return T.named(name);
    }
    return this.boxedRecs.size && this.boxedRecs.has(tyKey(stripIdBoxes(r))) ? T.box(r) : r;
  }

  mutStruct(t: ts.Type, subst: Subst, site: ts.Node): MutStruct {
    for (const m of this.mutStructs) if (m.rep === t || this.sameStructure(m.rep, t)) return m;
    const name = this.nameOf(t, subst, site);
    const failed = this.typeFail.get(name);
    if (failed) this.rethrow(failed, site);
    const ms: MutStruct = { name, fields: [], fieldIdx: new Map(), rep: t };
    // registered before the fields are mapped (recursive structures); removed on failure
    this.mutStructs.push(ms);
    this.classFields.set(name, ms.fields);
    try {
      const fs: Field[] = [];
      for (const p of this.checker.getPropertiesOfType(t)) {
        let ft = this.map(this.checker.getTypeOfSymbol(p), subst, site);
        if ((p.flags & ts.SymbolFlags.Optional) && ft.k !== 'opt') ft = T.opt(ft);
        fs.push({ name: p.name, ty: ft });
      }
      for (const f of sortFields(fs)) { ms.fieldIdx.set(f.name, ms.fields.length); ms.fields.push(f); }
    } catch (e) {
      this.mutStructs.splice(this.mutStructs.indexOf(ms), 1);
      this.classFields.delete(name);
      this.typeFail.set(name, e);
      throw e;
    }
    return ms;
  }

  /** types (classes, heap structures) whose fields have no IR type, with the reason */
  typeFail = new Map<string, unknown>();

  /** Re-raise a remembered failure at a new site (same rule and message). */
  rethrow(e: unknown, site: ts.Node): never {
    const r = e as { rule?: string; message?: string; extName?: string };
    reject(site, r.rule ?? 'unsupported-type', r.message ?? String(e), r.extName);
  }

  /** The class instantiation of a class instance type. */
  classInst(t: ts.Type, subst: Subst, site: ts.Node): ClassInst {
    const sym = t.getSymbol()!;
    const decl = sym.declarations?.find(d => ts.isClassDeclaration(d) || ts.isClassExpression(d)) as ts.ClassLikeDeclaration | undefined;
    if (!decl) reject(site, 'unsupported-type', `class ${sym.name} without declaration`);
    const tparams = decl.typeParameters?.map(tp => this.checker.getTypeAtLocation(tp)) ?? [];
    const args = (t as ts.ObjectType).objectFlags & ts.ObjectFlags.Reference ? this.checker.getTypeArguments(t as ts.TypeReference) : [];
    const csubst: Subst = new Map();
    tparams.forEach((tp, i) => { if (args[i]) csubst.set(tp, this.map(args[i], subst, site)); });
    const name = (sym.name) + (tparams.length ? `<${tparams.map(tp => prettyTy(csubst.get(tp)!)).join(', ')}>` : '');
    const known = this.classes.get(name);
    if (known) return known;
    const failed = this.typeFail.get(name);
    if (failed) this.rethrow(failed, site);
    if (decl.heritageClauses?.some(h => h.token === ts.SyntaxKind.ExtendsKeyword)) reject(site, 'no-extends', `class ${sym.name} extends another class`);
    const ci: ClassInst = { name, decl, subst: csubst, instType: t, fields: [], fieldIdx: new Map() };
    this.classes.set(name, ci);
    try {
      this.classFieldsOf(ci, decl, csubst);
    } catch (e) {
      this.classes.delete(name);
      this.classFields.delete(name);
      this.typeFail.set(name, e);
      throw e;
    }
    return ci;
  }

  private classFieldsOf(ci: ClassInst, decl: ts.ClassLikeDeclaration, csubst: Subst): void {
    const name = ci.name;
    this.classFields.set(name, ci.fields);
    // fields: parameter properties first, then property declarations (declaration order)
    const ctor = decl.members.find(ts.isConstructorDeclaration);
    const fieldDecls: { name: string; node: ts.Node }[] = [];
    if (ctor) for (const p of ctor.parameters) {
      if (ts.getModifiers(p)?.some(m => [ts.SyntaxKind.PublicKeyword, ts.SyntaxKind.PrivateKeyword, ts.SyntaxKind.ProtectedKeyword, ts.SyntaxKind.ReadonlyKeyword].includes(m.kind))) {
        if (!ts.isIdentifier(p.name)) reject(p, 'unsupported-syntax', 'destructured parameter property');
        fieldDecls.push({ name: p.name.text, node: p });
      }
    }
    for (const m of decl.members) {
      if (ts.isPropertyDeclaration(m) && !ts.getModifiers(m)?.some(x => x.kind === ts.SyntaxKind.StaticKeyword)) {
        if (!ts.isIdentifier(m.name) && !ts.isPrivateIdentifier(m.name)) reject(m, 'unsupported-syntax', 'computed property name');
        fieldDecls.push({ name: m.name.text, node: m });
      }
    }
    for (const fd of fieldDecls) {
      const ptype = this.checker.getTypeAtLocation(fd.node);
      let ft = this.map(ptype, csubst, fd.node);
      if (ts.isPropertyDeclaration(fd.node) && fd.node.questionToken && ft.k !== 'opt') ft = T.opt(ft);
      ci.fieldIdx.set(fd.name, ci.fields.length);
      ci.fields.push({ name: fd.name, ty: ft });
    }
  }
}

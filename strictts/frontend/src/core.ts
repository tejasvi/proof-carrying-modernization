// The translator: registries, function contexts, bindings and type conversions.
// Statement, expression and library lowering live in stmts.ts, exprs.ts and builtins.ts
// (they extend `Translator` through module augmentation; see index.ts).
import * as ts from 'typescript';
import { Ty, T, tyEq, prettyTy, showTy, leanJSStr, leanStrLit, Field, TIMER_TY } from './ty';
import { Expr, Item, Block, VarInfo, FunInfo, GlobalInfo, E, S, mkVar, declItem, stmtItem, isStable, InternalError, isPoison } from './ir';
import { Diags, Reject, reject } from './diag';
import { Analysis, VarFacts, ownerOf, paramSymbol } from './analysis';
import { TypeMapper, Subst, ClassInst, MutStruct, substKey, isLibDecl } from './types';
import { ProgramIR } from './emit';

export type Binding =
  /** a local variable holding the value (`errVar`: a `catch` variable, typed `Error`;
   * `fixed`: the IR type is authoritative, TypeScript's type is not mapped at reads;
   * `holes`: an array from `new Array(n)` filled in order, this variable holding n) */
  | { k: 'var'; v: VarInfo; errVar?: boolean; fixed?: boolean; holes?: VarInfo }
  /** a local slot holding a box (captured and reassigned `let`) */
  | { k: 'box'; v: VarInfo; t: Ty }
  /** a `let x: T;` without initialiser: the slot has type `opt T`; reads unwrap */
  | { k: 'optInit'; v: VarInfo }
  | { k: 'global'; g: GlobalInfo }
  /** a lambda-lifted nested function: `caps` are passed before the arguments */
  | { k: 'lifted'; f: FunInfo; caps: ts.Symbol[]; cell?: VarInfo }
  /** coverage mode: a variable whose declaration could not be translated */
  | { k: 'poison'; ty: Ty }
  /** a `let x: T;` without initialiser that is captured and reassigned: a box of `opt T` */
  | { k: 'boxOpt'; v: VarInfo; t: Ty };

export interface Jump {
  kind: 'loop' | 'breakable';
  labels: string[];
  /** the target of an unlabelled `break` (loops and switches) */
  breakTarget: boolean;
}

export class FnCtx {
  thisVar: VarInfo | null = null;
  isCtor = false;
  jumps: Jump[] = [];
  scopes: Map<ts.Symbol, Binding>[] = [new Map()];
  pre: Item[] = [];
  /** expressions already evaluated (bases of optional chains) */
  override = new Map<ts.Node, Expr>();
  /** coverage mode: `this` of a class that cannot be represented */
  thisPoison = false;
  /** coverage mode: the return type could not be mapped */
  retPoison = false;
  constructor(
    public parent: FnCtx | null,
    public kind: 'main' | 'fun' | 'lambda',
    public async: boolean,
    public bodyRet: Ty,
    public subst: Subst,
    public tsNode: ts.Node,
  ) {}

  bind(sym: ts.Symbol, b: Binding): void { this.scopes[this.scopes.length - 1].set(sym, b); }
  push(): void { this.scopes.push(new Map()); }
  pop(): void { this.scopes.pop(); }
}

export const LEAN_RESERVED = new Set([
  'def', 'fun', 'let', 'if', 'then', 'else', 'do', 'match', 'with', 'end', 'in', 'at', 'by', 'have', 'show', 'from',
  'open', 'import', 'namespace', 'section', 'variable', 'theorem', 'lemma', 'where', 'structure', 'class', 'instance',
  'mut', 'for', 'return', 'try', 'catch', 'finally', 'unless', 'break', 'continue', 'macro', 'syntax', 'deriving',
  'extends', 'abbrev', 'example', 'inductive', 'universe', 'local', 'private', 'protected', 'partial', 'noncomputable',
  'mutual', 'nomatch', 'Type', 'Prop', 'Sort', 'calc', 'suffices', 'obtain', 'axiom', 'opaque', 'set_option', 'attribute',
  'notation', 'infix', 'infixl', 'infixr', 'prefix', 'postfix', 'elab', 'scoped', 'export', 'omit', 'include', 'termination_by',
  'decreasing_by', 'unsafe', 'private', 'public', 'nofun', 'TT', 'program', 'mainBlock', 'StrictTS', 'true', 'false',
]);

export function sanitizeIdent(s: string): string {
  let r = s.replace(/[^A-Za-z0-9_]/g, '_');
  if (!/^[A-Za-z_]/.test(r)) r = '_' + r;
  if (r === '_') r = '_x';
  return r;
}

/** Lean literal of a JavaScript number (exact binary64 value). */
export function f64Lean(x: number): string {
  if (Number.isNaN(x)) return 'F64.nan';
  if (x === Infinity) return '(.inf false)';
  if (x === -Infinity) return '(.inf true)';
  if (Object.is(x, -0)) return '(F64.zero true)';
  if (Number.isInteger(x) && Math.abs(x) <= 2 ** 53) return x >= 0 ? `${x}` : `(F64.ofInt (${x}))`;
  const dv = new DataView(new ArrayBuffer(8));
  dv.setFloat64(0, x);
  const hi = dv.getUint32(0), lo = dv.getUint32(4);
  const neg = (hi >>> 31) === 1;
  const bexp = (hi >>> 20) & 0x7ff;
  const frac = BigInt(hi & 0xfffff) * 4294967296n + BigInt(lo);
  const man = bexp === 0 ? frac : frac + 4503599627370496n;
  const exp = bexp === 0 ? -1074 : bexp - 1075;
  return `(F64.mkFin ${neg} ${man} (${exp}))`;
}

export function numLit(x: number): Expr { return E.lit(`(.num ${f64Lean(x)})`, T.num, x); }
export function bigLit(x: bigint): Expr { return E.lit(`(.bigint ${x < 0n ? `(${x})` : x})`, T.bigint, x); }
export function strLit(s: string): Expr { return E.lit(`(.str ${leanJSStr(s)})`, T.str, s); }

export function isLitUndef(e: Expr): boolean { return e.k === 'lit' && e.ty.k === 'undef'; }

export interface FunDeclInst {
  decl: ts.SignatureDeclaration;
  subst: Subst;
  info: FunInfo;
  /** class instantiation for methods / constructors */
  cls?: ClassInst;
  role: 'fun' | 'ctor' | 'method' | 'getter' | 'setter' | 'static' | 'lifted' | 'structCtor';
  lifted?: { caps: ts.Symbol[]; capBindings: Binding[] };
  struct?: MutStruct;
}

export class Translator {
  checker: ts.TypeChecker;
  analysis: Analysis;
  types: TypeMapper;
  funs: FunInfo[] = [];
  globals: GlobalInfo[] = [];
  funDocs = new Map<FunInfo, string>();
  globalOf = new Map<ts.Symbol, GlobalInfo>();
  instances = new Map<string, FunDeclInst>();
  queue: FunDeclInst[] = [];
  usedLean = new Set<string>(LEAN_RESERVED);
  files: ts.SourceFile[] = [];
  helpers = new Map<string, FunInfo>();
  /** static fields of classes (globals) */
  staticFields = new Map<ts.Symbol, GlobalInfo>();
  /** `a` in element writes `a[i] = v` to arrays from `new Array(n)` (no length check) */
  holeWrites = new Set<ts.Node>();

  // ---- coverage mode (per-function subset coverage of real projects) ----
  coverage = false;
  /** source files of the project itself (coverage mode) */
  projectFiles = new Set<ts.SourceFile>();
  /** cells of top-level functions compared by identity, and their initialisations */
  fnBoxes = new Map<FunInfo, GlobalInfo>();
  fnBoxInits: Item[] = [];
  /** the original subset (`--strict` / `--no-dyn`): no values of type unknown/any */
  get strict(): boolean { return this.types.strict; }
  set strict(v: boolean) { this.types.strict = v; }
  /** module-level `const f = (…) => …` are functions where safe (liftedArrow; off in coverage mode) */
  liftConstArrows = true;
  liftSafe = new Map<ts.VariableDeclaration, boolean>();
  /** diagnostics of the function under analysis */
  covDiags: { rule: string; node: ts.Node | undefined; msg: string }[] = [];
  /** external callees / values used by the function under analysis */
  covExternals = new Set<string>();
  /** external types met by the function under analysis */
  covExtTypes = new Set<string>();
  /** error-derived placeholders created so far (cascade detection) */
  poisonCount = 0;

  constructor(public program: ts.Program, public diags: Diags) {
    this.checker = program.getTypeChecker();
    this.analysis = new Analysis(this.checker);
    this.types = new TypeMapper(this.checker, program, this.analysis);
  }

  /** Record a coverage diagnostic. */
  covRecord(e: unknown, node?: ts.Node): void {
    if (e instanceof Reject && e.extName) this.covExtTypes.add(e.extName);
    if (e instanceof Reject) this.covDiags.push({ rule: e.rule, node: e.node ?? node, msg: e.message });
    else if (e instanceof InternalError) this.covDiags.push({ rule: 'internal', node, msg: e.message });
    else if (e instanceof Error) this.covDiags.push({ rule: 'internal', node, msg: `translator error: ${e.message}` });
  }

  /** An error-derived placeholder for node `n` (typed when TypeScript's type maps). */
  poisonFor(n: ts.Node, fc: FnCtx, exp?: Ty): Expr {
    this.poisonCount++;
    if (exp) return E.poison(exp);
    try { return E.poison(this.tyAt(n, fc)); } catch { return E.poison(T.undef); }
  }

  /** A well-typed stand-in for the value of a call that coverage mode does not translate
   * (calls of other project functions, external calls). */
  placeholderFor(n: ts.Node, fc: FnCtx, exp?: Ty): Expr {
    if (exp) return E.unreachable(exp);
    try { return E.unreachable(this.tyAt(n, fc)); } catch { this.poisonCount++; return E.poison(T.undef); }
  }

  isProjectDecl(d: ts.Node | undefined): boolean {
    return !!d && this.projectFiles.has(d.getSourceFile());
  }

  /** Name of an external (non-project, non-modelled) symbol for coverage reports. */
  externalName(sym: ts.Symbol): string { return this.types.externalSymName(sym); }

  // -------------------------------------------------------------------------------------
  // names

  /** A fresh Lean name for a generated definition (printed with «» by the emitter, so
   * that names that are Lean keywords, like `repeat`, are fine). */
  leanName(base: string): string {
    let b = sanitizeIdent(base);
    let n = b, i = 2;
    while (this.usedLean.has(n) || this.usedLean.has(n + 'Ref') || this.usedLean.has(n + 'Def') || this.usedLean.has(n + '_call')) n = `${b}_${i++}`;
    this.usedLean.add(n);
    return n;
  }

  newFun(name: string, leanBase: string, params: VarInfo[], bodyRet: Ty, async: boolean): FunInfo {
    const f: FunInfo = {
      idx: this.funs.length, name, leanName: this.leanName(leanBase), params,
      ret: async ? T.promise(bodyRet) : bodyRet, async, bodyRet, body: null,
    };
    this.funs.push(f);
    return f;
  }

  newGlobal(name: string, ty: Ty): GlobalInfo {
    const g: GlobalInfo = { idx: this.globals.length, name, leanName: this.leanName('g_' + name), ty };
    this.globals.push(g);
    return g;
  }

  // -------------------------------------------------------------------------------------
  // types

  tyOf(t: ts.Type, fc: FnCtx | null, node: ts.Node): Ty {
    return this.types.map(t, fc ? fc.subst : new Map(), node);
  }

  tyAt(node: ts.Node, fc: FnCtx): Ty {
    return this.tyOf(this.checker.getTypeAtLocation(node), fc, node);
  }

  aliasOf(n: string): Ty {
    const t = this.types.aliases.get(n);
    if (!t) throw new InternalError(`unknown named type ${n}`);
    return t;
  }

  /** Structure of a possibly named type. */
  unfoldTy(t: Ty): Ty { return t.k === 'named' ? this.unfoldTy(this.aliasOf(t.n)) : t; }

  /** Unfold a value of named type until it is not named. */
  unfoldE(e: Expr): Expr {
    if (isPoison(e)) return e.ty.k === 'named' ? E.poison(this.unfoldTy(e.ty)) : e;
    while (e.ty.k === 'named') e = E.unfold(e.ty.n, e, this.aliasOf(e.ty.n));
    return e;
  }

  isNeverType(t: ts.Type): boolean { return !!(t.flags & ts.TypeFlags.Never); }

  fieldsOfObj(c: string): Field[] {
    const fs = this.types.classFields.get(c);
    if (!fs) throw new InternalError(`unknown class ${c}`);
    return fs;
  }

  // -------------------------------------------------------------------------------------
  // symbols and bindings

  resolveSym(sym: ts.Symbol | undefined): ts.Symbol | undefined {
    if (sym && (sym.flags & ts.SymbolFlags.Alias)) return this.checker.getAliasedSymbol(sym);
    return sym;
  }

  symAt(id: ts.Node): ts.Symbol | undefined {
    if (ts.isIdentifier(id)) {
      const ps = paramSymbol(this.checker, id);
      if (ps) return ps;
    }
    if (id.parent && ts.isShorthandPropertyAssignment(id.parent) && id.parent.name === id) {
      return this.resolveSym(this.checker.getShorthandAssignmentValueSymbol(id.parent));
    }
    return this.resolveSym(this.checker.getSymbolAtLocation(id));
  }

  lookup(sym: ts.Symbol, fc: FnCtx): Binding | undefined {
    for (let c: FnCtx | null = fc; c; c = c.parent) {
      for (let i = c.scopes.length - 1; i >= 0; i--) {
        const b = c.scopes[i].get(sym);
        if (b) return b;
      }
      if (c.kind !== 'lambda') break;
    }
    const g = this.globalOf.get(sym);
    if (g) return { k: 'global', g };
    const gp = this.globalPoison.get(sym);
    if (gp) {
      // coverage mode: a module-level variable without IR type; its reason is a violation
      // of every function that uses it
      if (!this.covDiags.some(d => d.node === gp.node && d.rule === gp.rule)) {
        this.covDiags.push({ rule: gp.rule, node: gp.node, msg: gp.msg });
        if (gp.extName) this.covExtTypes.add(gp.extName);
      }
      return { k: 'poison', ty: T.undef };
    }
    return undefined;
  }

  /** coverage mode: module-level variables whose type has no IR representation */
  globalPoison = new Map<ts.Symbol, { rule: string; node: ts.Node | undefined; msg: string; extName?: string }>();

  facts(sym: ts.Symbol): VarFacts | undefined { return this.analysis.vars.get(sym); }

  /** Is the variable reassigned after its declaration? */
  isReassigned(sym: ts.Symbol): boolean { return (this.facts(sym)?.writes.length ?? 0) > 0; }

  /** Does the variable need a box (captured by a closure and reassigned)? */
  needsBox(sym: ts.Symbol): boolean {
    const f = this.facts(sym);
    if (!f || !f.captured || f.writes.length === 0) return false;
    const loop = this.forHeadLoop(f.decl);
    if (loop && f.capturedRefs.every(r => within(r, loop.statement)) && f.writes.every(w => !within(w, loop.statement))) return false;
    return true;
  }

  /** The `for (let …; …; …)` statement whose initialiser declares `decl`, if any. */
  forHeadLoop(decl: ts.Node): ts.ForStatement | undefined {
    let n: ts.Node | undefined = decl;
    while (n && !ts.isVariableDeclarationList(n)) n = n.parent;
    if (n && n.parent && ts.isForStatement(n.parent) && n.parent.initializer === n) return n.parent;
    return undefined;
  }

  /** Is `sym` written anywhere inside `region`? */
  writtenWithin(sym: ts.Symbol, region: ts.Node | ts.Node[]): boolean {
    const f = this.facts(sym);
    if (!f) return false;
    const regions = Array.isArray(region) ? region : [region];
    return f.writes.some(w => regions.some(r => within(w, r)));
  }

  /** A local binding for a declared variable; boxes captured reassigned variables. */
  declareLocal(sym: ts.Symbol, name: string, ty: Ty, init: Expr, fc: FnCtx, out: Item[]): Binding {
    const g = fc.kind === 'main' ? this.globalOf.get(sym) : undefined;
    if (g) {
      out.push(stmtItem(S.gset(g, this.coerce(init, g.ty, sym.valueDeclaration ?? fc.tsNode))));
      return { k: 'global', g };
    }
    if (this.needsBox(sym)) {
      const v = mkVar(name, T.box(ty));
      out.push(declItem(v, E.builtin(`(.boxNew ${showTy(ty)})`, [init], [ty], T.box(ty))));
      const b: Binding = { k: 'box', v, t: ty };
      fc.bind(sym, b);
      return b;
    }
    const v = mkVar(name, ty, this.isReassigned(sym));
    out.push(declItem(v, init));
    const b: Binding = { k: 'var', v };
    fc.bind(sym, b);
    return b;
  }

  /** Read a binding (the stored type, before adapting to TypeScript's narrowed type). */
  readBinding(b: Binding, node: ts.Node): Expr {
    switch (b.k) {
      case 'var': return E.var(b.v);
      case 'box': return E.builtin(`(.boxGet ${showTy(b.t)})`, [E.var(b.v)], [T.box(b.t)], b.t);
      case 'optInit': return E.unwrap(E.var(b.v));
      case 'global': return E.gget(b.g);
      case 'lifted': reject(node, 'unsupported', 'a nested function used as a value must be called');
      case 'poison': return E.poison(b.ty);
      case 'boxOpt': return E.unwrap(E.builtin(`(.boxGet ${showTy(T.opt(b.t))})`, [E.var(b.v)], [T.box(T.opt(b.t))], T.opt(b.t)));
    }
  }

  /** The stored type of a binding. */
  bindingTy(b: Binding): Ty {
    switch (b.k) {
      case 'var': return b.v.ty;
      case 'box': return b.t;
      case 'optInit': return (b.v.ty as Extract<Ty, { k: 'opt' }>).t;
      case 'global': return b.g.ty;
      case 'lifted': return T.undef;
      case 'poison': return b.ty;
      case 'boxOpt': return b.t;
    }
  }

  // -------------------------------------------------------------------------------------
  // ANF helpers

  /** Bind `e` to a fresh constant in the current pre-list unless it is stable. */
  spill(e: Expr, fc: FnCtx, name = 't'): Expr {
    if (isStable(e)) return e;
    const v = mkVar(name, e.ty);
    fc.pre.push(declItem(v, e));
    return E.var(v);
  }

  /** Always bind `e` to a fresh constant. */
  bindTemp(e: Expr, fc: FnCtx, name = 't'): VarInfo {
    if (e.k === 'var' && isStable(e)) return e.v;
    const v = mkVar(name, e.ty);
    fc.pre.push(declItem(v, e));
    return v;
  }

  /** Evaluate thunks in order; when a later one emits pre-items, earlier unstable results
   * are bound to temporaries first (preserving JavaScript's left-to-right order). */
  seq(thunks: (() => Expr)[], fc: FnCtx): Expr[] {
    const res: Expr[] = [];
    for (const th of thunks) {
      const mark = fc.pre.length;
      const e = th();
      if (fc.pre.length > mark) {
        const spills: Item[] = [];
        for (let j = 0; j < res.length; j++) {
          if (!isStable(res[j])) {
            const v = mkVar('t', res[j].ty);
            spills.push(declItem(v, res[j]));
            res[j] = E.var(v);
          }
        }
        fc.pre.splice(mark, 0, ...spills);
      }
      res.push(e);
    }
    return res;
  }

  /** Run `f` with a fresh pre-list; returns the result and the items it emitted. */
  isolate<R>(fc: FnCtx, f: () => R): [R, Item[]] {
    const saved = fc.pre;
    fc.pre = [];
    try {
      const r = f();
      return [r, fc.pre];
    } finally {
      fc.pre = saved;
    }
  }

  /** A mutable temporary of type `t` with an initial value; for types without a default
   * value the temporary has type `opt t` (read with `unwrap`). */
  mutTemp(t: Ty, fc: FnCtx): { v: VarInfo; set: (e: Expr) => Item; get: () => Expr } {
    const dflt = defaultValue(t);
    if (dflt) {
      const v = mkVar('r', t, true);
      fc.pre.push(declItem(v, dflt));
      return { v, set: e => stmtItem(S.assign(v, e)), get: () => E.var(v) };
    }
    const v = mkVar('r', T.opt(t), true);
    fc.pre.push(declItem(v, E.none(t)));
    return { v, set: e => stmtItem(S.assign(v, E.some(e))), get: () => E.unwrap(E.var(v)) };
  }

  // -------------------------------------------------------------------------------------
  // conversions

  coerce(e: Expr, to: Ty, node: ts.Node): Expr {
    if (tyEq(e.ty, to)) return e;
    const r = this.convert(e, to, node, false, 0);
    if (r) return r;
    this.conversionError(e.ty, to, node);
  }

  /** Is the value converted at `node` of a dictionary type with named properties? */
  copiesNamedDict(node: ts.Node): boolean {
    let st: ts.Type | undefined;
    try { st = this.checker.getTypeAtLocation(node); } catch { st = undefined; }
    return !!st && this.types.isNamedDict(st);
  }

  conversionError(from: Ty, to: Ty, node: ts.Node): never {
    const f = this.unfoldTy(from), t = this.unfoldTy(to);
    if (f.k === 'dict' && t.k === 'record' && this.copiesNamedDict(node)) {
      reject(node, 'unsupported-conversion', `${prettyTy(from)} with named properties used as the record type ${prettyTy(to)}: a copy would not show later writes through the dictionary`);
    }
    const cellOf = (x: Ty): Ty | undefined =>
      x.k === 'box' && x.t.k === 'record' ? x.t : x.k === 'opt' ? cellOf(x.t) : x.k === 'union' ? x.ts.map(cellOf).find(y => !!y) : undefined;
    const cell = cellOf(t);
    if (cell && (f.k === 'record' || (f.k === 'box' && f.t.k === 'record'))) {
      reject(node, 'record-identity', `a value of type ${prettyTy(from)} used where objects of type ${prettyTy(cell)} are compared by identity ` +
        '(it would be a second object to StrictTS)');
    }
    if (t.k === 'obj' && (f.k === 'record' || (f.k === 'obj' && f.c !== t.c)) && !this.types.classes.has(t.c)) {
      reject(node, 'record-mutation', `${prettyTy(from)} flows into ${t.c}, an object type whose fields are assigned somewhere; ` +
        'mutation through width subtyping is not allowed (values of record types are immutable)');
    }
    if (t.k === 'obj' && f.k === 'obj' && f.c !== t.c) reject(node, 'unsupported-conversion', `class ${f.c} used as ${t.c} (classes are nominal)`);
    if ((t.k === 'record' && f.k === 'obj')) reject(node, 'unsupported-conversion', `heap object ${f.c} used as the record type ${prettyTy(to)} (no width subtyping for objects)`);
    if (f.k === 'arr' && t.k === 'arr') reject(node, 'unsupported-conversion', `array covariance: ${prettyTy(from)} used as ${prettyTy(to)} (arrays are mutable; copy the array)`);
    reject(node, 'unsupported-conversion', `cannot convert ${prettyTy(from)} to ${prettyTy(to)} here`);
  }

  /** Coerce, or narrow to TypeScript's narrowed type at a read. */
  adapt(e: Expr, to: Ty, node: ts.Node): Expr {
    if (tyEq(e.ty, to)) return e;
    const r = this.convert(e, to, node, true, 0);
    if (r) return r;
    this.conversionError(e.ty, to, node);
  }

  /** Evaluate `e` once and continue with a variable holding its value. */
  withValue(e: Expr, name: string, k: (x: Expr) => Expr): Expr {
    if (isStable(e) && (e.k === 'var' || e.k === 'lit')) return k(e);
    const v = mkVar(name, e.ty);
    return E.letE(v, e, k(E.var(v)));
  }

  /** The record in an object cell (identity.ts). */
  unboxCell(e: Expr): Expr {
    const rt = (e.ty as Extract<Ty, { k: 'box' }>).t;
    return E.builtin(`(.boxGet ${showTy(rt)})`, [e], [e.ty], rt);
  }

  /** Does a value of type `t` hold cells of functions or records compared by identity
   * (identity.ts; only of records with `recordsOnly`)? (Not counting the parameters and results
   * of functions in it.) */
  holdsIdBox(t: Ty, recordsOnly = false, seen = new Set<string>()): boolean {
    const r = (x: Ty) => this.holdsIdBox(x, recordsOnly, seen);
    switch (t.k) {
      case 'box': return t.t.k === 'record' || (t.t.k === 'fn' && !recordsOnly) || r(t.t);
      case 'named': {
        if (seen.has(t.n)) return false;
        seen.add(t.n);
        return r(this.aliasOf(t.n));
      }
      case 'arr': case 'set': case 'opt': case 'promise': case 'dict': return r(t.t);
      case 'map': return r(t.key) || r(t.val);
      case 'tup': case 'union': return t.ts.some(r);
      case 'record': return t.fs.some(f => r(f.ty));
      default: return false;
    }
  }

  /** The closure in a function cell (identity.ts). */
  unboxFn(e: Expr): Expr {
    const ft = (e.ty as Extract<Ty, { k: 'box' }>).t;
    return E.builtin(`(.boxGet ${showTy(ft)})`, [e], [e.ty], ft);
  }

  /** The cell of a top-level function compared by identity: one module variable, set when the
   * module starts (before its body: function declarations are hoisted). */
  fnBox(f: FunInfo): GlobalInfo {
    const known = this.fnBoxes.get(f);
    if (known) return known;
    const ft = T.fn(f.params.map(p => p.ty), f.ret);
    const g = this.newGlobal(`${f.name}$fn`, T.box(ft));
    this.fnBoxes.set(f, g);
    this.fnBoxInits.push(stmtItem(S.gset(g, E.builtin(`(.boxNew ${showTy(ft)})`, [E.funVal(f)], [ft], T.box(ft)))));
    return g;
  }

  /** Does a value of type `t` hold objects whose `toString` / `valueOf` is not the one of
   * `Object.prototype` (class methods, fields of mutable objects with these names)? */
  customToPrimitive(t: Ty, seen = new Set<string>()): boolean {
    switch (t.k) {
      case 'obj': {
        if (seen.has(t.c)) return false;
        seen.add(t.c);
        const special = (n: string | undefined) => n === 'toString' || n === 'valueOf';
        const ci = this.types.classes.get(t.c);
        if (ci && ci.decl.members.some(m => !!m.name && ts.isIdentifier(m.name) && special(m.name.text))) return true;
        const info = this.classOfObj(t.c);
        return !!info && (info.fields.some(f => special(f.name)) || info.fields.some(f => this.customToPrimitive(f.ty, seen)));
      }
      case 'named': {
        if (seen.has('named:' + t.n)) return false;
        seen.add('named:' + t.n);
        return this.customToPrimitive(this.aliasOf(t.n), seen);
      }
      case 'arr': case 'opt': case 'dict': return this.customToPrimitive(t.t, seen);
      case 'tup': case 'union': return t.ts.some(x => this.customToPrimitive(x, seen));
      case 'record': return t.fs.some(f => this.customToPrimitive(f.ty, seen));
      default: return false;
    }
  }

  /** An unknown value at type `to`: a checked cast; a record from a dictionary of unknown
   * values (JSON objects) as well as from a record value. */
  fromDyn(e: Expr, to: Ty, node: ts.Node): Expr {
    // (an unknown value may be an object the program already holds in a cell)
    if (this.holdsIdBox(to)) reject(node, 'record-identity', `an unknown value used as ${prettyTy(to)}, whose functions or objects are compared by identity`);
    const cast = (x: Expr, t: Ty) => E.prim(`(.dynCast ${showTy(t)})`, [x], [T.dyn], T.opt(t));
    if (this.unfoldTy(to).k !== 'record') return E.unwrap(cast(e, to));
    const dd = T.dict(T.dyn);
    return this.withValue(e, 'u', x => {
      const r = mkVar('r', to), d = mkVar('d', dd);
      return E.caseOpt(cast(x, to), E.caseOpt(cast(x, dd), E.unreachable(to), d, this.dictToRecord(E.var(d), to, node)), r, E.var(r));
    });
  }

  /** The record of type `to` from a dictionary of unknown values: each field read by name and
   * cast (absent: `undefined`, a panic for a required field). Fields holding typed arrays or
   * maps are not converted (that would copy them). */
  dictToRecord(e: Expr, to: Ty, node: ts.Node): Expr {
    const rt = this.unfoldTy(to) as Extract<Ty, { k: 'record' }>;
    const copies = (t: Ty): boolean => {
      const u = this.unfoldTy(t);
      switch (u.k) {
        case 'tarr': return true;
        case 'arr': case 'set': case 'dict': return this.unfoldTy(u.t).k !== 'dyn';
        case 'map': return true;
        case 'opt': return copies(u.t);
        case 'union': return u.ts.some(copies);
        case 'record': return u.fs.some(f => copies(f.ty));
        default: return false;
      }
    };
    if (copies(rt)) reject(node, 'unsupported-conversion', `${prettyTy(to)} from a dictionary of unknown values (typed arrays and maps in it would be copies)`);
    const dd = T.dict(T.dyn);
    const built = this.withValue(e, 'd', d => E.mkRec(rt, rt.fs.map(f => {
      const got = E.builtin('(.dictGet .dyn)', [d, strLit(f.name)], [dd, T.str], T.opt(T.dyn));
      if (f.ty.k === 'opt') {
        const x = mkVar('x', T.dyn);
        return E.caseOpt(got, E.none(f.ty.t), x, E.some(this.fromDyn(E.var(x), f.ty.t, node)));
      }
      return this.fromDyn(E.unwrap(got), f.ty, node);
    })));
    return to.k === 'named' ? E.fold(to.n, built) : built;
  }

  convert(e: Expr, to: Ty, node: ts.Node, narrow: boolean, depth: number): Expr | null {
    if (isPoison(e)) return E.poison(to);
    const from = e.ty;
    if (tyEq(from, to)) return e;
    if (depth > 12) return null;
    const rec = (x: Expr, t: Ty, nw = narrow) => this.convert(x, t, node, nw, depth + 1);
    // unknown: an upcast keeps the value with its type; a downcast (narrowing or `as`, which
    // TypeScript checked) is a checked cast that panics on a mismatch
    // functions compared by identity (identity.ts): a cell is read where a plain function is
    // expected; a plain function never becomes a cell here (that could make two cells for one
    // function object: cells are created only where JavaScript creates the function)
    if (from.k === 'box' && from.t.k === 'fn' && (to.k === 'fn' || to.k === 'dyn')) return rec(this.unboxFn(e), to);
    if (to.k === 'box' && to.t.k === 'fn' && from.k === 'fn') {
      reject(node, 'fn-identity', `a function of type ${prettyTy(from)} used where functions are compared by identity (${prettyTy(to.t)})`);
    }
    // records compared by identity: likewise, the cell is read where a record (of this or a
    // narrower type) or an unknown value is expected; a record never becomes a cell here, nor
    // a cell one of another record type (conversionError says why)
    if (from.k === 'box' && from.t.k === 'record' && (to.k === 'record' || to.k === 'dyn' || (to.k === 'named' && this.unfoldTy(to).k === 'record'))) {
      return rec(this.unboxCell(e), to);
    }
    if (to.k === 'box' && to.t.k === 'record' && (from.k === 'record' || from.k === 'box')) return null;
    if (to.k === 'dyn') {
      // (String(x) of an unknown value assumes Object.prototype.toString for objects)
      if (this.customToPrimitive(from)) reject(node, 'unsupported-conversion', `${prettyTy(from)} as unknown: an object with its own toString/valueOf`);
      if (this.holdsIdBox(from)) reject(node, 'record-identity', `${prettyTy(from)} as unknown: it holds functions or objects compared by identity`);
      if (holdsTimer(from)) reject(node, 'timer-handle', `${prettyTy(from)} as unknown: a Node timer handle (an object in Node, a number here)`);
      return E.prim(`(.toDyn ${showTy(from)})`, [e], [from], T.dyn);
    }
    if (from.k === 'dyn') return this.fromDyn(e, to, node);
    // a dictionary of unknown values (a JSON object, Firestore's DocumentData) as a record (a
    // copy; not of a dictionary type with named properties, which the program writes through)
    if (from.k === 'dict' && from.t.k === 'dyn' && this.unfoldTy(to).k === 'record') {
      return this.copiesNamedDict(node) ? null : this.dictToRecord(e, to, node);
    }
    if (from.k === 'named') return rec(E.unfold(from.n, e, this.aliasOf(from.n)), to);
    if (to.k === 'named') {
      const inner = rec(e, this.aliasOf(to.n));
      return inner && E.fold(to.n, inner);
    }
    switch (to.k) {
      case 'opt': {
        if (from.k === 'undef') return isLitUndef(e) ? E.none(to.t) : this.withValue(e, 'u', () => E.none(to.t));
        // (`undefined | undefined`: undefined either way)
        if (from.k === 'opt' && from.t.k === 'undef') return this.withValue(e, 'u', () => E.none(to.t));
        if (from.k === 'opt') {
          const v = mkVar('x', from.t);
          const inner = rec(E.var(v), to.t);
          if (inner) return E.caseOpt(e, E.none(to.t), v, E.some(inner));
          break;
        }
        const inner = rec(e, to.t, false);
        if (inner) return E.some(inner);
        break;
      }
      case 'union': {
        const i = to.ts.findIndex(m => tyEq(m, from));
        if (i >= 0) return E.inj(to, i, e);
        if (from.k === 'union') {
          const alts: { v: VarInfo; body: Expr }[] = [];
          let ok = true;
          for (const m of from.ts) {
            const v = mkVar('m', m);
            const b = rec(E.var(v), to);
            if (!b) { ok = false; break; }
            alts.push({ v, body: b });
          }
          if (ok) return E.caseU(e, alts);
          break;
        }
        // a member the value converts to; when several members accept it the choice would
        // be a guess (TypeScript's structural typing does not decide it), so it is rejected
        const cands: [number, Expr][] = [];
        for (let j = 0; j < to.ts.length; j++) {
          const inner = rec(e, to.ts[j], false);
          if (inner) cands.push([j, inner]);
        }
        if (cands.length === 1) return E.inj(to, cands[0][0], cands[0][1]);
        if (cands.length > 1) {
          // prefer a member of the same kind with exactly the same field names
          const f = this.unfoldTy(from);
          const same = cands.filter(([j]) => {
            const m = this.unfoldTy(to.ts[j]);
            return m.k === f.k && (m.k !== 'record' || (f.k === 'record' && m.fs.map(x => x.name).join() === f.fs.map(x => x.name).join()));
          });
          if (same.length === 1) return E.inj(to, same[0][0], same[0][1]);
          reject(node, 'unsupported-conversion', `${prettyTy(from)} fits several members of ${prettyTy(to)}; annotate the value with one member type`);
        }
        break;
      }
      case 'str':
        if (from.k === 'enum') return E.prim(`(.enumToStr [${from.cases.map(leanStrLit).join(', ')}])`, [e], [from], T.str);
        break;
      case 'enum':
        if (from.k === 'enum' && from.cases.every(c => to.cases.includes(c))) {
          return this.withValue(e, 'k', x => {
            let acc: Expr = E.enumLit(to, to.cases.indexOf(from.cases[from.cases.length - 1]));
            for (let i = from.cases.length - 2; i >= 0; i--) {
              acc = E.cond(E.seq(x, E.enumLit(from, i)), E.enumLit(to, to.cases.indexOf(from.cases[i])), acc);
            }
            return acc;
          });
        }
        if (from.k === 'str' && e.k === 'lit' && typeof e.js === 'string' && to.cases.includes(e.js)) {
          return E.enumLit(to, to.cases.indexOf(e.js));
        }
        break;
      case 'record':
        if (from.k === 'record') {
          return this.projectRecord(e, from.fs, to.fs, node, narrow, depth);
        }
        break;
      case 'tup':
        if (from.k === 'arr' && to.ts.every(x => tyEq(x, from.t))) {
          // an array TypeScript types as a tuple (e.g. the value of Promise.all); reading a
          // missing element panics
          return this.withValue(e, 'a', x => E.mkTup(to.ts.map((_, i) =>
            E.builtin(`(.arrGet ${showTy(from.t)})`, [x, numLit(i)], [from, T.num], from.t))));
        }
        if (from.k === 'tup' && from.ts.length === to.ts.length) {
          let ok = true;
          const r = this.withValue(e, 'p', x => {
            const parts: Expr[] = [];
            for (let i = 0; i < to.ts.length; i++) {
              const c = rec(E.getTup(x, i), to.ts[i]);
              if (!c) { ok = false; return x; }
              parts.push(c);
            }
            return E.mkTup(parts);
          });
          if (ok) return r;
        }
        break;
      case 'fn':
        if (from.k === 'fn') return this.wrapFn(e, from, to, node, depth);
        break;
      case 'arr':
        if (from.k === 'tup') {
          // a tuple value used as an array: a fresh array of its elements
          let ok = true;
          const r = this.withValue(e, 'p', x => {
            const parts: Expr[] = [];
            for (let i = 0; i < from.ts.length; i++) {
              const c = rec(E.getTup(x, i), to.t, false);
              if (!c) { ok = false; return x; }
              parts.push(c);
            }
            return E.builtin(`(.arrOf ${showTy(to.t)} ${parts.length})`, parts, parts.map(() => to.t), to);
          });
          if (ok) return r;
        }
        break;
    }
    if (narrow) return this.narrowTo(e, to, node, depth);
    return null;
  }

  private projectRecord(e: Expr, fromFs: Field[], toFs: Field[], node: ts.Node, narrow: boolean, depth: number): Expr | null {
    for (const f of toFs) {
      if (!fromFs.some(g => g.name === f.name) && f.ty.k !== 'opt') return null;
    }
    let ok = true;
    const r = this.withValue(e, 'r', x => {
      const parts: Expr[] = [];
      for (const f of toFs) {
        const gi = fromFs.findIndex(g => g.name === f.name);
        if (gi < 0) { parts.push(E.none((f.ty as Extract<Ty, { k: 'opt' }>).t)); continue; }
        const c = this.convert(E.getRec(x, gi), f.ty, node, narrow, depth + 1);
        if (!c) { ok = false; return x; }
        parts.push(c);
      }
      return E.mkRec(T.record(toFs), parts);
    });
    return ok ? r : null;
  }

  /** Adapt a function value to another function type (JavaScript call semantics: extra
   * arguments are dropped, missing optional parameters receive `undefined`). */
  private wrapFn(e: Expr, from: Extract<Ty, { k: 'fn' }>, to: Extract<Ty, { k: 'fn' }>, node: ts.Node, depth: number): Expr | null {
    const params = to.args.map((t, i) => mkVar(`a${i}`, t));
    const args: Expr[] = [];
    for (let i = 0; i < from.args.length; i++) {
      if (i < to.args.length) {
        const c = this.convert(E.var(params[i]), from.args[i], node, false, depth + 1);
        if (!c) return null;
        args.push(c);
      } else if (from.args[i].k === 'opt') args.push(E.none((from.args[i] as Extract<Ty, { k: 'opt' }>).t));
      else if (from.args[i].k === 'undef') args.push(E.undef());
      else if (from.args[i].k === 'dyn') args.push(E.prim('(.toDyn .undef)', [E.undef()], [T.undef], T.dyn));
      else return null;
    }
    const mk = (f: Expr): Expr | null => {
      const call = f.k === 'funVal' ? E.call(f.f, args) : E.app(f, args);
      let body: Block;
      if (to.ret.k === 'undef' && from.ret.k !== 'undef') body = [stmtItem(S.expr(call))];
      else {
        const r = this.convert(call, to.ret, node, false, depth + 1);
        if (!r) return null;
        body = [stmtItem(S.ret(r))];
      }
      return E.lam(false, params, to.ret, body);
    };
    if (e.k === 'funVal' || (e.k === 'var' && isStable(e))) return mk(e);
    const v = mkVar('f', e.ty);
    const inner = mk(E.var(v));
    return inner && E.letE(v, e, inner);
  }

  /** Narrowing conversions (TypeScript proved the value has the narrower type; other
   * cases panic). */
  private narrowTo(e: Expr, to: Ty, node: ts.Node, depth: number): Expr | null {
    const from = e.ty;
    const rec = (x: Expr, t: Ty) => this.convert(x, t, node, true, depth + 1);
    if (from.k === 'opt') {
      if (to.k === 'undef') return this.withValue(e, 'u', () => E.undef());
      if (to.k === 'opt') {
        const v = mkVar('x', from.t);
        const inner = rec(E.var(v), to.t);
        return inner && E.caseOpt(e, E.none(to.t), v, E.some(inner));
      }
      return rec(E.unwrap(e), to);
    }
    if (from.k === 'union') {
      // members of the narrowed type keep their value; TypeScript proved the others impossible
      const alts: { v: VarInfo; body: Expr }[] = [];
      let any = false;
      for (const m of from.ts) {
        const v = mkVar('m', m);
        const b = this.memberMatches(m, to) ? this.convert(E.var(v), to, node, true, depth + 1) : null;
        if (b) any = true;
        alts.push({ v, body: b ?? E.unreachable(to) });
      }
      return any ? E.caseU(e, alts) : null;
    }
    if (from.k === 'str' && to.k === 'enum') {
      // a string TypeScript narrowed to a literal union (e.g. a discriminant)
      return this.withValue(e, 'k', x => {
        let acc: Expr = E.unreachable(to);
        for (let i = to.cases.length - 1; i >= 0; i--) acc = E.cond(E.seq(x, strLit(to.cases[i])), E.enumLit(to, i), acc);
        return acc;
      });
    }
    if (from.k === 'enum' && to.k === 'enum' && to.cases.every(c => from.cases.includes(c))) {
      // through the case name (an equality on `from` would repeat its case list in every test)
      return rec(E.prim(`(.enumToStr [${from.cases.map(leanStrLit).join(', ')}])`, [e], [from], T.str), to);
    }
    return null;
  }

  /** Does union member `m` belong to the narrowed type `to` (same type, a member of a
   * narrower union, a string-like member of a string type, or a narrowable optional)? */
  memberMatches(m: Ty, to: Ty): boolean {
    const mu = this.unfoldTy(m), tu = this.unfoldTy(to);
    if (tyEq(m, to) || tyEq(mu, tu)) return true;
    if (tu.k === 'union') return tu.ts.some(x => this.memberMatches(m, x));
    if (tu.k === 'opt') return mu.k === 'undef' || this.memberMatches(m, tu.t);
    if ((mu.k === 'enum' || mu.k === 'str') && (tu.k === 'str' || tu.k === 'enum')) return true;
    if (mu.k === 'union') return mu.ts.some(x => this.memberMatches(x, to));
    if (mu.k === 'arr' && tu.k === 'tup') return true;
    return false;
  }

  // -------------------------------------------------------------------------------------
  // helpers used by several lowering files

  /** The JavaScript `typeof` tag of values of a type (for narrowing). */
  typeofTag(t: Ty): string {
    const u = this.unfoldTy(t);
    switch (u.k) {
      case 'num': return 'number';
      case 'bigint': return 'bigint';
      case 'bool': return 'boolean';
      case 'str': case 'enum': return 'string';
      case 'undef': return 'undefined';
      case 'fn': return 'function';
      case 'box': return u.t.k === 'fn' ? 'function' : 'object';
      default: return 'object';
    }
  }

  translateProgram(): ProgramIR | null { throw new InternalError('installed by index.ts'); }
}

/** Does a value of type `t` hold a Node timer handle (TIMER_TY)? */
export function holdsTimer(t: Ty): boolean {
  switch (t.k) {
    case 'record': return tyEq(t, TIMER_TY) || t.fs.some(f => holdsTimer(f.ty));
    case 'arr': case 'set': case 'opt': case 'promise': case 'dict': case 'box': return holdsTimer(t.t);
    case 'map': return holdsTimer(t.key) || holdsTimer(t.val);
    case 'tup': case 'union': return t.ts.some(holdsTimer);
    default: return false;
  }
}

export function defaultValue(t: Ty): Expr | null {
  switch (t.k) {
    case 'num': return numLit(0);
    case 'bigint': return bigLit(0n);
    case 'bool': return E.bool(false);
    case 'str': return strLit('');
    case 'undef': return E.undef();
    case 'opt': return E.none(t.t);
    default: return null;
  }
}

export function within(n: ts.Node, region: ts.Node): boolean {
  return n.pos >= region.pos && n.end <= region.end && n.getSourceFile() === region.getSourceFile();
}

export { ts, Reject, reject, ownerOf, isLibDecl, substKey };

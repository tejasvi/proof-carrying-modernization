// The StrictTS IR on the TypeScript side, with named variables. `emit.ts` turns it into
// the de Bruijn terms of `StrictTS/Core/Syntax.lean`.
import { Ty, T, showTy, tyEq, eqable, prettyTy } from './ty';

let nextVarId = 0;

/** A local variable (binder). `assigned` is set when an assignment to it is built; the
 * emitted slot is mutable iff it is assigned. `mayChange` is known up front (from the
 * TypeScript-level analysis) for variables that will be assigned somewhere. */
export interface VarInfo { id: number; name: string; ty: Ty; assigned: boolean; mayChange: boolean }

export function mkVar(name: string, ty: Ty, mayChange = false): VarInfo {
  return { id: nextVarId++, name, ty, assigned: false, mayChange };
}

/** A module-level variable (heap cell `idx`). */
export interface GlobalInfo { idx: number; name: string; leanName: string; ty: Ty }

/** A top-level function of the generated program. */
export interface FunInfo {
  idx: number;
  name: string;      // display name (FunRef/FunDef name field)
  leanName: string;  // Lean identifier of the FunDef; the FunRef is `${leanName}Ref`
  params: VarInfo[];
  /** type of the function value: `fn args ret` with `ret = promise ρ` for async */
  ret: Ty;
  async: boolean;
  /** return type of the body (`ρ`) */
  bodyRet: Ty;
  body: Block | null;
}

export function funArgs(f: FunInfo): Ty[] { return f.params.map(p => p.ty); }
export function funTy(f: FunInfo): Ty { return T.fn(funArgs(f), f.ret); }

export type Expr =
  | { k: 'lit'; lean: string; ty: Ty; js?: unknown; poison?: boolean }
  | { k: 'var'; v: VarInfo; ty: Ty }
  | { k: 'gget'; g: GlobalInfo; ty: Ty }
  | { k: 'prim'; op: string; args: Expr[]; ty: Ty }
  | { k: 'builtin'; op: string; args: Expr[]; ty: Ty }
  | { k: 'and'; a: Expr; b: Expr; ty: Ty }
  | { k: 'or'; a: Expr; b: Expr; ty: Ty }
  | { k: 'cond'; c: Expr; a: Expr; b: Expr; ty: Ty }
  | { k: 'letE'; v: VarInfo; init: Expr; body: Expr; ty: Ty }
  | { k: 'call'; f: FunInfo; args: Expr[]; ty: Ty }
  | { k: 'app'; f: Expr; args: Expr[]; ty: Ty }
  | { k: 'lam'; async: boolean; params: VarInfo[]; body: Block; ty: Ty }
  | { k: 'funVal'; f: FunInfo; ty: Ty }
  | { k: 'mkTup'; args: Expr[]; ty: Ty }
  | { k: 'getTup'; e: Expr; idx: number; ty: Ty }
  | { k: 'mkRec'; args: Expr[]; ty: Ty }
  | { k: 'getRec'; e: Expr; idx: number; ty: Ty }
  | { k: 'newObj'; c: string; ty: Ty }
  | { k: 'getField'; e: Expr; c: string; idx: number; ty: Ty }
  | { k: 'fold'; n: string; e: Expr; ty: Ty }
  | { k: 'unfold'; n: string; e: Expr; ty: Ty }
  | { k: 'none'; ty: Ty }
  | { k: 'some'; e: Expr; ty: Ty }
  | { k: 'unwrap'; e: Expr; ty: Ty }
  | { k: 'caseOpt'; e: Expr; none: Expr; v: VarInfo; some: Expr; ty: Ty }
  | { k: 'inj'; idx: number; e: Expr; ty: Ty }
  | { k: 'caseU'; e: Expr; alts: { v: VarInfo; body: Expr }[]; ty: Ty }
  | { k: 'enumLit'; idx: number; ty: Ty }
  /** a call of an external function answered by the world's oracle (`externAsync`: the
   * answer settles a fresh promise; `ty` is then `promise t`) */
  | { k: 'extern'; name: string; async: boolean; args: Expr[]; ty: Ty };

export type Stmt =
  | { k: 'expr'; e: Expr }
  | { k: 'assign'; v: VarInfo; e: Expr }
  | { k: 'gset'; g: GlobalInfo; e: Expr }
  | { k: 'setField'; o: Expr; c: string; idx: number; e: Expr }
  | { k: 'ite'; c: Expr; t: Block; f: Block }
  | { k: 'while'; c: Expr; body: Block }
  | { k: 'doWhile'; body: Block; c: Expr }
  | { k: 'forLoop'; c: Expr; body: Block; step: Block }
  | { k: 'forOf'; e: Expr; v: VarInfo; body: Block }
  | { k: 'forOfMap'; e: Expr; v: VarInfo; body: Block }
  | { k: 'forOfSet'; e: Expr; v: VarInfo; body: Block }
  | { k: 'forOfStr'; e: Expr; v: VarInfo; body: Block }
  | { k: 'brk'; n: number }
  | { k: 'cont'; n: number }
  | { k: 'ret'; e: Expr }
  | { k: 'retP'; e: Expr }
  | { k: 'throw'; e: Expr }
  | { k: 'try'; body: Block; v: VarInfo; handler: Block; fin: Block }
  | { k: 'tryFin'; body: Block; fin: Block }
  | { k: 'caseOptS'; e: Expr; none: Block; v: VarInfo; some: Block }
  | { k: 'caseUS'; e: Expr; alts: { v: VarInfo; body: Block }[] }
  | { k: 'block'; b: Block }
  | { k: 'breakable'; b: Block };

export type Item =
  | { k: 'stmt'; s: Stmt }
  | { k: 'decl'; v: VarInfo; init: Expr }
  | { k: 'await'; v: VarInfo; init: Expr };

export type Block = Item[];

export class InternalError extends Error {}

function check(cond: boolean, msg: string): void {
  if (!cond) throw new InternalError(msg);
}

function expectTy(e: Expr, t: Ty, what: string): void {
  if (!tyEq(e.ty, t)) throw new InternalError(`${what}: expected ${prettyTy(t)}, got ${prettyTy(e.ty)}`);
}

// ---------------------------------------------------------------------------------------
// Smart constructors (type-checked: an ill-typed IR term is an internal error)

export const E = {
  lit(lean: string, ty: Ty, js?: unknown): Expr { return { k: 'lit', lean, ty, js }; },
  var(v: VarInfo): Expr { return { k: 'var', v, ty: v.ty }; },
  gget(g: GlobalInfo): Expr { return { k: 'gget', g, ty: g.ty }; },
  prim(op: string, args: Expr[], argTys: Ty[], ty: Ty): Expr {
    check(args.length === argTys.length, `prim ${op}: arity`);
    args.forEach((a, i) => expectTy(a, argTys[i], `prim ${op} arg ${i}`));
    return { k: 'prim', op, args, ty };
  },
  builtin(op: string, args: Expr[], argTys: Ty[], ty: Ty): Expr {
    check(args.length === argTys.length, `builtin ${op}: arity ${args.length} vs ${argTys.length}`);
    args.forEach((a, i) => expectTy(a, argTys[i], `builtin ${op} arg ${i}`));
    return { k: 'builtin', op, args, ty };
  },
  and(a: Expr, b: Expr): Expr { expectTy(a, T.bool, 'and'); expectTy(b, T.bool, 'and'); return { k: 'and', a, b, ty: T.bool }; },
  or(a: Expr, b: Expr): Expr { expectTy(a, T.bool, 'or'); expectTy(b, T.bool, 'or'); return { k: 'or', a, b, ty: T.bool }; },
  cond(c: Expr, a: Expr, b: Expr): Expr {
    expectTy(c, T.bool, 'cond'); expectTy(b, a.ty, 'cond branches');
    return { k: 'cond', c, a, b, ty: a.ty };
  },
  letE(v: VarInfo, init: Expr, body: Expr): Expr {
    expectTy(init, v.ty, 'letE init');
    return { k: 'letE', v, init, body, ty: body.ty };
  },
  call(f: FunInfo, args: Expr[]): Expr {
    check(args.length === f.params.length, `call ${f.name}: arity`);
    args.forEach((a, i) => expectTy(a, f.params[i].ty, `call ${f.name} arg ${i}`));
    return { k: 'call', f, args, ty: f.ret };
  },
  app(f: Expr, args: Expr[]): Expr {
    check(f.ty.k === 'fn', 'app of non-function');
    const ft = f.ty as Extract<Ty, { k: 'fn' }>;
    check(args.length === ft.args.length, 'app arity');
    args.forEach((a, i) => expectTy(a, ft.args[i], `app arg ${i}`));
    return { k: 'app', f, args, ty: ft.ret };
  },
  lam(async: boolean, params: VarInfo[], ret: Ty, body: Block): Expr {
    return { k: 'lam', async, params, body, ty: T.fn(params.map(p => p.ty), async ? T.promise(ret) : ret) };
  },
  funVal(f: FunInfo): Expr { return { k: 'funVal', f, ty: funTy(f) }; },
  mkTup(args: Expr[]): Expr { return { k: 'mkTup', args, ty: T.tup(args.map(a => a.ty)) }; },
  getTup(e: Expr, idx: number): Expr {
    check(e.ty.k === 'tup', 'getTup of non-tuple');
    const ts = (e.ty as Extract<Ty, { k: 'tup' }>).ts;
    check(idx < ts.length, 'getTup index');
    return { k: 'getTup', e, idx, ty: ts[idx] };
  },
  mkRec(ty: Ty, args: Expr[]): Expr {
    check(ty.k === 'record', 'mkRec type');
    const fs = (ty as Extract<Ty, { k: 'record' }>).fs;
    check(fs.length === args.length, 'mkRec arity');
    args.forEach((a, i) => expectTy(a, fs[i].ty, `mkRec field ${fs[i].name}`));
    return { k: 'mkRec', args, ty };
  },
  getRec(e: Expr, idx: number): Expr {
    check(e.ty.k === 'record', 'getRec of non-record');
    const fs = (e.ty as Extract<Ty, { k: 'record' }>).fs;
    return { k: 'getRec', e, idx, ty: fs[idx].ty };
  },
  newObj(c: string): Expr { return { k: 'newObj', c, ty: T.obj(c) }; },
  getField(e: Expr, c: string, idx: number, fieldTy: Ty): Expr {
    expectTy(e, T.obj(c), 'getField');
    return { k: 'getField', e, c, idx, ty: fieldTy };
  },
  // (`unfold (fold e)` and `fold (unfold e)` are `e`: emitted as written, Lean could not infer
  // the name of the type between them)
  fold(n: string, e: Expr): Expr {
    if (e.k === 'unfold' && e.n === n) return e.e;
    return { k: 'fold', n, e, ty: T.named(n) };
  },
  unfold(n: string, e: Expr, aliasTy: Ty): Expr {
    expectTy(e, T.named(n), 'unfold');
    if (e.k === 'fold' && e.n === n) return e.e;
    return { k: 'unfold', n, e, ty: aliasTy };
  },
  none(t: Ty): Expr { return { k: 'none', ty: T.opt(t) }; },
  some(e: Expr): Expr { return { k: 'some', e, ty: T.opt(e.ty) }; },
  unwrap(e: Expr): Expr {
    check(e.ty.k === 'opt', 'unwrap of non-optional');
    return { k: 'unwrap', e, ty: (e.ty as Extract<Ty, { k: 'opt' }>).t };
  },
  caseOpt(e: Expr, none: Expr, v: VarInfo, some: Expr): Expr {
    check(e.ty.k === 'opt', 'caseOpt of non-optional');
    expectTy(E.var(v), (e.ty as Extract<Ty, { k: 'opt' }>).t, 'caseOpt binder');
    expectTy(some, none.ty, 'caseOpt branches');
    return { k: 'caseOpt', e, none, v, some, ty: none.ty };
  },
  inj(ty: Ty, idx: number, e: Expr): Expr {
    check(ty.k === 'union', 'inj into non-union');
    expectTy(e, (ty as Extract<Ty, { k: 'union' }>).ts[idx], 'inj member');
    return { k: 'inj', idx, e, ty };
  },
  caseU(e: Expr, alts: { v: VarInfo; body: Expr }[]): Expr {
    check(e.ty.k === 'union', 'caseU of non-union');
    const ts = (e.ty as Extract<Ty, { k: 'union' }>).ts;
    check(ts.length === alts.length && alts.length > 0, 'caseU arity');
    alts.forEach((a, i) => { expectTy(E.var(a.v), ts[i], 'caseU binder'); expectTy(a.body, alts[0].body.ty, 'caseU branches'); });
    return { k: 'caseU', e, alts, ty: alts[0].body.ty };
  },
  enumLit(ty: Ty, idx: number): Expr {
    check(ty.k === 'enum' && idx < (ty as Extract<Ty, { k: 'enum' }>).cases.length, 'enumLit');
    return { k: 'enumLit', idx, ty };
  },
  /** `===` (both sides of the same eqable type). */
  seq(a: Expr, b: Expr): Expr {
    expectTy(b, a.ty, 'seq');
    check(eqable(a.ty), `=== on non-eqable type ${prettyTy(a.ty)}`);
    return E.prim(`(.seq ${showTy(a.ty)} rfl)`, [a, b], [a.ty, a.ty], T.bool);
  },
  not(a: Expr): Expr {
    if (a.k === 'lit' && a.ty.k === 'bool') return E.bool(!(a.js as boolean));
    return E.prim('.not', [a], [T.bool], T.bool);
  },
  bool(b: boolean): Expr { return E.lit(`(.bool ${b})`, T.bool, b); },
  undef(): Expr { return E.lit('.undef', T.undef); },
  nullLit(): Expr { return E.lit('.null', T.null); },
  /** An expression that panics ("non-null assertion on undefined"); used for branches
   * TypeScript proved unreachable. */
  unreachable(t: Ty): Expr { return E.unwrap(E.none(t)); },
  extern(name: string, args: Expr[], ret: Ty): Expr { return { k: 'extern', name, async: false, args, ty: ret }; },
  externAsync(name: string, args: Expr[], t: Ty): Expr { return { k: 'extern', name, async: true, args, ty: T.promise(t) }; },
  /** Coverage mode: the value of an expression that could not be translated (never
   * emitted; conversions and operations on it are not checked). */
  poison(t: Ty): Expr { return { k: 'lit', lean: '<poison>', ty: t, poison: true }; },
};

export function isPoison(e: Expr): boolean { return e.k === 'lit' && !!e.poison; }

export const S = {
  // (a one-field record whose value is discarded, e.g. a Node timer handle around setTimeout's
  // number: only its field is evaluated; Lean could not infer the field name of `.mkRec` there)
  expr(e: Expr): Stmt { return e.k === 'mkRec' && e.args.length === 1 ? S.expr(e.args[0]) : { k: 'expr', e }; },
  assign(v: VarInfo, e: Expr): Stmt {
    expectTy(e, v.ty, `assign ${v.name}`);
    v.assigned = true;
    return { k: 'assign', v, e };
  },
  gset(g: GlobalInfo, e: Expr): Stmt { expectTy(e, g.ty, `gset ${g.name}`); return { k: 'gset', g, e }; },
  setField(o: Expr, c: string, idx: number, fieldTy: Ty, e: Expr): Stmt {
    expectTy(o, T.obj(c), 'setField object');
    expectTy(e, fieldTy, 'setField value');
    return { k: 'setField', o, c, idx, e };
  },
  ite(c: Expr, t: Block, f: Block): Stmt { expectTy(c, T.bool, 'if'); return { k: 'ite', c, t, f }; },
  ret(e: Expr): Stmt { return { k: 'ret', e }; },
  throw(e: Expr): Stmt { expectTy(e, T.err, 'throw'); return { k: 'throw', e }; },
};

export function stmtItem(s: Stmt): Item { return { k: 'stmt', s }; }
export function declItem(v: VarInfo, init: Expr): Item {
  expectTy(init, v.ty, `decl ${v.name}`);
  return { k: 'decl', v, init };
}
export function awaitItem(v: VarInfo, init: Expr): Item {
  expectTy(init, T.promise(v.ty), `await ${v.name}`);
  return { k: 'await', v, init };
}

/** Is evaluating `e` free of effects and of reads of mutable state (so it can be moved
 * across other evaluations)? */
export function isStable(e: Expr): boolean {
  switch (e.k) {
    case 'lit': case 'none': case 'enumLit': case 'funVal': return true;
    case 'var': return !e.v.assigned && !e.v.mayChange;
    case 'some': return isStable(e.e);
    case 'inj': return isStable(e.e);
    case 'fold': return isStable(e.e);
    case 'mkTup': case 'mkRec': return e.args.every(isStable);
    case 'getTup': case 'getRec': case 'unfold': return isStable(e.e);
    case 'lam': return false;
    default: return false;
  }
}

/** Does the block end in a way that never completes normally (syntactically)? */
export function blockAlwaysAbrupt(b: Block): boolean {
  for (const it of b) {
    if (it.k === 'stmt' && stmtAlwaysAbrupt(it.s)) return true;
  }
  return false;
}

export function stmtAlwaysAbrupt(s: Stmt): boolean {
  switch (s.k) {
    case 'brk': case 'cont': case 'ret': case 'retP': case 'throw': return true;
    case 'ite': return blockAlwaysAbrupt(s.t) && blockAlwaysAbrupt(s.f);
    case 'block': return blockAlwaysAbrupt(s.b);
    case 'caseOptS': return blockAlwaysAbrupt(s.none) && blockAlwaysAbrupt(s.some);
    case 'caseUS': return s.alts.every(a => blockAlwaysAbrupt(a.body));
    default: return false;
  }
}

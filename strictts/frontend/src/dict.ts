// Objects used as dictionaries (`{ [k: string]: T }`, `Record<string, T>`): `.dict T` and the
// dict builtins of the semantics (ECMA-262 key order: array indices ascending, then the other
// keys in insertion order; reading an inherited `Object.prototype` property panics).
//   o[k], o.p           -> dictGet (opt T), unwrapped where TypeScript types the read as T
//   o[k] = v, o.p = v   -> dictSet          k in o -> dictHas      delete o[k] -> dictDelete
//   Object.keys/values/entries(o), Object.hasOwn(o, k), o.hasOwnProperty(k)
//   object literals typed as dictionaries -> dictNew, then dictSet per property (spreads of
//   dictionaries copy their entries in order)
import * as ts from 'typescript';
import { Ty, T, showTy, prettyTy, tyEq } from './ty';
import { Expr, E, S, Stmt, mkVar, stmtItem, isPoison } from './ir';
import { reject } from './diag';
import { Translator, FnCtx, strLit, isLibDecl } from './core';
import { skipParens } from './stmts';
import { defensiveContext, holdsUnknown } from './exprs';

const P = Translator.prototype;
export type DictTy = Extract<Ty, { k: 'dict' }>;

declare module './core' {
  interface Translator {
    /** A property key as a string (`o[k]`: string, string-literal union or number). */
    dictKey(k: ts.Expression, fc: FnCtx): Expr;
    /** `dictGet` with an optional value type flattened: `opt T`. */
    dictGetOpt(d: Expr, key: Expr): Expr;
    /** The read `o[k]` / `o.p` at `node`: optional where TypeScript's type is, or where the
     * program tests for a missing key (`?.`, `??`, `=== undefined`); otherwise unwrapped (a
     * panic for a missing key, as for array indices). */
    dictRead(d: Expr, key: Expr, node: ts.Expression, fc: FnCtx, exp?: Ty): Expr;
    dictSetStmt(d: Expr, key: Expr, v: Expr): Stmt;
    /** The IR type of `e` if it is a dictionary (without diagnostics otherwise). */
    dictTyOf(e: ts.Expression, fc: FnCtx): DictTy | undefined;
    /** `Object.keys/values/entries/hasOwn(o, …)` and `o.hasOwnProperty(k)` on a dictionary. */
    lowerDictCall(call: ts.CallExpression, fc: FnCtx): Expr | undefined;
    lowerDictLit(n: ts.ObjectLiteralExpression, t: DictTy, fc: FnCtx): Expr;
    /** `o[k] = v`, `o[k] op= v` on a dictionary. */
    dictAssign(d0: Expr, key: () => Expr, b: ts.BinaryExpression, cop: ts.SyntaxKind | undefined, needValue: boolean, fc: FnCtx): Expr | null;
  }
}

P.dictKey = function (this: Translator, k, fc) {
  const e = this.unfoldE(this.lowerExpr(k, fc));
  if (isPoison(e)) return E.poison(T.str);
  if (e.ty.k === 'str') return e;
  if (e.ty.k === 'enum' || e.ty.k === 'num') return this.toStr(e, k);
  reject(k, 'unsupported', `a property key of type ${prettyTy(e.ty)}`);
};

P.dictGetOpt = function (this: Translator, d, key) {
  const t = (d.ty as DictTy).t;
  const g = E.builtin(`(.dictGet ${showTy(t)})`, [d, key], [d.ty, T.str], T.opt(t));
  if (t.k !== 'opt') return g;
  const v = mkVar('x', t);
  return E.caseOpt(g, E.none(t.t), v, E.var(v));
};

P.dictRead = function (this: Translator, d, key, node, fc, exp) {
  const g = this.dictGetOpt(d, key);
  const want = this.tyAt(node, fc);
  // (an unknown value includes undefined: an absent key reads as undefined)
  if (want.k === 'opt' || want.k === 'dyn') return this.adapt(g, want, node);
  if (defensiveContext(node) || (exp && exp.k === 'opt')) return g;
  // (an unknown value narrowed to `{}` by `x !== undefined` stays unknown)
  if ((d.ty as DictTy).t.k === 'dyn' && holdsUnknown(want)) return E.unwrap(g);
  return this.adapt(E.unwrap(g), want, node);
};

P.dictSetStmt = function (this: Translator, d, key, v) {
  const t = (d.ty as DictTy).t;
  return S.expr(E.builtin(`(.dictSet ${showTy(t)})`, [d, key, v], [d.ty, T.str, t], T.undef));
};

P.dictTyOf = function (this: Translator, e, fc) {
  try {
    const t = this.unfoldTy(this.tyAt(e, fc));
    return t.k === 'dict' ? t : undefined;
  } catch { return undefined; }
};

P.lowerDictCall = function (this: Translator, call, fc) {
  const callee = skipParens(call.expression);
  if (!ts.isPropertyAccessExpression(callee) || callee.questionDotToken) return undefined;
  const name = callee.name.text;
  const args = call.arguments;
  const recv = skipParens(callee.expression);
  if (ts.isIdentifier(recv) && recv.text === 'Object' && ['keys', 'values', 'entries', 'hasOwn'].includes(name) && args.length >= 1) {
    const sym = this.symAt(recv);
    if (!sym || !isLibDecl(this.program, sym.declarations?.[0]) || ts.isSpreadElement(args[0])) return undefined;
    const dt = this.dictTyOf(args[0], fc);
    if (!dt) return undefined;
    const t = dt.t, st = showTy(t);
    if (name === 'hasOwn') {
      if (args.length !== 2) reject(call, 'unsupported-builtin', 'Object.hasOwn takes an object and a key');
      const [d, k] = this.seq([() => this.lowerExpr(args[0], fc, dt), () => this.dictKey(args[1], fc)], fc);
      return E.builtin(`(.dictHasOwn ${st})`, [d, k], [dt, T.str], T.bool);
    }
    if (args.length !== 1) reject(call, 'unsupported-builtin', `Object.${name} takes one object`);
    const d = this.lowerExpr(args[0], fc, dt);
    if (name === 'keys') return E.builtin(`(.dictKeys ${st})`, [d], [dt], T.arr(T.str));
    if (name === 'values') return E.builtin(`(.dictValues ${st})`, [d], [dt], T.arr(t));
    return E.builtin(`(.dictEntries ${st})`, [d], [dt], T.arr(T.tup([T.str, t])));
  }
  if (name === 'hasOwnProperty' && args.length === 1) {
    const dt = this.dictTyOf(recv, fc);
    if (!dt) return undefined;
    const [d, k] = this.seq([() => this.lowerExpr(recv, fc, dt), () => this.dictKey(args[0], fc)], fc);
    return E.builtin(`(.dictHasOwn ${showTy(dt.t)})`, [d, k], [dt, T.str], T.bool);
  }
  return undefined;
};

P.lowerDictLit = function (this: Translator, n, t, fc) {
  const d = E.var(this.bindTemp(E.builtin(`(.dictNew ${showTy(t.t)})`, [], [], t), fc, 'dict'));
  for (const p of n.properties) {
    if (ts.isPropertyAssignment(p) || ts.isShorthandPropertyAssignment(p)) {
      const key = p.name;
      let k: () => Expr;
      if (ts.isIdentifier(key) || ts.isStringLiteral(key) || ts.isNoSubstitutionTemplateLiteral(key)) k = () => strLit(key.text);
      else if (ts.isNumericLiteral(key)) k = () => strLit(String(Number(key.text)));
      else if (ts.isComputedPropertyName(key)) k = () => this.dictKey(key.expression, fc);
      else reject(p, 'unsupported-syntax', 'property name');
      const valNode = ts.isPropertyAssignment(p) ? p.initializer : p.name;
      const [kv, v] = this.seq([k, () => this.lowerExpr(valNode, fc, t.t)], fc);
      fc.pre.push(stmtItem(this.dictSetStmt(d, kv, v)));
    } else if (ts.isSpreadAssignment(p)) {
      // own entries in order (CopyDataProperties)
      const src = this.unfoldE(this.lowerExpr(p.expression, fc));
      if (src.ty.k !== 'dict' || !tyEq(src.ty.t, t.t)) reject(p, 'unsupported', `spread of ${prettyTy(src.ty)} into ${prettyTy(t)}`);
      const et = T.tup([T.str, t.t]);
      const ev = mkVar('e', et);
      const body = [stmtItem(this.dictSetStmt(d, E.getTup(E.var(ev), 0), E.getTup(E.var(ev), 1)))];
      fc.pre.push(stmtItem({ k: 'forOf', e: E.builtin(`(.dictEntries ${showTy(t.t)})`, [src], [t], T.arr(et)), v: ev, body }));
    } else reject(p, 'unsupported-syntax', 'methods and accessors in a dictionary literal');
  }
  return d;
};

P.dictAssign = function (this: Translator, d0, key, b, cop, needValue, fc) {
  const t = (d0.ty as DictTy).t;
  if (cop === undefined) {
    const [d, k, v] = this.seq([() => d0, key, () => this.lowerExpr(b.right, fc, t)], fc);
    const vv = needValue ? E.var(this.bindTemp(v, fc, 'dv')) : v;
    fc.pre.push(stmtItem(this.dictSetStmt(d, k, vv)));
    return needValue ? vv : null;
  }
  const [d1, k1] = this.seq([() => d0, key], fc);
  const d = this.spill(d1, fc, 'd'), k = this.spill(k1, fc, 'k');
  const [cur, r] = this.seq([() => this.dictRead(d, k, b.left, fc), () => this.lowerExpr(b.right, fc)], fc);
  let value = this.coerce(this.arith(cop, cur, r, b), t, b);
  if (needValue) value = E.var(this.bindTemp(value, fc, 'dv'));
  fc.pre.push(stmtItem(this.dictSetStmt(d, k, value)));
  return needValue ? value : null;
};

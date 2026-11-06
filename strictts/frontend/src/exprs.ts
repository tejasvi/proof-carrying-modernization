// Expression lowering.
import * as ts from 'typescript';
import { Ty, T, tyEq, prettyTy, showTy, isObjectLike, eqable, sortFields, REGEXP_TY } from './ty';
import { Expr, Item, Block, VarInfo, E, S, mkVar, declItem, stmtItem, awaitItem, isStable, InternalError, isPoison } from './ir';
import { reject } from './diag';
import { Translator, FnCtx, Binding, numLit, bigLit, strLit, isLitUndef, isLibDecl, holdsTimer } from './core';
import { skipParens } from './stmts';

declare module './core' {
  interface Translator {
    lowerExpr(n: ts.Expression, fc: FnCtx, exp?: Ty): Expr;
    lowerRaw(n: ts.Expression, fc: FnCtx, exp?: Ty): Expr;
    lowerCond(n: ts.Expression, fc: FnCtx): Expr;
    truthy(e: Expr, node: ts.Node): Expr;
    lowerIdent(id: ts.Identifier, fc: FnCtx, exp?: Ty): Expr;
    /** A stored value read at a place where TypeScript may have narrowed its type: when the
     * consumer accepts the stored type, no narrowing is done (TypeScript's narrowing of
     * property paths survives calls that may invalidate it); otherwise adapt to the
     * narrowed type. */
    narrowedRead(stored: Expr, node: ts.Node, fc: FnCtx, exp?: Ty): Expr;
    lowerThis(n: ts.Node, fc: FnCtx): Expr;
    lowerAssign(b: ts.BinaryExpression, fc: FnCtx, needValue: boolean, forceEq?: boolean): Expr | null;
    lowerUpdate(u: ts.PrefixUnaryExpression | ts.PostfixUnaryExpression, fc: FnCtx, needValue: boolean): Expr | null;
    lowerAwaitOperand(a: ts.AwaitExpression, fc: FnCtx): Expr;
    readField(base: Expr, name: string, node: ts.Node): Expr;
    memberOf(base: Expr, name: string, node: ts.Node, fc: FnCtx): Expr;
    strictEqExprs(a: Expr, b: Expr, node: ts.Node, fc: FnCtx): Expr;
    toStr(e: Expr, node: ts.Node): Expr;
    arith(op: ts.SyntaxKind, a: Expr, b: Expr, node: ts.Node): Expr;
    lowerOptChain(n: ts.Expression, fc: FnCtx, exp?: Ty): Expr;
    nullishToOpt(e: Expr, node: ts.Node): Expr;
    lowerArrayLit(n: ts.ArrayLiteralExpression, fc: FnCtx, exp?: Ty): Expr;
    lowerObjectLit(n: ts.ObjectLiteralExpression, fc: FnCtx, exp?: Ty): Expr;
    assignTo(b: Binding, value: Expr, needValue: boolean, fc: FnCtx, node: ts.Node): Expr | null;
    classOfObj(c: string): { fields: { name: string; ty: Ty }[]; fieldIdx: Map<string, number> } | undefined;
    lowerCallArgs(specs: ParamSpec[], args: readonly ts.Expression[], fc: FnCtx, node: ts.Node, prefix: (() => Expr)[]): Expr[];
  }
}

export interface ParamSpec { ty: Ty; optional: boolean; rest: boolean }

const P = Translator.prototype;
const SK = ts.SyntaxKind;

P.lowerExpr = function (this: Translator, n, fc, exp) {
  if (exp && exp.k === 'dyn' && !(this.checker.getTypeAtLocation(n).flags & ts.TypeFlags.Any)) {
    // a value used as unknown: lowered at its own type, then kept with that type (an `any`
    // value, e.g. from `JSON.parse`, takes the expected type instead)
    const e = this.lowerExpr(n, fc);
    return isPoison(e) ? E.poison(T.dyn) : this.adapt(e, T.dyn, n);
  }
  if (!this.coverage) return lowerExpr0(this, n, fc, exp);
  // coverage mode: record the violation and continue with a placeholder value (a violation
  // inside an expression whose sub-expression already failed is a consequence, not recorded)
  const mark = this.poisonCount;
  try {
    return lowerExpr0(this, n, fc, exp);
  } catch (e) {
    if (isFatal(e)) throw e;
    if (this.poisonCount === mark) this.covRecord(e, n);
    return this.poisonFor(n, fc, exp);
  }
};

export function isFatal(e: unknown): boolean {
  return !(e instanceof Error) || (e instanceof RangeError && /call stack/.test(e.message));
}

declare module './core' {
  interface Translator {
    /** A placeholder derived from an untranslatable value (no new violation). */
    derivedPoison(n: ts.Node, fc: FnCtx, exp?: Ty): Expr;
  }
}

P.derivedPoison = function (this: Translator, n, fc, exp) {
  if (exp) return E.poison(exp);
  try { return E.poison(this.tyAt(n, fc)); } catch { return E.poison(T.undef); }
};

function lowerExpr0(tr: Translator, n: ts.Expression, fc: FnCtx, exp?: Ty): Expr {
  return lowerExprImpl.call(tr, n, fc, exp);
}

const lowerExprImpl = function (this: Translator, n: ts.Expression, fc: FnCtx, exp?: Ty): Expr {
  const ov = fc.override.get(n);
  if (ov) return exp ? this.coerce(ov, exp, n) : ov;
  const e = this.lowerRaw(n, fc, exp);
  if (!exp || tyEq(e.ty, exp)) return e;
  const tsT = this.checker.getTypeAtLocation(n);
  if (this.isNeverType(tsT)) return this.withValue(e, 'nv', () => E.unreachable(exp));
  // a string expression TypeScript types as one literal (e.g. a field of an `as const`
  // object) flowing into a literal union
  const target = exp.k === 'opt' ? exp.t : exp;
  if (target.k === 'enum' && this.unfoldTy(e.ty).k === 'str' && (tsT.flags & ts.TypeFlags.StringLiteral) &&
      target.cases.includes((tsT as ts.StringLiteralType).value)) {
    const lit = E.enumLit(target, target.cases.indexOf((tsT as ts.StringLiteralType).value));
    return this.coerce(this.withValue(e, 'k', () => lit), exp, n);
  }
  return this.coerce(e, exp, n);
};

function chainRoot(n: ts.Node): ts.Node | undefined {
  let cur: ts.Node = n;
  while (true) {
    if ((ts.isPropertyAccessExpression(cur) || ts.isElementAccessExpression(cur) || ts.isCallExpression(cur)) && cur.questionDotToken) return cur;
    if (ts.isPropertyAccessExpression(cur) || ts.isElementAccessExpression(cur) || ts.isCallExpression(cur) || ts.isNonNullExpression(cur)) {
      if (!ts.isOptionalChain(cur) && !ts.isNonNullExpression(cur)) return undefined;
      cur = cur.expression;
      continue;
    }
    return undefined;
  }
}

function needsChain(fc: FnCtx, n: ts.Node): boolean {
  if (!ts.isOptionalChain(n)) return false;
  const root = chainRoot(n) as ts.PropertyAccessExpression | undefined;
  return !!root && !fc.override.has(root.expression);
}

P.lowerRaw = function (this: Translator, n, fc, exp) {
  switch (n.kind) {
    case SK.NumericLiteral: return numLit(Number((n as ts.NumericLiteral).text.replace(/_/g, '')));
    case SK.BigIntLiteral: return bigLit(BigInt((n as ts.BigIntLiteral).text.slice(0, -1).replace(/_/g, '')));
    case SK.StringLiteral:
    case SK.NoSubstitutionTemplateLiteral: return strLit((n as ts.StringLiteral).text);
    case SK.TemplateExpression: return lowerTemplate(this, n as ts.TemplateExpression, fc);
    case SK.TrueKeyword: return E.bool(true);
    case SK.FalseKeyword: return E.bool(false);
    case SK.NullKeyword: return E.nullLit();
    case SK.Identifier: return this.lowerIdent(n as ts.Identifier, fc, exp);
    case SK.ThisKeyword: return this.lowerThis(n, fc);
    case SK.ParenthesizedExpression: return this.lowerExpr((n as ts.ParenthesizedExpression).expression, fc, exp);
    case SK.PropertyAccessExpression: {
      if (needsChain(fc, n)) return this.lowerOptChain(n, fc, exp);
      const pa = n as ts.PropertyAccessExpression;
      const st = this.lowerStaticMember(pa, fc);
      if (st) return st;
      if (this.isNamespaceRef(pa.expression)) return this.lowerIdentLike(pa, fc, exp);
      {
        const bs = this.resolveSym(this.checker.getSymbolAtLocation(skipParens(pa.expression)));
        const ps = this.resolveSym(this.checker.getSymbolAtLocation(pa.name));
        const staticBase = bs && (bs.flags & (ts.SymbolFlags.ValueModule | ts.SymbolFlags.NamespaceModule | ts.SymbolFlags.Class)) &&
          !(bs.flags & ts.SymbolFlags.Variable) && !(ts.isIdentifier(skipParens(pa.expression)) && this.lookup(bs, fc)) &&
          !(bs.declarations ?? []).some(d => this.isProjectDecl(d));
        if (staticBase && ps && !(ps.flags & (ts.SymbolFlags.ValueModule | ts.SymbolFlags.NamespaceModule | ts.SymbolFlags.Class))) {
          // `StyleSheet.hairlineWidth`, `admin.firestore.FieldValue` members: static values
          const name = this.externMemberName(ps, true);
          if (this.coverage) this.covExternals.add(name);
          return this.externResult(name, [], exp ?? this.tyAt(pa, fc), pa);
        }
      }
      const first = firstIterated(this, pa, fc);
      if (first) return this.adapt(first, exp ?? this.tyAt(pa, fc), pa);
      const base = this.lowerExpr(pa.expression, fc);
      if (isPoison(base)) return this.derivedPoison(pa, fc, exp);
      if (base.ty.k === 'ext') {
        // a property of an external object: answered by the oracle
        const pt = exp ?? this.tyAt(pa, fc);
        if (this.coverage) this.covExternals.add(`${base.ty.name}.get:${pa.name.text}`);
        return this.externResult(`${base.ty.name}.get:${pa.name.text}`, [base], pt, pa);
      }
      const e = this.memberOf(base, pa.name.text, pa, fc);
      // (a dictionary read is already at its type, optional where the program tests for absence)
      if (this.unfoldTy(base.ty).k === 'dict') return e;
      // members of library-typed values TypeScript types as `any` (a rejection reason `e`)
      if (this.checker.getTypeAtLocation(pa).flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown) && this.unfoldTy(base.ty).k === 'err') return e;
      return this.narrowedRead(e, pa, fc, exp);
    }
    case SK.ElementAccessExpression: {
      if (needsChain(fc, n)) return this.lowerOptChain(n, fc, exp);
      return lowerElemAccess(this, n as ts.ElementAccessExpression, fc, exp);
    }
    case SK.CallExpression: {
      if (needsChain(fc, n)) return this.lowerOptChain(n, fc, exp);
      return this.lowerCall(n as ts.CallExpression, fc, exp);
    }
    case SK.NewExpression: return this.lowerNew(n as ts.NewExpression, fc, exp);
    case SK.PrefixUnaryExpression: return lowerPrefix(this, n as ts.PrefixUnaryExpression, fc);
    case SK.PostfixUnaryExpression: return this.lowerUpdate(n as ts.PostfixUnaryExpression, fc, true)!;
    case SK.BinaryExpression: return lowerBinary(this, n as ts.BinaryExpression, fc, exp);
    case SK.ConditionalExpression: return lowerConditional(this, n as ts.ConditionalExpression, fc, exp);
    case SK.ArrowFunction:
    case SK.FunctionExpression: return this.lowerLambda(n as ts.ArrowFunction, fc, exp);
    case SK.AwaitExpression: {
      const p = this.lowerAwaitOperand(n as ts.AwaitExpression, fc);
      const v = mkVar('aw', (p.ty as Extract<Ty, { k: 'promise' }>).t);
      fc.pre.push(awaitItem(v, p));
      return E.var(v);
    }
    case SK.NonNullExpression: {
      if (needsChain(fc, n)) return this.lowerOptChain(n, fc, exp);
      const inner = this.lowerExpr((n as ts.NonNullExpression).expression, fc);
      return this.adapt(inner, this.tyAt(n, fc), n);
    }
    case SK.AsExpression:
    case SK.TypeAssertionExpression:
    case SK.SatisfiesExpression: return lowerAssertion(this, n as ts.AsExpression, fc);
    case SK.ArrayLiteralExpression: return this.lowerArrayLit(n as ts.ArrayLiteralExpression, fc, exp);
    case SK.ObjectLiteralExpression: return this.lowerObjectLit(n as ts.ObjectLiteralExpression, fc, exp);
    case SK.VoidExpression: {
      const inner = (n as ts.VoidExpression).expression;
      if (!ts.isNumericLiteral(skipParens(inner))) this.lowerExprStmt(inner, fc, fc.pre);
      return E.undef();
    }
    case SK.TypeOfExpression: {
      if (this.strict) reject(n, 'unsupported', '`typeof` is only supported in comparisons that narrow a variable');
      // `typeof x` as a value: on the runtime value
      let x = this.unfoldE(this.lowerExpr((n as ts.TypeOfExpression).expression, fc));
      if (isPoison(x)) return E.poison(T.str);
      // (a function or object compared by identity: the closure or record in its cell)
      if (x.ty.k === 'box' && x.ty.t.k === 'fn') x = this.unboxFn(x);
      else if (x.ty.k === 'box' && x.ty.t.k === 'record') x = this.unboxCell(x);
      const d = x.ty.k === 'dyn' ? x : E.prim(`(.toDyn ${showTy(x.ty)})`, [x], [x.ty], T.dyn);
      // (TypeScript types the result as the union of the typeof strings)
      return this.adapt(E.prim('.dynTypeof', [d], [T.dyn], T.str), exp ?? this.tyAt(n, fc), n);
    }
    // a regex as a value: the record of its flags and source (regex.ts)
    case SK.RegularExpressionLiteral: return this.regexValue(this.regexLit(n as ts.Expression)!);
    case SK.DeleteExpression: {
      const x = skipParens((n as ts.DeleteExpression).expression);
      const dt = (ts.isElementAccessExpression(x) || ts.isPropertyAccessExpression(x)) ? this.dictTyOf(x.expression, fc) : undefined;
      if (!dt) reject(n, 'no-delete', '`delete` is only supported on dictionary entries');
      const xa = x as ts.ElementAccessExpression | ts.PropertyAccessExpression;
      const [d, k] = this.seq([() => this.lowerExpr(xa.expression, fc, dt),
        () => ts.isPropertyAccessExpression(xa) ? strLit(xa.name.text) : this.dictKey(xa.argumentExpression, fc)], fc);
      return E.builtin(`(.dictDelete ${showTy(dt.t)})`, [d, k], [dt, T.str], T.bool);
    }
    case SK.YieldExpression: reject(n, 'no-generators', 'generators are not allowed');
    case SK.TaggedTemplateExpression: return lowerTaggedTemplate(this, n as ts.TaggedTemplateExpression, fc);
    case SK.ClassExpression: reject(n, 'unsupported-syntax', 'class expressions');
    case SK.SpreadElement: reject(n, 'unsupported-syntax', 'spread in this position');
    case SK.JsxElement: case SK.JsxSelfClosingElement: case SK.JsxFragment: reject(n, 'jsx', 'JSX is not supported');
    case SK.SuperKeyword: reject(n, 'no-extends', '`super` (classes cannot extend)');
    case SK.MetaProperty: reject(n, 'unsupported-syntax', '`new.target` / `import.meta`');
    default: reject(n, 'unsupported-syntax', `expression kind ${SK[n.kind]}`);
  }
};

// ---------------------------------------------------------------------------------------
// identifiers, this

/** `m.keys().next().value` (also `values()` / `entries()`, and of a Set): the first element of
 * the collection in insertion order, or undefined (e.g. the oldest key of a bounded cache). */
function firstIterated(tr: Translator, pa: ts.PropertyAccessExpression, fc: FnCtx): Expr | undefined {
  if (pa.name.text !== 'value') return undefined;
  const next = skipParens(pa.expression);
  if (!ts.isCallExpression(next) || next.arguments.length || !ts.isPropertyAccessExpression(next.expression) ||
      next.expression.questionDotToken || next.expression.name.text !== 'next') return undefined;
  const it = skipParens(next.expression.expression);
  if (!ts.isCallExpression(it) || it.arguments.length || !ts.isPropertyAccessExpression(it.expression) || it.expression.questionDotToken) return undefined;
  const method = it.expression.name.text;
  if (method !== 'keys' && method !== 'values' && method !== 'entries') return undefined;
  let ct: Ty;
  try { ct = tr.unfoldTy(tr.tyAt(it.expression.expression, fc)); } catch { return undefined; }
  if (ct.k !== 'map' && !(ct.k === 'set' && method !== 'entries')) return undefined;
  const arr = tr.collectionSnapshot(tr.lowerExpr(it.expression.expression, fc), method, it);
  const el = (arr.ty as Extract<Ty, { k: 'arr' }>).t;
  return E.builtin(`(.arrGetOpt ${showTy(el)})`, [arr, numLit(0)], [arr.ty, T.num], T.opt(el));
}

/** Does a narrowed type of an unknown value still hold unknown values (`{}`, `{} | null`,
 * `unknown[]`, …)? Such a value stays unknown. */
export function holdsUnknown(t: Ty): boolean {
  return t.k === 'dyn' || (t.k === 'record' && t.fs.length === 0) ||
    ((t.k === 'arr' || t.k === 'dict' || t.k === 'opt') && holdsUnknown(t.t)) ||
    (t.k === 'union' && t.ts.every(m => m.k === 'null' || holdsUnknown(m)));
}

P.narrowedRead = function (this: Translator, stored, node, fc, exp) {
  if (exp) {
    const direct = this.convert(stored, exp, node, false, 0);
    if (direct) return direct;
  }
  // TypeScript narrowed the read to `never`: unreachable code, keep the stored value
  if (this.isNeverType(this.checker.getTypeAtLocation(node))) return exp ? this.withValue(stored, 'nv', () => E.unreachable(exp)) : stored;
  if (stored.ty.k === 'dyn' || (stored.ty.k === 'opt' && stored.ty.t.k === 'dyn')) {
    // an `unknown` value narrowed to a type without IR representation (`object`,
    // `object & Record<"k", unknown>` after `"k" in x`) stays unknown
    let nt: Ty;
    try { nt = this.tyAt(node, fc); } catch (e) { if (isFatal(e)) throw e; return stored; }
    // narrowed to a type that still holds unknown values (`any[]` after Array.isArray, `{}` and
    // `{} | null` after `x !== undefined` / `x !== null`, which hold strings and numbers too):
    // keep the value as unknown (its reads go through the runtime value; no copy, no cast)
    if (stored.ty.k === 'dyn' && holdsUnknown(nt)) return stored;
    // (an optional unknown value, e.g. an optional field, narrowed so: TypeScript excluded undefined)
    if (stored.ty.k === 'opt' && nt.k !== 'dyn' && nt.k !== 'opt' && holdsUnknown(nt)) return E.unwrap(stored);
    return this.adapt(stored, nt, node);
  }
  const t = this.tyAt(node, fc);
  if (!exp && ts.isOptionalChain(node) && t.k === 'opt' && stored.ty.k !== 'opt') {
    // inside an optional chain TypeScript adds `undefined` for the short-circuit; the
    // value itself is defined here
    const c = this.convert(stored, t.t, node, true, 0);
    if (c) return c;
  }
  return this.adapt(stored, t, node);
};

declare module './core' {
  interface Translator {
    /** A host global (`process`, `window`) or package value read as a nullary extern. */
    externalValue(sym: ts.Symbol, id: ts.Identifier, fc: FnCtx, exp?: Ty): Expr;
  }
}

P.externalValue = function (this: Translator, sym, id, fc, exp) {
  if (sym.flags & (ts.SymbolFlags.Function | ts.SymbolFlags.Method)) reject(id, 'external-call', `the external function ${id.text} used as a value`);
  if (sym.flags & (ts.SymbolFlags.ValueModule | ts.SymbolFlags.NamespaceModule)) reject(id, 'external-call', `the module ${id.text} used as a value`);
  const name = this.externMemberName(sym, false);
  if (this.coverage) this.covExternals.add(name);
  return this.externResult(name, [], exp ?? this.tyAt(id, fc), id);
};

declare module './core' {
  interface Translator {
    /** Is `e` an `import * as m` namespace? */
    isNamespaceRef(e: ts.Expression): boolean;
    /** A reference through a namespace import (`m.f`, `m.x`), resolved like an identifier. */
    lowerIdentLike(n: ts.PropertyAccessExpression, fc: FnCtx, exp?: Ty): Expr;
  }
}

P.isNamespaceRef = function (this: Translator, e) {
  const x = skipParens(e);
  if (!ts.isIdentifier(x)) return false;
  const sym = this.resolveSym(this.checker.getSymbolAtLocation(x));
  return !!sym && !!(sym.flags & ts.SymbolFlags.ValueModule) && !isLibDecl(this.program, sym.declarations?.[0]);
};

P.lowerIdentLike = function (this: Translator, n, fc, exp) {
  const sym = this.resolveSym(this.checker.getSymbolAtLocation(n));
  if (!sym) reject(n, 'unsupported', `unknown export ${n.name.text}`);
  const b = this.lookup(sym, fc);
  if (b) return this.narrowedRead(this.readBinding(b, n), n, fc, exp);
  const fd = this.topFunDecl(sym);
  if (fd && !fd.typeParameters?.length) return this.adapt(E.funVal(this.funInfoFor(fd, new Map(), n)), this.tyAt(n, fc), n);
  reject(n, 'unsupported', `export ${n.name.text} is not supported here`);
};

P.lowerIdent = function (this: Translator, id, fc, exp) {
  const raw = this.checker.getSymbolAtLocation(id);
  const sym = this.symAt(id);
  const libSym = !sym || !sym.declarations?.length || isLibDecl(this.program, sym.declarations[0]);
  if (libSym) {
    if (id.text === 'undefined') return E.undef();
    if (id.text === 'NaN') return numLit(NaN);
    if (id.text === 'Infinity') return numLit(Infinity);
    if (sym && !['String', 'Number', 'Boolean', 'BigInt', 'Math', 'console', 'parseInt', 'parseFloat', 'isNaN', 'isFinite'].includes(id.text)) {
      return this.externalValue(sym, id, fc, exp);
    }
    reject(id, 'unsupported-builtin', `${id.text} is not supported as a value`);
  }
  if (sym && !this.lookup(sym, fc) && sym.declarations?.length && !sym.declarations.some(d => this.isProjectDecl(d))) {
    // a value imported from a package
    return this.externalValue(sym, id, fc, exp);
  }
  void raw;
  const vd = sym?.valueDeclaration;
  if (vd && ts.isVariableDeclaration(vd) && this.isRegexConst(vd)) return this.adapt(this.regexValue(this.regexLit(id)!), exp ?? this.tyAt(id, fc), id);
  const b = this.lookup(sym!, fc);
  if (b) {
    if (b.k === 'lifted') {
      const want = this.tyAt(id, fc);
      if (want.k === 'box') {
        // its one cell, created at its declaration
        if (!b.cell) reject(id, 'fn-identity', `the nested function ${id.text} used as a value compared by identity before its declaration`);
        return E.var(b.cell);
      }
      return this.liftedAsValue(b, id, fc);
    }
    const e = this.readBinding(b, id);
    if (b.k === 'var' && b.holes && !this.holeWrites.has(id)) {
      // an array from `new Array(n)`: holes would be observable unless its length reached n
      const at = b.v.ty as Extract<Ty, { k: 'arr' }>;
      const len = mkVar('len', T.num);
      fc.pre.push(declItem(len, E.builtin(`(.arrLength ${showTy(at.t)})`, [e], [at], T.num)));
      const short = E.prim('(.numCmp .lt)', [E.var(len), E.var(b.holes)], [T.num, T.num], T.bool);
      fc.pre.push(stmtItem(S.ite(short, [declItem(mkVar('holes', T.undef), E.unreachable(T.undef))], [])));
    }
    if (b.k === 'var' && (b.errVar || b.fixed)) return e;
    return this.narrowedRead(e, id, fc, exp);
  }
  const fd = this.topFunDecl(sym!);
  if (fd) {
    if (fd.typeParameters?.length) reject(id, 'unsupported-generic', 'generic functions can only be called directly');
    const f = this.funInfoFor(fd, new Map(), id);
    const want = this.tyAt(id, fc);
    // a top-level function compared by identity: its one cell, created when the module starts
    if (want.k === 'box' && want.t.k === 'fn') return this.adapt(E.gget(this.fnBox(f)), want, id);
    return this.adapt(E.funVal(f), want, id);
  }
  if (sym!.flags & ts.SymbolFlags.Class) reject(id, 'unsupported', 'classes cannot be used as values');
  reject(id, 'later-declared', `\`${id.text}\` is used before its declaration (e.g. by a closure created earlier)`);
};

P.lowerThis = function (this: Translator, n, fc) {
  for (let c: FnCtx | null = fc; c; c = c.parent) {
    if (c.thisPoison) return this.derivedPoison(n, fc);
    if (c.thisVar) return E.var(c.thisVar);
    if (c.kind !== 'lambda' || ts.isFunctionExpression(c.tsNode)) break;
  }
  reject(n, 'no-this', '`this` is only allowed in class methods and constructors');
};

// ---------------------------------------------------------------------------------------
// members

P.classOfObj = function (this: Translator, c) {
  const ci = this.types.classes.get(c);
  if (ci) return ci;
  return this.types.mutStructs.find(m => m.name === c);
};

P.readField = function (this: Translator, base, name, node) {
  const c = (base.ty as Extract<Ty, { k: 'obj' }>).c;
  const info = this.classOfObj(c);
  if (!info) throw new InternalError(`unknown class ${c}`);
  const i = info.fieldIdx.get(name);
  if (i !== undefined) return E.getField(base, c, i, info.fields[i].ty);
  const ci = this.types.classes.get(c);
  if (ci) {
    const getter = this.classMember(ci, name, 'getter', node);
    if (getter) return E.call(getter, [base]);
    const m = this.classMember(ci, name, 'method', node);
    if (m) reject(node, 'unsupported', `method ${name} used as a value (call it, or wrap it in an arrow function)`);
  }
  reject(node, 'unsupported', `no field ${name} on ${c}`);
};

P.memberOf = function (this: Translator, base0, name, node, fc) {
  if (isPoison(base0)) return this.derivedPoison(node, fc);
  const base = this.unfoldE(base0);
  const t = base.ty;
  if (t.k === 'box' && t.t.k === 'record') return this.memberOf(this.unboxCell(base), name, node, fc);
  if (tyEq(t, REGEXP_TY)) {
    // a regex value: its flags as booleans; its lastIndex (state) is not modelled
    if (name === 'lastIndex') reject(node, 'no-regexp', 'lastIndex of a regular expression (its matching state) is not modelled');
    const FLAG: Record<string, string> = { global: 'g', ignoreCase: 'i', multiline: 'm', dotAll: 's', unicode: 'u', unicodeSets: 'v', sticky: 'y', hasIndices: 'd' };
    if (Object.hasOwn(FLAG, name)) return this.withValue(base, 're', x => E.prim('.strIncludes', [E.getRec(x, 0), strLit(FLAG[name]), numLit(0)], [T.str, T.str, T.num], T.bool));
  }
  if (t.k === 'ext') {
    if (this.coverage) this.covExternals.add(`${t.name}.get:${name}`);
    return this.externResult(`${t.name}.get:${name}`, [base], this.tyAt(node, fc), node);
  }
  if (t.k === 'union') {
    // a property every member has (e.g. the discriminant): case split
    const target = this.tyAt(node, fc);
    return E.caseU(base, t.ts.map(m => {
      const v = mkVar('m', m);
      return { v, body: this.adapt(this.memberOf(E.var(v), name, node, fc), target, node) };
    }));
  }
  switch (t.k) {
    case 'dyn': return E.builtin('.dynGet', [base, strLit(name)], [T.dyn, T.str], T.dyn);
    case 'dict': return this.dictRead(base, strLit(name), node as ts.Expression, fc);
    case 'record': {
      const i = t.fs.findIndex(f => f.name === name);
      if (i < 0) reject(node, 'unsupported', `no field ${name}`);
      return E.getRec(base, i);
    }
    case 'obj': return this.readField(base, name, node);
    case 'arr':
      if (name === 'length') return E.builtin(`(.arrLength ${showTy(t.t)})`, [base], [t], T.num);
      break;
    case 'tarr':
      if (name === 'length') return E.builtin(`(.taLength .${t.kind})`, [base], [t], T.num);
      break;
    case 'str':
      if (name === 'length') return E.prim('.strLength', [base], [T.str], T.num);
      break;
    case 'enum':
      if (name === 'length') return E.prim('.strLength', [this.toStr(base, node)], [T.str], T.num);
      break;
    case 'tup':
      if (name === 'length') return this.withValue(base, 'p', () => numLit(t.ts.length));
      break;
    case 'map':
      if (name === 'size') return E.builtin(`(.mapSize ${showTy(t.key)} ${showTy(t.val)})`, [base], [t], T.num);
      break;
    case 'set':
      if (name === 'size') return E.builtin(`(.setSize ${showTy(t.t)})`, [base], [t], T.num);
      break;
    case 'err':
      if (name === 'message') return E.prim('.errMessage', [base], [T.err], T.str);
      if (name === 'name') return E.prim('.errName', [base], [T.err], T.str);
      if (name === 'stack' || name === 'cause') reject(node, 'unsupported', `Error.${name} is not supported`);
      break;
  }
  reject(node, 'unsupported', `property ${name} of ${prettyTy(t)} is not supported`);
};

function lowerElemAccess(tr: Translator, ea: ts.ElementAccessExpression, fc: FnCtx, exp?: Ty): Expr {
  const arg = skipParens(ea.argumentExpression);
  let b0 = tr.unfoldE(tr.lowerExpr(ea.expression, fc));
  if (b0.ty.k === 'box' && b0.ty.t.k === 'record') b0 = tr.unboxCell(b0);
  if (isPoison(b0)) { tr.lowerExpr(ea.argumentExpression, fc); return tr.derivedPoison(ea, fc, exp); }
  const bt = b0.ty;
  if (bt.k === 'tup' && ts.isNumericLiteral(arg)) return tr.narrowedRead(E.getTup(b0, Number(arg.text)), ea, fc);
  if (bt.k === 'tup') {
    // a computed index into a homogeneous tuple (e.g. an `as const` list): index an array of
    // its elements
    if (bt.ts.length === 0 || !bt.ts.every(x => tyEq(x, bt.ts[0]))) reject(arg, 'unsupported', 'computed index into a tuple with elements of different types');
    const el = bt.ts[0];
    const at = T.arr(el) as Extract<Ty, { k: 'arr' }>;
    const arr = tr.withValue(b0, 'p', x => E.builtin(`(.arrOf ${showTy(el)} ${bt.ts.length})`, bt.ts.map((_, i) => E.getTup(x, i)), bt.ts.map(() => el), at));
    const [a, i] = tr.seq([() => arr, () => tr.lowerExpr(ea.argumentExpression, fc, T.num)], fc);
    const want = tr.tyAt(ea, fc);
    const e = want.k === 'opt' || defensiveContext(ea) || (exp && exp.k === 'opt')
      ? E.builtin(`(.arrGetOpt ${showTy(el)})`, [a, i], [at, T.num], T.opt(el))
      : E.builtin(`(.arrGet ${showTy(el)})`, [a, i], [at, T.num], el);
    return e.ty.k === 'opt' && want.k !== 'opt' && (defensiveContext(ea) || (exp && exp.k === 'opt')) ? e : tr.adapt(e, want, ea);
  }
  if (bt.k === 'dict') {
    const [d, k] = tr.seq([() => b0, () => tr.dictKey(ea.argumentExpression, fc)], fc);
    return tr.dictRead(d, k, ea, fc, exp);
  }
  if (bt.k === 'dyn') {
    const [d, k] = tr.seq([() => b0, () => tr.dictKey(ea.argumentExpression, fc)], fc);
    return tr.narrowedRead(E.builtin('.dynGet', [d, k], [T.dyn, T.str], T.dyn), ea, fc, exp);
  }
  if (bt.k === 'record' || bt.k === 'obj') {
    if (!ts.isStringLiteral(arg)) {
      // a key of a string-literal union whose cases are all properties (`labels[lang]`): a case
      // split on the key
      const names = bt.k === 'record' ? bt.fs.map(f => f.name) : (tr.classOfObj(bt.c)?.fields ?? []).map(f => f.name);
      const kt = tr.unfoldTy(tr.tyAt(ea.argumentExpression, fc));
      if (kt.k !== 'enum' || !kt.cases.every(c => names.includes(c))) reject(arg, 'computed-key', `computed property access on ${prettyTy(bt)}`);
      const [o, k] = tr.seq([() => b0, () => tr.lowerExpr(ea.argumentExpression, fc, kt)], fc);
      const want = exp ?? tr.tyAt(ea, fc);
      return tr.withValue(o, 'o', ov => tr.withValue(k, 'k', kv => {
        let acc: Expr = E.unreachable(want);
        for (let i = kt.cases.length - 1; i >= 0; i--) {
          acc = E.cond(E.seq(kv, E.enumLit(kt, i)), tr.adapt(tr.memberOf(ov, kt.cases[i], ea, fc), want, ea), acc);
        }
        return acc;
      }));
    }
    return tr.narrowedRead(tr.memberOf(b0, arg.text, ea, fc), ea, fc);
  }
  if (bt.k === 'ext') {
    // an element of an external object (`buf[i]`)
    const [o, k] = tr.seq([() => b0, () => tr.lowerExpr(ea.argumentExpression, fc)], fc);
    const want = exp ?? tr.tyAt(ea, fc);
    if ((bt.name === 'RegExpMatchArray' || bt.name === 'RegExpExecArray') && want.k === 'str') {
      // a capture group that did not participate is undefined, though TypeScript types it string
      return E.unwrap(E.extern(`${bt.name}.get:[]`, [o, k], T.opt(T.str)));
    }
    return tr.externResult(`${bt.name}.get:[]`, [o, k], want, ea);
  }
  const [base, idx] = tr.seq([() => b0, () => tr.lowerExpr(ea.argumentExpression, fc, T.num)], fc);
  let want = tr.tyAt(ea, fc);
  if (ts.isOptionalChain(ea) && want.k === 'opt' && base.ty.k === 'arr' && base.ty.t.k !== 'opt') want = want.t;
  // `a[i]?.x`, `a[i] ?? d`, `a[i] === undefined`: the program handles a missing element, so
  // read it as optional (JavaScript yields undefined; TypeScript's type omits it)
  if ((defensiveContext(ea) || (exp && exp.k === 'opt')) && want.k !== 'opt' && (base.ty.k === 'arr' || base.ty.k === 'str')) {
    if (base.ty.k === 'arr') return E.builtin(`(.arrGetOpt ${showTy(base.ty.t)})`, [base, idx], [base.ty, T.num], T.opt(base.ty.t));
    return strIndex(tr, base, idx);
  }
  const t = base.ty;
  if (t.k === 'arr') {
    const e = want.k === 'opt' && t.t.k !== 'opt'
      ? E.builtin(`(.arrGetOpt ${showTy(t.t)})`, [base, idx], [t, T.num], T.opt(t.t))
      : E.builtin(`(.arrGet ${showTy(t.t)})`, [base, idx], [t, T.num], t.t);
    return tr.adapt(e, want, ea);
  }
  if (t.k === 'str') return tr.adapt(strIndex(tr, base, idx), want, ea);
  if (t.k === 'tarr') {
    return tr.adapt(E.builtin(`(.taGet .${t.kind})`, [base, idx], [t, T.num], t.kind === 'bi64' || t.kind === 'bu64' ? T.bigint : T.num), want, ea);
  }
  reject(ea, 'unsupported', `indexing a value of type ${prettyTy(t)}`);
}

/** Is the value of `n` immediately tested for undefined (`?.`, `??`, `=== undefined`)? */
export function defensiveContext(n: ts.Node): boolean {
  let c: ts.Node = n;
  while (c.parent && ts.isParenthesizedExpression(c.parent)) c = c.parent;
  const p = c.parent;
  if (!p) return false;
  if ((ts.isPropertyAccessExpression(p) || ts.isElementAccessExpression(p) || ts.isCallExpression(p)) && p.questionDotToken && p.expression === c) return true;
  // tested for truthiness (`if (!d[k])`, `while (a[i])`, `d[k] ? … : …`, `d[k] || x`): a missing
  // element is undefined, which is falsy
  if (ts.isPrefixUnaryExpression(p) && p.operator === SK.ExclamationToken) return true;
  if ((ts.isIfStatement(p) || ts.isWhileStatement(p) || ts.isDoStatement(p)) && p.expression === c) return true;
  if (ts.isForStatement(p) && p.condition === c) return true;
  if (ts.isConditionalExpression(p) && p.condition === c) return true;
  if (ts.isBinaryExpression(p)) {
    const k = p.operatorToken.kind;
    if ((k === SK.AmpersandAmpersandToken || k === SK.BarBarToken) && p.left === c) return true;
    if (k === SK.QuestionQuestionToken && p.left === c) return true;
    if (k === SK.EqualsEqualsEqualsToken || k === SK.ExclamationEqualsEqualsToken) {
      const other = p.left === c ? p.right : p.left;
      const o = skipParens(other);
      return ts.isIdentifier(o) && o.text === 'undefined';
    }
  }
  return false;
}

// ---------------------------------------------------------------------------------------
// optional chains

P.lowerOptChain = function (this: Translator, n, fc, exp) {
  const root = chainRoot(n) as ts.PropertyAccessExpression | ts.ElementAccessExpression | ts.CallExpression;
  const baseNode = root.expression;
  const base = this.nullishToOpt(this.lowerExpr(baseNode, fc), baseNode);
  const resultTy = exp ?? this.tyAt(n, fc);
  if (base.ty.k === 'dyn') {
    // a value of type any/unknown may be undefined or null: the chain yields undefined then,
    // without reading a property of it
    const dynLit = (t: Ty) => E.prim(`(.toDyn ${showTy(t)})`, [t.k === 'null' ? E.nullLit() : E.undef()], [t], T.dyn);
    const isNullish = (x: Expr) => E.or(E.prim('.dynEq', [x, dynLit(T.undef)], [T.dyn, T.dyn], T.bool), E.prim('.dynEq', [x, dynLit(T.null)], [T.dyn, T.dyn], T.bool));
    const bv = this.bindTemp(base, fc, 'o');
    fc.override.set(baseNode, E.var(bv));
    let rest: Expr, pre: Item[];
    try {
      [rest, pre] = this.isolate(fc, () => this.lowerExpr(n, fc, resultTy));
    } finally { fc.override.delete(baseNode); }
    const dflt = resultTy.k === 'dyn' ? dynLit(T.undef) : resultTy.k === 'opt' ? E.none(resultTy.t) : resultTy.k === 'undef' ? E.undef() : null;
    if (!dflt) reject(n, 'unsupported', `optional chain on an unknown value at type ${prettyTy(resultTy)}, which excludes undefined`);
    if (!pre.length) return E.cond(isNullish(E.var(bv)), dflt, rest);
    const r = this.mutTemp(resultTy, fc);
    fc.pre.push(stmtItem(S.ite(isNullish(E.var(bv)), [r.set(dflt)], [...pre, r.set(rest)])));
    return r.get();
  }
  if (base.ty.k !== 'opt') {
    // never nullish: plain access (the caller converts the result)
    fc.override.set(baseNode, base);
    try { return this.lowerExpr(n, fc); } finally { fc.override.delete(baseNode); }
  }
  const inner = base.ty.t;
  const v = mkVar('o', inner);
  // TypeScript may type the chain without `undefined` when it believes the base is
  // defined (e.g. `xs[0]?.x`); the chain still yields undefined when it is not
  const chainTy: Ty = resultTy.k === 'opt' || resultTy.k === 'undef' ? resultTy : T.opt(resultTy);
  fc.override.set(baseNode, E.var(v));
  let rest: Expr, pre: Item[];
  try {
    [rest, pre] = this.isolate(fc, () => this.lowerExpr(n, fc, chainTy));
  } finally { fc.override.delete(baseNode); }
  const dflt = chainTy.k === 'opt' ? E.none(chainTy.t) : E.undef();
  let res: Expr;
  if (!pre.length) res = E.caseOpt(base, dflt, v, rest);
  else {
    const r = this.mutTemp(chainTy, fc);
    fc.pre.push(stmtItem({ k: 'caseOptS', e: base, none: [r.set(dflt)], v, some: [...pre, r.set(rest)] }));
    res = r.get();
  }
  return chainTy === resultTy ? res : this.adapt(res, resultTy, n);
};

/** `T | null | undefined`-like values as `opt T'` (null and undefined both become `none`). */
P.nullishToOpt = function (this: Translator, e0, node) {
  if (isPoison(e0)) return e0;
  const e = e0.ty.k === 'named' ? this.unfoldE(e0) : e0;
  const t = e.ty;
  const stripNull = (x: Expr): Expr | null => {
    const u = x.ty;
    if (u.k !== 'union' || !u.ts.some(m => m.k === 'null')) return null;
    const rest = u.ts.filter(m => m.k !== 'null');
    const target: Ty = rest.length === 1 ? rest[0] : T.union(rest);
    return E.caseU(x, u.ts.map(m => {
      const v = mkVar('m', m);
      return { v, body: m.k === 'null' ? E.none(target) : E.some(this.coerce(E.var(v), target, node)) };
    }));
  };
  if (t.k === 'opt') {
    const tt = this.unfoldTy(t.t);
    if (tt.k === 'union' && tt.ts.some(m => m.k === 'null')) {
      const rest = tt.ts.filter(m => m.k !== 'null');
      const target: Ty = rest.length === 1 ? rest[0] : T.union(rest);
      const v = mkVar('x', t.t);
      return E.caseOpt(e, E.none(target), v, stripNull(this.unfoldE(E.var(v)))!);
    }
    return e;
  }
  return stripNull(e) ?? e;
};

// ---------------------------------------------------------------------------------------
// templates and string conversion

function lowerTemplate(tr: Translator, n: ts.TemplateExpression, fc: FnCtx): Expr {
  const parts = tr.seq(n.templateSpans.map(sp => () => tr.toStr(tr.lowerExpr(sp.expression, fc), sp.expression)), fc);
  let acc: Expr | null = n.head.text ? strLit(n.head.text) : null;
  const cat = (a: Expr | null, b: Expr): Expr => a ? E.prim('.strConcat', [a, b], [T.str, T.str], T.str) : b;
  n.templateSpans.forEach((sp, i) => {
    acc = cat(acc, parts[i]);
    if (sp.literal.text) acc = cat(acc, strLit(sp.literal.text));
  });
  return acc ?? strLit('');
}

/** `String.raw\`…\``: the template's raw text (escape sequences as written, line breaks as LF,
 * as ECMA-262's TRV) with the substitutions converted as in a template literal. Other tags are
 * rejected. */
function lowerTaggedTemplate(tr: Translator, n: ts.TaggedTemplateExpression, fc: FnCtx): Expr {
  const tag = skipParens(n.tag);
  const isRaw = ts.isPropertyAccessExpression(tag) && tag.name.text === 'raw' && ts.isIdentifier(tag.expression) &&
    tag.expression.text === 'String' && isLibDecl(tr.program, tr.symAt(tag.expression)?.declarations?.[0]);
  if (!isRaw || n.typeArguments) reject(n, 'unsupported-syntax', 'tagged templates (other than String.raw)');
  const raw = (lit: ts.TemplateLiteralLikeNode) => (lit.rawText ?? lit.text).replace(/\r\n?/g, '\n');
  const t = n.template;
  if (ts.isNoSubstitutionTemplateLiteral(t)) return strLit(raw(t));
  const parts = tr.seq(t.templateSpans.map(sp => () => tr.toStr(tr.lowerExpr(sp.expression, fc), sp.expression)), fc);
  const cat = (a: Expr | null, b: Expr): Expr => a ? E.prim('.strConcat', [a, b], [T.str, T.str], T.str) : b;
  let acc: Expr | null = raw(t.head) ? strLit(raw(t.head)) : null;
  t.templateSpans.forEach((sp, i) => {
    acc = cat(acc, parts[i]);
    if (raw(sp.literal)) acc = cat(acc, strLit(raw(sp.literal)));
  });
  return acc ?? strLit('');
}

P.toStr = function (this: Translator, e0, node) {
  if (isPoison(e0)) return E.poison(T.str);
  const e = this.unfoldE(e0);
  if (holdsTimer(e.ty)) reject(node, 'timer-handle', 'a Node timer handle as a string (Node gives its id)');
  switch (e.ty.k) {
    case 'str': return e;
    case 'enum': return this.coerce(e, T.str, node);
    case 'num': return E.prim('.numToStr', [e], [T.num], T.str);
    case 'bigint': return E.prim('.bigToStr', [e], [T.bigint], T.str);
    case 'bool': return E.prim('.boolToStr', [e], [T.bool], T.str);
    case 'undef': return this.withValue(e, 'u', () => strLit('undefined'));
    case 'null': return this.withValue(e, 'u', () => strLit('null'));
    case 'obj': {
      // ToString of a class instance calls its toString() method
      const ci = this.types.classes.get(e.ty.c);
      const m = ci && this.classMember(ci, 'toString', 'method', node);
      if (m && m.params.length === 1 && m.ret.k === 'str') return E.call(m, [e]);
      break;
    }
    case 'opt': {
      const v = mkVar('x', e.ty.t);
      return E.caseOpt(e, strLit('undefined'), v, this.toStr(E.var(v), node));
    }
    case 'dyn': return E.builtin('.dynToStr', [e], [T.dyn], T.str);
    case 'union': return E.caseU(e, e.ty.ts.map(m => { const v = mkVar('m', m); return { v, body: this.toStr(E.var(v), node) }; }));
    case 'err': return this.withValue(e, 'e', x => {
      // Error.prototype.toString: name, ": ", message (either part may be empty)
      const name = E.prim('.errName', [x], [T.err], T.str);
      const msg = E.prim('.errMessage', [x], [T.err], T.str);
      const cat = (a: Expr, b: Expr) => E.prim('.strConcat', [a, b], [T.str, T.str], T.str);
      return E.cond(E.seq(msg, strLit('')), name,
        E.cond(E.seq(name, strLit('')), msg, cat(cat(name, strLit(': ')), msg)));
    });
  }
  reject(node, 'template-hole', `cannot convert ${prettyTy(e.ty)} to a string implicitly; only string, number, bigint and boolean are allowed`);
};

// ---------------------------------------------------------------------------------------
// operators

function isStringy(t: Ty): boolean { return t.k === 'str' || t.k === 'enum'; }

const NUM_BIN: Partial<Record<ts.SyntaxKind, string>> = {
  [SK.PlusToken]: 'add', [SK.MinusToken]: 'sub', [SK.AsteriskToken]: 'mul', [SK.SlashToken]: 'div', [SK.PercentToken]: 'rem',
  [SK.AsteriskAsteriskToken]: 'pow', [SK.AmpersandToken]: 'band', [SK.BarToken]: 'bor', [SK.CaretToken]: 'bxor',
  [SK.LessThanLessThanToken]: 'shl', [SK.GreaterThanGreaterThanToken]: 'sar', [SK.GreaterThanGreaterThanGreaterThanToken]: 'shr',
};
const CMP: Partial<Record<ts.SyntaxKind, string>> = {
  [SK.LessThanToken]: 'lt', [SK.LessThanEqualsToken]: 'le', [SK.GreaterThanToken]: 'gt', [SK.GreaterThanEqualsToken]: 'ge',
};
const COMPOUND: Partial<Record<ts.SyntaxKind, ts.SyntaxKind>> = {
  [SK.PlusEqualsToken]: SK.PlusToken, [SK.MinusEqualsToken]: SK.MinusToken, [SK.AsteriskEqualsToken]: SK.AsteriskToken,
  [SK.SlashEqualsToken]: SK.SlashToken, [SK.PercentEqualsToken]: SK.PercentToken, [SK.AsteriskAsteriskEqualsToken]: SK.AsteriskAsteriskToken,
  [SK.AmpersandEqualsToken]: SK.AmpersandToken, [SK.BarEqualsToken]: SK.BarToken, [SK.CaretEqualsToken]: SK.CaretToken,
  [SK.LessThanLessThanEqualsToken]: SK.LessThanLessThanToken, [SK.GreaterThanGreaterThanEqualsToken]: SK.GreaterThanGreaterThanToken,
  [SK.GreaterThanGreaterThanGreaterThanEqualsToken]: SK.GreaterThanGreaterThanGreaterThanToken,
};

/** `<`, `<=`, `>`, `>=` with an unknown operand, as JavaScript compares the runtime values:
 * ToPrimitive (an object gives its String(x), as String(x) of an unknown value does), then two
 * strings compare by code units and other primitives as numbers (ToNumber). A bigint or a
 * function operand panics (not modelled). */
function dynCompare(tr: Translator, cmp: string, a: Expr, b: Expr, node: ts.Node): Expr {
  const tag = (d: Expr) => E.prim('.dynTypeof', [d], [T.dyn], T.str);
  const is = (d: Expr, s: string) => E.seq(tag(d), strLit(s));
  const as = (d: Expr, t: Ty) => E.unwrap(E.prim(`(.dynCast ${showTy(t)})`, [d], [T.dyn], T.opt(t)));
  const isNull = (d: Expr) => E.prim('.dynEq', [d, E.prim('(.toDyn .null)', [E.nullLit()], [T.null], T.dyn)], [T.dyn, T.dyn], T.bool);
  const toDyn = (x: Expr) => x.ty.k === 'dyn' ? x
    : isStringy(x.ty) ? E.prim('(.toDyn .str)', [tr.toStr(x, node)], [T.str], T.dyn) : tr.coerce(x, T.dyn, node);
  const prim = (x: Expr) => tr.withValue(toDyn(x), 'd', d =>
    E.cond(is(d, 'object'), E.cond(isNull(d), d, E.prim('(.toDyn .str)', [E.builtin('.dynToStr', [d], [T.dyn], T.str)], [T.str], T.dyn)),
      E.cond(is(d, 'function'), E.unreachable(T.dyn), d)));
  const num = (p: Expr) => E.cond(is(p, 'number'), as(p, T.num),
    E.cond(is(p, 'string'), E.prim('.strToNum', [as(p, T.str)], [T.str], T.num),
      E.cond(is(p, 'boolean'), E.cond(as(p, T.bool), numLit(1), numLit(0)),
        E.cond(is(p, 'undefined'), numLit(NaN), E.cond(isNull(p), numLit(0), E.unreachable(T.num))))));
  return tr.withValue(prim(a), 'pa', pa => tr.withValue(prim(b), 'pb', pb => {
    const sa = mkVar('sa', T.str), sb = mkVar('sb', T.str);
    const str = (p: Expr) => E.prim('(.dynCast .str)', [p], [T.dyn], T.opt(T.str));
    const nums = E.prim(`(.numCmp .${cmp})`, [num(pa), num(pb)], [T.num, T.num], T.bool);
    return E.caseOpt(str(pa), nums, sa, E.caseOpt(str(pb), nums, sb, E.prim(`(.strCmp .${cmp})`, [E.var(sa), E.var(sb)], [T.str, T.str], T.bool)));
  }));
}

P.arith = function (this: Translator, op, a0, b0, node) {
  if (isPoison(a0) || isPoison(b0)) {
    if (CMP[op]) return E.poison(T.bool);
    const other = isPoison(a0) ? b0 : a0;
    return E.poison(isPoison(other) ? T.undef : other.ty);
  }
  const a = this.unfoldE(a0), b = this.unfoldE(b0);
  const ta = a.ty, tb = b.ty;
  if (holdsTimer(ta) || holdsTimer(tb)) reject(node, 'timer-handle', 'a Node timer handle in arithmetic, a comparison or a string (Node converts it to its id)');
  if (ta.k === 'dyn' || tb.k === 'dyn') {
    // string + unknown: ToPrimitive then ToString, as String(x) for the modelled runtime types
    if (op === SK.PlusToken && (isStringy(ta) || isStringy(tb))) {
      return E.prim('.strConcat', [this.toStr(a, node), this.toStr(b, node)], [T.str, T.str], T.str);
    }
    const c = CMP[op];
    if (c) return dynCompare(this, c, a, b, node);
    reject(node, 'any-op', `operator ${ts.tokenToString(op)} on a value of type any/unknown (cast it first)`);
  }
  if (op === SK.PlusToken && isStringy(ta) && isStringy(tb)) {
    return E.prim('.strConcat', [this.toStr(a, node), this.toStr(b, node)], [T.str, T.str], T.str);
  }
  const cmp = CMP[op];
  if (cmp) {
    if (ta.k === 'num' && tb.k === 'num') return E.prim(`(.numCmp .${cmp})`, [a, b], [T.num, T.num], T.bool);
    if (ta.k === 'bigint' && tb.k === 'bigint') return E.prim(`(.bigCmp .${cmp})`, [a, b], [T.bigint, T.bigint], T.bool);
    if (isStringy(ta) && isStringy(tb)) return E.prim(`(.strCmp .${cmp})`, [this.toStr(a, node), this.toStr(b, node)], [T.str, T.str], T.bool);
    reject(node, 'mixed-compare', `comparison between ${prettyTy(ta)} and ${prettyTy(tb)}`);
  }
  const nb = NUM_BIN[op];
  if (nb) {
    if (ta.k === 'num' && tb.k === 'num') return E.prim(`(.numBin .${nb})`, [a, b], [T.num, T.num], T.num);
    if (ta.k === 'bigint' && tb.k === 'bigint') {
      if (nb === 'shr') reject(node, 'unsupported', '`>>>` on bigint');
      return E.prim(`(.bigBin .${nb})`, [a, b], [T.bigint, T.bigint], T.bigint);
    }
    if (op === SK.PlusToken) reject(node, 'mixed-plus', `\`+\` between ${prettyTy(ta)} and ${prettyTy(tb)}; use a template literal or an explicit conversion`);
    reject(node, 'unsupported', `operator ${ts.tokenToString(op)} on ${prettyTy(ta)} and ${prettyTy(tb)}`);
  }
  reject(node, 'unsupported', `operator ${ts.tokenToString(op)}`);
};

function lowerPrefix(tr: Translator, u: ts.PrefixUnaryExpression, fc: FnCtx): Expr {
  if (u.operator === SK.PlusToken || u.operator === SK.MinusToken || u.operator === SK.TildeToken) {
    if (holdsTimer(tr.tyAt(u.operand, fc))) reject(u, 'timer-handle', 'a Node timer handle as a number (Node converts it to its id)');
  }
  switch (u.operator) {
    case SK.PlusPlusToken: case SK.MinusMinusToken: return tr.lowerUpdate(u, fc, true)!;
    case SK.ExclamationToken: return E.not(tr.lowerCond(u.operand, fc));
    case SK.MinusToken: {
      const o = skipParens(u.operand);
      if (ts.isNumericLiteral(o)) return numLit(-Number(o.text.replace(/_/g, '')));
      if (ts.isBigIntLiteral(o)) return bigLit(-BigInt(o.text.slice(0, -1).replace(/_/g, '')));
      const e = tr.unfoldE(tr.lowerExpr(u.operand, fc));
      if (e.ty.k === 'num') return E.prim('(.numUn .neg)', [e], [T.num], T.num);
      if (e.ty.k === 'bigint') return E.prim('.bigNeg', [e], [T.bigint], T.bigint);
      if (e.ty.k === 'dyn') reject(u, 'any-op', 'unary minus on a value of type any/unknown');
      reject(u, 'unsupported', `unary minus on ${prettyTy(e.ty)}`);
    }
    case SK.PlusToken: {
      const e = tr.unfoldE(tr.lowerExpr(u.operand, fc));
      if (e.ty.k === 'num') return e;
      if (e.ty.k === 'dyn') reject(u, 'any-op', 'unary plus on a value of type any/unknown');
      reject(u, 'unsupported', `unary plus on ${prettyTy(e.ty)}; use Number(...)`);
    }
    case SK.TildeToken: {
      const e = tr.unfoldE(tr.lowerExpr(u.operand, fc));
      if (e.ty.k === 'num') return E.prim('(.numUn .bnot)', [e], [T.num], T.num);
      if (e.ty.k === 'bigint') return E.prim('.bigNot', [e], [T.bigint], T.bigint);
      reject(u, 'unsupported', `~ on ${prettyTy(e.ty)}`);
    }
  }
  reject(u, 'unsupported-syntax', `prefix operator ${ts.tokenToString(u.operator)}`);
}

function isBoolTs(t: ts.Type): boolean {
  if (t.flags & (ts.TypeFlags.Boolean | ts.TypeFlags.BooleanLiteral)) return true;
  return t.isUnion() && t.types.every(m => !!(m.flags & ts.TypeFlags.BooleanLiteral));
}

function lowerBinary(tr: Translator, b: ts.BinaryExpression, fc: FnCtx, exp?: Ty): Expr {
  const op = b.operatorToken.kind;
  if (op >= SK.FirstAssignment && op <= SK.LastAssignment) return tr.lowerAssign(b, fc, true)!;
  switch (op) {
    case SK.CommaToken:
      tr.lowerExprStmt(b.left, fc, fc.pre);
      return tr.lowerExpr(b.right, fc, exp);
    case SK.AmpersandAmpersandToken:
    case SK.BarBarToken: {
      const whole = tr.checker.getTypeAtLocation(b);
      if (isBoolTs(whole) || (exp && exp.k === 'bool')) return tr.lowerCond(b, fc);
      return lowerValueLogical(tr, b, fc, exp);
    }
    case SK.QuestionQuestionToken: return lowerNullish(tr, b, fc, exp);
    case SK.EqualsEqualsEqualsToken:
    case SK.ExclamationEqualsEqualsToken: {
      const r = lowerEq(tr, b, fc);
      return op === SK.EqualsEqualsEqualsToken ? r : E.not(r);
    }
    case SK.EqualsEqualsToken:
    case SK.ExclamationEqualsToken: {
      const lit = isNullishLit(tr, b.right) ? b.right : isNullishLit(tr, b.left) ? b.left : null;
      if (!lit) reject(b, 'no-loose-eq', '`==` and `!=` are only allowed against null or undefined; use `===` / `!==`');
      const r = lowerIsNullish(tr, lit === b.right ? b.left : b.right, fc);
      return op === SK.EqualsEqualsToken ? r : E.not(r);
    }
    case SK.InKeyword: {
      const dt = tr.dictTyOf(b.right, fc);
      if (dt) {
        const [k, d] = tr.seq([() => tr.dictKey(b.left, fc), () => tr.lowerExpr(b.right, fc, dt)], fc);
        return E.builtin(`(.dictHas ${showTy(dt.t)})`, [d, k], [dt, T.str], T.bool);
      }
      // an unknown value (TypeScript may have narrowed it to `object`)
      const [k, d] = tr.seq([() => tr.dictKey(b.left, fc), () => tr.lowerExpr(b.right, fc)], fc);
      if (d.ty.k !== 'dyn') reject(b, 'no-in', 'the `in` operator is only supported on dictionaries and unknown values');
      return E.builtin('.dynHas', [d, k], [T.dyn, T.str], T.bool);
    }
    case SK.InstanceOfKeyword: return lowerInstanceof(tr, b, fc);
  }
  const [l, r] = tr.seq([() => tr.lowerExpr(b.left, fc), () => tr.lowerExpr(b.right, fc)], fc);
  return tr.arith(op, l, r, b);
}

function lowerInstanceof(tr: Translator, b: ts.BinaryExpression, fc: FnCtx): Expr {
  const right = skipParens(b.right);
  if (!ts.isIdentifier(right)) reject(b, 'unsupported', '`instanceof` with a computed class');
  const rsym = tr.symAt(right);
  const lib = rsym && isLibDecl(tr.program, rsym.declarations?.[0]);
  let e = tr.lowerExpr(b.left, fc);
  if (lib && ['Error', 'TypeError', 'RangeError', 'SyntaxError', 'ReferenceError', 'EvalError', 'URIError'].includes(right.text)) {
    if (e.ty.k === 'dyn') {
      // an unknown value: is it an Error (then its name decides the subclass)?
      const c = E.prim('(.dynCast .err)', [e], [T.dyn], T.opt(T.err));
      const v = mkVar('e', T.err);
      return E.caseOpt(c, E.bool(false), v, right.text === 'Error' ? E.bool(true) : E.seq(E.prim('.errName', [E.var(v)], [T.err], T.str), strLit(right.text)));
    }
    if (e.ty.k !== 'err') reject(b, 'unsupported', `instanceof ${right.text} on ${prettyTy(e.ty)}`);
    if (right.text === 'Error') return tr.withValue(e, 'e', () => E.bool(true));
    return E.seq(E.prim('.errName', [e], [T.err], T.str), strLit(right.text));
  }
  if (rsym && (rsym.flags & ts.SymbolFlags.Class) && !lib) {
    const target = tr.unfoldTy(e.ty);
    const isC = (t: Ty) => t.k === 'obj' && (t.c === right.text || t.c.startsWith(right.text + '<'));
    if (isC(target)) return tr.withValue(e, 'o', () => E.bool(true));
    if (target.k === 'union') {
      const ue = tr.unfoldE(e);
      return E.caseU(ue, target.ts.map(m => ({ v: mkVar('m', m), body: E.bool(isC(m)) })));
    }
    if (target.k === 'opt') {
      const v = mkVar('o', target.t);
      return E.caseOpt(e, E.bool(false), v, E.bool(isC(target.t)));
    }
  }
  // a library or package class (Date, Map, a Firestore Timestamp, a typed array): decided on the
  // value's type, which is nominal for these (an unknown value: by its runtime type)
  if (rsym && (rsym.flags & ts.SymbolFlags.Value) && !tr.isProjectDecl(rsym.declarations?.[0])) {
    let ct: Ty | undefined;
    try { ct = tr.tyOf(tr.checker.getDeclaredTypeOfSymbol(rsym), fc, b); } catch { ct = undefined; }
    if (ct && ['ext', 'map', 'set', 'tarr', 'arr'].includes(ct.k)) {
      const cty = ct;
      const isC = (t: Ty): boolean => t.k === cty.k && (t.k !== 'ext' || (cty.k === 'ext' && t.name === cty.name)) &&
        (t.k !== 'tarr' || (cty.k === 'tarr' && t.kind === cty.kind));
      const test = (x: Expr): Expr => {
        const u = tr.unfoldE(x);
        if (u.ty.k === 'dyn') {
          // (an unknown array is an Array whatever its element type)
          if (cty.k === 'arr') return E.prim('.dynIsArray', [u], [T.dyn], T.bool);
          const v = mkVar('c', cty);
          return E.caseOpt(E.prim(`(.dynCast ${showTy(cty)})`, [u], [T.dyn], T.opt(cty)), E.bool(false), v, E.bool(true));
        }
        if (u.ty.k === 'opt') { const v = mkVar('o', u.ty.t); return E.caseOpt(u, E.bool(false), v, test(E.var(v))); }
        if (u.ty.k === 'union') return E.caseU(u, u.ty.ts.map(m => { const v = mkVar('m', m); return { v, body: test(E.var(v)) }; }));
        return tr.withValue(u, 'x', () => E.bool(isC(u.ty)));
      };
      return test(e);
    }
  }
  reject(b, 'instanceof', '`instanceof` is only supported for Error classes, classes of a union and library classes');
}

function isUndefinedNode(tr: Translator, e: ts.Expression): boolean {
  e = skipParens(e);
  if (ts.isIdentifier(e) && e.text === 'undefined') {
    const s = tr.symAt(e);
    return !s || !s.declarations?.length || isLibDecl(tr.program, s.declarations[0]);
  }
  return ts.isVoidExpression(e);
}

/** `Number.isInteger(x)` (and isSafeInteger, isFinite, isNaN): false unless the runtime value of
 * `x` is a number, so it is decided on that value when the static type may hold one (unknown,
 * `T | undefined`, unions), not only when it is `number`. */
/** `s[i]` on a string: `i` is a property key, so only an array index (an integer from 0, -0
 * included) reads a code unit; a negative, fractional, NaN or infinite number names a property a
 * string does not have: undefined. (`.strAt` is `String.prototype.at`, which truncates the index
 * and counts negative ones from the end.) */
function strIndex(tr: Translator, s: Expr, i: Expr): Expr {
  // (a literal index that is an array index needs no test)
  if (i.k === 'lit' && typeof i.js === 'number' && Number.isInteger(i.js) && i.js >= 0) return E.prim('.strAt', [s, i], [T.str, T.num], T.opt(T.str));
  return tr.withValue(s, 's', sv => tr.withValue(i, 'i', iv => E.cond(
    E.and(E.prim('(.numPred .isInteger)', [iv], [T.num], T.bool), E.prim('(.numCmp .ge)', [iv, numLit(0)], [T.num, T.num], T.bool)),
    E.prim('.strAt', [sv, iv], [T.str, T.num], T.opt(T.str)),
    E.none(T.str))));
}

export function numberPred(tr: Translator, e0: Expr, name: string): Expr {
  const e = tr.unfoldE(e0);
  const t = e.ty;
  const pred = (x: Expr) => E.prim(`(.numPred .${name})`, [x], [T.num], T.bool);
  if (t.k === 'num') return pred(e);
  if (t.k === 'dyn') {
    const v = mkVar('n', T.num);
    return E.caseOpt(E.prim('(.dynCast .num)', [e], [T.dyn], T.opt(T.num)), E.bool(false), v, pred(E.var(v)));
  }
  if (t.k === 'opt') { const v = mkVar('x', t.t); return E.caseOpt(e, E.bool(false), v, numberPred(tr, E.var(v), name)); }
  if (t.k === 'union') return E.caseU(e, t.ts.map(m => { const v = mkVar('m', m); return { v, body: numberPred(tr, E.var(v), name) }; }));
  return tr.withValue(e, 'x', () => E.bool(false));
}

/** `===` with JavaScript semantics on the IR types. */
function lowerEq(tr: Translator, b: ts.BinaryExpression, fc: FnCtx): Expr {
  const L = skipParens(b.left), R = skipParens(b.right);
  // `x === x` (one variable on both sides) on values without identity in the IR (unknown values,
  // records, tuples): false exactly when x is NaN, whatever the value, while the IR's `===` cannot
  // decide it for records. (Types with `===` in the IR keep it.)
  if (ts.isIdentifier(L) && ts.isIdentifier(R) && L.text === R.text) {
    const s = tr.symAt(L);
    if (s && s === tr.symAt(R)) {
      const x = tr.lowerExpr(L, fc);
      if (!eqable(tr.unfoldE(x).ty)) return E.not(numberPred(tr, x, 'isNaN'));
    }
  }
  // typeof x === "tag"
  for (const [x, y] of [[L, R], [R, L]] as const) {
    if (ts.isTypeOfExpression(x) && ts.isStringLiteral(y)) {
      const e = tr.lowerExpr(x.expression, fc);
      return typeofTest(tr, e, y.text, b);
    }
  }
  // comparisons with undefined / null
  const dynIs = (u: Expr, lit: Ty): Expr =>
    E.prim('.dynEq', [u, E.prim(`(.toDyn ${showTy(lit)})`, [lit.k === 'null' ? E.nullLit() : E.undef()], [lit], T.dyn)], [T.dyn, T.dyn], T.bool);
  for (const [x, y] of [[L, R], [R, L]] as const) {
    if (isUndefinedNode(tr, y)) {
      const e = tr.unfoldE(tr.lowerExpr(x, fc));
      if (e.ty.k === 'dyn') return dynIs(e, T.undef);
      if (e.ty.k === 'opt' && e.ty.t.k === 'dyn') { const v = mkVar('x', e.ty.t); return E.caseOpt(e, E.bool(true), v, dynIs(E.var(v), T.undef)); }
      if (e.ty.k === 'opt') { const v = mkVar('x', e.ty.t); return E.caseOpt(e, E.bool(true), v, E.bool(false)); }
      if (e.ty.k === 'undef') return tr.withValue(e, 'u', () => E.bool(true));
      return tr.withValue(e, 'u', () => E.bool(false));
    }
    if (y.kind === SK.NullKeyword) {
      const e = tr.unfoldE(tr.lowerExpr(x, fc));
      const isNullU = (u: Expr): Expr => {
        if (u.ty.k === 'dyn') return dynIs(u, T.null);
        if (u.ty.k === 'union') return E.caseU(u, u.ty.ts.map(m => ({ v: mkVar('m', m), body: E.bool(m.k === 'null') })));
        if (u.ty.k === 'null') return tr.withValue(u, 'u', () => E.bool(true));
        return tr.withValue(u, 'u', () => E.bool(false));
      };
      if (e.ty.k === 'opt') { const v = mkVar('x', e.ty.t); return E.caseOpt(e, E.bool(false), v, isNullU(tr.unfoldE(E.var(v)))); }
      return isNullU(e);
    }
  }
  const [l, r] = tr.seq([() => tr.lowerExpr(b.left, fc), () => tr.lowerExpr(b.right, fc)], fc);
  return tr.strictEqExprs(l, r, b, fc);
}

function typeofTest(tr: Translator, e0: Expr, tag: string, node: ts.Node): Expr {
  if (isPoison(e0)) return E.poison(T.bool);
  const e = tr.unfoldE(e0);
  const t = e.ty;
  if (t.k === 'dyn') return E.seq(E.prim('.dynTypeof', [e], [T.dyn], T.str), strLit(tag));
  if (t.k === 'opt') {
    const v = mkVar('x', t.t);
    return E.caseOpt(e, E.bool(tag === 'undefined'), v, typeofTest(tr, E.var(v), tag, node));
  }
  if (t.k === 'union') return E.caseU(e, t.ts.map(m => ({ v: mkVar('m', m), body: E.bool(tr.typeofTag(m) === tag) })));
  return tr.withValue(e, 'x', () => E.bool(tr.typeofTag(t) === tag));
}

P.strictEqExprs = function (this: Translator, a0, b0, node, _fc) {
  if (isPoison(a0) || isPoison(b0)) return E.poison(T.bool);
  if (holdsTimer(a0.ty) || holdsTimer(b0.ty)) reject(node, 'timer-handle', '=== on a Node timer handle other than with null or undefined');
  let a = a0, b = b0;
  if (a.ty.k === 'dyn' || b.ty.k === 'dyn') {
    // `===` with an unknown operand: on the runtime values
    const d = (x: Expr) => x.ty.k === 'dyn' ? x : E.prim(`(.toDyn ${showTy(x.ty)})`, [x], [x.ty], T.dyn);
    return E.prim('.dynEq', [d(a), d(b)], [T.dyn, T.dyn], T.bool);
  }
  if (a.ty.k === 'named' || b.ty.k === 'named') { a = this.unfoldE(a); b = this.unfoldE(b); }
  if (isLitUndef(a) && b.ty.k === 'opt') [a, b] = [b, a];
  if (isLitUndef(b) && a.ty.k === 'opt') {
    const v = mkVar('x', a.ty.t);
    // (an optional unknown holding an unknown undefined is undefined too)
    const inner = this.unfoldTy(a.ty.t).k === 'dyn'
      ? E.prim('.dynEq', [this.unfoldE(E.var(v)), E.prim('(.toDyn .undef)', [E.undef()], [T.undef], T.dyn)], [T.dyn, T.dyn], T.bool)
      : E.bool(false);
    return E.caseOpt(a, E.bool(true), v, inner);
  }
  if (isLitUndef(a) && !isLitUndef(b)) [a, b] = [b, a];
  if (isLitUndef(b) && a.ty.k !== 'undef' && a.ty.k !== 'opt') return this.withValue(a, 'x', () => E.bool(false));
  // a value with records or tuples in its type compared with a primitive value: no identity is
  // involved (it is equal only if it is that primitive)
  if (!eqable(a.ty) && isPrimitiveTy(b.ty)) return this.withValue(a, 'l', x => this.withValue(b, 'r', y => eqPrimitive(this, x, y, node, _fc)));
  if (!eqable(b.ty) && isPrimitiveTy(a.ty)) return this.withValue(a, 'l', x => this.withValue(b, 'r', y => eqPrimitive(this, y, x, node, _fc)));
  if (!tyEq(a.ty, b.ty)) {
    // string literal vs enum, enum vs string, T vs T | undefined, member vs union, …
    if (isStringy(a.ty) && isStringy(b.ty) && !(a.ty.k === 'enum' && b.ty.k === 'enum')) {
      if (a.ty.k === 'enum' && b.k === 'lit') { const c = this.convert(b, a.ty, node, false, 0); if (c) b = c; }
      else if (b.ty.k === 'enum' && a.k === 'lit') { const c = this.convert(a, b.ty, node, false, 0); if (c) a = c; }
      if (!tyEq(a.ty, b.ty)) { a = this.toStr(a, node); b = this.toStr(b, node); }
    } else {
      const ab = this.convert(a, b.ty, node, false, 0);
      if (ab) a = ab;
      else {
        const ba = this.convert(b, a.ty, node, false, 0);
        if (ba) b = ba;
        else if (a.ty.k === 'enum' && b.ty.k === 'enum') { a = this.toStr(a, node); b = this.toStr(b, node); }
        else reject(node, 'unsupported', `=== between ${prettyTy(a0.ty)} and ${prettyTy(b0.ty)}`);
      }
    }
  }
  if (a.ty.k === 'fn') reject(node, 'no-record-eq', `=== on functions (closures have no identity in StrictTS)`);
  if (tyEq(a.ty, REGEXP_TY)) reject(node, 'no-regexp', '=== on regular expressions (they are compared by identity; regex values have none)');
  if (!eqable(a.ty)) reject(node, 'no-record-eq', `=== on ${prettyTy(a.ty)} (records and tuples have no identity)`);
  return E.seq(a, b);
};

function isPrimitiveTy(t: Ty): boolean {
  return t.k === 'str' || t.k === 'enum' || t.k === 'num' || t.k === 'bool' || t.k === 'bigint' || t.k === 'null' || t.k === 'undef';
}

/** `x === p` for a primitive `p`, by the members of `x`'s type: members of another type (records,
 * tuples, other primitives) are never equal to it. */
function eqPrimitive(tr: Translator, x0: Expr, p: Expr, node: ts.Node, fc: FnCtx): Expr {
  const x = tr.unfoldE(x0);
  const t = x.ty;
  if (t.k === 'opt') { const v = mkVar('x', t.t); return E.caseOpt(x, E.bool(p.ty.k === 'undef'), v, eqPrimitive(tr, E.var(v), p, node, fc)); }
  if (t.k === 'union') return E.caseU(x, t.ts.map(m => { const v = mkVar('m', m); return { v, body: eqPrimitive(tr, E.var(v), p, node, fc) }; }));
  if (t.k === 'dyn' || tyEq(t, p.ty) || (isStringy(t) && isStringy(p.ty))) return tr.strictEqExprs(x, p, node, fc);
  return tr.withValue(x, 'x', () => E.bool(false));
}

function lowerValueLogical(tr: Translator, b: ts.BinaryExpression, fc: FnCtx, exp?: Ty): Expr {
  const target = exp ?? tr.tyAt(b, fc);
  const a0 = tr.lowerExpr(b.left, fc);
  if (isPoison(a0)) { tr.lowerExpr(b.right, fc); return tr.derivedPoison(b, fc, exp); }
  const a = tr.nullishToOpt(a0, b.left);
  if (a.ty.k !== 'opt' || !isObjectLike(tr.unfoldTy(a.ty.t))) {
    // general truthiness: `a || d` is a if a is truthy, else d; `a && e` the other way round
    const isAnd0 = b.operatorToken.kind === SK.AmpersandAmpersandToken;
    const x = mkVar('l', a0.ty);
    const [rhs0, pre0] = tr.isolate(fc, () => tr.lowerExpr(b.right, fc, target));
    const keep = tr.adapt(E.var(x), target, b.left);
    if (!pre0.length) {
      return E.letE(x, a0, E.cond(tr.truthy(E.var(x), b.left), isAnd0 ? rhs0 : keep, isAnd0 ? keep : rhs0));
    }
    const xv = tr.bindTemp(a0, fc, 'l');
    const keep2 = tr.adapt(E.var(xv), target, b.left);
    const r0 = tr.mutTemp(target, fc);
    const evalR = [...pre0, r0.set(rhs0)];
    const keepR = [r0.set(keep2)];
    fc.pre.push(stmtItem(S.ite(tr.truthy(E.var(xv), b.left), isAnd0 ? evalR : keepR, isAnd0 ? keepR : evalR)));
    return r0.get();
  }
  const v = mkVar('o', a.ty.t);
  const isAnd = b.operatorToken.kind === SK.AmpersandAmpersandToken;
  const [rhs, pre] = tr.isolate(fc, () => {
    if (!isAnd) return tr.lowerExpr(b.right, fc, target);
    return tr.lowerExpr(b.right, fc, target);
  });
  const dflt = isAnd ? (target.k === 'opt' ? E.none(target.t) : null) : rhs;
  if (!dflt) reject(b, 'unsupported', '`&&` whose result cannot be undefined');
  const someV = isAnd ? rhs : tr.coerce(E.var(v), target, b);
  if (!pre.length) return E.caseOpt(a, isAnd ? dflt : rhs, v, someV);
  const r = tr.mutTemp(target, fc);
  if (isAnd) fc.pre.push(stmtItem({ k: 'caseOptS', e: a, none: [r.set(dflt)], v, some: [...pre, r.set(rhs)] }));
  else fc.pre.push(stmtItem({ k: 'caseOptS', e: a, none: [...pre, r.set(rhs)], v, some: [r.set(someV)] }));
  return r.get();
}

/** `null`, the global `undefined`, or `void <number>`. */
function isNullishLit(tr: Translator, e0: ts.Expression): boolean {
  const e = skipParens(e0);
  if (e.kind === SK.NullKeyword) return true;
  if (ts.isIdentifier(e) && e.text === 'undefined') { const s = tr.checker.getSymbolAtLocation(e); return !s || !tr.facts(s); }
  return ts.isVoidExpression(e) && ts.isNumericLiteral(skipParens(e.expression));
}

/** `x == null` (the loose comparison with null or undefined): true exactly when x is null or
 * undefined (ECMA-262 IsLooselyEqual; the IR has no `document.all`). The operand is evaluated once. */
function lowerIsNullish(tr: Translator, x: ts.Expression, fc: FnCtx): Expr {
  const e0 = tr.lowerExpr(x, fc);
  if (isPoison(e0)) return e0;
  const e = e0.ty.k === 'named' ? tr.unfoldE(e0) : e0;
  if (e.ty.k === 'dyn') {
    const v = tr.bindTemp(e, fc, 'n');
    const dynLit = (t: Ty) => E.prim(`(.toDyn ${showTy(t)})`, [t.k === 'null' ? E.nullLit() : E.undef()], [t], T.dyn);
    return E.or(E.prim('.dynEq', [E.var(v), dynLit(T.undef)], [T.dyn, T.dyn], T.bool), E.prim('.dynEq', [E.var(v), dynLit(T.null)], [T.dyn, T.dyn], T.bool));
  }
  if (e.ty.k === 'null' || e.ty.k === 'undef') { tr.bindTemp(e, fc, 'n'); return E.bool(true); }
  const a = tr.nullishToOpt(e, x);
  if (a.ty.k === 'opt') return E.caseOpt(a, E.bool(true), mkVar('n', a.ty.t), E.bool(false));
  // never null or undefined: the operand still runs
  tr.bindTemp(a, fc, 'n');
  return E.bool(false);
}

function lowerNullish(tr: Translator, b: ts.BinaryExpression, fc: FnCtx, exp?: Ty): Expr {
  const target = exp ?? tr.tyAt(b, fc);
  // an array expected for the whole: the left side is expected as an optional array (e.g. a global
  // regex match, whose lib type is a match object, answers an array of strings there)
  const a = tr.nullishToOpt(tr.lowerExpr(b.left, fc, exp && exp.k === 'arr' ? T.opt(exp) : undefined), b.left);
  if (a.ty.k !== 'opt') return tr.coerce(a, target, b);
  const v = mkVar('x', a.ty.t);
  const someV = tr.coerce(E.var(v), target, b);
  const [d, pre] = tr.isolate(fc, () => tr.lowerExpr(b.right, fc, target));
  if (!pre.length) return E.caseOpt(a, d, v, someV);
  const r = tr.mutTemp(target, fc);
  fc.pre.push(stmtItem({ k: 'caseOptS', e: a, none: [...pre, r.set(d)], v, some: [r.set(someV)] }));
  return r.get();
}

function lowerConditional(tr: Translator, n: ts.ConditionalExpression, fc: FnCtx, exp?: Ty): Expr {
  const target = exp ?? tr.tyAt(n, fc);
  const test = tr.narrowTest(n.condition, fc);
  if (test && test.kind === 'opt' && tr.isRebindable(test.sym, fc, [n.whenTrue, n.whenFalse])) {
    const inner = (test.scrut.ty as Extract<Ty, { k: 'opt' }>).t;
    const v = mkVar(test.sym.name, inner);
    const [someE, preS] = tr.isolate(fc, () => {
      fc.push(); fc.bind(test.sym, { k: 'var', v });
      try { return tr.lowerExpr(test.thenSome ? n.whenTrue : n.whenFalse, fc, target); } finally { fc.pop(); }
    });
    const [noneE, preN] = tr.isolate(fc, () => tr.lowerExpr(test.thenSome ? n.whenFalse : n.whenTrue, fc, target));
    if (!preS.length && !preN.length) return E.caseOpt(test.scrut, noneE, v, someE);
    const r = tr.mutTemp(target, fc);
    fc.pre.push(stmtItem({ k: 'caseOptS', e: test.scrut, none: [...preN, r.set(noneE)], v, some: [...preS, r.set(someE)] }));
    return r.get();
  }
  const c = tr.lowerCond(n.condition, fc);
  const [a, preA] = tr.isolate(fc, () => tr.lowerExpr(n.whenTrue, fc, target));
  const [bb, preB] = tr.isolate(fc, () => tr.lowerExpr(n.whenFalse, fc, target));
  if (!preA.length && !preB.length) return E.cond(c, a, bb);
  const r = tr.mutTemp(target, fc);
  fc.pre.push(stmtItem(S.ite(c, [...preA, r.set(a)], [...preB, r.set(bb)])));
  return r.get();
}

function lowerAssertion(tr: Translator, n: ts.AsExpression | ts.SatisfiesExpression | ts.TypeAssertion, fc: FnCtx): Expr {
  const inner = n.expression;
  if (ts.isAsExpression(n) && ts.isTypeReferenceNode(n.type) && n.type.typeName.getText() === 'const') {
    return tr.lowerExpr(inner, fc, tr.tyAt(n, fc));
  }
  const target = tr.checker.getTypeAtLocation(n);
  const src = tr.checker.getTypeAtLocation(inner);
  // catch variables (unknown) used as Error
  const innerS = skipParens(inner);
  if (ts.isIdentifier(innerS)) {
    const sym = tr.symAt(innerS);
    const b = sym && tr.lookup(sym, fc);
    if (b && b.k === 'var' && b.errVar) {
      const tt = tr.tyOf(target, fc, n);
      if (tt.k !== 'err') reject(n, 'as-downcast', 'a catch variable can only be used as an Error');
      return E.var(b.v);
    }
  }
  // the value of an external call (a new object: nothing else in the program holds it) cast to a
  // record type compared by identity is a new cell (identity.ts)
  const castTo = (tt: Ty): Expr => {
    if (tt.k !== 'box' || tt.t.k !== 'record' || !ts.isCallExpression(innerS) || tr.classifyCall(innerS, fc).kind !== 'external') return tr.lowerExpr(inner, fc, tt);
    const r = tr.lowerExpr(inner, fc, tt.t);
    return E.builtin(`(.boxNew ${showTy(tt.t)})`, [r], [tt.t], tt);
  };
  // a cast of an unknown value (also as narrowed to `object`) is a checked cast
  const unknownish = (x: ts.Type) => !!(x.flags & (ts.TypeFlags.Unknown | ts.TypeFlags.NonPrimitive));
  if (unknownish(src) || (src.isIntersection() && src.types.some(unknownish))) return castTo(tr.tyOf(target, fc, n));
  // a dictionary of unknown values (DocumentData, a parsed JSON object) cast to a record type
  if (!tr.strict) {
    let st: Ty | undefined;
    try { st = tr.unfoldTy(tr.tyOf(src, fc, n)); } catch { st = undefined; }
    const dd = (t: Ty | undefined) => !!t && t.k === 'dict' && t.t.k === 'dyn';
    if (st && (dd(st) || (st.k === 'opt' && dd(st.t)))) return castTo(tr.tyOf(target, fc, n));
  }
  if (!ts.isSatisfiesExpression(n) && !tr.checker.isTypeAssignableTo(src, target)) {
    // a downcast to a narrower type (`x as string` for `string | undefined`, a string to a
    // string-literal union, a union to one member): a checked narrowing, a panic on a mismatch
    // (not in the original subset, `--strict`)
    if (!tr.strict && tr.checker.isTypeAssignableTo(target, src)) {
      const tt = tr.tyOf(target, fc, n);
      const e = tr.lowerExpr(inner, fc);
      const c = isPoison(e) ? E.poison(tt) : tr.convert(e, tt, n, true, 0);
      if (c) return c;
    }
    reject(n, 'as-downcast', `\`as\` downcast from ${tr.checker.typeToString(src)} to ${tr.checker.typeToString(target)}`);
  }
  return castTo(tr.tyOf(target, fc, n));
}

// ---------------------------------------------------------------------------------------
// conditions

P.lowerCond = function (this: Translator, n0, fc) {
  const n = skipParens(n0);
  if (ts.isPrefixUnaryExpression(n) && n.operator === SK.ExclamationToken) return E.not(this.lowerCond(n.operand, fc));
  if (ts.isBinaryExpression(n) && (n.operatorToken.kind === SK.AmpersandAmpersandToken || n.operatorToken.kind === SK.BarBarToken)) {
    const isAnd = n.operatorToken.kind === SK.AmpersandAmpersandToken;
    // `x !== undefined && P(x)` / `x === undefined || P(x)`: rebind x in P
    const test = this.narrowTest(n.left, fc);
    if (test && test.kind === 'opt' && test.thenSome === isAnd && this.isRebindable(test.sym, fc, n.right)) {
      const inner = (test.scrut.ty as Extract<Ty, { k: 'opt' }>).t;
      const v = mkVar(test.sym.name, inner);
      const [rhs, pre] = this.isolate(fc, () => {
        fc.push(); fc.bind(test.sym, { k: 'var', v });
        try { return this.lowerCond(n.right, fc); } finally { fc.pop(); }
      });
      if (!pre.length) return E.caseOpt(test.scrut, E.bool(!isAnd), v, rhs);
      const r = mkVar('c', T.bool, true);
      fc.pre.push(declItem(r, E.bool(!isAnd)));
      fc.pre.push(stmtItem({ k: 'caseOptS', e: test.scrut, none: [], v, some: [...pre, stmtItem(S.assign(r, rhs))] }));
      return E.var(r);
    }
    const l = this.lowerCond(n.left, fc);
    const [rhs, pre] = this.isolate(fc, () => this.lowerCond(n.right, fc));
    if (!pre.length) return isAnd ? E.and(l, rhs) : E.or(l, rhs);
    const r = mkVar('c', T.bool, true);
    fc.pre.push(declItem(r, E.bool(!isAnd)));
    const assign = [...pre, stmtItem(S.assign(r, rhs))];
    fc.pre.push(stmtItem(isAnd ? S.ite(l, assign, []) : S.ite(l, [], assign)));
    return E.var(r);
  }
  const t = this.checker.getTypeAtLocation(n);
  if (isBoolTs(t)) {
    // (a tested element read is optional: a missing element is falsy)
    const e = this.lowerExpr(n, fc, (ts.isElementAccessExpression(n) || ts.isPropertyAccessExpression(n)) ? undefined : T.bool);
    return this.unfoldE(e).ty.k === 'bool' ? e : this.truthy(e, n);
  }
  return this.truthy(this.lowerExpr(n, fc), n);
};

P.truthy = function (this: Translator, e0, node) {
  // JavaScript truthiness as explicit tests: "" / 0 / -0 / NaN / 0n / undefined / null are
  // falsy; objects, arrays and functions are truthy (a null test for optional ones)
  if (isPoison(e0)) return E.poison(T.bool);
  const e = this.unfoldE(e0);
  const t = e.ty;
  switch (t.k) {
    case 'bool': return e;
    case 'str': return E.not(E.seq(e, strLit('')));
    case 'enum': return t.cases.includes('') ? E.not(E.seq(this.toStr(e, node), strLit(''))) : this.withValue(e, 'k', () => E.bool(true));
    case 'num': return this.withValue(e, 'n', x => E.and(E.not(E.seq(x, numLit(0))), E.seq(x, x)));
    case 'bigint': return E.not(E.seq(e, bigLit(0n)));
    case 'dyn': return E.prim('.dynTruthy', [e], [T.dyn], T.bool);
    case 'undef': case 'null': return this.withValue(e, 'u', () => E.bool(false));
    case 'opt': { const v = mkVar('x', t.t); return E.caseOpt(e, E.bool(false), v, this.truthy(E.var(v), node)); }
    case 'union': return E.caseU(e, t.ts.map(m => { const v = mkVar('m', m); return { v, body: this.truthy(E.var(v), node) }; }));
  }
  if (isObjectLike(t)) return this.withValue(e, 'o', () => E.bool(true));
  reject(node, 'truthiness', `condition of type ${prettyTy(t)}`);
};

// ---------------------------------------------------------------------------------------
// assignment

P.assignTo = function (this: Translator, b, value0, needValue, fc, node) {
  let value = value0;
  let result: Expr | null = null;
  if (needValue) {
    const v = this.bindTemp(value, fc, 'av');
    value = E.var(v);
    result = E.var(v);
  }
  switch (b.k) {
    case 'poison':
      break;
    case 'var':
      if (b.errVar) reject(node, 'unsupported', 'assignment to a catch variable');
      fc.pre.push(stmtItem(S.assign(b.v, value)));
      break;
    case 'box':
      fc.pre.push(stmtItem(S.expr(E.builtin(`(.boxSet ${showTy(b.t)})`, [E.var(b.v), value], [T.box(b.t), b.t], T.undef))));
      break;
    case 'boxOpt':
      fc.pre.push(stmtItem(S.expr(E.builtin(`(.boxSet ${showTy(T.opt(b.t))})`, [E.var(b.v), E.some(value)], [T.box(T.opt(b.t)), T.opt(b.t)], T.undef))));
      break;
    case 'optInit':
      fc.pre.push(stmtItem(S.assign(b.v, E.some(value))));
      break;
    case 'global':
      fc.pre.push(stmtItem(S.gset(b.g, value)));
      break;
    case 'lifted':
      reject(node, 'unsupported', 'assignment to a function');
  }
  return result;
};

function compoundOp(op: ts.SyntaxKind): ts.SyntaxKind | undefined { return COMPOUND[op]; }

P.lowerAssign = function (this: Translator, b, fc, needValue, forceEq = false) {
  const op = forceEq ? SK.EqualsToken : b.operatorToken.kind;
  const L = skipParens(b.left);
  if (op === SK.AmpersandAmpersandEqualsToken || op === SK.BarBarEqualsToken || op === SK.QuestionQuestionEqualsToken) {
    return lowerLogicalAssign(this, b, fc, needValue);
  }
  if (ts.isArrayLiteralExpression(L)) {
    if (op !== SK.EqualsToken) reject(b, 'unsupported-syntax', 'compound destructuring assignment');
    return lowerDestructAssign(this, L, b.right, fc, needValue, b);
  }
  if (ts.isObjectLiteralExpression(L)) reject(b, 'unsupported-syntax', 'object destructuring assignment');
  const cop = op === SK.EqualsToken ? undefined : compoundOp(op);
  if (op !== SK.EqualsToken && cop === undefined) reject(b, 'unsupported-syntax', `assignment operator ${ts.tokenToString(op)}`);
  if (ts.isIdentifier(L)) {
    const sym = this.symAt(L);
    const bd = sym && this.lookup(sym, fc);
    if (!bd) reject(L, 'unsupported', `assignment to ${L.text}`);
    if (bd.k === 'poison') { this.lowerExpr(b.right, fc); return needValue ? E.poison(bd.ty) : null; }
    const ty = this.bindingTy(bd);
    let value: Expr;
    if (cop === undefined) value = this.lowerExpr(b.right, fc, ty);
    else {
      const [cur, r] = this.seq([() => this.readBinding(bd, L), () => this.lowerExpr(b.right, fc)], fc);
      value = this.coerce(this.arith(cop, cur, r, b), ty, b);
    }
    return this.assignTo(bd, value, needValue, fc, b);
  }
  if (ts.isPropertyAccessExpression(L)) {
    const st = this.staticFieldGlobal(L);
    if (st) {
      const bd: Binding = { k: 'global', g: st };
      let value: Expr;
      if (cop === undefined) value = this.lowerExpr(b.right, fc, st.ty);
      else {
        const [cur, r] = this.seq([() => E.gget(st), () => this.lowerExpr(b.right, fc)], fc);
        value = this.coerce(this.arith(cop, cur, r, b), st.ty, b);
      }
      return this.assignTo(bd, value, needValue, fc, b);
    }
    const name = L.name.text;
    const objE = this.lowerExpr(L.expression, fc);
    const o0 = this.unfoldE(objE);
    if (isPoison(o0)) { this.lowerExpr(b.right, fc); return needValue ? this.derivedPoison(b, fc) : null; }
    if (o0.ty.k === 'dict') return this.dictAssign(o0, () => strLit(name), b, cop, needValue, fc);
    if (o0.ty.k === 'dyn') reject(b, 'any-op', `assignment to property ${name} of a value of type any/unknown`);
    if (o0.ty.k === 'ext' && cop === undefined) {
      // a property write on an external object: an external call
      const pt = this.tyAt(L, fc);
      const [o, v] = this.seq([() => o0, () => this.lowerExpr(b.right, fc, pt)], fc);
      const vv = needValue ? E.var(this.bindTemp(v, fc, 'xv')) : v;
      fc.pre.push(stmtItem(S.expr(E.extern(`${o0.ty.name}.set:${name}`, [o, vv], T.undef))));
      return needValue ? vv : null;
    }
    if (o0.ty.k === 'arr' && name === 'length') {
      const at = o0.ty;
      const [o, n] = this.seq([() => o0, () => this.lowerExpr(b.right, fc, T.num)], fc);
      const nv = needValue ? E.var(this.bindTemp(n, fc, 'len')) : n;
      fc.pre.push(stmtItem(S.expr(E.builtin(`(.arrSetLength ${showTy(at.t)})`, [o, nv], [at, T.num], T.undef))));
      return needValue ? nv : null;
    }
    if (tyEq(o0.ty, REGEXP_TY)) reject(b, 'no-regexp', `assignment to ${name} of a regular expression (its matching state is not modelled)`);
    if (o0.ty.k === 'record') reject(b, 'record-mutation', `assignment to field ${name} of an immutable record type (the value flows through a record type here)`);
    if (o0.ty.k !== 'obj') reject(b, 'unsupported', `assignment to property ${name} of ${prettyTy(o0.ty)}`);
    const c = o0.ty.c;
    const info = this.classOfObj(c);
    const idx = info?.fieldIdx.get(name);
    if (!info || idx === undefined) {
      const ci = this.types.classes.get(c);
      const setter = ci && this.classMember(ci, name, 'setter', b);
      if (setter && cop === undefined) {
        const pt = setter.params[1].ty;
        const [o, v] = this.seq([() => o0, () => this.lowerExpr(b.right, fc, pt)], fc);
        const vv = needValue ? E.var(this.bindTemp(v, fc, 'sv')) : v;
        fc.pre.push(stmtItem(S.expr(E.call(setter, [o, vv]))));
        return needValue ? vv : null;
      }
      reject(b, 'unsupported', `no field ${name} on ${c}`);
    }
    const fty = info.fields[idx].ty;
    if (cop === undefined) {
      const [o, v] = this.seq([() => o0, () => this.lowerExpr(b.right, fc, fty)], fc);
      const vv = needValue ? E.var(this.bindTemp(v, fc, 'fv')) : v;
      fc.pre.push(stmtItem(S.setField(o, c, idx, fty, vv)));
      return needValue ? vv : null;
    }
    const o = this.spill(o0, fc, 'o');
    const [cur, r] = this.seq([() => E.getField(o, c, idx, fty), () => this.lowerExpr(b.right, fc)], fc);
    let value = this.coerce(this.arith(cop, cur, r, b), fty, b);
    if (needValue) value = E.var(this.bindTemp(value, fc, 'fv'));
    fc.pre.push(stmtItem(S.setField(o, c, idx, fty, value)));
    return needValue ? value : null;
  }
  if (ts.isElementAccessExpression(L)) {
    const base = this.unfoldE(this.lowerExpr(L.expression, fc));
    if (isPoison(base)) { this.lowerExpr(L.argumentExpression, fc); this.lowerExpr(b.right, fc); return needValue ? this.derivedPoison(b, fc) : null; }
    if (base.ty.k === 'dict') return this.dictAssign(base, () => this.dictKey(L.argumentExpression, fc), b, cop, needValue, fc);
    if (base.ty.k === 'dyn') reject(b, 'any-op', 'element assignment on a value of type any/unknown');
    if (base.ty.k !== 'arr' && base.ty.k !== 'tarr') {
      if (base.ty.k === 'record' || base.ty.k === 'obj') reject(L, 'computed-key', `assignment to a computed property of ${prettyTy(base.ty)}`);
      reject(b, 'unsupported', `element assignment on ${prettyTy(base.ty)}`);
    }
    const [a0, i0] = this.seq([() => base, () => this.lowerExpr(L.argumentExpression, fc, T.num)], fc);
    const at = a0.ty;
    if (at.k !== 'arr' && at.k !== 'tarr') reject(b, 'unsupported', `element assignment on ${prettyTy(at)}`);
    const elemTy = at.k === 'arr' ? at.t : (at.kind === 'bi64' || at.kind === 'bu64' ? T.bigint : T.num);
    const setOp = at.k === 'arr' ? `(.arrSet ${showTy(at.t)})` : `(.taSet .${at.kind})`;
    const getOp = at.k === 'arr' ? `(.arrGet ${showTy(at.t)})` : `(.taGet .${at.kind})`;
    if (cop === undefined) {
      const [a, i, v] = this.seq([() => a0, () => i0, () => this.lowerExpr(b.right, fc, elemTy)], fc);
      const vv = needValue ? E.var(this.bindTemp(v, fc, 'ev')) : v;
      fc.pre.push(stmtItem(S.expr(E.builtin(setOp, [a, i, vv], [at, T.num, elemTy], T.undef))));
      return needValue ? vv : null;
    }
    const a = this.spill(a0, fc, 'a'), i = this.spill(i0, fc, 'i');
    const [cur, r] = this.seq([() => E.builtin(getOp, [a, i], [at, T.num], elemTy), () => this.lowerExpr(b.right, fc)], fc);
    let value = this.coerce(this.arith(cop, cur, r, b), elemTy, b);
    if (needValue) value = E.var(this.bindTemp(value, fc, 'ev'));
    fc.pre.push(stmtItem(S.expr(E.builtin(setOp, [a, i, value], [at, T.num, elemTy], T.undef))));
    return needValue ? value : null;
  }
  reject(b, 'unsupported-syntax', 'assignment target');
};

function lowerLogicalAssign(tr: Translator, b: ts.BinaryExpression, fc: FnCtx, needValue: boolean): Expr | null {
  const op = b.operatorToken.kind;
  const L = skipParens(b.left);
  if (needValue && !ts.isIdentifier(L)) reject(b, 'unsupported', 'logical assignment to a property used as a value');
  if (needValue) {
    // the value of `x ??= e` is x afterwards
    lowerLogicalAssign(tr, b, fc, false);
    return tr.lowerExpr(L, fc);
  }
  if (ts.isElementAccessExpression(L) || ts.isPropertyAccessExpression(L)) {
    const dt = tr.dictTyOf(L.expression, fc);
    if (dt) {
      // o[k] ??= e  ==>  if (!(k in own entries) or o[k] === undefined) o[k] = e  (similarly ||=, &&=)
      const [d1, k1] = tr.seq([() => tr.lowerExpr(L.expression, fc, dt),
        () => ts.isPropertyAccessExpression(L) ? strLit(L.name.text) : tr.dictKey(L.argumentExpression, fc)], fc);
      const d = tr.spill(d1, fc, 'd'), k = tr.spill(k1, fc, 'k');
      const cur = tr.dictGetOpt(d, k);
      let c: Expr;
      if (op === SK.QuestionQuestionEqualsToken) {
        const v = mkVar('x', (cur.ty as Extract<Ty, { k: 'opt' }>).t);
        c = E.caseOpt(cur, E.bool(true), v, E.bool(false));
      } else c = op === SK.BarBarEqualsToken ? E.not(tr.truthy(cur, L)) : tr.truthy(cur, L);
      const body: Item[] = [];
      const saved = fc.pre;
      fc.pre = body;
      try {
        const v = tr.lowerExpr(b.right, fc, dt.t);
        body.push(stmtItem(tr.dictSetStmt(d, k, v)));
      } finally { fc.pre = saved; }
      fc.pre.push(stmtItem(S.ite(c, body, [])));
      return null;
    }
  }
  if (!ts.isIdentifier(L) && !ts.isPropertyAccessExpression(L)) reject(b, 'unsupported', 'logical assignment target');
  // x ??= e  ==>  if (x === undefined) x = e   (similarly ||=, &&= on booleans)
  // (the stored value is tested, not TypeScript's narrowed view of it)
  let cur: Expr;
  if (ts.isIdentifier(L)) {
    const sym = tr.symAt(L);
    const bd = sym && tr.lookup(sym, fc);
    if (!bd) reject(L, 'unsupported', `assignment to ${L.text}`);
    cur = bd.k === 'optInit' ? E.var(bd.v) : tr.readBinding(bd, L);
  } else {
    const o = tr.unfoldE(tr.lowerExpr((L as ts.PropertyAccessExpression).expression, fc));
    cur = o.ty.k === 'obj' ? tr.readField(o, (L as ts.PropertyAccessExpression).name.text, L) : tr.memberOf(o, (L as ts.PropertyAccessExpression).name.text, L, fc);
  }
  let test: Expr;
  if (op === SK.QuestionQuestionEqualsToken) {
    const o = tr.nullishToOpt(cur, L);
    if (o.ty.k !== 'opt') return null;
    const v = mkVar('x', o.ty.t);
    test = E.caseOpt(o, E.bool(true), v, E.bool(false));
  } else {
    const c = tr.truthy(cur, L);
    test = op === SK.BarBarEqualsToken ? E.not(c) : c;
  }
  const body: Item[] = [];
  const saved = fc.pre;
  fc.pre = body;
  try {
    tr.lowerAssign(b, fc, false, true);
  } finally { fc.pre = saved; }
  fc.pre.push(stmtItem(S.ite(test, body, [])));
  return null;
}

function lowerDestructAssign(tr: Translator, L: ts.ArrayLiteralExpression, R: ts.Expression, fc: FnCtx, needValue: boolean, node: ts.Node): Expr | null {
  if (needValue) reject(node, 'unsupported', 'destructuring assignment used as a value');
  const rhs = tr.unfoldE(tr.lowerExpr(R, fc));
  const v = tr.bindTemp(rhs, fc, 'd');
  // ECMA-262 order: for each element, the target reference is evaluated, then the next
  // value is taken and stored
  L.elements.forEach((el, i) => {
    if (ts.isOmittedExpression(el)) return;
    if (ts.isSpreadElement(el)) reject(el, 'unsupported-syntax', 'rest element in a destructuring assignment');
    const t = rhs.ty;
    const val = (): Expr => {
      if (t.k === 'tup') return E.getTup(E.var(v), i);
      if (t.k === 'arr') return E.builtin(`(.arrGet ${showTy(t.t)})`, [E.var(v), numLit(i)], [t, T.num], t.t);
      reject(R, 'unsupported', `destructuring assignment from ${prettyTy(t)}`);
    };
    tr.assignNode(skipParens(el), val, fc, el);
  });
  return null;
}

declare module './core' {
  interface Translator {
    /** Store a value into an assignment target (variable, field, array element); the
     * target's base and index are evaluated before the value thunk. */
    assignNode(target: ts.Expression, value: () => Expr, fc: FnCtx, node: ts.Node): void;
  }
}

P.assignNode = function (this: Translator, target, value, fc, node) {
  if (ts.isIdentifier(target)) {
    const sym = this.symAt(target);
    const bd = sym && this.lookup(sym, fc);
    if (!bd) reject(target, 'unsupported', `assignment to ${target.text}`);
    this.assignTo(bd, this.coerce(value(), this.bindingTy(bd), node), false, fc, node);
    return;
  }
  if (ts.isPropertyAccessExpression(target)) {
    const st = this.staticFieldGlobal(target);
    if (st) { fc.pre.push(stmtItem(S.gset(st, this.coerce(value(), st.ty, node)))); return; }
    const o = this.unfoldE(this.lowerExpr(target.expression, fc));
    if (o.ty.k !== 'obj') reject(node, o.ty.k === 'record' ? 'record-mutation' : 'unsupported', `assignment to property ${target.name.text} of ${prettyTy(o.ty)}`);
    const c = o.ty.c;
    const info = this.classOfObj(c);
    const idx = info?.fieldIdx.get(target.name.text);
    if (!info || idx === undefined) reject(node, 'unsupported', `no field ${target.name.text} on ${c}`);
    const fty = info.fields[idx].ty;
    const [ob, vv] = this.seq([() => o, () => this.coerce(value(), fty, node)], fc);
    fc.pre.push(stmtItem(S.setField(ob, c, idx, fty, vv)));
    return;
  }
  if (ts.isElementAccessExpression(target)) {
    const [a0, i0] = this.seq([() => this.unfoldE(this.lowerExpr(target.expression, fc)), () => this.lowerExpr(target.argumentExpression, fc, T.num)], fc);
    if (a0.ty.k !== 'arr') reject(node, 'unsupported', `element assignment on ${prettyTy(a0.ty)}`);
    const at = a0.ty;
    const [a, i, vv] = this.seq([() => a0, () => i0, () => this.coerce(value(), at.t, node)], fc);
    fc.pre.push(stmtItem(S.expr(E.builtin(`(.arrSet ${showTy(at.t)})`, [a, i, vv], [at, T.num, at.t], T.undef))));
    return;
  }
  reject(node, 'unsupported-syntax', 'destructuring assignment target');
};

P.lowerUpdate = function (this: Translator, u, fc, needValue) {
  const inc = u.operator === SK.PlusPlusToken;
  const prefix = ts.isPrefixUnaryExpression(u);
  const L = skipParens(u.operand);
  const step = (cur: Expr): Expr => {
    const c = this.unfoldE(cur);
    if (c.ty.k === 'num') return E.prim(`(.numBin .${inc ? 'add' : 'sub'})`, [c, numLit(1)], [T.num, T.num], T.num);
    if (c.ty.k === 'bigint') return E.prim(`(.bigBin .${inc ? 'add' : 'sub'})`, [c, bigLit(1n)], [T.bigint, T.bigint], T.bigint);
    reject(u, 'unsupported', `++/-- on ${prettyTy(c.ty)}`);
  };
  const run = (read: () => Expr, write: (v: Expr) => void): Expr | null => {
    if (!needValue) { write(step(read())); return null; }
    if (prefix) { const nv = this.bindTemp(step(read()), fc, 'nv'); write(E.var(nv)); return E.var(nv); }
    const old = this.bindTemp(read(), fc, 'old');
    write(step(E.var(old)));
    return E.var(old);
  };
  if (ts.isIdentifier(L)) {
    const sym = this.symAt(L);
    const bd = sym && this.lookup(sym, fc);
    if (!bd) reject(L, 'unsupported', `update of ${L.text}`);
    if (bd.k === 'poison') return needValue ? E.poison(bd.ty) : null;
    return run(() => this.readBinding(bd, L), v => { this.assignTo(bd, v, false, fc, u); });
  }
  if (ts.isPropertyAccessExpression(L)) {
    const st = this.staticFieldGlobal(L);
    if (st) return run(() => E.gget(st), v => { fc.pre.push(stmtItem(S.gset(st, v))); });
    const o0 = this.unfoldE(this.lowerExpr(L.expression, fc));
    if (isPoison(o0)) return needValue ? this.derivedPoison(u, fc) : null;
    if (o0.ty.k === 'dyn') reject(u, 'any-op', '++/-- on a property of a value of type any/unknown');
    if (o0.ty.k === 'dict') {
      const d = this.spill(o0, fc, 'd'), k = strLit(L.name.text);
      return run(() => this.dictRead(d, k, L, fc), v => { fc.pre.push(stmtItem(this.dictSetStmt(d, k, v))); });
    }
    if (o0.ty.k !== 'obj') reject(u, o0.ty.k === 'record' ? 'record-mutation' : 'unsupported', `update of property ${L.name.text} of ${prettyTy(o0.ty)}`);
    const c = o0.ty.c;
    const info = this.classOfObj(c);
    const idx = info?.fieldIdx.get(L.name.text);
    if (!info || idx === undefined) reject(u, 'unsupported', `no field ${L.name.text} on ${c}`);
    const fty = info.fields[idx].ty;
    const o = this.spill(o0, fc, 'o');
    return run(() => E.getField(o, c, idx, fty), v => { fc.pre.push(stmtItem(S.setField(o, c, idx, fty, v))); });
  }
  if (ts.isElementAccessExpression(L)) {
    const base = this.unfoldE(this.lowerExpr(L.expression, fc));
    if (isPoison(base)) { this.lowerExpr(L.argumentExpression, fc); return needValue ? this.derivedPoison(u, fc) : null; }
    if (base.ty.k === 'dyn') reject(u, 'any-op', '++/-- on an element of a value of type any/unknown');
    if (base.ty.k === 'dict') {
      const [d1, k1] = this.seq([() => base, () => this.dictKey(L.argumentExpression, fc)], fc);
      const d = this.spill(d1, fc, 'd'), k = this.spill(k1, fc, 'k');
      return run(() => this.dictRead(d, k, L, fc), v => { fc.pre.push(stmtItem(this.dictSetStmt(d, k, v))); });
    }
    if (base.ty.k === 'record' || base.ty.k === 'obj') reject(L, 'computed-key', `update of a computed property of ${prettyTy(base.ty)}`);
    const [a0, i0] = this.seq([() => base, () => this.lowerExpr(L.argumentExpression, fc, T.num)], fc);
    if (a0.ty.k !== 'arr') reject(u, 'unsupported', `++/-- on an element of ${prettyTy(a0.ty)}`);
    const at = a0.ty;
    const a = this.spill(a0, fc, 'a'), i = this.spill(i0, fc, 'i');
    return run(() => E.builtin(`(.arrGet ${showTy(at.t)})`, [a, i], [at, T.num], at.t),
      v => { fc.pre.push(stmtItem(S.expr(E.builtin(`(.arrSet ${showTy(at.t)})`, [a, i, v], [at, T.num, at.t], T.undef)))); });
  }
  reject(u, 'unsupported-syntax', '++/-- target');
};

P.lowerAwaitOperand = function (this: Translator, a, fc) {
  if (fc.kind === 'main') reject(a, 'top-level-await', 'top-level `await` is not supported; use an async function');
  if (!fc.async) reject(a, 'unsupported', '`await` outside an async function');
  const e = this.lowerExpr(a.expression, fc);
  if (isPoison(e)) {
    let t: Ty = T.undef;
    try { t = this.tyAt(a, fc); } catch { /* unknown */ }
    return E.poison(T.promise(t));
  }
  if (e.ty.k === 'promise') return e;
  return E.builtin(`(.promResolve ${showTy(e.ty)})`, [e], [e.ty], T.promise(e.ty));
};

// ---------------------------------------------------------------------------------------
// literals

P.lowerArrayLit = function (this: Translator, n, fc, exp) {
  let target = exp ?? this.tyAt(n, fc);
  if (target.k === 'opt') return E.some(this.lowerArrayLit(n, fc, target.t));
  if (target.k === 'named') return E.fold(target.n, this.lowerArrayLit(n, fc, this.aliasOf(target.n)));
  if (target.k === 'union') {
    const nat = this.tyAt(n, fc);
    if (nat.k === 'union') reject(n, 'unsupported', 'array literal of a union type');
    return this.coerce(this.lowerArrayLit(n, fc, nat), target, n);
  }
  if (target.k === 'tup') {
    const tt = target;
    if (n.elements.length !== tt.ts.length || n.elements.some(ts.isSpreadElement)) reject(n, 'unsupported', 'tuple literal does not match the tuple type');
    const parts = this.seq(n.elements.map((el, i) => () => this.lowerExpr(el, fc, tt.ts[i])), fc);
    return E.mkTup(parts);
  }
  if (target.k === 'set' || target.k === 'map') reject(n, 'unsupported', 'array literal used as a Set/Map');
  if (target.k !== 'arr') reject(n, 'unsupported', `array literal of type ${prettyTy(target)}`);
  const el = target.t;
  if (n.elements.some(e => e.kind === SK.OmittedExpression)) reject(n, 'no-sparse', 'array holes are not allowed');
  if (!n.elements.some(ts.isSpreadElement)) {
    const parts = this.seq(n.elements.map(e => () => this.lowerExpr(e, fc, el)), fc);
    return E.builtin(`(.arrOf ${showTy(el)} ${parts.length})`, parts, parts.map(() => el), target);
  }
  // segments: runs of plain elements and spreads
  const segs: { spread: boolean; nodes: ts.Expression[] }[] = [];
  for (const e of n.elements) {
    if (ts.isSpreadElement(e)) segs.push({ spread: true, nodes: [e.expression] });
    else if (segs.length && !segs[segs.length - 1].spread) segs[segs.length - 1].nodes.push(e);
    else segs.push({ spread: false, nodes: [e] });
  }
  const at = target;
  const segExprs = this.seq(segs.map((sg, si) => () => {
    if (!sg.spread) {
      const parts = this.seq(sg.nodes.map(e => () => this.lowerExpr(e, fc, el)), fc);
      return E.builtin(`(.arrOf ${showTy(el)} ${parts.length})`, parts, parts.map(() => el), at);
    }
    const src = this.spreadSource(sg.nodes[0], fc, el);
    // snapshot when later segments may run code
    const later = segs.slice(si + 1);
    if (src.fresh || later.length === 0) return src.e;
    return E.builtin(`(.arrCopy ${showTy(el)})`, [src.e], [at], at);
  }), fc);
  let acc = segExprs[0];
  if (segs[0].spread && segs.length === 1 && !this.spreadSource(segs[0].nodes[0], fc, el, true).fresh) {
    acc = E.builtin(`(.arrCopy ${showTy(el)})`, [acc], [at], at);
  }
  for (let i = 1; i < segExprs.length; i++) acc = E.builtin(`(.arrConcat ${showTy(el)})`, [acc, segExprs[i]], [at, at], at);
  return acc;
};

declare module './core' {
  interface Translator {
    /** Elements of a spread `...x` as an array (fresh = a new array was allocated). */
    spreadSource(n: ts.Expression, fc: FnCtx, el: Ty, dryRun?: boolean): { e: Expr; fresh: boolean };
  }
}

P.spreadSource = function (this: Translator, n, fc, el, dryRun = false) {
  const it = skipParens(n);
  if (ts.isCallExpression(it) && ts.isPropertyAccessExpression(it.expression) && it.arguments.length === 0) {
    const m = it.expression.name.text;
    const rt = this.unfoldTy(this.tyAt(it.expression.expression, fc));
    if ((rt.k === 'map' && ['keys', 'values', 'entries'].includes(m)) || (rt.k === 'set' && ['keys', 'values'].includes(m))) {
      if (dryRun) return { e: E.undef(), fresh: true };
      const base = this.lowerExpr(it.expression.expression, fc);
      return { e: this.coerce(this.collectionSnapshot(base, m, it), T.arr(el), n), fresh: true };
    }
  }
  if (dryRun) {
    const t = this.unfoldTy(this.tyAt(it, fc));
    return { e: E.undef(), fresh: t.k === 'set' || t.k === 'map' || t.k === 'str' || t.k === 'enum' };
  }
  const e = this.unfoldE(this.lowerExpr(it, fc));
  if (e.ty.k === 'arr') {
    if (!tyEq(e.ty.t, el)) reject(n, 'unsupported', `spread of ${prettyTy(e.ty)} into ${prettyTy(T.arr(el))}`);
    return { e, fresh: false };
  }
  if (e.ty.k === 'str' || e.ty.k === 'enum') return { e: this.coerce(this.codePoints(e, fc, n), T.arr(el), n), fresh: true };
  if (e.ty.k === 'tup') return { e: this.coerce(e, T.arr(el), n), fresh: true };
  if (e.ty.k === 'set') return { e: this.coerce(this.collectionSnapshot(e, 'values', n), T.arr(el), n), fresh: true };
  if (e.ty.k === 'map') return { e: this.coerce(this.collectionSnapshot(e, 'entries', n), T.arr(el), n), fresh: true };
  reject(n, e.ty.k === 'dyn' ? 'any-op' : 'unsupported', `spread of ${prettyTy(e.ty)}`);
};

declare module './core' {
  interface Translator {
    /** The code points of a string as a fresh array (`[...s]`, `Array.from(s)`). */
    codePoints(e: Expr, fc: FnCtx, node: ts.Node): Expr;
  }
}

P.codePoints = function (this: Translator, e, fc, node) {
  const str = this.spill(this.toStr(e, node), fc, 's');
  const out = mkVar('cps', T.arr(T.str));
  fc.pre.push(declItem(out, E.builtin('(.arrOf .str 0)', [], [], T.arr(T.str))));
  const ch = mkVar('ch', T.str);
  fc.pre.push(stmtItem({ k: 'forOfStr', e: str, v: ch, body: [stmtItem(S.expr(E.builtin('(.arrPush .str)', [E.var(out), E.var(ch)], [T.arr(T.str), T.str], T.num)))] }));
  return E.var(out);
};

P.lowerObjectLit = function (this: Translator, n, fc, exp) {
  const target = exp ?? this.tyAt(n, fc);
  if (target.k === 'box' && target.t.k === 'record') {
    // an object compared by identity (identity.ts): a new cell at each evaluation
    const r = this.lowerObjectLit(n, fc, target.t);
    return E.builtin(`(.boxNew ${showTy(target.t)})`, [r], [target.t], target);
  }
  if (target.k === 'opt') return E.some(this.lowerObjectLit(n, fc, target.t));
  if (target.k === 'named') return E.fold(target.n, this.lowerObjectLit(n, fc, this.aliasOf(target.n)));
  if (target.k === 'dict') return this.lowerDictLit(n, target, fc);
  if (target.k === 'union') {
    // pick the member TypeScript assigns the literal to
    const litT = this.checker.getTypeAtLocation(n);
    const ctx = this.checker.getContextualType(n);
    const members = ctx && ctx.isUnion() ? ctx.types : [];
    for (const m of members) {
      if (m.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null)) continue;
      if (!this.checker.isTypeAssignableTo(litT, m)) continue;
      const mt = this.tyOf(m, fc, n);
      const idx = target.ts.findIndex(x => tyEq(x, mt));
      if (idx >= 0) return E.inj(target, idx, this.lowerObjectLit(n, fc, mt));
    }
    const nat = this.tyOf(litT, fc, n);
    if (nat.k === 'union' || nat.k === 'opt' || nat.k === 'named') reject(n, 'unsupported', `object literal of type ${prettyTy(target)} that matches no single member`);
    return this.coerce(this.lowerObjectLit(n, fc, nat), target, n);
  }
  // providers in source order
  interface Prov { name?: string; node: ts.Node; thunk: () => Expr; spreadOf?: Ty }
  const fields: { name: string; ty: Ty }[] = target.k === 'record' ? target.fs
    : target.k === 'obj' ? (this.classOfObj(target.c)?.fields ?? []) : [];
  if (target.k === 'obj') {
    if (this.types.classes.has(target.c)) reject(n, 'unsupported', `object literal used as an instance of class ${target.c}`);
  } else if (target.k === 'ext') reject(n, 'ext-literal', `object literal used as a value of the external type ${target.name}`);
  else if (target.k !== 'record') reject(n, 'unsupported', `object literal of type ${prettyTy(target)}`);
  const fieldTy = (name: string): Ty | undefined => fields.find(f => f.name === name)?.ty;
  const provs: Prov[] = [];
  for (const p of n.properties) {
    if (ts.isPropertyAssignment(p) || ts.isShorthandPropertyAssignment(p)) {
      const key = p.name;
      if (!ts.isIdentifier(key) && !ts.isStringLiteral(key) && !ts.isNumericLiteral(key)) reject(p, 'unsupported-syntax', 'computed property name');
      const name = key.text;
      const ft = fieldTy(name);
      if (!ft) reject(p, 'unsupported', `property ${name} is not part of ${prettyTy(target)}`);
      const valNode = ts.isPropertyAssignment(p) ? p.initializer : p.name;
      provs.push({ name, node: p, thunk: () => this.lowerExpr(valNode, fc, ft) });
    } else if (ts.isMethodDeclaration(p)) {
      if (!ts.isIdentifier(p.name)) reject(p, 'unsupported-syntax', 'computed method name');
      const name = p.name.text;
      const ft = fieldTy(name);
      if (!ft) reject(p, 'unsupported', `method ${name} is not part of ${prettyTy(target)}`);
      provs.push({ name, node: p, thunk: () => this.lowerLambda(p as unknown as ts.FunctionExpression, fc, ft) });
    } else if (ts.isSpreadAssignment(p)) {
      // `...(c ? { k: v } : {})` / `...(c && { k: v })`: the empty object contributes nothing,
      // so the spread is an optional value of the other branch (TypeScript's type of the
      // conditional adds `k?: undefined` to `{}`, which would read as a property)
      const se = skipParens(p.expression);
      const isEmptyLit = (x: ts.Expression) => { const y = skipParens(x); return ts.isObjectLiteralExpression(y) && y.properties.length === 0; };
      let cond: ts.Expression | undefined, branch: ts.Expression | undefined, flip = false;
      if (ts.isConditionalExpression(se) && (isEmptyLit(se.whenTrue) !== isEmptyLit(se.whenFalse))) {
        cond = se.condition; flip = isEmptyLit(se.whenTrue); branch = flip ? se.whenFalse : se.whenTrue;
      } else if (ts.isBinaryExpression(se) && se.operatorToken.kind === SK.AmpersandAmpersandToken && ts.isObjectLiteralExpression(skipParens(se.right))) {
        cond = se.left; branch = se.right;
      }
      if (cond && branch) {
        const c0 = cond, b0 = branch, fl = flip;
        provs.push({ node: p, thunk: () => {
          const c = this.lowerCond(c0, fc);
          const bt = this.tyAt(b0, fc);
          // (the branch is evaluated only when taken)
          const saved = fc.pre;
          const items: Item[] = [];
          fc.pre = items;
          let bv: Expr;
          try { bv = this.lowerExpr(b0, fc, bt); } finally { fc.pre = saved; }
          const r = mkVar('sp', T.opt(bt));
          fc.pre.push(declItem(r, E.none(bt)));
          r.assigned = true;
          fc.pre.push(stmtItem(S.ite(fl ? E.not(c) : c, [...items, stmtItem(S.assign(r, E.some(bv)))], [])));
          return E.var(r);
        } });
      } else provs.push({ node: p, thunk: () => this.unfoldE(this.lowerExpr(p.expression, fc)) });
    } else reject(p, 'unsupported-syntax', 'getters/setters in object literals');
  }
  const vals = this.seq(provs.map(pv => pv.thunk), fc);
  // JavaScript evaluates the initialisers in source order, the value is built in field order:
  // with more than one effect, every initialiser is evaluated into a temporary first (spreads
  // always are, so that several fields can be read; overridden values only for their effects)
  // (a spread has no name; the property name "" is a name)
  const effects = provs.filter((pv, i) => pv.name === undefined || !isStable(vals[i])).length;
  // a spread source: records, dictionaries, objects (their fields read at the spread, as a
  // record), and optional values and unions of those (`...(opts ?? {})`, `...(c ? a : b)`)
  const spreadable = (t0: Ty): boolean => {
    const t = this.unfoldTy(t0);
    switch (t.k) {
      case 'record': case 'dict': case 'undef': case 'null': return true;
      case 'box': return t.t.k === 'record';
      case 'obj': return !!this.classOfObj(t.c);
      case 'opt': return spreadable(t.t);
      case 'union': return t.ts.every(spreadable);
      default: return false;
    }
  };
  provs.forEach((pv, i) => {
    if (pv.name === undefined) {
      let sv = this.unfoldE(vals[i]);
      if (sv.ty.k === 'box' && sv.ty.t.k === 'record') sv = this.unboxCell(sv);
      if (sv.ty.k === 'obj') {
        // CopyDataProperties reads the own properties now: a record of the fields
        const info = this.classOfObj(sv.ty.c)!;
        const c = sv.ty.c;
        const o = E.var(this.bindTemp(sv, fc, 'so'));
        const fs = sortFields(info.fields);
        sv = E.mkRec(T.record(fs), fs.map(f => { const idx = info.fields.findIndex(g => g.name === f.name); return E.getField(o, c, idx, f.ty); }));
      }
      const v = this.bindTemp(sv, fc, 'sp');
      vals[i] = E.var(v);
      if (!spreadable(vals[i].ty)) reject(pv.node, vals[i].ty.k === 'dyn' ? 'any-op' : 'unsupported', `spread of ${prettyTy(vals[i].ty)}`);
    } else if (effects > 1 && !isStable(vals[i])) {
      if (provs.slice(i + 1).some(q => q.name === pv.name)) { fc.pre.push(stmtItem(S.expr(vals[i]))); vals[i] = E.undef(); }
      else vals[i] = E.var(this.bindTemp(vals[i], fc, 'fv'));
    }
  });
  // the value of field f from the providers up to i (the last one that has f wins; whether a
  // spread dictionary has f is decided at run time)
  // the field f from a spread value at provider i, else from the providers before it
  const fromSpread = (v0: Expr, f: { name: string; ty: Ty }, i: number, node: ts.Node): Expr => {
    const v = this.unfoldE(v0);
    const t = v.ty;
    switch (t.k) {
      case 'record': {
        const j = t.fs.findIndex(g => g.name === f.name);
        if (j < 0) return provide(f, i - 1);
        if (t.fs[j].ty.k === 'opt' && f.ty.k !== 'opt') {
          reject(node, 'spread-optional', `spread of an optional field ${f.name}: JavaScript keeps an explicit undefined, records cannot tell it from a missing field`);
        }
        return this.coerce(E.getRec(v, j), f.ty, node);
      }
      case 'dict': {
        const key = strLit(f.name);
        const got = this.dictGetOpt(v, key);
        const val = f.ty.k === 'opt' ? this.coerce(got, f.ty, node) : this.coerce(E.unwrap(got), f.ty, node);
        return E.cond(E.builtin(`(.dictHasOwn ${showTy(t.t)})`, [v, key], [t, T.str], T.bool), val, provide(f, i - 1));
      }
      case 'undef': case 'null': return provide(f, i - 1);
      case 'box': if (t.t.k === 'record') return fromSpread(this.unboxCell(v), f, i, node); break;
      case 'opt': {
        const x = mkVar('s', t.t);
        return E.caseOpt(v, provide(f, i - 1), x, fromSpread(E.var(x), f, i, node));
      }
      case 'union': return E.caseU(v, t.ts.map(m => { const x = mkVar('s', m); return { v: x, body: fromSpread(E.var(x), f, i, node) }; }));
    }
    reject(node, 'unsupported', `spread of ${prettyTy(t)}`);
  };
  // the value of field f from the providers up to `upto` (the last one that has f wins; for
  // dictionaries, optional values and unions that is decided at run time)
  // can a spread value of type t provide the field? (a record has exactly its fields; whether
  // a dictionary has the key is decided at run time)
  const mayHave = (t0: Ty, name: string): boolean => {
    const t = this.unfoldTy(t0);
    switch (t.k) {
      case 'record': return t.fs.some(g => g.name === name);
      case 'box': case 'opt': return mayHave(t.t, name);
      case 'union': return t.ts.some(m => mayHave(m, name));
      case 'undef': case 'null': return false;
      default: return true;
    }
  };
  const provide = (f: { name: string; ty: Ty }, upto: number): Expr => {
    for (let i = upto; i >= 0; i--) {
      const pv = provs[i];
      if (pv.name === f.name) return vals[i];
      if (pv.name === undefined) {
        // a spread that cannot have f (a record without it, also optional or in a union): look
        // further back without a case split (with one, both branches would hold the providers
        // before it: exponential in the number of such spreads)
        if (!mayHave(vals[i].ty, f.name)) continue;
        return fromSpread(vals[i], f, i, pv.node);
      }
    }
    if (f.ty.k === 'opt') return E.none(f.ty.t);
    if (f.ty.k === 'undef') return E.undef();
    // (only after a spread that may lack the field at run time: TypeScript's types were wrong)
    if (provs.slice(0, upto + 1).some((pv, i) => pv.name === undefined && this.unfoldTy(vals[i].ty).k !== 'record')) return E.unreachable(f.ty);
    reject(n, 'unsupported', `missing property ${f.name}`);
  };
  const fieldVals = fields.map(f => provide(f, provs.length - 1));
  // evaluated values that are not used (overridden properties) are kept for their effects
  // (the only effect, else they were evaluated above)
  provs.forEach((pv, i) => {
    if (pv.name !== undefined && !fieldVals.includes(vals[i]) && !isStable(vals[i])) fc.pre.push(stmtItem(S.expr(vals[i])));
  });
  if (target.k === 'record') return E.mkRec(target, fieldVals);
  const ms = this.types.mutStructs.find(m => m.name === target.c)!;
  return E.call(this.structCtor(ms, n), fieldVals);
};

P.lowerCallArgs = function (this: Translator, specs, args, fc, node, prefix) {
  const thunks: (() => Expr)[] = [...prefix];
  const restIdx = specs.findIndex(s => s.rest);
  const nFixed = restIdx >= 0 ? restIdx : specs.length;
  for (let i = 0; i < nFixed; i++) {
    const sp = specs[i];
    if (i < args.length) {
      if (ts.isSpreadElement(args[i])) reject(args[i], 'unsupported', 'spread argument to a non-rest parameter');
      thunks.push(() => this.lowerExpr(args[i], fc, sp.ty));
    } else if (sp.ty.k === 'opt') thunks.push(() => E.none((sp.ty as Extract<Ty, { k: 'opt' }>).t));
    else if (sp.ty.k === 'undef') thunks.push(() => E.undef());
    else reject(node, 'unsupported', 'missing argument');
  }
  if (restIdx >= 0) {
    const at = specs[restIdx].ty as Extract<Ty, { k: 'arr' }>;
    const rest = args.slice(nFixed);
    if (rest.length === 1 && ts.isSpreadElement(rest[0])) {
      const sp = rest[0] as ts.SpreadElement;
      thunks.push(() => {
        const src = this.spreadSource(sp.expression, fc, at.t);
        return src.fresh ? src.e : E.builtin(`(.arrCopy ${showTy(at.t)})`, [src.e], [at], at);
      });
    } else {
      if (rest.some(ts.isSpreadElement)) reject(node, 'unsupported', 'spread mixed with other rest arguments');
      thunks.push(() => {
        const parts = this.seq(rest.map(a => () => this.lowerExpr(a, fc, at.t)), fc);
        return E.builtin(`(.arrOf ${showTy(at.t)} ${parts.length})`, parts, parts.map(() => at.t), at);
      });
    }
  } else if (args.length > specs.length) reject(args[specs.length], 'unsupported', 'too many arguments');
  return this.seq(thunks, fc);
};


// Statement lowering.
import * as ts from 'typescript';
import { Ty, T, tyEq, prettyTy, isObjectLike } from './ty';
import { Expr, Stmt, Item, Block, VarInfo, E, S, mkVar, declItem, stmtItem, awaitItem, blockAlwaysAbrupt, InternalError, isStable, isPoison } from './ir';
import { isFatal } from './exprs';
import { isTypeOnlyAmbient } from './check';
import { reject } from './diag';
import { Translator, FnCtx, Binding, Jump, within, numLit, bigLit, strLit, isLibDecl } from './core';

declare module './core' {
  interface Translator {
    lowerBlockStmts(stmts: readonly ts.Statement[], fc: FnCtx): Block;
    lowerSubStmt(s: ts.Statement, fc: FnCtx): Block;
    lowerStmtList(stmts: readonly ts.Statement[], i: number, fc: FnCtx, out: Item[]): void;
    lowerStmt(s: ts.Statement, fc: FnCtx, out: Item[], labels?: string[]): void;
    lowerVarDecl(d: ts.VariableDeclaration, isConst: boolean, fc: FnCtx, out: Item[]): void;
    bindPattern(p: ts.BindingName, value: Expr, fc: FnCtx, out: Item[], isConst: boolean): void;
    lowerExprStmt(e: ts.Expression, fc: FnCtx, out: Item[]): void;
    narrowTest(cond: ts.Expression, fc: FnCtx): NarrowTest | null;
    applyNarrow(t: NarrowTest, thenB: (fc: FnCtx) => Block, elseB: (fc: FnCtx) => Block, fc: FnCtx): Stmt;
    breakDepth(fc: FnCtx, label: string | undefined, node: ts.Node): number;
    contDepth(fc: FnCtx, label: string | undefined, node: ts.Node): number;
    hoistFunctions(stmts: readonly ts.Statement[], fc: FnCtx): void;
    isRebindable(sym: ts.Symbol, fc: FnCtx, region: ts.Node | ts.Node[]): Binding | null;
  }
}

/** A narrowing test on a variable: which members of its type go to the `then` branch. */
export interface NarrowTest {
  sym: ts.Symbol;
  scrut: Expr;              // the variable read (its stored type)
  /** opt: `thenSome` = the `then` branch receives the defined value */
  kind: 'opt' | 'union';
  thenSome?: boolean;
  /** union: per member, does it go to `then`? */
  toThen?: boolean[];
  node: ts.Node;
}

const P = Translator.prototype;

function skipParens(e: ts.Expression): ts.Expression {
  while (ts.isParenthesizedExpression(e)) e = e.expression;
  return e;
}

function hasDecls(b: Block): boolean { return b.some(it => it.k !== 'stmt'); }

P.lowerBlockStmts = function (this: Translator, stmts, fc) {
  fc.push();
  try {
    if (this.coverage) {
      try { this.hoistFunctions(stmts, fc); } catch (e) {
        if (isFatal(e)) throw e;
        this.covRecord(e, stmts[0]);
        this.poisonCount++;
        for (const st of stmts) if (ts.isFunctionDeclaration(st) && st.name) { const sym = this.symAt(st.name); if (sym && !this.lookup(sym, fc)) fc.bind(sym, { k: 'poison', ty: T.undef }); }
      }
    } else this.hoistFunctions(stmts, fc);
    const out: Item[] = [];
    this.lowerStmtList(stmts, 0, fc, out);
    return out;
  } finally { fc.pop(); }
};

P.lowerSubStmt = function (this: Translator, s, fc) {
  if (ts.isBlock(s)) return this.lowerBlockStmts(s.statements, fc);
  return this.lowerBlockStmts([s], fc);
};

P.lowerStmtList = function (this: Translator, stmts, i, fc, out) {
  for (; i < stmts.length; i++) {
    const s = stmts[i];
    if (unionGuardChain(this, stmts, i, fc, out)) return;
    if (ts.isIfStatement(s) && !s.elseStatement && i + 1 < stmts.length) {
      // early-exit guards: `if (A || B || …) { …abrupt… }` narrows the rest of the block;
      // it is processed as the guards `if (A) …; if (B) …; …` (B runs only when A is false)
      const conds = orOperands(s.expression);
      const small = tsStmtCount(s.thenStatement) <= 2;
      if ((conds.length === 1 || small) && conds.some(c => this.narrowTest(c, fc) !== null)) {
        const thenBlock = this.lowerSubStmt(s.thenStatement, fc);
        if (blockAlwaysAbrupt(thenBlock)) {
          lowerGuardChain(this, conds, s.thenStatement, small, stmts, i + 1, fc, out);
          return;
        }
      }
    }
    this.lowerStmt(s, fc, out);
  }
};

function mentions(tr: Translator, n: ts.Node, sym: ts.Symbol): boolean {
  let found = false;
  const visit = (c: ts.Node): void => {
    if (found) return;
    if (ts.isIdentifier(c) && tr.symAt(c) === sym) { found = true; return; }
    ts.forEachChild(c, visit);
  };
  visit(n);
  return found;
}

/** Consecutive guards `if (x.kind === …) return …;` on the same union variable become one
 * caseUS: each member runs the block of the first guard that catches it, the member no
 * guard catches runs the rest of the block. */
function unionGuardChain(tr: Translator, stmts: readonly ts.Statement[], i: number, fc: FnCtx, out: Item[]): boolean {
  const guards: { s: ts.IfStatement; caught: number[] }[] = [];
  let sym: ts.Symbol | undefined;
  let scrut: Expr | undefined;
  let remaining: number[] = [];
  let j = i;
  for (; j < stmts.length; j++) {
    const st = stmts[j];
    if (!ts.isIfStatement(st) || st.elseStatement) break;
    const test = tr.narrowTest(st.expression, fc);
    if (!test || test.kind !== 'union') break;
    if (sym && test.sym !== sym) break;
    if (!sym) {
      sym = test.sym;
      scrut = test.scrut;
      remaining = (test.scrut.ty as Extract<Ty, { k: 'union' }>).ts.map((_, k) => k);
    }
    if (!tsAlwaysAbrupt(st.thenStatement)) break;
    const caught = remaining.filter(k => test.toThen![k]);
    if (caught.length > 1 && (tsStmtCount(st.thenStatement) > 2 || mentions(tr, st.thenStatement, sym))) break;
    guards.push({ s: st, caught });
    remaining = remaining.filter(k => !test.toThen![k]);
    if (remaining.length <= 1) { j++; break; }
  }
  if (guards.length < 2 || remaining.length > 1 || !sym || !scrut) return false;
  const rest = stmts.slice(j);
  if (!tr.isRebindable(sym, fc, [...guards.map(g => g.s), ...rest])) return false;
  const u = scrut.ty as Extract<Ty, { k: 'union' }>;
  const alts = u.ts.map((m, k) => {
    const v = mkVar(sym!.name, m);
    fc.push();
    fc.bind(sym!, { k: 'var', v });
    try {
      const g = guards.find(gd => gd.caught.includes(k));
      if (g) return { v, body: tr.lowerSubStmt(g.s.thenStatement, fc) };
      const items: Item[] = [];
      tr.hoistFunctions(rest, fc);
      tr.lowerStmtList(stmts, j, fc, items);
      return { v, body: items };
    } finally { fc.pop(); }
  });
  out.push(stmtItem({ k: 'caseUS', e: scrut, alts }));
  return true;
}

function orOperands(e: ts.Expression): ts.Expression[] {
  const x = skipParens(e);
  if (ts.isBinaryExpression(x) && x.operatorToken.kind === ts.SyntaxKind.BarBarToken) return [...orOperands(x.left), ...orOperands(x.right)];
  return [x];
}

function tsStmtCount(s: ts.Statement): number {
  return ts.isBlock(s) ? s.statements.length : 1;
}

/** Guards `if (c_k) S` for k = 0.., then the rest of the block; narrowing guards become
 * caseOptS/caseUS with the rest in the branch where the variable is narrowed. */
function lowerGuardChain(tr: Translator, conds: ts.Expression[], thenS: ts.Statement, small: boolean,
    stmts: readonly ts.Statement[], restIdx: number, fc: FnCtx, out: Item[]): void {
  const rest = stmts.slice(restIdx);
  const go = (k: number, fc2: FnCtx, out2: Item[]): void => {
    if (k === conds.length) {
      fc2.push();
      try { tr.hoistFunctions(rest, fc2); tr.lowerStmtList(stmts, restIdx, fc2, out2); } finally { fc2.pop(); }
      return;
    }
    const later = [...conds.slice(k + 1), ...rest];
    const test = tr.narrowTest(conds[k], fc2);
    // the `then` block may be duplicated per union member only if it does not use the
    // variable (TypeScript could narrow it differently inside)
    const dupOk = small && !!test && !mentions(tr, thenS, test.sym);
    if (test && tr.isRebindable(test.sym, fc2, later) && guardOk(test, dupOk)) {
      out2.push(stmtItem(tr.applyNarrow(test, () => tr.lowerSubStmt(thenS, fc2), (fc3) => {
        const items: Item[] = [];
        go(k + 1, fc3, items);
        return items;
      }, fc2)));
      return;
    }
    const saved = fc2.pre;
    fc2.pre = out2;
    let restNarrow = false;
    try {
      if (test && tr.isRebindable(test.sym, fc2, thenS) && narrowNoDup(test, false)) {
        // narrow inside the guard only (the rest stays outside the case split)
        out2.push(stmtItem(tr.applyNarrow(test, () => tr.lowerSubStmt(thenS, fc2), () => [], fc2)));
      } else {
        const c = tr.lowerCond(conds[k], fc2);
        const unionTest = !!test && test.kind === 'union';
        const thenB = unionTest && tr.isRebindable(test!.sym, fc2, thenS)
          ? tr.withNarrowed(test!, true, fc2, () => tr.lowerSubStmt(thenS, fc2)) : tr.lowerSubStmt(thenS, fc2);
        out2.push(stmtItem(S.ite(c, thenB, [])));
        restNarrow = unionTest && !!tr.isRebindable(test!.sym, fc2, later);
      }
    } finally { fc2.pre = saved; }
    if (restNarrow) {
      // after the guard the variable has the remaining members: rebind it once
      const items = tr.withNarrowed(test!, false, fc2, () => { const xs: Item[] = []; go(k + 1, fc2, xs); return xs; });
      out2.push(...items);
      return;
    }
    go(k + 1, fc2, out2);
  };
  go(0, fc, out);
}

/** A guard is restructured when the rest of the block goes to at most one union member
 * (no duplication of the rest); the abrupt `then` block may be duplicated when small. */
function guardOk(t: NarrowTest, smallThen = false): boolean {
  if (t.kind === 'opt') return true;
  const th = (t.toThen ?? []).filter(x => x).length;
  return (th <= 1 || smallThen) && (t.toThen ?? []).length - th <= 1;
}

P.isRebindable = function (this: Translator, sym, fc, region) {
  const b = this.lookup(sym, fc);
  if (!b || b.k !== 'var' || b.errVar) return null;
  if (this.writtenWithin(sym, region)) return null;
  if (b.v.ty.k !== 'opt' && b.v.ty.k !== 'union' && b.v.ty.k !== 'named') return null;
  return b;
};

P.lowerStmt = function (this: Translator, s, fc, out, labels = []) {
  const saved = fc.pre;
  fc.pre = out;
  try {
    if (!this.coverage) { lowerStmt1(this, s, fc, out, labels); return; }
    // coverage mode: record the violation, skip the statement, and give the variables it
    // declares placeholder values
    const mark = this.poisonCount;
    try {
      lowerStmt1(this, s, fc, out, labels);
    } catch (e) {
      if (isFatal(e)) throw e;
      if (this.poisonCount === mark) this.covRecord(e, s);
      this.poisonCount++;
      bindDeclaredPoison(this, s, fc);
    }
  } finally { fc.pre = saved; }
};

/** Coverage mode: the variables declared by a statement that could not be translated. */
function bindDeclaredPoison(tr: Translator, s: ts.Statement, fc: FnCtx): void {
  if (!ts.isVariableStatement(s)) return;
  for (const d of s.declarationList.declarations) bindPatternPoison(tr, d.name, fc);
}

export function bindPatternPoison(tr: Translator, p: ts.BindingName, fc: FnCtx): void {
  if (ts.isIdentifier(p)) {
    const sym = tr.symAt(p);
    if (!sym) return;
    let ty: Ty = T.undef;
    try { ty = tr.tyOf(tr.checker.getTypeOfSymbol(sym), fc, p); } catch { /* unknown */ }
    fc.bind(sym, { k: 'poison', ty });
    return;
  }
  for (const el of p.elements) if (!ts.isOmittedExpression(el)) bindPatternPoison(tr, el.name, fc);
}

function lowerStmt1(tr: Translator, s: ts.Statement, fc: FnCtx, out: Item[], labels: string[]): void {
  switch (s.kind) {
    case ts.SyntaxKind.VariableStatement: {
      const vs = s as ts.VariableStatement;
      const flags = vs.declarationList.flags;
      const kind = flags & ts.NodeFlags.BlockScoped;
      if (kind === 0) reject(s, 'no-var', '`var` declarations are not allowed; use `let` or `const`');
      if (kind !== ts.NodeFlags.Let && kind !== ts.NodeFlags.Const) reject(s, 'unsupported-syntax', '`using` declarations');
      for (const d of vs.declarationList.declarations) tr.lowerVarDecl(d, kind === ts.NodeFlags.Const, fc, out);
      return;
    }
    case ts.SyntaxKind.ExpressionStatement:
      tr.lowerExprStmt((s as ts.ExpressionStatement).expression, fc, out);
      return;
    case ts.SyntaxKind.IfStatement: {
      const is = s as ts.IfStatement;
      const test = tr.narrowTest(is.expression, fc);
      if (test) {
        const regions: ts.Node[] = [is.thenStatement, ...(is.elseStatement ? [is.elseStatement] : [])];
        if (tr.isRebindable(test.sym, fc, regions) && narrowNoDup(test, !!is.elseStatement)) {
          out.push(stmtItem(tr.applyNarrow(test, () => tr.lowerSubStmt(is.thenStatement, fc),
            () => is.elseStatement ? tr.lowerSubStmt(is.elseStatement, fc) : [], fc)));
          return;
        }
      }
      const c = tr.lowerCond(is.expression, fc);
      if (test && test.kind === 'union' && tr.isRebindable(test.sym, fc, [is.thenStatement, ...(is.elseStatement ? [is.elseStatement] : [])])) {
        // narrow once per branch: the variable is rebound to the narrowed (sub-)union
        const t = tr.withNarrowed(test, true, fc, () => tr.lowerSubStmt(is.thenStatement, fc));
        const f = is.elseStatement ? tr.withNarrowed(test, false, fc, () => tr.lowerSubStmt(is.elseStatement!, fc)) : [];
        out.push(stmtItem(S.ite(c, t, f)));
        return;
      }
      const t = tr.lowerSubStmt(is.thenStatement, fc);
      const f = is.elseStatement ? tr.lowerSubStmt(is.elseStatement, fc) : [];
      out.push(stmtItem(S.ite(c, t, f)));
      return;
    }
    case ts.SyntaxKind.Block: {
      const b = tr.lowerBlockStmts((s as ts.Block).statements, fc);
      if (hasDecls(b)) out.push(stmtItem({ k: 'block', b }));
      else out.push(...b);
      return;
    }
    case ts.SyntaxKind.EmptyStatement:
    case ts.SyntaxKind.InterfaceDeclaration:
    case ts.SyntaxKind.TypeAliasDeclaration:
    case ts.SyntaxKind.ImportDeclaration:
    case ts.SyntaxKind.ImportEqualsDeclaration:
      return;
    case ts.SyntaxKind.ExportDeclaration:
      return;
    case ts.SyntaxKind.FunctionDeclaration: {
      // hoisted (top-level FunDef or lambda-lifted); a nested function compared by identity
      // (identity.ts) gets its one cell here, for the references after its declaration
      const fd = s as ts.FunctionDeclaration;
      const sym = fd.name && tr.symAt(fd.name);
      const b = sym && tr.lookup(sym, fc);
      if (b && b.k === 'lifted' && fd.name) {
        let want: Ty | undefined;
        try { want = tr.tyAt(fd.name, fc); } catch { want = undefined; }
        if (want && want.k === 'box' && want.t.k === 'fn') {
          const saved = fc.pre;
          fc.pre = out;
          try {
            const clo = tr.liftedAsValue(b, fd.name, fc, want.t);
            const cell = mkVar(`${fd.name.text}$fn`, want);
            out.push(declItem(cell, E.builtin(`(.boxNew ${showT(want.t)})`, [clo], [want.t], want)));
            b.cell = cell;
          } finally { fc.pre = saved; }
        }
      }
      return;
    }
    case ts.SyntaxKind.ClassDeclaration:
      tr.lowerClassDeclStmt(s as ts.ClassDeclaration, fc, out);
      return;
    case ts.SyntaxKind.ReturnStatement:
      lowerReturn(tr, s as ts.ReturnStatement, fc, out);
      return;
    case ts.SyntaxKind.ThrowStatement: {
      const th = s as ts.ThrowStatement;
      const e = tr.unfoldE(tr.lowerExpr(th.expression, fc));
      if (isPoison(e)) { out.push(stmtItem(S.throw(E.poison(T.err)))); return; }
      if (e.ty.k === 'dyn') {
        // an unknown value must be an Error (throwing other values is outside the subset: a panic)
        out.push(stmtItem(S.throw(E.unwrap(E.prim('(.dynCast .err)', [e], [T.dyn], T.opt(T.err))))));
        return;
      }
      if (e.ty.k !== 'err') reject(th, 'throw-non-error', `only Error values can be thrown (this is ${prettyTy(e.ty)})`);
      out.push(stmtItem(S.throw(e)));
      return;
    }
    case ts.SyntaxKind.BreakStatement: {
      const b = s as ts.BreakStatement;
      out.push(stmtItem({ k: 'brk', n: tr.breakDepth(fc, b.label?.text, s) }));
      return;
    }
    case ts.SyntaxKind.ContinueStatement: {
      const c = s as ts.ContinueStatement;
      out.push(stmtItem({ k: 'cont', n: tr.contDepth(fc, c.label?.text, s) }));
      return;
    }
    case ts.SyntaxKind.LabeledStatement: {
      const ls = s as ts.LabeledStatement;
      const inner = ls.statement;
      if (!(ts.isForStatement(inner) || ts.isForOfStatement(inner) || ts.isWhileStatement(inner) || ts.isDoStatement(inner) || ts.isLabeledStatement(inner))) {
        reject(s, 'no-label-non-loop', 'labels are only allowed on loops');
      }
      lowerStmt1(tr, inner, fc, out, [...labels, ls.label.text]);
      return;
    }
    case ts.SyntaxKind.WhileStatement: lowerWhile(tr, s as ts.WhileStatement, fc, out, labels); return;
    case ts.SyntaxKind.DoStatement: lowerDo(tr, s as ts.DoStatement, fc, out, labels); return;
    case ts.SyntaxKind.ForStatement: lowerFor(tr, s as ts.ForStatement, fc, out, labels); return;
    case ts.SyntaxKind.ForOfStatement: lowerForOf(tr, s as ts.ForOfStatement, fc, out, labels); return;
    case ts.SyntaxKind.ForInStatement: reject(s, 'no-for-in', '`for … in` is not allowed');
    case ts.SyntaxKind.SwitchStatement: lowerSwitch(tr, s as ts.SwitchStatement, fc, out); return;
    case ts.SyntaxKind.TryStatement: lowerTry(tr, s as ts.TryStatement, fc, out); return;
    case ts.SyntaxKind.WithStatement: reject(s, 'no-with', '`with` is not allowed');
    case ts.SyntaxKind.EnumDeclaration: reject(s, 'no-enum-decl', 'TypeScript `enum` declarations are not supported; use a string-literal union');
    case ts.SyntaxKind.ModuleDeclaration:
      if (isTypeOnlyAmbient(s as ts.ModuleDeclaration)) return;
      reject(s, 'unsupported-syntax', 'namespaces are not supported');
    case ts.SyntaxKind.DebuggerStatement: reject(s, 'unsupported-syntax', '`debugger`');
    case ts.SyntaxKind.ExportAssignment: reject(s, 'unsupported-syntax', '`export default <expression>` / `export =`');
    default:
      reject(s, 'unsupported-syntax', `statement kind ${ts.SyntaxKind[s.kind]}`);
  }
}

function narrowNoDup(t: NarrowTest, hasElse: boolean): boolean {
  if (t.kind === 'opt') return true;
  const th = (t.toThen ?? []).filter(x => x).length;
  const el = (t.toThen ?? []).length - th;
  return th <= 1 && (el <= 1 || !hasElse);
}

// ---------------------------------------------------------------------------------------
// declarations

P.lowerVarDecl = function (this: Translator, d, isConst, fc, out) {
  if (this.isRegexConst(d)) return;
  if (fc.kind === 'main' && this.liftedArrow(d)) return;
  if (fc.kind === 'main' && this.isGlobalDecl(d)) { this.lowerGlobalDecl(d, fc, out); return; }
  if (this.coverage) {
    // the declared type first: when it has no IR type, record that and still look at the
    // initialiser
    let ok = true;
    const names: ts.Identifier[] = [];
    const collect = (b: ts.BindingName) => { if (ts.isIdentifier(b)) names.push(b); else b.elements.forEach(el => { if (!ts.isOmittedExpression(el)) collect(el.name); }); };
    collect(d.name);
    for (const id of names) {
      const sym = this.symAt(id);
      if (!sym) continue;
      try { this.tyOf(this.checker.getTypeOfSymbol(sym), fc, id); } catch (e) { if (isFatal(e)) throw e; this.covRecord(e, id); ok = false; }
    }
    if (!ok) {
      if (d.initializer) this.lowerExpr(d.initializer, fc);
      this.poisonCount++;
      bindPatternPoison(this, d.name, fc);
      return;
    }
  }
  if (ts.isIdentifier(d.name)) {
    const sym = this.symAt(d.name)!;
    const declTy = this.tyOf(this.checker.getTypeOfSymbol(sym), fc, d.name);
    if (!d.initializer) {
      if (declTy.k === 'opt') { this.declareLocal(sym, d.name.text, declTy, E.none(declTy.t), fc, out); return; }
      if (declTy.k === 'undef') { this.declareLocal(sym, d.name.text, declTy, E.undef(), fc, out); return; }
      if (this.needsBox(sym)) {
        // captured and assigned later: a box holding `undefined` until the first assignment
        const bv = mkVar(d.name.text, T.box(T.opt(declTy)));
        out.push(declItem(bv, E.builtin(`(.boxNew ${showT(T.opt(declTy))})`, [E.none(declTy)], [T.opt(declTy)], T.box(T.opt(declTy)))));
        fc.bind(sym, { k: 'boxOpt', v: bv, t: declTy });
        return;
      }
      const v = mkVar(d.name.text, T.opt(declTy), true);
      out.push(declItem(v, E.none(declTy)));
      fc.bind(sym, { k: 'optInit', v });
      return;
    }
    const lifted = this.liftedConstArrow(d, sym, fc);
    if (lifted) return;
    const hole = declTy.k === 'arr' ? holeArray(this, d, sym, isConst, fc) : undefined;
    if (hole && declTy.k === 'arr') {
      // TypeScript types an unannotated `new Array(n)` any[]: its elements get the type of the
      // values written when they all have one (the variable's IR type is then authoritative)
      const elem = declTy.t.k === 'dyn' && !d.type && !hole.typeArgs ? holeElemTy(this, hole.writes, fc) : undefined;
      const at = (elem ? T.arr(elem) : declTy) as Extract<Ty, { k: 'arr' }>;
      const len = mkVar(`${d.name.text}_len`, T.num);
      out.push(declItem(len, this.lowerExpr(hole.len, fc, T.num)));
      // (JavaScript's RangeError unless the length is an integer in [0, 2^32 - 1])
      const cmp = (op: string, k: number) => E.prim(`(.numCmp .${op})`, [E.var(len), numLit(k)], [T.num, T.num], T.bool);
      const ok = E.and(E.prim('(.numPred .isInteger)', [E.var(len)], [T.num], T.bool), E.and(cmp('ge', 0), cmp('le', 2 ** 32 - 1)));
      out.push(stmtItem(S.ite(E.not(ok), [stmtItem(S.throw(E.prim('(.errNew .rangeError)', [strLit('Invalid array length')], [T.str], T.err)))], [])));
      const b = this.declareLocal(sym, d.name.text, at, E.builtin(`(.arrOf ${showT(at.t)} 0)`, [], [], at), fc, out);
      if (b.k === 'var') { b.holes = len; if (elem) b.fixed = true; }
      return;
    }
    const initNode = skipParens(d.initializer);
    if (ts.isAwaitExpression(initNode) && !this.needsBox(sym) && !this.isReassigned(sym) && !(fc.kind === 'main' && this.globalOf.has(sym))) {
      // `const x = await e`: the await binds x directly
      const p = this.lowerAwaitOperand(initNode, fc);
      const pt = (p.ty as Extract<Ty, { k: 'promise' }>).t;
      if (tyEq(pt, declTy)) {
        const v = mkVar(d.name.text, declTy);
        out.push(awaitItem(v, p));
        fc.bind(sym, { k: 'var', v });
        return;
      }
      const t = mkVar('aw', pt);
      out.push(awaitItem(t, p));
      this.declareLocal(sym, d.name.text, declTy, this.coerce(E.var(t), declTy, d), fc, out);
      return;
    }
    const init = this.lowerExpr(d.initializer, fc, declTy);
    this.declareLocal(sym, d.name.text, declTy, init, fc, out);
    return;
  }
  if (!d.initializer) reject(d, 'unsupported-syntax', 'destructuring declaration without initialiser');
  const init = this.lowerExpr(d.initializer, fc);
  const v = this.bindTemp(init, fc, 'd');
  this.bindPattern(d.name, E.var(v), fc, out, isConst);
};

/** `const a = new Array(n)` (or `Array(n)`, n a number) in a function, used nowhere in a
 * nested function: `a` starts empty and grows by element writes `a[i] = v` (arrSet panics on
 * a write past the end, which would leave a hole); every other use of `a` first checks that
 * its length reached n (a panic otherwise: holes would be observable). Returns n's node and
 * the writes (recorded: they do not check the length). */
function holeArray(tr: Translator, d: ts.VariableDeclaration, sym: ts.Symbol, isConst: boolean, fc: FnCtx):
    { len: ts.Expression; writes: ts.Identifier[]; typeArgs: boolean } | undefined {
  if (!isConst || fc.kind === 'main' || !d.initializer || tr.needsBox(sym)) return undefined;
  const init = skipParens(d.initializer);
  if (!(ts.isNewExpression(init) || ts.isCallExpression(init)) || !ts.isIdentifier(init.expression) || init.expression.text !== 'Array') return undefined;
  if (!isLibDecl(tr.program, tr.symAt(init.expression)?.declarations?.[0])) return undefined;
  const args = init.arguments ?? [];
  if (args.length !== 1 || ts.isSpreadElement(args[0]) || !(tr.checker.getTypeAtLocation(args[0]).flags & ts.TypeFlags.NumberLike)) return undefined;
  const writes: ts.Identifier[] = [];
  let ok = true;
  const visit = (n: ts.Node): void => {
    if (!ok) return;
    if (ts.isIdentifier(n) && n !== d.name && tr.symAt(n) === sym) {
      for (let p = n.parent; p && p !== fc.tsNode; p = p.parent) if (ts.isFunctionLike(p)) { ok = false; return; }
      const p = n.parent;
      if (ts.isElementAccessExpression(p) && p.expression === n && ts.isBinaryExpression(p.parent) && p.parent.left === p &&
          p.parent.operatorToken.kind === ts.SyntaxKind.EqualsToken) writes.push(n);
    }
    ts.forEachChild(n, visit);
  };
  visit(fc.tsNode);
  if (!ok) return undefined;
  for (const w of writes) tr.holeWrites.add(w);
  return { len: args[0], writes, typeArgs: !!init.typeArguments?.length };
}

/** The one IR type of the values written by `a[i] = v` (literals widened), if not dyn. */
function holeElemTy(tr: Translator, writes: ts.Identifier[], fc: FnCtx): Ty | undefined {
  let t: Ty | undefined;
  for (const w of writes) {
    const v = ((w.parent as ts.ElementAccessExpression).parent as ts.BinaryExpression).right;
    let vt: Ty;
    try { vt = tr.tyOf(tr.checker.getBaseTypeOfLiteralType(tr.checker.getTypeAtLocation(v)), fc, v); } catch (e) { if (isFatal(e)) throw e; return undefined; }
    if (vt.k === 'dyn' || (t && !tyEq(t, vt))) return undefined;
    t = vt;
  }
  return t;
}

P.bindPattern = function (this: Translator, p, value, fc, out, isConst) {
  if (isPoison(value) && !ts.isIdentifier(p)) { bindPatternPoison(this, p, fc); return; }
  if (ts.isIdentifier(p)) {
    const sym = this.symAt(p)!;
    const declTy = this.tyOf(this.checker.getTypeOfSymbol(sym), fc, p);
    this.declareLocal(sym, p.text, declTy, this.coerce(value, declTy, p), fc, out);
    return;
  }
  let base = this.unfoldE(value);
  if (base.ty.k === 'box' && base.ty.t.k === 'record') base = this.unboxCell(base);
  const bt = base.ty;
  if (ts.isObjectBindingPattern(p)) {
    const used = new Set<string>();
    for (const el of p.elements) {
      if (el.dotDotDotToken) {
        if (bt.k !== 'record') reject(el, 'unsupported-syntax', 'object rest pattern on a non-record');
        const restFs = bt.fs.filter(f => !used.has(f.name));
        let restV = E.mkRec(T.record(restFs), restFs.map(f => E.getRec(base, bt.fs.indexOf(f))));
        // (the rest is a new object: a new cell if its type is compared by identity)
        const restTy = ts.isIdentifier(el.name) ? this.tyOf(this.checker.getTypeOfSymbol(this.symAt(el.name)!), fc, el.name) : undefined;
        if (restTy && restTy.k === 'box' && restTy.t.k === 'record') {
          restV = E.builtin(`(.boxNew ${showT(restTy.t)})`, [this.coerce(restV, restTy.t, el)], [restTy.t], restTy);
        }
        this.bindPattern(el.name, restV, fc, out, isConst);
        continue;
      }
      const key = el.propertyName ?? el.name;
      if (!ts.isIdentifier(key) && !ts.isStringLiteral(key)) reject(el, 'unsupported-syntax', 'computed key in a destructuring pattern');
      const fname = key.text;
      used.add(fname);
      let fv: Expr;
      if (bt.k === 'record') {
        const i = bt.fs.findIndex(f => f.name === fname);
        if (i < 0) reject(el, 'unsupported', `no field ${fname}`);
        fv = E.getRec(base, i);
      } else if (bt.k === 'obj') {
        fv = this.readField(base, fname, el);
      } else if (bt.k === 'dict') {
        fv = this.memberOf(base, fname, el, fc);
      } else if (bt.k === 'err' && (fname === 'message' || fname === 'name')) {
        fv = E.prim(fname === 'message' ? '.errMessage' : '.errName', [base], [T.err], T.str);
      } else reject(el, bt.k === 'dyn' ? 'any-op' : 'unsupported', `destructuring of ${prettyTy(bt)}`);
      if (el.initializer) {
        if (fv.ty.k !== 'opt') reject(el, 'unsupported', 'default value for a field that cannot be undefined');
        const inner = (fv.ty as Extract<Ty, { k: 'opt' }>).t;
        const tv = this.bindTemp(fv, fc, fname);
        const x = mkVar(fname, inner);
        const [dflt, pre] = this.isolate(fc, () => this.lowerExpr(el.initializer!, fc, inner));
        if (pre.length) reject(el.initializer, 'unsupported', 'default value with await/assignments');
        fv = E.caseOpt(E.var(tv), dflt, x, E.var(x));
      }
      this.bindPattern(el.name, fv, fc, out, isConst);
    }
    return;
  }
  // array binding pattern
  const elems = p.elements;
  if (bt.k === 'tup' && base.k === 'mkTup' && !elems.some(el => !ts.isOmittedExpression(el) && el.dotDotDotToken) &&
      base.args.every((a, i) => (i < elems.length && !ts.isOmittedExpression(elems[i])) || isStable(a))) {
    // destructuring a tuple literal: bind the components directly
    elems.forEach((el, i) => {
      if (ts.isOmittedExpression(el)) return;
      if (el.initializer) reject(el, 'unsupported-syntax', 'default value in a tuple pattern');
      this.bindPattern(el.name, base.args[i], fc, out, isConst);
    });
    return;
  }
  if (bt.k === 'tup') {
    elems.forEach((el, i) => {
      if (ts.isOmittedExpression(el)) return;
      if (el.dotDotDotToken) {
        const restTy = this.tyOf(this.checker.getTypeAtLocation(el.name), fc, el.name);
        if (restTy.k === 'tup') {
          this.bindPattern(el.name, this.coerce(E.mkTup(bt.ts.slice(i).map((_, j) => E.getTup(base, i + j))), restTy, el), fc, out, isConst);
          return;
        }
        if (restTy.k !== 'arr') reject(el, 'unsupported', 'rest element of a tuple pattern');
        const parts = bt.ts.slice(i).map((_, j) => this.coerce(E.getTup(base, i + j), restTy.t, el));
        this.bindPattern(el.name, E.builtin(`(.arrOf ${showT(restTy.t)} ${parts.length})`, parts, parts.map(() => restTy.t), restTy), fc, out, isConst);
        return;
      }
      if (i >= bt.ts.length) reject(el, 'unsupported', 'tuple pattern longer than the tuple');
      if (el.initializer) reject(el, 'unsupported-syntax', 'default value in a tuple pattern');
      this.bindPattern(el.name, E.getTup(base, i), fc, out, isConst);
    });
    return;
  }
  if (bt.k === 'arr') {
    elems.forEach((el, i) => {
      if (ts.isOmittedExpression(el)) return;
      if (el.dotDotDotToken) {
        const sl = E.builtin(`(.arrSlice ${showT(bt.t)})`, [base, numLit(i), E.none(T.num)], [bt, T.num, T.opt(T.num)], bt);
        this.bindPattern(el.name, sl, fc, out, isConst);
        return;
      }
      if (el.initializer) reject(el, 'unsupported-syntax', 'default value in an array pattern');
      const elTs = this.checker.getTypeAtLocation(el.name);
      const want = this.tyOf(elTs, fc, el.name);
      const get = want.k === 'opt' && bt.t.k !== 'opt'
        ? E.builtin(`(.arrGetOpt ${showT(bt.t)})`, [base, numLit(i)], [bt, T.num], T.opt(bt.t))
        : E.builtin(`(.arrGet ${showT(bt.t)})`, [base, numLit(i)], [bt, T.num], bt.t);
      this.bindPattern(el.name, get, fc, out, isConst);
    });
    return;
  }
  reject(p, bt.k === 'dyn' ? 'any-op' : 'unsupported', `array destructuring of ${prettyTy(bt)}`);
};

import { showTy as showT } from './ty';

// ---------------------------------------------------------------------------------------
// expression statements

P.lowerExprStmt = function (this: Translator, e0, fc, out) {
  const e = skipParens(e0);
  if (ts.isBinaryExpression(e)) {
    const k = e.operatorToken.kind;
    if (k >= ts.SyntaxKind.FirstAssignment && k <= ts.SyntaxKind.LastAssignment) {
      this.lowerAssign(e, fc, false);
      return;
    }
    if (k === ts.SyntaxKind.CommaToken) {
      this.lowerExprStmt(e.left, fc, out);
      this.lowerExprStmt(e.right, fc, out);
      return;
    }
  }
  if ((ts.isPrefixUnaryExpression(e) || ts.isPostfixUnaryExpression(e)) &&
      (e.operator === ts.SyntaxKind.PlusPlusToken || e.operator === ts.SyntaxKind.MinusMinusToken)) {
    this.lowerUpdate(e, fc, false);
    return;
  }
  if (ts.isAwaitExpression(e)) {
    const p = this.lowerAwaitOperand(e, fc);
    const v = mkVar('_', (p.ty as Extract<Ty, { k: 'promise' }>).t);
    fc.pre.push(awaitItem(v, p));
    return;
  }
  if (ts.isVoidExpression(e)) { this.lowerExprStmt(e.expression, fc, out); return; }
  if (ts.isConditionalExpression(e)) {
    const c = this.lowerCond(e.condition, fc);
    out.push(stmtItem(S.ite(c, this.lowerBlockStmtsFromExpr(e.whenTrue, fc), this.lowerBlockStmtsFromExpr(e.whenFalse, fc))));
    return;
  }
  if (ts.isBinaryExpression(e) && (e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken || e.operatorToken.kind === ts.SyntaxKind.BarBarToken)) {
    // `c && f()` / `c || f()` used as statements
    const c = this.lowerCond(e.left, fc);
    const rhs = this.lowerBlockStmtsFromExpr(e.right, fc);
    out.push(stmtItem(e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken ? S.ite(c, rhs, []) : S.ite(c, [], rhs)));
    return;
  }
  const v = this.lowerExpr(e, fc);
  out.push(stmtItem(S.expr(v)));
};

declare module './core' {
  interface Translator { lowerBlockStmtsFromExpr(e: ts.Expression, fc: FnCtx): Block }
}
P.lowerBlockStmtsFromExpr = function (this: Translator, e, fc) {
  const out: Item[] = [];
  const saved = fc.pre;
  fc.pre = out;
  try { this.lowerExprStmt(e, fc, out); } finally { fc.pre = saved; }
  return out;
};

// ---------------------------------------------------------------------------------------
// narrowing

function isUndefinedExpr(tr: Translator, e: ts.Expression): boolean {
  e = skipParens(e);
  if (ts.isIdentifier(e) && e.text === 'undefined') {
    const s = tr.checker.getSymbolAtLocation(e);
    return !s || !tr.facts(s);
  }
  return ts.isVoidExpression(e) && ts.isNumericLiteral(skipParens(e.expression));
}

function isNullExpr(e: ts.Expression): boolean {
  return skipParens(e).kind === ts.SyntaxKind.NullKeyword;
}

P.narrowTest = function (this: Translator, cond0, fc) {
  const cond = skipParens(cond0);
  const varOf = (x: ts.Expression): { sym: ts.Symbol; b: Binding } | null => {
    x = skipParens(x);
    if (!ts.isIdentifier(x)) return null;
    const sym = this.symAt(x);
    if (!sym) return null;
    const b = this.lookup(sym, fc);
    if (!b || b.k !== 'var' || b.errVar) return null;
    return { sym, b };
  };
  const scrutOf = (b: Binding): Expr => this.unfoldE(E.var((b as Extract<Binding, { k: 'var' }>).v));
  // !x
  if (ts.isPrefixUnaryExpression(cond) && cond.operator === ts.SyntaxKind.ExclamationToken) {
    const inner = this.narrowTest(cond.operand, fc);
    if (!inner) return null;
    if (inner.kind === 'opt') return { ...inner, thenSome: !inner.thenSome };
    return { ...inner, toThen: inner.toThen!.map(x => !x) };
  }
  // truthiness of an optional object / union with null
  if (ts.isIdentifier(cond)) {
    const vb = varOf(cond);
    if (!vb) return null;
    const scrut = scrutOf(vb.b);
    if (scrut.ty.k === 'opt' && isObjectLike(this.unfoldTy(scrut.ty.t))) return { sym: vb.sym, scrut, kind: 'opt', thenSome: true, node: cond };
    if (scrut.ty.k === 'union' && scrut.ty.ts.some(m => m.k === 'null') && scrut.ty.ts.every(m => m.k === 'null' || isObjectLike(this.unfoldTy(m)))) {
      return { sym: vb.sym, scrut, kind: 'union', toThen: scrut.ty.ts.map(m => m.k !== 'null'), node: cond };
    }
    return null;
  }
  if (!ts.isBinaryExpression(cond)) return null;
  const op = cond.operatorToken.kind;
  // x == null / x != undefined: null and undefined at once
  if (op === ts.SyntaxKind.EqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsToken) {
    const eq = op === ts.SyntaxKind.EqualsEqualsToken;
    for (const [a, b] of [[cond.left, cond.right], [cond.right, cond.left]] as const) {
      if (!isUndefinedExpr(this, b) && !isNullExpr(b)) continue;
      const vb = varOf(a);
      if (!vb) continue;
      const scrut = scrutOf(vb.b);
      // an optional or a union with null, seen as `opt T'` with both null and undefined as none
      // (not for unknown values: they keep their type)
      if (scrut.ty.k === 'opt' && this.unfoldTy(scrut.ty.t).k === 'dyn') return null;
      if (scrut.ty.k !== 'opt' && !(scrut.ty.k === 'union' && scrut.ty.ts.some(m => m.k === 'null'))) return null;
      const opt = this.nullishToOpt(scrut, a);
      if (opt.ty.k !== 'opt') return null;
      return { sym: vb.sym, scrut: opt, kind: 'opt', thenSome: !eq, node: cond };
    }
    return null;
  }
  if (op !== ts.SyntaxKind.EqualsEqualsEqualsToken && op !== ts.SyntaxKind.ExclamationEqualsEqualsToken) return null;
  const eq = op === ts.SyntaxKind.EqualsEqualsEqualsToken;
  // x === undefined / x === null
  for (const [a, b] of [[cond.left, cond.right], [cond.right, cond.left]] as const) {
    const vb = varOf(a);
    if (!vb) continue;
    const scrut = scrutOf(vb.b);
    // (not for an optional unknown: an unknown holding undefined is undefined too)
    if (isUndefinedExpr(this, b) && scrut.ty.k === 'opt' && this.unfoldTy(scrut.ty.t).k !== 'dyn') return { sym: vb.sym, scrut, kind: 'opt', thenSome: !eq, node: cond };
    if (isNullExpr(b) && scrut.ty.k === 'union' && scrut.ty.ts.some(m => m.k === 'null')) {
      return { sym: vb.sym, scrut, kind: 'union', toThen: scrut.ty.ts.map(m => (m.k === 'null') === eq), node: cond };
    }
  }
  // typeof x === "tag"
  for (const [a, b] of [[cond.left, cond.right], [cond.right, cond.left]] as const) {
    const ta = skipParens(a), tb = skipParens(b);
    if (ts.isTypeOfExpression(ta) && ts.isStringLiteral(tb)) {
      const vb = varOf(ta.expression);
      if (!vb) return null;
      const scrut = scrutOf(vb.b);
      const tag = tb.text;
      if (scrut.ty.k === 'opt') {
        // typeof x === "undefined" splits an optional
        if (tag === 'undefined') return this.unfoldTy(scrut.ty.t).k === 'dyn' ? null : { sym: vb.sym, scrut, kind: 'opt', thenSome: !eq, node: cond };
        if (this.typeofTag(scrut.ty.t) === tag) return { sym: vb.sym, scrut, kind: 'opt', thenSome: eq, node: cond };
        return null;
      }
      if (scrut.ty.k === 'union') {
        return { sym: vb.sym, scrut, kind: 'union', toThen: scrut.ty.ts.map(m => (this.typeofTag(m) === tag) === eq), node: cond };
      }
      return null;
    }
  }
  // x.kind === "lit" (discriminated union)
  for (const [a, b] of [[cond.left, cond.right], [cond.right, cond.left]] as const) {
    const pa = skipParens(a), lit = skipParens(b);
    if (!ts.isPropertyAccessExpression(pa) || !ts.isStringLiteral(lit)) continue;
    const vb = varOf(pa.expression);
    if (!vb) continue;
    const scrut = scrutOf(vb.b);
    if (scrut.ty.k !== 'union') continue;
    const toThen = this.discriminantSplit(scrut.ty, pa.expression, pa.name.text, [lit.text], fc);
    if (!toThen) continue;
    return { sym: vb.sym, scrut, kind: 'union', toThen: toThen.map(x => x === eq), node: cond };
  }
  return null;
};

declare module './core' {
  interface Translator {
    /** For each member of an IR union: does its discriminant `prop` take one of `values`?
     * null when TypeScript's members do not line up with the IR members. */
    discriminantSplit(u: Extract<Ty, { k: 'union' }>, baseNode: ts.Expression, prop: string, values: string[], fc: FnCtx): boolean[] | null;
  }
}

P.discriminantSplit = function (this: Translator, u, baseNode, prop, values, fc) {
  const sym = this.symAt(baseNode);
  if (!sym) return null;
  const declT = this.checker.getTypeOfSymbol(sym);
  const tsMembers = (declT.isUnion() ? declT.types : [declT]).filter(m => !(m.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null)));
  const res: (boolean | undefined)[] = u.ts.map(() => undefined);
  for (const m of tsMembers) {
    let ir: Ty;
    try { ir = this.tyOf(m, fc, baseNode); } catch { return null; }
    const idx = u.ts.findIndex(x => tyEq(x, ir));
    if (idx < 0) return null;
    const p = this.checker.getPropertyOfType(m, prop);
    if (!p) return null;
    const pt = this.checker.getTypeOfSymbol(p);
    const lits = (pt.isUnion() ? pt.types : [pt]);
    if (!lits.every(l => l.flags & ts.TypeFlags.StringLiteral)) return null;
    const hits = lits.map(l => values.includes((l as ts.StringLiteralType).value));
    if (hits.some(h => h) && hits.some(h => !h)) return null;
    const r = hits[0];
    if (res[idx] !== undefined && res[idx] !== r) return null;
    res[idx] = r;
  }
  return res.map(x => x ?? false);
};

declare module './core' {
  interface Translator {
    /** Lower a branch of a union test with the variable rebound (by one narrowing
     * declaration at the start of the branch) to the members that reach the branch. */
    withNarrowed(t: NarrowTest, thenSide: boolean, fc: FnCtx, f: () => Block): Block;
  }
}

P.withNarrowed = function (this: Translator, t, thenSide, fc, f) {
  const u = t.scrut.ty as Extract<Ty, { k: 'union' }>;
  const members = u.ts.filter((_, k) => t.toThen![k] === thenSide);
  if (members.length === u.ts.length || members.length === 0) return f();
  const nt: Ty = members.length === 1 ? members[0] : T.union(members);
  const v = mkVar(t.sym.name, nt);
  const init = this.adapt(t.scrut, nt, t.node);
  fc.push();
  fc.bind(t.sym, { k: 'var', v });
  try { return [declItem(v, init), ...f()]; } finally { fc.pop(); }
};

P.applyNarrow = function (this: Translator, t, thenB, elseB, fc) {
  if (t.kind === 'opt') {
    const inner = (t.scrut.ty as Extract<Ty, { k: 'opt' }>).t;
    const v = mkVar(t.sym.name, inner);
    const some = (): Block => {
      fc.push();
      fc.bind(t.sym, { k: 'var', v });
      try { return t.thenSome ? thenB(fc) : elseB(fc); } finally { fc.pop(); }
    };
    const none = (): Block => (t.thenSome ? elseB(fc) : thenB(fc));
    const someBlock = some();
    const noneBlock = none();
    return { k: 'caseOptS', e: t.scrut, none: noneBlock, v, some: someBlock };
  }
  const u = t.scrut.ty as Extract<Ty, { k: 'union' }>;
  const alts = u.ts.map((m, i) => {
    const v = mkVar(t.sym.name, m);
    fc.push();
    fc.bind(t.sym, { k: 'var', v });
    try { return { v, body: t.toThen![i] ? thenB(fc) : elseB(fc) }; } finally { fc.pop(); }
  });
  return { k: 'caseUS', e: t.scrut, alts };
};

// ---------------------------------------------------------------------------------------
// jumps

P.breakDepth = function (this: Translator, fc, label, node) {
  for (let i = fc.jumps.length - 1, n = 0; i >= 0; i--, n++) {
    const j = fc.jumps[i];
    if (label ? j.labels.includes(label) : j.breakTarget) return n;
  }
  reject(node, 'unsupported', label ? `no enclosing loop labelled ${label}` : '`break` outside of a loop or switch');
};

P.contDepth = function (this: Translator, fc, label, node) {
  let n = 0;
  for (let i = fc.jumps.length - 1; i >= 0; i--) {
    const j = fc.jumps[i];
    if (j.kind !== 'loop') continue;
    if (!label || j.labels.includes(label)) return n;
    n++;
  }
  reject(node, 'unsupported', label ? `no enclosing loop labelled ${label}` : '`continue` outside of a loop');
};

function loopJump(labels: string[]): Jump { return { kind: 'loop', labels, breakTarget: true }; }

function notE(c: Expr): Expr { return E.not(c); }

function lowerWhile(tr: Translator, s: ts.WhileStatement, fc: FnCtx, out: Item[], labels: string[]): void {
  const [c, preC] = tr.isolate(fc, () => tr.lowerCond(s.expression, fc));
  fc.jumps.push(loopJump(labels));
  let body: Block;
  try { body = tr.lowerSubStmt(s.statement, fc); } finally { fc.jumps.pop(); }
  if (!preC.length) { out.push(stmtItem({ k: 'while', c, body })); return; }
  out.push(stmtItem({ k: 'while', c: E.bool(true), body: [...preC, stmtItem(S.ite(notE(c), [stmtItem({ k: 'brk', n: 0 })], [])), ...body] }));
}

function lowerDo(tr: Translator, s: ts.DoStatement, fc: FnCtx, out: Item[], labels: string[]): void {
  fc.jumps.push(loopJump(labels));
  let body: Block;
  try { body = tr.lowerSubStmt(s.statement, fc); } finally { fc.jumps.pop(); }
  const [c, preC] = tr.isolate(fc, () => tr.lowerCond(s.expression, fc));
  if (!preC.length) { out.push(stmtItem({ k: 'doWhile', body, c })); return; }
  // let first = true; while (true) { if (!first) { pre; if (!c) break; } first = false; body }
  const first = mkVar('first', T.bool, true);
  const items: Item[] = [declItem(first, E.bool(true))];
  const check: Block = [...preC, stmtItem(S.ite(notE(c), [stmtItem({ k: 'brk', n: 0 })], []))];
  items.push(stmtItem({ k: 'while', c: E.bool(true), body: [stmtItem(S.ite(notE(E.var(first)), check, [])), stmtItem(S.assign(first, E.bool(false))), ...body] }));
  out.push(stmtItem({ k: 'block', b: items }));
}

function lowerFor(tr: Translator, s: ts.ForStatement, fc: FnCtx, out: Item[], labels: string[]): void {
  fc.push();
  const items: Item[] = [];
  const saved = fc.pre;
  fc.pre = items;
  const loopVars: ts.Symbol[] = [];
  try {
    if (s.initializer) {
      if (ts.isVariableDeclarationList(s.initializer)) {
        const flags = s.initializer.flags;
        const kind = flags & ts.NodeFlags.BlockScoped;
        if (kind !== ts.NodeFlags.Let && kind !== ts.NodeFlags.Const) reject(s.initializer, 'no-var', '`var` declarations are not allowed; use `let` or `const`');
        for (const d of s.initializer.declarations) {
          tr.lowerVarDecl(d, kind === ts.NodeFlags.Const, fc, items);
          if (ts.isIdentifier(d.name)) { const sym = tr.symAt(d.name); if (sym) loopVars.push(sym); }
        }
      } else tr.lowerExprStmt(s.initializer, fc, items);
    }
  } finally { fc.pre = saved; }
  // per-iteration copies of loop variables captured by closures in the body
  for (const sym of loopVars) {
    const f = tr.facts(sym);
    if (!f || !f.captured) continue;
    if (f.capturedRefs.some(r => !within(r, s.statement))) reject(s, 'unsupported', `closure in the loop head captures loop variable ${sym.name}`);
    if (tr.writtenWithin(sym, s.statement)) reject(s, 'unsupported', `closure captures loop variable ${sym.name}, which the loop body modifies`);
  }
  const [c, preC] = tr.isolate(fc, () => s.condition ? tr.lowerCond(s.condition, fc) : E.bool(true));
  let step: Block = [];
  if (s.incrementor) step = tr.lowerBlockStmtsFromExpr(s.incrementor, fc);
  fc.jumps.push(loopJump(labels));
  fc.push();
  let body: Block;
  try {
    const copies: Item[] = [];
    for (const sym of loopVars) {
      const f = tr.facts(sym);
      if (!f || !f.captured) continue;
      const b = tr.lookup(sym, fc);
      if (!b || b.k !== 'var') continue;
      const copy = mkVar(sym.name, b.v.ty);
      copies.push(declItem(copy, E.var(b.v)));
      fc.bind(sym, { k: 'var', v: copy });
    }
    body = [...copies, ...tr.lowerSubStmt(s.statement, fc)];
  } finally { fc.pop(); fc.jumps.pop(); fc.pop(); }
  if (!preC.length) items.push(stmtItem({ k: 'forLoop', c, body, step }));
  else items.push(stmtItem({ k: 'forLoop', c: E.bool(true), body: [...preC, stmtItem(S.ite(notE(c), [stmtItem({ k: 'brk', n: 0 })], [])), ...body], step }));
  if (hasDecls(items)) out.push(stmtItem({ k: 'block', b: items }));
  else out.push(...items);
}

declare module './core' {
  interface Translator {
    /** Iterable of a `for … of`: the IR statement kind, collection and element type. */
    lowerIterable(e: ts.Expression, fc: FnCtx): { kind: 'forOf' | 'forOfMap' | 'forOfSet' | 'forOfStr'; coll: Expr; elem: Ty; proj?: (v: Expr) => Expr; indexed?: boolean; dyn?: boolean };
  }
}

P.lowerIterable = function (this: Translator, e, fc) {
  const n = skipParens(e);
  // live iteration over map.keys()/values()/entries(), set.values()/keys(), arr.entries()/values()
  if (ts.isCallExpression(n) && ts.isPropertyAccessExpression(n.expression) && n.arguments.length === 0) {
    const m = n.expression.name.text;
    const recv = this.unfoldTy(this.tyAt(n.expression.expression, fc));
    if (recv.k === 'map' && (m === 'keys' || m === 'values' || m === 'entries')) {
      const coll = this.unfoldE(this.lowerExpr(n.expression.expression, fc));
      const tupT = T.tup([recv.key, recv.val]);
      return { kind: 'forOfMap', coll, elem: tupT, proj: m === 'entries' ? undefined : (v: Expr) => E.getTup(v, m === 'keys' ? 0 : 1) };
    }
    if (recv.k === 'set' && (m === 'values' || m === 'keys')) {
      const coll = this.unfoldE(this.lowerExpr(n.expression.expression, fc));
      return { kind: 'forOfSet', coll, elem: recv.t };
    }
    if (recv.k === 'arr' && (m === 'entries' || m === 'values')) {
      const coll = this.unfoldE(this.lowerExpr(n.expression.expression, fc));
      if (m === 'values') return { kind: 'forOf', coll, elem: recv.t };
      return { kind: 'forOf', coll, elem: recv.t, indexed: true };
    }
  }
  let coll = this.unfoldE(this.lowerExpr(n, fc));
  if (isPoison(coll)) return { kind: 'forOf', coll, elem: T.undef };
  if (coll.ty.k === 'tup' && coll.ty.ts.length > 0 && coll.ty.ts.every(x => tyEq(x, (coll.ty as Extract<Ty, { k: 'tup' }>).ts[0]))) {
    // a homogeneous tuple (e.g. a literal `as const`) iterates like an array of its elements
    const tt = coll.ty;
    const at = T.arr(tt.ts[0]);
    coll = this.withValue(coll, 'p', x => E.builtin(`(.arrOf ${showT(tt.ts[0])} ${tt.ts.length})`, tt.ts.map((_, i) => E.getTup(x, i)), tt.ts.map(() => tt.ts[0]), at));
  }
  const t = coll.ty;
  switch (t.k) {
    case 'arr': return { kind: 'forOf', coll, elem: t.t };
    case 'map': return { kind: 'forOfMap', coll, elem: T.tup([t.key, t.val]) };
    case 'set': return { kind: 'forOfSet', coll, elem: t.t };
    case 'str': return { kind: 'forOfStr', coll, elem: T.str };
    case 'enum': return { kind: 'forOfStr', coll: this.toStr(coll, e), elem: T.str };
  }
  if (t.k === 'dyn') return { kind: 'forOf', coll, elem: T.dyn, dyn: true };
  reject(e, 'unsupported', `for…of over ${prettyTy(t)}`);
};

function lowerForOf(tr: Translator, s: ts.ForOfStatement, fc: FnCtx, out: Item[], labels: string[]): void {
  if (s.awaitModifier) reject(s, 'unsupported-syntax', '`for await`');
  if (!ts.isVariableDeclarationList(s.initializer)) reject(s.initializer, 'unsupported-syntax', '`for (x of …)` with an existing variable; declare it with const/let');
  const list = s.initializer;
  const lkind = list.flags & ts.NodeFlags.BlockScoped;
  if (lkind !== ts.NodeFlags.Let && lkind !== ts.NodeFlags.Const) reject(list, 'no-var', '`var` declarations are not allowed; use `let` or `const`');
  const decl = list.declarations[0];
  const isConst = lkind === ts.NodeFlags.Const;
  const it = tr.lowerIterable(s.expression, fc);
  if (isPoison(it.coll)) {
    fc.jumps.push(loopJump(labels));
    fc.push();
    try {
      bindPatternPoison(tr, decl.name, fc);
      const body = tr.lowerSubStmt(s.statement, fc);
      out.push(stmtItem({ k: 'block', b: body }));
    } finally { fc.pop(); fc.jumps.pop(); }
    return;
  }
  if (it.indexed) {
    lowerIndexedForOf(tr, s, decl, isConst, it.coll, fc, out, labels);
    return;
  }
  if (it.dyn) {
    lowerDynForOf(tr, s, decl, isConst, it.coll, fc, out, labels);
    return;
  }
  // `for (const x of xs)`: the loop binder is the variable itself (no copy) when possible
  const directSym = ts.isIdentifier(decl.name) && !it.proj ? tr.symAt(decl.name) : undefined;
  const direct = !!directSym && !tr.isReassigned(directSym) && !tr.needsBox(directSym) &&
    tyEq(tr.tyOf(tr.checker.getTypeOfSymbol(directSym), fc, decl.name), it.elem);
  const v = mkVar(direct ? (decl.name as ts.Identifier).text : 'x', it.elem);
  fc.jumps.push(loopJump(labels));
  fc.push();
  let body: Block;
  try {
    const items: Item[] = [];
    const saved = fc.pre;
    fc.pre = items;
    try {
      if (direct) fc.bind(directSym!, { k: 'var', v });
      else {
        const val = it.proj ? it.proj(E.var(v)) : E.var(v);
        tr.bindPattern(decl.name, val, fc, items, isConst);
      }
    } finally { fc.pre = saved; }
    body = [...items, ...tr.lowerSubStmt(s.statement, fc)];
  } finally { fc.pop(); fc.jumps.pop(); }
  out.push(stmtItem({ k: it.kind, e: it.coll, v, body } as Stmt));
}

/** `for (const [i, x] of arr.entries())` as an index loop (the array iterator re-reads the
 * length at every step, like the loop condition). */
function lowerIndexedForOf(tr: Translator, s: ts.ForOfStatement, decl: ts.VariableDeclaration, isConst: boolean,
    arr: Expr, fc: FnCtx, out: Item[], labels: string[]): void {
  const at = arr.ty as Extract<Ty, { k: 'arr' }>;
  const items: Item[] = [];
  const a = mkVar('a', at);
  items.push(declItem(a, arr));
  const i = mkVar('i', T.num, true);
  items.push(declItem(i, numLit(0)));
  const len = E.builtin(`(.arrLength ${showT(at.t)})`, [E.var(a)], [at], T.num);
  const c = E.prim('(.numCmp .lt)', [E.var(i), len], [T.num, T.num], T.bool);
  const step: Block = [stmtItem(S.assign(i, E.prim('(.numBin .add)', [E.var(i), numLit(1)], [T.num, T.num], T.num)))];
  fc.jumps.push(loopJump(labels));
  fc.push();
  let body: Block;
  try {
    const bitems: Item[] = [];
    const ic = mkVar('i', T.num);
    bitems.push(declItem(ic, E.var(i)));
    const el = E.builtin(`(.arrGet ${showT(at.t)})`, [E.var(a), E.var(ic)], [at, T.num], at.t);
    const saved = fc.pre;
    fc.pre = bitems;
    try { tr.bindPattern(decl.name, E.mkTup([E.var(ic), el]), fc, bitems, isConst); } finally { fc.pre = saved; }
    body = [...bitems, ...tr.lowerSubStmt(s.statement, fc)];
  } finally { fc.pop(); fc.jumps.pop(); }
  items.push(stmtItem({ k: 'forLoop', c, body, step }));
  out.push(stmtItem({ k: 'block', b: items }));
}

/** `for (const x of u)` with `u` unknown: an array (of any element type) iterated by index,
reading each element as unknown and the length at every step (the array iterator); other
runtime values (strings, Maps, Sets held as unknown) are not modelled: a panic. */
function lowerDynForOf(tr: Translator, s: ts.ForOfStatement, decl: ts.VariableDeclaration, isConst: boolean,
    u: Expr, fc: FnCtx, out: Item[], labels: string[]): void {
  const items: Item[] = [];
  const d = mkVar('d', T.dyn);
  items.push(declItem(d, u));
  // (a declaration gives the panicking `unwrap none` its type)
  items.push(stmtItem(S.ite(E.prim('.dynIsArray', [E.var(d)], [T.dyn], T.bool), [], [declItem(mkVar('notArray', T.undef), E.unreachable(T.undef))])));
  const i = mkVar('i', T.num, true);
  items.push(declItem(i, numLit(0)));
  const get = (k: Expr) => E.builtin('.dynGet', [E.var(d), k], [T.dyn, T.str], T.dyn);
  const len = E.unwrap(E.prim('(.dynCast .num)', [get(strLit('length'))], [T.dyn], T.opt(T.num)));
  const c = E.prim('(.numCmp .lt)', [E.var(i), len], [T.num, T.num], T.bool);
  const step: Block = [stmtItem(S.assign(i, E.prim('(.numBin .add)', [E.var(i), numLit(1)], [T.num, T.num], T.num)))];
  fc.jumps.push(loopJump(labels));
  fc.push();
  let body: Block;
  try {
    const bitems: Item[] = [];
    const el = get(E.prim('.numToStr', [E.var(i)], [T.num], T.str));
    const saved = fc.pre;
    fc.pre = bitems;
    try { tr.bindPattern(decl.name, el, fc, bitems, isConst); } finally { fc.pre = saved; }
    body = [...bitems, ...tr.lowerSubStmt(s.statement, fc)];
  } finally { fc.pop(); fc.jumps.pop(); }
  items.push(stmtItem({ k: 'forLoop', c, body, step }));
  out.push(stmtItem({ k: 'block', b: items }));
}

// ---------------------------------------------------------------------------------------
// switch

function lowerSwitch(tr: Translator, s: ts.SwitchStatement, fc: FnCtx, out: Item[]): void {
  const clauses = s.caseBlock.clauses;
  // fallthrough check; strip one trailing `break` per clause
  const bodies: ts.Statement[][] = [];
  clauses.forEach((cl, i) => {
    let st = [...cl.statements];
    if (st.length === 1 && ts.isBlock(st[0])) st = [...(st[0] as ts.Block).statements];
    if (st.length && ts.isBreakStatement(st[st.length - 1]) && !(st[st.length - 1] as ts.BreakStatement).label) st = st.slice(0, -1);
    else if (st.length && i < clauses.length - 1 && !tsAlwaysAbrupt(cl.statements[cl.statements.length - 1])) {
      reject(cl, 'switch-fallthrough', 'a non-empty switch case must end with break/return/throw/continue');
    }
    bodies.push(st);
  });
  const needBreakable = clauses.some((cl, i) => bodies[i].some(st => containsSwitchBreak(st)));
  // groups: consecutive empty clauses share the next body
  interface Group { tests: ts.Expression[]; isDefault: boolean; body: ts.Statement[]; node: ts.Node }
  const groups: Group[] = [];
  let pending: ts.Expression[] = [];
  let pendingDefault = false;
  clauses.forEach((cl, i) => {
    if (ts.isDefaultClause(cl)) pendingDefault = true; else pending.push(cl.expression);
    if (cl.statements.length > 0 || i === clauses.length - 1) {
      groups.push({ tests: pending, isDefault: pendingDefault, body: bodies[i], node: cl });
      pending = [];
      pendingDefault = false;
    }
  });
  const jump: Jump = { kind: 'breakable', labels: [], breakTarget: true };
  const lowerBody = (g: Group): Block => {
    if (needBreakable) fc.jumps.push(jump);
    try { return tr.lowerBlockStmts(g.body, fc); } finally { if (needBreakable) fc.jumps.pop(); }
  };
  const items: Item[] = [];
  const saved = fc.pre;
  fc.pre = items;
  try {
    // discriminated union switch: switch (x.kind) with x a union variable
    const disc = skipParens(s.expression);
    if (ts.isPropertyAccessExpression(disc) && ts.isIdentifier(disc.expression)) {
      const sym = tr.symAt(disc.expression);
      const b = sym && tr.isRebindable(sym, fc, s.caseBlock);
      if (sym && b && b.k === 'var') {
        const scrut = tr.unfoldE(E.var(b.v));
        if (scrut.ty.k === 'union' && groups.every(g => g.tests.every(t => ts.isStringLiteral(skipParens(t))))) {
          const u = scrut.ty;
          const memberGroup: (Group | undefined)[] = u.ts.map(() => undefined);
          let ok = true;
          for (const g of groups) {
            if (g.isDefault) continue;
            const split = tr.discriminantSplit(u, disc.expression, disc.name.text, g.tests.map(t => (skipParens(t) as ts.StringLiteral).text), fc);
            if (!split) { ok = false; break; }
            split.forEach((hit, i) => { if (hit && !memberGroup[i]) memberGroup[i] = g; });
          }
          const dflt = groups.find(g => g.isDefault);
          if (ok) {
            const uses = new Map<Group, number>();
            u.ts.forEach((_, i) => { const g = memberGroup[i] ?? dflt; if (g) uses.set(g, (uses.get(g) ?? 0) + 1); });
            const dup = [...uses.entries()].some(([g, n]) => n > 1 && g.body.length > 0);
            if (!dup) {
              const alts = u.ts.map((m, i) => {
                const v = mkVar(sym.name, m);
                fc.push();
                fc.bind(sym, { k: 'var', v });
                try {
                  const g = memberGroup[i] ?? dflt;
                  return { v, body: g ? lowerBody(g) : [] };
                } finally { fc.pop(); }
              });
              const st: Stmt = { k: 'caseUS', e: scrut, alts };
              items.push(stmtItem(st));
              if (needBreakable) out.push(stmtItem({ k: 'breakable', b: items }));
              else if (hasDecls(items)) out.push(stmtItem({ k: 'block', b: items }));
              else out.push(...items);
              return;
            }
          }
        }
      }
    }
    const d = tr.lowerExpr(s.expression, fc);
    const dv = tr.bindTemp(d, fc, 'sw');
    // if-chain in clause order; the default group is the final else
    const dflt = groups.find(g => g.isDefault);
    let chain: Block = dflt ? lowerBody(dflt) : [];
    for (let gi = groups.length - 1; gi >= 0; gi--) {
      const g = groups[gi];
      if (!g.tests.length) continue;
      const [test, preT] = tr.isolate(fc, () => {
        let acc: Expr | null = null;
        for (const t of g.tests) {
          const c = tr.strictEqExprs(E.var(dv), tr.lowerExpr(t, fc), t, fc);
          acc = acc ? E.or(acc, c) : c;
        }
        return acc!;
      });
      if (preT.length) reject(g.node, 'unsupported', 'case expression with await/assignments');
      chain = [stmtItem(S.ite(test, lowerBody(g), chain))];
    }
    items.push(...chain);
  } finally { fc.pre = saved; }
  if (needBreakable) out.push(stmtItem({ k: 'breakable', b: items }));
  else if (hasDecls(items)) out.push(stmtItem({ k: 'block', b: items }));
  else out.push(...items);
}

function tsAlwaysAbrupt(s: ts.Statement | undefined): boolean {
  if (!s) return false;
  if (ts.isReturnStatement(s) || ts.isThrowStatement(s) || ts.isBreakStatement(s) || ts.isContinueStatement(s)) return true;
  if (ts.isBlock(s)) return s.statements.length > 0 && tsAlwaysAbrupt(s.statements[s.statements.length - 1]);
  if (ts.isIfStatement(s)) return !!s.elseStatement && tsAlwaysAbrupt(s.thenStatement) && tsAlwaysAbrupt(s.elseStatement);
  return false;
}

/** Does `n` contain an unlabelled `break` that targets the enclosing switch? */
function containsSwitchBreak(n: ts.Node): boolean {
  if (ts.isBreakStatement(n)) return !n.label;
  if (ts.isIterationStatement(n, false) || ts.isSwitchStatement(n) || ts.isFunctionLike(n) || ts.isClassLike(n)) return false;
  let found = false;
  ts.forEachChild(n, c => { if (!found && containsSwitchBreak(c)) found = true; });
  return found;
}

// ---------------------------------------------------------------------------------------
// try / return

function lowerTry(tr: Translator, s: ts.TryStatement, fc: FnCtx, out: Item[]): void {
  const body = tr.lowerBlockStmts(s.tryBlock.statements, fc);
  const fin = s.finallyBlock ? tr.lowerBlockStmts(s.finallyBlock.statements, fc) : [];
  if (!s.catchClause) { out.push(stmtItem({ k: 'tryFin', body, fin })); return; }
  const cv = s.catchClause.variableDeclaration;
  const v = mkVar(cv && ts.isIdentifier(cv.name) ? cv.name.text : 'e', T.err);
  fc.push();
  let handler: Block;
  try {
    if (cv) {
      if (!ts.isIdentifier(cv.name)) reject(cv, 'unsupported-syntax', 'destructuring catch parameter');
      const sym = tr.symAt(cv.name)!;
      if (tr.isReassigned(sym)) reject(cv, 'unsupported', 'reassigned catch variable');
      fc.bind(sym, { k: 'var', v, errVar: true });
    }
    handler = tr.lowerBlockStmts(s.catchClause.block.statements, fc);
  } finally { fc.pop(); }
  out.push(stmtItem({ k: 'try', body, v, handler, fin }));
}

function lowerReturn(tr: Translator, s: ts.ReturnStatement, fc: FnCtx, out: Item[]): void {
  if (fc.kind === 'main') reject(s, 'unsupported-syntax', '`return` at module level');
  if (fc.retPoison) {
    // coverage mode: the return type has no IR type (already recorded)
    if (s.expression) tr.lowerExpr(s.expression, fc);
    out.push(stmtItem(S.ret(E.poison(T.undef))));
    return;
  }
  if (fc.isCtor) {
    if (s.expression) reject(s, 'unsupported', 'returning a value from a constructor');
    out.push(stmtItem(S.ret(E.var(fc.thisVar!))));
    return;
  }
  if (!s.expression) {
    if (fc.bodyRet.k === 'opt') { out.push(stmtItem(S.ret(E.none(fc.bodyRet.t)))); return; }
    if (fc.bodyRet.k !== 'undef') reject(s, 'unsupported', `\`return;\` in a function returning ${prettyTy(fc.bodyRet)}`);
    out.push(stmtItem(S.ret(E.undef())));
    return;
  }
  const tsT = tr.checker.getTypeAtLocation(s.expression);
  if (fc.async) {
    const nat = tr.tyOf(tsT, fc, s.expression);
    if (nat.k === 'promise') {
      const p = tr.lowerExpr(s.expression, fc, T.promise(fc.bodyRet));
      out.push(stmtItem({ k: 'retP', e: p }));
      return;
    }
  }
  if (fc.bodyRet.k === 'undef') {
    const e = tr.lowerExpr(s.expression, fc);
    if (e.ty.k === 'undef') { out.push(stmtItem(S.ret(e))); return; }
    out.push(stmtItem(S.expr(e)));
    out.push(stmtItem(S.ret(E.undef())));
    return;
  }
  if (fc.bodyRet.k === 'bool' && fc.kind === 'lambda' && tr.tyAt(s.expression, fc).k !== 'bool') {
    out.push(stmtItem(S.ret(tr.truthy(tr.lowerExpr(s.expression, fc), s.expression))));
    return;
  }
  out.push(stmtItem(S.ret(tr.lowerExpr(s.expression, fc, fc.bodyRet))));
}

export { skipParens, tsAlwaysAbrupt };

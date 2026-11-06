"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.bindPatternPoison = bindPatternPoison;
exports.skipParens = skipParens;
exports.tsAlwaysAbrupt = tsAlwaysAbrupt;
// Statement lowering.
const ts = __importStar(require("typescript"));
const ty_1 = require("./ty");
const ir_1 = require("./ir");
const exprs_1 = require("./exprs");
const check_1 = require("./check");
const diag_1 = require("./diag");
const core_1 = require("./core");
const P = core_1.Translator.prototype;
function skipParens(e) {
    while (ts.isParenthesizedExpression(e))
        e = e.expression;
    return e;
}
function hasDecls(b) { return b.some(it => it.k !== 'stmt'); }
P.lowerBlockStmts = function (stmts, fc) {
    fc.push();
    try {
        if (this.coverage) {
            try {
                this.hoistFunctions(stmts, fc);
            }
            catch (e) {
                if ((0, exprs_1.isFatal)(e))
                    throw e;
                this.covRecord(e, stmts[0]);
                this.poisonCount++;
                for (const st of stmts)
                    if (ts.isFunctionDeclaration(st) && st.name) {
                        const sym = this.symAt(st.name);
                        if (sym && !this.lookup(sym, fc))
                            fc.bind(sym, { k: 'poison', ty: ty_1.T.undef });
                    }
            }
        }
        else
            this.hoistFunctions(stmts, fc);
        const out = [];
        this.lowerStmtList(stmts, 0, fc, out);
        return out;
    }
    finally {
        fc.pop();
    }
};
P.lowerSubStmt = function (s, fc) {
    if (ts.isBlock(s))
        return this.lowerBlockStmts(s.statements, fc);
    return this.lowerBlockStmts([s], fc);
};
P.lowerStmtList = function (stmts, i, fc, out) {
    for (; i < stmts.length; i++) {
        const s = stmts[i];
        if (unionGuardChain(this, stmts, i, fc, out))
            return;
        if (ts.isIfStatement(s) && !s.elseStatement && i + 1 < stmts.length) {
            // early-exit guards: `if (A || B || …) { …abrupt… }` narrows the rest of the block;
            // it is processed as the guards `if (A) …; if (B) …; …` (B runs only when A is false)
            const conds = orOperands(s.expression);
            const small = tsStmtCount(s.thenStatement) <= 2;
            if ((conds.length === 1 || small) && conds.some(c => this.narrowTest(c, fc) !== null)) {
                const thenBlock = this.lowerSubStmt(s.thenStatement, fc);
                if ((0, ir_1.blockAlwaysAbrupt)(thenBlock)) {
                    lowerGuardChain(this, conds, s.thenStatement, small, stmts, i + 1, fc, out);
                    return;
                }
            }
        }
        this.lowerStmt(s, fc, out);
    }
};
function mentions(tr, n, sym) {
    let found = false;
    const visit = (c) => {
        if (found)
            return;
        if (ts.isIdentifier(c) && tr.symAt(c) === sym) {
            found = true;
            return;
        }
        ts.forEachChild(c, visit);
    };
    visit(n);
    return found;
}
/** Consecutive guards `if (x.kind === …) return …;` on the same union variable become one
 * caseUS: each member runs the block of the first guard that catches it, the member no
 * guard catches runs the rest of the block. */
function unionGuardChain(tr, stmts, i, fc, out) {
    const guards = [];
    let sym;
    let scrut;
    let remaining = [];
    let j = i;
    for (; j < stmts.length; j++) {
        const st = stmts[j];
        if (!ts.isIfStatement(st) || st.elseStatement)
            break;
        const test = tr.narrowTest(st.expression, fc);
        if (!test || test.kind !== 'union')
            break;
        if (sym && test.sym !== sym)
            break;
        if (!sym) {
            sym = test.sym;
            scrut = test.scrut;
            remaining = test.scrut.ty.ts.map((_, k) => k);
        }
        if (!tsAlwaysAbrupt(st.thenStatement))
            break;
        const caught = remaining.filter(k => test.toThen[k]);
        if (caught.length > 1 && (tsStmtCount(st.thenStatement) > 2 || mentions(tr, st.thenStatement, sym)))
            break;
        guards.push({ s: st, caught });
        remaining = remaining.filter(k => !test.toThen[k]);
        if (remaining.length <= 1) {
            j++;
            break;
        }
    }
    if (guards.length < 2 || remaining.length > 1 || !sym || !scrut)
        return false;
    const rest = stmts.slice(j);
    if (!tr.isRebindable(sym, fc, [...guards.map(g => g.s), ...rest]))
        return false;
    const u = scrut.ty;
    const alts = u.ts.map((m, k) => {
        const v = (0, ir_1.mkVar)(sym.name, m);
        fc.push();
        fc.bind(sym, { k: 'var', v });
        try {
            const g = guards.find(gd => gd.caught.includes(k));
            if (g)
                return { v, body: tr.lowerSubStmt(g.s.thenStatement, fc) };
            const items = [];
            tr.hoistFunctions(rest, fc);
            tr.lowerStmtList(stmts, j, fc, items);
            return { v, body: items };
        }
        finally {
            fc.pop();
        }
    });
    out.push((0, ir_1.stmtItem)({ k: 'caseUS', e: scrut, alts }));
    return true;
}
function orOperands(e) {
    const x = skipParens(e);
    if (ts.isBinaryExpression(x) && x.operatorToken.kind === ts.SyntaxKind.BarBarToken)
        return [...orOperands(x.left), ...orOperands(x.right)];
    return [x];
}
function tsStmtCount(s) {
    return ts.isBlock(s) ? s.statements.length : 1;
}
/** Guards `if (c_k) S` for k = 0.., then the rest of the block; narrowing guards become
 * caseOptS/caseUS with the rest in the branch where the variable is narrowed. */
function lowerGuardChain(tr, conds, thenS, small, stmts, restIdx, fc, out) {
    const rest = stmts.slice(restIdx);
    const go = (k, fc2, out2) => {
        if (k === conds.length) {
            fc2.push();
            try {
                tr.hoistFunctions(rest, fc2);
                tr.lowerStmtList(stmts, restIdx, fc2, out2);
            }
            finally {
                fc2.pop();
            }
            return;
        }
        const later = [...conds.slice(k + 1), ...rest];
        const test = tr.narrowTest(conds[k], fc2);
        // the `then` block may be duplicated per union member only if it does not use the
        // variable (TypeScript could narrow it differently inside)
        const dupOk = small && !!test && !mentions(tr, thenS, test.sym);
        if (test && tr.isRebindable(test.sym, fc2, later) && guardOk(test, dupOk)) {
            out2.push((0, ir_1.stmtItem)(tr.applyNarrow(test, () => tr.lowerSubStmt(thenS, fc2), (fc3) => {
                const items = [];
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
                out2.push((0, ir_1.stmtItem)(tr.applyNarrow(test, () => tr.lowerSubStmt(thenS, fc2), () => [], fc2)));
            }
            else {
                const c = tr.lowerCond(conds[k], fc2);
                const unionTest = !!test && test.kind === 'union';
                const thenB = unionTest && tr.isRebindable(test.sym, fc2, thenS)
                    ? tr.withNarrowed(test, true, fc2, () => tr.lowerSubStmt(thenS, fc2)) : tr.lowerSubStmt(thenS, fc2);
                out2.push((0, ir_1.stmtItem)(ir_1.S.ite(c, thenB, [])));
                restNarrow = unionTest && !!tr.isRebindable(test.sym, fc2, later);
            }
        }
        finally {
            fc2.pre = saved;
        }
        if (restNarrow) {
            // after the guard the variable has the remaining members: rebind it once
            const items = tr.withNarrowed(test, false, fc2, () => { const xs = []; go(k + 1, fc2, xs); return xs; });
            out2.push(...items);
            return;
        }
        go(k + 1, fc2, out2);
    };
    go(0, fc, out);
}
/** A guard is restructured when the rest of the block goes to at most one union member
 * (no duplication of the rest); the abrupt `then` block may be duplicated when small. */
function guardOk(t, smallThen = false) {
    if (t.kind === 'opt')
        return true;
    const th = (t.toThen ?? []).filter(x => x).length;
    return (th <= 1 || smallThen) && (t.toThen ?? []).length - th <= 1;
}
P.isRebindable = function (sym, fc, region) {
    const b = this.lookup(sym, fc);
    if (!b || b.k !== 'var' || b.errVar)
        return null;
    if (this.writtenWithin(sym, region))
        return null;
    if (b.v.ty.k !== 'opt' && b.v.ty.k !== 'union' && b.v.ty.k !== 'named')
        return null;
    return b;
};
P.lowerStmt = function (s, fc, out, labels = []) {
    const saved = fc.pre;
    fc.pre = out;
    try {
        if (!this.coverage) {
            lowerStmt1(this, s, fc, out, labels);
            return;
        }
        // coverage mode: record the violation, skip the statement, and give the variables it
        // declares placeholder values
        const mark = this.poisonCount;
        try {
            lowerStmt1(this, s, fc, out, labels);
        }
        catch (e) {
            if ((0, exprs_1.isFatal)(e))
                throw e;
            if (this.poisonCount === mark)
                this.covRecord(e, s);
            this.poisonCount++;
            bindDeclaredPoison(this, s, fc);
        }
    }
    finally {
        fc.pre = saved;
    }
};
/** Coverage mode: the variables declared by a statement that could not be translated. */
function bindDeclaredPoison(tr, s, fc) {
    if (!ts.isVariableStatement(s))
        return;
    for (const d of s.declarationList.declarations)
        bindPatternPoison(tr, d.name, fc);
}
function bindPatternPoison(tr, p, fc) {
    if (ts.isIdentifier(p)) {
        const sym = tr.symAt(p);
        if (!sym)
            return;
        let ty = ty_1.T.undef;
        try {
            ty = tr.tyOf(tr.checker.getTypeOfSymbol(sym), fc, p);
        }
        catch { /* unknown */ }
        fc.bind(sym, { k: 'poison', ty });
        return;
    }
    for (const el of p.elements)
        if (!ts.isOmittedExpression(el))
            bindPatternPoison(tr, el.name, fc);
}
function lowerStmt1(tr, s, fc, out, labels) {
    switch (s.kind) {
        case ts.SyntaxKind.VariableStatement: {
            const vs = s;
            const flags = vs.declarationList.flags;
            const kind = flags & ts.NodeFlags.BlockScoped;
            if (kind === 0)
                (0, diag_1.reject)(s, 'no-var', '`var` declarations are not allowed; use `let` or `const`');
            if (kind !== ts.NodeFlags.Let && kind !== ts.NodeFlags.Const)
                (0, diag_1.reject)(s, 'unsupported-syntax', '`using` declarations');
            for (const d of vs.declarationList.declarations)
                tr.lowerVarDecl(d, kind === ts.NodeFlags.Const, fc, out);
            return;
        }
        case ts.SyntaxKind.ExpressionStatement:
            tr.lowerExprStmt(s.expression, fc, out);
            return;
        case ts.SyntaxKind.IfStatement: {
            const is = s;
            const test = tr.narrowTest(is.expression, fc);
            if (test) {
                const regions = [is.thenStatement, ...(is.elseStatement ? [is.elseStatement] : [])];
                if (tr.isRebindable(test.sym, fc, regions) && narrowNoDup(test, !!is.elseStatement)) {
                    out.push((0, ir_1.stmtItem)(tr.applyNarrow(test, () => tr.lowerSubStmt(is.thenStatement, fc), () => is.elseStatement ? tr.lowerSubStmt(is.elseStatement, fc) : [], fc)));
                    return;
                }
            }
            const c = tr.lowerCond(is.expression, fc);
            if (test && test.kind === 'union' && tr.isRebindable(test.sym, fc, [is.thenStatement, ...(is.elseStatement ? [is.elseStatement] : [])])) {
                // narrow once per branch: the variable is rebound to the narrowed (sub-)union
                const t = tr.withNarrowed(test, true, fc, () => tr.lowerSubStmt(is.thenStatement, fc));
                const f = is.elseStatement ? tr.withNarrowed(test, false, fc, () => tr.lowerSubStmt(is.elseStatement, fc)) : [];
                out.push((0, ir_1.stmtItem)(ir_1.S.ite(c, t, f)));
                return;
            }
            const t = tr.lowerSubStmt(is.thenStatement, fc);
            const f = is.elseStatement ? tr.lowerSubStmt(is.elseStatement, fc) : [];
            out.push((0, ir_1.stmtItem)(ir_1.S.ite(c, t, f)));
            return;
        }
        case ts.SyntaxKind.Block: {
            const b = tr.lowerBlockStmts(s.statements, fc);
            if (hasDecls(b))
                out.push((0, ir_1.stmtItem)({ k: 'block', b }));
            else
                out.push(...b);
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
            const fd = s;
            const sym = fd.name && tr.symAt(fd.name);
            const b = sym && tr.lookup(sym, fc);
            if (b && b.k === 'lifted' && fd.name) {
                let want;
                try {
                    want = tr.tyAt(fd.name, fc);
                }
                catch {
                    want = undefined;
                }
                if (want && want.k === 'box' && want.t.k === 'fn') {
                    const saved = fc.pre;
                    fc.pre = out;
                    try {
                        const clo = tr.liftedAsValue(b, fd.name, fc, want.t);
                        const cell = (0, ir_1.mkVar)(`${fd.name.text}$fn`, want);
                        out.push((0, ir_1.declItem)(cell, ir_1.E.builtin(`(.boxNew ${(0, ty_2.showTy)(want.t)})`, [clo], [want.t], want)));
                        b.cell = cell;
                    }
                    finally {
                        fc.pre = saved;
                    }
                }
            }
            return;
        }
        case ts.SyntaxKind.ClassDeclaration:
            tr.lowerClassDeclStmt(s, fc, out);
            return;
        case ts.SyntaxKind.ReturnStatement:
            lowerReturn(tr, s, fc, out);
            return;
        case ts.SyntaxKind.ThrowStatement: {
            const th = s;
            const e = tr.unfoldE(tr.lowerExpr(th.expression, fc));
            if ((0, ir_1.isPoison)(e)) {
                out.push((0, ir_1.stmtItem)(ir_1.S.throw(ir_1.E.poison(ty_1.T.err))));
                return;
            }
            if (e.ty.k === 'dyn') {
                // an unknown value must be an Error (throwing other values is outside the subset: a panic)
                out.push((0, ir_1.stmtItem)(ir_1.S.throw(ir_1.E.unwrap(ir_1.E.prim('(.dynCast .err)', [e], [ty_1.T.dyn], ty_1.T.opt(ty_1.T.err))))));
                return;
            }
            if (e.ty.k !== 'err')
                (0, diag_1.reject)(th, 'throw-non-error', `only Error values can be thrown (this is ${(0, ty_1.prettyTy)(e.ty)})`);
            out.push((0, ir_1.stmtItem)(ir_1.S.throw(e)));
            return;
        }
        case ts.SyntaxKind.BreakStatement: {
            const b = s;
            out.push((0, ir_1.stmtItem)({ k: 'brk', n: tr.breakDepth(fc, b.label?.text, s) }));
            return;
        }
        case ts.SyntaxKind.ContinueStatement: {
            const c = s;
            out.push((0, ir_1.stmtItem)({ k: 'cont', n: tr.contDepth(fc, c.label?.text, s) }));
            return;
        }
        case ts.SyntaxKind.LabeledStatement: {
            const ls = s;
            const inner = ls.statement;
            if (!(ts.isForStatement(inner) || ts.isForOfStatement(inner) || ts.isWhileStatement(inner) || ts.isDoStatement(inner) || ts.isLabeledStatement(inner))) {
                (0, diag_1.reject)(s, 'no-label-non-loop', 'labels are only allowed on loops');
            }
            lowerStmt1(tr, inner, fc, out, [...labels, ls.label.text]);
            return;
        }
        case ts.SyntaxKind.WhileStatement:
            lowerWhile(tr, s, fc, out, labels);
            return;
        case ts.SyntaxKind.DoStatement:
            lowerDo(tr, s, fc, out, labels);
            return;
        case ts.SyntaxKind.ForStatement:
            lowerFor(tr, s, fc, out, labels);
            return;
        case ts.SyntaxKind.ForOfStatement:
            lowerForOf(tr, s, fc, out, labels);
            return;
        case ts.SyntaxKind.ForInStatement: (0, diag_1.reject)(s, 'no-for-in', '`for … in` is not allowed');
        case ts.SyntaxKind.SwitchStatement:
            lowerSwitch(tr, s, fc, out);
            return;
        case ts.SyntaxKind.TryStatement:
            lowerTry(tr, s, fc, out);
            return;
        case ts.SyntaxKind.WithStatement: (0, diag_1.reject)(s, 'no-with', '`with` is not allowed');
        case ts.SyntaxKind.EnumDeclaration: (0, diag_1.reject)(s, 'no-enum-decl', 'TypeScript `enum` declarations are not supported; use a string-literal union');
        case ts.SyntaxKind.ModuleDeclaration:
            if ((0, check_1.isTypeOnlyAmbient)(s))
                return;
            (0, diag_1.reject)(s, 'unsupported-syntax', 'namespaces are not supported');
        case ts.SyntaxKind.DebuggerStatement: (0, diag_1.reject)(s, 'unsupported-syntax', '`debugger`');
        case ts.SyntaxKind.ExportAssignment: (0, diag_1.reject)(s, 'unsupported-syntax', '`export default <expression>` / `export =`');
        default:
            (0, diag_1.reject)(s, 'unsupported-syntax', `statement kind ${ts.SyntaxKind[s.kind]}`);
    }
}
function narrowNoDup(t, hasElse) {
    if (t.kind === 'opt')
        return true;
    const th = (t.toThen ?? []).filter(x => x).length;
    const el = (t.toThen ?? []).length - th;
    return th <= 1 && (el <= 1 || !hasElse);
}
// ---------------------------------------------------------------------------------------
// declarations
P.lowerVarDecl = function (d, isConst, fc, out) {
    if (this.isRegexConst(d))
        return;
    if (fc.kind === 'main' && this.liftedArrow(d))
        return;
    if (fc.kind === 'main' && this.isGlobalDecl(d)) {
        this.lowerGlobalDecl(d, fc, out);
        return;
    }
    if (this.coverage) {
        // the declared type first: when it has no IR type, record that and still look at the
        // initialiser
        let ok = true;
        const names = [];
        const collect = (b) => { if (ts.isIdentifier(b))
            names.push(b);
        else
            b.elements.forEach(el => { if (!ts.isOmittedExpression(el))
                collect(el.name); }); };
        collect(d.name);
        for (const id of names) {
            const sym = this.symAt(id);
            if (!sym)
                continue;
            try {
                this.tyOf(this.checker.getTypeOfSymbol(sym), fc, id);
            }
            catch (e) {
                if ((0, exprs_1.isFatal)(e))
                    throw e;
                this.covRecord(e, id);
                ok = false;
            }
        }
        if (!ok) {
            if (d.initializer)
                this.lowerExpr(d.initializer, fc);
            this.poisonCount++;
            bindPatternPoison(this, d.name, fc);
            return;
        }
    }
    if (ts.isIdentifier(d.name)) {
        const sym = this.symAt(d.name);
        const declTy = this.tyOf(this.checker.getTypeOfSymbol(sym), fc, d.name);
        if (!d.initializer) {
            if (declTy.k === 'opt') {
                this.declareLocal(sym, d.name.text, declTy, ir_1.E.none(declTy.t), fc, out);
                return;
            }
            if (declTy.k === 'undef') {
                this.declareLocal(sym, d.name.text, declTy, ir_1.E.undef(), fc, out);
                return;
            }
            if (this.needsBox(sym)) {
                // captured and assigned later: a box holding `undefined` until the first assignment
                const bv = (0, ir_1.mkVar)(d.name.text, ty_1.T.box(ty_1.T.opt(declTy)));
                out.push((0, ir_1.declItem)(bv, ir_1.E.builtin(`(.boxNew ${(0, ty_2.showTy)(ty_1.T.opt(declTy))})`, [ir_1.E.none(declTy)], [ty_1.T.opt(declTy)], ty_1.T.box(ty_1.T.opt(declTy)))));
                fc.bind(sym, { k: 'boxOpt', v: bv, t: declTy });
                return;
            }
            const v = (0, ir_1.mkVar)(d.name.text, ty_1.T.opt(declTy), true);
            out.push((0, ir_1.declItem)(v, ir_1.E.none(declTy)));
            fc.bind(sym, { k: 'optInit', v });
            return;
        }
        const lifted = this.liftedConstArrow(d, sym, fc);
        if (lifted)
            return;
        const hole = declTy.k === 'arr' ? holeArray(this, d, sym, isConst, fc) : undefined;
        if (hole && declTy.k === 'arr') {
            // TypeScript types an unannotated `new Array(n)` any[]: its elements get the type of the
            // values written when they all have one (the variable's IR type is then authoritative)
            const elem = declTy.t.k === 'dyn' && !d.type && !hole.typeArgs ? holeElemTy(this, hole.writes, fc) : undefined;
            const at = (elem ? ty_1.T.arr(elem) : declTy);
            const len = (0, ir_1.mkVar)(`${d.name.text}_len`, ty_1.T.num);
            out.push((0, ir_1.declItem)(len, this.lowerExpr(hole.len, fc, ty_1.T.num)));
            // (JavaScript's RangeError unless the length is an integer in [0, 2^32 - 1])
            const cmp = (op, k) => ir_1.E.prim(`(.numCmp .${op})`, [ir_1.E.var(len), (0, core_1.numLit)(k)], [ty_1.T.num, ty_1.T.num], ty_1.T.bool);
            const ok = ir_1.E.and(ir_1.E.prim('(.numPred .isInteger)', [ir_1.E.var(len)], [ty_1.T.num], ty_1.T.bool), ir_1.E.and(cmp('ge', 0), cmp('le', 2 ** 32 - 1)));
            out.push((0, ir_1.stmtItem)(ir_1.S.ite(ir_1.E.not(ok), [(0, ir_1.stmtItem)(ir_1.S.throw(ir_1.E.prim('(.errNew .rangeError)', [(0, core_1.strLit)('Invalid array length')], [ty_1.T.str], ty_1.T.err)))], [])));
            const b = this.declareLocal(sym, d.name.text, at, ir_1.E.builtin(`(.arrOf ${(0, ty_2.showTy)(at.t)} 0)`, [], [], at), fc, out);
            if (b.k === 'var') {
                b.holes = len;
                if (elem)
                    b.fixed = true;
            }
            return;
        }
        const initNode = skipParens(d.initializer);
        if (ts.isAwaitExpression(initNode) && !this.needsBox(sym) && !this.isReassigned(sym) && !(fc.kind === 'main' && this.globalOf.has(sym))) {
            // `const x = await e`: the await binds x directly
            const p = this.lowerAwaitOperand(initNode, fc);
            const pt = p.ty.t;
            if ((0, ty_1.tyEq)(pt, declTy)) {
                const v = (0, ir_1.mkVar)(d.name.text, declTy);
                out.push((0, ir_1.awaitItem)(v, p));
                fc.bind(sym, { k: 'var', v });
                return;
            }
            const t = (0, ir_1.mkVar)('aw', pt);
            out.push((0, ir_1.awaitItem)(t, p));
            this.declareLocal(sym, d.name.text, declTy, this.coerce(ir_1.E.var(t), declTy, d), fc, out);
            return;
        }
        const init = this.lowerExpr(d.initializer, fc, declTy);
        this.declareLocal(sym, d.name.text, declTy, init, fc, out);
        return;
    }
    if (!d.initializer)
        (0, diag_1.reject)(d, 'unsupported-syntax', 'destructuring declaration without initialiser');
    const init = this.lowerExpr(d.initializer, fc);
    const v = this.bindTemp(init, fc, 'd');
    this.bindPattern(d.name, ir_1.E.var(v), fc, out, isConst);
};
/** `const a = new Array(n)` (or `Array(n)`, n a number) in a function, used nowhere in a
 * nested function: `a` starts empty and grows by element writes `a[i] = v` (arrSet panics on
 * a write past the end, which would leave a hole); every other use of `a` first checks that
 * its length reached n (a panic otherwise: holes would be observable). Returns n's node and
 * the writes (recorded: they do not check the length). */
function holeArray(tr, d, sym, isConst, fc) {
    if (!isConst || fc.kind === 'main' || !d.initializer || tr.needsBox(sym))
        return undefined;
    const init = skipParens(d.initializer);
    if (!(ts.isNewExpression(init) || ts.isCallExpression(init)) || !ts.isIdentifier(init.expression) || init.expression.text !== 'Array')
        return undefined;
    if (!(0, core_1.isLibDecl)(tr.program, tr.symAt(init.expression)?.declarations?.[0]))
        return undefined;
    const args = init.arguments ?? [];
    if (args.length !== 1 || ts.isSpreadElement(args[0]) || !(tr.checker.getTypeAtLocation(args[0]).flags & ts.TypeFlags.NumberLike))
        return undefined;
    const writes = [];
    let ok = true;
    const visit = (n) => {
        if (!ok)
            return;
        if (ts.isIdentifier(n) && n !== d.name && tr.symAt(n) === sym) {
            for (let p = n.parent; p && p !== fc.tsNode; p = p.parent)
                if (ts.isFunctionLike(p)) {
                    ok = false;
                    return;
                }
            const p = n.parent;
            if (ts.isElementAccessExpression(p) && p.expression === n && ts.isBinaryExpression(p.parent) && p.parent.left === p &&
                p.parent.operatorToken.kind === ts.SyntaxKind.EqualsToken)
                writes.push(n);
        }
        ts.forEachChild(n, visit);
    };
    visit(fc.tsNode);
    if (!ok)
        return undefined;
    for (const w of writes)
        tr.holeWrites.add(w);
    return { len: args[0], writes, typeArgs: !!init.typeArguments?.length };
}
/** The one IR type of the values written by `a[i] = v` (literals widened), if not dyn. */
function holeElemTy(tr, writes, fc) {
    let t;
    for (const w of writes) {
        const v = w.parent.parent.right;
        let vt;
        try {
            vt = tr.tyOf(tr.checker.getBaseTypeOfLiteralType(tr.checker.getTypeAtLocation(v)), fc, v);
        }
        catch (e) {
            if ((0, exprs_1.isFatal)(e))
                throw e;
            return undefined;
        }
        if (vt.k === 'dyn' || (t && !(0, ty_1.tyEq)(t, vt)))
            return undefined;
        t = vt;
    }
    return t;
}
P.bindPattern = function (p, value, fc, out, isConst) {
    if ((0, ir_1.isPoison)(value) && !ts.isIdentifier(p)) {
        bindPatternPoison(this, p, fc);
        return;
    }
    if (ts.isIdentifier(p)) {
        const sym = this.symAt(p);
        const declTy = this.tyOf(this.checker.getTypeOfSymbol(sym), fc, p);
        this.declareLocal(sym, p.text, declTy, this.coerce(value, declTy, p), fc, out);
        return;
    }
    let base = this.unfoldE(value);
    if (base.ty.k === 'box' && base.ty.t.k === 'record')
        base = this.unboxCell(base);
    const bt = base.ty;
    if (ts.isObjectBindingPattern(p)) {
        const used = new Set();
        for (const el of p.elements) {
            if (el.dotDotDotToken) {
                if (bt.k !== 'record')
                    (0, diag_1.reject)(el, 'unsupported-syntax', 'object rest pattern on a non-record');
                const restFs = bt.fs.filter(f => !used.has(f.name));
                let restV = ir_1.E.mkRec(ty_1.T.record(restFs), restFs.map(f => ir_1.E.getRec(base, bt.fs.indexOf(f))));
                // (the rest is a new object: a new cell if its type is compared by identity)
                const restTy = ts.isIdentifier(el.name) ? this.tyOf(this.checker.getTypeOfSymbol(this.symAt(el.name)), fc, el.name) : undefined;
                if (restTy && restTy.k === 'box' && restTy.t.k === 'record') {
                    restV = ir_1.E.builtin(`(.boxNew ${(0, ty_2.showTy)(restTy.t)})`, [this.coerce(restV, restTy.t, el)], [restTy.t], restTy);
                }
                this.bindPattern(el.name, restV, fc, out, isConst);
                continue;
            }
            const key = el.propertyName ?? el.name;
            if (!ts.isIdentifier(key) && !ts.isStringLiteral(key))
                (0, diag_1.reject)(el, 'unsupported-syntax', 'computed key in a destructuring pattern');
            const fname = key.text;
            used.add(fname);
            let fv;
            if (bt.k === 'record') {
                const i = bt.fs.findIndex(f => f.name === fname);
                if (i < 0)
                    (0, diag_1.reject)(el, 'unsupported', `no field ${fname}`);
                fv = ir_1.E.getRec(base, i);
            }
            else if (bt.k === 'obj') {
                fv = this.readField(base, fname, el);
            }
            else if (bt.k === 'dict') {
                fv = this.memberOf(base, fname, el, fc);
            }
            else if (bt.k === 'err' && (fname === 'message' || fname === 'name')) {
                fv = ir_1.E.prim(fname === 'message' ? '.errMessage' : '.errName', [base], [ty_1.T.err], ty_1.T.str);
            }
            else
                (0, diag_1.reject)(el, bt.k === 'dyn' ? 'any-op' : 'unsupported', `destructuring of ${(0, ty_1.prettyTy)(bt)}`);
            if (el.initializer) {
                if (fv.ty.k !== 'opt')
                    (0, diag_1.reject)(el, 'unsupported', 'default value for a field that cannot be undefined');
                const inner = fv.ty.t;
                const tv = this.bindTemp(fv, fc, fname);
                const x = (0, ir_1.mkVar)(fname, inner);
                const [dflt, pre] = this.isolate(fc, () => this.lowerExpr(el.initializer, fc, inner));
                if (pre.length)
                    (0, diag_1.reject)(el.initializer, 'unsupported', 'default value with await/assignments');
                fv = ir_1.E.caseOpt(ir_1.E.var(tv), dflt, x, ir_1.E.var(x));
            }
            this.bindPattern(el.name, fv, fc, out, isConst);
        }
        return;
    }
    // array binding pattern
    const elems = p.elements;
    if (bt.k === 'tup' && base.k === 'mkTup' && !elems.some(el => !ts.isOmittedExpression(el) && el.dotDotDotToken) &&
        base.args.every((a, i) => (i < elems.length && !ts.isOmittedExpression(elems[i])) || (0, ir_1.isStable)(a))) {
        // destructuring a tuple literal: bind the components directly
        elems.forEach((el, i) => {
            if (ts.isOmittedExpression(el))
                return;
            if (el.initializer)
                (0, diag_1.reject)(el, 'unsupported-syntax', 'default value in a tuple pattern');
            this.bindPattern(el.name, base.args[i], fc, out, isConst);
        });
        return;
    }
    if (bt.k === 'tup') {
        elems.forEach((el, i) => {
            if (ts.isOmittedExpression(el))
                return;
            if (el.dotDotDotToken) {
                const restTy = this.tyOf(this.checker.getTypeAtLocation(el.name), fc, el.name);
                if (restTy.k === 'tup') {
                    this.bindPattern(el.name, this.coerce(ir_1.E.mkTup(bt.ts.slice(i).map((_, j) => ir_1.E.getTup(base, i + j))), restTy, el), fc, out, isConst);
                    return;
                }
                if (restTy.k !== 'arr')
                    (0, diag_1.reject)(el, 'unsupported', 'rest element of a tuple pattern');
                const parts = bt.ts.slice(i).map((_, j) => this.coerce(ir_1.E.getTup(base, i + j), restTy.t, el));
                this.bindPattern(el.name, ir_1.E.builtin(`(.arrOf ${(0, ty_2.showTy)(restTy.t)} ${parts.length})`, parts, parts.map(() => restTy.t), restTy), fc, out, isConst);
                return;
            }
            if (i >= bt.ts.length)
                (0, diag_1.reject)(el, 'unsupported', 'tuple pattern longer than the tuple');
            if (el.initializer)
                (0, diag_1.reject)(el, 'unsupported-syntax', 'default value in a tuple pattern');
            this.bindPattern(el.name, ir_1.E.getTup(base, i), fc, out, isConst);
        });
        return;
    }
    if (bt.k === 'arr') {
        elems.forEach((el, i) => {
            if (ts.isOmittedExpression(el))
                return;
            if (el.dotDotDotToken) {
                const sl = ir_1.E.builtin(`(.arrSlice ${(0, ty_2.showTy)(bt.t)})`, [base, (0, core_1.numLit)(i), ir_1.E.none(ty_1.T.num)], [bt, ty_1.T.num, ty_1.T.opt(ty_1.T.num)], bt);
                this.bindPattern(el.name, sl, fc, out, isConst);
                return;
            }
            if (el.initializer)
                (0, diag_1.reject)(el, 'unsupported-syntax', 'default value in an array pattern');
            const elTs = this.checker.getTypeAtLocation(el.name);
            const want = this.tyOf(elTs, fc, el.name);
            const get = want.k === 'opt' && bt.t.k !== 'opt'
                ? ir_1.E.builtin(`(.arrGetOpt ${(0, ty_2.showTy)(bt.t)})`, [base, (0, core_1.numLit)(i)], [bt, ty_1.T.num], ty_1.T.opt(bt.t))
                : ir_1.E.builtin(`(.arrGet ${(0, ty_2.showTy)(bt.t)})`, [base, (0, core_1.numLit)(i)], [bt, ty_1.T.num], bt.t);
            this.bindPattern(el.name, get, fc, out, isConst);
        });
        return;
    }
    (0, diag_1.reject)(p, bt.k === 'dyn' ? 'any-op' : 'unsupported', `array destructuring of ${(0, ty_1.prettyTy)(bt)}`);
};
const ty_2 = require("./ty");
// ---------------------------------------------------------------------------------------
// expression statements
P.lowerExprStmt = function (e0, fc, out) {
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
        const v = (0, ir_1.mkVar)('_', p.ty.t);
        fc.pre.push((0, ir_1.awaitItem)(v, p));
        return;
    }
    if (ts.isVoidExpression(e)) {
        this.lowerExprStmt(e.expression, fc, out);
        return;
    }
    if (ts.isConditionalExpression(e)) {
        const c = this.lowerCond(e.condition, fc);
        out.push((0, ir_1.stmtItem)(ir_1.S.ite(c, this.lowerBlockStmtsFromExpr(e.whenTrue, fc), this.lowerBlockStmtsFromExpr(e.whenFalse, fc))));
        return;
    }
    if (ts.isBinaryExpression(e) && (e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken || e.operatorToken.kind === ts.SyntaxKind.BarBarToken)) {
        // `c && f()` / `c || f()` used as statements
        const c = this.lowerCond(e.left, fc);
        const rhs = this.lowerBlockStmtsFromExpr(e.right, fc);
        out.push((0, ir_1.stmtItem)(e.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken ? ir_1.S.ite(c, rhs, []) : ir_1.S.ite(c, [], rhs)));
        return;
    }
    const v = this.lowerExpr(e, fc);
    out.push((0, ir_1.stmtItem)(ir_1.S.expr(v)));
};
P.lowerBlockStmtsFromExpr = function (e, fc) {
    const out = [];
    const saved = fc.pre;
    fc.pre = out;
    try {
        this.lowerExprStmt(e, fc, out);
    }
    finally {
        fc.pre = saved;
    }
    return out;
};
// ---------------------------------------------------------------------------------------
// narrowing
function isUndefinedExpr(tr, e) {
    e = skipParens(e);
    if (ts.isIdentifier(e) && e.text === 'undefined') {
        const s = tr.checker.getSymbolAtLocation(e);
        return !s || !tr.facts(s);
    }
    return ts.isVoidExpression(e) && ts.isNumericLiteral(skipParens(e.expression));
}
function isNullExpr(e) {
    return skipParens(e).kind === ts.SyntaxKind.NullKeyword;
}
P.narrowTest = function (cond0, fc) {
    const cond = skipParens(cond0);
    const varOf = (x) => {
        x = skipParens(x);
        if (!ts.isIdentifier(x))
            return null;
        const sym = this.symAt(x);
        if (!sym)
            return null;
        const b = this.lookup(sym, fc);
        if (!b || b.k !== 'var' || b.errVar)
            return null;
        return { sym, b };
    };
    const scrutOf = (b) => this.unfoldE(ir_1.E.var(b.v));
    // !x
    if (ts.isPrefixUnaryExpression(cond) && cond.operator === ts.SyntaxKind.ExclamationToken) {
        const inner = this.narrowTest(cond.operand, fc);
        if (!inner)
            return null;
        if (inner.kind === 'opt')
            return { ...inner, thenSome: !inner.thenSome };
        return { ...inner, toThen: inner.toThen.map(x => !x) };
    }
    // truthiness of an optional object / union with null
    if (ts.isIdentifier(cond)) {
        const vb = varOf(cond);
        if (!vb)
            return null;
        const scrut = scrutOf(vb.b);
        if (scrut.ty.k === 'opt' && (0, ty_1.isObjectLike)(this.unfoldTy(scrut.ty.t)))
            return { sym: vb.sym, scrut, kind: 'opt', thenSome: true, node: cond };
        if (scrut.ty.k === 'union' && scrut.ty.ts.some(m => m.k === 'null') && scrut.ty.ts.every(m => m.k === 'null' || (0, ty_1.isObjectLike)(this.unfoldTy(m)))) {
            return { sym: vb.sym, scrut, kind: 'union', toThen: scrut.ty.ts.map(m => m.k !== 'null'), node: cond };
        }
        return null;
    }
    if (!ts.isBinaryExpression(cond))
        return null;
    const op = cond.operatorToken.kind;
    // x == null / x != undefined: null and undefined at once
    if (op === ts.SyntaxKind.EqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsToken) {
        const eq = op === ts.SyntaxKind.EqualsEqualsToken;
        for (const [a, b] of [[cond.left, cond.right], [cond.right, cond.left]]) {
            if (!isUndefinedExpr(this, b) && !isNullExpr(b))
                continue;
            const vb = varOf(a);
            if (!vb)
                continue;
            const scrut = scrutOf(vb.b);
            // an optional or a union with null, seen as `opt T'` with both null and undefined as none
            // (not for unknown values: they keep their type)
            if (scrut.ty.k === 'opt' && this.unfoldTy(scrut.ty.t).k === 'dyn')
                return null;
            if (scrut.ty.k !== 'opt' && !(scrut.ty.k === 'union' && scrut.ty.ts.some(m => m.k === 'null')))
                return null;
            const opt = this.nullishToOpt(scrut, a);
            if (opt.ty.k !== 'opt')
                return null;
            return { sym: vb.sym, scrut: opt, kind: 'opt', thenSome: !eq, node: cond };
        }
        return null;
    }
    if (op !== ts.SyntaxKind.EqualsEqualsEqualsToken && op !== ts.SyntaxKind.ExclamationEqualsEqualsToken)
        return null;
    const eq = op === ts.SyntaxKind.EqualsEqualsEqualsToken;
    // x === undefined / x === null
    for (const [a, b] of [[cond.left, cond.right], [cond.right, cond.left]]) {
        const vb = varOf(a);
        if (!vb)
            continue;
        const scrut = scrutOf(vb.b);
        // (not for an optional unknown: an unknown holding undefined is undefined too)
        if (isUndefinedExpr(this, b) && scrut.ty.k === 'opt' && this.unfoldTy(scrut.ty.t).k !== 'dyn')
            return { sym: vb.sym, scrut, kind: 'opt', thenSome: !eq, node: cond };
        if (isNullExpr(b) && scrut.ty.k === 'union' && scrut.ty.ts.some(m => m.k === 'null')) {
            return { sym: vb.sym, scrut, kind: 'union', toThen: scrut.ty.ts.map(m => (m.k === 'null') === eq), node: cond };
        }
    }
    // typeof x === "tag"
    for (const [a, b] of [[cond.left, cond.right], [cond.right, cond.left]]) {
        const ta = skipParens(a), tb = skipParens(b);
        if (ts.isTypeOfExpression(ta) && ts.isStringLiteral(tb)) {
            const vb = varOf(ta.expression);
            if (!vb)
                return null;
            const scrut = scrutOf(vb.b);
            const tag = tb.text;
            if (scrut.ty.k === 'opt') {
                // typeof x === "undefined" splits an optional
                if (tag === 'undefined')
                    return this.unfoldTy(scrut.ty.t).k === 'dyn' ? null : { sym: vb.sym, scrut, kind: 'opt', thenSome: !eq, node: cond };
                if (this.typeofTag(scrut.ty.t) === tag)
                    return { sym: vb.sym, scrut, kind: 'opt', thenSome: eq, node: cond };
                return null;
            }
            if (scrut.ty.k === 'union') {
                return { sym: vb.sym, scrut, kind: 'union', toThen: scrut.ty.ts.map(m => (this.typeofTag(m) === tag) === eq), node: cond };
            }
            return null;
        }
    }
    // x.kind === "lit" (discriminated union)
    for (const [a, b] of [[cond.left, cond.right], [cond.right, cond.left]]) {
        const pa = skipParens(a), lit = skipParens(b);
        if (!ts.isPropertyAccessExpression(pa) || !ts.isStringLiteral(lit))
            continue;
        const vb = varOf(pa.expression);
        if (!vb)
            continue;
        const scrut = scrutOf(vb.b);
        if (scrut.ty.k !== 'union')
            continue;
        const toThen = this.discriminantSplit(scrut.ty, pa.expression, pa.name.text, [lit.text], fc);
        if (!toThen)
            continue;
        return { sym: vb.sym, scrut, kind: 'union', toThen: toThen.map(x => x === eq), node: cond };
    }
    return null;
};
P.discriminantSplit = function (u, baseNode, prop, values, fc) {
    const sym = this.symAt(baseNode);
    if (!sym)
        return null;
    const declT = this.checker.getTypeOfSymbol(sym);
    const tsMembers = (declT.isUnion() ? declT.types : [declT]).filter(m => !(m.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null)));
    const res = u.ts.map(() => undefined);
    for (const m of tsMembers) {
        let ir;
        try {
            ir = this.tyOf(m, fc, baseNode);
        }
        catch {
            return null;
        }
        const idx = u.ts.findIndex(x => (0, ty_1.tyEq)(x, ir));
        if (idx < 0)
            return null;
        const p = this.checker.getPropertyOfType(m, prop);
        if (!p)
            return null;
        const pt = this.checker.getTypeOfSymbol(p);
        const lits = (pt.isUnion() ? pt.types : [pt]);
        if (!lits.every(l => l.flags & ts.TypeFlags.StringLiteral))
            return null;
        const hits = lits.map(l => values.includes(l.value));
        if (hits.some(h => h) && hits.some(h => !h))
            return null;
        const r = hits[0];
        if (res[idx] !== undefined && res[idx] !== r)
            return null;
        res[idx] = r;
    }
    return res.map(x => x ?? false);
};
P.withNarrowed = function (t, thenSide, fc, f) {
    const u = t.scrut.ty;
    const members = u.ts.filter((_, k) => t.toThen[k] === thenSide);
    if (members.length === u.ts.length || members.length === 0)
        return f();
    const nt = members.length === 1 ? members[0] : ty_1.T.union(members);
    const v = (0, ir_1.mkVar)(t.sym.name, nt);
    const init = this.adapt(t.scrut, nt, t.node);
    fc.push();
    fc.bind(t.sym, { k: 'var', v });
    try {
        return [(0, ir_1.declItem)(v, init), ...f()];
    }
    finally {
        fc.pop();
    }
};
P.applyNarrow = function (t, thenB, elseB, fc) {
    if (t.kind === 'opt') {
        const inner = t.scrut.ty.t;
        const v = (0, ir_1.mkVar)(t.sym.name, inner);
        const some = () => {
            fc.push();
            fc.bind(t.sym, { k: 'var', v });
            try {
                return t.thenSome ? thenB(fc) : elseB(fc);
            }
            finally {
                fc.pop();
            }
        };
        const none = () => (t.thenSome ? elseB(fc) : thenB(fc));
        const someBlock = some();
        const noneBlock = none();
        return { k: 'caseOptS', e: t.scrut, none: noneBlock, v, some: someBlock };
    }
    const u = t.scrut.ty;
    const alts = u.ts.map((m, i) => {
        const v = (0, ir_1.mkVar)(t.sym.name, m);
        fc.push();
        fc.bind(t.sym, { k: 'var', v });
        try {
            return { v, body: t.toThen[i] ? thenB(fc) : elseB(fc) };
        }
        finally {
            fc.pop();
        }
    });
    return { k: 'caseUS', e: t.scrut, alts };
};
// ---------------------------------------------------------------------------------------
// jumps
P.breakDepth = function (fc, label, node) {
    for (let i = fc.jumps.length - 1, n = 0; i >= 0; i--, n++) {
        const j = fc.jumps[i];
        if (label ? j.labels.includes(label) : j.breakTarget)
            return n;
    }
    (0, diag_1.reject)(node, 'unsupported', label ? `no enclosing loop labelled ${label}` : '`break` outside of a loop or switch');
};
P.contDepth = function (fc, label, node) {
    let n = 0;
    for (let i = fc.jumps.length - 1; i >= 0; i--) {
        const j = fc.jumps[i];
        if (j.kind !== 'loop')
            continue;
        if (!label || j.labels.includes(label))
            return n;
        n++;
    }
    (0, diag_1.reject)(node, 'unsupported', label ? `no enclosing loop labelled ${label}` : '`continue` outside of a loop');
};
function loopJump(labels) { return { kind: 'loop', labels, breakTarget: true }; }
function notE(c) { return ir_1.E.not(c); }
function lowerWhile(tr, s, fc, out, labels) {
    const [c, preC] = tr.isolate(fc, () => tr.lowerCond(s.expression, fc));
    fc.jumps.push(loopJump(labels));
    let body;
    try {
        body = tr.lowerSubStmt(s.statement, fc);
    }
    finally {
        fc.jumps.pop();
    }
    if (!preC.length) {
        out.push((0, ir_1.stmtItem)({ k: 'while', c, body }));
        return;
    }
    out.push((0, ir_1.stmtItem)({ k: 'while', c: ir_1.E.bool(true), body: [...preC, (0, ir_1.stmtItem)(ir_1.S.ite(notE(c), [(0, ir_1.stmtItem)({ k: 'brk', n: 0 })], [])), ...body] }));
}
function lowerDo(tr, s, fc, out, labels) {
    fc.jumps.push(loopJump(labels));
    let body;
    try {
        body = tr.lowerSubStmt(s.statement, fc);
    }
    finally {
        fc.jumps.pop();
    }
    const [c, preC] = tr.isolate(fc, () => tr.lowerCond(s.expression, fc));
    if (!preC.length) {
        out.push((0, ir_1.stmtItem)({ k: 'doWhile', body, c }));
        return;
    }
    // let first = true; while (true) { if (!first) { pre; if (!c) break; } first = false; body }
    const first = (0, ir_1.mkVar)('first', ty_1.T.bool, true);
    const items = [(0, ir_1.declItem)(first, ir_1.E.bool(true))];
    const check = [...preC, (0, ir_1.stmtItem)(ir_1.S.ite(notE(c), [(0, ir_1.stmtItem)({ k: 'brk', n: 0 })], []))];
    items.push((0, ir_1.stmtItem)({ k: 'while', c: ir_1.E.bool(true), body: [(0, ir_1.stmtItem)(ir_1.S.ite(notE(ir_1.E.var(first)), check, [])), (0, ir_1.stmtItem)(ir_1.S.assign(first, ir_1.E.bool(false))), ...body] }));
    out.push((0, ir_1.stmtItem)({ k: 'block', b: items }));
}
function lowerFor(tr, s, fc, out, labels) {
    fc.push();
    const items = [];
    const saved = fc.pre;
    fc.pre = items;
    const loopVars = [];
    try {
        if (s.initializer) {
            if (ts.isVariableDeclarationList(s.initializer)) {
                const flags = s.initializer.flags;
                const kind = flags & ts.NodeFlags.BlockScoped;
                if (kind !== ts.NodeFlags.Let && kind !== ts.NodeFlags.Const)
                    (0, diag_1.reject)(s.initializer, 'no-var', '`var` declarations are not allowed; use `let` or `const`');
                for (const d of s.initializer.declarations) {
                    tr.lowerVarDecl(d, kind === ts.NodeFlags.Const, fc, items);
                    if (ts.isIdentifier(d.name)) {
                        const sym = tr.symAt(d.name);
                        if (sym)
                            loopVars.push(sym);
                    }
                }
            }
            else
                tr.lowerExprStmt(s.initializer, fc, items);
        }
    }
    finally {
        fc.pre = saved;
    }
    // per-iteration copies of loop variables captured by closures in the body
    for (const sym of loopVars) {
        const f = tr.facts(sym);
        if (!f || !f.captured)
            continue;
        if (f.capturedRefs.some(r => !(0, core_1.within)(r, s.statement)))
            (0, diag_1.reject)(s, 'unsupported', `closure in the loop head captures loop variable ${sym.name}`);
        if (tr.writtenWithin(sym, s.statement))
            (0, diag_1.reject)(s, 'unsupported', `closure captures loop variable ${sym.name}, which the loop body modifies`);
    }
    const [c, preC] = tr.isolate(fc, () => s.condition ? tr.lowerCond(s.condition, fc) : ir_1.E.bool(true));
    let step = [];
    if (s.incrementor)
        step = tr.lowerBlockStmtsFromExpr(s.incrementor, fc);
    fc.jumps.push(loopJump(labels));
    fc.push();
    let body;
    try {
        const copies = [];
        for (const sym of loopVars) {
            const f = tr.facts(sym);
            if (!f || !f.captured)
                continue;
            const b = tr.lookup(sym, fc);
            if (!b || b.k !== 'var')
                continue;
            const copy = (0, ir_1.mkVar)(sym.name, b.v.ty);
            copies.push((0, ir_1.declItem)(copy, ir_1.E.var(b.v)));
            fc.bind(sym, { k: 'var', v: copy });
        }
        body = [...copies, ...tr.lowerSubStmt(s.statement, fc)];
    }
    finally {
        fc.pop();
        fc.jumps.pop();
        fc.pop();
    }
    if (!preC.length)
        items.push((0, ir_1.stmtItem)({ k: 'forLoop', c, body, step }));
    else
        items.push((0, ir_1.stmtItem)({ k: 'forLoop', c: ir_1.E.bool(true), body: [...preC, (0, ir_1.stmtItem)(ir_1.S.ite(notE(c), [(0, ir_1.stmtItem)({ k: 'brk', n: 0 })], [])), ...body], step }));
    if (hasDecls(items))
        out.push((0, ir_1.stmtItem)({ k: 'block', b: items }));
    else
        out.push(...items);
}
P.lowerIterable = function (e, fc) {
    const n = skipParens(e);
    // live iteration over map.keys()/values()/entries(), set.values()/keys(), arr.entries()/values()
    if (ts.isCallExpression(n) && ts.isPropertyAccessExpression(n.expression) && n.arguments.length === 0) {
        const m = n.expression.name.text;
        const recv = this.unfoldTy(this.tyAt(n.expression.expression, fc));
        if (recv.k === 'map' && (m === 'keys' || m === 'values' || m === 'entries')) {
            const coll = this.unfoldE(this.lowerExpr(n.expression.expression, fc));
            const tupT = ty_1.T.tup([recv.key, recv.val]);
            return { kind: 'forOfMap', coll, elem: tupT, proj: m === 'entries' ? undefined : (v) => ir_1.E.getTup(v, m === 'keys' ? 0 : 1) };
        }
        if (recv.k === 'set' && (m === 'values' || m === 'keys')) {
            const coll = this.unfoldE(this.lowerExpr(n.expression.expression, fc));
            return { kind: 'forOfSet', coll, elem: recv.t };
        }
        if (recv.k === 'arr' && (m === 'entries' || m === 'values')) {
            const coll = this.unfoldE(this.lowerExpr(n.expression.expression, fc));
            if (m === 'values')
                return { kind: 'forOf', coll, elem: recv.t };
            return { kind: 'forOf', coll, elem: recv.t, indexed: true };
        }
    }
    let coll = this.unfoldE(this.lowerExpr(n, fc));
    if ((0, ir_1.isPoison)(coll))
        return { kind: 'forOf', coll, elem: ty_1.T.undef };
    if (coll.ty.k === 'tup' && coll.ty.ts.length > 0 && coll.ty.ts.every(x => (0, ty_1.tyEq)(x, coll.ty.ts[0]))) {
        // a homogeneous tuple (e.g. a literal `as const`) iterates like an array of its elements
        const tt = coll.ty;
        const at = ty_1.T.arr(tt.ts[0]);
        coll = this.withValue(coll, 'p', x => ir_1.E.builtin(`(.arrOf ${(0, ty_2.showTy)(tt.ts[0])} ${tt.ts.length})`, tt.ts.map((_, i) => ir_1.E.getTup(x, i)), tt.ts.map(() => tt.ts[0]), at));
    }
    const t = coll.ty;
    switch (t.k) {
        case 'arr': return { kind: 'forOf', coll, elem: t.t };
        case 'map': return { kind: 'forOfMap', coll, elem: ty_1.T.tup([t.key, t.val]) };
        case 'set': return { kind: 'forOfSet', coll, elem: t.t };
        case 'str': return { kind: 'forOfStr', coll, elem: ty_1.T.str };
        case 'enum': return { kind: 'forOfStr', coll: this.toStr(coll, e), elem: ty_1.T.str };
    }
    if (t.k === 'dyn')
        return { kind: 'forOf', coll, elem: ty_1.T.dyn, dyn: true };
    (0, diag_1.reject)(e, 'unsupported', `for…of over ${(0, ty_1.prettyTy)(t)}`);
};
function lowerForOf(tr, s, fc, out, labels) {
    if (s.awaitModifier)
        (0, diag_1.reject)(s, 'unsupported-syntax', '`for await`');
    if (!ts.isVariableDeclarationList(s.initializer))
        (0, diag_1.reject)(s.initializer, 'unsupported-syntax', '`for (x of …)` with an existing variable; declare it with const/let');
    const list = s.initializer;
    const lkind = list.flags & ts.NodeFlags.BlockScoped;
    if (lkind !== ts.NodeFlags.Let && lkind !== ts.NodeFlags.Const)
        (0, diag_1.reject)(list, 'no-var', '`var` declarations are not allowed; use `let` or `const`');
    const decl = list.declarations[0];
    const isConst = lkind === ts.NodeFlags.Const;
    const it = tr.lowerIterable(s.expression, fc);
    if ((0, ir_1.isPoison)(it.coll)) {
        fc.jumps.push(loopJump(labels));
        fc.push();
        try {
            bindPatternPoison(tr, decl.name, fc);
            const body = tr.lowerSubStmt(s.statement, fc);
            out.push((0, ir_1.stmtItem)({ k: 'block', b: body }));
        }
        finally {
            fc.pop();
            fc.jumps.pop();
        }
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
        (0, ty_1.tyEq)(tr.tyOf(tr.checker.getTypeOfSymbol(directSym), fc, decl.name), it.elem);
    const v = (0, ir_1.mkVar)(direct ? decl.name.text : 'x', it.elem);
    fc.jumps.push(loopJump(labels));
    fc.push();
    let body;
    try {
        const items = [];
        const saved = fc.pre;
        fc.pre = items;
        try {
            if (direct)
                fc.bind(directSym, { k: 'var', v });
            else {
                const val = it.proj ? it.proj(ir_1.E.var(v)) : ir_1.E.var(v);
                tr.bindPattern(decl.name, val, fc, items, isConst);
            }
        }
        finally {
            fc.pre = saved;
        }
        body = [...items, ...tr.lowerSubStmt(s.statement, fc)];
    }
    finally {
        fc.pop();
        fc.jumps.pop();
    }
    out.push((0, ir_1.stmtItem)({ k: it.kind, e: it.coll, v, body }));
}
/** `for (const [i, x] of arr.entries())` as an index loop (the array iterator re-reads the
 * length at every step, like the loop condition). */
function lowerIndexedForOf(tr, s, decl, isConst, arr, fc, out, labels) {
    const at = arr.ty;
    const items = [];
    const a = (0, ir_1.mkVar)('a', at);
    items.push((0, ir_1.declItem)(a, arr));
    const i = (0, ir_1.mkVar)('i', ty_1.T.num, true);
    items.push((0, ir_1.declItem)(i, (0, core_1.numLit)(0)));
    const len = ir_1.E.builtin(`(.arrLength ${(0, ty_2.showTy)(at.t)})`, [ir_1.E.var(a)], [at], ty_1.T.num);
    const c = ir_1.E.prim('(.numCmp .lt)', [ir_1.E.var(i), len], [ty_1.T.num, ty_1.T.num], ty_1.T.bool);
    const step = [(0, ir_1.stmtItem)(ir_1.S.assign(i, ir_1.E.prim('(.numBin .add)', [ir_1.E.var(i), (0, core_1.numLit)(1)], [ty_1.T.num, ty_1.T.num], ty_1.T.num)))];
    fc.jumps.push(loopJump(labels));
    fc.push();
    let body;
    try {
        const bitems = [];
        const ic = (0, ir_1.mkVar)('i', ty_1.T.num);
        bitems.push((0, ir_1.declItem)(ic, ir_1.E.var(i)));
        const el = ir_1.E.builtin(`(.arrGet ${(0, ty_2.showTy)(at.t)})`, [ir_1.E.var(a), ir_1.E.var(ic)], [at, ty_1.T.num], at.t);
        const saved = fc.pre;
        fc.pre = bitems;
        try {
            tr.bindPattern(decl.name, ir_1.E.mkTup([ir_1.E.var(ic), el]), fc, bitems, isConst);
        }
        finally {
            fc.pre = saved;
        }
        body = [...bitems, ...tr.lowerSubStmt(s.statement, fc)];
    }
    finally {
        fc.pop();
        fc.jumps.pop();
    }
    items.push((0, ir_1.stmtItem)({ k: 'forLoop', c, body, step }));
    out.push((0, ir_1.stmtItem)({ k: 'block', b: items }));
}
/** `for (const x of u)` with `u` unknown: an array (of any element type) iterated by index,
reading each element as unknown and the length at every step (the array iterator); other
runtime values (strings, Maps, Sets held as unknown) are not modelled: a panic. */
function lowerDynForOf(tr, s, decl, isConst, u, fc, out, labels) {
    const items = [];
    const d = (0, ir_1.mkVar)('d', ty_1.T.dyn);
    items.push((0, ir_1.declItem)(d, u));
    // (a declaration gives the panicking `unwrap none` its type)
    items.push((0, ir_1.stmtItem)(ir_1.S.ite(ir_1.E.prim('.dynIsArray', [ir_1.E.var(d)], [ty_1.T.dyn], ty_1.T.bool), [], [(0, ir_1.declItem)((0, ir_1.mkVar)('notArray', ty_1.T.undef), ir_1.E.unreachable(ty_1.T.undef))])));
    const i = (0, ir_1.mkVar)('i', ty_1.T.num, true);
    items.push((0, ir_1.declItem)(i, (0, core_1.numLit)(0)));
    const get = (k) => ir_1.E.builtin('.dynGet', [ir_1.E.var(d), k], [ty_1.T.dyn, ty_1.T.str], ty_1.T.dyn);
    const len = ir_1.E.unwrap(ir_1.E.prim('(.dynCast .num)', [get((0, core_1.strLit)('length'))], [ty_1.T.dyn], ty_1.T.opt(ty_1.T.num)));
    const c = ir_1.E.prim('(.numCmp .lt)', [ir_1.E.var(i), len], [ty_1.T.num, ty_1.T.num], ty_1.T.bool);
    const step = [(0, ir_1.stmtItem)(ir_1.S.assign(i, ir_1.E.prim('(.numBin .add)', [ir_1.E.var(i), (0, core_1.numLit)(1)], [ty_1.T.num, ty_1.T.num], ty_1.T.num)))];
    fc.jumps.push(loopJump(labels));
    fc.push();
    let body;
    try {
        const bitems = [];
        const el = get(ir_1.E.prim('.numToStr', [ir_1.E.var(i)], [ty_1.T.num], ty_1.T.str));
        const saved = fc.pre;
        fc.pre = bitems;
        try {
            tr.bindPattern(decl.name, el, fc, bitems, isConst);
        }
        finally {
            fc.pre = saved;
        }
        body = [...bitems, ...tr.lowerSubStmt(s.statement, fc)];
    }
    finally {
        fc.pop();
        fc.jumps.pop();
    }
    items.push((0, ir_1.stmtItem)({ k: 'forLoop', c, body, step }));
    out.push((0, ir_1.stmtItem)({ k: 'block', b: items }));
}
// ---------------------------------------------------------------------------------------
// switch
function lowerSwitch(tr, s, fc, out) {
    const clauses = s.caseBlock.clauses;
    // fallthrough check; strip one trailing `break` per clause
    const bodies = [];
    clauses.forEach((cl, i) => {
        let st = [...cl.statements];
        if (st.length === 1 && ts.isBlock(st[0]))
            st = [...st[0].statements];
        if (st.length && ts.isBreakStatement(st[st.length - 1]) && !st[st.length - 1].label)
            st = st.slice(0, -1);
        else if (st.length && i < clauses.length - 1 && !tsAlwaysAbrupt(cl.statements[cl.statements.length - 1])) {
            (0, diag_1.reject)(cl, 'switch-fallthrough', 'a non-empty switch case must end with break/return/throw/continue');
        }
        bodies.push(st);
    });
    const needBreakable = clauses.some((cl, i) => bodies[i].some(st => containsSwitchBreak(st)));
    const groups = [];
    let pending = [];
    let pendingDefault = false;
    clauses.forEach((cl, i) => {
        if (ts.isDefaultClause(cl))
            pendingDefault = true;
        else
            pending.push(cl.expression);
        if (cl.statements.length > 0 || i === clauses.length - 1) {
            groups.push({ tests: pending, isDefault: pendingDefault, body: bodies[i], node: cl });
            pending = [];
            pendingDefault = false;
        }
    });
    const jump = { kind: 'breakable', labels: [], breakTarget: true };
    const lowerBody = (g) => {
        if (needBreakable)
            fc.jumps.push(jump);
        try {
            return tr.lowerBlockStmts(g.body, fc);
        }
        finally {
            if (needBreakable)
                fc.jumps.pop();
        }
    };
    const items = [];
    const saved = fc.pre;
    fc.pre = items;
    try {
        // discriminated union switch: switch (x.kind) with x a union variable
        const disc = skipParens(s.expression);
        if (ts.isPropertyAccessExpression(disc) && ts.isIdentifier(disc.expression)) {
            const sym = tr.symAt(disc.expression);
            const b = sym && tr.isRebindable(sym, fc, s.caseBlock);
            if (sym && b && b.k === 'var') {
                const scrut = tr.unfoldE(ir_1.E.var(b.v));
                if (scrut.ty.k === 'union' && groups.every(g => g.tests.every(t => ts.isStringLiteral(skipParens(t))))) {
                    const u = scrut.ty;
                    const memberGroup = u.ts.map(() => undefined);
                    let ok = true;
                    for (const g of groups) {
                        if (g.isDefault)
                            continue;
                        const split = tr.discriminantSplit(u, disc.expression, disc.name.text, g.tests.map(t => skipParens(t).text), fc);
                        if (!split) {
                            ok = false;
                            break;
                        }
                        split.forEach((hit, i) => { if (hit && !memberGroup[i])
                            memberGroup[i] = g; });
                    }
                    const dflt = groups.find(g => g.isDefault);
                    if (ok) {
                        const uses = new Map();
                        u.ts.forEach((_, i) => { const g = memberGroup[i] ?? dflt; if (g)
                            uses.set(g, (uses.get(g) ?? 0) + 1); });
                        const dup = [...uses.entries()].some(([g, n]) => n > 1 && g.body.length > 0);
                        if (!dup) {
                            const alts = u.ts.map((m, i) => {
                                const v = (0, ir_1.mkVar)(sym.name, m);
                                fc.push();
                                fc.bind(sym, { k: 'var', v });
                                try {
                                    const g = memberGroup[i] ?? dflt;
                                    return { v, body: g ? lowerBody(g) : [] };
                                }
                                finally {
                                    fc.pop();
                                }
                            });
                            const st = { k: 'caseUS', e: scrut, alts };
                            items.push((0, ir_1.stmtItem)(st));
                            if (needBreakable)
                                out.push((0, ir_1.stmtItem)({ k: 'breakable', b: items }));
                            else if (hasDecls(items))
                                out.push((0, ir_1.stmtItem)({ k: 'block', b: items }));
                            else
                                out.push(...items);
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
        let chain = dflt ? lowerBody(dflt) : [];
        for (let gi = groups.length - 1; gi >= 0; gi--) {
            const g = groups[gi];
            if (!g.tests.length)
                continue;
            const [test, preT] = tr.isolate(fc, () => {
                let acc = null;
                for (const t of g.tests) {
                    const c = tr.strictEqExprs(ir_1.E.var(dv), tr.lowerExpr(t, fc), t, fc);
                    acc = acc ? ir_1.E.or(acc, c) : c;
                }
                return acc;
            });
            if (preT.length)
                (0, diag_1.reject)(g.node, 'unsupported', 'case expression with await/assignments');
            chain = [(0, ir_1.stmtItem)(ir_1.S.ite(test, lowerBody(g), chain))];
        }
        items.push(...chain);
    }
    finally {
        fc.pre = saved;
    }
    if (needBreakable)
        out.push((0, ir_1.stmtItem)({ k: 'breakable', b: items }));
    else if (hasDecls(items))
        out.push((0, ir_1.stmtItem)({ k: 'block', b: items }));
    else
        out.push(...items);
}
function tsAlwaysAbrupt(s) {
    if (!s)
        return false;
    if (ts.isReturnStatement(s) || ts.isThrowStatement(s) || ts.isBreakStatement(s) || ts.isContinueStatement(s))
        return true;
    if (ts.isBlock(s))
        return s.statements.length > 0 && tsAlwaysAbrupt(s.statements[s.statements.length - 1]);
    if (ts.isIfStatement(s))
        return !!s.elseStatement && tsAlwaysAbrupt(s.thenStatement) && tsAlwaysAbrupt(s.elseStatement);
    return false;
}
/** Does `n` contain an unlabelled `break` that targets the enclosing switch? */
function containsSwitchBreak(n) {
    if (ts.isBreakStatement(n))
        return !n.label;
    if (ts.isIterationStatement(n, false) || ts.isSwitchStatement(n) || ts.isFunctionLike(n) || ts.isClassLike(n))
        return false;
    let found = false;
    ts.forEachChild(n, c => { if (!found && containsSwitchBreak(c))
        found = true; });
    return found;
}
// ---------------------------------------------------------------------------------------
// try / return
function lowerTry(tr, s, fc, out) {
    const body = tr.lowerBlockStmts(s.tryBlock.statements, fc);
    const fin = s.finallyBlock ? tr.lowerBlockStmts(s.finallyBlock.statements, fc) : [];
    if (!s.catchClause) {
        out.push((0, ir_1.stmtItem)({ k: 'tryFin', body, fin }));
        return;
    }
    const cv = s.catchClause.variableDeclaration;
    const v = (0, ir_1.mkVar)(cv && ts.isIdentifier(cv.name) ? cv.name.text : 'e', ty_1.T.err);
    fc.push();
    let handler;
    try {
        if (cv) {
            if (!ts.isIdentifier(cv.name))
                (0, diag_1.reject)(cv, 'unsupported-syntax', 'destructuring catch parameter');
            const sym = tr.symAt(cv.name);
            if (tr.isReassigned(sym))
                (0, diag_1.reject)(cv, 'unsupported', 'reassigned catch variable');
            fc.bind(sym, { k: 'var', v, errVar: true });
        }
        handler = tr.lowerBlockStmts(s.catchClause.block.statements, fc);
    }
    finally {
        fc.pop();
    }
    out.push((0, ir_1.stmtItem)({ k: 'try', body, v, handler, fin }));
}
function lowerReturn(tr, s, fc, out) {
    if (fc.kind === 'main')
        (0, diag_1.reject)(s, 'unsupported-syntax', '`return` at module level');
    if (fc.retPoison) {
        // coverage mode: the return type has no IR type (already recorded)
        if (s.expression)
            tr.lowerExpr(s.expression, fc);
        out.push((0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.poison(ty_1.T.undef))));
        return;
    }
    if (fc.isCtor) {
        if (s.expression)
            (0, diag_1.reject)(s, 'unsupported', 'returning a value from a constructor');
        out.push((0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.var(fc.thisVar))));
        return;
    }
    if (!s.expression) {
        if (fc.bodyRet.k === 'opt') {
            out.push((0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.none(fc.bodyRet.t))));
            return;
        }
        if (fc.bodyRet.k !== 'undef')
            (0, diag_1.reject)(s, 'unsupported', `\`return;\` in a function returning ${(0, ty_1.prettyTy)(fc.bodyRet)}`);
        out.push((0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.undef())));
        return;
    }
    const tsT = tr.checker.getTypeAtLocation(s.expression);
    if (fc.async) {
        const nat = tr.tyOf(tsT, fc, s.expression);
        if (nat.k === 'promise') {
            const p = tr.lowerExpr(s.expression, fc, ty_1.T.promise(fc.bodyRet));
            out.push((0, ir_1.stmtItem)({ k: 'retP', e: p }));
            return;
        }
    }
    if (fc.bodyRet.k === 'undef') {
        const e = tr.lowerExpr(s.expression, fc);
        if (e.ty.k === 'undef') {
            out.push((0, ir_1.stmtItem)(ir_1.S.ret(e)));
            return;
        }
        out.push((0, ir_1.stmtItem)(ir_1.S.expr(e)));
        out.push((0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.undef())));
        return;
    }
    if (fc.bodyRet.k === 'bool' && fc.kind === 'lambda' && tr.tyAt(s.expression, fc).k !== 'bool') {
        out.push((0, ir_1.stmtItem)(ir_1.S.ret(tr.truthy(tr.lowerExpr(s.expression, fc), s.expression))));
        return;
    }
    out.push((0, ir_1.stmtItem)(ir_1.S.ret(tr.lowerExpr(s.expression, fc, fc.bodyRet))));
}

"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.S = exports.E = exports.InternalError = void 0;
exports.mkVar = mkVar;
exports.funArgs = funArgs;
exports.funTy = funTy;
exports.isPoison = isPoison;
exports.stmtItem = stmtItem;
exports.declItem = declItem;
exports.awaitItem = awaitItem;
exports.isStable = isStable;
exports.blockAlwaysAbrupt = blockAlwaysAbrupt;
exports.stmtAlwaysAbrupt = stmtAlwaysAbrupt;
// The StrictTS IR on the TypeScript side, with named variables. `emit.ts` turns it into
// the de Bruijn terms of `StrictTS/Core/Syntax.lean`.
const ty_1 = require("./ty");
let nextVarId = 0;
function mkVar(name, ty, mayChange = false) {
    return { id: nextVarId++, name, ty, assigned: false, mayChange };
}
function funArgs(f) { return f.params.map(p => p.ty); }
function funTy(f) { return ty_1.T.fn(funArgs(f), f.ret); }
class InternalError extends Error {
}
exports.InternalError = InternalError;
function check(cond, msg) {
    if (!cond)
        throw new InternalError(msg);
}
function expectTy(e, t, what) {
    if (!(0, ty_1.tyEq)(e.ty, t))
        throw new InternalError(`${what}: expected ${(0, ty_1.prettyTy)(t)}, got ${(0, ty_1.prettyTy)(e.ty)}`);
}
// ---------------------------------------------------------------------------------------
// Smart constructors (type-checked: an ill-typed IR term is an internal error)
exports.E = {
    lit(lean, ty, js) { return { k: 'lit', lean, ty, js }; },
    var(v) { return { k: 'var', v, ty: v.ty }; },
    gget(g) { return { k: 'gget', g, ty: g.ty }; },
    prim(op, args, argTys, ty) {
        check(args.length === argTys.length, `prim ${op}: arity`);
        args.forEach((a, i) => expectTy(a, argTys[i], `prim ${op} arg ${i}`));
        return { k: 'prim', op, args, ty };
    },
    builtin(op, args, argTys, ty) {
        check(args.length === argTys.length, `builtin ${op}: arity ${args.length} vs ${argTys.length}`);
        args.forEach((a, i) => expectTy(a, argTys[i], `builtin ${op} arg ${i}`));
        return { k: 'builtin', op, args, ty };
    },
    and(a, b) { expectTy(a, ty_1.T.bool, 'and'); expectTy(b, ty_1.T.bool, 'and'); return { k: 'and', a, b, ty: ty_1.T.bool }; },
    or(a, b) { expectTy(a, ty_1.T.bool, 'or'); expectTy(b, ty_1.T.bool, 'or'); return { k: 'or', a, b, ty: ty_1.T.bool }; },
    cond(c, a, b) {
        expectTy(c, ty_1.T.bool, 'cond');
        expectTy(b, a.ty, 'cond branches');
        return { k: 'cond', c, a, b, ty: a.ty };
    },
    letE(v, init, body) {
        expectTy(init, v.ty, 'letE init');
        return { k: 'letE', v, init, body, ty: body.ty };
    },
    call(f, args) {
        check(args.length === f.params.length, `call ${f.name}: arity`);
        args.forEach((a, i) => expectTy(a, f.params[i].ty, `call ${f.name} arg ${i}`));
        return { k: 'call', f, args, ty: f.ret };
    },
    app(f, args) {
        check(f.ty.k === 'fn', 'app of non-function');
        const ft = f.ty;
        check(args.length === ft.args.length, 'app arity');
        args.forEach((a, i) => expectTy(a, ft.args[i], `app arg ${i}`));
        return { k: 'app', f, args, ty: ft.ret };
    },
    lam(async, params, ret, body) {
        return { k: 'lam', async, params, body, ty: ty_1.T.fn(params.map(p => p.ty), async ? ty_1.T.promise(ret) : ret) };
    },
    funVal(f) { return { k: 'funVal', f, ty: funTy(f) }; },
    mkTup(args) { return { k: 'mkTup', args, ty: ty_1.T.tup(args.map(a => a.ty)) }; },
    getTup(e, idx) {
        check(e.ty.k === 'tup', 'getTup of non-tuple');
        const ts = e.ty.ts;
        check(idx < ts.length, 'getTup index');
        return { k: 'getTup', e, idx, ty: ts[idx] };
    },
    mkRec(ty, args) {
        check(ty.k === 'record', 'mkRec type');
        const fs = ty.fs;
        check(fs.length === args.length, 'mkRec arity');
        args.forEach((a, i) => expectTy(a, fs[i].ty, `mkRec field ${fs[i].name}`));
        return { k: 'mkRec', args, ty };
    },
    getRec(e, idx) {
        check(e.ty.k === 'record', 'getRec of non-record');
        const fs = e.ty.fs;
        return { k: 'getRec', e, idx, ty: fs[idx].ty };
    },
    newObj(c) { return { k: 'newObj', c, ty: ty_1.T.obj(c) }; },
    getField(e, c, idx, fieldTy) {
        expectTy(e, ty_1.T.obj(c), 'getField');
        return { k: 'getField', e, c, idx, ty: fieldTy };
    },
    // (`unfold (fold e)` and `fold (unfold e)` are `e`: emitted as written, Lean could not infer
    // the name of the type between them)
    fold(n, e) {
        if (e.k === 'unfold' && e.n === n)
            return e.e;
        return { k: 'fold', n, e, ty: ty_1.T.named(n) };
    },
    unfold(n, e, aliasTy) {
        expectTy(e, ty_1.T.named(n), 'unfold');
        if (e.k === 'fold' && e.n === n)
            return e.e;
        return { k: 'unfold', n, e, ty: aliasTy };
    },
    none(t) { return { k: 'none', ty: ty_1.T.opt(t) }; },
    some(e) { return { k: 'some', e, ty: ty_1.T.opt(e.ty) }; },
    unwrap(e) {
        check(e.ty.k === 'opt', 'unwrap of non-optional');
        return { k: 'unwrap', e, ty: e.ty.t };
    },
    caseOpt(e, none, v, some) {
        check(e.ty.k === 'opt', 'caseOpt of non-optional');
        expectTy(exports.E.var(v), e.ty.t, 'caseOpt binder');
        expectTy(some, none.ty, 'caseOpt branches');
        return { k: 'caseOpt', e, none, v, some, ty: none.ty };
    },
    inj(ty, idx, e) {
        check(ty.k === 'union', 'inj into non-union');
        expectTy(e, ty.ts[idx], 'inj member');
        return { k: 'inj', idx, e, ty };
    },
    caseU(e, alts) {
        check(e.ty.k === 'union', 'caseU of non-union');
        const ts = e.ty.ts;
        check(ts.length === alts.length && alts.length > 0, 'caseU arity');
        alts.forEach((a, i) => { expectTy(exports.E.var(a.v), ts[i], 'caseU binder'); expectTy(a.body, alts[0].body.ty, 'caseU branches'); });
        return { k: 'caseU', e, alts, ty: alts[0].body.ty };
    },
    enumLit(ty, idx) {
        check(ty.k === 'enum' && idx < ty.cases.length, 'enumLit');
        return { k: 'enumLit', idx, ty };
    },
    /** `===` (both sides of the same eqable type). */
    seq(a, b) {
        expectTy(b, a.ty, 'seq');
        check((0, ty_1.eqable)(a.ty), `=== on non-eqable type ${(0, ty_1.prettyTy)(a.ty)}`);
        return exports.E.prim(`(.seq ${(0, ty_1.showTy)(a.ty)} rfl)`, [a, b], [a.ty, a.ty], ty_1.T.bool);
    },
    not(a) {
        if (a.k === 'lit' && a.ty.k === 'bool')
            return exports.E.bool(!a.js);
        return exports.E.prim('.not', [a], [ty_1.T.bool], ty_1.T.bool);
    },
    bool(b) { return exports.E.lit(`(.bool ${b})`, ty_1.T.bool, b); },
    undef() { return exports.E.lit('.undef', ty_1.T.undef); },
    nullLit() { return exports.E.lit('.null', ty_1.T.null); },
    /** An expression that panics ("non-null assertion on undefined"); used for branches
     * TypeScript proved unreachable. */
    unreachable(t) { return exports.E.unwrap(exports.E.none(t)); },
    extern(name, args, ret) { return { k: 'extern', name, async: false, args, ty: ret }; },
    externAsync(name, args, t) { return { k: 'extern', name, async: true, args, ty: ty_1.T.promise(t) }; },
    /** Coverage mode: the value of an expression that could not be translated (never
     * emitted; conversions and operations on it are not checked). */
    poison(t) { return { k: 'lit', lean: '<poison>', ty: t, poison: true }; },
};
function isPoison(e) { return e.k === 'lit' && !!e.poison; }
exports.S = {
    // (a one-field record whose value is discarded, e.g. a Node timer handle around setTimeout's
    // number: only its field is evaluated; Lean could not infer the field name of `.mkRec` there)
    expr(e) { return e.k === 'mkRec' && e.args.length === 1 ? exports.S.expr(e.args[0]) : { k: 'expr', e }; },
    assign(v, e) {
        expectTy(e, v.ty, `assign ${v.name}`);
        v.assigned = true;
        return { k: 'assign', v, e };
    },
    gset(g, e) { expectTy(e, g.ty, `gset ${g.name}`); return { k: 'gset', g, e }; },
    setField(o, c, idx, fieldTy, e) {
        expectTy(o, ty_1.T.obj(c), 'setField object');
        expectTy(e, fieldTy, 'setField value');
        return { k: 'setField', o, c, idx, e };
    },
    ite(c, t, f) { expectTy(c, ty_1.T.bool, 'if'); return { k: 'ite', c, t, f }; },
    ret(e) { return { k: 'ret', e }; },
    throw(e) { expectTy(e, ty_1.T.err, 'throw'); return { k: 'throw', e }; },
};
function stmtItem(s) { return { k: 'stmt', s }; }
function declItem(v, init) {
    expectTy(init, v.ty, `decl ${v.name}`);
    return { k: 'decl', v, init };
}
function awaitItem(v, init) {
    expectTy(init, ty_1.T.promise(v.ty), `await ${v.name}`);
    return { k: 'await', v, init };
}
/** Is evaluating `e` free of effects and of reads of mutable state (so it can be moved
 * across other evaluations)? */
function isStable(e) {
    switch (e.k) {
        case 'lit':
        case 'none':
        case 'enumLit':
        case 'funVal': return true;
        case 'var': return !e.v.assigned && !e.v.mayChange;
        case 'some': return isStable(e.e);
        case 'inj': return isStable(e.e);
        case 'fold': return isStable(e.e);
        case 'mkTup':
        case 'mkRec': return e.args.every(isStable);
        case 'getTup':
        case 'getRec':
        case 'unfold': return isStable(e.e);
        case 'lam': return false;
        default: return false;
    }
}
/** Does the block end in a way that never completes normally (syntactically)? */
function blockAlwaysAbrupt(b) {
    for (const it of b) {
        if (it.k === 'stmt' && stmtAlwaysAbrupt(it.s))
            return true;
    }
    return false;
}
function stmtAlwaysAbrupt(s) {
    switch (s.k) {
        case 'brk':
        case 'cont':
        case 'ret':
        case 'retP':
        case 'throw': return true;
        case 'ite': return blockAlwaysAbrupt(s.t) && blockAlwaysAbrupt(s.f);
        case 'block': return blockAlwaysAbrupt(s.b);
        case 'caseOptS': return blockAlwaysAbrupt(s.none) && blockAlwaysAbrupt(s.some);
        case 'caseUS': return s.alts.every(a => blockAlwaysAbrupt(a.body));
        default: return false;
    }
}

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
// Functions, lambdas, classes, lambda lifting, globals and program assembly.
const ts = __importStar(require("typescript"));
const ty_1 = require("./ty");
const ir_1 = require("./ir");
const diag_1 = require("./diag");
const core_1 = require("./core");
const types_1 = require("./types");
const stmts_1 = require("./stmts");
const P = core_1.Translator.prototype;
const SK = ts.SyntaxKind;
function declId(n) {
    return `${n.getSourceFile().fileName}:${n.pos}`;
}
P.isAsync = function (decl) {
    return !!ts.getModifiers(decl)?.some(m => m.kind === SK.AsyncKeyword);
};
P.queueInst = function (inst) {
    this.instances.set(`${inst.role}:${inst.info.name}:${inst.info.idx}`, inst);
    this.queue.push(inst);
};
P.topFunDecl = function (sym) {
    const decls = sym.declarations ?? [];
    const fds = decls.filter(ts.isFunctionDeclaration);
    if (!fds.length) {
        // `const f = (…) => …` at module level is the function f when that is safe (liftedArrow)
        const vd = decls.find(ts.isVariableDeclaration);
        const a = vd && !(0, types_1.isLibDecl)(this.program, vd) ? this.liftedArrow(vd) : undefined;
        if (!a)
            return undefined;
        this.unitNames ??= new Map();
        if (!this.unitNames.has(a))
            this.unitNames.set(a, vd.name.text);
        return a;
    }
    const withBody = fds.filter(d => d.body);
    const d = withBody[0];
    if (!d || !ts.isSourceFile(d.parent) || (0, types_1.isLibDecl)(this.program, d))
        return undefined;
    // overload signatures only type the calls; the implementation (the one declaration with a body)
    // is the function that runs, and calls convert their arguments to its parameter types
    if (withBody.length > 1)
        (0, diag_1.reject)(d, 'unsupported', 'more than one implementation of a function');
    return d;
};
/** `const f = (…) => …` (or a function expression) at module level. */
function liftableArrow(d) {
    if (!ts.isIdentifier(d.name) || !d.initializer || !(d.parent.flags & ts.NodeFlags.Const))
        return undefined;
    const st = d.parent.parent;
    if (!st || !ts.isVariableStatement(st) || !ts.isSourceFile(st.parent))
        return undefined;
    let e = d.initializer;
    while (ts.isParenthesizedExpression(e))
        e = e.expression;
    return ts.isArrowFunction(e) || ts.isFunctionExpression(e) ? e : undefined;
}
// A module-level `const f = (…) => …` is translated as a top-level function (FunRef, callFun)
// instead of a module variable holding a closure. The constant is never reassigned and a
// closure at module level captures only module-level bindings, which a function reads the
// same way; the one difference is the temporal dead zone: the variable cannot be read before
// its declaration has run. So f is lifted only if no code that may run before that point can
// reach it: the module statements before the declaration (and the earlier declarators of the
// same statement), followed through every function, class and lifted arrow they mention
// (conservatively: mentioned, not only called).
P.liftedArrow = function (d) {
    if (!this.liftConstArrows)
        return undefined;
    const a = liftableArrow(d);
    if (!a)
        return undefined;
    const known = this.liftSafe.get(d);
    if (known !== undefined)
        return known ? a : undefined;
    const f = this.symAt(d.name);
    const st = d.parent.parent;
    const sf = st.getSourceFile();
    const work = [...sf.statements.slice(0, sf.statements.indexOf(st))];
    for (const x of st.declarationList.declarations) {
        if (x === d)
            break;
        work.push(x);
    }
    const visited = new Set();
    let safe = !!f;
    const visit = (n) => {
        if (!safe)
            return;
        if (ts.isIdentifier(n)) {
            const s = this.symAt(n);
            if (!s)
                return;
            if (s === f) {
                safe = false;
                return;
            }
            for (const decl of s.declarations ?? []) {
                if ((0, types_1.isLibDecl)(this.program, decl) || decl.getSourceFile().isDeclarationFile)
                    continue;
                // code that runs when the symbol is called or constructed
                const body = ts.isFunctionDeclaration(decl) || ts.isClassDeclaration(decl) || ts.isMethodDeclaration(decl) ? decl
                    : ts.isVariableDeclaration(decl) ? liftableArrow(decl) : undefined;
                if (body && !visited.has(body)) {
                    visited.add(body);
                    work.push(body);
                }
            }
            return;
        }
        ts.forEachChild(n, visit);
    };
    while (safe && work.length)
        visit(work.pop());
    this.liftSafe.set(d, safe);
    return safe ? a : undefined;
};
P.tsParams = function (decl) {
    return decl.parameters.filter(p => !(ts.isIdentifier(p.name) && p.name.text === 'this'));
};
P.paramSpecs = function (decl, subst) {
    if (decl.parameters.some(p => ts.isIdentifier(p.name) && p.name.text === 'this'))
        (0, diag_1.reject)(decl, 'unsupported', '`this` parameters');
    return this.tsParams(decl).map(p => {
        let ty = this.types.map(this.checker.getTypeAtLocation(p), subst, p);
        if (p.dotDotDotToken) {
            if (ty.k !== 'arr')
                (0, diag_1.reject)(p, 'unsupported', 'rest parameter must be an array');
            return { ty, optional: false, rest: true };
        }
        const optional = !!(p.questionToken || p.initializer);
        if (optional && ty.k !== 'opt')
            ty = ty_1.T.opt(ty);
        return { ty, optional, rest: false };
    });
};
P.returnTy = function (decl, subst, async) {
    const sig = this.checker.getSignatureFromDeclaration(decl);
    if (!sig)
        (0, diag_1.reject)(decl, 'unsupported', 'function without signature');
    const rt = this.types.map(sig.getReturnType(), subst, decl);
    if (async) {
        if (rt.k !== 'promise')
            (0, diag_1.reject)(decl, 'unsupported', 'async function must return a Promise');
        return rt.t;
    }
    return rt;
};
P.instantiate = function (decl, call, fc, base) {
    const tps = decl.typeParameters ?? [];
    if (!tps.length)
        return base;
    const sig = this.checker.getResolvedSignature(call);
    const targs = sig && this.checker.getTypeArgumentsForResolvedSignature(sig);
    if (!targs || targs.length < tps.length)
        (0, diag_1.reject)(call, 'unsupported-generic', 'cannot determine the type arguments of this call');
    const s = new Map(base);
    // a call resolved to an overload signature: its type arguments, matched to the implementation's
    // type parameters by name
    const sdecl = sig.declaration;
    if (sdecl && sdecl !== decl && !ts.isJSDocSignature(sdecl)) {
        const names = (sdecl.typeParameters ?? []).map(tp => tp.name.text);
        for (const tp of tps) {
            const i = names.indexOf(tp.name.text);
            if (i < 0)
                (0, diag_1.reject)(call, 'unsupported-generic', `the overload this call resolves to has no type parameter ${tp.name.text} of the implementation`);
            s.set(this.checker.getTypeAtLocation(tp), this.tyOf(targs[i], fc, call));
        }
        return s;
    }
    tps.forEach((tp, i) => s.set(this.checker.getTypeAtLocation(tp), this.tyOf(targs[i], fc, call)));
    return s;
};
function paramName(p, i) {
    return p && ts.isIdentifier(p.name) ? p.name.text : `p${i}`;
}
P.funInfoFor = function (decl, subst, node) {
    const tps = decl.typeParameters ?? [];
    const own = new Map([...subst].filter(([k]) => tps.some(tp => this.checker.getTypeAtLocation(tp) === k)));
    const key = `fun:${declId(decl)}:${(0, types_1.substKey)(own)}`;
    const known = this.instances.get(key);
    if (known)
        return known.info;
    if (decl.asteriskToken)
        (0, diag_1.reject)(decl, 'no-generators', 'generators are not allowed');
    const async = this.isAsync(decl);
    const specs = this.paramSpecs(decl, own);
    const tsp = this.tsParams(decl);
    const params = specs.map((s, i) => (0, ir_1.mkVar)(paramName(tsp[i], i), s.ty));
    const base = this.unitNames?.get(decl) ?? decl.name?.text ?? 'anon';
    const targs = tps.map(tp => own.get(this.checker.getTypeAtLocation(tp)));
    const suffix = tps.length ? `<${targs.map(ty_1.prettyTy).join(', ')}>` : '';
    const leanBase = tps.length ? `${base}_${targs.map(t => this.types.shortName(t)).join('_')}` : base;
    const info = this.newFun(base + suffix, leanBase, params, this.returnTy(decl, own, async), async);
    this.funDocs.set(info, `${base}${suffix}(${tsp.map((p, i) => `${paramName(p, i)}: ${(0, ty_1.prettyTy)(specs[i].ty)}`).join(', ')}): ${(0, ty_1.prettyTy)(info.ret)}`);
    const inst = { decl, subst: own, info, role: 'fun' };
    this.instances.set(key, inst);
    this.queue.push(inst);
    void node;
    return info;
};
// ---------------------------------------------------------------------------------------
// parameters and lambdas
P.bindParams = function (decl, params, fc, out, fixedParams = false) {
    const tsp = this.tsParams(decl);
    tsp.forEach((p, i) => {
        const v = params[i];
        if (fixedParams && v && ts.isIdentifier(p.name)) {
            // callback parameters typed by the library (Promise executors, rejection handlers)
            const sym = this.symAt(p.name);
            if (this.isReassigned(sym))
                (0, diag_1.reject)(p, 'unsupported', `reassigned parameter ${p.name.text}`);
            if (v.ty.k === 'fn' && this.types.boxedFns.has((0, ty_1.tyKey)((0, ty_1.stripIdBoxes)(v.ty)))) {
                // (a resolve function of a type compared by identity, e.g. kept in a Set: one cell)
                const bt = ty_1.T.box(v.ty);
                this.declareLocal(sym, p.name.text, bt, ir_1.E.builtin(`(.boxNew ${(0, ty_1.showTy)(v.ty)})`, [ir_1.E.var(v)], [v.ty], bt), fc, out);
                return;
            }
            fc.bind(sym, { k: 'var', v, fixed: true, errVar: v.ty.k === 'err' });
            return;
        }
        if (p.dotDotDotToken) {
            if (!v)
                (0, diag_1.reject)(p, 'unsupported', 'rest parameter in a callback');
            if (!ts.isIdentifier(p.name))
                (0, diag_1.reject)(p, 'unsupported-syntax', 'destructured rest parameter');
            const sym = this.symAt(p.name);
            if (this.needsBox(sym) || this.isReassigned(sym))
                this.declareLocal(sym, p.name.text, v.ty, ir_1.E.var(v), fc, out);
            else
                fc.bind(sym, { k: 'var', v });
            return;
        }
        if (ts.isIdentifier(p.name)) {
            const sym = this.symAt(p.name);
            const inner = this.tyOf(this.checker.getTypeOfSymbol(sym), fc, p);
            let value;
            if (!v) {
                if (p.initializer) {
                    const [d, pre] = this.isolate(fc, () => this.lowerExpr(p.initializer, fc, inner));
                    out.push(...pre);
                    value = d;
                }
                else if (inner.k === 'opt')
                    value = ir_1.E.none(inner.t);
                else if (inner.k === 'undef')
                    value = ir_1.E.undef();
                else
                    (0, diag_1.reject)(p, 'unsupported', `parameter ${p.name.text} receives no argument here`);
            }
            else if (p.initializer && v.ty.k === 'opt') {
                const y = (0, ir_1.mkVar)(p.name.text, v.ty.t);
                const [d, pre] = this.isolate(fc, () => this.lowerExpr(p.initializer, fc, inner));
                if (pre.length)
                    (0, diag_1.reject)(p.initializer, 'unsupported', 'default parameter value with await/assignments');
                value = ir_1.E.caseOpt(ir_1.E.var(v), d, y, this.coerce(ir_1.E.var(y), inner, p));
            }
            else if (inner.k === 'box' && inner.t.k === 'fn' && v.ty.k === 'fn' && (0, ty_1.tyEq)(inner.t, v.ty)) {
                // a plain function received where functions are compared by identity: one cell
                value = ir_1.E.builtin(`(.boxNew ${(0, ty_1.showTy)(v.ty)})`, [ir_1.E.var(v)], [v.ty], inner);
            }
            else
                value = this.adapt(ir_1.E.var(v), inner, p);
            if (v && value.k === 'var' && value.v === v && !this.needsBox(sym)) {
                v.mayChange = this.isReassigned(sym);
                fc.bind(sym, { k: 'var', v });
            }
            else
                this.declareLocal(sym, p.name.text, inner, value, fc, out);
            return;
        }
        if (!v)
            (0, diag_1.reject)(p, 'unsupported', 'destructured parameter without argument');
        if (p.initializer) {
            // `{ a = 1 }: T = {}`: the default where the argument is undefined, then the pattern
            if (v.ty.k !== 'opt')
                (0, diag_1.reject)(p, 'unsupported-syntax', 'default value for a destructured parameter that cannot be undefined');
            const t = v.ty.t;
            const [d, pre] = this.isolate(fc, () => this.lowerExpr(p.initializer, fc, t));
            if (pre.length)
                (0, diag_1.reject)(p.initializer, 'unsupported', 'default parameter value with await/assignments');
            const y = (0, ir_1.mkVar)('p', t), pv = (0, ir_1.mkVar)('p', t);
            out.push((0, ir_1.declItem)(pv, ir_1.E.caseOpt(ir_1.E.var(v), d, y, ir_1.E.var(y))));
            this.bindPattern(p.name, ir_1.E.var(pv), fc, out, true);
            return;
        }
        this.bindPattern(p.name, ir_1.E.var(v), fc, out, true);
    });
};
P.lowerConciseBody = function (body, fc, out) {
    const saved = fc.pre;
    fc.pre = out;
    try {
        if (fc.retPoison) {
            this.lowerExpr(body, fc);
            return;
        }
        const nat = this.tyAt(body, fc);
        if (fc.async && nat.k === 'promise') {
            out.push((0, ir_1.stmtItem)({ k: 'retP', e: this.lowerExpr(body, fc, ty_1.T.promise(fc.bodyRet)) }));
            return;
        }
        if (fc.bodyRet.k === 'undef') {
            // `() => f(x)` used as a void function: evaluate for effect, return undefined
            this.lowerExprStmt(body, fc, out);
            return;
        }
        if (fc.bodyRet.k === 'bool' && this.tyAt(body, fc).k !== 'bool') {
            // `xs.filter(x => x.parent)`: JavaScript tests truthiness (a pure null test for
            // optional objects; otherwise the truthiness rule)
            out.push((0, ir_1.stmtItem)(ir_1.S.ret(this.truthy(this.lowerExpr(body, fc), body))));
            return;
        }
        out.push((0, ir_1.stmtItem)(ir_1.S.ret(this.lowerExpr(body, fc, fc.bodyRet))));
    }
    finally {
        fc.pre = saved;
    }
};
P.lowerLambda = function (n, fc, exp, fixedParams = false) {
    if (n.asteriskToken)
        (0, diag_1.reject)(n, 'no-generators', 'generators are not allowed');
    // a function compared by identity (identity.ts): a new cell holding the closure, each time
    const boxedTarget = exp && exp.k === 'box' && exp.t.k === 'fn' ? exp.t : undefined;
    const ownBoxed = !boxedTarget && (!exp || exp.k !== 'fn') && (() => { const own = this.tyAt(n, fc); return own.k === 'box' && own.t.k === 'fn'; })();
    if (boxedTarget || ownBoxed) {
        const ft = boxedTarget ?? this.tyAt(n, fc).t;
        const lam = this.lowerLambda(n, fc, ft, fixedParams);
        const cell = ir_1.E.builtin(`(.boxNew ${(0, ty_1.showTy)(lam.ty)})`, [lam], [lam.ty], ty_1.T.box(lam.ty));
        return exp && !boxedTarget ? this.coerce(cell, exp, n) : cell;
    }
    let fnTy = exp && exp.k === 'fn' ? exp : this.tyAt(n, fc);
    if (fnTy.k !== 'fn')
        (0, diag_1.reject)(n, 'unsupported', `function used as ${(0, ty_1.prettyTy)(fnTy)}`);
    const async = this.isAsync(n);
    if (async && fnTy.ret.k === 'undef' && exp) {
        // an async callback where a void function is expected: its promise is dropped
        const nat = this.tyAt(n, fc);
        if (nat.k === 'fn' && nat.ret.k === 'promise') {
            const inner = this.lowerLambda(n, fc, ty_1.T.fn(fnTy.args, nat.ret), fixedParams);
            return this.coerce(inner, exp, n);
        }
    }
    let bodyRet = fnTy.ret;
    if (async) {
        if (bodyRet.k !== 'promise')
            (0, diag_1.reject)(n, 'unsupported', 'async function used as a function that does not return a Promise');
        bodyRet = bodyRet.t;
    }
    if (ts.isFunctionExpression(n) && n.name) {
        const self = this.symAt(n.name);
        const f = self && this.facts(self);
        if (self && this.analysis.vars.get(self) === undefined) {
            // named function expression: references to its own name are not supported
            void f;
        }
    }
    const child = new core_1.FnCtx(fc, 'lambda', async, bodyRet, fc.subst, n);
    const tsp = this.tsParams(n);
    const params = fnTy.args.map((t, i) => (0, ir_1.mkVar)(paramName(tsp[i], i), t));
    const items = [];
    child.pre = items;
    this.bindParams(n, params, child, items, fixedParams);
    if (ts.isBlock(n.body))
        items.push(...this.lowerBlockStmts(n.body.statements, child));
    else
        this.lowerConciseBody(n.body, child, items);
    const lam = ir_1.E.lam(async, params, bodyRet, items);
    return exp && exp.k !== 'fn' ? this.coerce(lam, exp, n) : lam;
};
// ---------------------------------------------------------------------------------------
// function bodies
P.lowerFunBody = function (inst) {
    const { decl, subst, info } = inst;
    const fc = new core_1.FnCtx(null, 'fun', info.async, info.bodyRet, subst, decl);
    const items = [];
    fc.pre = items;
    let params = info.params;
    if (inst.role === 'method' || inst.role === 'getter' || inst.role === 'setter') {
        fc.thisVar = info.params[0];
        params = info.params.slice(1);
    }
    if (inst.role === 'lifted' && inst.lifted) {
        const { caps, capBindings } = inst.lifted;
        caps.forEach((sym, i) => fc.bind(sym, capBindings[i]));
        for (const [sym, b] of inst.liftedScope ?? [])
            fc.bind(sym, b);
        params = info.params.slice(caps.length);
    }
    if (inst.role === 'ctor') {
        lowerCtorBody(this, inst, fc, items);
        info.body = items;
        return;
    }
    this.bindParams(decl, params, fc, items);
    const body = decl.body;
    if (!body)
        (0, diag_1.reject)(decl, 'unsupported', 'function without body');
    if (ts.isBlock(body))
        items.push(...this.lowerBlockStmts(body.statements, fc));
    else
        this.lowerConciseBody(body, fc, items);
    info.body = items;
};
function lowerCtorBody(tr, inst, fc, items) {
    const ci = inst.cls;
    const info = inst.info;
    fc.isCtor = true;
    const thisV = (0, ir_1.mkVar)('this', ty_1.T.obj(ci.name));
    items.push((0, ir_1.declItem)(thisV, ir_1.E.newObj(ci.name)));
    fc.thisVar = thisV;
    // field initialisers (declaration order), before the parameters are bound (ECMA-262
    // [[Construct]]: InitializeInstanceElements precedes FunctionDeclarationInstantiation)
    for (const m of ci.decl.members) {
        if (!ts.isPropertyDeclaration(m) || ts.getModifiers(m)?.some(x => x.kind === SK.StaticKeyword))
            continue;
        const name = m.name.text;
        const idx = ci.fieldIdx.get(name);
        const fty = ci.fields[idx].ty;
        if (m.initializer) {
            const saved = fc.pre;
            fc.pre = items;
            try {
                items.push((0, ir_1.stmtItem)(ir_1.S.setField(ir_1.E.var(thisV), ci.name, idx, fty, tr.lowerExpr(m.initializer, fc, fty))));
            }
            finally {
                fc.pre = saved;
            }
        }
        else if (fty.k === 'opt')
            items.push((0, ir_1.stmtItem)(ir_1.S.setField(ir_1.E.var(thisV), ci.name, idx, fty, ir_1.E.none(fty.t))));
        else if (fty.k === 'undef')
            items.push((0, ir_1.stmtItem)(ir_1.S.setField(ir_1.E.var(thisV), ci.name, idx, fty, ir_1.E.undef())));
    }
    const ctor = ci.decl.members.find(ts.isConstructorDeclaration);
    if (ctor) {
        tr.bindParams(ctor, info.params, fc, items);
        for (const p of ctor.parameters) {
            if (!ts.getModifiers(p)?.some(m => [SK.PublicKeyword, SK.PrivateKeyword, SK.ProtectedKeyword, SK.ReadonlyKeyword].includes(m.kind)))
                continue;
            const name = p.name.text;
            const idx = ci.fieldIdx.get(name);
            const sym = tr.symAt(p.name);
            const b = tr.lookup(sym, fc);
            const v = tr.coerce(tr.readBinding(b, p), ci.fields[idx].ty, p);
            items.push((0, ir_1.stmtItem)(ir_1.S.setField(ir_1.E.var(thisV), ci.name, idx, ci.fields[idx].ty, v)));
        }
        if (ctor.body)
            items.push(...tr.lowerBlockStmts(ctor.body.statements, fc));
    }
    items.push((0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.var(thisV))));
}
// ---------------------------------------------------------------------------------------
// classes
function memberName(m) {
    if (!m.name)
        return undefined;
    if (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name) || ts.isStringLiteral(m.name))
        return m.name.text;
    return undefined;
}
function isStatic(m) {
    return !!ts.getModifiers(m)?.some(x => x.kind === SK.StaticKeyword);
}
P.classCtor = function (ci, node) {
    const key = `ctor:${ci.name}`;
    const known = this.instances.get(key);
    if (known)
        return known.info;
    const ctor = ci.decl.members.find(ts.isConstructorDeclaration);
    const specs = ctor ? this.paramSpecs(ctor, ci.subst) : [];
    const tsp = ctor ? this.tsParams(ctor) : [];
    const params = specs.map((s, i) => (0, ir_1.mkVar)(paramName(tsp[i], i), s.ty));
    const info = this.newFun(`${ci.name}.constructor`, `${ci.name}_new`, params, ty_1.T.obj(ci.name), false);
    this.funDocs.set(info, `new ${ci.name}(${tsp.map((p, i) => `${paramName(p, i)}: ${(0, ty_1.prettyTy)(specs[i].ty)}`).join(', ')})`);
    const inst = { decl: ctor ?? ci.decl, subst: ci.subst, info, cls: ci, role: 'ctor' };
    this.instances.set(key, inst);
    this.queue.push(inst);
    void node;
    return info;
};
P.classMember = function (ci, name, kind, node) {
    const key = `${kind}:${ci.name}:${name}`;
    const known = this.instances.get(key);
    if (known)
        return known.info;
    const m = ci.decl.members.find(x => !isStatic(x) && memberName(x) === name &&
        (kind === 'method' ? ts.isMethodDeclaration(x) : kind === 'getter' ? ts.isGetAccessorDeclaration(x) : ts.isSetAccessorDeclaration(x)));
    if (!m)
        return null;
    if (m.typeParameters?.length)
        (0, diag_1.reject)(m, 'unsupported-generic', 'generic methods are not supported');
    if (m.asteriskToken)
        (0, diag_1.reject)(m, 'no-generators', 'generators are not allowed');
    const async = this.isAsync(m);
    const specs = this.paramSpecs(m, ci.subst);
    const tsp = this.tsParams(m);
    const thisV = (0, ir_1.mkVar)('this', ty_1.T.obj(ci.name));
    const params = [thisV, ...specs.map((s, i) => (0, ir_1.mkVar)(paramName(tsp[i], i), s.ty))];
    const ret = kind === 'setter' ? ty_1.T.undef : this.returnTy(m, ci.subst, async);
    const lean = kind === 'method' ? `${ci.name}_${name}` : `${ci.name}_${kind === 'getter' ? 'get' : 'set'}_${name}`;
    const info = this.newFun(`${ci.name}.${kind === 'method' ? '' : kind === 'getter' ? 'get ' : 'set '}${name}`, lean, params, ret, async);
    this.funDocs.set(info, `${ci.name}.${name}(this${tsp.map((p, i) => `, ${paramName(p, i)}: ${(0, ty_1.prettyTy)(specs[i].ty)}`).join('')}): ${(0, ty_1.prettyTy)(info.ret)}`);
    const inst = { decl: m, subst: ci.subst, info, cls: ci, role: kind };
    this.instances.set(key, inst);
    this.queue.push(inst);
    void node;
    return info;
};
P.classStatic = function (ci, name, node) {
    const key = `static:${ci.name}:${name}`;
    const known = this.instances.get(key);
    if (known)
        return known.info;
    const m = ci.decl.members.find(x => isStatic(x) && memberName(x) === name && ts.isMethodDeclaration(x));
    if (!m)
        return null;
    if (m.typeParameters?.length)
        (0, diag_1.reject)(m, 'unsupported-generic', 'generic methods are not supported');
    const async = this.isAsync(m);
    const specs = this.paramSpecs(m, ci.subst);
    const tsp = this.tsParams(m);
    const params = specs.map((s, i) => (0, ir_1.mkVar)(paramName(tsp[i], i), s.ty));
    const info = this.newFun(`${ci.name}.${name}`, `${ci.name}_static_${name}`, params, this.returnTy(m, ci.subst, async), async);
    const inst = { decl: m, subst: ci.subst, info, cls: ci, role: 'static' };
    this.instances.set(key, inst);
    this.queue.push(inst);
    void node;
    return info;
};
P.structCtor = function (ms, _node) {
    const key = `struct:${ms.name}`;
    const known = this.instances.get(key);
    if (known)
        return known.info;
    const params = ms.fields.map(f => (0, ir_1.mkVar)(f.name, f.ty));
    const info = this.newFun(`${ms.name}.literal`, `${ms.name}_lit`, params, ty_1.T.obj(ms.name), false);
    this.funDocs.set(info, `{ ${ms.fields.map(f => `${f.name}: ${(0, ty_1.prettyTy)(f.ty)}`).join(', ')} } (object literal of ${ms.name})`);
    const o = (0, ir_1.mkVar)('o', ty_1.T.obj(ms.name));
    info.body = [
        (0, ir_1.declItem)(o, ir_1.E.newObj(ms.name)),
        ...ms.fields.map((f, i) => (0, ir_1.stmtItem)(ir_1.S.setField(ir_1.E.var(o), ms.name, i, f.ty, ir_1.E.var(params[i])))),
        (0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.var(o))),
    ];
    this.instances.set(key, { decl: undefined, subst: new Map(), info, role: 'structCtor', struct: ms });
    return info;
};
P.staticFieldGlobal = function (pa) {
    const base = (0, stmts_1.skipParens)(pa.expression);
    if (!ts.isIdentifier(base))
        return null;
    const sym = this.symAt(base);
    if (!sym || !(sym.flags & ts.SymbolFlags.Class) || (0, types_1.isLibDecl)(this.program, sym.declarations?.[0]))
        return null;
    const decl = sym.declarations.find(ts.isClassDeclaration);
    const prop = decl.members.find(m => isStatic(m) && ts.isPropertyDeclaration(m) && memberName(m) === pa.name.text);
    if (!prop)
        return null;
    const psym = this.checker.getSymbolAtLocation(prop.name);
    const known = this.staticFields.get(psym);
    if (known)
        return known;
    if (decl.typeParameters?.length)
        (0, diag_1.reject)(pa, 'unsupported-generic', 'static fields of generic classes');
    const ty = this.types.map(this.checker.getTypeAtLocation(prop), new Map(), prop);
    const g = this.newGlobal(`${decl.name?.text}.${pa.name.text}`, ty);
    this.staticFields.set(psym, g);
    return g;
};
P.lowerClassDeclStmt = function (cd, fc, out) {
    if (fc.kind !== 'main' || !ts.isSourceFile(cd.parent))
        (0, diag_1.reject)(cd, 'unsupported', 'classes must be declared at module level');
    for (const m of cd.members) {
        if (ts.isClassStaticBlockDeclaration(m))
            (0, diag_1.reject)(m, 'unsupported-syntax', 'static blocks');
        if (ts.isPropertyDeclaration(m) && isStatic(m)) {
            const psym = this.checker.getSymbolAtLocation(m.name);
            let g = this.staticFields.get(psym);
            if (!g) {
                const ty = this.types.map(this.checker.getTypeAtLocation(m), new Map(), m);
                g = this.newGlobal(`${cd.name?.text}.${memberName(m)}`, ty);
                this.staticFields.set(psym, g);
            }
            if (m.initializer) {
                const saved = fc.pre;
                fc.pre = out;
                try {
                    out.push((0, ir_1.stmtItem)(ir_1.S.gset(g, this.lowerExpr(m.initializer, fc, g.ty))));
                }
                finally {
                    fc.pre = saved;
                }
            }
            else if (g.ty.k === 'opt')
                out.push((0, ir_1.stmtItem)(ir_1.S.gset(g, ir_1.E.none(g.ty.t))));
            else if (g.ty.k === 'undef')
                out.push((0, ir_1.stmtItem)(ir_1.S.gset(g, ir_1.E.undef())));
        }
    }
};
function freeOf(tr, fn, selfSym) {
    const syms = [];
    const lifted = [];
    const visit = (n, inArrowOfFn) => {
        if (n.kind === SK.ThisKeyword && inArrowOfFn)
            (0, diag_1.reject)(n, 'no-this', '`this` in a nested function');
        if (ts.isIdentifier(n)) {
            const sym = tr.symAt(n);
            if (sym && sym !== selfSym) {
                const f = tr.facts(sym);
                if (f && !(0, core_1.within)(f.decl, fn) && !tr.globalOf.has(sym)) {
                    if (!syms.includes(sym))
                        syms.push(sym);
                }
                else if (!f) {
                    const d = sym.declarations?.[0];
                    if (d && ((ts.isFunctionDeclaration(d) && !ts.isSourceFile(d.parent)) || (ts.isVariableDeclaration(d) && d.initializer && ts.isArrowFunction(d.initializer))) && !(0, core_1.within)(d, fn)) {
                        if (!lifted.includes(sym))
                            lifted.push(sym);
                    }
                }
            }
        }
        const isFnBoundary = ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) || ts.isClassLike(n);
        ts.forEachChild(n, c => visit(c, isFnBoundary && n !== fn ? false : inArrowOfFn));
    };
    visit(fn, true);
    return { syms, lifted };
}
P.liftFunctions = function (list, fc) {
    // captures: free variables plus the captures of lifted functions they call (fixpoint)
    const infos = list.map(x => ({ ...x, free: freeOf(this, x.decl, x.sym) }));
    const caps = new Map();
    for (const x of infos)
        caps.set(x.sym, [...x.free.syms]);
    const capsOfOuter = (s) => {
        const b = this.lookup(s, fc);
        return b && b.k === 'lifted' ? b.caps : undefined;
    };
    let changed = true;
    while (changed) {
        changed = false;
        for (const x of infos) {
            const mine = caps.get(x.sym);
            for (const g of x.free.lifted) {
                const theirs = caps.get(g) ?? capsOfOuter(g) ?? [];
                for (const s of theirs)
                    if (!mine.includes(s)) {
                        mine.push(s);
                        changed = true;
                    }
            }
        }
    }
    const created = [];
    for (const x of infos) {
        const cs = caps.get(x.sym);
        const optInit = (s) => {
            const d = s.valueDeclaration;
            return !!d && ts.isVariableDeclaration(d) && !d.initializer && !(d.parent && ts.isVariableDeclarationList(d.parent) && d.parent.parent && ts.isForOfStatement(d.parent.parent));
        };
        const capTys = cs.map(s => {
            const declTy = this.tyOf(this.checker.getTypeOfSymbol(s), fc, x.decl);
            if (this.needsBox(s) && optInit(s) && declTy.k !== 'opt' && declTy.k !== 'undef')
                return ty_1.T.box(ty_1.T.opt(declTy));
            return this.needsBox(s) ? ty_1.T.box(declTy) : declTy;
        });
        const capVars = cs.map((s, i) => (0, ir_1.mkVar)(s.name, capTys[i]));
        const async = this.isAsync(x.decl);
        const specs = this.paramSpecs(x.decl, fc.subst);
        const tsp = this.tsParams(x.decl);
        const params = specs.map((s, i) => (0, ir_1.mkVar)(paramName(tsp[i], i), s.ty));
        const info = this.newFun(x.name, x.name, [...capVars, ...params], this.returnTy(x.decl, fc.subst, async), async);
        this.funDocs.set(info, `${x.name}(${[...cs.map((s, i) => `${s.name}: ${(0, ty_1.prettyTy)(capTys[i])} (captured)`), ...tsp.map((p, i) => `${paramName(p, i)}: ${(0, ty_1.prettyTy)(specs[i].ty)}`)].join(', ')}): ${(0, ty_1.prettyTy)(info.ret)}`);
        const capBindings = cs.map((s, i) => {
            if (!this.needsBox(s))
                return { k: 'var', v: capVars[i] };
            const inner = capTys[i].t;
            const declTy = this.tyOf(this.checker.getTypeOfSymbol(s), fc, x.decl);
            if (inner.k === 'opt' && declTy.k !== 'opt')
                return { k: 'boxOpt', v: capVars[i], t: declTy };
            return { k: 'box', v: capVars[i], t: inner };
        });
        const b = { k: 'lifted', f: info, caps: cs };
        const inst = { decl: x.decl, subst: fc.subst, info, role: 'lifted', lifted: { caps: cs, capBindings } };
        created.push({ x, b, inst });
        fc.bind(x.sym, b);
    }
    // inside each lifted body, the lifted functions it can see are bound too
    for (const c of created) {
        const scope = new Map();
        for (const d of created)
            scope.set(d.x.sym, d.b);
        for (const g of c.x.free.lifted) {
            const ob = this.lookup(g, fc);
            if (ob && ob.k === 'lifted' && !scope.has(g))
                scope.set(g, ob);
        }
        c.inst.liftedScope = scope;
        this.instances.set(`lifted:${declId(c.x.decl)}`, c.inst);
        this.queue.push(c.inst);
    }
};
P.hoistFunctions = function (stmts, fc) {
    if (!stmts.length || ts.isSourceFile(stmts[0].parent))
        return;
    const fds = stmts.filter(ts.isFunctionDeclaration).filter(d => d.body);
    if (!fds.length)
        return;
    this.liftFunctions(fds.map(d => {
        if (!d.name)
            (0, diag_1.reject)(d, 'unsupported-syntax', 'anonymous function declaration');
        return { decl: d, sym: this.symAt(d.name), name: d.name.text };
    }), fc);
};
P.liftedConstArrow = function (d, sym, fc) {
    const init = d.initializer && (0, stmts_1.skipParens)(d.initializer);
    if (!init || !(ts.isArrowFunction(init) || ts.isFunctionExpression(init)))
        return false;
    const f = this.facts(sym);
    if (!f || this.isReassigned(sym))
        return false;
    const selfRef = f.refs.some(r => (0, core_1.within)(r, init));
    if (!selfRef)
        return false;
    if (fc.kind === 'main' && this.globalOf.has(sym))
        return false;
    this.liftFunctions([{ decl: init, sym, name: d.name.text }], fc);
    return true;
};
P.liftedCapArgs = function (b, fc, node) {
    return b.caps.map((s, i) => {
        const cb = this.lookup(s, fc);
        if (!cb)
            (0, diag_1.reject)(node, 'unsupported', `${b.f.name} is called before ${s.name} (which it uses) is declared`);
        const pt = b.f.params[i].ty;
        if (cb.k === 'box' || cb.k === 'boxOpt')
            return ir_1.E.var(cb.v);
        if (cb.k === 'lifted')
            (0, diag_1.reject)(node, 'unsupported', 'captured function');
        return this.coerce(this.readBinding(cb, node), pt, node);
    });
};
P.liftedAsValue = function (b, node, fc, target) {
    const caps = this.liftedCapArgs(b, fc, node);
    const userParams = b.f.params.slice(b.caps.length).map(p => (0, ir_1.mkVar)(p.name, p.ty));
    const capVals = caps.map(c => {
        if (c.k === 'var' || c.k === 'lit')
            return c;
        const v = this.bindTemp(c, fc, 'cap');
        return ir_1.E.var(v);
    });
    const call = ir_1.E.call(b.f, [...capVals, ...userParams.map(p => ir_1.E.var(p))]);
    const lam = ir_1.E.lam(false, userParams, b.f.ret, [(0, ir_1.stmtItem)(ir_1.S.ret(call))]);
    return this.adapt(lam, target ?? this.tyAt(node, fc), node);
};
// ---------------------------------------------------------------------------------------
// globals
P.isGlobalDecl = function (d) {
    const list = d.parent;
    return ts.isVariableDeclarationList(list) && ts.isVariableStatement(list.parent) && ts.isSourceFile(list.parent.parent);
};
P.lowerGlobalDecl = function (d, fc, out) {
    if (ts.isIdentifier(d.name)) {
        const sym = this.symAt(d.name);
        const g = this.globalOf.get(sym);
        if (!g)
            (0, diag_1.reject)(d, 'unsupported', `module-level variable ${d.name.text} has an unsupported type`);
        if (!d.initializer) {
            if (g.ty.k === 'opt')
                out.push((0, ir_1.stmtItem)(ir_1.S.gset(g, ir_1.E.none(g.ty.t))));
            else if (g.ty.k === 'undef')
                out.push((0, ir_1.stmtItem)(ir_1.S.gset(g, ir_1.E.undef())));
            return;
        }
        out.push((0, ir_1.stmtItem)(ir_1.S.gset(g, this.lowerExpr(d.initializer, fc, g.ty))));
        return;
    }
    if (!d.initializer)
        (0, diag_1.reject)(d, 'unsupported-syntax', 'destructuring without initialiser');
    const init = this.lowerExpr(d.initializer, fc);
    const v = this.bindTemp(init, fc, 'd');
    this.bindPattern(d.name, ir_1.E.var(v), fc, out, true);
};
// ---------------------------------------------------------------------------------------
// program
function importOrder(tr, roots) {
    const order = [];
    const seen = new Set();
    const user = new Set(roots);
    const visit = (sf) => {
        if (seen.has(sf))
            return;
        seen.add(sf);
        for (const st of sf.statements) {
            const spec = (ts.isImportDeclaration(st) || ts.isExportDeclaration(st)) ? st.moduleSpecifier : undefined;
            if (!spec || !ts.isStringLiteral(spec))
                continue;
            const res = ts.resolveModuleName(spec.text, sf.fileName, tr.program.getCompilerOptions(), ts.sys);
            const target = res.resolvedModule && tr.program.getSourceFile(res.resolvedModule.resolvedFileName);
            if (target && user.has(target))
                visit(target);
        }
        order.push(sf);
    };
    for (const r of roots)
        visit(r);
    return order;
}
function collectNames(n, out) {
    if (ts.isIdentifier(n)) {
        out.push(n);
        return;
    }
    for (const el of n.elements)
        if (!ts.isOmittedExpression(el))
            collectNames(el.name, out);
}
P.guard = function (node, f) {
    try {
        f();
    }
    catch (e) {
        if (e instanceof diag_1.Reject)
            this.diags.at(e.node ?? node, e.rule, e.message);
        else if (e instanceof ir_1.InternalError)
            this.diags.at(node, 'internal', e.message);
        else if (e instanceof Error && !(e instanceof RangeError && /call stack/.test(e.message))) {
            this.diags.at(node, 'internal', `translator error: ${e.message} (${(e.stack ?? '').split('\n')[1]?.trim() ?? ''})`);
        }
        else
            throw e;
    }
};
P.translateProgram = function () {
    const files = importOrder(this, this.files);
    this.analysis.run(files);
    this.analyzeIdentity(files);
    // module-level variables
    for (const sf of files) {
        for (const st of sf.statements) {
            if (!ts.isVariableStatement(st))
                continue;
            for (const d of st.declarationList.declarations) {
                if (this.isRegexConst(d) || this.liftedArrow(d))
                    continue;
                const ids = [];
                collectNames(d.name, ids);
                for (const id of ids)
                    this.guard(id, () => {
                        const sym = this.symAt(id);
                        const ty = this.types.map(this.checker.getTypeOfSymbol(sym), new Map(), id);
                        this.globalOf.set(sym, this.newGlobal(id.text, ty));
                    });
            }
        }
    }
    // top-level functions and classes
    for (const sf of files) {
        for (const st of sf.statements) {
            if (ts.isFunctionDeclaration(st) && st.body && !st.typeParameters?.length) {
                this.guard(st, () => { this.topFunDecl(this.symAt(st.name)); this.funInfoFor(st, new Map(), st); });
            }
            // a lifted `const f = (…) => …` is a top-level function like a declaration: translated even
            // when nothing calls it (before, only a use translated it, so an uncalled one was missing)
            if (ts.isVariableStatement(st)) {
                for (const d of st.declarationList.declarations) {
                    const a = this.liftedArrow(d);
                    if (!a || a.typeParameters?.length || (0, types_1.isLibDecl)(this.program, d))
                        continue;
                    this.guard(d, () => { const fd = this.topFunDecl(this.symAt(d.name)); if (fd)
                        this.funInfoFor(fd, new Map(), d); });
                }
            }
            if (ts.isClassDeclaration(st) && !st.typeParameters?.length) {
                this.guard(st, () => {
                    if (st.heritageClauses?.some(h => h.token === SK.ExtendsKeyword))
                        (0, diag_1.reject)(st, 'no-extends', 'classes cannot extend other classes');
                    const t = this.checker.getTypeAtLocation(st);
                    const ci = this.types.classInst(t, new Map(), st);
                    this.classCtor(ci, st);
                    for (const m of st.members) {
                        const name = memberName(m);
                        if (!name)
                            continue;
                        if (ts.isMethodDeclaration(m)) {
                            if (isStatic(m))
                                this.classStatic(ci, name, m);
                            else
                                this.classMember(ci, name, 'method', m);
                        }
                        else if (ts.isGetAccessorDeclaration(m) && !isStatic(m))
                            this.classMember(ci, name, 'getter', m);
                        else if (ts.isSetAccessorDeclaration(m) && !isStatic(m))
                            this.classMember(ci, name, 'setter', m);
                    }
                });
            }
        }
    }
    // module bodies
    const main = new core_1.FnCtx(null, 'main', false, ty_1.T.undef, new Map(), files[0]);
    const mainItems = [];
    for (const sf of files) {
        for (const st of sf.statements) {
            this.guard(st, () => {
                const items = [];
                this.lowerStmt(st, main, items);
                mainItems.push(...items);
            });
        }
    }
    // function bodies (instantiations may enqueue more)
    for (let i = 0; i < this.queue.length; i++) {
        const inst = this.queue[i];
        this.guard(inst.decl, () => this.lowerFunBody(inst));
        if (!inst.info.body)
            inst.info.body = [];
    }
    if (this.diags.count)
        return null;
    const pir = {
        namespace: '', sources: files.map(f => f.fileName), aliases: this.types.aliases, classes: this.types.classFields,
        funs: this.funs, globals: this.globals, main: [...this.fnBoxInits, ...mainItems], funDocs: this.funDocs,
    };
    return pir;
};
void ty_1.tyEq;
void ty_1.showTy;

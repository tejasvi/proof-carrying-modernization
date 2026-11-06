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
exports.isFatal = isFatal;
exports.holdsUnknown = holdsUnknown;
exports.defensiveContext = defensiveContext;
exports.numberPred = numberPred;
// Expression lowering.
const ts = __importStar(require("typescript"));
const ty_1 = require("./ty");
const ir_1 = require("./ir");
const diag_1 = require("./diag");
const core_1 = require("./core");
const stmts_1 = require("./stmts");
const P = core_1.Translator.prototype;
const SK = ts.SyntaxKind;
P.lowerExpr = function (n, fc, exp) {
    if (exp && exp.k === 'dyn' && !(this.checker.getTypeAtLocation(n).flags & ts.TypeFlags.Any)) {
        // a value used as unknown: lowered at its own type, then kept with that type (an `any`
        // value, e.g. from `JSON.parse`, takes the expected type instead)
        const e = this.lowerExpr(n, fc);
        return (0, ir_1.isPoison)(e) ? ir_1.E.poison(ty_1.T.dyn) : this.adapt(e, ty_1.T.dyn, n);
    }
    if (!this.coverage)
        return lowerExpr0(this, n, fc, exp);
    // coverage mode: record the violation and continue with a placeholder value (a violation
    // inside an expression whose sub-expression already failed is a consequence, not recorded)
    const mark = this.poisonCount;
    try {
        return lowerExpr0(this, n, fc, exp);
    }
    catch (e) {
        if (isFatal(e))
            throw e;
        if (this.poisonCount === mark)
            this.covRecord(e, n);
        return this.poisonFor(n, fc, exp);
    }
};
function isFatal(e) {
    return !(e instanceof Error) || (e instanceof RangeError && /call stack/.test(e.message));
}
P.derivedPoison = function (n, fc, exp) {
    if (exp)
        return ir_1.E.poison(exp);
    try {
        return ir_1.E.poison(this.tyAt(n, fc));
    }
    catch {
        return ir_1.E.poison(ty_1.T.undef);
    }
};
function lowerExpr0(tr, n, fc, exp) {
    return lowerExprImpl.call(tr, n, fc, exp);
}
const lowerExprImpl = function (n, fc, exp) {
    const ov = fc.override.get(n);
    if (ov)
        return exp ? this.coerce(ov, exp, n) : ov;
    const e = this.lowerRaw(n, fc, exp);
    if (!exp || (0, ty_1.tyEq)(e.ty, exp))
        return e;
    const tsT = this.checker.getTypeAtLocation(n);
    if (this.isNeverType(tsT))
        return this.withValue(e, 'nv', () => ir_1.E.unreachable(exp));
    // a string expression TypeScript types as one literal (e.g. a field of an `as const`
    // object) flowing into a literal union
    const target = exp.k === 'opt' ? exp.t : exp;
    if (target.k === 'enum' && this.unfoldTy(e.ty).k === 'str' && (tsT.flags & ts.TypeFlags.StringLiteral) &&
        target.cases.includes(tsT.value)) {
        const lit = ir_1.E.enumLit(target, target.cases.indexOf(tsT.value));
        return this.coerce(this.withValue(e, 'k', () => lit), exp, n);
    }
    return this.coerce(e, exp, n);
};
function chainRoot(n) {
    let cur = n;
    while (true) {
        if ((ts.isPropertyAccessExpression(cur) || ts.isElementAccessExpression(cur) || ts.isCallExpression(cur)) && cur.questionDotToken)
            return cur;
        if (ts.isPropertyAccessExpression(cur) || ts.isElementAccessExpression(cur) || ts.isCallExpression(cur) || ts.isNonNullExpression(cur)) {
            if (!ts.isOptionalChain(cur) && !ts.isNonNullExpression(cur))
                return undefined;
            cur = cur.expression;
            continue;
        }
        return undefined;
    }
}
function needsChain(fc, n) {
    if (!ts.isOptionalChain(n))
        return false;
    const root = chainRoot(n);
    return !!root && !fc.override.has(root.expression);
}
P.lowerRaw = function (n, fc, exp) {
    switch (n.kind) {
        case SK.NumericLiteral: return (0, core_1.numLit)(Number(n.text.replace(/_/g, '')));
        case SK.BigIntLiteral: return (0, core_1.bigLit)(BigInt(n.text.slice(0, -1).replace(/_/g, '')));
        case SK.StringLiteral:
        case SK.NoSubstitutionTemplateLiteral: return (0, core_1.strLit)(n.text);
        case SK.TemplateExpression: return lowerTemplate(this, n, fc);
        case SK.TrueKeyword: return ir_1.E.bool(true);
        case SK.FalseKeyword: return ir_1.E.bool(false);
        case SK.NullKeyword: return ir_1.E.nullLit();
        case SK.Identifier: return this.lowerIdent(n, fc, exp);
        case SK.ThisKeyword: return this.lowerThis(n, fc);
        case SK.ParenthesizedExpression: return this.lowerExpr(n.expression, fc, exp);
        case SK.PropertyAccessExpression: {
            if (needsChain(fc, n))
                return this.lowerOptChain(n, fc, exp);
            const pa = n;
            const st = this.lowerStaticMember(pa, fc);
            if (st)
                return st;
            if (this.isNamespaceRef(pa.expression))
                return this.lowerIdentLike(pa, fc, exp);
            {
                const bs = this.resolveSym(this.checker.getSymbolAtLocation((0, stmts_1.skipParens)(pa.expression)));
                const ps = this.resolveSym(this.checker.getSymbolAtLocation(pa.name));
                const staticBase = bs && (bs.flags & (ts.SymbolFlags.ValueModule | ts.SymbolFlags.NamespaceModule | ts.SymbolFlags.Class)) &&
                    !(bs.flags & ts.SymbolFlags.Variable) && !(ts.isIdentifier((0, stmts_1.skipParens)(pa.expression)) && this.lookup(bs, fc)) &&
                    !(bs.declarations ?? []).some(d => this.isProjectDecl(d));
                if (staticBase && ps && !(ps.flags & (ts.SymbolFlags.ValueModule | ts.SymbolFlags.NamespaceModule | ts.SymbolFlags.Class))) {
                    // `StyleSheet.hairlineWidth`, `admin.firestore.FieldValue` members: static values
                    const name = this.externMemberName(ps, true);
                    if (this.coverage)
                        this.covExternals.add(name);
                    return this.externResult(name, [], exp ?? this.tyAt(pa, fc), pa);
                }
            }
            const first = firstIterated(this, pa, fc);
            if (first)
                return this.adapt(first, exp ?? this.tyAt(pa, fc), pa);
            const base = this.lowerExpr(pa.expression, fc);
            if ((0, ir_1.isPoison)(base))
                return this.derivedPoison(pa, fc, exp);
            if (base.ty.k === 'ext') {
                // a property of an external object: answered by the oracle
                const pt = exp ?? this.tyAt(pa, fc);
                if (this.coverage)
                    this.covExternals.add(`${base.ty.name}.get:${pa.name.text}`);
                return this.externResult(`${base.ty.name}.get:${pa.name.text}`, [base], pt, pa);
            }
            const e = this.memberOf(base, pa.name.text, pa, fc);
            // (a dictionary read is already at its type, optional where the program tests for absence)
            if (this.unfoldTy(base.ty).k === 'dict')
                return e;
            // members of library-typed values TypeScript types as `any` (a rejection reason `e`)
            if (this.checker.getTypeAtLocation(pa).flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown) && this.unfoldTy(base.ty).k === 'err')
                return e;
            return this.narrowedRead(e, pa, fc, exp);
        }
        case SK.ElementAccessExpression: {
            if (needsChain(fc, n))
                return this.lowerOptChain(n, fc, exp);
            return lowerElemAccess(this, n, fc, exp);
        }
        case SK.CallExpression: {
            if (needsChain(fc, n))
                return this.lowerOptChain(n, fc, exp);
            return this.lowerCall(n, fc, exp);
        }
        case SK.NewExpression: return this.lowerNew(n, fc, exp);
        case SK.PrefixUnaryExpression: return lowerPrefix(this, n, fc);
        case SK.PostfixUnaryExpression: return this.lowerUpdate(n, fc, true);
        case SK.BinaryExpression: return lowerBinary(this, n, fc, exp);
        case SK.ConditionalExpression: return lowerConditional(this, n, fc, exp);
        case SK.ArrowFunction:
        case SK.FunctionExpression: return this.lowerLambda(n, fc, exp);
        case SK.AwaitExpression: {
            const p = this.lowerAwaitOperand(n, fc);
            const v = (0, ir_1.mkVar)('aw', p.ty.t);
            fc.pre.push((0, ir_1.awaitItem)(v, p));
            return ir_1.E.var(v);
        }
        case SK.NonNullExpression: {
            if (needsChain(fc, n))
                return this.lowerOptChain(n, fc, exp);
            const inner = this.lowerExpr(n.expression, fc);
            return this.adapt(inner, this.tyAt(n, fc), n);
        }
        case SK.AsExpression:
        case SK.TypeAssertionExpression:
        case SK.SatisfiesExpression: return lowerAssertion(this, n, fc);
        case SK.ArrayLiteralExpression: return this.lowerArrayLit(n, fc, exp);
        case SK.ObjectLiteralExpression: return this.lowerObjectLit(n, fc, exp);
        case SK.VoidExpression: {
            const inner = n.expression;
            if (!ts.isNumericLiteral((0, stmts_1.skipParens)(inner)))
                this.lowerExprStmt(inner, fc, fc.pre);
            return ir_1.E.undef();
        }
        case SK.TypeOfExpression: {
            if (this.strict)
                (0, diag_1.reject)(n, 'unsupported', '`typeof` is only supported in comparisons that narrow a variable');
            // `typeof x` as a value: on the runtime value
            let x = this.unfoldE(this.lowerExpr(n.expression, fc));
            if ((0, ir_1.isPoison)(x))
                return ir_1.E.poison(ty_1.T.str);
            // (a function or object compared by identity: the closure or record in its cell)
            if (x.ty.k === 'box' && x.ty.t.k === 'fn')
                x = this.unboxFn(x);
            else if (x.ty.k === 'box' && x.ty.t.k === 'record')
                x = this.unboxCell(x);
            const d = x.ty.k === 'dyn' ? x : ir_1.E.prim(`(.toDyn ${(0, ty_1.showTy)(x.ty)})`, [x], [x.ty], ty_1.T.dyn);
            // (TypeScript types the result as the union of the typeof strings)
            return this.adapt(ir_1.E.prim('.dynTypeof', [d], [ty_1.T.dyn], ty_1.T.str), exp ?? this.tyAt(n, fc), n);
        }
        // a regex as a value: the record of its flags and source (regex.ts)
        case SK.RegularExpressionLiteral: return this.regexValue(this.regexLit(n));
        case SK.DeleteExpression: {
            const x = (0, stmts_1.skipParens)(n.expression);
            const dt = (ts.isElementAccessExpression(x) || ts.isPropertyAccessExpression(x)) ? this.dictTyOf(x.expression, fc) : undefined;
            if (!dt)
                (0, diag_1.reject)(n, 'no-delete', '`delete` is only supported on dictionary entries');
            const xa = x;
            const [d, k] = this.seq([() => this.lowerExpr(xa.expression, fc, dt),
                () => ts.isPropertyAccessExpression(xa) ? (0, core_1.strLit)(xa.name.text) : this.dictKey(xa.argumentExpression, fc)], fc);
            return ir_1.E.builtin(`(.dictDelete ${(0, ty_1.showTy)(dt.t)})`, [d, k], [dt, ty_1.T.str], ty_1.T.bool);
        }
        case SK.YieldExpression: (0, diag_1.reject)(n, 'no-generators', 'generators are not allowed');
        case SK.TaggedTemplateExpression: return lowerTaggedTemplate(this, n, fc);
        case SK.ClassExpression: (0, diag_1.reject)(n, 'unsupported-syntax', 'class expressions');
        case SK.SpreadElement: (0, diag_1.reject)(n, 'unsupported-syntax', 'spread in this position');
        case SK.JsxElement:
        case SK.JsxSelfClosingElement:
        case SK.JsxFragment: (0, diag_1.reject)(n, 'jsx', 'JSX is not supported');
        case SK.SuperKeyword: (0, diag_1.reject)(n, 'no-extends', '`super` (classes cannot extend)');
        case SK.MetaProperty: (0, diag_1.reject)(n, 'unsupported-syntax', '`new.target` / `import.meta`');
        default: (0, diag_1.reject)(n, 'unsupported-syntax', `expression kind ${SK[n.kind]}`);
    }
};
// ---------------------------------------------------------------------------------------
// identifiers, this
/** `m.keys().next().value` (also `values()` / `entries()`, and of a Set): the first element of
 * the collection in insertion order, or undefined (e.g. the oldest key of a bounded cache). */
function firstIterated(tr, pa, fc) {
    if (pa.name.text !== 'value')
        return undefined;
    const next = (0, stmts_1.skipParens)(pa.expression);
    if (!ts.isCallExpression(next) || next.arguments.length || !ts.isPropertyAccessExpression(next.expression) ||
        next.expression.questionDotToken || next.expression.name.text !== 'next')
        return undefined;
    const it = (0, stmts_1.skipParens)(next.expression.expression);
    if (!ts.isCallExpression(it) || it.arguments.length || !ts.isPropertyAccessExpression(it.expression) || it.expression.questionDotToken)
        return undefined;
    const method = it.expression.name.text;
    if (method !== 'keys' && method !== 'values' && method !== 'entries')
        return undefined;
    let ct;
    try {
        ct = tr.unfoldTy(tr.tyAt(it.expression.expression, fc));
    }
    catch {
        return undefined;
    }
    if (ct.k !== 'map' && !(ct.k === 'set' && method !== 'entries'))
        return undefined;
    const arr = tr.collectionSnapshot(tr.lowerExpr(it.expression.expression, fc), method, it);
    const el = arr.ty.t;
    return ir_1.E.builtin(`(.arrGetOpt ${(0, ty_1.showTy)(el)})`, [arr, (0, core_1.numLit)(0)], [arr.ty, ty_1.T.num], ty_1.T.opt(el));
}
/** Does a narrowed type of an unknown value still hold unknown values (`{}`, `{} | null`,
 * `unknown[]`, …)? Such a value stays unknown. */
function holdsUnknown(t) {
    return t.k === 'dyn' || (t.k === 'record' && t.fs.length === 0) ||
        ((t.k === 'arr' || t.k === 'dict' || t.k === 'opt') && holdsUnknown(t.t)) ||
        (t.k === 'union' && t.ts.every(m => m.k === 'null' || holdsUnknown(m)));
}
P.narrowedRead = function (stored, node, fc, exp) {
    if (exp) {
        const direct = this.convert(stored, exp, node, false, 0);
        if (direct)
            return direct;
    }
    // TypeScript narrowed the read to `never`: unreachable code, keep the stored value
    if (this.isNeverType(this.checker.getTypeAtLocation(node)))
        return exp ? this.withValue(stored, 'nv', () => ir_1.E.unreachable(exp)) : stored;
    if (stored.ty.k === 'dyn' || (stored.ty.k === 'opt' && stored.ty.t.k === 'dyn')) {
        // an `unknown` value narrowed to a type without IR representation (`object`,
        // `object & Record<"k", unknown>` after `"k" in x`) stays unknown
        let nt;
        try {
            nt = this.tyAt(node, fc);
        }
        catch (e) {
            if (isFatal(e))
                throw e;
            return stored;
        }
        // narrowed to a type that still holds unknown values (`any[]` after Array.isArray, `{}` and
        // `{} | null` after `x !== undefined` / `x !== null`, which hold strings and numbers too):
        // keep the value as unknown (its reads go through the runtime value; no copy, no cast)
        if (stored.ty.k === 'dyn' && holdsUnknown(nt))
            return stored;
        // (an optional unknown value, e.g. an optional field, narrowed so: TypeScript excluded undefined)
        if (stored.ty.k === 'opt' && nt.k !== 'dyn' && nt.k !== 'opt' && holdsUnknown(nt))
            return ir_1.E.unwrap(stored);
        return this.adapt(stored, nt, node);
    }
    const t = this.tyAt(node, fc);
    if (!exp && ts.isOptionalChain(node) && t.k === 'opt' && stored.ty.k !== 'opt') {
        // inside an optional chain TypeScript adds `undefined` for the short-circuit; the
        // value itself is defined here
        const c = this.convert(stored, t.t, node, true, 0);
        if (c)
            return c;
    }
    return this.adapt(stored, t, node);
};
P.externalValue = function (sym, id, fc, exp) {
    if (sym.flags & (ts.SymbolFlags.Function | ts.SymbolFlags.Method))
        (0, diag_1.reject)(id, 'external-call', `the external function ${id.text} used as a value`);
    if (sym.flags & (ts.SymbolFlags.ValueModule | ts.SymbolFlags.NamespaceModule))
        (0, diag_1.reject)(id, 'external-call', `the module ${id.text} used as a value`);
    const name = this.externMemberName(sym, false);
    if (this.coverage)
        this.covExternals.add(name);
    return this.externResult(name, [], exp ?? this.tyAt(id, fc), id);
};
P.isNamespaceRef = function (e) {
    const x = (0, stmts_1.skipParens)(e);
    if (!ts.isIdentifier(x))
        return false;
    const sym = this.resolveSym(this.checker.getSymbolAtLocation(x));
    return !!sym && !!(sym.flags & ts.SymbolFlags.ValueModule) && !(0, core_1.isLibDecl)(this.program, sym.declarations?.[0]);
};
P.lowerIdentLike = function (n, fc, exp) {
    const sym = this.resolveSym(this.checker.getSymbolAtLocation(n));
    if (!sym)
        (0, diag_1.reject)(n, 'unsupported', `unknown export ${n.name.text}`);
    const b = this.lookup(sym, fc);
    if (b)
        return this.narrowedRead(this.readBinding(b, n), n, fc, exp);
    const fd = this.topFunDecl(sym);
    if (fd && !fd.typeParameters?.length)
        return this.adapt(ir_1.E.funVal(this.funInfoFor(fd, new Map(), n)), this.tyAt(n, fc), n);
    (0, diag_1.reject)(n, 'unsupported', `export ${n.name.text} is not supported here`);
};
P.lowerIdent = function (id, fc, exp) {
    const raw = this.checker.getSymbolAtLocation(id);
    const sym = this.symAt(id);
    const libSym = !sym || !sym.declarations?.length || (0, core_1.isLibDecl)(this.program, sym.declarations[0]);
    if (libSym) {
        if (id.text === 'undefined')
            return ir_1.E.undef();
        if (id.text === 'NaN')
            return (0, core_1.numLit)(NaN);
        if (id.text === 'Infinity')
            return (0, core_1.numLit)(Infinity);
        if (sym && !['String', 'Number', 'Boolean', 'BigInt', 'Math', 'console', 'parseInt', 'parseFloat', 'isNaN', 'isFinite'].includes(id.text)) {
            return this.externalValue(sym, id, fc, exp);
        }
        (0, diag_1.reject)(id, 'unsupported-builtin', `${id.text} is not supported as a value`);
    }
    if (sym && !this.lookup(sym, fc) && sym.declarations?.length && !sym.declarations.some(d => this.isProjectDecl(d))) {
        // a value imported from a package
        return this.externalValue(sym, id, fc, exp);
    }
    void raw;
    const vd = sym?.valueDeclaration;
    if (vd && ts.isVariableDeclaration(vd) && this.isRegexConst(vd))
        return this.adapt(this.regexValue(this.regexLit(id)), exp ?? this.tyAt(id, fc), id);
    const b = this.lookup(sym, fc);
    if (b) {
        if (b.k === 'lifted') {
            const want = this.tyAt(id, fc);
            if (want.k === 'box') {
                // its one cell, created at its declaration
                if (!b.cell)
                    (0, diag_1.reject)(id, 'fn-identity', `the nested function ${id.text} used as a value compared by identity before its declaration`);
                return ir_1.E.var(b.cell);
            }
            return this.liftedAsValue(b, id, fc);
        }
        const e = this.readBinding(b, id);
        if (b.k === 'var' && b.holes && !this.holeWrites.has(id)) {
            // an array from `new Array(n)`: holes would be observable unless its length reached n
            const at = b.v.ty;
            const len = (0, ir_1.mkVar)('len', ty_1.T.num);
            fc.pre.push((0, ir_1.declItem)(len, ir_1.E.builtin(`(.arrLength ${(0, ty_1.showTy)(at.t)})`, [e], [at], ty_1.T.num)));
            const short = ir_1.E.prim('(.numCmp .lt)', [ir_1.E.var(len), ir_1.E.var(b.holes)], [ty_1.T.num, ty_1.T.num], ty_1.T.bool);
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.ite(short, [(0, ir_1.declItem)((0, ir_1.mkVar)('holes', ty_1.T.undef), ir_1.E.unreachable(ty_1.T.undef))], [])));
        }
        if (b.k === 'var' && (b.errVar || b.fixed))
            return e;
        return this.narrowedRead(e, id, fc, exp);
    }
    const fd = this.topFunDecl(sym);
    if (fd) {
        if (fd.typeParameters?.length)
            (0, diag_1.reject)(id, 'unsupported-generic', 'generic functions can only be called directly');
        const f = this.funInfoFor(fd, new Map(), id);
        const want = this.tyAt(id, fc);
        // a top-level function compared by identity: its one cell, created when the module starts
        if (want.k === 'box' && want.t.k === 'fn')
            return this.adapt(ir_1.E.gget(this.fnBox(f)), want, id);
        return this.adapt(ir_1.E.funVal(f), want, id);
    }
    if (sym.flags & ts.SymbolFlags.Class)
        (0, diag_1.reject)(id, 'unsupported', 'classes cannot be used as values');
    (0, diag_1.reject)(id, 'later-declared', `\`${id.text}\` is used before its declaration (e.g. by a closure created earlier)`);
};
P.lowerThis = function (n, fc) {
    for (let c = fc; c; c = c.parent) {
        if (c.thisPoison)
            return this.derivedPoison(n, fc);
        if (c.thisVar)
            return ir_1.E.var(c.thisVar);
        if (c.kind !== 'lambda' || ts.isFunctionExpression(c.tsNode))
            break;
    }
    (0, diag_1.reject)(n, 'no-this', '`this` is only allowed in class methods and constructors');
};
// ---------------------------------------------------------------------------------------
// members
P.classOfObj = function (c) {
    const ci = this.types.classes.get(c);
    if (ci)
        return ci;
    return this.types.mutStructs.find(m => m.name === c);
};
P.readField = function (base, name, node) {
    const c = base.ty.c;
    const info = this.classOfObj(c);
    if (!info)
        throw new ir_1.InternalError(`unknown class ${c}`);
    const i = info.fieldIdx.get(name);
    if (i !== undefined)
        return ir_1.E.getField(base, c, i, info.fields[i].ty);
    const ci = this.types.classes.get(c);
    if (ci) {
        const getter = this.classMember(ci, name, 'getter', node);
        if (getter)
            return ir_1.E.call(getter, [base]);
        const m = this.classMember(ci, name, 'method', node);
        if (m)
            (0, diag_1.reject)(node, 'unsupported', `method ${name} used as a value (call it, or wrap it in an arrow function)`);
    }
    (0, diag_1.reject)(node, 'unsupported', `no field ${name} on ${c}`);
};
P.memberOf = function (base0, name, node, fc) {
    if ((0, ir_1.isPoison)(base0))
        return this.derivedPoison(node, fc);
    const base = this.unfoldE(base0);
    const t = base.ty;
    if (t.k === 'box' && t.t.k === 'record')
        return this.memberOf(this.unboxCell(base), name, node, fc);
    if ((0, ty_1.tyEq)(t, ty_1.REGEXP_TY)) {
        // a regex value: its flags as booleans; its lastIndex (state) is not modelled
        if (name === 'lastIndex')
            (0, diag_1.reject)(node, 'no-regexp', 'lastIndex of a regular expression (its matching state) is not modelled');
        const FLAG = { global: 'g', ignoreCase: 'i', multiline: 'm', dotAll: 's', unicode: 'u', unicodeSets: 'v', sticky: 'y', hasIndices: 'd' };
        if (Object.hasOwn(FLAG, name))
            return this.withValue(base, 're', x => ir_1.E.prim('.strIncludes', [ir_1.E.getRec(x, 0), (0, core_1.strLit)(FLAG[name]), (0, core_1.numLit)(0)], [ty_1.T.str, ty_1.T.str, ty_1.T.num], ty_1.T.bool));
    }
    if (t.k === 'ext') {
        if (this.coverage)
            this.covExternals.add(`${t.name}.get:${name}`);
        return this.externResult(`${t.name}.get:${name}`, [base], this.tyAt(node, fc), node);
    }
    if (t.k === 'union') {
        // a property every member has (e.g. the discriminant): case split
        const target = this.tyAt(node, fc);
        return ir_1.E.caseU(base, t.ts.map(m => {
            const v = (0, ir_1.mkVar)('m', m);
            return { v, body: this.adapt(this.memberOf(ir_1.E.var(v), name, node, fc), target, node) };
        }));
    }
    switch (t.k) {
        case 'dyn': return ir_1.E.builtin('.dynGet', [base, (0, core_1.strLit)(name)], [ty_1.T.dyn, ty_1.T.str], ty_1.T.dyn);
        case 'dict': return this.dictRead(base, (0, core_1.strLit)(name), node, fc);
        case 'record': {
            const i = t.fs.findIndex(f => f.name === name);
            if (i < 0)
                (0, diag_1.reject)(node, 'unsupported', `no field ${name}`);
            return ir_1.E.getRec(base, i);
        }
        case 'obj': return this.readField(base, name, node);
        case 'arr':
            if (name === 'length')
                return ir_1.E.builtin(`(.arrLength ${(0, ty_1.showTy)(t.t)})`, [base], [t], ty_1.T.num);
            break;
        case 'tarr':
            if (name === 'length')
                return ir_1.E.builtin(`(.taLength .${t.kind})`, [base], [t], ty_1.T.num);
            break;
        case 'str':
            if (name === 'length')
                return ir_1.E.prim('.strLength', [base], [ty_1.T.str], ty_1.T.num);
            break;
        case 'enum':
            if (name === 'length')
                return ir_1.E.prim('.strLength', [this.toStr(base, node)], [ty_1.T.str], ty_1.T.num);
            break;
        case 'tup':
            if (name === 'length')
                return this.withValue(base, 'p', () => (0, core_1.numLit)(t.ts.length));
            break;
        case 'map':
            if (name === 'size')
                return ir_1.E.builtin(`(.mapSize ${(0, ty_1.showTy)(t.key)} ${(0, ty_1.showTy)(t.val)})`, [base], [t], ty_1.T.num);
            break;
        case 'set':
            if (name === 'size')
                return ir_1.E.builtin(`(.setSize ${(0, ty_1.showTy)(t.t)})`, [base], [t], ty_1.T.num);
            break;
        case 'err':
            if (name === 'message')
                return ir_1.E.prim('.errMessage', [base], [ty_1.T.err], ty_1.T.str);
            if (name === 'name')
                return ir_1.E.prim('.errName', [base], [ty_1.T.err], ty_1.T.str);
            if (name === 'stack' || name === 'cause')
                (0, diag_1.reject)(node, 'unsupported', `Error.${name} is not supported`);
            break;
    }
    (0, diag_1.reject)(node, 'unsupported', `property ${name} of ${(0, ty_1.prettyTy)(t)} is not supported`);
};
function lowerElemAccess(tr, ea, fc, exp) {
    const arg = (0, stmts_1.skipParens)(ea.argumentExpression);
    let b0 = tr.unfoldE(tr.lowerExpr(ea.expression, fc));
    if (b0.ty.k === 'box' && b0.ty.t.k === 'record')
        b0 = tr.unboxCell(b0);
    if ((0, ir_1.isPoison)(b0)) {
        tr.lowerExpr(ea.argumentExpression, fc);
        return tr.derivedPoison(ea, fc, exp);
    }
    const bt = b0.ty;
    if (bt.k === 'tup' && ts.isNumericLiteral(arg))
        return tr.narrowedRead(ir_1.E.getTup(b0, Number(arg.text)), ea, fc);
    if (bt.k === 'tup') {
        // a computed index into a homogeneous tuple (e.g. an `as const` list): index an array of
        // its elements
        if (bt.ts.length === 0 || !bt.ts.every(x => (0, ty_1.tyEq)(x, bt.ts[0])))
            (0, diag_1.reject)(arg, 'unsupported', 'computed index into a tuple with elements of different types');
        const el = bt.ts[0];
        const at = ty_1.T.arr(el);
        const arr = tr.withValue(b0, 'p', x => ir_1.E.builtin(`(.arrOf ${(0, ty_1.showTy)(el)} ${bt.ts.length})`, bt.ts.map((_, i) => ir_1.E.getTup(x, i)), bt.ts.map(() => el), at));
        const [a, i] = tr.seq([() => arr, () => tr.lowerExpr(ea.argumentExpression, fc, ty_1.T.num)], fc);
        const want = tr.tyAt(ea, fc);
        const e = want.k === 'opt' || defensiveContext(ea) || (exp && exp.k === 'opt')
            ? ir_1.E.builtin(`(.arrGetOpt ${(0, ty_1.showTy)(el)})`, [a, i], [at, ty_1.T.num], ty_1.T.opt(el))
            : ir_1.E.builtin(`(.arrGet ${(0, ty_1.showTy)(el)})`, [a, i], [at, ty_1.T.num], el);
        return e.ty.k === 'opt' && want.k !== 'opt' && (defensiveContext(ea) || (exp && exp.k === 'opt')) ? e : tr.adapt(e, want, ea);
    }
    if (bt.k === 'dict') {
        const [d, k] = tr.seq([() => b0, () => tr.dictKey(ea.argumentExpression, fc)], fc);
        return tr.dictRead(d, k, ea, fc, exp);
    }
    if (bt.k === 'dyn') {
        const [d, k] = tr.seq([() => b0, () => tr.dictKey(ea.argumentExpression, fc)], fc);
        return tr.narrowedRead(ir_1.E.builtin('.dynGet', [d, k], [ty_1.T.dyn, ty_1.T.str], ty_1.T.dyn), ea, fc, exp);
    }
    if (bt.k === 'record' || bt.k === 'obj') {
        if (!ts.isStringLiteral(arg)) {
            // a key of a string-literal union whose cases are all properties (`labels[lang]`): a case
            // split on the key
            const names = bt.k === 'record' ? bt.fs.map(f => f.name) : (tr.classOfObj(bt.c)?.fields ?? []).map(f => f.name);
            const kt = tr.unfoldTy(tr.tyAt(ea.argumentExpression, fc));
            if (kt.k !== 'enum' || !kt.cases.every(c => names.includes(c)))
                (0, diag_1.reject)(arg, 'computed-key', `computed property access on ${(0, ty_1.prettyTy)(bt)}`);
            const [o, k] = tr.seq([() => b0, () => tr.lowerExpr(ea.argumentExpression, fc, kt)], fc);
            const want = exp ?? tr.tyAt(ea, fc);
            return tr.withValue(o, 'o', ov => tr.withValue(k, 'k', kv => {
                let acc = ir_1.E.unreachable(want);
                for (let i = kt.cases.length - 1; i >= 0; i--) {
                    acc = ir_1.E.cond(ir_1.E.seq(kv, ir_1.E.enumLit(kt, i)), tr.adapt(tr.memberOf(ov, kt.cases[i], ea, fc), want, ea), acc);
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
            return ir_1.E.unwrap(ir_1.E.extern(`${bt.name}.get:[]`, [o, k], ty_1.T.opt(ty_1.T.str)));
        }
        return tr.externResult(`${bt.name}.get:[]`, [o, k], want, ea);
    }
    const [base, idx] = tr.seq([() => b0, () => tr.lowerExpr(ea.argumentExpression, fc, ty_1.T.num)], fc);
    let want = tr.tyAt(ea, fc);
    if (ts.isOptionalChain(ea) && want.k === 'opt' && base.ty.k === 'arr' && base.ty.t.k !== 'opt')
        want = want.t;
    // `a[i]?.x`, `a[i] ?? d`, `a[i] === undefined`: the program handles a missing element, so
    // read it as optional (JavaScript yields undefined; TypeScript's type omits it)
    if ((defensiveContext(ea) || (exp && exp.k === 'opt')) && want.k !== 'opt' && (base.ty.k === 'arr' || base.ty.k === 'str')) {
        if (base.ty.k === 'arr')
            return ir_1.E.builtin(`(.arrGetOpt ${(0, ty_1.showTy)(base.ty.t)})`, [base, idx], [base.ty, ty_1.T.num], ty_1.T.opt(base.ty.t));
        return strIndex(tr, base, idx);
    }
    const t = base.ty;
    if (t.k === 'arr') {
        const e = want.k === 'opt' && t.t.k !== 'opt'
            ? ir_1.E.builtin(`(.arrGetOpt ${(0, ty_1.showTy)(t.t)})`, [base, idx], [t, ty_1.T.num], ty_1.T.opt(t.t))
            : ir_1.E.builtin(`(.arrGet ${(0, ty_1.showTy)(t.t)})`, [base, idx], [t, ty_1.T.num], t.t);
        return tr.adapt(e, want, ea);
    }
    if (t.k === 'str')
        return tr.adapt(strIndex(tr, base, idx), want, ea);
    if (t.k === 'tarr') {
        return tr.adapt(ir_1.E.builtin(`(.taGet .${t.kind})`, [base, idx], [t, ty_1.T.num], t.kind === 'bi64' || t.kind === 'bu64' ? ty_1.T.bigint : ty_1.T.num), want, ea);
    }
    (0, diag_1.reject)(ea, 'unsupported', `indexing a value of type ${(0, ty_1.prettyTy)(t)}`);
}
/** Is the value of `n` immediately tested for undefined (`?.`, `??`, `=== undefined`)? */
function defensiveContext(n) {
    let c = n;
    while (c.parent && ts.isParenthesizedExpression(c.parent))
        c = c.parent;
    const p = c.parent;
    if (!p)
        return false;
    if ((ts.isPropertyAccessExpression(p) || ts.isElementAccessExpression(p) || ts.isCallExpression(p)) && p.questionDotToken && p.expression === c)
        return true;
    // tested for truthiness (`if (!d[k])`, `while (a[i])`, `d[k] ? … : …`, `d[k] || x`): a missing
    // element is undefined, which is falsy
    if (ts.isPrefixUnaryExpression(p) && p.operator === SK.ExclamationToken)
        return true;
    if ((ts.isIfStatement(p) || ts.isWhileStatement(p) || ts.isDoStatement(p)) && p.expression === c)
        return true;
    if (ts.isForStatement(p) && p.condition === c)
        return true;
    if (ts.isConditionalExpression(p) && p.condition === c)
        return true;
    if (ts.isBinaryExpression(p)) {
        const k = p.operatorToken.kind;
        if ((k === SK.AmpersandAmpersandToken || k === SK.BarBarToken) && p.left === c)
            return true;
        if (k === SK.QuestionQuestionToken && p.left === c)
            return true;
        if (k === SK.EqualsEqualsEqualsToken || k === SK.ExclamationEqualsEqualsToken) {
            const other = p.left === c ? p.right : p.left;
            const o = (0, stmts_1.skipParens)(other);
            return ts.isIdentifier(o) && o.text === 'undefined';
        }
    }
    return false;
}
// ---------------------------------------------------------------------------------------
// optional chains
P.lowerOptChain = function (n, fc, exp) {
    const root = chainRoot(n);
    const baseNode = root.expression;
    const base = this.nullishToOpt(this.lowerExpr(baseNode, fc), baseNode);
    const resultTy = exp ?? this.tyAt(n, fc);
    if (base.ty.k === 'dyn') {
        // a value of type any/unknown may be undefined or null: the chain yields undefined then,
        // without reading a property of it
        const dynLit = (t) => ir_1.E.prim(`(.toDyn ${(0, ty_1.showTy)(t)})`, [t.k === 'null' ? ir_1.E.nullLit() : ir_1.E.undef()], [t], ty_1.T.dyn);
        const isNullish = (x) => ir_1.E.or(ir_1.E.prim('.dynEq', [x, dynLit(ty_1.T.undef)], [ty_1.T.dyn, ty_1.T.dyn], ty_1.T.bool), ir_1.E.prim('.dynEq', [x, dynLit(ty_1.T.null)], [ty_1.T.dyn, ty_1.T.dyn], ty_1.T.bool));
        const bv = this.bindTemp(base, fc, 'o');
        fc.override.set(baseNode, ir_1.E.var(bv));
        let rest, pre;
        try {
            [rest, pre] = this.isolate(fc, () => this.lowerExpr(n, fc, resultTy));
        }
        finally {
            fc.override.delete(baseNode);
        }
        const dflt = resultTy.k === 'dyn' ? dynLit(ty_1.T.undef) : resultTy.k === 'opt' ? ir_1.E.none(resultTy.t) : resultTy.k === 'undef' ? ir_1.E.undef() : null;
        if (!dflt)
            (0, diag_1.reject)(n, 'unsupported', `optional chain on an unknown value at type ${(0, ty_1.prettyTy)(resultTy)}, which excludes undefined`);
        if (!pre.length)
            return ir_1.E.cond(isNullish(ir_1.E.var(bv)), dflt, rest);
        const r = this.mutTemp(resultTy, fc);
        fc.pre.push((0, ir_1.stmtItem)(ir_1.S.ite(isNullish(ir_1.E.var(bv)), [r.set(dflt)], [...pre, r.set(rest)])));
        return r.get();
    }
    if (base.ty.k !== 'opt') {
        // never nullish: plain access (the caller converts the result)
        fc.override.set(baseNode, base);
        try {
            return this.lowerExpr(n, fc);
        }
        finally {
            fc.override.delete(baseNode);
        }
    }
    const inner = base.ty.t;
    const v = (0, ir_1.mkVar)('o', inner);
    // TypeScript may type the chain without `undefined` when it believes the base is
    // defined (e.g. `xs[0]?.x`); the chain still yields undefined when it is not
    const chainTy = resultTy.k === 'opt' || resultTy.k === 'undef' ? resultTy : ty_1.T.opt(resultTy);
    fc.override.set(baseNode, ir_1.E.var(v));
    let rest, pre;
    try {
        [rest, pre] = this.isolate(fc, () => this.lowerExpr(n, fc, chainTy));
    }
    finally {
        fc.override.delete(baseNode);
    }
    const dflt = chainTy.k === 'opt' ? ir_1.E.none(chainTy.t) : ir_1.E.undef();
    let res;
    if (!pre.length)
        res = ir_1.E.caseOpt(base, dflt, v, rest);
    else {
        const r = this.mutTemp(chainTy, fc);
        fc.pre.push((0, ir_1.stmtItem)({ k: 'caseOptS', e: base, none: [r.set(dflt)], v, some: [...pre, r.set(rest)] }));
        res = r.get();
    }
    return chainTy === resultTy ? res : this.adapt(res, resultTy, n);
};
/** `T | null | undefined`-like values as `opt T'` (null and undefined both become `none`). */
P.nullishToOpt = function (e0, node) {
    if ((0, ir_1.isPoison)(e0))
        return e0;
    const e = e0.ty.k === 'named' ? this.unfoldE(e0) : e0;
    const t = e.ty;
    const stripNull = (x) => {
        const u = x.ty;
        if (u.k !== 'union' || !u.ts.some(m => m.k === 'null'))
            return null;
        const rest = u.ts.filter(m => m.k !== 'null');
        const target = rest.length === 1 ? rest[0] : ty_1.T.union(rest);
        return ir_1.E.caseU(x, u.ts.map(m => {
            const v = (0, ir_1.mkVar)('m', m);
            return { v, body: m.k === 'null' ? ir_1.E.none(target) : ir_1.E.some(this.coerce(ir_1.E.var(v), target, node)) };
        }));
    };
    if (t.k === 'opt') {
        const tt = this.unfoldTy(t.t);
        if (tt.k === 'union' && tt.ts.some(m => m.k === 'null')) {
            const rest = tt.ts.filter(m => m.k !== 'null');
            const target = rest.length === 1 ? rest[0] : ty_1.T.union(rest);
            const v = (0, ir_1.mkVar)('x', t.t);
            return ir_1.E.caseOpt(e, ir_1.E.none(target), v, stripNull(this.unfoldE(ir_1.E.var(v))));
        }
        return e;
    }
    return stripNull(e) ?? e;
};
// ---------------------------------------------------------------------------------------
// templates and string conversion
function lowerTemplate(tr, n, fc) {
    const parts = tr.seq(n.templateSpans.map(sp => () => tr.toStr(tr.lowerExpr(sp.expression, fc), sp.expression)), fc);
    let acc = n.head.text ? (0, core_1.strLit)(n.head.text) : null;
    const cat = (a, b) => a ? ir_1.E.prim('.strConcat', [a, b], [ty_1.T.str, ty_1.T.str], ty_1.T.str) : b;
    n.templateSpans.forEach((sp, i) => {
        acc = cat(acc, parts[i]);
        if (sp.literal.text)
            acc = cat(acc, (0, core_1.strLit)(sp.literal.text));
    });
    return acc ?? (0, core_1.strLit)('');
}
/** `String.raw\`…\``: the template's raw text (escape sequences as written, line breaks as LF,
 * as ECMA-262's TRV) with the substitutions converted as in a template literal. Other tags are
 * rejected. */
function lowerTaggedTemplate(tr, n, fc) {
    const tag = (0, stmts_1.skipParens)(n.tag);
    const isRaw = ts.isPropertyAccessExpression(tag) && tag.name.text === 'raw' && ts.isIdentifier(tag.expression) &&
        tag.expression.text === 'String' && (0, core_1.isLibDecl)(tr.program, tr.symAt(tag.expression)?.declarations?.[0]);
    if (!isRaw || n.typeArguments)
        (0, diag_1.reject)(n, 'unsupported-syntax', 'tagged templates (other than String.raw)');
    const raw = (lit) => (lit.rawText ?? lit.text).replace(/\r\n?/g, '\n');
    const t = n.template;
    if (ts.isNoSubstitutionTemplateLiteral(t))
        return (0, core_1.strLit)(raw(t));
    const parts = tr.seq(t.templateSpans.map(sp => () => tr.toStr(tr.lowerExpr(sp.expression, fc), sp.expression)), fc);
    const cat = (a, b) => a ? ir_1.E.prim('.strConcat', [a, b], [ty_1.T.str, ty_1.T.str], ty_1.T.str) : b;
    let acc = raw(t.head) ? (0, core_1.strLit)(raw(t.head)) : null;
    t.templateSpans.forEach((sp, i) => {
        acc = cat(acc, parts[i]);
        if (raw(sp.literal))
            acc = cat(acc, (0, core_1.strLit)(raw(sp.literal)));
    });
    return acc ?? (0, core_1.strLit)('');
}
P.toStr = function (e0, node) {
    if ((0, ir_1.isPoison)(e0))
        return ir_1.E.poison(ty_1.T.str);
    const e = this.unfoldE(e0);
    if ((0, core_1.holdsTimer)(e.ty))
        (0, diag_1.reject)(node, 'timer-handle', 'a Node timer handle as a string (Node gives its id)');
    switch (e.ty.k) {
        case 'str': return e;
        case 'enum': return this.coerce(e, ty_1.T.str, node);
        case 'num': return ir_1.E.prim('.numToStr', [e], [ty_1.T.num], ty_1.T.str);
        case 'bigint': return ir_1.E.prim('.bigToStr', [e], [ty_1.T.bigint], ty_1.T.str);
        case 'bool': return ir_1.E.prim('.boolToStr', [e], [ty_1.T.bool], ty_1.T.str);
        case 'undef': return this.withValue(e, 'u', () => (0, core_1.strLit)('undefined'));
        case 'null': return this.withValue(e, 'u', () => (0, core_1.strLit)('null'));
        case 'obj': {
            // ToString of a class instance calls its toString() method
            const ci = this.types.classes.get(e.ty.c);
            const m = ci && this.classMember(ci, 'toString', 'method', node);
            if (m && m.params.length === 1 && m.ret.k === 'str')
                return ir_1.E.call(m, [e]);
            break;
        }
        case 'opt': {
            const v = (0, ir_1.mkVar)('x', e.ty.t);
            return ir_1.E.caseOpt(e, (0, core_1.strLit)('undefined'), v, this.toStr(ir_1.E.var(v), node));
        }
        case 'dyn': return ir_1.E.builtin('.dynToStr', [e], [ty_1.T.dyn], ty_1.T.str);
        case 'union': return ir_1.E.caseU(e, e.ty.ts.map(m => { const v = (0, ir_1.mkVar)('m', m); return { v, body: this.toStr(ir_1.E.var(v), node) }; }));
        case 'err': return this.withValue(e, 'e', x => {
            // Error.prototype.toString: name, ": ", message (either part may be empty)
            const name = ir_1.E.prim('.errName', [x], [ty_1.T.err], ty_1.T.str);
            const msg = ir_1.E.prim('.errMessage', [x], [ty_1.T.err], ty_1.T.str);
            const cat = (a, b) => ir_1.E.prim('.strConcat', [a, b], [ty_1.T.str, ty_1.T.str], ty_1.T.str);
            return ir_1.E.cond(ir_1.E.seq(msg, (0, core_1.strLit)('')), name, ir_1.E.cond(ir_1.E.seq(name, (0, core_1.strLit)('')), msg, cat(cat(name, (0, core_1.strLit)(': ')), msg)));
        });
    }
    (0, diag_1.reject)(node, 'template-hole', `cannot convert ${(0, ty_1.prettyTy)(e.ty)} to a string implicitly; only string, number, bigint and boolean are allowed`);
};
// ---------------------------------------------------------------------------------------
// operators
function isStringy(t) { return t.k === 'str' || t.k === 'enum'; }
const NUM_BIN = {
    [SK.PlusToken]: 'add', [SK.MinusToken]: 'sub', [SK.AsteriskToken]: 'mul', [SK.SlashToken]: 'div', [SK.PercentToken]: 'rem',
    [SK.AsteriskAsteriskToken]: 'pow', [SK.AmpersandToken]: 'band', [SK.BarToken]: 'bor', [SK.CaretToken]: 'bxor',
    [SK.LessThanLessThanToken]: 'shl', [SK.GreaterThanGreaterThanToken]: 'sar', [SK.GreaterThanGreaterThanGreaterThanToken]: 'shr',
};
const CMP = {
    [SK.LessThanToken]: 'lt', [SK.LessThanEqualsToken]: 'le', [SK.GreaterThanToken]: 'gt', [SK.GreaterThanEqualsToken]: 'ge',
};
const COMPOUND = {
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
function dynCompare(tr, cmp, a, b, node) {
    const tag = (d) => ir_1.E.prim('.dynTypeof', [d], [ty_1.T.dyn], ty_1.T.str);
    const is = (d, s) => ir_1.E.seq(tag(d), (0, core_1.strLit)(s));
    const as = (d, t) => ir_1.E.unwrap(ir_1.E.prim(`(.dynCast ${(0, ty_1.showTy)(t)})`, [d], [ty_1.T.dyn], ty_1.T.opt(t)));
    const isNull = (d) => ir_1.E.prim('.dynEq', [d, ir_1.E.prim('(.toDyn .null)', [ir_1.E.nullLit()], [ty_1.T.null], ty_1.T.dyn)], [ty_1.T.dyn, ty_1.T.dyn], ty_1.T.bool);
    const toDyn = (x) => x.ty.k === 'dyn' ? x
        : isStringy(x.ty) ? ir_1.E.prim('(.toDyn .str)', [tr.toStr(x, node)], [ty_1.T.str], ty_1.T.dyn) : tr.coerce(x, ty_1.T.dyn, node);
    const prim = (x) => tr.withValue(toDyn(x), 'd', d => ir_1.E.cond(is(d, 'object'), ir_1.E.cond(isNull(d), d, ir_1.E.prim('(.toDyn .str)', [ir_1.E.builtin('.dynToStr', [d], [ty_1.T.dyn], ty_1.T.str)], [ty_1.T.str], ty_1.T.dyn)), ir_1.E.cond(is(d, 'function'), ir_1.E.unreachable(ty_1.T.dyn), d)));
    const num = (p) => ir_1.E.cond(is(p, 'number'), as(p, ty_1.T.num), ir_1.E.cond(is(p, 'string'), ir_1.E.prim('.strToNum', [as(p, ty_1.T.str)], [ty_1.T.str], ty_1.T.num), ir_1.E.cond(is(p, 'boolean'), ir_1.E.cond(as(p, ty_1.T.bool), (0, core_1.numLit)(1), (0, core_1.numLit)(0)), ir_1.E.cond(is(p, 'undefined'), (0, core_1.numLit)(NaN), ir_1.E.cond(isNull(p), (0, core_1.numLit)(0), ir_1.E.unreachable(ty_1.T.num))))));
    return tr.withValue(prim(a), 'pa', pa => tr.withValue(prim(b), 'pb', pb => {
        const sa = (0, ir_1.mkVar)('sa', ty_1.T.str), sb = (0, ir_1.mkVar)('sb', ty_1.T.str);
        const str = (p) => ir_1.E.prim('(.dynCast .str)', [p], [ty_1.T.dyn], ty_1.T.opt(ty_1.T.str));
        const nums = ir_1.E.prim(`(.numCmp .${cmp})`, [num(pa), num(pb)], [ty_1.T.num, ty_1.T.num], ty_1.T.bool);
        return ir_1.E.caseOpt(str(pa), nums, sa, ir_1.E.caseOpt(str(pb), nums, sb, ir_1.E.prim(`(.strCmp .${cmp})`, [ir_1.E.var(sa), ir_1.E.var(sb)], [ty_1.T.str, ty_1.T.str], ty_1.T.bool)));
    }));
}
P.arith = function (op, a0, b0, node) {
    if ((0, ir_1.isPoison)(a0) || (0, ir_1.isPoison)(b0)) {
        if (CMP[op])
            return ir_1.E.poison(ty_1.T.bool);
        const other = (0, ir_1.isPoison)(a0) ? b0 : a0;
        return ir_1.E.poison((0, ir_1.isPoison)(other) ? ty_1.T.undef : other.ty);
    }
    const a = this.unfoldE(a0), b = this.unfoldE(b0);
    const ta = a.ty, tb = b.ty;
    if ((0, core_1.holdsTimer)(ta) || (0, core_1.holdsTimer)(tb))
        (0, diag_1.reject)(node, 'timer-handle', 'a Node timer handle in arithmetic, a comparison or a string (Node converts it to its id)');
    if (ta.k === 'dyn' || tb.k === 'dyn') {
        // string + unknown: ToPrimitive then ToString, as String(x) for the modelled runtime types
        if (op === SK.PlusToken && (isStringy(ta) || isStringy(tb))) {
            return ir_1.E.prim('.strConcat', [this.toStr(a, node), this.toStr(b, node)], [ty_1.T.str, ty_1.T.str], ty_1.T.str);
        }
        const c = CMP[op];
        if (c)
            return dynCompare(this, c, a, b, node);
        (0, diag_1.reject)(node, 'any-op', `operator ${ts.tokenToString(op)} on a value of type any/unknown (cast it first)`);
    }
    if (op === SK.PlusToken && isStringy(ta) && isStringy(tb)) {
        return ir_1.E.prim('.strConcat', [this.toStr(a, node), this.toStr(b, node)], [ty_1.T.str, ty_1.T.str], ty_1.T.str);
    }
    const cmp = CMP[op];
    if (cmp) {
        if (ta.k === 'num' && tb.k === 'num')
            return ir_1.E.prim(`(.numCmp .${cmp})`, [a, b], [ty_1.T.num, ty_1.T.num], ty_1.T.bool);
        if (ta.k === 'bigint' && tb.k === 'bigint')
            return ir_1.E.prim(`(.bigCmp .${cmp})`, [a, b], [ty_1.T.bigint, ty_1.T.bigint], ty_1.T.bool);
        if (isStringy(ta) && isStringy(tb))
            return ir_1.E.prim(`(.strCmp .${cmp})`, [this.toStr(a, node), this.toStr(b, node)], [ty_1.T.str, ty_1.T.str], ty_1.T.bool);
        (0, diag_1.reject)(node, 'mixed-compare', `comparison between ${(0, ty_1.prettyTy)(ta)} and ${(0, ty_1.prettyTy)(tb)}`);
    }
    const nb = NUM_BIN[op];
    if (nb) {
        if (ta.k === 'num' && tb.k === 'num')
            return ir_1.E.prim(`(.numBin .${nb})`, [a, b], [ty_1.T.num, ty_1.T.num], ty_1.T.num);
        if (ta.k === 'bigint' && tb.k === 'bigint') {
            if (nb === 'shr')
                (0, diag_1.reject)(node, 'unsupported', '`>>>` on bigint');
            return ir_1.E.prim(`(.bigBin .${nb})`, [a, b], [ty_1.T.bigint, ty_1.T.bigint], ty_1.T.bigint);
        }
        if (op === SK.PlusToken)
            (0, diag_1.reject)(node, 'mixed-plus', `\`+\` between ${(0, ty_1.prettyTy)(ta)} and ${(0, ty_1.prettyTy)(tb)}; use a template literal or an explicit conversion`);
        (0, diag_1.reject)(node, 'unsupported', `operator ${ts.tokenToString(op)} on ${(0, ty_1.prettyTy)(ta)} and ${(0, ty_1.prettyTy)(tb)}`);
    }
    (0, diag_1.reject)(node, 'unsupported', `operator ${ts.tokenToString(op)}`);
};
function lowerPrefix(tr, u, fc) {
    if (u.operator === SK.PlusToken || u.operator === SK.MinusToken || u.operator === SK.TildeToken) {
        if ((0, core_1.holdsTimer)(tr.tyAt(u.operand, fc)))
            (0, diag_1.reject)(u, 'timer-handle', 'a Node timer handle as a number (Node converts it to its id)');
    }
    switch (u.operator) {
        case SK.PlusPlusToken:
        case SK.MinusMinusToken: return tr.lowerUpdate(u, fc, true);
        case SK.ExclamationToken: return ir_1.E.not(tr.lowerCond(u.operand, fc));
        case SK.MinusToken: {
            const o = (0, stmts_1.skipParens)(u.operand);
            if (ts.isNumericLiteral(o))
                return (0, core_1.numLit)(-Number(o.text.replace(/_/g, '')));
            if (ts.isBigIntLiteral(o))
                return (0, core_1.bigLit)(-BigInt(o.text.slice(0, -1).replace(/_/g, '')));
            const e = tr.unfoldE(tr.lowerExpr(u.operand, fc));
            if (e.ty.k === 'num')
                return ir_1.E.prim('(.numUn .neg)', [e], [ty_1.T.num], ty_1.T.num);
            if (e.ty.k === 'bigint')
                return ir_1.E.prim('.bigNeg', [e], [ty_1.T.bigint], ty_1.T.bigint);
            if (e.ty.k === 'dyn')
                (0, diag_1.reject)(u, 'any-op', 'unary minus on a value of type any/unknown');
            (0, diag_1.reject)(u, 'unsupported', `unary minus on ${(0, ty_1.prettyTy)(e.ty)}`);
        }
        case SK.PlusToken: {
            const e = tr.unfoldE(tr.lowerExpr(u.operand, fc));
            if (e.ty.k === 'num')
                return e;
            if (e.ty.k === 'dyn')
                (0, diag_1.reject)(u, 'any-op', 'unary plus on a value of type any/unknown');
            (0, diag_1.reject)(u, 'unsupported', `unary plus on ${(0, ty_1.prettyTy)(e.ty)}; use Number(...)`);
        }
        case SK.TildeToken: {
            const e = tr.unfoldE(tr.lowerExpr(u.operand, fc));
            if (e.ty.k === 'num')
                return ir_1.E.prim('(.numUn .bnot)', [e], [ty_1.T.num], ty_1.T.num);
            if (e.ty.k === 'bigint')
                return ir_1.E.prim('.bigNot', [e], [ty_1.T.bigint], ty_1.T.bigint);
            (0, diag_1.reject)(u, 'unsupported', `~ on ${(0, ty_1.prettyTy)(e.ty)}`);
        }
    }
    (0, diag_1.reject)(u, 'unsupported-syntax', `prefix operator ${ts.tokenToString(u.operator)}`);
}
function isBoolTs(t) {
    if (t.flags & (ts.TypeFlags.Boolean | ts.TypeFlags.BooleanLiteral))
        return true;
    return t.isUnion() && t.types.every(m => !!(m.flags & ts.TypeFlags.BooleanLiteral));
}
function lowerBinary(tr, b, fc, exp) {
    const op = b.operatorToken.kind;
    if (op >= SK.FirstAssignment && op <= SK.LastAssignment)
        return tr.lowerAssign(b, fc, true);
    switch (op) {
        case SK.CommaToken:
            tr.lowerExprStmt(b.left, fc, fc.pre);
            return tr.lowerExpr(b.right, fc, exp);
        case SK.AmpersandAmpersandToken:
        case SK.BarBarToken: {
            const whole = tr.checker.getTypeAtLocation(b);
            if (isBoolTs(whole) || (exp && exp.k === 'bool'))
                return tr.lowerCond(b, fc);
            return lowerValueLogical(tr, b, fc, exp);
        }
        case SK.QuestionQuestionToken: return lowerNullish(tr, b, fc, exp);
        case SK.EqualsEqualsEqualsToken:
        case SK.ExclamationEqualsEqualsToken: {
            const r = lowerEq(tr, b, fc);
            return op === SK.EqualsEqualsEqualsToken ? r : ir_1.E.not(r);
        }
        case SK.EqualsEqualsToken:
        case SK.ExclamationEqualsToken: {
            const lit = isNullishLit(tr, b.right) ? b.right : isNullishLit(tr, b.left) ? b.left : null;
            if (!lit)
                (0, diag_1.reject)(b, 'no-loose-eq', '`==` and `!=` are only allowed against null or undefined; use `===` / `!==`');
            const r = lowerIsNullish(tr, lit === b.right ? b.left : b.right, fc);
            return op === SK.EqualsEqualsToken ? r : ir_1.E.not(r);
        }
        case SK.InKeyword: {
            const dt = tr.dictTyOf(b.right, fc);
            if (dt) {
                const [k, d] = tr.seq([() => tr.dictKey(b.left, fc), () => tr.lowerExpr(b.right, fc, dt)], fc);
                return ir_1.E.builtin(`(.dictHas ${(0, ty_1.showTy)(dt.t)})`, [d, k], [dt, ty_1.T.str], ty_1.T.bool);
            }
            // an unknown value (TypeScript may have narrowed it to `object`)
            const [k, d] = tr.seq([() => tr.dictKey(b.left, fc), () => tr.lowerExpr(b.right, fc)], fc);
            if (d.ty.k !== 'dyn')
                (0, diag_1.reject)(b, 'no-in', 'the `in` operator is only supported on dictionaries and unknown values');
            return ir_1.E.builtin('.dynHas', [d, k], [ty_1.T.dyn, ty_1.T.str], ty_1.T.bool);
        }
        case SK.InstanceOfKeyword: return lowerInstanceof(tr, b, fc);
    }
    const [l, r] = tr.seq([() => tr.lowerExpr(b.left, fc), () => tr.lowerExpr(b.right, fc)], fc);
    return tr.arith(op, l, r, b);
}
function lowerInstanceof(tr, b, fc) {
    const right = (0, stmts_1.skipParens)(b.right);
    if (!ts.isIdentifier(right))
        (0, diag_1.reject)(b, 'unsupported', '`instanceof` with a computed class');
    const rsym = tr.symAt(right);
    const lib = rsym && (0, core_1.isLibDecl)(tr.program, rsym.declarations?.[0]);
    let e = tr.lowerExpr(b.left, fc);
    if (lib && ['Error', 'TypeError', 'RangeError', 'SyntaxError', 'ReferenceError', 'EvalError', 'URIError'].includes(right.text)) {
        if (e.ty.k === 'dyn') {
            // an unknown value: is it an Error (then its name decides the subclass)?
            const c = ir_1.E.prim('(.dynCast .err)', [e], [ty_1.T.dyn], ty_1.T.opt(ty_1.T.err));
            const v = (0, ir_1.mkVar)('e', ty_1.T.err);
            return ir_1.E.caseOpt(c, ir_1.E.bool(false), v, right.text === 'Error' ? ir_1.E.bool(true) : ir_1.E.seq(ir_1.E.prim('.errName', [ir_1.E.var(v)], [ty_1.T.err], ty_1.T.str), (0, core_1.strLit)(right.text)));
        }
        if (e.ty.k !== 'err')
            (0, diag_1.reject)(b, 'unsupported', `instanceof ${right.text} on ${(0, ty_1.prettyTy)(e.ty)}`);
        if (right.text === 'Error')
            return tr.withValue(e, 'e', () => ir_1.E.bool(true));
        return ir_1.E.seq(ir_1.E.prim('.errName', [e], [ty_1.T.err], ty_1.T.str), (0, core_1.strLit)(right.text));
    }
    if (rsym && (rsym.flags & ts.SymbolFlags.Class) && !lib) {
        const target = tr.unfoldTy(e.ty);
        const isC = (t) => t.k === 'obj' && (t.c === right.text || t.c.startsWith(right.text + '<'));
        if (isC(target))
            return tr.withValue(e, 'o', () => ir_1.E.bool(true));
        if (target.k === 'union') {
            const ue = tr.unfoldE(e);
            return ir_1.E.caseU(ue, target.ts.map(m => ({ v: (0, ir_1.mkVar)('m', m), body: ir_1.E.bool(isC(m)) })));
        }
        if (target.k === 'opt') {
            const v = (0, ir_1.mkVar)('o', target.t);
            return ir_1.E.caseOpt(e, ir_1.E.bool(false), v, ir_1.E.bool(isC(target.t)));
        }
    }
    // a library or package class (Date, Map, a Firestore Timestamp, a typed array): decided on the
    // value's type, which is nominal for these (an unknown value: by its runtime type)
    if (rsym && (rsym.flags & ts.SymbolFlags.Value) && !tr.isProjectDecl(rsym.declarations?.[0])) {
        let ct;
        try {
            ct = tr.tyOf(tr.checker.getDeclaredTypeOfSymbol(rsym), fc, b);
        }
        catch {
            ct = undefined;
        }
        if (ct && ['ext', 'map', 'set', 'tarr', 'arr'].includes(ct.k)) {
            const cty = ct;
            const isC = (t) => t.k === cty.k && (t.k !== 'ext' || (cty.k === 'ext' && t.name === cty.name)) &&
                (t.k !== 'tarr' || (cty.k === 'tarr' && t.kind === cty.kind));
            const test = (x) => {
                const u = tr.unfoldE(x);
                if (u.ty.k === 'dyn') {
                    // (an unknown array is an Array whatever its element type)
                    if (cty.k === 'arr')
                        return ir_1.E.prim('.dynIsArray', [u], [ty_1.T.dyn], ty_1.T.bool);
                    const v = (0, ir_1.mkVar)('c', cty);
                    return ir_1.E.caseOpt(ir_1.E.prim(`(.dynCast ${(0, ty_1.showTy)(cty)})`, [u], [ty_1.T.dyn], ty_1.T.opt(cty)), ir_1.E.bool(false), v, ir_1.E.bool(true));
                }
                if (u.ty.k === 'opt') {
                    const v = (0, ir_1.mkVar)('o', u.ty.t);
                    return ir_1.E.caseOpt(u, ir_1.E.bool(false), v, test(ir_1.E.var(v)));
                }
                if (u.ty.k === 'union')
                    return ir_1.E.caseU(u, u.ty.ts.map(m => { const v = (0, ir_1.mkVar)('m', m); return { v, body: test(ir_1.E.var(v)) }; }));
                return tr.withValue(u, 'x', () => ir_1.E.bool(isC(u.ty)));
            };
            return test(e);
        }
    }
    (0, diag_1.reject)(b, 'instanceof', '`instanceof` is only supported for Error classes, classes of a union and library classes');
}
function isUndefinedNode(tr, e) {
    e = (0, stmts_1.skipParens)(e);
    if (ts.isIdentifier(e) && e.text === 'undefined') {
        const s = tr.symAt(e);
        return !s || !s.declarations?.length || (0, core_1.isLibDecl)(tr.program, s.declarations[0]);
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
function strIndex(tr, s, i) {
    // (a literal index that is an array index needs no test)
    if (i.k === 'lit' && typeof i.js === 'number' && Number.isInteger(i.js) && i.js >= 0)
        return ir_1.E.prim('.strAt', [s, i], [ty_1.T.str, ty_1.T.num], ty_1.T.opt(ty_1.T.str));
    return tr.withValue(s, 's', sv => tr.withValue(i, 'i', iv => ir_1.E.cond(ir_1.E.and(ir_1.E.prim('(.numPred .isInteger)', [iv], [ty_1.T.num], ty_1.T.bool), ir_1.E.prim('(.numCmp .ge)', [iv, (0, core_1.numLit)(0)], [ty_1.T.num, ty_1.T.num], ty_1.T.bool)), ir_1.E.prim('.strAt', [sv, iv], [ty_1.T.str, ty_1.T.num], ty_1.T.opt(ty_1.T.str)), ir_1.E.none(ty_1.T.str))));
}
function numberPred(tr, e0, name) {
    const e = tr.unfoldE(e0);
    const t = e.ty;
    const pred = (x) => ir_1.E.prim(`(.numPred .${name})`, [x], [ty_1.T.num], ty_1.T.bool);
    if (t.k === 'num')
        return pred(e);
    if (t.k === 'dyn') {
        const v = (0, ir_1.mkVar)('n', ty_1.T.num);
        return ir_1.E.caseOpt(ir_1.E.prim('(.dynCast .num)', [e], [ty_1.T.dyn], ty_1.T.opt(ty_1.T.num)), ir_1.E.bool(false), v, pred(ir_1.E.var(v)));
    }
    if (t.k === 'opt') {
        const v = (0, ir_1.mkVar)('x', t.t);
        return ir_1.E.caseOpt(e, ir_1.E.bool(false), v, numberPred(tr, ir_1.E.var(v), name));
    }
    if (t.k === 'union')
        return ir_1.E.caseU(e, t.ts.map(m => { const v = (0, ir_1.mkVar)('m', m); return { v, body: numberPred(tr, ir_1.E.var(v), name) }; }));
    return tr.withValue(e, 'x', () => ir_1.E.bool(false));
}
/** `===` with JavaScript semantics on the IR types. */
function lowerEq(tr, b, fc) {
    const L = (0, stmts_1.skipParens)(b.left), R = (0, stmts_1.skipParens)(b.right);
    // `x === x` (one variable on both sides) on values without identity in the IR (unknown values,
    // records, tuples): false exactly when x is NaN, whatever the value, while the IR's `===` cannot
    // decide it for records. (Types with `===` in the IR keep it.)
    if (ts.isIdentifier(L) && ts.isIdentifier(R) && L.text === R.text) {
        const s = tr.symAt(L);
        if (s && s === tr.symAt(R)) {
            const x = tr.lowerExpr(L, fc);
            if (!(0, ty_1.eqable)(tr.unfoldE(x).ty))
                return ir_1.E.not(numberPred(tr, x, 'isNaN'));
        }
    }
    // typeof x === "tag"
    for (const [x, y] of [[L, R], [R, L]]) {
        if (ts.isTypeOfExpression(x) && ts.isStringLiteral(y)) {
            const e = tr.lowerExpr(x.expression, fc);
            return typeofTest(tr, e, y.text, b);
        }
    }
    // comparisons with undefined / null
    const dynIs = (u, lit) => ir_1.E.prim('.dynEq', [u, ir_1.E.prim(`(.toDyn ${(0, ty_1.showTy)(lit)})`, [lit.k === 'null' ? ir_1.E.nullLit() : ir_1.E.undef()], [lit], ty_1.T.dyn)], [ty_1.T.dyn, ty_1.T.dyn], ty_1.T.bool);
    for (const [x, y] of [[L, R], [R, L]]) {
        if (isUndefinedNode(tr, y)) {
            const e = tr.unfoldE(tr.lowerExpr(x, fc));
            if (e.ty.k === 'dyn')
                return dynIs(e, ty_1.T.undef);
            if (e.ty.k === 'opt' && e.ty.t.k === 'dyn') {
                const v = (0, ir_1.mkVar)('x', e.ty.t);
                return ir_1.E.caseOpt(e, ir_1.E.bool(true), v, dynIs(ir_1.E.var(v), ty_1.T.undef));
            }
            if (e.ty.k === 'opt') {
                const v = (0, ir_1.mkVar)('x', e.ty.t);
                return ir_1.E.caseOpt(e, ir_1.E.bool(true), v, ir_1.E.bool(false));
            }
            if (e.ty.k === 'undef')
                return tr.withValue(e, 'u', () => ir_1.E.bool(true));
            return tr.withValue(e, 'u', () => ir_1.E.bool(false));
        }
        if (y.kind === SK.NullKeyword) {
            const e = tr.unfoldE(tr.lowerExpr(x, fc));
            const isNullU = (u) => {
                if (u.ty.k === 'dyn')
                    return dynIs(u, ty_1.T.null);
                if (u.ty.k === 'union')
                    return ir_1.E.caseU(u, u.ty.ts.map(m => ({ v: (0, ir_1.mkVar)('m', m), body: ir_1.E.bool(m.k === 'null') })));
                if (u.ty.k === 'null')
                    return tr.withValue(u, 'u', () => ir_1.E.bool(true));
                return tr.withValue(u, 'u', () => ir_1.E.bool(false));
            };
            if (e.ty.k === 'opt') {
                const v = (0, ir_1.mkVar)('x', e.ty.t);
                return ir_1.E.caseOpt(e, ir_1.E.bool(false), v, isNullU(tr.unfoldE(ir_1.E.var(v))));
            }
            return isNullU(e);
        }
    }
    const [l, r] = tr.seq([() => tr.lowerExpr(b.left, fc), () => tr.lowerExpr(b.right, fc)], fc);
    return tr.strictEqExprs(l, r, b, fc);
}
function typeofTest(tr, e0, tag, node) {
    if ((0, ir_1.isPoison)(e0))
        return ir_1.E.poison(ty_1.T.bool);
    const e = tr.unfoldE(e0);
    const t = e.ty;
    if (t.k === 'dyn')
        return ir_1.E.seq(ir_1.E.prim('.dynTypeof', [e], [ty_1.T.dyn], ty_1.T.str), (0, core_1.strLit)(tag));
    if (t.k === 'opt') {
        const v = (0, ir_1.mkVar)('x', t.t);
        return ir_1.E.caseOpt(e, ir_1.E.bool(tag === 'undefined'), v, typeofTest(tr, ir_1.E.var(v), tag, node));
    }
    if (t.k === 'union')
        return ir_1.E.caseU(e, t.ts.map(m => ({ v: (0, ir_1.mkVar)('m', m), body: ir_1.E.bool(tr.typeofTag(m) === tag) })));
    return tr.withValue(e, 'x', () => ir_1.E.bool(tr.typeofTag(t) === tag));
}
P.strictEqExprs = function (a0, b0, node, _fc) {
    if ((0, ir_1.isPoison)(a0) || (0, ir_1.isPoison)(b0))
        return ir_1.E.poison(ty_1.T.bool);
    if ((0, core_1.holdsTimer)(a0.ty) || (0, core_1.holdsTimer)(b0.ty))
        (0, diag_1.reject)(node, 'timer-handle', '=== on a Node timer handle other than with null or undefined');
    let a = a0, b = b0;
    if (a.ty.k === 'dyn' || b.ty.k === 'dyn') {
        // `===` with an unknown operand: on the runtime values
        const d = (x) => x.ty.k === 'dyn' ? x : ir_1.E.prim(`(.toDyn ${(0, ty_1.showTy)(x.ty)})`, [x], [x.ty], ty_1.T.dyn);
        return ir_1.E.prim('.dynEq', [d(a), d(b)], [ty_1.T.dyn, ty_1.T.dyn], ty_1.T.bool);
    }
    if (a.ty.k === 'named' || b.ty.k === 'named') {
        a = this.unfoldE(a);
        b = this.unfoldE(b);
    }
    if ((0, core_1.isLitUndef)(a) && b.ty.k === 'opt')
        [a, b] = [b, a];
    if ((0, core_1.isLitUndef)(b) && a.ty.k === 'opt') {
        const v = (0, ir_1.mkVar)('x', a.ty.t);
        // (an optional unknown holding an unknown undefined is undefined too)
        const inner = this.unfoldTy(a.ty.t).k === 'dyn'
            ? ir_1.E.prim('.dynEq', [this.unfoldE(ir_1.E.var(v)), ir_1.E.prim('(.toDyn .undef)', [ir_1.E.undef()], [ty_1.T.undef], ty_1.T.dyn)], [ty_1.T.dyn, ty_1.T.dyn], ty_1.T.bool)
            : ir_1.E.bool(false);
        return ir_1.E.caseOpt(a, ir_1.E.bool(true), v, inner);
    }
    if ((0, core_1.isLitUndef)(a) && !(0, core_1.isLitUndef)(b))
        [a, b] = [b, a];
    if ((0, core_1.isLitUndef)(b) && a.ty.k !== 'undef' && a.ty.k !== 'opt')
        return this.withValue(a, 'x', () => ir_1.E.bool(false));
    // a value with records or tuples in its type compared with a primitive value: no identity is
    // involved (it is equal only if it is that primitive)
    if (!(0, ty_1.eqable)(a.ty) && isPrimitiveTy(b.ty))
        return this.withValue(a, 'l', x => this.withValue(b, 'r', y => eqPrimitive(this, x, y, node, _fc)));
    if (!(0, ty_1.eqable)(b.ty) && isPrimitiveTy(a.ty))
        return this.withValue(a, 'l', x => this.withValue(b, 'r', y => eqPrimitive(this, y, x, node, _fc)));
    if (!(0, ty_1.tyEq)(a.ty, b.ty)) {
        // string literal vs enum, enum vs string, T vs T | undefined, member vs union, …
        if (isStringy(a.ty) && isStringy(b.ty) && !(a.ty.k === 'enum' && b.ty.k === 'enum')) {
            if (a.ty.k === 'enum' && b.k === 'lit') {
                const c = this.convert(b, a.ty, node, false, 0);
                if (c)
                    b = c;
            }
            else if (b.ty.k === 'enum' && a.k === 'lit') {
                const c = this.convert(a, b.ty, node, false, 0);
                if (c)
                    a = c;
            }
            if (!(0, ty_1.tyEq)(a.ty, b.ty)) {
                a = this.toStr(a, node);
                b = this.toStr(b, node);
            }
        }
        else {
            const ab = this.convert(a, b.ty, node, false, 0);
            if (ab)
                a = ab;
            else {
                const ba = this.convert(b, a.ty, node, false, 0);
                if (ba)
                    b = ba;
                else if (a.ty.k === 'enum' && b.ty.k === 'enum') {
                    a = this.toStr(a, node);
                    b = this.toStr(b, node);
                }
                else
                    (0, diag_1.reject)(node, 'unsupported', `=== between ${(0, ty_1.prettyTy)(a0.ty)} and ${(0, ty_1.prettyTy)(b0.ty)}`);
            }
        }
    }
    if (a.ty.k === 'fn')
        (0, diag_1.reject)(node, 'no-record-eq', `=== on functions (closures have no identity in StrictTS)`);
    if ((0, ty_1.tyEq)(a.ty, ty_1.REGEXP_TY))
        (0, diag_1.reject)(node, 'no-regexp', '=== on regular expressions (they are compared by identity; regex values have none)');
    if (!(0, ty_1.eqable)(a.ty))
        (0, diag_1.reject)(node, 'no-record-eq', `=== on ${(0, ty_1.prettyTy)(a.ty)} (records and tuples have no identity)`);
    return ir_1.E.seq(a, b);
};
function isPrimitiveTy(t) {
    return t.k === 'str' || t.k === 'enum' || t.k === 'num' || t.k === 'bool' || t.k === 'bigint' || t.k === 'null' || t.k === 'undef';
}
/** `x === p` for a primitive `p`, by the members of `x`'s type: members of another type (records,
 * tuples, other primitives) are never equal to it. */
function eqPrimitive(tr, x0, p, node, fc) {
    const x = tr.unfoldE(x0);
    const t = x.ty;
    if (t.k === 'opt') {
        const v = (0, ir_1.mkVar)('x', t.t);
        return ir_1.E.caseOpt(x, ir_1.E.bool(p.ty.k === 'undef'), v, eqPrimitive(tr, ir_1.E.var(v), p, node, fc));
    }
    if (t.k === 'union')
        return ir_1.E.caseU(x, t.ts.map(m => { const v = (0, ir_1.mkVar)('m', m); return { v, body: eqPrimitive(tr, ir_1.E.var(v), p, node, fc) }; }));
    if (t.k === 'dyn' || (0, ty_1.tyEq)(t, p.ty) || (isStringy(t) && isStringy(p.ty)))
        return tr.strictEqExprs(x, p, node, fc);
    return tr.withValue(x, 'x', () => ir_1.E.bool(false));
}
function lowerValueLogical(tr, b, fc, exp) {
    const target = exp ?? tr.tyAt(b, fc);
    const a0 = tr.lowerExpr(b.left, fc);
    if ((0, ir_1.isPoison)(a0)) {
        tr.lowerExpr(b.right, fc);
        return tr.derivedPoison(b, fc, exp);
    }
    const a = tr.nullishToOpt(a0, b.left);
    if (a.ty.k !== 'opt' || !(0, ty_1.isObjectLike)(tr.unfoldTy(a.ty.t))) {
        // general truthiness: `a || d` is a if a is truthy, else d; `a && e` the other way round
        const isAnd0 = b.operatorToken.kind === SK.AmpersandAmpersandToken;
        const x = (0, ir_1.mkVar)('l', a0.ty);
        const [rhs0, pre0] = tr.isolate(fc, () => tr.lowerExpr(b.right, fc, target));
        const keep = tr.adapt(ir_1.E.var(x), target, b.left);
        if (!pre0.length) {
            return ir_1.E.letE(x, a0, ir_1.E.cond(tr.truthy(ir_1.E.var(x), b.left), isAnd0 ? rhs0 : keep, isAnd0 ? keep : rhs0));
        }
        const xv = tr.bindTemp(a0, fc, 'l');
        const keep2 = tr.adapt(ir_1.E.var(xv), target, b.left);
        const r0 = tr.mutTemp(target, fc);
        const evalR = [...pre0, r0.set(rhs0)];
        const keepR = [r0.set(keep2)];
        fc.pre.push((0, ir_1.stmtItem)(ir_1.S.ite(tr.truthy(ir_1.E.var(xv), b.left), isAnd0 ? evalR : keepR, isAnd0 ? keepR : evalR)));
        return r0.get();
    }
    const v = (0, ir_1.mkVar)('o', a.ty.t);
    const isAnd = b.operatorToken.kind === SK.AmpersandAmpersandToken;
    const [rhs, pre] = tr.isolate(fc, () => {
        if (!isAnd)
            return tr.lowerExpr(b.right, fc, target);
        return tr.lowerExpr(b.right, fc, target);
    });
    const dflt = isAnd ? (target.k === 'opt' ? ir_1.E.none(target.t) : null) : rhs;
    if (!dflt)
        (0, diag_1.reject)(b, 'unsupported', '`&&` whose result cannot be undefined');
    const someV = isAnd ? rhs : tr.coerce(ir_1.E.var(v), target, b);
    if (!pre.length)
        return ir_1.E.caseOpt(a, isAnd ? dflt : rhs, v, someV);
    const r = tr.mutTemp(target, fc);
    if (isAnd)
        fc.pre.push((0, ir_1.stmtItem)({ k: 'caseOptS', e: a, none: [r.set(dflt)], v, some: [...pre, r.set(rhs)] }));
    else
        fc.pre.push((0, ir_1.stmtItem)({ k: 'caseOptS', e: a, none: [...pre, r.set(rhs)], v, some: [r.set(someV)] }));
    return r.get();
}
/** `null`, the global `undefined`, or `void <number>`. */
function isNullishLit(tr, e0) {
    const e = (0, stmts_1.skipParens)(e0);
    if (e.kind === SK.NullKeyword)
        return true;
    if (ts.isIdentifier(e) && e.text === 'undefined') {
        const s = tr.checker.getSymbolAtLocation(e);
        return !s || !tr.facts(s);
    }
    return ts.isVoidExpression(e) && ts.isNumericLiteral((0, stmts_1.skipParens)(e.expression));
}
/** `x == null` (the loose comparison with null or undefined): true exactly when x is null or
 * undefined (ECMA-262 IsLooselyEqual; the IR has no `document.all`). The operand is evaluated once. */
function lowerIsNullish(tr, x, fc) {
    const e0 = tr.lowerExpr(x, fc);
    if ((0, ir_1.isPoison)(e0))
        return e0;
    const e = e0.ty.k === 'named' ? tr.unfoldE(e0) : e0;
    if (e.ty.k === 'dyn') {
        const v = tr.bindTemp(e, fc, 'n');
        const dynLit = (t) => ir_1.E.prim(`(.toDyn ${(0, ty_1.showTy)(t)})`, [t.k === 'null' ? ir_1.E.nullLit() : ir_1.E.undef()], [t], ty_1.T.dyn);
        return ir_1.E.or(ir_1.E.prim('.dynEq', [ir_1.E.var(v), dynLit(ty_1.T.undef)], [ty_1.T.dyn, ty_1.T.dyn], ty_1.T.bool), ir_1.E.prim('.dynEq', [ir_1.E.var(v), dynLit(ty_1.T.null)], [ty_1.T.dyn, ty_1.T.dyn], ty_1.T.bool));
    }
    if (e.ty.k === 'null' || e.ty.k === 'undef') {
        tr.bindTemp(e, fc, 'n');
        return ir_1.E.bool(true);
    }
    const a = tr.nullishToOpt(e, x);
    if (a.ty.k === 'opt')
        return ir_1.E.caseOpt(a, ir_1.E.bool(true), (0, ir_1.mkVar)('n', a.ty.t), ir_1.E.bool(false));
    // never null or undefined: the operand still runs
    tr.bindTemp(a, fc, 'n');
    return ir_1.E.bool(false);
}
function lowerNullish(tr, b, fc, exp) {
    const target = exp ?? tr.tyAt(b, fc);
    // an array expected for the whole: the left side is expected as an optional array (e.g. a global
    // regex match, whose lib type is a match object, answers an array of strings there)
    const a = tr.nullishToOpt(tr.lowerExpr(b.left, fc, exp && exp.k === 'arr' ? ty_1.T.opt(exp) : undefined), b.left);
    if (a.ty.k !== 'opt')
        return tr.coerce(a, target, b);
    const v = (0, ir_1.mkVar)('x', a.ty.t);
    const someV = tr.coerce(ir_1.E.var(v), target, b);
    const [d, pre] = tr.isolate(fc, () => tr.lowerExpr(b.right, fc, target));
    if (!pre.length)
        return ir_1.E.caseOpt(a, d, v, someV);
    const r = tr.mutTemp(target, fc);
    fc.pre.push((0, ir_1.stmtItem)({ k: 'caseOptS', e: a, none: [...pre, r.set(d)], v, some: [r.set(someV)] }));
    return r.get();
}
function lowerConditional(tr, n, fc, exp) {
    const target = exp ?? tr.tyAt(n, fc);
    const test = tr.narrowTest(n.condition, fc);
    if (test && test.kind === 'opt' && tr.isRebindable(test.sym, fc, [n.whenTrue, n.whenFalse])) {
        const inner = test.scrut.ty.t;
        const v = (0, ir_1.mkVar)(test.sym.name, inner);
        const [someE, preS] = tr.isolate(fc, () => {
            fc.push();
            fc.bind(test.sym, { k: 'var', v });
            try {
                return tr.lowerExpr(test.thenSome ? n.whenTrue : n.whenFalse, fc, target);
            }
            finally {
                fc.pop();
            }
        });
        const [noneE, preN] = tr.isolate(fc, () => tr.lowerExpr(test.thenSome ? n.whenFalse : n.whenTrue, fc, target));
        if (!preS.length && !preN.length)
            return ir_1.E.caseOpt(test.scrut, noneE, v, someE);
        const r = tr.mutTemp(target, fc);
        fc.pre.push((0, ir_1.stmtItem)({ k: 'caseOptS', e: test.scrut, none: [...preN, r.set(noneE)], v, some: [...preS, r.set(someE)] }));
        return r.get();
    }
    const c = tr.lowerCond(n.condition, fc);
    const [a, preA] = tr.isolate(fc, () => tr.lowerExpr(n.whenTrue, fc, target));
    const [bb, preB] = tr.isolate(fc, () => tr.lowerExpr(n.whenFalse, fc, target));
    if (!preA.length && !preB.length)
        return ir_1.E.cond(c, a, bb);
    const r = tr.mutTemp(target, fc);
    fc.pre.push((0, ir_1.stmtItem)(ir_1.S.ite(c, [...preA, r.set(a)], [...preB, r.set(bb)])));
    return r.get();
}
function lowerAssertion(tr, n, fc) {
    const inner = n.expression;
    if (ts.isAsExpression(n) && ts.isTypeReferenceNode(n.type) && n.type.typeName.getText() === 'const') {
        return tr.lowerExpr(inner, fc, tr.tyAt(n, fc));
    }
    const target = tr.checker.getTypeAtLocation(n);
    const src = tr.checker.getTypeAtLocation(inner);
    // catch variables (unknown) used as Error
    const innerS = (0, stmts_1.skipParens)(inner);
    if (ts.isIdentifier(innerS)) {
        const sym = tr.symAt(innerS);
        const b = sym && tr.lookup(sym, fc);
        if (b && b.k === 'var' && b.errVar) {
            const tt = tr.tyOf(target, fc, n);
            if (tt.k !== 'err')
                (0, diag_1.reject)(n, 'as-downcast', 'a catch variable can only be used as an Error');
            return ir_1.E.var(b.v);
        }
    }
    // the value of an external call (a new object: nothing else in the program holds it) cast to a
    // record type compared by identity is a new cell (identity.ts)
    const castTo = (tt) => {
        if (tt.k !== 'box' || tt.t.k !== 'record' || !ts.isCallExpression(innerS) || tr.classifyCall(innerS, fc).kind !== 'external')
            return tr.lowerExpr(inner, fc, tt);
        const r = tr.lowerExpr(inner, fc, tt.t);
        return ir_1.E.builtin(`(.boxNew ${(0, ty_1.showTy)(tt.t)})`, [r], [tt.t], tt);
    };
    // a cast of an unknown value (also as narrowed to `object`) is a checked cast
    const unknownish = (x) => !!(x.flags & (ts.TypeFlags.Unknown | ts.TypeFlags.NonPrimitive));
    if (unknownish(src) || (src.isIntersection() && src.types.some(unknownish)))
        return castTo(tr.tyOf(target, fc, n));
    // a dictionary of unknown values (DocumentData, a parsed JSON object) cast to a record type
    if (!tr.strict) {
        let st;
        try {
            st = tr.unfoldTy(tr.tyOf(src, fc, n));
        }
        catch {
            st = undefined;
        }
        const dd = (t) => !!t && t.k === 'dict' && t.t.k === 'dyn';
        if (st && (dd(st) || (st.k === 'opt' && dd(st.t))))
            return castTo(tr.tyOf(target, fc, n));
    }
    if (!ts.isSatisfiesExpression(n) && !tr.checker.isTypeAssignableTo(src, target)) {
        // a downcast to a narrower type (`x as string` for `string | undefined`, a string to a
        // string-literal union, a union to one member): a checked narrowing, a panic on a mismatch
        // (not in the original subset, `--strict`)
        if (!tr.strict && tr.checker.isTypeAssignableTo(target, src)) {
            const tt = tr.tyOf(target, fc, n);
            const e = tr.lowerExpr(inner, fc);
            const c = (0, ir_1.isPoison)(e) ? ir_1.E.poison(tt) : tr.convert(e, tt, n, true, 0);
            if (c)
                return c;
        }
        (0, diag_1.reject)(n, 'as-downcast', `\`as\` downcast from ${tr.checker.typeToString(src)} to ${tr.checker.typeToString(target)}`);
    }
    return castTo(tr.tyOf(target, fc, n));
}
// ---------------------------------------------------------------------------------------
// conditions
P.lowerCond = function (n0, fc) {
    const n = (0, stmts_1.skipParens)(n0);
    if (ts.isPrefixUnaryExpression(n) && n.operator === SK.ExclamationToken)
        return ir_1.E.not(this.lowerCond(n.operand, fc));
    if (ts.isBinaryExpression(n) && (n.operatorToken.kind === SK.AmpersandAmpersandToken || n.operatorToken.kind === SK.BarBarToken)) {
        const isAnd = n.operatorToken.kind === SK.AmpersandAmpersandToken;
        // `x !== undefined && P(x)` / `x === undefined || P(x)`: rebind x in P
        const test = this.narrowTest(n.left, fc);
        if (test && test.kind === 'opt' && test.thenSome === isAnd && this.isRebindable(test.sym, fc, n.right)) {
            const inner = test.scrut.ty.t;
            const v = (0, ir_1.mkVar)(test.sym.name, inner);
            const [rhs, pre] = this.isolate(fc, () => {
                fc.push();
                fc.bind(test.sym, { k: 'var', v });
                try {
                    return this.lowerCond(n.right, fc);
                }
                finally {
                    fc.pop();
                }
            });
            if (!pre.length)
                return ir_1.E.caseOpt(test.scrut, ir_1.E.bool(!isAnd), v, rhs);
            const r = (0, ir_1.mkVar)('c', ty_1.T.bool, true);
            fc.pre.push((0, ir_1.declItem)(r, ir_1.E.bool(!isAnd)));
            fc.pre.push((0, ir_1.stmtItem)({ k: 'caseOptS', e: test.scrut, none: [], v, some: [...pre, (0, ir_1.stmtItem)(ir_1.S.assign(r, rhs))] }));
            return ir_1.E.var(r);
        }
        const l = this.lowerCond(n.left, fc);
        const [rhs, pre] = this.isolate(fc, () => this.lowerCond(n.right, fc));
        if (!pre.length)
            return isAnd ? ir_1.E.and(l, rhs) : ir_1.E.or(l, rhs);
        const r = (0, ir_1.mkVar)('c', ty_1.T.bool, true);
        fc.pre.push((0, ir_1.declItem)(r, ir_1.E.bool(!isAnd)));
        const assign = [...pre, (0, ir_1.stmtItem)(ir_1.S.assign(r, rhs))];
        fc.pre.push((0, ir_1.stmtItem)(isAnd ? ir_1.S.ite(l, assign, []) : ir_1.S.ite(l, [], assign)));
        return ir_1.E.var(r);
    }
    const t = this.checker.getTypeAtLocation(n);
    if (isBoolTs(t)) {
        // (a tested element read is optional: a missing element is falsy)
        const e = this.lowerExpr(n, fc, (ts.isElementAccessExpression(n) || ts.isPropertyAccessExpression(n)) ? undefined : ty_1.T.bool);
        return this.unfoldE(e).ty.k === 'bool' ? e : this.truthy(e, n);
    }
    return this.truthy(this.lowerExpr(n, fc), n);
};
P.truthy = function (e0, node) {
    // JavaScript truthiness as explicit tests: "" / 0 / -0 / NaN / 0n / undefined / null are
    // falsy; objects, arrays and functions are truthy (a null test for optional ones)
    if ((0, ir_1.isPoison)(e0))
        return ir_1.E.poison(ty_1.T.bool);
    const e = this.unfoldE(e0);
    const t = e.ty;
    switch (t.k) {
        case 'bool': return e;
        case 'str': return ir_1.E.not(ir_1.E.seq(e, (0, core_1.strLit)('')));
        case 'enum': return t.cases.includes('') ? ir_1.E.not(ir_1.E.seq(this.toStr(e, node), (0, core_1.strLit)(''))) : this.withValue(e, 'k', () => ir_1.E.bool(true));
        case 'num': return this.withValue(e, 'n', x => ir_1.E.and(ir_1.E.not(ir_1.E.seq(x, (0, core_1.numLit)(0))), ir_1.E.seq(x, x)));
        case 'bigint': return ir_1.E.not(ir_1.E.seq(e, (0, core_1.bigLit)(0n)));
        case 'dyn': return ir_1.E.prim('.dynTruthy', [e], [ty_1.T.dyn], ty_1.T.bool);
        case 'undef':
        case 'null': return this.withValue(e, 'u', () => ir_1.E.bool(false));
        case 'opt': {
            const v = (0, ir_1.mkVar)('x', t.t);
            return ir_1.E.caseOpt(e, ir_1.E.bool(false), v, this.truthy(ir_1.E.var(v), node));
        }
        case 'union': return ir_1.E.caseU(e, t.ts.map(m => { const v = (0, ir_1.mkVar)('m', m); return { v, body: this.truthy(ir_1.E.var(v), node) }; }));
    }
    if ((0, ty_1.isObjectLike)(t))
        return this.withValue(e, 'o', () => ir_1.E.bool(true));
    (0, diag_1.reject)(node, 'truthiness', `condition of type ${(0, ty_1.prettyTy)(t)}`);
};
// ---------------------------------------------------------------------------------------
// assignment
P.assignTo = function (b, value0, needValue, fc, node) {
    let value = value0;
    let result = null;
    if (needValue) {
        const v = this.bindTemp(value, fc, 'av');
        value = ir_1.E.var(v);
        result = ir_1.E.var(v);
    }
    switch (b.k) {
        case 'poison':
            break;
        case 'var':
            if (b.errVar)
                (0, diag_1.reject)(node, 'unsupported', 'assignment to a catch variable');
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.assign(b.v, value)));
            break;
        case 'box':
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(ir_1.E.builtin(`(.boxSet ${(0, ty_1.showTy)(b.t)})`, [ir_1.E.var(b.v), value], [ty_1.T.box(b.t), b.t], ty_1.T.undef))));
            break;
        case 'boxOpt':
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(ir_1.E.builtin(`(.boxSet ${(0, ty_1.showTy)(ty_1.T.opt(b.t))})`, [ir_1.E.var(b.v), ir_1.E.some(value)], [ty_1.T.box(ty_1.T.opt(b.t)), ty_1.T.opt(b.t)], ty_1.T.undef))));
            break;
        case 'optInit':
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.assign(b.v, ir_1.E.some(value))));
            break;
        case 'global':
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.gset(b.g, value)));
            break;
        case 'lifted':
            (0, diag_1.reject)(node, 'unsupported', 'assignment to a function');
    }
    return result;
};
function compoundOp(op) { return COMPOUND[op]; }
P.lowerAssign = function (b, fc, needValue, forceEq = false) {
    const op = forceEq ? SK.EqualsToken : b.operatorToken.kind;
    const L = (0, stmts_1.skipParens)(b.left);
    if (op === SK.AmpersandAmpersandEqualsToken || op === SK.BarBarEqualsToken || op === SK.QuestionQuestionEqualsToken) {
        return lowerLogicalAssign(this, b, fc, needValue);
    }
    if (ts.isArrayLiteralExpression(L)) {
        if (op !== SK.EqualsToken)
            (0, diag_1.reject)(b, 'unsupported-syntax', 'compound destructuring assignment');
        return lowerDestructAssign(this, L, b.right, fc, needValue, b);
    }
    if (ts.isObjectLiteralExpression(L))
        (0, diag_1.reject)(b, 'unsupported-syntax', 'object destructuring assignment');
    const cop = op === SK.EqualsToken ? undefined : compoundOp(op);
    if (op !== SK.EqualsToken && cop === undefined)
        (0, diag_1.reject)(b, 'unsupported-syntax', `assignment operator ${ts.tokenToString(op)}`);
    if (ts.isIdentifier(L)) {
        const sym = this.symAt(L);
        const bd = sym && this.lookup(sym, fc);
        if (!bd)
            (0, diag_1.reject)(L, 'unsupported', `assignment to ${L.text}`);
        if (bd.k === 'poison') {
            this.lowerExpr(b.right, fc);
            return needValue ? ir_1.E.poison(bd.ty) : null;
        }
        const ty = this.bindingTy(bd);
        let value;
        if (cop === undefined)
            value = this.lowerExpr(b.right, fc, ty);
        else {
            const [cur, r] = this.seq([() => this.readBinding(bd, L), () => this.lowerExpr(b.right, fc)], fc);
            value = this.coerce(this.arith(cop, cur, r, b), ty, b);
        }
        return this.assignTo(bd, value, needValue, fc, b);
    }
    if (ts.isPropertyAccessExpression(L)) {
        const st = this.staticFieldGlobal(L);
        if (st) {
            const bd = { k: 'global', g: st };
            let value;
            if (cop === undefined)
                value = this.lowerExpr(b.right, fc, st.ty);
            else {
                const [cur, r] = this.seq([() => ir_1.E.gget(st), () => this.lowerExpr(b.right, fc)], fc);
                value = this.coerce(this.arith(cop, cur, r, b), st.ty, b);
            }
            return this.assignTo(bd, value, needValue, fc, b);
        }
        const name = L.name.text;
        const objE = this.lowerExpr(L.expression, fc);
        const o0 = this.unfoldE(objE);
        if ((0, ir_1.isPoison)(o0)) {
            this.lowerExpr(b.right, fc);
            return needValue ? this.derivedPoison(b, fc) : null;
        }
        if (o0.ty.k === 'dict')
            return this.dictAssign(o0, () => (0, core_1.strLit)(name), b, cop, needValue, fc);
        if (o0.ty.k === 'dyn')
            (0, diag_1.reject)(b, 'any-op', `assignment to property ${name} of a value of type any/unknown`);
        if (o0.ty.k === 'ext' && cop === undefined) {
            // a property write on an external object: an external call
            const pt = this.tyAt(L, fc);
            const [o, v] = this.seq([() => o0, () => this.lowerExpr(b.right, fc, pt)], fc);
            const vv = needValue ? ir_1.E.var(this.bindTemp(v, fc, 'xv')) : v;
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(ir_1.E.extern(`${o0.ty.name}.set:${name}`, [o, vv], ty_1.T.undef))));
            return needValue ? vv : null;
        }
        if (o0.ty.k === 'arr' && name === 'length') {
            const at = o0.ty;
            const [o, n] = this.seq([() => o0, () => this.lowerExpr(b.right, fc, ty_1.T.num)], fc);
            const nv = needValue ? ir_1.E.var(this.bindTemp(n, fc, 'len')) : n;
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(ir_1.E.builtin(`(.arrSetLength ${(0, ty_1.showTy)(at.t)})`, [o, nv], [at, ty_1.T.num], ty_1.T.undef))));
            return needValue ? nv : null;
        }
        if ((0, ty_1.tyEq)(o0.ty, ty_1.REGEXP_TY))
            (0, diag_1.reject)(b, 'no-regexp', `assignment to ${name} of a regular expression (its matching state is not modelled)`);
        if (o0.ty.k === 'record')
            (0, diag_1.reject)(b, 'record-mutation', `assignment to field ${name} of an immutable record type (the value flows through a record type here)`);
        if (o0.ty.k !== 'obj')
            (0, diag_1.reject)(b, 'unsupported', `assignment to property ${name} of ${(0, ty_1.prettyTy)(o0.ty)}`);
        const c = o0.ty.c;
        const info = this.classOfObj(c);
        const idx = info?.fieldIdx.get(name);
        if (!info || idx === undefined) {
            const ci = this.types.classes.get(c);
            const setter = ci && this.classMember(ci, name, 'setter', b);
            if (setter && cop === undefined) {
                const pt = setter.params[1].ty;
                const [o, v] = this.seq([() => o0, () => this.lowerExpr(b.right, fc, pt)], fc);
                const vv = needValue ? ir_1.E.var(this.bindTemp(v, fc, 'sv')) : v;
                fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(ir_1.E.call(setter, [o, vv]))));
                return needValue ? vv : null;
            }
            (0, diag_1.reject)(b, 'unsupported', `no field ${name} on ${c}`);
        }
        const fty = info.fields[idx].ty;
        if (cop === undefined) {
            const [o, v] = this.seq([() => o0, () => this.lowerExpr(b.right, fc, fty)], fc);
            const vv = needValue ? ir_1.E.var(this.bindTemp(v, fc, 'fv')) : v;
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.setField(o, c, idx, fty, vv)));
            return needValue ? vv : null;
        }
        const o = this.spill(o0, fc, 'o');
        const [cur, r] = this.seq([() => ir_1.E.getField(o, c, idx, fty), () => this.lowerExpr(b.right, fc)], fc);
        let value = this.coerce(this.arith(cop, cur, r, b), fty, b);
        if (needValue)
            value = ir_1.E.var(this.bindTemp(value, fc, 'fv'));
        fc.pre.push((0, ir_1.stmtItem)(ir_1.S.setField(o, c, idx, fty, value)));
        return needValue ? value : null;
    }
    if (ts.isElementAccessExpression(L)) {
        const base = this.unfoldE(this.lowerExpr(L.expression, fc));
        if ((0, ir_1.isPoison)(base)) {
            this.lowerExpr(L.argumentExpression, fc);
            this.lowerExpr(b.right, fc);
            return needValue ? this.derivedPoison(b, fc) : null;
        }
        if (base.ty.k === 'dict')
            return this.dictAssign(base, () => this.dictKey(L.argumentExpression, fc), b, cop, needValue, fc);
        if (base.ty.k === 'dyn')
            (0, diag_1.reject)(b, 'any-op', 'element assignment on a value of type any/unknown');
        if (base.ty.k !== 'arr' && base.ty.k !== 'tarr') {
            if (base.ty.k === 'record' || base.ty.k === 'obj')
                (0, diag_1.reject)(L, 'computed-key', `assignment to a computed property of ${(0, ty_1.prettyTy)(base.ty)}`);
            (0, diag_1.reject)(b, 'unsupported', `element assignment on ${(0, ty_1.prettyTy)(base.ty)}`);
        }
        const [a0, i0] = this.seq([() => base, () => this.lowerExpr(L.argumentExpression, fc, ty_1.T.num)], fc);
        const at = a0.ty;
        if (at.k !== 'arr' && at.k !== 'tarr')
            (0, diag_1.reject)(b, 'unsupported', `element assignment on ${(0, ty_1.prettyTy)(at)}`);
        const elemTy = at.k === 'arr' ? at.t : (at.kind === 'bi64' || at.kind === 'bu64' ? ty_1.T.bigint : ty_1.T.num);
        const setOp = at.k === 'arr' ? `(.arrSet ${(0, ty_1.showTy)(at.t)})` : `(.taSet .${at.kind})`;
        const getOp = at.k === 'arr' ? `(.arrGet ${(0, ty_1.showTy)(at.t)})` : `(.taGet .${at.kind})`;
        if (cop === undefined) {
            const [a, i, v] = this.seq([() => a0, () => i0, () => this.lowerExpr(b.right, fc, elemTy)], fc);
            const vv = needValue ? ir_1.E.var(this.bindTemp(v, fc, 'ev')) : v;
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(ir_1.E.builtin(setOp, [a, i, vv], [at, ty_1.T.num, elemTy], ty_1.T.undef))));
            return needValue ? vv : null;
        }
        const a = this.spill(a0, fc, 'a'), i = this.spill(i0, fc, 'i');
        const [cur, r] = this.seq([() => ir_1.E.builtin(getOp, [a, i], [at, ty_1.T.num], elemTy), () => this.lowerExpr(b.right, fc)], fc);
        let value = this.coerce(this.arith(cop, cur, r, b), elemTy, b);
        if (needValue)
            value = ir_1.E.var(this.bindTemp(value, fc, 'ev'));
        fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(ir_1.E.builtin(setOp, [a, i, value], [at, ty_1.T.num, elemTy], ty_1.T.undef))));
        return needValue ? value : null;
    }
    (0, diag_1.reject)(b, 'unsupported-syntax', 'assignment target');
};
function lowerLogicalAssign(tr, b, fc, needValue) {
    const op = b.operatorToken.kind;
    const L = (0, stmts_1.skipParens)(b.left);
    if (needValue && !ts.isIdentifier(L))
        (0, diag_1.reject)(b, 'unsupported', 'logical assignment to a property used as a value');
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
                () => ts.isPropertyAccessExpression(L) ? (0, core_1.strLit)(L.name.text) : tr.dictKey(L.argumentExpression, fc)], fc);
            const d = tr.spill(d1, fc, 'd'), k = tr.spill(k1, fc, 'k');
            const cur = tr.dictGetOpt(d, k);
            let c;
            if (op === SK.QuestionQuestionEqualsToken) {
                const v = (0, ir_1.mkVar)('x', cur.ty.t);
                c = ir_1.E.caseOpt(cur, ir_1.E.bool(true), v, ir_1.E.bool(false));
            }
            else
                c = op === SK.BarBarEqualsToken ? ir_1.E.not(tr.truthy(cur, L)) : tr.truthy(cur, L);
            const body = [];
            const saved = fc.pre;
            fc.pre = body;
            try {
                const v = tr.lowerExpr(b.right, fc, dt.t);
                body.push((0, ir_1.stmtItem)(tr.dictSetStmt(d, k, v)));
            }
            finally {
                fc.pre = saved;
            }
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.ite(c, body, [])));
            return null;
        }
    }
    if (!ts.isIdentifier(L) && !ts.isPropertyAccessExpression(L))
        (0, diag_1.reject)(b, 'unsupported', 'logical assignment target');
    // x ??= e  ==>  if (x === undefined) x = e   (similarly ||=, &&= on booleans)
    // (the stored value is tested, not TypeScript's narrowed view of it)
    let cur;
    if (ts.isIdentifier(L)) {
        const sym = tr.symAt(L);
        const bd = sym && tr.lookup(sym, fc);
        if (!bd)
            (0, diag_1.reject)(L, 'unsupported', `assignment to ${L.text}`);
        cur = bd.k === 'optInit' ? ir_1.E.var(bd.v) : tr.readBinding(bd, L);
    }
    else {
        const o = tr.unfoldE(tr.lowerExpr(L.expression, fc));
        cur = o.ty.k === 'obj' ? tr.readField(o, L.name.text, L) : tr.memberOf(o, L.name.text, L, fc);
    }
    let test;
    if (op === SK.QuestionQuestionEqualsToken) {
        const o = tr.nullishToOpt(cur, L);
        if (o.ty.k !== 'opt')
            return null;
        const v = (0, ir_1.mkVar)('x', o.ty.t);
        test = ir_1.E.caseOpt(o, ir_1.E.bool(true), v, ir_1.E.bool(false));
    }
    else {
        const c = tr.truthy(cur, L);
        test = op === SK.BarBarEqualsToken ? ir_1.E.not(c) : c;
    }
    const body = [];
    const saved = fc.pre;
    fc.pre = body;
    try {
        tr.lowerAssign(b, fc, false, true);
    }
    finally {
        fc.pre = saved;
    }
    fc.pre.push((0, ir_1.stmtItem)(ir_1.S.ite(test, body, [])));
    return null;
}
function lowerDestructAssign(tr, L, R, fc, needValue, node) {
    if (needValue)
        (0, diag_1.reject)(node, 'unsupported', 'destructuring assignment used as a value');
    const rhs = tr.unfoldE(tr.lowerExpr(R, fc));
    const v = tr.bindTemp(rhs, fc, 'd');
    // ECMA-262 order: for each element, the target reference is evaluated, then the next
    // value is taken and stored
    L.elements.forEach((el, i) => {
        if (ts.isOmittedExpression(el))
            return;
        if (ts.isSpreadElement(el))
            (0, diag_1.reject)(el, 'unsupported-syntax', 'rest element in a destructuring assignment');
        const t = rhs.ty;
        const val = () => {
            if (t.k === 'tup')
                return ir_1.E.getTup(ir_1.E.var(v), i);
            if (t.k === 'arr')
                return ir_1.E.builtin(`(.arrGet ${(0, ty_1.showTy)(t.t)})`, [ir_1.E.var(v), (0, core_1.numLit)(i)], [t, ty_1.T.num], t.t);
            (0, diag_1.reject)(R, 'unsupported', `destructuring assignment from ${(0, ty_1.prettyTy)(t)}`);
        };
        tr.assignNode((0, stmts_1.skipParens)(el), val, fc, el);
    });
    return null;
}
P.assignNode = function (target, value, fc, node) {
    if (ts.isIdentifier(target)) {
        const sym = this.symAt(target);
        const bd = sym && this.lookup(sym, fc);
        if (!bd)
            (0, diag_1.reject)(target, 'unsupported', `assignment to ${target.text}`);
        this.assignTo(bd, this.coerce(value(), this.bindingTy(bd), node), false, fc, node);
        return;
    }
    if (ts.isPropertyAccessExpression(target)) {
        const st = this.staticFieldGlobal(target);
        if (st) {
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.gset(st, this.coerce(value(), st.ty, node))));
            return;
        }
        const o = this.unfoldE(this.lowerExpr(target.expression, fc));
        if (o.ty.k !== 'obj')
            (0, diag_1.reject)(node, o.ty.k === 'record' ? 'record-mutation' : 'unsupported', `assignment to property ${target.name.text} of ${(0, ty_1.prettyTy)(o.ty)}`);
        const c = o.ty.c;
        const info = this.classOfObj(c);
        const idx = info?.fieldIdx.get(target.name.text);
        if (!info || idx === undefined)
            (0, diag_1.reject)(node, 'unsupported', `no field ${target.name.text} on ${c}`);
        const fty = info.fields[idx].ty;
        const [ob, vv] = this.seq([() => o, () => this.coerce(value(), fty, node)], fc);
        fc.pre.push((0, ir_1.stmtItem)(ir_1.S.setField(ob, c, idx, fty, vv)));
        return;
    }
    if (ts.isElementAccessExpression(target)) {
        const [a0, i0] = this.seq([() => this.unfoldE(this.lowerExpr(target.expression, fc)), () => this.lowerExpr(target.argumentExpression, fc, ty_1.T.num)], fc);
        if (a0.ty.k !== 'arr')
            (0, diag_1.reject)(node, 'unsupported', `element assignment on ${(0, ty_1.prettyTy)(a0.ty)}`);
        const at = a0.ty;
        const [a, i, vv] = this.seq([() => a0, () => i0, () => this.coerce(value(), at.t, node)], fc);
        fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(ir_1.E.builtin(`(.arrSet ${(0, ty_1.showTy)(at.t)})`, [a, i, vv], [at, ty_1.T.num, at.t], ty_1.T.undef))));
        return;
    }
    (0, diag_1.reject)(node, 'unsupported-syntax', 'destructuring assignment target');
};
P.lowerUpdate = function (u, fc, needValue) {
    const inc = u.operator === SK.PlusPlusToken;
    const prefix = ts.isPrefixUnaryExpression(u);
    const L = (0, stmts_1.skipParens)(u.operand);
    const step = (cur) => {
        const c = this.unfoldE(cur);
        if (c.ty.k === 'num')
            return ir_1.E.prim(`(.numBin .${inc ? 'add' : 'sub'})`, [c, (0, core_1.numLit)(1)], [ty_1.T.num, ty_1.T.num], ty_1.T.num);
        if (c.ty.k === 'bigint')
            return ir_1.E.prim(`(.bigBin .${inc ? 'add' : 'sub'})`, [c, (0, core_1.bigLit)(1n)], [ty_1.T.bigint, ty_1.T.bigint], ty_1.T.bigint);
        (0, diag_1.reject)(u, 'unsupported', `++/-- on ${(0, ty_1.prettyTy)(c.ty)}`);
    };
    const run = (read, write) => {
        if (!needValue) {
            write(step(read()));
            return null;
        }
        if (prefix) {
            const nv = this.bindTemp(step(read()), fc, 'nv');
            write(ir_1.E.var(nv));
            return ir_1.E.var(nv);
        }
        const old = this.bindTemp(read(), fc, 'old');
        write(step(ir_1.E.var(old)));
        return ir_1.E.var(old);
    };
    if (ts.isIdentifier(L)) {
        const sym = this.symAt(L);
        const bd = sym && this.lookup(sym, fc);
        if (!bd)
            (0, diag_1.reject)(L, 'unsupported', `update of ${L.text}`);
        if (bd.k === 'poison')
            return needValue ? ir_1.E.poison(bd.ty) : null;
        return run(() => this.readBinding(bd, L), v => { this.assignTo(bd, v, false, fc, u); });
    }
    if (ts.isPropertyAccessExpression(L)) {
        const st = this.staticFieldGlobal(L);
        if (st)
            return run(() => ir_1.E.gget(st), v => { fc.pre.push((0, ir_1.stmtItem)(ir_1.S.gset(st, v))); });
        const o0 = this.unfoldE(this.lowerExpr(L.expression, fc));
        if ((0, ir_1.isPoison)(o0))
            return needValue ? this.derivedPoison(u, fc) : null;
        if (o0.ty.k === 'dyn')
            (0, diag_1.reject)(u, 'any-op', '++/-- on a property of a value of type any/unknown');
        if (o0.ty.k === 'dict') {
            const d = this.spill(o0, fc, 'd'), k = (0, core_1.strLit)(L.name.text);
            return run(() => this.dictRead(d, k, L, fc), v => { fc.pre.push((0, ir_1.stmtItem)(this.dictSetStmt(d, k, v))); });
        }
        if (o0.ty.k !== 'obj')
            (0, diag_1.reject)(u, o0.ty.k === 'record' ? 'record-mutation' : 'unsupported', `update of property ${L.name.text} of ${(0, ty_1.prettyTy)(o0.ty)}`);
        const c = o0.ty.c;
        const info = this.classOfObj(c);
        const idx = info?.fieldIdx.get(L.name.text);
        if (!info || idx === undefined)
            (0, diag_1.reject)(u, 'unsupported', `no field ${L.name.text} on ${c}`);
        const fty = info.fields[idx].ty;
        const o = this.spill(o0, fc, 'o');
        return run(() => ir_1.E.getField(o, c, idx, fty), v => { fc.pre.push((0, ir_1.stmtItem)(ir_1.S.setField(o, c, idx, fty, v))); });
    }
    if (ts.isElementAccessExpression(L)) {
        const base = this.unfoldE(this.lowerExpr(L.expression, fc));
        if ((0, ir_1.isPoison)(base)) {
            this.lowerExpr(L.argumentExpression, fc);
            return needValue ? this.derivedPoison(u, fc) : null;
        }
        if (base.ty.k === 'dyn')
            (0, diag_1.reject)(u, 'any-op', '++/-- on an element of a value of type any/unknown');
        if (base.ty.k === 'dict') {
            const [d1, k1] = this.seq([() => base, () => this.dictKey(L.argumentExpression, fc)], fc);
            const d = this.spill(d1, fc, 'd'), k = this.spill(k1, fc, 'k');
            return run(() => this.dictRead(d, k, L, fc), v => { fc.pre.push((0, ir_1.stmtItem)(this.dictSetStmt(d, k, v))); });
        }
        if (base.ty.k === 'record' || base.ty.k === 'obj')
            (0, diag_1.reject)(L, 'computed-key', `update of a computed property of ${(0, ty_1.prettyTy)(base.ty)}`);
        const [a0, i0] = this.seq([() => base, () => this.lowerExpr(L.argumentExpression, fc, ty_1.T.num)], fc);
        if (a0.ty.k !== 'arr')
            (0, diag_1.reject)(u, 'unsupported', `++/-- on an element of ${(0, ty_1.prettyTy)(a0.ty)}`);
        const at = a0.ty;
        const a = this.spill(a0, fc, 'a'), i = this.spill(i0, fc, 'i');
        return run(() => ir_1.E.builtin(`(.arrGet ${(0, ty_1.showTy)(at.t)})`, [a, i], [at, ty_1.T.num], at.t), v => { fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(ir_1.E.builtin(`(.arrSet ${(0, ty_1.showTy)(at.t)})`, [a, i, v], [at, ty_1.T.num, at.t], ty_1.T.undef)))); });
    }
    (0, diag_1.reject)(u, 'unsupported-syntax', '++/-- target');
};
P.lowerAwaitOperand = function (a, fc) {
    if (fc.kind === 'main')
        (0, diag_1.reject)(a, 'top-level-await', 'top-level `await` is not supported; use an async function');
    if (!fc.async)
        (0, diag_1.reject)(a, 'unsupported', '`await` outside an async function');
    const e = this.lowerExpr(a.expression, fc);
    if ((0, ir_1.isPoison)(e)) {
        let t = ty_1.T.undef;
        try {
            t = this.tyAt(a, fc);
        }
        catch { /* unknown */ }
        return ir_1.E.poison(ty_1.T.promise(t));
    }
    if (e.ty.k === 'promise')
        return e;
    return ir_1.E.builtin(`(.promResolve ${(0, ty_1.showTy)(e.ty)})`, [e], [e.ty], ty_1.T.promise(e.ty));
};
// ---------------------------------------------------------------------------------------
// literals
P.lowerArrayLit = function (n, fc, exp) {
    let target = exp ?? this.tyAt(n, fc);
    if (target.k === 'opt')
        return ir_1.E.some(this.lowerArrayLit(n, fc, target.t));
    if (target.k === 'named')
        return ir_1.E.fold(target.n, this.lowerArrayLit(n, fc, this.aliasOf(target.n)));
    if (target.k === 'union') {
        const nat = this.tyAt(n, fc);
        if (nat.k === 'union')
            (0, diag_1.reject)(n, 'unsupported', 'array literal of a union type');
        return this.coerce(this.lowerArrayLit(n, fc, nat), target, n);
    }
    if (target.k === 'tup') {
        const tt = target;
        if (n.elements.length !== tt.ts.length || n.elements.some(ts.isSpreadElement))
            (0, diag_1.reject)(n, 'unsupported', 'tuple literal does not match the tuple type');
        const parts = this.seq(n.elements.map((el, i) => () => this.lowerExpr(el, fc, tt.ts[i])), fc);
        return ir_1.E.mkTup(parts);
    }
    if (target.k === 'set' || target.k === 'map')
        (0, diag_1.reject)(n, 'unsupported', 'array literal used as a Set/Map');
    if (target.k !== 'arr')
        (0, diag_1.reject)(n, 'unsupported', `array literal of type ${(0, ty_1.prettyTy)(target)}`);
    const el = target.t;
    if (n.elements.some(e => e.kind === SK.OmittedExpression))
        (0, diag_1.reject)(n, 'no-sparse', 'array holes are not allowed');
    if (!n.elements.some(ts.isSpreadElement)) {
        const parts = this.seq(n.elements.map(e => () => this.lowerExpr(e, fc, el)), fc);
        return ir_1.E.builtin(`(.arrOf ${(0, ty_1.showTy)(el)} ${parts.length})`, parts, parts.map(() => el), target);
    }
    // segments: runs of plain elements and spreads
    const segs = [];
    for (const e of n.elements) {
        if (ts.isSpreadElement(e))
            segs.push({ spread: true, nodes: [e.expression] });
        else if (segs.length && !segs[segs.length - 1].spread)
            segs[segs.length - 1].nodes.push(e);
        else
            segs.push({ spread: false, nodes: [e] });
    }
    const at = target;
    const segExprs = this.seq(segs.map((sg, si) => () => {
        if (!sg.spread) {
            const parts = this.seq(sg.nodes.map(e => () => this.lowerExpr(e, fc, el)), fc);
            return ir_1.E.builtin(`(.arrOf ${(0, ty_1.showTy)(el)} ${parts.length})`, parts, parts.map(() => el), at);
        }
        const src = this.spreadSource(sg.nodes[0], fc, el);
        // snapshot when later segments may run code
        const later = segs.slice(si + 1);
        if (src.fresh || later.length === 0)
            return src.e;
        return ir_1.E.builtin(`(.arrCopy ${(0, ty_1.showTy)(el)})`, [src.e], [at], at);
    }), fc);
    let acc = segExprs[0];
    if (segs[0].spread && segs.length === 1 && !this.spreadSource(segs[0].nodes[0], fc, el, true).fresh) {
        acc = ir_1.E.builtin(`(.arrCopy ${(0, ty_1.showTy)(el)})`, [acc], [at], at);
    }
    for (let i = 1; i < segExprs.length; i++)
        acc = ir_1.E.builtin(`(.arrConcat ${(0, ty_1.showTy)(el)})`, [acc, segExprs[i]], [at, at], at);
    return acc;
};
P.spreadSource = function (n, fc, el, dryRun = false) {
    const it = (0, stmts_1.skipParens)(n);
    if (ts.isCallExpression(it) && ts.isPropertyAccessExpression(it.expression) && it.arguments.length === 0) {
        const m = it.expression.name.text;
        const rt = this.unfoldTy(this.tyAt(it.expression.expression, fc));
        if ((rt.k === 'map' && ['keys', 'values', 'entries'].includes(m)) || (rt.k === 'set' && ['keys', 'values'].includes(m))) {
            if (dryRun)
                return { e: ir_1.E.undef(), fresh: true };
            const base = this.lowerExpr(it.expression.expression, fc);
            return { e: this.coerce(this.collectionSnapshot(base, m, it), ty_1.T.arr(el), n), fresh: true };
        }
    }
    if (dryRun) {
        const t = this.unfoldTy(this.tyAt(it, fc));
        return { e: ir_1.E.undef(), fresh: t.k === 'set' || t.k === 'map' || t.k === 'str' || t.k === 'enum' };
    }
    const e = this.unfoldE(this.lowerExpr(it, fc));
    if (e.ty.k === 'arr') {
        if (!(0, ty_1.tyEq)(e.ty.t, el))
            (0, diag_1.reject)(n, 'unsupported', `spread of ${(0, ty_1.prettyTy)(e.ty)} into ${(0, ty_1.prettyTy)(ty_1.T.arr(el))}`);
        return { e, fresh: false };
    }
    if (e.ty.k === 'str' || e.ty.k === 'enum')
        return { e: this.coerce(this.codePoints(e, fc, n), ty_1.T.arr(el), n), fresh: true };
    if (e.ty.k === 'tup')
        return { e: this.coerce(e, ty_1.T.arr(el), n), fresh: true };
    if (e.ty.k === 'set')
        return { e: this.coerce(this.collectionSnapshot(e, 'values', n), ty_1.T.arr(el), n), fresh: true };
    if (e.ty.k === 'map')
        return { e: this.coerce(this.collectionSnapshot(e, 'entries', n), ty_1.T.arr(el), n), fresh: true };
    (0, diag_1.reject)(n, e.ty.k === 'dyn' ? 'any-op' : 'unsupported', `spread of ${(0, ty_1.prettyTy)(e.ty)}`);
};
P.codePoints = function (e, fc, node) {
    const str = this.spill(this.toStr(e, node), fc, 's');
    const out = (0, ir_1.mkVar)('cps', ty_1.T.arr(ty_1.T.str));
    fc.pre.push((0, ir_1.declItem)(out, ir_1.E.builtin('(.arrOf .str 0)', [], [], ty_1.T.arr(ty_1.T.str))));
    const ch = (0, ir_1.mkVar)('ch', ty_1.T.str);
    fc.pre.push((0, ir_1.stmtItem)({ k: 'forOfStr', e: str, v: ch, body: [(0, ir_1.stmtItem)(ir_1.S.expr(ir_1.E.builtin('(.arrPush .str)', [ir_1.E.var(out), ir_1.E.var(ch)], [ty_1.T.arr(ty_1.T.str), ty_1.T.str], ty_1.T.num)))] }));
    return ir_1.E.var(out);
};
P.lowerObjectLit = function (n, fc, exp) {
    const target = exp ?? this.tyAt(n, fc);
    if (target.k === 'box' && target.t.k === 'record') {
        // an object compared by identity (identity.ts): a new cell at each evaluation
        const r = this.lowerObjectLit(n, fc, target.t);
        return ir_1.E.builtin(`(.boxNew ${(0, ty_1.showTy)(target.t)})`, [r], [target.t], target);
    }
    if (target.k === 'opt')
        return ir_1.E.some(this.lowerObjectLit(n, fc, target.t));
    if (target.k === 'named')
        return ir_1.E.fold(target.n, this.lowerObjectLit(n, fc, this.aliasOf(target.n)));
    if (target.k === 'dict')
        return this.lowerDictLit(n, target, fc);
    if (target.k === 'union') {
        // pick the member TypeScript assigns the literal to
        const litT = this.checker.getTypeAtLocation(n);
        const ctx = this.checker.getContextualType(n);
        const members = ctx && ctx.isUnion() ? ctx.types : [];
        for (const m of members) {
            if (m.flags & (ts.TypeFlags.Undefined | ts.TypeFlags.Null))
                continue;
            if (!this.checker.isTypeAssignableTo(litT, m))
                continue;
            const mt = this.tyOf(m, fc, n);
            const idx = target.ts.findIndex(x => (0, ty_1.tyEq)(x, mt));
            if (idx >= 0)
                return ir_1.E.inj(target, idx, this.lowerObjectLit(n, fc, mt));
        }
        const nat = this.tyOf(litT, fc, n);
        if (nat.k === 'union' || nat.k === 'opt' || nat.k === 'named')
            (0, diag_1.reject)(n, 'unsupported', `object literal of type ${(0, ty_1.prettyTy)(target)} that matches no single member`);
        return this.coerce(this.lowerObjectLit(n, fc, nat), target, n);
    }
    const fields = target.k === 'record' ? target.fs
        : target.k === 'obj' ? (this.classOfObj(target.c)?.fields ?? []) : [];
    if (target.k === 'obj') {
        if (this.types.classes.has(target.c))
            (0, diag_1.reject)(n, 'unsupported', `object literal used as an instance of class ${target.c}`);
    }
    else if (target.k === 'ext')
        (0, diag_1.reject)(n, 'ext-literal', `object literal used as a value of the external type ${target.name}`);
    else if (target.k !== 'record')
        (0, diag_1.reject)(n, 'unsupported', `object literal of type ${(0, ty_1.prettyTy)(target)}`);
    const fieldTy = (name) => fields.find(f => f.name === name)?.ty;
    const provs = [];
    for (const p of n.properties) {
        if (ts.isPropertyAssignment(p) || ts.isShorthandPropertyAssignment(p)) {
            const key = p.name;
            if (!ts.isIdentifier(key) && !ts.isStringLiteral(key) && !ts.isNumericLiteral(key))
                (0, diag_1.reject)(p, 'unsupported-syntax', 'computed property name');
            const name = key.text;
            const ft = fieldTy(name);
            if (!ft)
                (0, diag_1.reject)(p, 'unsupported', `property ${name} is not part of ${(0, ty_1.prettyTy)(target)}`);
            const valNode = ts.isPropertyAssignment(p) ? p.initializer : p.name;
            provs.push({ name, node: p, thunk: () => this.lowerExpr(valNode, fc, ft) });
        }
        else if (ts.isMethodDeclaration(p)) {
            if (!ts.isIdentifier(p.name))
                (0, diag_1.reject)(p, 'unsupported-syntax', 'computed method name');
            const name = p.name.text;
            const ft = fieldTy(name);
            if (!ft)
                (0, diag_1.reject)(p, 'unsupported', `method ${name} is not part of ${(0, ty_1.prettyTy)(target)}`);
            provs.push({ name, node: p, thunk: () => this.lowerLambda(p, fc, ft) });
        }
        else if (ts.isSpreadAssignment(p)) {
            // `...(c ? { k: v } : {})` / `...(c && { k: v })`: the empty object contributes nothing,
            // so the spread is an optional value of the other branch (TypeScript's type of the
            // conditional adds `k?: undefined` to `{}`, which would read as a property)
            const se = (0, stmts_1.skipParens)(p.expression);
            const isEmptyLit = (x) => { const y = (0, stmts_1.skipParens)(x); return ts.isObjectLiteralExpression(y) && y.properties.length === 0; };
            let cond, branch, flip = false;
            if (ts.isConditionalExpression(se) && (isEmptyLit(se.whenTrue) !== isEmptyLit(se.whenFalse))) {
                cond = se.condition;
                flip = isEmptyLit(se.whenTrue);
                branch = flip ? se.whenFalse : se.whenTrue;
            }
            else if (ts.isBinaryExpression(se) && se.operatorToken.kind === SK.AmpersandAmpersandToken && ts.isObjectLiteralExpression((0, stmts_1.skipParens)(se.right))) {
                cond = se.left;
                branch = se.right;
            }
            if (cond && branch) {
                const c0 = cond, b0 = branch, fl = flip;
                provs.push({ node: p, thunk: () => {
                        const c = this.lowerCond(c0, fc);
                        const bt = this.tyAt(b0, fc);
                        // (the branch is evaluated only when taken)
                        const saved = fc.pre;
                        const items = [];
                        fc.pre = items;
                        let bv;
                        try {
                            bv = this.lowerExpr(b0, fc, bt);
                        }
                        finally {
                            fc.pre = saved;
                        }
                        const r = (0, ir_1.mkVar)('sp', ty_1.T.opt(bt));
                        fc.pre.push((0, ir_1.declItem)(r, ir_1.E.none(bt)));
                        r.assigned = true;
                        fc.pre.push((0, ir_1.stmtItem)(ir_1.S.ite(fl ? ir_1.E.not(c) : c, [...items, (0, ir_1.stmtItem)(ir_1.S.assign(r, ir_1.E.some(bv)))], [])));
                        return ir_1.E.var(r);
                    } });
            }
            else
                provs.push({ node: p, thunk: () => this.unfoldE(this.lowerExpr(p.expression, fc)) });
        }
        else
            (0, diag_1.reject)(p, 'unsupported-syntax', 'getters/setters in object literals');
    }
    const vals = this.seq(provs.map(pv => pv.thunk), fc);
    // JavaScript evaluates the initialisers in source order, the value is built in field order:
    // with more than one effect, every initialiser is evaluated into a temporary first (spreads
    // always are, so that several fields can be read; overridden values only for their effects)
    // (a spread has no name; the property name "" is a name)
    const effects = provs.filter((pv, i) => pv.name === undefined || !(0, ir_1.isStable)(vals[i])).length;
    // a spread source: records, dictionaries, objects (their fields read at the spread, as a
    // record), and optional values and unions of those (`...(opts ?? {})`, `...(c ? a : b)`)
    const spreadable = (t0) => {
        const t = this.unfoldTy(t0);
        switch (t.k) {
            case 'record':
            case 'dict':
            case 'undef':
            case 'null': return true;
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
            if (sv.ty.k === 'box' && sv.ty.t.k === 'record')
                sv = this.unboxCell(sv);
            if (sv.ty.k === 'obj') {
                // CopyDataProperties reads the own properties now: a record of the fields
                const info = this.classOfObj(sv.ty.c);
                const c = sv.ty.c;
                const o = ir_1.E.var(this.bindTemp(sv, fc, 'so'));
                const fs = (0, ty_1.sortFields)(info.fields);
                sv = ir_1.E.mkRec(ty_1.T.record(fs), fs.map(f => { const idx = info.fields.findIndex(g => g.name === f.name); return ir_1.E.getField(o, c, idx, f.ty); }));
            }
            const v = this.bindTemp(sv, fc, 'sp');
            vals[i] = ir_1.E.var(v);
            if (!spreadable(vals[i].ty))
                (0, diag_1.reject)(pv.node, vals[i].ty.k === 'dyn' ? 'any-op' : 'unsupported', `spread of ${(0, ty_1.prettyTy)(vals[i].ty)}`);
        }
        else if (effects > 1 && !(0, ir_1.isStable)(vals[i])) {
            if (provs.slice(i + 1).some(q => q.name === pv.name)) {
                fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(vals[i])));
                vals[i] = ir_1.E.undef();
            }
            else
                vals[i] = ir_1.E.var(this.bindTemp(vals[i], fc, 'fv'));
        }
    });
    // the value of field f from the providers up to i (the last one that has f wins; whether a
    // spread dictionary has f is decided at run time)
    // the field f from a spread value at provider i, else from the providers before it
    const fromSpread = (v0, f, i, node) => {
        const v = this.unfoldE(v0);
        const t = v.ty;
        switch (t.k) {
            case 'record': {
                const j = t.fs.findIndex(g => g.name === f.name);
                if (j < 0)
                    return provide(f, i - 1);
                if (t.fs[j].ty.k === 'opt' && f.ty.k !== 'opt') {
                    (0, diag_1.reject)(node, 'spread-optional', `spread of an optional field ${f.name}: JavaScript keeps an explicit undefined, records cannot tell it from a missing field`);
                }
                return this.coerce(ir_1.E.getRec(v, j), f.ty, node);
            }
            case 'dict': {
                const key = (0, core_1.strLit)(f.name);
                const got = this.dictGetOpt(v, key);
                const val = f.ty.k === 'opt' ? this.coerce(got, f.ty, node) : this.coerce(ir_1.E.unwrap(got), f.ty, node);
                return ir_1.E.cond(ir_1.E.builtin(`(.dictHasOwn ${(0, ty_1.showTy)(t.t)})`, [v, key], [t, ty_1.T.str], ty_1.T.bool), val, provide(f, i - 1));
            }
            case 'undef':
            case 'null': return provide(f, i - 1);
            case 'box':
                if (t.t.k === 'record')
                    return fromSpread(this.unboxCell(v), f, i, node);
                break;
            case 'opt': {
                const x = (0, ir_1.mkVar)('s', t.t);
                return ir_1.E.caseOpt(v, provide(f, i - 1), x, fromSpread(ir_1.E.var(x), f, i, node));
            }
            case 'union': return ir_1.E.caseU(v, t.ts.map(m => { const x = (0, ir_1.mkVar)('s', m); return { v: x, body: fromSpread(ir_1.E.var(x), f, i, node) }; }));
        }
        (0, diag_1.reject)(node, 'unsupported', `spread of ${(0, ty_1.prettyTy)(t)}`);
    };
    // the value of field f from the providers up to `upto` (the last one that has f wins; for
    // dictionaries, optional values and unions that is decided at run time)
    // can a spread value of type t provide the field? (a record has exactly its fields; whether
    // a dictionary has the key is decided at run time)
    const mayHave = (t0, name) => {
        const t = this.unfoldTy(t0);
        switch (t.k) {
            case 'record': return t.fs.some(g => g.name === name);
            case 'box':
            case 'opt': return mayHave(t.t, name);
            case 'union': return t.ts.some(m => mayHave(m, name));
            case 'undef':
            case 'null': return false;
            default: return true;
        }
    };
    const provide = (f, upto) => {
        for (let i = upto; i >= 0; i--) {
            const pv = provs[i];
            if (pv.name === f.name)
                return vals[i];
            if (pv.name === undefined) {
                // a spread that cannot have f (a record without it, also optional or in a union): look
                // further back without a case split (with one, both branches would hold the providers
                // before it: exponential in the number of such spreads)
                if (!mayHave(vals[i].ty, f.name))
                    continue;
                return fromSpread(vals[i], f, i, pv.node);
            }
        }
        if (f.ty.k === 'opt')
            return ir_1.E.none(f.ty.t);
        if (f.ty.k === 'undef')
            return ir_1.E.undef();
        // (only after a spread that may lack the field at run time: TypeScript's types were wrong)
        if (provs.slice(0, upto + 1).some((pv, i) => pv.name === undefined && this.unfoldTy(vals[i].ty).k !== 'record'))
            return ir_1.E.unreachable(f.ty);
        (0, diag_1.reject)(n, 'unsupported', `missing property ${f.name}`);
    };
    const fieldVals = fields.map(f => provide(f, provs.length - 1));
    // evaluated values that are not used (overridden properties) are kept for their effects
    // (the only effect, else they were evaluated above)
    provs.forEach((pv, i) => {
        if (pv.name !== undefined && !fieldVals.includes(vals[i]) && !(0, ir_1.isStable)(vals[i]))
            fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(vals[i])));
    });
    if (target.k === 'record')
        return ir_1.E.mkRec(target, fieldVals);
    const ms = this.types.mutStructs.find(m => m.name === target.c);
    return ir_1.E.call(this.structCtor(ms, n), fieldVals);
};
P.lowerCallArgs = function (specs, args, fc, node, prefix) {
    const thunks = [...prefix];
    const restIdx = specs.findIndex(s => s.rest);
    const nFixed = restIdx >= 0 ? restIdx : specs.length;
    for (let i = 0; i < nFixed; i++) {
        const sp = specs[i];
        if (i < args.length) {
            if (ts.isSpreadElement(args[i]))
                (0, diag_1.reject)(args[i], 'unsupported', 'spread argument to a non-rest parameter');
            thunks.push(() => this.lowerExpr(args[i], fc, sp.ty));
        }
        else if (sp.ty.k === 'opt')
            thunks.push(() => ir_1.E.none(sp.ty.t));
        else if (sp.ty.k === 'undef')
            thunks.push(() => ir_1.E.undef());
        else
            (0, diag_1.reject)(node, 'unsupported', 'missing argument');
    }
    if (restIdx >= 0) {
        const at = specs[restIdx].ty;
        const rest = args.slice(nFixed);
        if (rest.length === 1 && ts.isSpreadElement(rest[0])) {
            const sp = rest[0];
            thunks.push(() => {
                const src = this.spreadSource(sp.expression, fc, at.t);
                return src.fresh ? src.e : ir_1.E.builtin(`(.arrCopy ${(0, ty_1.showTy)(at.t)})`, [src.e], [at], at);
            });
        }
        else {
            if (rest.some(ts.isSpreadElement))
                (0, diag_1.reject)(node, 'unsupported', 'spread mixed with other rest arguments');
            thunks.push(() => {
                const parts = this.seq(rest.map(a => () => this.lowerExpr(a, fc, at.t)), fc);
                return ir_1.E.builtin(`(.arrOf ${(0, ty_1.showTy)(at.t)} ${parts.length})`, parts, parts.map(() => at.t), at);
            });
        }
    }
    else if (args.length > specs.length)
        (0, diag_1.reject)(args[specs.length], 'unsupported', 'too many arguments');
    return this.seq(thunks, fc);
};

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
// Objects used as dictionaries (`{ [k: string]: T }`, `Record<string, T>`): `.dict T` and the
// dict builtins of the semantics (ECMA-262 key order: array indices ascending, then the other
// keys in insertion order; reading an inherited `Object.prototype` property panics).
//   o[k], o.p           -> dictGet (opt T), unwrapped where TypeScript types the read as T
//   o[k] = v, o.p = v   -> dictSet          k in o -> dictHas      delete o[k] -> dictDelete
//   Object.keys/values/entries(o), Object.hasOwn(o, k), o.hasOwnProperty(k)
//   object literals typed as dictionaries -> dictNew, then dictSet per property (spreads of
//   dictionaries copy their entries in order)
const ts = __importStar(require("typescript"));
const ty_1 = require("./ty");
const ir_1 = require("./ir");
const diag_1 = require("./diag");
const core_1 = require("./core");
const stmts_1 = require("./stmts");
const exprs_1 = require("./exprs");
const P = core_1.Translator.prototype;
P.dictKey = function (k, fc) {
    const e = this.unfoldE(this.lowerExpr(k, fc));
    if ((0, ir_1.isPoison)(e))
        return ir_1.E.poison(ty_1.T.str);
    if (e.ty.k === 'str')
        return e;
    if (e.ty.k === 'enum' || e.ty.k === 'num')
        return this.toStr(e, k);
    (0, diag_1.reject)(k, 'unsupported', `a property key of type ${(0, ty_1.prettyTy)(e.ty)}`);
};
P.dictGetOpt = function (d, key) {
    const t = d.ty.t;
    const g = ir_1.E.builtin(`(.dictGet ${(0, ty_1.showTy)(t)})`, [d, key], [d.ty, ty_1.T.str], ty_1.T.opt(t));
    if (t.k !== 'opt')
        return g;
    const v = (0, ir_1.mkVar)('x', t);
    return ir_1.E.caseOpt(g, ir_1.E.none(t.t), v, ir_1.E.var(v));
};
P.dictRead = function (d, key, node, fc, exp) {
    const g = this.dictGetOpt(d, key);
    const want = this.tyAt(node, fc);
    // (an unknown value includes undefined: an absent key reads as undefined)
    if (want.k === 'opt' || want.k === 'dyn')
        return this.adapt(g, want, node);
    if ((0, exprs_1.defensiveContext)(node) || (exp && exp.k === 'opt'))
        return g;
    // (an unknown value narrowed to `{}` by `x !== undefined` stays unknown)
    if (d.ty.t.k === 'dyn' && (0, exprs_1.holdsUnknown)(want))
        return ir_1.E.unwrap(g);
    return this.adapt(ir_1.E.unwrap(g), want, node);
};
P.dictSetStmt = function (d, key, v) {
    const t = d.ty.t;
    return ir_1.S.expr(ir_1.E.builtin(`(.dictSet ${(0, ty_1.showTy)(t)})`, [d, key, v], [d.ty, ty_1.T.str, t], ty_1.T.undef));
};
P.dictTyOf = function (e, fc) {
    try {
        const t = this.unfoldTy(this.tyAt(e, fc));
        return t.k === 'dict' ? t : undefined;
    }
    catch {
        return undefined;
    }
};
P.lowerDictCall = function (call, fc) {
    const callee = (0, stmts_1.skipParens)(call.expression);
    if (!ts.isPropertyAccessExpression(callee) || callee.questionDotToken)
        return undefined;
    const name = callee.name.text;
    const args = call.arguments;
    const recv = (0, stmts_1.skipParens)(callee.expression);
    if (ts.isIdentifier(recv) && recv.text === 'Object' && ['keys', 'values', 'entries', 'hasOwn'].includes(name) && args.length >= 1) {
        const sym = this.symAt(recv);
        if (!sym || !(0, core_1.isLibDecl)(this.program, sym.declarations?.[0]) || ts.isSpreadElement(args[0]))
            return undefined;
        const dt = this.dictTyOf(args[0], fc);
        if (!dt)
            return undefined;
        const t = dt.t, st = (0, ty_1.showTy)(t);
        if (name === 'hasOwn') {
            if (args.length !== 2)
                (0, diag_1.reject)(call, 'unsupported-builtin', 'Object.hasOwn takes an object and a key');
            const [d, k] = this.seq([() => this.lowerExpr(args[0], fc, dt), () => this.dictKey(args[1], fc)], fc);
            return ir_1.E.builtin(`(.dictHasOwn ${st})`, [d, k], [dt, ty_1.T.str], ty_1.T.bool);
        }
        if (args.length !== 1)
            (0, diag_1.reject)(call, 'unsupported-builtin', `Object.${name} takes one object`);
        const d = this.lowerExpr(args[0], fc, dt);
        if (name === 'keys')
            return ir_1.E.builtin(`(.dictKeys ${st})`, [d], [dt], ty_1.T.arr(ty_1.T.str));
        if (name === 'values')
            return ir_1.E.builtin(`(.dictValues ${st})`, [d], [dt], ty_1.T.arr(t));
        return ir_1.E.builtin(`(.dictEntries ${st})`, [d], [dt], ty_1.T.arr(ty_1.T.tup([ty_1.T.str, t])));
    }
    if (name === 'hasOwnProperty' && args.length === 1) {
        const dt = this.dictTyOf(recv, fc);
        if (!dt)
            return undefined;
        const [d, k] = this.seq([() => this.lowerExpr(recv, fc, dt), () => this.dictKey(args[0], fc)], fc);
        return ir_1.E.builtin(`(.dictHasOwn ${(0, ty_1.showTy)(dt.t)})`, [d, k], [dt, ty_1.T.str], ty_1.T.bool);
    }
    return undefined;
};
P.lowerDictLit = function (n, t, fc) {
    const d = ir_1.E.var(this.bindTemp(ir_1.E.builtin(`(.dictNew ${(0, ty_1.showTy)(t.t)})`, [], [], t), fc, 'dict'));
    for (const p of n.properties) {
        if (ts.isPropertyAssignment(p) || ts.isShorthandPropertyAssignment(p)) {
            const key = p.name;
            let k;
            if (ts.isIdentifier(key) || ts.isStringLiteral(key) || ts.isNoSubstitutionTemplateLiteral(key))
                k = () => (0, core_1.strLit)(key.text);
            else if (ts.isNumericLiteral(key))
                k = () => (0, core_1.strLit)(String(Number(key.text)));
            else if (ts.isComputedPropertyName(key))
                k = () => this.dictKey(key.expression, fc);
            else
                (0, diag_1.reject)(p, 'unsupported-syntax', 'property name');
            const valNode = ts.isPropertyAssignment(p) ? p.initializer : p.name;
            const [kv, v] = this.seq([k, () => this.lowerExpr(valNode, fc, t.t)], fc);
            fc.pre.push((0, ir_1.stmtItem)(this.dictSetStmt(d, kv, v)));
        }
        else if (ts.isSpreadAssignment(p)) {
            // own entries in order (CopyDataProperties)
            const src = this.unfoldE(this.lowerExpr(p.expression, fc));
            if (src.ty.k !== 'dict' || !(0, ty_1.tyEq)(src.ty.t, t.t))
                (0, diag_1.reject)(p, 'unsupported', `spread of ${(0, ty_1.prettyTy)(src.ty)} into ${(0, ty_1.prettyTy)(t)}`);
            const et = ty_1.T.tup([ty_1.T.str, t.t]);
            const ev = (0, ir_1.mkVar)('e', et);
            const body = [(0, ir_1.stmtItem)(this.dictSetStmt(d, ir_1.E.getTup(ir_1.E.var(ev), 0), ir_1.E.getTup(ir_1.E.var(ev), 1)))];
            fc.pre.push((0, ir_1.stmtItem)({ k: 'forOf', e: ir_1.E.builtin(`(.dictEntries ${(0, ty_1.showTy)(t.t)})`, [src], [t], ty_1.T.arr(et)), v: ev, body }));
        }
        else
            (0, diag_1.reject)(p, 'unsupported-syntax', 'methods and accessors in a dictionary literal');
    }
    return d;
};
P.dictAssign = function (d0, key, b, cop, needValue, fc) {
    const t = d0.ty.t;
    if (cop === undefined) {
        const [d, k, v] = this.seq([() => d0, key, () => this.lowerExpr(b.right, fc, t)], fc);
        const vv = needValue ? ir_1.E.var(this.bindTemp(v, fc, 'dv')) : v;
        fc.pre.push((0, ir_1.stmtItem)(this.dictSetStmt(d, k, vv)));
        return needValue ? vv : null;
    }
    const [d1, k1] = this.seq([() => d0, key], fc);
    const d = this.spill(d1, fc, 'd'), k = this.spill(k1, fc, 'k');
    const [cur, r] = this.seq([() => this.dictRead(d, k, b.left, fc), () => this.lowerExpr(b.right, fc)], fc);
    let value = this.coerce(this.arith(cop, cur, r, b), t, b);
    if (needValue)
        value = ir_1.E.var(this.bindTemp(value, fc, 'dv'));
    fc.pre.push((0, ir_1.stmtItem)(this.dictSetStmt(d, k, value)));
    return needValue ? value : null;
};

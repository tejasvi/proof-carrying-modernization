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
// Regular expressions as external calls. A regex used as the receiver of `test` / `exec` or as
// the pattern of `match` / `replace` / `replaceAll` / `split` / `search` becomes an `extern`
// whose arguments are the receiver, then the pattern and the flags, then the other arguments:
//   re.test(s)        -> .extern "RegExp.test" [pattern, flags, s]
//   s.replace(re, r)  -> .extern "String.replace" [s, pattern, flags, r]
// A literal (written at the call or bound by a `const` declaration) gives them as string
// literals; any other regex is a value, the record of its flags and source (`REGEXP_TY`): a
// literal used as a value, or `new RegExp(pattern, flags)`, the extern "RegExp.new" (which
// throws Node's SyntaxError for a bad pattern). `test` / `exec` (and `match` / `replace` on
// sticky regexes) read and write `lastIndex` when the regex is global or sticky; that state is
// not modelled, so such calls are accepted on a literal written at the call (a fresh regex each
// time), rejected on a literal bound to a name, and panic on a value with such flags; `lastIndex`
// itself is rejected, and so is `===` on regex values (identity). `split` and replacer functions
// need the groups of the pattern, so they take literals only.
const ts = __importStar(require("typescript"));
const ty_1 = require("./ty");
const ir_1 = require("./ir");
const diag_1 = require("./diag");
const core_1 = require("./core");
const stmts_1 = require("./stmts");
const P = core_1.Translator.prototype;
/** Pattern and flags of a literal; the flags in the order of `RegExp.prototype.flags`. */
function parseLit(n) {
    const i = n.text.lastIndexOf('/');
    const fl = n.text.slice(i + 1);
    return { pattern: n.text.slice(1, i), flags: [...'dgimsuvy'].filter(c => fl.includes(c)).join('') };
}
/** The number of capturing groups of the pattern (`none` if it has named groups, whose
 * `groups` object would be passed to replacers). */
function captureCount(p) {
    let inClass = false, n = 0;
    for (let i = 0; i < p.length; i++) {
        const c = p[i];
        if (c === '\\') {
            i++;
            continue;
        }
        if (inClass) {
            if (c === ']')
                inClass = false;
            continue;
        }
        if (c === '[')
            inClass = true;
        else if (c === '(') {
            if (p[i + 1] !== '?')
                n++;
            else if (p[i + 2] === '<' && p[i + 3] !== '=' && p[i + 3] !== '!')
                return undefined;
        }
    }
    return n;
}
/** Whether the pattern has a capturing group (`(` not escaped, not in a class, not `(?`
 * except named groups `(?<name>`). */
function hasCapture(p) {
    let inClass = false;
    for (let i = 0; i < p.length; i++) {
        const c = p[i];
        if (c === '\\') {
            i++;
            continue;
        }
        if (inClass) {
            if (c === ']')
                inClass = false;
            continue;
        }
        if (c === '[')
            inClass = true;
        else if (c === '(' && (p[i + 1] !== '?' || (p[i + 2] === '<' && p[i + 3] !== '=' && p[i + 3] !== '!')))
            return true;
    }
    return false;
}
// STRICTTS_NO_REGEX=1: regexes rejected as before (to measure coverage without them)
const off = !!process.env.STRICTTS_NO_REGEX;
P.isRegexConst = function (d) {
    return !off && ts.isIdentifier(d.name) && !!d.initializer && ts.isRegularExpressionLiteral((0, stmts_1.skipParens)(d.initializer)) &&
        !!(d.parent.flags & ts.NodeFlags.Const);
};
P.regexLit = function (e0) {
    const e = (0, stmts_1.skipParens)(e0);
    if (ts.isRegularExpressionLiteral(e))
        return { ...parseLit(e), inline: true };
    if (ts.isIdentifier(e)) {
        const d = this.symAt(e)?.valueDeclaration;
        if (d && ts.isVariableDeclaration(d) && this.isRegexConst(d) && this.isProjectDecl(d)) {
            return { ...parseLit((0, stmts_1.skipParens)(d.initializer)), inline: false };
        }
    }
    return undefined;
};
/** `s.replace(re, f)` / `s.replaceAll(re, f)` with a replacer function, as RegExp.prototype
 * [@@replace] does it: the matches first (the extern `String.matchAll` for a global regex,
 * `RegExp.exec` otherwise), then for each match, in order, its index, the match and its groups
 * (each an extern read of the match result), the replacer called with them, the offset and the
 * string, and the pieces of the string between the matches. */
function replaceWithFunction(tr, call, recv, re, fnNode, fc) {
    const n = captureCount(re.pattern);
    if (n === undefined)
        (0, diag_1.reject)(call, 'no-regexp', 'a replacer function with named groups (its groups argument)');
    const global = re.flags.includes('g');
    if (!global && !re.inline && re.flags.includes('y'))
        (0, diag_1.reject)(call, 'no-regexp', 'replace with a sticky regex bound to a name reads and writes its lastIndex (not modelled)');
    const mt = ty_1.T.ext('RegExpExecArray');
    const fnTy = ty_1.T.fn([ty_1.T.str, ...Array.from({ length: n }, () => ty_1.T.opt(ty_1.T.str)), ty_1.T.num, ty_1.T.str], ty_1.T.str);
    const [s0, f0] = tr.seq([() => tr.lowerExpr(recv, fc, ty_1.T.str), () => tr.lowerCallback(fnNode, fc, fnTy)], fc);
    const s = ir_1.E.var(tr.bindTemp(s0, fc, 's'));
    const f = ir_1.E.var(tr.bindTemp(f0, fc, 'f'));
    const lit = [(0, core_1.strLit)(re.pattern), (0, core_1.strLit)(re.flags)];
    if (tr.coverage) {
        tr.covExternals.add(global ? 'String.matchAll' : 'RegExp.exec');
        tr.covExternals.add('RegExpExecArray.get:[]');
    }
    // the matches, as an array
    let ms;
    if (global)
        ms = ir_1.E.extern('String.matchAll', [s, ...lit], ty_1.T.arr(mt));
    else {
        const one = ir_1.E.extern('RegExp.exec', [...lit, s], ty_1.T.union([mt, ty_1.T.null]));
        const v = (0, ir_1.mkVar)('m', mt), u = (0, ir_1.mkVar)('u', ty_1.T.null);
        ms = ir_1.E.caseU(one, [{ v, body: ir_1.E.builtin(`(.arrOf ${(0, ty_1.showTy)(mt)} 1)`, [ir_1.E.var(v)], [mt], ty_1.T.arr(mt)) }, { v: u, body: ir_1.E.builtin(`(.arrOf ${(0, ty_1.showTy)(mt)} 0)`, [], [], ty_1.T.arr(mt)) }]);
    }
    const out = (0, ir_1.mkVar)('out', ty_1.T.str, true), next = (0, ir_1.mkVar)('next', ty_1.T.num, true);
    fc.pre.push((0, ir_1.declItem)(out, (0, core_1.strLit)('')));
    fc.pre.push((0, ir_1.declItem)(next, ir_1.E.lit('(.num 0)', ty_1.T.num, 0)));
    const m = (0, ir_1.mkVar)('m', mt);
    const body = [];
    const idx = (0, ir_1.mkVar)('idx', ty_1.T.num), m0 = (0, ir_1.mkVar)('m0', ty_1.T.str);
    body.push((0, ir_1.declItem)(idx, ir_1.E.extern('RegExpExecArray.get:index', [ir_1.E.var(m)], ty_1.T.num)));
    body.push((0, ir_1.declItem)(m0, ir_1.E.unwrap(ir_1.E.extern('RegExpExecArray.get:[]', [ir_1.E.var(m), ir_1.E.lit('(.num 0)', ty_1.T.num, 0)], ty_1.T.opt(ty_1.T.str)))));
    const groups = Array.from({ length: n }, (_, k) => {
        const g = (0, ir_1.mkVar)(`g${k + 1}`, ty_1.T.opt(ty_1.T.str));
        body.push((0, ir_1.declItem)(g, ir_1.E.extern('RegExpExecArray.get:[]', [ir_1.E.var(m), ir_1.E.lit(`(.num ${k + 1})`, ty_1.T.num, k + 1)], ty_1.T.opt(ty_1.T.str))));
        return ir_1.E.var(g);
    });
    const repl = (0, ir_1.mkVar)('repl', ty_1.T.str);
    body.push((0, ir_1.declItem)(repl, ir_1.E.app(f, [ir_1.E.var(m0), ...groups, ir_1.E.var(idx), s])));
    const slice = (a, b) => ir_1.E.prim('.strSlice', [s, a, b ? ir_1.E.some(b) : ir_1.E.none(ty_1.T.num)], [ty_1.T.str, ty_1.T.num, ty_1.T.opt(ty_1.T.num)], ty_1.T.str);
    const cat = (a, b) => ir_1.E.prim('.strConcat', [a, b], [ty_1.T.str, ty_1.T.str], ty_1.T.str);
    // (a match before the end of the previous one adds nothing: as in the specification)
    body.push((0, ir_1.stmtItem)(ir_1.S.ite(ir_1.E.prim('(.numCmp .ge)', [ir_1.E.var(idx), ir_1.E.var(next)], [ty_1.T.num, ty_1.T.num], ty_1.T.bool), [
        (0, ir_1.stmtItem)(ir_1.S.assign(out, cat(cat(ir_1.E.var(out), slice(ir_1.E.var(next), ir_1.E.var(idx))), ir_1.E.var(repl)))),
        (0, ir_1.stmtItem)(ir_1.S.assign(next, ir_1.E.prim('(.numBin .add)', [ir_1.E.var(idx), ir_1.E.prim('.strLength', [ir_1.E.var(m0)], [ty_1.T.str], ty_1.T.num)], [ty_1.T.num, ty_1.T.num], ty_1.T.num))),
    ], [])));
    fc.pre.push((0, ir_1.stmtItem)({ k: 'forOf', e: ms, v: m, body }));
    return cat(ir_1.E.var(out), slice(ir_1.E.var(next)));
}
const STRING_METHODS = new Set(['match', 'matchAll', 'replace', 'replaceAll', 'split', 'search']);
P.regexValue = function (re) {
    return ir_1.E.mkRec(ty_1.REGEXP_TY, [(0, core_1.strLit)(re.flags), (0, core_1.strLit)(re.pattern)]);
};
P.isRegExpType = function (t) {
    const sym = t.getSymbol();
    return !!sym && sym.name === 'RegExp' && (0, core_1.isLibDecl)(this.program, sym.declarations?.[0]);
};
/** `call` unless the flags of the regex value contain one of `bad` (and none of `unless`): those
 * flags make the call read and write `lastIndex`, which is not modelled (a panic). */
function guardFlags(flags, bad, unless, call) {
    const has = (c) => ir_1.E.prim('.strIncludes', [flags, (0, core_1.strLit)(c), (0, core_1.numLit)(0)], [ty_1.T.str, ty_1.T.str, ty_1.T.num], ty_1.T.bool);
    let c = [...bad].map(has).reduce((a, b) => ir_1.E.or(a, b));
    for (const u of unless)
        c = ir_1.E.and(c, ir_1.E.not(has(u)));
    return ir_1.E.cond(c, ir_1.E.unreachable(call.ty), call);
}
P.lowerRegexCall = function (call, fc, exp) {
    const callee = (0, stmts_1.skipParens)(call.expression);
    if (off || !ts.isPropertyAccessExpression(callee) || callee.questionDotToken)
        return undefined;
    const name = callee.name.text;
    const args = call.arguments;
    const stateful = (re, flags) => !re.inline && [...flags].some(f => re.flags.includes(f));
    const sig = () => {
        const s = this.checker.getResolvedSignature(call);
        if (!s)
            (0, diag_1.reject)(call, 'no-regexp', `cannot resolve the signature of ${name}`);
        return this.tyOf(s.getReturnType(), fc, call);
    };
    const lit = (re) => [(0, core_1.strLit)(re.pattern), (0, core_1.strLit)(re.flags)];
    // a regex value (not a literal): the record of its flags and source
    const valueOf = (x) => this.isRegExpType(this.checker.getTypeAtLocation(x));
    // (evaluated into a variable in its turn: its two fields are read)
    const value = (x) => () => ir_1.E.var(this.bindTemp(this.lowerExpr(x, fc, ty_1.REGEXP_TY), fc, 're'));
    const fields = (rv) => [ir_1.E.getRec(rv, 1), ir_1.E.getRec(rv, 0)];
    if (name === 'test' || name === 'exec') {
        const re = this.regexLit(callee.expression);
        if (!re && !valueOf(callee.expression))
            return undefined;
        if (args.length !== 1 || ts.isSpreadElement(args[0]))
            (0, diag_1.reject)(call, 'no-regexp', `RegExp.${name} takes one string`);
        if (re && stateful(re, 'gy')) {
            (0, diag_1.reject)(call, 'no-regexp', `${name} on a global or sticky regex bound to a name reads and writes its lastIndex (not modelled); write the literal at the call`);
        }
        if (this.coverage)
            this.covExternals.add(`RegExp.${name}`);
        const ret = name === 'test' ? ty_1.T.bool : sig();
        if (re)
            return ir_1.E.extern(`RegExp.${name}`, [...lit(re), this.lowerExpr(args[0], fc, ty_1.T.str)], ret);
        const [rv, s] = this.seq([value(callee.expression), () => this.lowerExpr(args[0], fc, ty_1.T.str)], fc);
        const [pat, fl] = fields(rv);
        return guardFlags(fl, 'gy', '', ir_1.E.extern(`RegExp.${name}`, [pat, fl, s], ret));
    }
    if (STRING_METHODS.has(name) && args.length >= 1 && !ts.isSpreadElement(args[0])) {
        const re = this.regexLit(args[0]);
        if (!re && !valueOf(args[0]))
            return undefined;
        const rt = this.checker.getTypeAtLocation(callee.expression);
        if (!(rt.flags & ts.TypeFlags.StringLike))
            return undefined;
        if (re && (name === 'match' || name === 'replace') && stateful(re, 'y') && !re.flags.includes('g')) {
            (0, diag_1.reject)(call, 'no-regexp', `${name} with a sticky regex bound to a name reads and writes its lastIndex (not modelled)`);
        }
        if (name === 'split' && re && hasCapture(re.pattern)) {
            (0, diag_1.reject)(call, 'no-regexp', 'split with a capturing group puts the groups (possibly undefined) into the result');
        }
        const rest = args.slice(1);
        const fnArg = rest.length === 1 && (() => { const ax = (0, stmts_1.skipParens)(rest[0]); return ts.isArrowFunction(ax) || ts.isFunctionExpression(ax) || this.checker.getTypeAtLocation(rest[0]).getCallSignatures().length > 0; })();
        if ((name === 'replace' || name === 'replaceAll') && fnArg) {
            if (!re)
                (0, diag_1.reject)(call, 'no-regexp', `${name} with a replacer function and a regex value: the groups it is called with are not known`);
            return replaceWithFunction(this, call, callee.expression, re, rest[0], fc);
        }
        for (const a of rest) {
            const ax = (0, stmts_1.skipParens)(a);
            if (ts.isSpreadElement(a))
                (0, diag_1.reject)(a, 'extern-spread', `spread argument to String.${name}`);
            if (ts.isArrowFunction(ax) || ts.isFunctionExpression(ax) || this.checker.getTypeAtLocation(a).getCallSignatures().length) {
                (0, diag_1.reject)(a, 'extern-callback', `callback passed to the external function String.${name}`);
            }
        }
        if (name === 'matchAll' && args.length !== 1)
            (0, diag_1.reject)(call, 'no-regexp', 'String.matchAll takes one regex');
        const restTys = name === 'split' ? [ty_1.T.num] : [ty_1.T.str];
        if (rest.length > restTys.length)
            (0, diag_1.reject)(call, 'no-regexp', `String.${name} with ${args.length} arguments`);
        const vals = this.seq([() => this.lowerExpr(callee.expression, fc, ty_1.T.str), ...(re ? [] : [value(args[0])]),
            ...rest.map((a, i) => () => this.lowerExpr(a, fc, restTys[i]))], fc);
        const pf = re ? lit(re) : fields(vals.splice(1, 1)[0]);
        if (this.coverage)
            this.covExternals.add(`String.${name}`);
        // matchAll: its iterator as the array of the match results (consumed by for…of, spreads and
        // Array.from; the oracle answers a fresh array)
        const matchAllElem = () => {
            const it = this.checker.getTypeAtLocation(call);
            const targs = (it.flags & ts.TypeFlags.Object) ? this.checker.getTypeArguments(it) : [];
            const el = targs.length ? this.tyOf(targs[0], fc, call) : ty_1.T.ext('RegExpMatchArray');
            if (el.k !== 'ext')
                (0, diag_1.reject)(call, 'no-regexp', 'matchAll elements of an unexpected type');
            return el;
        };
        // match with a global regex answers the array of the matched strings (or null), not a match
        // object (TypeScript's lib types both as RegExpMatchArray): typed so where an array is
        // expected (e.g. `Array.from(s.match(re) ?? [])`); elsewhere the value keeps the lib's type
        const ret = name === 'replace' || name === 'replaceAll' ? ty_1.T.str : name === 'search' ? ty_1.T.num : name === 'split' ? ty_1.T.arr(ty_1.T.str)
            : name === 'matchAll' ? ty_1.T.arr(matchAllElem()) : name === 'match' && re && re.flags.includes('g') && exp && (exp.k === 'arr' || (exp.k === 'opt' && exp.t.k === 'arr')) ? ty_1.T.opt(ty_1.T.arr(ty_1.T.str)) : sig();
        if (name === 'split' && !re) {
            // the groups of a value's pattern are put into the result: an absent one (undefined, which
            // the type string[] excludes) panics
            const os = ty_1.T.opt(ty_1.T.str);
            const ps = [(0, ir_1.mkVar)('x', os), (0, ir_1.mkVar)('i', ty_1.T.num), (0, ir_1.mkVar)('a', ty_1.T.arr(os))];
            const unwrap = ir_1.E.lam(false, ps, ty_1.T.str, [(0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.unwrap(ir_1.E.var(ps[0]))))]);
            const got = ir_1.E.extern('String.split', [vals[0], ...pf, ...vals.slice(1)], ty_1.T.arr(os));
            return ir_1.E.builtin(`(.arrMap ${(0, ty_1.showTy)(os)} .str)`, [got, unwrap], [ty_1.T.arr(os), ty_1.T.fn([os, ty_1.T.num, ty_1.T.arr(os)], ty_1.T.str)], ty_1.T.arr(ty_1.T.str));
        }
        const ext = ir_1.E.extern(`String.${name}`, [vals[0], ...pf, ...vals.slice(1)], ret);
        // (a sticky value that is not global: match / replace read and write its lastIndex)
        return !re && (name === 'match' || name === 'replace') ? guardFlags(pf[1], 'y', 'g', ext) : ext;
    }
    void exp;
    return undefined;
};

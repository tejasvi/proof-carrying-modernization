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
exports.substKey = exports.isLibDecl = exports.ownerOf = exports.reject = exports.Reject = exports.ts = exports.Translator = exports.LEAN_RESERVED = exports.FnCtx = void 0;
exports.sanitizeIdent = sanitizeIdent;
exports.f64Lean = f64Lean;
exports.numLit = numLit;
exports.bigLit = bigLit;
exports.strLit = strLit;
exports.isLitUndef = isLitUndef;
exports.holdsTimer = holdsTimer;
exports.defaultValue = defaultValue;
exports.within = within;
// The translator: registries, function contexts, bindings and type conversions.
// Statement, expression and library lowering live in stmts.ts, exprs.ts and builtins.ts
// (they extend `Translator` through module augmentation; see index.ts).
const ts = __importStar(require("typescript"));
exports.ts = ts;
const ty_1 = require("./ty");
const ir_1 = require("./ir");
const diag_1 = require("./diag");
Object.defineProperty(exports, "Reject", { enumerable: true, get: function () { return diag_1.Reject; } });
Object.defineProperty(exports, "reject", { enumerable: true, get: function () { return diag_1.reject; } });
const analysis_1 = require("./analysis");
Object.defineProperty(exports, "ownerOf", { enumerable: true, get: function () { return analysis_1.ownerOf; } });
const types_1 = require("./types");
Object.defineProperty(exports, "substKey", { enumerable: true, get: function () { return types_1.substKey; } });
Object.defineProperty(exports, "isLibDecl", { enumerable: true, get: function () { return types_1.isLibDecl; } });
class FnCtx {
    parent;
    kind;
    async;
    bodyRet;
    subst;
    tsNode;
    thisVar = null;
    isCtor = false;
    jumps = [];
    scopes = [new Map()];
    pre = [];
    /** expressions already evaluated (bases of optional chains) */
    override = new Map();
    /** coverage mode: `this` of a class that cannot be represented */
    thisPoison = false;
    /** coverage mode: the return type could not be mapped */
    retPoison = false;
    constructor(parent, kind, async, bodyRet, subst, tsNode) {
        this.parent = parent;
        this.kind = kind;
        this.async = async;
        this.bodyRet = bodyRet;
        this.subst = subst;
        this.tsNode = tsNode;
    }
    bind(sym, b) { this.scopes[this.scopes.length - 1].set(sym, b); }
    push() { this.scopes.push(new Map()); }
    pop() { this.scopes.pop(); }
}
exports.FnCtx = FnCtx;
exports.LEAN_RESERVED = new Set([
    'def', 'fun', 'let', 'if', 'then', 'else', 'do', 'match', 'with', 'end', 'in', 'at', 'by', 'have', 'show', 'from',
    'open', 'import', 'namespace', 'section', 'variable', 'theorem', 'lemma', 'where', 'structure', 'class', 'instance',
    'mut', 'for', 'return', 'try', 'catch', 'finally', 'unless', 'break', 'continue', 'macro', 'syntax', 'deriving',
    'extends', 'abbrev', 'example', 'inductive', 'universe', 'local', 'private', 'protected', 'partial', 'noncomputable',
    'mutual', 'nomatch', 'Type', 'Prop', 'Sort', 'calc', 'suffices', 'obtain', 'axiom', 'opaque', 'set_option', 'attribute',
    'notation', 'infix', 'infixl', 'infixr', 'prefix', 'postfix', 'elab', 'scoped', 'export', 'omit', 'include', 'termination_by',
    'decreasing_by', 'unsafe', 'private', 'public', 'nofun', 'TT', 'program', 'mainBlock', 'StrictTS', 'true', 'false',
]);
function sanitizeIdent(s) {
    let r = s.replace(/[^A-Za-z0-9_]/g, '_');
    if (!/^[A-Za-z_]/.test(r))
        r = '_' + r;
    if (r === '_')
        r = '_x';
    return r;
}
/** Lean literal of a JavaScript number (exact binary64 value). */
function f64Lean(x) {
    if (Number.isNaN(x))
        return 'F64.nan';
    if (x === Infinity)
        return '(.inf false)';
    if (x === -Infinity)
        return '(.inf true)';
    if (Object.is(x, -0))
        return '(F64.zero true)';
    if (Number.isInteger(x) && Math.abs(x) <= 2 ** 53)
        return x >= 0 ? `${x}` : `(F64.ofInt (${x}))`;
    const dv = new DataView(new ArrayBuffer(8));
    dv.setFloat64(0, x);
    const hi = dv.getUint32(0), lo = dv.getUint32(4);
    const neg = (hi >>> 31) === 1;
    const bexp = (hi >>> 20) & 0x7ff;
    const frac = BigInt(hi & 0xfffff) * 4294967296n + BigInt(lo);
    const man = bexp === 0 ? frac : frac + 4503599627370496n;
    const exp = bexp === 0 ? -1074 : bexp - 1075;
    return `(F64.mkFin ${neg} ${man} (${exp}))`;
}
function numLit(x) { return ir_1.E.lit(`(.num ${f64Lean(x)})`, ty_1.T.num, x); }
function bigLit(x) { return ir_1.E.lit(`(.bigint ${x < 0n ? `(${x})` : x})`, ty_1.T.bigint, x); }
function strLit(s) { return ir_1.E.lit(`(.str ${(0, ty_1.leanJSStr)(s)})`, ty_1.T.str, s); }
function isLitUndef(e) { return e.k === 'lit' && e.ty.k === 'undef'; }
class Translator {
    program;
    diags;
    checker;
    analysis;
    types;
    funs = [];
    globals = [];
    funDocs = new Map();
    globalOf = new Map();
    instances = new Map();
    queue = [];
    usedLean = new Set(exports.LEAN_RESERVED);
    files = [];
    helpers = new Map();
    /** static fields of classes (globals) */
    staticFields = new Map();
    /** `a` in element writes `a[i] = v` to arrays from `new Array(n)` (no length check) */
    holeWrites = new Set();
    // ---- coverage mode (per-function subset coverage of real projects) ----
    coverage = false;
    /** source files of the project itself (coverage mode) */
    projectFiles = new Set();
    /** cells of top-level functions compared by identity, and their initialisations */
    fnBoxes = new Map();
    fnBoxInits = [];
    /** the original subset (`--strict` / `--no-dyn`): no values of type unknown/any */
    get strict() { return this.types.strict; }
    set strict(v) { this.types.strict = v; }
    /** module-level `const f = (…) => …` are functions where safe (liftedArrow; off in coverage mode) */
    liftConstArrows = true;
    liftSafe = new Map();
    /** diagnostics of the function under analysis */
    covDiags = [];
    /** external callees / values used by the function under analysis */
    covExternals = new Set();
    /** external types met by the function under analysis */
    covExtTypes = new Set();
    /** error-derived placeholders created so far (cascade detection) */
    poisonCount = 0;
    constructor(program, diags) {
        this.program = program;
        this.diags = diags;
        this.checker = program.getTypeChecker();
        this.analysis = new analysis_1.Analysis(this.checker);
        this.types = new types_1.TypeMapper(this.checker, program, this.analysis);
    }
    /** Record a coverage diagnostic. */
    covRecord(e, node) {
        if (e instanceof diag_1.Reject && e.extName)
            this.covExtTypes.add(e.extName);
        if (e instanceof diag_1.Reject)
            this.covDiags.push({ rule: e.rule, node: e.node ?? node, msg: e.message });
        else if (e instanceof ir_1.InternalError)
            this.covDiags.push({ rule: 'internal', node, msg: e.message });
        else if (e instanceof Error)
            this.covDiags.push({ rule: 'internal', node, msg: `translator error: ${e.message}` });
    }
    /** An error-derived placeholder for node `n` (typed when TypeScript's type maps). */
    poisonFor(n, fc, exp) {
        this.poisonCount++;
        if (exp)
            return ir_1.E.poison(exp);
        try {
            return ir_1.E.poison(this.tyAt(n, fc));
        }
        catch {
            return ir_1.E.poison(ty_1.T.undef);
        }
    }
    /** A well-typed stand-in for the value of a call that coverage mode does not translate
     * (calls of other project functions, external calls). */
    placeholderFor(n, fc, exp) {
        if (exp)
            return ir_1.E.unreachable(exp);
        try {
            return ir_1.E.unreachable(this.tyAt(n, fc));
        }
        catch {
            this.poisonCount++;
            return ir_1.E.poison(ty_1.T.undef);
        }
    }
    isProjectDecl(d) {
        return !!d && this.projectFiles.has(d.getSourceFile());
    }
    /** Name of an external (non-project, non-modelled) symbol for coverage reports. */
    externalName(sym) { return this.types.externalSymName(sym); }
    // -------------------------------------------------------------------------------------
    // names
    /** A fresh Lean name for a generated definition (printed with «» by the emitter, so
     * that names that are Lean keywords, like `repeat`, are fine). */
    leanName(base) {
        let b = sanitizeIdent(base);
        let n = b, i = 2;
        while (this.usedLean.has(n) || this.usedLean.has(n + 'Ref') || this.usedLean.has(n + 'Def') || this.usedLean.has(n + '_call'))
            n = `${b}_${i++}`;
        this.usedLean.add(n);
        return n;
    }
    newFun(name, leanBase, params, bodyRet, async) {
        const f = {
            idx: this.funs.length, name, leanName: this.leanName(leanBase), params,
            ret: async ? ty_1.T.promise(bodyRet) : bodyRet, async, bodyRet, body: null,
        };
        this.funs.push(f);
        return f;
    }
    newGlobal(name, ty) {
        const g = { idx: this.globals.length, name, leanName: this.leanName('g_' + name), ty };
        this.globals.push(g);
        return g;
    }
    // -------------------------------------------------------------------------------------
    // types
    tyOf(t, fc, node) {
        return this.types.map(t, fc ? fc.subst : new Map(), node);
    }
    tyAt(node, fc) {
        return this.tyOf(this.checker.getTypeAtLocation(node), fc, node);
    }
    aliasOf(n) {
        const t = this.types.aliases.get(n);
        if (!t)
            throw new ir_1.InternalError(`unknown named type ${n}`);
        return t;
    }
    /** Structure of a possibly named type. */
    unfoldTy(t) { return t.k === 'named' ? this.unfoldTy(this.aliasOf(t.n)) : t; }
    /** Unfold a value of named type until it is not named. */
    unfoldE(e) {
        if ((0, ir_1.isPoison)(e))
            return e.ty.k === 'named' ? ir_1.E.poison(this.unfoldTy(e.ty)) : e;
        while (e.ty.k === 'named')
            e = ir_1.E.unfold(e.ty.n, e, this.aliasOf(e.ty.n));
        return e;
    }
    isNeverType(t) { return !!(t.flags & ts.TypeFlags.Never); }
    fieldsOfObj(c) {
        const fs = this.types.classFields.get(c);
        if (!fs)
            throw new ir_1.InternalError(`unknown class ${c}`);
        return fs;
    }
    // -------------------------------------------------------------------------------------
    // symbols and bindings
    resolveSym(sym) {
        if (sym && (sym.flags & ts.SymbolFlags.Alias))
            return this.checker.getAliasedSymbol(sym);
        return sym;
    }
    symAt(id) {
        if (ts.isIdentifier(id)) {
            const ps = (0, analysis_1.paramSymbol)(this.checker, id);
            if (ps)
                return ps;
        }
        if (id.parent && ts.isShorthandPropertyAssignment(id.parent) && id.parent.name === id) {
            return this.resolveSym(this.checker.getShorthandAssignmentValueSymbol(id.parent));
        }
        return this.resolveSym(this.checker.getSymbolAtLocation(id));
    }
    lookup(sym, fc) {
        for (let c = fc; c; c = c.parent) {
            for (let i = c.scopes.length - 1; i >= 0; i--) {
                const b = c.scopes[i].get(sym);
                if (b)
                    return b;
            }
            if (c.kind !== 'lambda')
                break;
        }
        const g = this.globalOf.get(sym);
        if (g)
            return { k: 'global', g };
        const gp = this.globalPoison.get(sym);
        if (gp) {
            // coverage mode: a module-level variable without IR type; its reason is a violation
            // of every function that uses it
            if (!this.covDiags.some(d => d.node === gp.node && d.rule === gp.rule)) {
                this.covDiags.push({ rule: gp.rule, node: gp.node, msg: gp.msg });
                if (gp.extName)
                    this.covExtTypes.add(gp.extName);
            }
            return { k: 'poison', ty: ty_1.T.undef };
        }
        return undefined;
    }
    /** coverage mode: module-level variables whose type has no IR representation */
    globalPoison = new Map();
    facts(sym) { return this.analysis.vars.get(sym); }
    /** Is the variable reassigned after its declaration? */
    isReassigned(sym) { return (this.facts(sym)?.writes.length ?? 0) > 0; }
    /** Does the variable need a box (captured by a closure and reassigned)? */
    needsBox(sym) {
        const f = this.facts(sym);
        if (!f || !f.captured || f.writes.length === 0)
            return false;
        const loop = this.forHeadLoop(f.decl);
        if (loop && f.capturedRefs.every(r => within(r, loop.statement)) && f.writes.every(w => !within(w, loop.statement)))
            return false;
        return true;
    }
    /** The `for (let …; …; …)` statement whose initialiser declares `decl`, if any. */
    forHeadLoop(decl) {
        let n = decl;
        while (n && !ts.isVariableDeclarationList(n))
            n = n.parent;
        if (n && n.parent && ts.isForStatement(n.parent) && n.parent.initializer === n)
            return n.parent;
        return undefined;
    }
    /** Is `sym` written anywhere inside `region`? */
    writtenWithin(sym, region) {
        const f = this.facts(sym);
        if (!f)
            return false;
        const regions = Array.isArray(region) ? region : [region];
        return f.writes.some(w => regions.some(r => within(w, r)));
    }
    /** A local binding for a declared variable; boxes captured reassigned variables. */
    declareLocal(sym, name, ty, init, fc, out) {
        const g = fc.kind === 'main' ? this.globalOf.get(sym) : undefined;
        if (g) {
            out.push((0, ir_1.stmtItem)(ir_1.S.gset(g, this.coerce(init, g.ty, sym.valueDeclaration ?? fc.tsNode))));
            return { k: 'global', g };
        }
        if (this.needsBox(sym)) {
            const v = (0, ir_1.mkVar)(name, ty_1.T.box(ty));
            out.push((0, ir_1.declItem)(v, ir_1.E.builtin(`(.boxNew ${(0, ty_1.showTy)(ty)})`, [init], [ty], ty_1.T.box(ty))));
            const b = { k: 'box', v, t: ty };
            fc.bind(sym, b);
            return b;
        }
        const v = (0, ir_1.mkVar)(name, ty, this.isReassigned(sym));
        out.push((0, ir_1.declItem)(v, init));
        const b = { k: 'var', v };
        fc.bind(sym, b);
        return b;
    }
    /** Read a binding (the stored type, before adapting to TypeScript's narrowed type). */
    readBinding(b, node) {
        switch (b.k) {
            case 'var': return ir_1.E.var(b.v);
            case 'box': return ir_1.E.builtin(`(.boxGet ${(0, ty_1.showTy)(b.t)})`, [ir_1.E.var(b.v)], [ty_1.T.box(b.t)], b.t);
            case 'optInit': return ir_1.E.unwrap(ir_1.E.var(b.v));
            case 'global': return ir_1.E.gget(b.g);
            case 'lifted': (0, diag_1.reject)(node, 'unsupported', 'a nested function used as a value must be called');
            case 'poison': return ir_1.E.poison(b.ty);
            case 'boxOpt': return ir_1.E.unwrap(ir_1.E.builtin(`(.boxGet ${(0, ty_1.showTy)(ty_1.T.opt(b.t))})`, [ir_1.E.var(b.v)], [ty_1.T.box(ty_1.T.opt(b.t))], ty_1.T.opt(b.t)));
        }
    }
    /** The stored type of a binding. */
    bindingTy(b) {
        switch (b.k) {
            case 'var': return b.v.ty;
            case 'box': return b.t;
            case 'optInit': return b.v.ty.t;
            case 'global': return b.g.ty;
            case 'lifted': return ty_1.T.undef;
            case 'poison': return b.ty;
            case 'boxOpt': return b.t;
        }
    }
    // -------------------------------------------------------------------------------------
    // ANF helpers
    /** Bind `e` to a fresh constant in the current pre-list unless it is stable. */
    spill(e, fc, name = 't') {
        if ((0, ir_1.isStable)(e))
            return e;
        const v = (0, ir_1.mkVar)(name, e.ty);
        fc.pre.push((0, ir_1.declItem)(v, e));
        return ir_1.E.var(v);
    }
    /** Always bind `e` to a fresh constant. */
    bindTemp(e, fc, name = 't') {
        if (e.k === 'var' && (0, ir_1.isStable)(e))
            return e.v;
        const v = (0, ir_1.mkVar)(name, e.ty);
        fc.pre.push((0, ir_1.declItem)(v, e));
        return v;
    }
    /** Evaluate thunks in order; when a later one emits pre-items, earlier unstable results
     * are bound to temporaries first (preserving JavaScript's left-to-right order). */
    seq(thunks, fc) {
        const res = [];
        for (const th of thunks) {
            const mark = fc.pre.length;
            const e = th();
            if (fc.pre.length > mark) {
                const spills = [];
                for (let j = 0; j < res.length; j++) {
                    if (!(0, ir_1.isStable)(res[j])) {
                        const v = (0, ir_1.mkVar)('t', res[j].ty);
                        spills.push((0, ir_1.declItem)(v, res[j]));
                        res[j] = ir_1.E.var(v);
                    }
                }
                fc.pre.splice(mark, 0, ...spills);
            }
            res.push(e);
        }
        return res;
    }
    /** Run `f` with a fresh pre-list; returns the result and the items it emitted. */
    isolate(fc, f) {
        const saved = fc.pre;
        fc.pre = [];
        try {
            const r = f();
            return [r, fc.pre];
        }
        finally {
            fc.pre = saved;
        }
    }
    /** A mutable temporary of type `t` with an initial value; for types without a default
     * value the temporary has type `opt t` (read with `unwrap`). */
    mutTemp(t, fc) {
        const dflt = defaultValue(t);
        if (dflt) {
            const v = (0, ir_1.mkVar)('r', t, true);
            fc.pre.push((0, ir_1.declItem)(v, dflt));
            return { v, set: e => (0, ir_1.stmtItem)(ir_1.S.assign(v, e)), get: () => ir_1.E.var(v) };
        }
        const v = (0, ir_1.mkVar)('r', ty_1.T.opt(t), true);
        fc.pre.push((0, ir_1.declItem)(v, ir_1.E.none(t)));
        return { v, set: e => (0, ir_1.stmtItem)(ir_1.S.assign(v, ir_1.E.some(e))), get: () => ir_1.E.unwrap(ir_1.E.var(v)) };
    }
    // -------------------------------------------------------------------------------------
    // conversions
    coerce(e, to, node) {
        if ((0, ty_1.tyEq)(e.ty, to))
            return e;
        const r = this.convert(e, to, node, false, 0);
        if (r)
            return r;
        this.conversionError(e.ty, to, node);
    }
    /** Is the value converted at `node` of a dictionary type with named properties? */
    copiesNamedDict(node) {
        let st;
        try {
            st = this.checker.getTypeAtLocation(node);
        }
        catch {
            st = undefined;
        }
        return !!st && this.types.isNamedDict(st);
    }
    conversionError(from, to, node) {
        const f = this.unfoldTy(from), t = this.unfoldTy(to);
        if (f.k === 'dict' && t.k === 'record' && this.copiesNamedDict(node)) {
            (0, diag_1.reject)(node, 'unsupported-conversion', `${(0, ty_1.prettyTy)(from)} with named properties used as the record type ${(0, ty_1.prettyTy)(to)}: a copy would not show later writes through the dictionary`);
        }
        const cellOf = (x) => x.k === 'box' && x.t.k === 'record' ? x.t : x.k === 'opt' ? cellOf(x.t) : x.k === 'union' ? x.ts.map(cellOf).find(y => !!y) : undefined;
        const cell = cellOf(t);
        if (cell && (f.k === 'record' || (f.k === 'box' && f.t.k === 'record'))) {
            (0, diag_1.reject)(node, 'record-identity', `a value of type ${(0, ty_1.prettyTy)(from)} used where objects of type ${(0, ty_1.prettyTy)(cell)} are compared by identity ` +
                '(it would be a second object to StrictTS)');
        }
        if (t.k === 'obj' && (f.k === 'record' || (f.k === 'obj' && f.c !== t.c)) && !this.types.classes.has(t.c)) {
            (0, diag_1.reject)(node, 'record-mutation', `${(0, ty_1.prettyTy)(from)} flows into ${t.c}, an object type whose fields are assigned somewhere; ` +
                'mutation through width subtyping is not allowed (values of record types are immutable)');
        }
        if (t.k === 'obj' && f.k === 'obj' && f.c !== t.c)
            (0, diag_1.reject)(node, 'unsupported-conversion', `class ${f.c} used as ${t.c} (classes are nominal)`);
        if ((t.k === 'record' && f.k === 'obj'))
            (0, diag_1.reject)(node, 'unsupported-conversion', `heap object ${f.c} used as the record type ${(0, ty_1.prettyTy)(to)} (no width subtyping for objects)`);
        if (f.k === 'arr' && t.k === 'arr')
            (0, diag_1.reject)(node, 'unsupported-conversion', `array covariance: ${(0, ty_1.prettyTy)(from)} used as ${(0, ty_1.prettyTy)(to)} (arrays are mutable; copy the array)`);
        (0, diag_1.reject)(node, 'unsupported-conversion', `cannot convert ${(0, ty_1.prettyTy)(from)} to ${(0, ty_1.prettyTy)(to)} here`);
    }
    /** Coerce, or narrow to TypeScript's narrowed type at a read. */
    adapt(e, to, node) {
        if ((0, ty_1.tyEq)(e.ty, to))
            return e;
        const r = this.convert(e, to, node, true, 0);
        if (r)
            return r;
        this.conversionError(e.ty, to, node);
    }
    /** Evaluate `e` once and continue with a variable holding its value. */
    withValue(e, name, k) {
        if ((0, ir_1.isStable)(e) && (e.k === 'var' || e.k === 'lit'))
            return k(e);
        const v = (0, ir_1.mkVar)(name, e.ty);
        return ir_1.E.letE(v, e, k(ir_1.E.var(v)));
    }
    /** The record in an object cell (identity.ts). */
    unboxCell(e) {
        const rt = e.ty.t;
        return ir_1.E.builtin(`(.boxGet ${(0, ty_1.showTy)(rt)})`, [e], [e.ty], rt);
    }
    /** Does a value of type `t` hold cells of functions or records compared by identity
     * (identity.ts; only of records with `recordsOnly`)? (Not counting the parameters and results
     * of functions in it.) */
    holdsIdBox(t, recordsOnly = false, seen = new Set()) {
        const r = (x) => this.holdsIdBox(x, recordsOnly, seen);
        switch (t.k) {
            case 'box': return t.t.k === 'record' || (t.t.k === 'fn' && !recordsOnly) || r(t.t);
            case 'named': {
                if (seen.has(t.n))
                    return false;
                seen.add(t.n);
                return r(this.aliasOf(t.n));
            }
            case 'arr':
            case 'set':
            case 'opt':
            case 'promise':
            case 'dict': return r(t.t);
            case 'map': return r(t.key) || r(t.val);
            case 'tup':
            case 'union': return t.ts.some(r);
            case 'record': return t.fs.some(f => r(f.ty));
            default: return false;
        }
    }
    /** The closure in a function cell (identity.ts). */
    unboxFn(e) {
        const ft = e.ty.t;
        return ir_1.E.builtin(`(.boxGet ${(0, ty_1.showTy)(ft)})`, [e], [e.ty], ft);
    }
    /** The cell of a top-level function compared by identity: one module variable, set when the
     * module starts (before its body: function declarations are hoisted). */
    fnBox(f) {
        const known = this.fnBoxes.get(f);
        if (known)
            return known;
        const ft = ty_1.T.fn(f.params.map(p => p.ty), f.ret);
        const g = this.newGlobal(`${f.name}$fn`, ty_1.T.box(ft));
        this.fnBoxes.set(f, g);
        this.fnBoxInits.push((0, ir_1.stmtItem)(ir_1.S.gset(g, ir_1.E.builtin(`(.boxNew ${(0, ty_1.showTy)(ft)})`, [ir_1.E.funVal(f)], [ft], ty_1.T.box(ft)))));
        return g;
    }
    /** Does a value of type `t` hold objects whose `toString` / `valueOf` is not the one of
     * `Object.prototype` (class methods, fields of mutable objects with these names)? */
    customToPrimitive(t, seen = new Set()) {
        switch (t.k) {
            case 'obj': {
                if (seen.has(t.c))
                    return false;
                seen.add(t.c);
                const special = (n) => n === 'toString' || n === 'valueOf';
                const ci = this.types.classes.get(t.c);
                if (ci && ci.decl.members.some(m => !!m.name && ts.isIdentifier(m.name) && special(m.name.text)))
                    return true;
                const info = this.classOfObj(t.c);
                return !!info && (info.fields.some(f => special(f.name)) || info.fields.some(f => this.customToPrimitive(f.ty, seen)));
            }
            case 'named': {
                if (seen.has('named:' + t.n))
                    return false;
                seen.add('named:' + t.n);
                return this.customToPrimitive(this.aliasOf(t.n), seen);
            }
            case 'arr':
            case 'opt':
            case 'dict': return this.customToPrimitive(t.t, seen);
            case 'tup':
            case 'union': return t.ts.some(x => this.customToPrimitive(x, seen));
            case 'record': return t.fs.some(f => this.customToPrimitive(f.ty, seen));
            default: return false;
        }
    }
    /** An unknown value at type `to`: a checked cast; a record from a dictionary of unknown
     * values (JSON objects) as well as from a record value. */
    fromDyn(e, to, node) {
        // (an unknown value may be an object the program already holds in a cell)
        if (this.holdsIdBox(to))
            (0, diag_1.reject)(node, 'record-identity', `an unknown value used as ${(0, ty_1.prettyTy)(to)}, whose functions or objects are compared by identity`);
        const cast = (x, t) => ir_1.E.prim(`(.dynCast ${(0, ty_1.showTy)(t)})`, [x], [ty_1.T.dyn], ty_1.T.opt(t));
        if (this.unfoldTy(to).k !== 'record')
            return ir_1.E.unwrap(cast(e, to));
        const dd = ty_1.T.dict(ty_1.T.dyn);
        return this.withValue(e, 'u', x => {
            const r = (0, ir_1.mkVar)('r', to), d = (0, ir_1.mkVar)('d', dd);
            return ir_1.E.caseOpt(cast(x, to), ir_1.E.caseOpt(cast(x, dd), ir_1.E.unreachable(to), d, this.dictToRecord(ir_1.E.var(d), to, node)), r, ir_1.E.var(r));
        });
    }
    /** The record of type `to` from a dictionary of unknown values: each field read by name and
     * cast (absent: `undefined`, a panic for a required field). Fields holding typed arrays or
     * maps are not converted (that would copy them). */
    dictToRecord(e, to, node) {
        const rt = this.unfoldTy(to);
        const copies = (t) => {
            const u = this.unfoldTy(t);
            switch (u.k) {
                case 'tarr': return true;
                case 'arr':
                case 'set':
                case 'dict': return this.unfoldTy(u.t).k !== 'dyn';
                case 'map': return true;
                case 'opt': return copies(u.t);
                case 'union': return u.ts.some(copies);
                case 'record': return u.fs.some(f => copies(f.ty));
                default: return false;
            }
        };
        if (copies(rt))
            (0, diag_1.reject)(node, 'unsupported-conversion', `${(0, ty_1.prettyTy)(to)} from a dictionary of unknown values (typed arrays and maps in it would be copies)`);
        const dd = ty_1.T.dict(ty_1.T.dyn);
        const built = this.withValue(e, 'd', d => ir_1.E.mkRec(rt, rt.fs.map(f => {
            const got = ir_1.E.builtin('(.dictGet .dyn)', [d, strLit(f.name)], [dd, ty_1.T.str], ty_1.T.opt(ty_1.T.dyn));
            if (f.ty.k === 'opt') {
                const x = (0, ir_1.mkVar)('x', ty_1.T.dyn);
                return ir_1.E.caseOpt(got, ir_1.E.none(f.ty.t), x, ir_1.E.some(this.fromDyn(ir_1.E.var(x), f.ty.t, node)));
            }
            return this.fromDyn(ir_1.E.unwrap(got), f.ty, node);
        })));
        return to.k === 'named' ? ir_1.E.fold(to.n, built) : built;
    }
    convert(e, to, node, narrow, depth) {
        if ((0, ir_1.isPoison)(e))
            return ir_1.E.poison(to);
        const from = e.ty;
        if ((0, ty_1.tyEq)(from, to))
            return e;
        if (depth > 12)
            return null;
        const rec = (x, t, nw = narrow) => this.convert(x, t, node, nw, depth + 1);
        // unknown: an upcast keeps the value with its type; a downcast (narrowing or `as`, which
        // TypeScript checked) is a checked cast that panics on a mismatch
        // functions compared by identity (identity.ts): a cell is read where a plain function is
        // expected; a plain function never becomes a cell here (that could make two cells for one
        // function object: cells are created only where JavaScript creates the function)
        if (from.k === 'box' && from.t.k === 'fn' && (to.k === 'fn' || to.k === 'dyn'))
            return rec(this.unboxFn(e), to);
        if (to.k === 'box' && to.t.k === 'fn' && from.k === 'fn') {
            (0, diag_1.reject)(node, 'fn-identity', `a function of type ${(0, ty_1.prettyTy)(from)} used where functions are compared by identity (${(0, ty_1.prettyTy)(to.t)})`);
        }
        // records compared by identity: likewise, the cell is read where a record (of this or a
        // narrower type) or an unknown value is expected; a record never becomes a cell here, nor
        // a cell one of another record type (conversionError says why)
        if (from.k === 'box' && from.t.k === 'record' && (to.k === 'record' || to.k === 'dyn' || (to.k === 'named' && this.unfoldTy(to).k === 'record'))) {
            return rec(this.unboxCell(e), to);
        }
        if (to.k === 'box' && to.t.k === 'record' && (from.k === 'record' || from.k === 'box'))
            return null;
        if (to.k === 'dyn') {
            // (String(x) of an unknown value assumes Object.prototype.toString for objects)
            if (this.customToPrimitive(from))
                (0, diag_1.reject)(node, 'unsupported-conversion', `${(0, ty_1.prettyTy)(from)} as unknown: an object with its own toString/valueOf`);
            if (this.holdsIdBox(from))
                (0, diag_1.reject)(node, 'record-identity', `${(0, ty_1.prettyTy)(from)} as unknown: it holds functions or objects compared by identity`);
            if (holdsTimer(from))
                (0, diag_1.reject)(node, 'timer-handle', `${(0, ty_1.prettyTy)(from)} as unknown: a Node timer handle (an object in Node, a number here)`);
            return ir_1.E.prim(`(.toDyn ${(0, ty_1.showTy)(from)})`, [e], [from], ty_1.T.dyn);
        }
        if (from.k === 'dyn')
            return this.fromDyn(e, to, node);
        // a dictionary of unknown values (a JSON object, Firestore's DocumentData) as a record (a
        // copy; not of a dictionary type with named properties, which the program writes through)
        if (from.k === 'dict' && from.t.k === 'dyn' && this.unfoldTy(to).k === 'record') {
            return this.copiesNamedDict(node) ? null : this.dictToRecord(e, to, node);
        }
        if (from.k === 'named')
            return rec(ir_1.E.unfold(from.n, e, this.aliasOf(from.n)), to);
        if (to.k === 'named') {
            const inner = rec(e, this.aliasOf(to.n));
            return inner && ir_1.E.fold(to.n, inner);
        }
        switch (to.k) {
            case 'opt': {
                if (from.k === 'undef')
                    return isLitUndef(e) ? ir_1.E.none(to.t) : this.withValue(e, 'u', () => ir_1.E.none(to.t));
                // (`undefined | undefined`: undefined either way)
                if (from.k === 'opt' && from.t.k === 'undef')
                    return this.withValue(e, 'u', () => ir_1.E.none(to.t));
                if (from.k === 'opt') {
                    const v = (0, ir_1.mkVar)('x', from.t);
                    const inner = rec(ir_1.E.var(v), to.t);
                    if (inner)
                        return ir_1.E.caseOpt(e, ir_1.E.none(to.t), v, ir_1.E.some(inner));
                    break;
                }
                const inner = rec(e, to.t, false);
                if (inner)
                    return ir_1.E.some(inner);
                break;
            }
            case 'union': {
                const i = to.ts.findIndex(m => (0, ty_1.tyEq)(m, from));
                if (i >= 0)
                    return ir_1.E.inj(to, i, e);
                if (from.k === 'union') {
                    const alts = [];
                    let ok = true;
                    for (const m of from.ts) {
                        const v = (0, ir_1.mkVar)('m', m);
                        const b = rec(ir_1.E.var(v), to);
                        if (!b) {
                            ok = false;
                            break;
                        }
                        alts.push({ v, body: b });
                    }
                    if (ok)
                        return ir_1.E.caseU(e, alts);
                    break;
                }
                // a member the value converts to; when several members accept it the choice would
                // be a guess (TypeScript's structural typing does not decide it), so it is rejected
                const cands = [];
                for (let j = 0; j < to.ts.length; j++) {
                    const inner = rec(e, to.ts[j], false);
                    if (inner)
                        cands.push([j, inner]);
                }
                if (cands.length === 1)
                    return ir_1.E.inj(to, cands[0][0], cands[0][1]);
                if (cands.length > 1) {
                    // prefer a member of the same kind with exactly the same field names
                    const f = this.unfoldTy(from);
                    const same = cands.filter(([j]) => {
                        const m = this.unfoldTy(to.ts[j]);
                        return m.k === f.k && (m.k !== 'record' || (f.k === 'record' && m.fs.map(x => x.name).join() === f.fs.map(x => x.name).join()));
                    });
                    if (same.length === 1)
                        return ir_1.E.inj(to, same[0][0], same[0][1]);
                    (0, diag_1.reject)(node, 'unsupported-conversion', `${(0, ty_1.prettyTy)(from)} fits several members of ${(0, ty_1.prettyTy)(to)}; annotate the value with one member type`);
                }
                break;
            }
            case 'str':
                if (from.k === 'enum')
                    return ir_1.E.prim(`(.enumToStr [${from.cases.map(ty_1.leanStrLit).join(', ')}])`, [e], [from], ty_1.T.str);
                break;
            case 'enum':
                if (from.k === 'enum' && from.cases.every(c => to.cases.includes(c))) {
                    return this.withValue(e, 'k', x => {
                        let acc = ir_1.E.enumLit(to, to.cases.indexOf(from.cases[from.cases.length - 1]));
                        for (let i = from.cases.length - 2; i >= 0; i--) {
                            acc = ir_1.E.cond(ir_1.E.seq(x, ir_1.E.enumLit(from, i)), ir_1.E.enumLit(to, to.cases.indexOf(from.cases[i])), acc);
                        }
                        return acc;
                    });
                }
                if (from.k === 'str' && e.k === 'lit' && typeof e.js === 'string' && to.cases.includes(e.js)) {
                    return ir_1.E.enumLit(to, to.cases.indexOf(e.js));
                }
                break;
            case 'record':
                if (from.k === 'record') {
                    return this.projectRecord(e, from.fs, to.fs, node, narrow, depth);
                }
                break;
            case 'tup':
                if (from.k === 'arr' && to.ts.every(x => (0, ty_1.tyEq)(x, from.t))) {
                    // an array TypeScript types as a tuple (e.g. the value of Promise.all); reading a
                    // missing element panics
                    return this.withValue(e, 'a', x => ir_1.E.mkTup(to.ts.map((_, i) => ir_1.E.builtin(`(.arrGet ${(0, ty_1.showTy)(from.t)})`, [x, numLit(i)], [from, ty_1.T.num], from.t))));
                }
                if (from.k === 'tup' && from.ts.length === to.ts.length) {
                    let ok = true;
                    const r = this.withValue(e, 'p', x => {
                        const parts = [];
                        for (let i = 0; i < to.ts.length; i++) {
                            const c = rec(ir_1.E.getTup(x, i), to.ts[i]);
                            if (!c) {
                                ok = false;
                                return x;
                            }
                            parts.push(c);
                        }
                        return ir_1.E.mkTup(parts);
                    });
                    if (ok)
                        return r;
                }
                break;
            case 'fn':
                if (from.k === 'fn')
                    return this.wrapFn(e, from, to, node, depth);
                break;
            case 'arr':
                if (from.k === 'tup') {
                    // a tuple value used as an array: a fresh array of its elements
                    let ok = true;
                    const r = this.withValue(e, 'p', x => {
                        const parts = [];
                        for (let i = 0; i < from.ts.length; i++) {
                            const c = rec(ir_1.E.getTup(x, i), to.t, false);
                            if (!c) {
                                ok = false;
                                return x;
                            }
                            parts.push(c);
                        }
                        return ir_1.E.builtin(`(.arrOf ${(0, ty_1.showTy)(to.t)} ${parts.length})`, parts, parts.map(() => to.t), to);
                    });
                    if (ok)
                        return r;
                }
                break;
        }
        if (narrow)
            return this.narrowTo(e, to, node, depth);
        return null;
    }
    projectRecord(e, fromFs, toFs, node, narrow, depth) {
        for (const f of toFs) {
            if (!fromFs.some(g => g.name === f.name) && f.ty.k !== 'opt')
                return null;
        }
        let ok = true;
        const r = this.withValue(e, 'r', x => {
            const parts = [];
            for (const f of toFs) {
                const gi = fromFs.findIndex(g => g.name === f.name);
                if (gi < 0) {
                    parts.push(ir_1.E.none(f.ty.t));
                    continue;
                }
                const c = this.convert(ir_1.E.getRec(x, gi), f.ty, node, narrow, depth + 1);
                if (!c) {
                    ok = false;
                    return x;
                }
                parts.push(c);
            }
            return ir_1.E.mkRec(ty_1.T.record(toFs), parts);
        });
        return ok ? r : null;
    }
    /** Adapt a function value to another function type (JavaScript call semantics: extra
     * arguments are dropped, missing optional parameters receive `undefined`). */
    wrapFn(e, from, to, node, depth) {
        const params = to.args.map((t, i) => (0, ir_1.mkVar)(`a${i}`, t));
        const args = [];
        for (let i = 0; i < from.args.length; i++) {
            if (i < to.args.length) {
                const c = this.convert(ir_1.E.var(params[i]), from.args[i], node, false, depth + 1);
                if (!c)
                    return null;
                args.push(c);
            }
            else if (from.args[i].k === 'opt')
                args.push(ir_1.E.none(from.args[i].t));
            else if (from.args[i].k === 'undef')
                args.push(ir_1.E.undef());
            else if (from.args[i].k === 'dyn')
                args.push(ir_1.E.prim('(.toDyn .undef)', [ir_1.E.undef()], [ty_1.T.undef], ty_1.T.dyn));
            else
                return null;
        }
        const mk = (f) => {
            const call = f.k === 'funVal' ? ir_1.E.call(f.f, args) : ir_1.E.app(f, args);
            let body;
            if (to.ret.k === 'undef' && from.ret.k !== 'undef')
                body = [(0, ir_1.stmtItem)(ir_1.S.expr(call))];
            else {
                const r = this.convert(call, to.ret, node, false, depth + 1);
                if (!r)
                    return null;
                body = [(0, ir_1.stmtItem)(ir_1.S.ret(r))];
            }
            return ir_1.E.lam(false, params, to.ret, body);
        };
        if (e.k === 'funVal' || (e.k === 'var' && (0, ir_1.isStable)(e)))
            return mk(e);
        const v = (0, ir_1.mkVar)('f', e.ty);
        const inner = mk(ir_1.E.var(v));
        return inner && ir_1.E.letE(v, e, inner);
    }
    /** Narrowing conversions (TypeScript proved the value has the narrower type; other
     * cases panic). */
    narrowTo(e, to, node, depth) {
        const from = e.ty;
        const rec = (x, t) => this.convert(x, t, node, true, depth + 1);
        if (from.k === 'opt') {
            if (to.k === 'undef')
                return this.withValue(e, 'u', () => ir_1.E.undef());
            if (to.k === 'opt') {
                const v = (0, ir_1.mkVar)('x', from.t);
                const inner = rec(ir_1.E.var(v), to.t);
                return inner && ir_1.E.caseOpt(e, ir_1.E.none(to.t), v, ir_1.E.some(inner));
            }
            return rec(ir_1.E.unwrap(e), to);
        }
        if (from.k === 'union') {
            // members of the narrowed type keep their value; TypeScript proved the others impossible
            const alts = [];
            let any = false;
            for (const m of from.ts) {
                const v = (0, ir_1.mkVar)('m', m);
                const b = this.memberMatches(m, to) ? this.convert(ir_1.E.var(v), to, node, true, depth + 1) : null;
                if (b)
                    any = true;
                alts.push({ v, body: b ?? ir_1.E.unreachable(to) });
            }
            return any ? ir_1.E.caseU(e, alts) : null;
        }
        if (from.k === 'str' && to.k === 'enum') {
            // a string TypeScript narrowed to a literal union (e.g. a discriminant)
            return this.withValue(e, 'k', x => {
                let acc = ir_1.E.unreachable(to);
                for (let i = to.cases.length - 1; i >= 0; i--)
                    acc = ir_1.E.cond(ir_1.E.seq(x, strLit(to.cases[i])), ir_1.E.enumLit(to, i), acc);
                return acc;
            });
        }
        if (from.k === 'enum' && to.k === 'enum' && to.cases.every(c => from.cases.includes(c))) {
            // through the case name (an equality on `from` would repeat its case list in every test)
            return rec(ir_1.E.prim(`(.enumToStr [${from.cases.map(ty_1.leanStrLit).join(', ')}])`, [e], [from], ty_1.T.str), to);
        }
        return null;
    }
    /** Does union member `m` belong to the narrowed type `to` (same type, a member of a
     * narrower union, a string-like member of a string type, or a narrowable optional)? */
    memberMatches(m, to) {
        const mu = this.unfoldTy(m), tu = this.unfoldTy(to);
        if ((0, ty_1.tyEq)(m, to) || (0, ty_1.tyEq)(mu, tu))
            return true;
        if (tu.k === 'union')
            return tu.ts.some(x => this.memberMatches(m, x));
        if (tu.k === 'opt')
            return mu.k === 'undef' || this.memberMatches(m, tu.t);
        if ((mu.k === 'enum' || mu.k === 'str') && (tu.k === 'str' || tu.k === 'enum'))
            return true;
        if (mu.k === 'union')
            return mu.ts.some(x => this.memberMatches(x, to));
        if (mu.k === 'arr' && tu.k === 'tup')
            return true;
        return false;
    }
    // -------------------------------------------------------------------------------------
    // helpers used by several lowering files
    /** The JavaScript `typeof` tag of values of a type (for narrowing). */
    typeofTag(t) {
        const u = this.unfoldTy(t);
        switch (u.k) {
            case 'num': return 'number';
            case 'bigint': return 'bigint';
            case 'bool': return 'boolean';
            case 'str':
            case 'enum': return 'string';
            case 'undef': return 'undefined';
            case 'fn': return 'function';
            case 'box': return u.t.k === 'fn' ? 'function' : 'object';
            default: return 'object';
        }
    }
    translateProgram() { throw new ir_1.InternalError('installed by index.ts'); }
}
exports.Translator = Translator;
/** Does a value of type `t` hold a Node timer handle (TIMER_TY)? */
function holdsTimer(t) {
    switch (t.k) {
        case 'record': return (0, ty_1.tyEq)(t, ty_1.TIMER_TY) || t.fs.some(f => holdsTimer(f.ty));
        case 'arr':
        case 'set':
        case 'opt':
        case 'promise':
        case 'dict':
        case 'box': return holdsTimer(t.t);
        case 'map': return holdsTimer(t.key) || holdsTimer(t.val);
        case 'tup':
        case 'union': return t.ts.some(holdsTimer);
        default: return false;
    }
}
function defaultValue(t) {
    switch (t.k) {
        case 'num': return numLit(0);
        case 'bigint': return bigLit(0n);
        case 'bool': return ir_1.E.bool(false);
        case 'str': return strLit('');
        case 'undef': return ir_1.E.undef();
        case 'opt': return ir_1.E.none(t.t);
        default: return null;
    }
}
function within(n, region) {
    return n.pos >= region.pos && n.end <= region.end && n.getSourceFile() === region.getSourceFile();
}

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
// Calls: user functions, methods, closures, and the JavaScript library (Math, String,
// Array, Map, Set, Promise, console, timers). JavaScript's argument defaults are made
// explicit and callbacks are eta-expanded to the arity JavaScript calls them with.
const ts = __importStar(require("typescript"));
const ty_1 = require("./ty");
const ir_1 = require("./ir");
const diag_1 = require("./diag");
const core_1 = require("./core");
const exprs_1 = require("./exprs");
const stmts_1 = require("./stmts");
const P = core_1.Translator.prototype;
const SK = ts.SyntaxKind;
const B = (op, args, argTys, ret) => ir_1.E.builtin(op, args, argTys, ret);
const Pr = (op, args, argTys, ret) => ir_1.E.prim(op, args, argTys, ret);
const st = ty_1.showTy;
function isLib(tr, sym) {
    return !!sym && (0, core_1.isLibDecl)(tr.program, sym.declarations?.[0]);
}
function argc(call, min, max, what) {
    const args = call.arguments ?? ts.factory.createNodeArray();
    if (args.length < min || args.length > max)
        (0, diag_1.reject)(call, 'unsupported-builtin', `${what} with ${args.length} argument(s)`);
    if (args.some(ts.isSpreadElement))
        (0, diag_1.reject)(call, 'unsupported-builtin', `spread arguments to ${what}`);
    return args;
}
/** The delay of a timer (the semantics clamps it like Node: outside [1, 2^31 - 1] it is 1;
 * Node's documented default is 1). */
function timerDelay(tr, arg, fc) {
    if (!arg)
        return (0, core_1.numLit)(1);
    return tr.lowerExpr(arg, fc, ty_1.T.num);
}
const MATH_UN = new Set(['abs', 'floor', 'ceil', 'trunc', 'round', 'sign', 'sqrt', 'fround', 'clz32', 'cbrt', 'exp', 'expm1',
    'log', 'log1p', 'log2', 'log10', 'sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'sinh', 'cosh', 'tanh', 'asinh', 'acosh', 'atanh']);
const MATH_CONST = {
    PI: Math.PI, E: Math.E, LN2: Math.LN2, LN10: Math.LN10, LOG2E: Math.LOG2E, LOG10E: Math.LOG10E, SQRT2: Math.SQRT2, SQRT1_2: Math.SQRT1_2,
};
const NUMBER_CONST = {
    MAX_SAFE_INTEGER: Number.MAX_SAFE_INTEGER, MIN_SAFE_INTEGER: Number.MIN_SAFE_INTEGER, EPSILON: Number.EPSILON,
    MAX_VALUE: Number.MAX_VALUE, MIN_VALUE: Number.MIN_VALUE, POSITIVE_INFINITY: Infinity, NEGATIVE_INFINITY: -Infinity, NaN: NaN,
};
const ERR_KINDS = {
    Error: 'error', TypeError: 'typeError', RangeError: 'rangeError', SyntaxError: 'syntaxError', ReferenceError: 'referenceError',
};
P.lowerStaticMember = function (pa, fc) {
    const base = (0, stmts_1.skipParens)(pa.expression);
    if (!ts.isIdentifier(base))
        return null;
    const sym = this.symAt(base);
    if (!sym)
        return null;
    if (isLib(this, sym)) {
        const name = pa.name.text;
        if (base.text === 'Math' && Object.hasOwn(MATH_CONST, name))
            return (0, core_1.numLit)(MATH_CONST[name]);
        if (base.text === 'Number' && Object.hasOwn(NUMBER_CONST, name))
            return (0, core_1.numLit)(NUMBER_CONST[name]);
        // `Math.random` / `Date.now` as values (a default `rng = Math.random`): a function that calls
        // them, drawing from the same oracle
        if ((base.text === 'Math' && name === 'random') || (base.text === 'Date' && name === 'now')) {
            const f = ir_1.E.lam(false, [], ty_1.T.num, [(0, ir_1.stmtItem)(ir_1.S.ret(B(name === 'random' ? '.random' : '.now', [], [], ty_1.T.num)))]);
            return this.adapt(f, this.tyAt(pa, fc), pa);
        }
        if (['Math', 'Number', 'console', 'Promise', 'Array', 'Object', 'JSON', 'String', 'BigInt', 'Symbol', 'Reflect'].includes(base.text)) {
            (0, diag_1.reject)(pa, 'unsupported-builtin', `${base.text}.${name} is not supported`);
        }
        return null;
    }
    if (sym.flags & ts.SymbolFlags.Class) {
        const g = this.staticFieldGlobal(pa);
        if (g)
            return this.adapt(ir_1.E.gget(g), this.tyAt(pa, fc), pa);
        (0, diag_1.reject)(pa, 'unsupported', `static member ${pa.name.text} used as a value`);
    }
    return null;
};
P.collectionSnapshot = function (base0, method, node) {
    const base = this.unfoldE(base0);
    const t = base.ty;
    if (t.k === 'map') {
        if (method === 'keys')
            return B(`(.mapKeys ${st(t.key)} ${st(t.val)})`, [base], [t], ty_1.T.arr(t.key));
        if (method === 'values')
            return B(`(.mapValues ${st(t.key)} ${st(t.val)})`, [base], [t], ty_1.T.arr(t.val));
        if (method === 'entries')
            return B(`(.mapEntries ${st(t.key)} ${st(t.val)})`, [base], [t], ty_1.T.arr(ty_1.T.tup([t.key, t.val])));
    }
    if (t.k === 'set' && (method === 'values' || method === 'keys'))
        return B(`(.setValues ${st(t.t)})`, [base], [t], ty_1.T.arr(t.t));
    if (t.k === 'arr' && method === 'values')
        return B(`(.arrCopy ${st(t.t)})`, [base], [t], t);
    (0, diag_1.reject)(node, 'unsupported-builtin', `${method}() of ${(0, ty_1.prettyTy)(t)} outside for…of / spread / Array.from`);
};
P.lowerCallback = function (arg, fc, fnTy, fixedParams = false) {
    const n = (0, stmts_1.skipParens)(arg);
    if (ts.isArrowFunction(n) || ts.isFunctionExpression(n))
        return this.lowerLambda(n, fc, fnTy, fixedParams);
    if (ts.isIdentifier(n) && isLib(this, this.symAt(n)) && (n.text === 'String' || n.text === 'Number' || n.text === 'Boolean') && fnTy.k === 'fn' && fnTy.args.length >= 1) {
        // `xs.map(String)`, `xs.filter(Boolean)`: the conversion of the first argument
        const ps = fnTy.args.map((t, i) => (0, ir_1.mkVar)(`a${i}`, t));
        const x = ir_1.E.var(ps[0]);
        let body;
        if (n.text === 'String')
            body = this.toStr(x, n);
        else if (n.text === 'Boolean')
            body = this.truthy(x, n);
        else
            body = numberOf(this, x, n);
        return ir_1.E.lam(false, ps, fnTy.ret, [(0, ir_1.stmtItem)(ir_1.S.ret(this.coerce(body, fnTy.ret, n)))]);
    }
    return this.coerce(this.lowerExpr(n, fc), fnTy, n);
};
function numberOf(tr, x0, node) {
    const x = tr.unfoldE(x0);
    if ((0, core_1.holdsTimer)(x.ty))
        (0, diag_1.reject)(node, 'timer-handle', 'Number(...) of a Node timer handle (Node gives its id)');
    switch (x.ty.k) {
        case 'num': return x;
        case 'str': return Pr('.strToNum', [x], [ty_1.T.str], ty_1.T.num);
        case 'enum': return Pr('.strToNum', [tr.toStr(x, node)], [ty_1.T.str], ty_1.T.num);
        case 'bigint': return Pr('.numOfBig', [x], [ty_1.T.bigint], ty_1.T.num);
        case 'bool': return ir_1.E.cond(x, (0, core_1.numLit)(1), (0, core_1.numLit)(0));
        case 'undef': return tr.withValue(x, 'u', () => (0, core_1.numLit)(NaN));
        case 'null': return tr.withValue(x, 'u', () => (0, core_1.numLit)(0));
        case 'opt': {
            const v = (0, ir_1.mkVar)('x', x.ty.t);
            return ir_1.E.caseOpt(x, (0, core_1.numLit)(NaN), v, numberOf(tr, ir_1.E.var(v), node));
        }
        case 'union': return ir_1.E.caseU(x, x.ty.ts.map(m => { const v = (0, ir_1.mkVar)('m', m); return { v, body: numberOf(tr, ir_1.E.var(v), node) }; }));
        case 'dyn': return tr.withValue(x, 'd', d => {
            // ToNumber on the runtime value: numbers, bigints, booleans, undefined and null directly;
            // strings and objects through their string (ToPrimitive of the modelled objects is their
            // String(x): arrays join, other objects give NaN)
            const tag = ir_1.E.prim('.dynTypeof', [d], [ty_1.T.dyn], ty_1.T.str);
            const as = (t) => ir_1.E.unwrap(Pr(`(.dynCast ${st(t)})`, [d], [ty_1.T.dyn], ty_1.T.opt(t)));
            const isNull = Pr('.dynEq', [d, Pr('(.toDyn .null)', [ir_1.E.nullLit()], [ty_1.T.null], ty_1.T.dyn)], [ty_1.T.dyn, ty_1.T.dyn], ty_1.T.bool);
            const viaStr = ir_1.E.cond(isNull, (0, core_1.numLit)(0), Pr('.strToNum', [ir_1.E.builtin('.dynToStr', [d], [ty_1.T.dyn], ty_1.T.str)], [ty_1.T.str], ty_1.T.num));
            const is = (s) => ir_1.E.seq(tag, (0, core_1.strLit)(s));
            return ir_1.E.cond(is('number'), as(ty_1.T.num), ir_1.E.cond(is('bigint'), Pr('.numOfBig', [as(ty_1.T.bigint)], [ty_1.T.bigint], ty_1.T.num), ir_1.E.cond(is('boolean'), ir_1.E.cond(as(ty_1.T.bool), (0, core_1.numLit)(1), (0, core_1.numLit)(0)), ir_1.E.cond(is('undefined'), (0, core_1.numLit)(NaN), viaStr))));
        });
    }
    (0, diag_1.reject)(node, 'unsupported-builtin', `Number(...) of ${(0, ty_1.prettyTy)(x.ty)}`);
}
function fnSpecs(t) {
    return t.args.map(a => ({ ty: a, optional: a.k === 'opt', rest: false }));
}
// ---------------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------------
// coverage mode: calls of other project functions are assumed translatable; uses of
// package / host APIs outside the modelled library are `external-call`
const MODELLED_PARENTS = new Set(['Array', 'ReadonlyArray', 'String', 'Map', 'ReadonlyMap', 'Set', 'ReadonlySet', 'Promise',
    'PromiseConstructor', 'PromiseLike', 'Math', 'Number', 'NumberConstructor', 'BigInt', 'BigIntConstructor', 'StringConstructor',
    'ArrayConstructor', 'Console', 'Boolean', 'Error', 'ErrorConstructor', 'MapConstructor', 'SetConstructor', 'Function',
    'Int8Array', 'Uint8Array', 'Uint8ClampedArray', 'Int16Array', 'Uint16Array', 'Int32Array', 'Uint32Array', 'Float32Array',
    'Float64Array', 'BigInt64Array', 'BigUint64Array', 'TypeErrorConstructor', 'RangeErrorConstructor', 'SyntaxErrorConstructor',
    'ReferenceErrorConstructor']);
const MODELLED_FNS = new Set(['String', 'Number', 'BigInt', 'Boolean', 'parseInt', 'parseFloat', 'isNaN', 'isFinite', 'setTimeout',
    'queueMicrotask', 'Map', 'Set', 'Error', 'TypeError', 'RangeError', 'SyntaxError', 'ReferenceError', 'Promise', 'Array',
    'Int8Array', 'Uint8Array', 'Uint8ClampedArray', 'Int16Array', 'Uint16Array', 'Int32Array', 'Uint32Array', 'Float32Array',
    'Float64Array', 'BigInt64Array', 'BigUint64Array']);
const MODELLED_NS = new Set(['Math', 'Number', 'Promise', 'Array', 'String', 'BigInt', 'console', 'Boolean']);
function parentName(d) {
    const p = d.parent;
    if (p && (ts.isInterfaceDeclaration(p) || ts.isClassDeclaration(p) || ts.isModuleDeclaration(p)) && p.name)
        return p.name.text;
    if (p && ts.isTypeLiteralNode(p) && p.parent && ts.isTypeAliasDeclaration(p.parent))
        return p.parent.name.text;
    return '';
}
P.externalUse = function (_sym, name, node, fc, exp) {
    this.covExternals.add(name);
    this.covDiags.push({ rule: 'external-call', node, msg: `uses ${name} (outside the project and the StrictTS library)` });
    return this.placeholderFor(node, fc, exp);
};
P.externalGlobalMember = function (pa, fc) {
    const base = (0, stmts_1.skipParens)(pa.expression);
    if (!ts.isIdentifier(base))
        return null;
    const sym = this.symAt(base);
    if (!sym || this.lookup(sym, fc))
        return null;
    const decls = sym.declarations ?? [];
    if (!decls.length || decls.some(d => this.isProjectDecl(d)))
        return null;
    if (MODELLED_NS.has(base.text) && isLib(this, sym))
        return null;
    return { sym, name: `${this.externalName(sym)}.${pa.name.text}` };
};
/** A receiver that is a host singleton (`JSON`, `document`) or a namespace import is not
 * passed to externs; values (`res.json()`, `db.collection()`) are. */
function isValueReceiver(tr, recv, fc) {
    const r = (0, stmts_1.skipParens)(recv);
    // a static path (`admin.firestore.FieldValue`, `StyleSheet`): namespaces and classes
    const rs = tr.resolveSym(tr.checker.getSymbolAtLocation(ts.isPropertyAccessExpression(r) ? r.name : r));
    if (rs && (rs.flags & (ts.SymbolFlags.ValueModule | ts.SymbolFlags.NamespaceModule | ts.SymbolFlags.Class | ts.SymbolFlags.Enum)) &&
        !(rs.flags & (ts.SymbolFlags.Variable | ts.SymbolFlags.Property)) && !(ts.isIdentifier(r) && tr.lookup(rs, fc)))
        return false;
    if (!ts.isIdentifier(r))
        return true;
    const sym = tr.symAt(r);
    if (!sym)
        return true;
    if (tr.lookup(sym, fc))
        return true;
    if (sym.flags & (ts.SymbolFlags.ValueModule | ts.SymbolFlags.NamespaceModule))
        return false;
    const decls = sym.declarations ?? [];
    if (decls.some(d => tr.isProjectDecl(d)))
        return true;
    return false;
}
P.externMemberName = function (sym, isMember) {
    const d = sym.declarations?.[0];
    const file = d?.getSourceFile().fileName ?? '';
    const m = file.match(/node_modules\/((?:@[^/]+\/)?[^/]+)\/(.*)$/);
    const pkg = m && !m[1].startsWith('@types/') && m[1] !== 'typescript' ? m[1] : undefined;
    const parent = d ? parentName(d).replace(/Constructor$/, '') : '';
    if (isMember && parent)
        return pkg ? `${pkg}:${parent}.${sym.name}` : `${parent}.${sym.name}`;
    if (pkg) {
        // a module-level function: the module path (`firebase-functions/logger:warn`)
        const sub = m[2].replace(/\.d\.(m|c)?ts$/, '').replace(/(^|\/)(lib|dist|build|cjs|esm|types|src)\//g, '$1').replace(/(^|\/)index$/, '');
        const mod = sub && sub !== m[1].split('/').pop() ? `${pkg}/${sub}` : pkg;
        return `${mod}:${sym.name}`;
    }
    return this.externalName(sym);
};
P.classifyCall = function (call, fc) {
    const callee = (0, stmts_1.skipParens)(call.expression);
    if (ts.isIdentifier(callee)) {
        const sym = this.symAt(callee);
        if (!sym)
            return { kind: 'external', name: `<unresolved>:${callee.text}` };
        const decls = sym.declarations ?? [];
        if (decls.some(d => ts.isVariableDeclaration(d) && !!d.initializer && this.isGlobalDecl(d) && this.isProjectDecl(d) &&
            (ts.isArrowFunction((0, stmts_1.skipParens)(d.initializer)) || ts.isFunctionExpression((0, stmts_1.skipParens)(d.initializer)))))
            return { kind: 'project' };
        if (this.lookup(sym, fc))
            return { kind: 'normal' };
        if (decls.length && decls.every(d => this.isProjectDecl(d) && ts.isFunctionDeclaration(d) && !d.body)) {
            // `declare function f(...)` in the program: implemented by the host
            return { kind: 'external', name: callee.text, sym, receiver: false };
        }
        if (decls.some(d => this.isProjectDecl(d))) {
            if (decls.some(d => ts.isFunctionDeclaration(d) || ts.isClassDeclaration(d)))
                return { kind: 'project' };
            // module-level `const f = (...) => ...`
            if (decls.some(d => ts.isVariableDeclaration(d) && !!d.initializer && this.isGlobalDecl(d) &&
                (ts.isArrowFunction((0, stmts_1.skipParens)(d.initializer)) || ts.isFunctionExpression((0, stmts_1.skipParens)(d.initializer)))))
                return { kind: 'project' };
            return { kind: 'normal' };
        }
        if (!decls.length)
            return { kind: 'normal' };
        if (MODELLED_FNS.has(callee.text) && isLib(this, sym))
            return { kind: 'normal' };
        // (`RegExp(p, f)` constructs like `new RegExp(p, f)`: regex.ts)
        if (callee.text === 'RegExp' && isLib(this, sym))
            return { kind: 'external', name: 'RegExp.new', sym, receiver: false };
        return { kind: 'external', name: this.externMemberName(sym, false), sym, receiver: false };
    }
    if (ts.isPropertyAccessExpression(callee) || ts.isElementAccessExpression(callee)) {
        const nameNode = ts.isPropertyAccessExpression(callee) ? callee.name : callee.argumentExpression;
        const msym = this.resolveSym(this.checker.getSymbolAtLocation(nameNode));
        const label = ts.isPropertyAccessExpression(callee) ? callee.name.text : '[]';
        if (!msym || !msym.declarations?.length) {
            const rt = this.checker.getTypeAtLocation(callee.expression);
            if (rt.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown))
                return { kind: 'external', name: `<any>.${label}` };
            return { kind: 'normal' };
        }
        const d0 = msym.declarations[0];
        if (this.isProjectDecl(d0)) {
            if (ts.isMethodDeclaration(d0) || ts.isFunctionDeclaration(d0) || ts.isGetAccessorDeclaration(d0))
                return { kind: 'project' };
            return { kind: 'normal' };
        }
        if (MODELLED_PARENTS.has(parentName(d0)) && isLib(this, msym))
            return { kind: 'normal' };
        // `next` / `return` / `throw` of an `Iterator<…>` value (the record of its closures, types.ts):
        // calls through its fields (on other iterator types they stay external)
        if (parentName(d0) === 'Iterator' && isLib(this, msym)) {
            const rs = this.checker.getTypeAtLocation(callee.expression).getNonNullableType().getSymbol();
            if (rs && rs.name === 'Iterator' && isLib(this, rs))
                return { kind: 'normal' };
        }
        if (parentName(d0) === 'DateConstructor' && msym.name === 'now' && isLib(this, msym))
            return { kind: 'normal' };
        const receiver = isValueReceiver(this, callee.expression, fc);
        return { kind: 'external', name: this.externMemberName(msym, !!parentName(d0)), sym: msym, receiver };
    }
    return { kind: 'normal' };
};
function isPromiseType(tr, t) {
    const sym = t.getSymbol();
    if (sym && sym.name === 'Promise' && isLib(tr, sym) && t.objectFlags & ts.ObjectFlags.Reference) {
        return tr.checker.getTypeArguments(t)[0];
    }
    return undefined;
}
/** Host functions whose effect is on the program's own state (timers, objects, the
 * process): an oracle cannot model them. */
const EXTERN_EFFECT = new Set(['clearTimeout', 'clearInterval', 'clearImmediate', 'Object.assign', 'Object.freeze', 'Object.seal',
    'Object.preventExtensions', 'Object.defineProperty', 'Object.defineProperties', 'Object.setPrototypeOf', 'process.exit',
    'NodeJS.Process.exit', 'Array.prototype', 'WindowOrWorkerGlobalScope.clearTimeout', 'WindowOrWorkerGlobalScope.clearInterval']);
// Functions returned by external code (React's state setters, unsubscribe functions) are not
// oracle values: the oracle answers a handle `.ext "<extern>:result"` and the program sees a
// closure that calls the extern `"<handle type>.call"` with the handle and its arguments.
function containsFn(t) {
    switch (t.k) {
        case 'fn': return true;
        case 'tup':
        case 'union': return t.ts.some(containsFn);
        case 'record': return t.fs.some(f => containsFn(f.ty));
        case 'opt':
        case 'arr':
        case 'set':
        case 'promise':
        case 'dict': return containsFn(t.t);
        case 'map': return containsFn(t.key) || containsFn(t.val);
        default: return false;
    }
}
/** The type the oracle answers for a result of type `t`: function types replaced by handles. */
function oracleTy(t, base, node) {
    if (!containsFn(t))
        return t;
    switch (t.k) {
        case 'fn': return ty_1.T.ext(`${base}:result`);
        case 'tup': return ty_1.T.tup(t.ts.map((x, i) => oracleTy(x, `${base}.${i}`, node)));
        case 'record': return ty_1.T.record(t.fs.map(f => ({ name: f.name, ty: oracleTy(f.ty, `${base}.${f.name}`, node) })));
        case 'opt': return ty_1.T.opt(oracleTy(t.t, base, node));
        case 'union': return ty_1.T.union(t.ts.map((x, i) => oracleTy(x, `${base}.u${i}`, node)));
    }
    (0, diag_1.reject)(node, 'extern-fn-result', `${base} returns functions inside ${(0, ty_1.prettyTy)(t)}`);
}
P.externResult = function (name, args, want, node) {
    // (an answer would be a new object to StrictTS, though external code may return one the
    // program already has; identity.ts)
    if (this.holdsIdBox(want))
        (0, diag_1.reject)(node, 'record-identity', `${name} returns functions or objects compared by identity (${(0, ty_1.prettyTy)(want)})`);
    if (!containsFn(want))
        return ir_1.E.extern(name, args, want);
    const wrap = (e, t, base) => {
        if (!containsFn(t))
            return e;
        switch (t.k) {
            case 'fn': {
                const h = (0, ir_1.mkVar)('h', e.ty);
                const params = t.args.map((a, i) => (0, ir_1.mkVar)(`a${i}`, a));
                const callName = `${e.ty.name}.call`;
                const argv = [ir_1.E.var(h), ...params.map(p => ir_1.E.var(p))];
                if (this.coverage)
                    this.covExternals.add(callName);
                const r = t.ret.k === 'promise'
                    ? (containsFn(t.ret.t) ? (0, diag_1.reject)(node, 'extern-fn-result', `${callName} returns functions inside ${(0, ty_1.prettyTy)(t.ret)}`)
                        : this.holdsIdBox(t.ret.t) ? (0, diag_1.reject)(node, 'record-identity', `${callName} resolves to functions or objects compared by identity`)
                            : ir_1.E.externAsync(callName, argv, t.ret.t))
                    : this.externResult(callName, argv, t.ret, node);
                return ir_1.E.letE(h, e, ir_1.E.lam(false, params, t.ret, [(0, ir_1.stmtItem)(ir_1.S.ret(r))]));
            }
            case 'tup':
            case 'record': {
                const v = (0, ir_1.mkVar)('r', e.ty);
                const parts = t.k === 'tup'
                    ? t.ts.map((x, i) => wrap(ir_1.E.getTup(ir_1.E.var(v), i), x, `${base}.${i}`))
                    : t.fs.map((f, i) => wrap(ir_1.E.getRec(ir_1.E.var(v), i), f.ty, `${base}.${f.name}`));
                return ir_1.E.letE(v, e, t.k === 'tup' ? ir_1.E.mkTup(parts) : ir_1.E.mkRec(t, parts));
            }
            case 'opt': {
                const v = (0, ir_1.mkVar)('x', e.ty.t);
                return ir_1.E.caseOpt(e, ir_1.E.none(t.t), v, ir_1.E.some(wrap(ir_1.E.var(v), t.t, base)));
            }
            case 'union': {
                const et = e.ty;
                return ir_1.E.caseU(e, et.ts.map((m, i) => { const v = (0, ir_1.mkVar)('m', m); return { v, body: ir_1.E.inj(t, i, wrap(ir_1.E.var(v), t.ts[i], `${base}.u${i}`)) }; }));
            }
        }
        return e;
    };
    return wrap(ir_1.E.extern(name, args, oracleTy(want, name, node)), want, name);
};
/** A value as external code receives it: the cells of records compared by identity are read
 * (identity.ts), also inside optional values, unions, records, tuples and arrays (a copy). */
function forExtern(tr, e, node) {
    const t = e.ty;
    if (!tr.holdsIdBox(t, true))
        return e;
    const inner = (v) => forExtern(tr, ir_1.E.var(v), node);
    switch (t.k) {
        case 'box': return forExtern(tr, tr.unboxCell(e), node);
        case 'opt': {
            const v = (0, ir_1.mkVar)('x', t.t);
            const b = inner(v);
            return ir_1.E.caseOpt(e, ir_1.E.none(b.ty), v, ir_1.E.some(b));
        }
        case 'union': {
            const alts = t.ts.map(m => { const v = (0, ir_1.mkVar)('m', m); return { v, body: inner(v) }; });
            const ut = ty_1.T.union(alts.map(a => a.body.ty));
            return ir_1.E.caseU(e, alts.map((a, i) => ({ v: a.v, body: ir_1.E.inj(ut, i, a.body) })));
        }
        case 'record': return tr.withValue(e, 'r', x => {
            const parts = t.fs.map((_, i) => forExtern(tr, ir_1.E.getRec(x, i), node));
            return ir_1.E.mkRec(ty_1.T.record(t.fs.map((f, i) => ({ name: f.name, ty: parts[i].ty }))), parts);
        });
        case 'tup': return tr.withValue(e, 'p', x => ir_1.E.mkTup(t.ts.map((_, i) => forExtern(tr, ir_1.E.getTup(x, i), node))));
        case 'arr': {
            const ps = [(0, ir_1.mkVar)('x', t.t), (0, ir_1.mkVar)('i', ty_1.T.num), (0, ir_1.mkVar)('a', t)];
            const b = inner(ps[0]);
            const f = ir_1.E.lam(false, ps, b.ty, [(0, ir_1.stmtItem)(ir_1.S.ret(b))]);
            return B(`(.arrMap ${st(t.t)} ${st(b.ty)})`, [e, f], [t, cbTy3(t.t, b.ty)], ty_1.T.arr(b.ty));
        }
    }
    (0, diag_1.reject)(node, 'record-identity', `${(0, ty_1.prettyTy)(t)} passed to external code: it holds objects compared by identity`);
}
P.lowerExternCall = function (call, fc, exp, name, receiver) {
    if (EXTERN_EFFECT.has(name) || EXTERN_EFFECT.has(name.replace(/^[^:]*:/, ''))) {
        (0, diag_1.reject)(call, 'extern-effect', `${name} acts on the program's own state (timers, objects, the process); an external oracle cannot model it`);
    }
    const sig = this.checker.getResolvedSignature(call);
    if (!sig)
        (0, diag_1.reject)(call, 'external-call', `cannot resolve the signature of ${name}`);
    const params = sig.getParameters();
    const args = call.arguments ?? ts.factory.createNodeArray();
    const thunks = [];
    if (receiver)
        thunks.push(() => forExtern(this, this.lowerExpr(receiver, fc), receiver));
    args.forEach((a, i) => {
        if (ts.isSpreadElement(a))
            (0, diag_1.reject)(a, 'extern-spread', `spread argument to the external function ${name}`);
        const p = params[Math.min(i, params.length - 1)];
        const pd = p?.valueDeclaration;
        let pt = p ? this.checker.getTypeOfSymbolAtLocation(p, call) : undefined;
        if (pt && pd?.dotDotDotToken)
            pt = this.checker.getIndexTypeOfType(pt, ts.IndexKind.Number) ?? pt;
        const isFn = (t) => !!t && (t.getCallSignatures().length > 0 || (t.isUnion() && t.types.some(x => x.getCallSignatures().length > 0)));
        const ax = (0, stmts_1.skipParens)(a);
        if (isFn(this.checker.getTypeAtLocation(a)) || ts.isArrowFunction(ax) || ts.isFunctionExpression(ax)) {
            (0, diag_1.reject)(a, 'extern-callback', `callback passed to the external function ${name}`);
        }
        thunks.push(() => {
            let want;
            try {
                if (pt && !(pt.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)))
                    want = this.tyOf(pt, fc, a);
            }
            catch {
                want = undefined;
            }
            // the oracle receives the argument at its own type when the parameter type has none
            if (want) {
                const e = this.lowerExpr(a, fc);
                const c = this.convert(e, want, a, true, 0);
                return forExtern(this, c ?? e, a);
            }
            return forExtern(this, this.lowerExpr(a, fc), a);
        });
    });
    const vals = this.seq(thunks, fc);
    const rt = sig.getReturnType();
    const inner = isPromiseType(this, rt);
    const mapRet = (t) => {
        if (exp && (t.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)))
            return exp.k === 'promise' && inner ? exp.t : exp;
        return this.tyOf(t, fc, call);
    };
    if (this.coverage)
        this.covExternals.add(name);
    if (inner) {
        const t = exp && exp.k === 'promise' && (inner.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) ? exp.t : mapRet(inner);
        if (containsFn(t))
            (0, diag_1.reject)(call, 'extern-fn-result', `${name} resolves to functions (${(0, ty_1.prettyTy)(t)})`);
        if (this.holdsIdBox(t))
            (0, diag_1.reject)(call, 'record-identity', `${name} resolves to functions or objects compared by identity (${(0, ty_1.prettyTy)(t)})`);
        return ir_1.E.externAsync(name, vals, t);
    }
    if (name === 'JSON.stringify' && mapRet(rt).k === 'str') {
        // undefined, though TypeScript types the result string, for undefined, a function or a
        // symbol at the top level (also when toJSON or a replacer gives undefined): the oracle answers
        // `string | undefined`, and where a string is needed undefined stops the program (a designed
        // panic, as for a capture group that did not participate)
        const r = ir_1.E.extern(name, vals, ty_1.T.opt(ty_1.T.str));
        return exp && exp.k === 'opt' && exp.t.k === 'str' ? r : ir_1.E.unwrap(r);
    }
    return this.externResult(name, vals, mapRet(rt), call);
};
P.lowerLoose = function (call, fc) {
    const callee = (0, stmts_1.skipParens)(call.expression);
    if ((ts.isPropertyAccessExpression(callee) || ts.isElementAccessExpression(callee)) && !this.isNamespaceRef(callee.expression)) {
        const recv = (0, stmts_1.skipParens)(callee.expression);
        // a receiver that is just a name (`Date`, `admin`, `this`) has nothing to check
        if (recv.kind !== SK.SuperKeyword && !ts.isIdentifier(recv) && recv.kind !== SK.ThisKeyword)
            this.lowerExpr(callee.expression, fc);
    }
    for (const a of call.arguments ?? [])
        this.lowerExpr(ts.isSpreadElement(a) ? a.expression : a, fc);
};
P.lowerCall = function (call, fc, exp) {
    const callee = (0, stmts_1.skipParens)(call.expression);
    const rx = this.lowerRegexCall(call, fc, exp) ?? this.lowerDictCall(call, fc);
    if (rx)
        return rx;
    if (!fc.override.has(call.expression) && !fc.override.has(callee)) {
        const c = this.classifyCall(call, fc);
        if (this.coverage && c.kind === 'project') {
            this.lowerLoose(call, fc);
            return this.placeholderFor(call, fc, exp);
        }
        if (c.kind === 'external') {
            if (!c.sym) {
                // unresolvable (any-typed) callee
                if (c.name.startsWith('<any>'))
                    (0, diag_1.reject)(call, 'any-op', `method call ${c.name.slice(5)} on a value of type any/unknown`);
                if (this.coverage)
                    this.covExternals.add(c.name);
                (0, diag_1.reject)(call, 'external-call', `calls ${c.name} (no TypeScript signature)`);
            }
            const recv = c.receiver && (ts.isPropertyAccessExpression(callee) || ts.isElementAccessExpression(callee)) ? callee.expression : undefined;
            return this.lowerExternCall(call, fc, exp, c.name, recv);
        }
    }
    const ov = fc.override.get(call.expression) ?? fc.override.get(callee);
    if (ov) {
        // `f?.(x)`: the callee was evaluated by the optional chain
        let f = this.unfoldE(ov);
        if ((0, ir_1.isPoison)(f)) {
            this.lowerLoose(call, fc);
            return this.derivedPoison(call, fc, exp);
        }
        if (f.ty.k === 'dyn')
            (0, diag_1.reject)(call, 'any-op', 'calling a value of type any/unknown');
        if (f.ty.k === 'box' && f.ty.t.k === 'fn')
            f = this.unboxFn(f);
        if (f.ty.k !== 'fn')
            (0, diag_1.reject)(call, 'unsupported', `calling a value of type ${(0, ty_1.prettyTy)(f.ty)}`);
        const args = this.lowerCallArgs(fnSpecs(f.ty), call.arguments, fc, call, [() => f]);
        return ir_1.E.app(args[0], args.slice(1));
    }
    if (callee.kind === SK.SuperKeyword)
        (0, diag_1.reject)(call, 'no-extends', '`super` calls (classes cannot extend)');
    if (callee.kind === SK.ImportKeyword)
        (0, diag_1.reject)(call, 'dynamic-import', 'dynamic import');
    if (ts.isPropertyAccessExpression(callee) || ts.isElementAccessExpression(callee)) {
        let name;
        if (ts.isPropertyAccessExpression(callee))
            name = callee.name.text;
        else {
            const a = (0, stmts_1.skipParens)(callee.argumentExpression);
            if (!ts.isStringLiteral(a))
                (0, diag_1.reject)(callee, 'unsupported', 'computed method call');
            name = a.text;
        }
        const objNode = (0, stmts_1.skipParens)(callee.expression);
        if (ts.isPropertyAccessExpression(callee) && this.isNamespaceRef(objNode)) {
            // m.f(...) through `import * as m`
            const sym = this.resolveSym(this.checker.getSymbolAtLocation(callee));
            const fd = sym && this.topFunDecl(sym);
            if (fd) {
                const subst = this.instantiate(fd, call, fc, new Map());
                const f = this.funInfoFor(fd, subst, call);
                return ir_1.E.call(f, this.lowerCallArgs(this.paramSpecs(fd, subst), call.arguments, fc, call, []));
            }
            const fv = this.unfoldE(this.lowerIdentLike(callee, fc));
            if (fv.ty.k !== 'fn')
                (0, diag_1.reject)(call, 'unsupported', `calling ${(0, ty_1.prettyTy)(fv.ty)}`);
            const args = this.lowerCallArgs(fnSpecs(fv.ty), call.arguments, fc, call, [() => fv]);
            return ir_1.E.app(args[0], args.slice(1));
        }
        if (ts.isIdentifier(objNode) && !fc.override.has(callee.expression)) {
            const osym = this.symAt(objNode);
            if (osym && isLib(this, osym) && !this.lookup(osym, fc))
                return lowerLibStatic(this, objNode.text, name, call, fc, exp);
            if (osym && (osym.flags & ts.SymbolFlags.Class) && !isLib(this, osym)) {
                const ci = this.types.classInst(this.checker.getDeclaredTypeOfSymbol(osym), fc.subst, call);
                const f = this.classStatic(ci, name, call);
                if (!f)
                    (0, diag_1.reject)(call, 'unsupported', `no static method ${name}`);
                const decl = osym.declarations.find(ts.isClassDeclaration).members.find(m => ts.isMethodDeclaration(m) && m.name.text === name);
                const args = this.lowerCallArgs(this.paramSpecs(decl, ci.subst), call.arguments, fc, call, []);
                return ir_1.E.call(f, args);
            }
        }
        // `new Array(n).fill(x)` / `Array(n).fill(x)`
        if (name === 'fill' && (ts.isNewExpression(objNode) || ts.isCallExpression(objNode)) && ts.isIdentifier(objNode.expression) &&
            objNode.expression.text === 'Array' && isLib(this, this.symAt(objNode.expression)) && (objNode.arguments?.length ?? 0) === 1) {
            const rt = this.tyAt(call, fc);
            if (rt.k !== 'arr')
                (0, diag_1.reject)(call, 'unsupported-builtin', 'Array(n).fill');
            argc(call, 1, 1, 'Array(n).fill');
            const [n, x] = this.seq([() => this.lowerExpr(objNode.arguments[0], fc, ty_1.T.num), () => this.lowerExpr(call.arguments[0], fc, rt.t)], fc);
            return B(`(.arrMakeFill ${st(rt.t)})`, [n, x], [ty_1.T.num, rt.t], rt);
        }
        const base = this.lowerExpr(callee.expression, fc);
        return this.lowerMethodCall(base, name, call, fc, exp);
    }
    if (ts.isIdentifier(callee)) {
        const sym = this.symAt(callee);
        if (sym && isLib(this, sym) && !this.lookup(sym, fc))
            return lowerLibFunction(this, callee.text, call, fc, exp);
        const b = sym && this.lookup(sym, fc);
        if (b && b.k === 'lifted') {
            const decl = b.f;
            const caps = this.liftedCapArgs(b, fc, call);
            const specs = decl.params.slice(b.caps.length).map(p => ({ ty: p.ty, optional: p.ty.k === 'opt', rest: false }));
            const declNode = sym.declarations?.find(d => ts.isFunctionDeclaration(d) || ts.isVariableDeclaration(d));
            let realSpecs = specs;
            if (declNode && ts.isFunctionDeclaration(declNode))
                realSpecs = this.paramSpecs(declNode, fc.subst);
            else if (declNode && ts.isVariableDeclaration(declNode) && declNode.initializer) {
                const init = (0, stmts_1.skipParens)(declNode.initializer);
                if (ts.isArrowFunction(init) || ts.isFunctionExpression(init))
                    realSpecs = this.paramSpecs(init, fc.subst);
            }
            const args = this.lowerCallArgs(realSpecs, call.arguments, fc, call, caps.map(c => () => c));
            return ir_1.E.call(decl, args);
        }
        if (b) {
            let f = this.unfoldE(this.lowerIdent(callee, fc));
            if ((0, ir_1.isPoison)(f)) {
                this.lowerLoose(call, fc);
                return this.derivedPoison(call, fc, exp);
            }
            if (f.ty.k === 'ext')
                return this.lowerExternCall(call, fc, exp, `${f.ty.name}.call`, callee);
            if (f.ty.k === 'dyn')
                (0, diag_1.reject)(call, 'any-op', 'calling a value of type any/unknown');
            if (f.ty.k === 'box' && f.ty.t.k === 'fn')
                f = this.unboxFn(f);
            if (f.ty.k !== 'fn')
                (0, diag_1.reject)(call, 'unsupported', `calling a value of type ${(0, ty_1.prettyTy)(f.ty)}`);
            const args = this.lowerCallArgs(fnSpecs(f.ty), call.arguments, fc, call, [() => f]);
            return ir_1.E.app(args[0], args.slice(1));
        }
        const fd = sym && this.topFunDecl(sym);
        if (fd) {
            const subst = this.instantiate(fd, call, fc, new Map());
            const f = this.funInfoFor(fd, subst, call);
            const args = this.lowerCallArgs(this.paramSpecs(fd, subst), call.arguments, fc, call, []);
            return ir_1.E.call(f, args);
        }
        if (sym && (sym.flags & ts.SymbolFlags.Class))
            (0, diag_1.reject)(call, 'unsupported', 'class constructors must be called with `new`');
        (0, diag_1.reject)(call, 'unsupported', `\`${callee.text}\` is called before its declaration (or is not supported)`);
    }
    let f = this.unfoldE(this.lowerExpr(callee, fc));
    if ((0, ir_1.isPoison)(f)) {
        for (const a of call.arguments)
            this.lowerExpr(a, fc);
        return this.derivedPoison(call, fc, exp);
    }
    if (f.ty.k === 'ext')
        return this.lowerExternCall(call, fc, exp, `${f.ty.name}.call`, callee);
    if (f.ty.k === 'dyn')
        (0, diag_1.reject)(call, 'any-op', 'calling a value of type any/unknown');
    if (f.ty.k === 'box' && f.ty.t.k === 'fn')
        f = this.unboxFn(f);
    if (f.ty.k !== 'fn')
        (0, diag_1.reject)(call, 'unsupported', `calling a value of type ${(0, ty_1.prettyTy)(f.ty)}`);
    const args = this.lowerCallArgs(fnSpecs(f.ty), call.arguments, fc, call, [() => f]);
    return ir_1.E.app(args[0], args.slice(1));
};
// ---------------------------------------------------------------------------------------
// library: global functions and namespaces
function lowerLibFunction(tr, name, call, fc, exp) {
    switch (name) {
        case 'String': {
            const a = argc(call, 0, 1, 'String');
            if (!a.length)
                return (0, core_1.strLit)('');
            return tr.toStr(tr.lowerExpr(a[0], fc), a[0]);
        }
        case 'Number': {
            const a = argc(call, 0, 1, 'Number');
            if (!a.length)
                return (0, core_1.numLit)(0);
            return numberOf(tr, tr.lowerExpr(a[0], fc), a[0]);
        }
        case 'BigInt': {
            const a = argc(call, 1, 1, 'BigInt');
            const x = tr.unfoldE(tr.lowerExpr(a[0], fc));
            if (x.ty.k === 'num')
                return Pr('.bigOfNum', [x], [ty_1.T.num], ty_1.T.bigint);
            if (x.ty.k === 'str')
                return Pr('.strToBig', [x], [ty_1.T.str], ty_1.T.bigint);
            if (x.ty.k === 'bigint')
                return x;
            if (x.ty.k === 'bool')
                return ir_1.E.cond(x, (0, core_1.bigLit)(1n), (0, core_1.bigLit)(0n));
            (0, diag_1.reject)(call, 'unsupported-builtin', `BigInt(...) of ${(0, ty_1.prettyTy)(x.ty)}`);
        }
        case 'Boolean': {
            const a = argc(call, 1, 1, 'Boolean');
            return tr.lowerCond(a[0], fc);
        }
        case 'parseInt': {
            const a = argc(call, 1, 2, 'parseInt');
            const args = tr.seq([() => tr.lowerExpr(a[0], fc, ty_1.T.str), () => a[1] ? tr.lowerExpr(a[1], fc, ty_1.T.num) : (0, core_1.numLit)(0)], fc);
            return Pr('.parseInt', args, [ty_1.T.str, ty_1.T.num], ty_1.T.num);
        }
        case 'parseFloat': {
            const a = argc(call, 1, 1, 'parseFloat');
            return Pr('.parseFloat', [tr.lowerExpr(a[0], fc, ty_1.T.str)], [ty_1.T.str], ty_1.T.num);
        }
        case 'isNaN':
        case 'isFinite': {
            const a = argc(call, 1, 1, name);
            return Pr(`(.numPred .${name})`, [tr.lowerExpr(a[0], fc, ty_1.T.num)], [ty_1.T.num], ty_1.T.bool);
        }
        case 'setTimeout': {
            const a = argc(call, 1, 2, 'setTimeout');
            const [cb, ms] = tr.seq([() => tr.lowerCallback(a[0], fc, ty_1.T.fn([], ty_1.T.undef)), () => timerDelay(tr, a[1], fc)], fc);
            const id = B('.setTimeout', [cb, ms], [ty_1.T.fn([], ty_1.T.undef), ty_1.T.num], ty_1.T.num);
            // (Node's types: a `NodeJS.Timeout` object holding the number)
            return (0, ty_1.tyEq)(tr.tyAt(call, fc), ty_1.TIMER_TY) ? ir_1.E.mkRec(ty_1.TIMER_TY, [id]) : id;
        }
        case 'queueMicrotask': {
            const a = argc(call, 1, 1, 'queueMicrotask');
            return B('.queueMicrotask', [tr.lowerCallback(a[0], fc, ty_1.T.fn([], ty_1.T.undef))], [ty_1.T.fn([], ty_1.T.undef)], ty_1.T.undef);
        }
        case 'Array': (0, diag_1.reject)(call, 'unsupported-builtin', '`Array(n)` creates holes; use `Array(n).fill(x)` or `Array.from`');
    }
    void exp;
    (0, diag_1.reject)(call, 'unsupported-builtin', `${name}(...) is not supported`);
}
function lowerLibStatic(tr, ns, name, call, fc, exp) {
    const key = `${ns}.${name}`;
    if (ns === 'console') {
        // console.warn / console.error write to the process's standard error, outside the modelled
        // state: externs with no result (the oracle sees their arguments)
        if (name === 'warn' || name === 'error')
            return tr.lowerExternCall(call, fc, exp, `console.${name}`, undefined);
        // (console.info and console.debug write to standard output, as console.log does)
        if (name !== 'log' && name !== 'info' && name !== 'debug')
            (0, diag_1.reject)(call, 'console', `console.${name} is not modelled (only console.log of one string, console.warn and console.error)`);
        if (call.arguments.length > 1)
            (0, diag_1.reject)(call, 'console', `console.${name} with ${call.arguments.length} arguments (only one string is modelled)`);
        const a = argc(call, 0, 1, 'console.log');
        if (!a.length)
            return B('.log', [(0, core_1.strLit)('')], [ty_1.T.str], ty_1.T.undef);
        const e = tr.unfoldE(tr.lowerExpr(a[0], fc));
        if ((0, ir_1.isPoison)(e))
            return B('.log', [ir_1.E.poison(ty_1.T.str)], [ty_1.T.str], ty_1.T.undef);
        if (e.ty.k !== 'str' && e.ty.k !== 'enum')
            (0, diag_1.reject)(a[0], 'console', `console.log of ${(0, ty_1.prettyTy)(e.ty)} (only strings are printed; use a template literal)`);
        return B('.log', [tr.toStr(e, a[0])], [ty_1.T.str], ty_1.T.undef);
    }
    if (ns === 'Math') {
        if (MATH_UN.has(name)) {
            const a = argc(call, 1, 1, key);
            return Pr(`(.numUn .${name})`, [tr.lowerExpr(a[0], fc, ty_1.T.num)], [ty_1.T.num], ty_1.T.num);
        }
        if (name === 'max' || name === 'min') {
            const a = call.arguments;
            if (a.some(ts.isSpreadElement)) {
                // `Math.max(x, ...xs)`: a fold from -Infinity (Infinity for min) over the arguments in
                // order, a spread array through arrReduce (max/min propagate NaN, +0 above -0)
                const op = `(.numBin .${name})`;
                const na = ty_1.T.arr(ty_1.T.num);
                const vals = tr.seq(a.map(x => () => ts.isSpreadElement(x) ? tr.lowerExpr(x.expression, fc, na) : tr.lowerExpr(x, fc, ty_1.T.num)), fc);
                let acc = (0, core_1.numLit)(name === 'max' ? -Infinity : Infinity);
                vals.forEach((v, i) => {
                    if (ts.isSpreadElement(a[i])) {
                        const m = (0, ir_1.mkVar)('m', ty_1.T.num), x = (0, ir_1.mkVar)('x', ty_1.T.num), j = (0, ir_1.mkVar)('i', ty_1.T.num), arr = (0, ir_1.mkVar)('a', na);
                        const f = ir_1.E.lam(false, [m, x, j, arr], ty_1.T.num, [(0, ir_1.stmtItem)(ir_1.S.ret(Pr(op, [ir_1.E.var(m), ir_1.E.var(x)], [ty_1.T.num, ty_1.T.num], ty_1.T.num)))]);
                        acc = B('(.arrReduce .num .num)', [v, f, acc], [na, ty_1.T.fn([ty_1.T.num, ty_1.T.num, ty_1.T.num, na], ty_1.T.num), ty_1.T.num], ty_1.T.num);
                    }
                    else
                        acc = Pr(op, [acc, v], [ty_1.T.num, ty_1.T.num], ty_1.T.num);
                });
                return acc;
            }
            if (!a.length)
                return (0, core_1.numLit)(name === 'max' ? -Infinity : Infinity);
            const xs = tr.seq(a.map(x => () => tr.lowerExpr(x, fc, ty_1.T.num)), fc);
            if (xs.length === 1)
                return Pr('(.numBin .max)', [xs[0], xs[0]], [ty_1.T.num, ty_1.T.num], ty_1.T.num);
            let acc = xs[0];
            for (let i = 1; i < xs.length; i++)
                acc = Pr(`(.numBin .${name})`, [acc, xs[i]], [ty_1.T.num, ty_1.T.num], ty_1.T.num);
            return acc;
        }
        if (name === 'pow' || name === 'atan2' || name === 'hypot' || name === 'imul') {
            const a = argc(call, 2, 2, key);
            const xs = tr.seq(a.map(x => () => tr.lowerExpr(x, fc, ty_1.T.num)), fc);
            return Pr(`(.numBin .${name})`, xs, [ty_1.T.num, ty_1.T.num], ty_1.T.num);
        }
        if (name === 'random') {
            argc(call, 0, 0, key);
            return B('.random', [], [], ty_1.T.num);
        }
    }
    if (ns === 'Number') {
        if (['isInteger', 'isSafeInteger', 'isFinite', 'isNaN'].includes(name)) {
            const a = argc(call, 1, 1, key);
            return (0, exprs_1.numberPred)(tr, tr.lowerExpr(a[0], fc), name);
        }
        if (name === 'parseFloat' || name === 'parseInt')
            return lowerLibFunction(tr, name, call, fc, exp);
    }
    if (ns === 'BigInt' && (name === 'asIntN' || name === 'asUintN')) {
        const a = argc(call, 2, 2, key);
        const xs = tr.seq([() => tr.lowerExpr(a[0], fc, ty_1.T.num), () => tr.lowerExpr(a[1], fc, ty_1.T.bigint)], fc);
        return Pr(name === 'asIntN' ? '.bigAsIntN' : '.bigAsUintN', xs, [ty_1.T.num, ty_1.T.bigint], ty_1.T.bigint);
    }
    if (ns === 'String' && name === 'fromCodePoint') {
        // each argument (a spread one: its elements), checked as a code point (RangeError
        // otherwise), as one or two UTF-16 code units
        const a = call.arguments;
        if (!a.length)
            return (0, core_1.strLit)('');
        let arr;
        if (a.length === 1 && ts.isSpreadElement(a[0]))
            arr = tr.coerce(tr.lowerExpr(a[0].expression, fc), ty_1.T.arr(ty_1.T.num), a[0]);
        else {
            if (a.some(ts.isSpreadElement))
                (0, diag_1.reject)(call, 'unsupported-builtin', 'String.fromCodePoint with spread and other arguments');
            const xs = tr.seq(a.map(x => () => tr.lowerExpr(x, fc, ty_1.T.num)), fc);
            arr = B(`(.arrOf .num ${xs.length})`, xs, xs.map(() => ty_1.T.num), ty_1.T.arr(ty_1.T.num));
        }
        const ps = [(0, ir_1.mkVar)('c', ty_1.T.num), (0, ir_1.mkVar)('i', ty_1.T.num), (0, ir_1.mkVar)('a', ty_1.T.arr(ty_1.T.num))];
        const c = ir_1.E.var(ps[0]);
        const cmp = (op, k) => Pr(`(.numCmp .${op})`, [c, (0, core_1.numLit)(k)], [ty_1.T.num, ty_1.T.num], ty_1.T.bool);
        const bin = (op, x, k) => Pr(`(.numBin .${op})`, [x, (0, core_1.numLit)(k)], [ty_1.T.num, ty_1.T.num], ty_1.T.num);
        const unit = (x) => Pr('.fromCharCode', [x], [ty_1.T.num], ty_1.T.str);
        const ok = ir_1.E.and(Pr('(.numPred .isInteger)', [c], [ty_1.T.num], ty_1.T.bool), ir_1.E.and(cmp('ge', 0), cmp('le', 0x10ffff)));
        const msg = Pr('.strConcat', [(0, core_1.strLit)('Invalid code point '), Pr('.numToStr', [c], [ty_1.T.num], ty_1.T.str)], [ty_1.T.str, ty_1.T.str], ty_1.T.str);
        const off = bin('sub', c, 0x10000);
        const pair = Pr('.strConcat', [unit(bin('add', Pr('(.numUn .floor)', [bin('div', off, 0x400)], [ty_1.T.num], ty_1.T.num), 0xd800)), unit(bin('add', bin('rem', off, 0x400), 0xdc00))], [ty_1.T.str, ty_1.T.str], ty_1.T.str);
        const body = [
            (0, ir_1.stmtItem)(ir_1.S.ite(ir_1.E.not(ok), [(0, ir_1.stmtItem)(ir_1.S.throw(Pr('(.errNew .rangeError)', [msg], [ty_1.T.str], ty_1.T.err)))], [])),
            (0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.cond(cmp('le', 0xffff), unit(c), pair))),
        ];
        const f = ir_1.E.lam(false, ps, ty_1.T.str, body);
        const strs = B('(.arrMap .num .str)', [arr, f], [ty_1.T.arr(ty_1.T.num), ty_1.T.fn([ty_1.T.num, ty_1.T.num, ty_1.T.arr(ty_1.T.num)], ty_1.T.str)], ty_1.T.arr(ty_1.T.str));
        return B('.arrJoin', [strs, (0, core_1.strLit)('')], [ty_1.T.arr(ty_1.T.str), ty_1.T.str], ty_1.T.str);
    }
    if (ns === 'String' && name === 'fromCharCode') {
        const a = call.arguments;
        if (!a.length)
            return (0, core_1.strLit)('');
        const xs = tr.seq(a.map(x => () => tr.lowerExpr(x, fc, ty_1.T.num)), fc).map(x => Pr('.fromCharCode', [x], [ty_1.T.num], ty_1.T.str));
        return xs.reduce((acc, x) => Pr('.strConcat', [acc, x], [ty_1.T.str, ty_1.T.str], ty_1.T.str));
    }
    if (ns === 'Promise')
        return lowerPromiseStatic(tr, name, call, fc, exp);
    if (ns === 'Date' && name === 'now') {
        argc(call, 0, 0, key);
        return B('.now', [], [], ty_1.T.num);
    }
    if (ns === 'Array') {
        if (name === 'from')
            return lowerArrayFrom(tr, call, fc, exp);
        if (name === 'isArray' && !tr.strict) {
            // decided on the runtime value (typed values are seen as unknown)
            const a = argc(call, 1, 1, key);
            const x = tr.unfoldE(tr.lowerExpr(a[0], fc));
            const d = x.ty.k === 'dyn' ? x : Pr(`(.toDyn ${st(x.ty)})`, [x], [x.ty], ty_1.T.dyn);
            return Pr('.dynIsArray', [d], [ty_1.T.dyn], ty_1.T.bool);
        }
        if (name === 'of') {
            const rt = exp ?? tr.tyAt(call, fc);
            if (rt.k !== 'arr')
                (0, diag_1.reject)(call, 'unsupported-builtin', 'Array.of');
            const xs = tr.seq(call.arguments.map(x => () => tr.lowerExpr(x, fc, rt.t)), fc);
            return B(`(.arrOf ${st(rt.t)} ${xs.length})`, xs, xs.map(() => rt.t), rt);
        }
    }
    if (ns === 'Object' && (name === 'keys' || name === 'values' || name === 'entries' || name === 'assign' || name === 'freeze')) {
        (0, diag_1.reject)(call, 'unsupported-builtin', `Object.${name} (records have no property order in StrictTS)`);
    }
    (0, diag_1.reject)(call, 'unsupported-builtin', `${key} is not supported`);
}
function lowerPromiseStatic(tr, name, call, fc, exp) {
    const rt = exp && exp.k === 'promise' ? exp : tr.tyAt(call, fc);
    if (rt.k !== 'promise')
        (0, diag_1.reject)(call, 'unsupported-builtin', `Promise.${name}`);
    switch (name) {
        case 'resolve': {
            const a = argc(call, 0, 1, 'Promise.resolve');
            if (!a.length)
                return B(`(.promResolve .undef)`, [ir_1.E.undef()], [ty_1.T.undef], ty_1.T.promise(ty_1.T.undef));
            const v = tr.lowerExpr(a[0], fc);
            if (v.ty.k === 'promise')
                return v; // Promise.resolve(p) returns p itself
            const c = tr.coerce(v, rt.t, a[0]);
            return B(`(.promResolve ${st(rt.t)})`, [c], [rt.t], rt);
        }
        case 'reject': {
            const a = argc(call, 1, 1, 'Promise.reject');
            return B(`(.promReject ${st(rt.t)})`, [tr.lowerExpr(a[0], fc, ty_1.T.err)], [ty_1.T.err], rt);
        }
        case 'all':
        case 'race': {
            const a = argc(call, 1, 1, `Promise.${name}`);
            let elem = name === 'all' ? (rt.t.k === 'arr' ? rt.t.t : null) : rt.t;
            // Promise.all of a tuple whose elements have one type resolves to an array of it
            if (name === 'all' && rt.t.k === 'tup' && rt.t.ts.length > 0 && rt.t.ts.every(x => (0, ty_1.tyEq)(x, rt.t.ts[0])))
                elem = rt.t.ts[0];
            // a tuple of different types (or the empty tuple): one reaction per element, typed slots
            if (name === 'all' && !elem && rt.t.k === 'tup') {
                const tts = rt.t.ts;
                const tup = lowerPromiseTuple(tr, a[0], tts, fc, call, name);
                return B(`(.promAllTup ${showTysOf(tts)})`, [tup], [tup.ty], ty_1.T.promise(ty_1.T.tup(tts)));
            }
            if (!elem)
                (0, diag_1.reject)(call, 'unsupported-builtin', 'Promise.all of a tuple of different types');
            let arr;
            const lit = (0, stmts_1.skipParens)(a[0]);
            if (ts.isArrayLiteralExpression(lit) && !lit.elements.some(ts.isSpreadElement)) {
                // plain values in the array are wrapped like PromiseResolve does (a resolved promise)
                const el = elem;
                const parts = tr.seq(lit.elements.map(x => () => {
                    const v = tr.lowerExpr(x, fc);
                    if (v.ty.k === 'promise')
                        return tr.coerce(v, ty_1.T.promise(el), x);
                    return B(`(.promResolve ${st(el)})`, [tr.coerce(v, el, x)], [el], ty_1.T.promise(el));
                }), fc);
                arr = B(`(.arrOf ${st(ty_1.T.promise(el))} ${parts.length})`, parts, parts.map(() => ty_1.T.promise(el)), ty_1.T.arr(ty_1.T.promise(el)));
            }
            else
                arr = tr.lowerExpr(a[0], fc, ty_1.T.arr(ty_1.T.promise(elem)));
            return B(`(.${name === 'all' ? 'promAll' : 'promRace'} ${st(elem)})`, [arr], [ty_1.T.arr(ty_1.T.promise(elem))], name === 'all' ? ty_1.T.promise(ty_1.T.arr(elem)) : ty_1.T.promise(elem));
        }
        case 'allSettled': {
            // PromiseSettledResult<T> (StrictTS/Core/Ty.lean `Ty.settled`): `reason: any` needs
            // `unknown` values, so not in --strict
            const a = argc(call, 1, 1, 'Promise.allSettled');
            if (rt.t.k === 'tup' && rt.t.ts.every(x => settledValueTy(x) !== null)) {
                const tts = rt.t.ts.map(x => settledValueTy(x));
                const tup = lowerPromiseTuple(tr, a[0], tts, fc, call, name);
                return B(`(.promAllSettledTup ${showTysOf(tts)})`, [tup], [tup.ty], ty_1.T.promise(ty_1.T.tup(tts.map(settledTy))));
            }
            const elem = rt.t.k === 'arr' ? settledValueTy(rt.t.t) : null;
            if (elem === null)
                (0, diag_1.reject)(call, 'unsupported-builtin', `Promise.allSettled with the result type ${(0, ty_1.prettyTy)(rt.t)} (${st(rt.t)})`);
            const el = elem;
            let arr;
            const lit = (0, stmts_1.skipParens)(a[0]);
            if (ts.isArrayLiteralExpression(lit) && !lit.elements.some(ts.isSpreadElement)) {
                const parts = tr.seq(lit.elements.map(x => () => promiseOf(tr, x, el, fc)), fc);
                arr = B(`(.arrOf ${st(ty_1.T.promise(el))} ${parts.length})`, parts, parts.map(() => ty_1.T.promise(el)), ty_1.T.arr(ty_1.T.promise(el)));
            }
            else
                arr = tr.lowerExpr(a[0], fc, ty_1.T.arr(ty_1.T.promise(el)));
            return B(`(.promAllSettled ${st(el)})`, [arr], [ty_1.T.arr(ty_1.T.promise(el))], ty_1.T.promise(ty_1.T.arr(settledTy(el))));
        }
    }
    (0, diag_1.reject)(call, 'unsupported-builtin', `Promise.${name} is not supported`);
}
/** `Tys` term of a list of types. */
function showTysOf(tts) {
    return `tys[${tts.map(st).join(', ')}]`;
}
/** A promise of `el` from an element of a `Promise.all`-like array: a promise as it is, a plain
 * value as a resolved promise (what PromiseResolve does, with the same jobs). */
function promiseOf(tr, x, el, fc) {
    const v = tr.lowerExpr(x, fc);
    if (v.ty.k === 'promise')
        return tr.coerce(v, ty_1.T.promise(el), x);
    return B(`(.promResolve ${st(el)})`, [tr.coerce(v, el, x)], [el], ty_1.T.promise(el));
}
/** The tuple of promises (of the types `tts`) that `Promise.all` / `Promise.allSettled` take
 * over a tuple: an array literal element by element, otherwise a value of that tuple type. */
function lowerPromiseTuple(tr, a0, tts, fc, call, name) {
    const lit = (0, stmts_1.skipParens)(a0);
    if (ts.isArrayLiteralExpression(lit) && !lit.elements.some(ts.isSpreadElement)) {
        if (lit.elements.length !== tts.length)
            (0, diag_1.reject)(call, 'unsupported-builtin', `Promise.${name} of ${lit.elements.length} values typed as ${tts.length}`);
        return ir_1.E.mkTup(tr.seq(lit.elements.map((x, i) => () => promiseOf(tr, x, tts[i], fc)), fc));
    }
    return tr.lowerExpr(a0, fc, ty_1.T.tup(tts.map(ty_1.T.promise)));
}
/** TypeScript's `PromiseSettledResult<T>` as StrictTS translates it (`Ty.settled` in Core/Ty.lean). */
function settledTy(t) {
    return ty_1.T.union([
        ty_1.T.record([{ name: 'reason', ty: ty_1.T.dyn }, { name: 'status', ty: ty_1.T.str }]),
        ty_1.T.record([{ name: 'status', ty: ty_1.T.str }, { name: 'value', ty: t }]),
    ]);
}
/** `T` when `u` is `PromiseSettledResult<T>`. */
function settledValueTy(u) {
    if (u.k !== 'union' || u.ts.length !== 2)
        return null;
    const f = u.ts[1];
    if (f.k !== 'record' || f.fs.length !== 2 || f.fs[1].name !== 'value')
        return null;
    return (0, ty_1.tyEq)(u, settledTy(f.fs[1].ty)) ? f.fs[1].ty : null;
}
function lowerArrayFrom(tr, call, fc, exp) {
    const a = argc(call, 1, 2, 'Array.from');
    const rt = exp && exp.k === 'arr' ? exp : tr.tyAt(call, fc);
    if (rt.k !== 'arr')
        (0, diag_1.reject)(call, 'unsupported-builtin', 'Array.from');
    const src = (0, stmts_1.skipParens)(a[0]);
    // Array.from({ length: n }, (_, i) => …)
    if (ts.isObjectLiteralExpression(src) && src.properties.length === 1) {
        const p = src.properties[0];
        if (ts.isPropertyAssignment(p) && ts.isIdentifier(p.name) && p.name.text === 'length') {
            if (!a[1])
                (0, diag_1.reject)(call, 'unsupported-builtin', 'Array.from({ length }) without a map function creates undefined elements');
            const [n, f] = tr.seq([() => tr.lowerExpr(p.initializer, fc, ty_1.T.num), () => tr.lowerCallback(a[1], fc, ty_1.T.fn([ty_1.T.undef, ty_1.T.num], rt.t))], fc);
            return B(`(.arrFromFn ${st(rt.t)})`, [n, f], [ty_1.T.num, ty_1.T.fn([ty_1.T.undef, ty_1.T.num], rt.t)], rt);
        }
    }
    let arr;
    if (ts.isCallExpression(src) && ts.isPropertyAccessExpression(src.expression) && src.arguments.length === 0 &&
        ['keys', 'values', 'entries'].includes(src.expression.name.text)) {
        const base = tr.lowerExpr(src.expression.expression, fc);
        arr = tr.collectionSnapshot(base, src.expression.name.text, src);
    }
    else {
        // a union of array types (e.g. `s.match(re) ?? []`: RegExpMatchArray | undefined[]) is lowered at
        // the result's array type when there is no map function
        const srcTy = tr.checker.getTypeAtLocation(src);
        const arrays = srcTy.isUnion() && srcTy.types.every(t => tr.checker.isArrayType(t) || tr.checker.isArrayLikeType(t));
        const x = tr.unfoldE(tr.lowerExpr(src, fc, arrays && !a[1] ? rt : undefined));
        if (x.ty.k === 'arr')
            arr = B(`(.arrCopy ${st(x.ty.t)})`, [x], [x.ty], x.ty);
        else if (x.ty.k === 'set')
            arr = tr.collectionSnapshot(x, 'values', src);
        else if (x.ty.k === 'map')
            arr = tr.collectionSnapshot(x, 'entries', src);
        else if (x.ty.k === 'str' || x.ty.k === 'enum')
            arr = tr.codePoints(x, fc, src);
        else
            (0, diag_1.reject)(src, 'unsupported-builtin', `Array.from of ${(0, ty_1.prettyTy)(x.ty)}`);
    }
    if (!a[1])
        return tr.coerce(arr, rt, call);
    const at = arr.ty;
    const cbTy = ty_1.T.fn([at.t, ty_1.T.num, at], rt.t);
    const v = tr.spill(arr, fc, 'src');
    const f = tr.lowerCallback(a[1], fc, cbTy);
    return B(`(.arrMap ${st(at.t)} ${st(rt.t)})`, [v, f], [at, cbTy], rt);
}
// ---------------------------------------------------------------------------------------
// methods
P.lowerMethodCall = function (base0, name, call, fc, exp) {
    if ((0, ir_1.isPoison)(base0)) {
        for (const a of call.arguments)
            this.lowerExpr(ts.isSpreadElement(a) ? a.expression : a, fc);
        return this.derivedPoison(call, fc, exp);
    }
    const base = this.unfoldE(base0);
    const t = base.ty;
    switch (t.k) {
        case 'obj': {
            const ci = this.types.classes.get(t.c);
            if (ci) {
                const f = this.classMember(ci, name, 'method', call);
                if (f) {
                    const decl = ci.decl.members.find(m => ts.isMethodDeclaration(m) && m.name && m.name.text === name);
                    const args = this.lowerCallArgs(this.paramSpecs(decl, ci.subst), call.arguments, fc, call, [() => base]);
                    return ir_1.E.call(f, args);
                }
            }
            let fv = this.unfoldE(this.readField(base, name, call));
            if (fv.ty.k === 'opt')
                fv = this.unfoldE(this.adapt(fv, this.tyAt(call.expression, fc), call));
            if (fv.ty.k === 'box' && fv.ty.t.k === 'fn')
                fv = this.unboxFn(fv);
            if (fv.ty.k !== 'fn')
                (0, diag_1.reject)(call, 'unsupported', `${name} is not a method`);
            const args = this.lowerCallArgs(fnSpecs(fv.ty), call.arguments, fc, call, [() => fv]);
            return ir_1.E.app(args[0], args.slice(1));
        }
        case 'record': {
            if ((0, ty_1.tyEq)(t, ty_1.TIMER_TY))
                (0, diag_1.reject)(call, 'timer-handle', `${name}() of a Node timer handle (ref, unref, hasRef, refresh) is not modelled`);
            const i = t.fs.findIndex(f => f.name === name);
            if (i < 0)
                (0, diag_1.reject)(call, 'unsupported', `no method ${name}`);
            let fv = this.unfoldE(ir_1.E.getRec(base, i));
            if (fv.ty.k === 'opt')
                fv = this.unfoldE(this.adapt(fv, this.tyAt(call.expression, fc), call));
            if (fv.ty.k === 'box' && fv.ty.t.k === 'fn')
                fv = this.unboxFn(fv);
            if (fv.ty.k !== 'fn')
                (0, diag_1.reject)(call, 'unsupported', `${name} is not a function`);
            const args = this.lowerCallArgs(fnSpecs(fv.ty), call.arguments, fc, call, [() => fv]);
            return ir_1.E.app(args[0], args.slice(1));
        }
        case 'box':
            if (t.t.k === 'record')
                return this.lowerMethodCall(this.unboxCell(base), name, call, fc, exp);
            break;
        case 'fn':
            (0, diag_1.reject)(call, 'unsupported-builtin', `Function.prototype.${name}`);
        case 'dyn': {
            // an unknown value narrowed to `any[]` / `unknown[]`: the array methods, on the array as
            // an array of unknown values (a checked cast: arrays of another element type panic)
            const callee = (0, stmts_1.skipParens)(call.expression);
            let rt;
            try {
                rt = ts.isPropertyAccessExpression(callee) ? this.unfoldTy(this.tyAt(callee.expression, fc)) : undefined;
            }
            catch {
                rt = undefined;
            }
            if (rt && rt.k === 'arr' && rt.t.k === 'dyn') {
                const at = ty_1.T.arr(ty_1.T.dyn);
                return arrayMethod(this, ir_1.E.unwrap(Pr('(.dynCast (.arr .dyn))', [base], [ty_1.T.dyn], ty_1.T.opt(at))), at, name, call, fc, exp);
            }
            (0, diag_1.reject)(call, 'any-op', `method call ${name} on a value of type any/unknown`);
        }
        case 'arr': return arrayMethod(this, base, t, name, call, fc, exp);
        case 'str': return stringMethod(this, base, name, call, fc);
        case 'enum': return stringMethod(this, this.toStr(base, call), name, call, fc);
        case 'map': return mapMethod(this, base, t, name, call, fc);
        case 'set': return setMethod(this, base, t, name, call, fc);
        case 'promise': return promiseMethod(this, base, t, name, call, fc, exp);
        case 'num': return numberMethod(this, base, name, call, fc);
        case 'bigint':
            if (name === 'toString') {
                argc(call, 0, 0, 'bigint.toString (with radix)');
                return Pr('.bigToStr', [base], [ty_1.T.bigint], ty_1.T.str);
            }
            break;
        case 'bool':
            if (name === 'toString') {
                argc(call, 0, 0, 'toString');
                return Pr('.boolToStr', [base], [ty_1.T.bool], ty_1.T.str);
            }
            break;
        case 'err':
            if (name === 'toString') {
                argc(call, 0, 0, 'toString');
                return this.toStr(base, call);
            }
            break;
        case 'tarr': return typedArrayMethod(this, base, t, name, call, fc);
        case 'tup': {
            // read-only array methods on a homogeneous tuple act on a fresh array of its elements
            const MUT = ['push', 'pop', 'shift', 'unshift', 'splice', 'sort', 'reverse', 'fill'];
            if (MUT.includes(name))
                (0, diag_1.reject)(call, 'unsupported-builtin', `tuples are immutable (${name})`);
            if (t.ts.length === 0 || !t.ts.every(x => (0, ty_1.tyEq)(x, t.ts[0])))
                (0, diag_1.reject)(call, 'unsupported-builtin', `method ${name} on a heterogeneous tuple`);
            const at = ty_1.T.arr(t.ts[0]);
            const arr = this.withValue(base, 'p', x => B(`(.arrOf ${st(at.t)} ${t.ts.length})`, t.ts.map((_, i) => ir_1.E.getTup(x, i)), t.ts.map(() => at.t), at));
            return arrayMethod(this, arr, at, name, call, fc, exp);
        }
    }
    (0, diag_1.reject)(call, 'unsupported-builtin', `method ${name} of ${(0, ty_1.prettyTy)(t)} is not supported`);
};
function cbTy3(t, ret) { return ty_1.T.fn([t, ty_1.T.num, ty_1.T.arr(t)], ret); }
function arrayMethod(tr, a, at, name, call, fc, exp) {
    const t = at.t;
    const args = call.arguments;
    const S2 = (thunks) => tr.seq([() => a, ...thunks], fc);
    const resultArr = () => {
        const r = exp && exp.k === 'arr' ? exp : tr.tyAt(call, fc);
        if (r.k !== 'arr')
            (0, diag_1.reject)(call, 'unsupported-builtin', `${name} result type`);
        return r;
    };
    switch (name) {
        case 'push': {
            if (args.some(ts.isSpreadElement)) {
                // `a.push(x, ...ys)`: every argument is evaluated first (a spread array as a snapshot),
                // then the values are pushed in order; the value is the new length
                const vs = S2(args.map(e => () => ts.isSpreadElement(e)
                    ? B(`(.arrCopy ${st(t)})`, [tr.lowerExpr(e.expression, fc, at)], [at], at)
                    : tr.lowerExpr(e, fc, t)));
                const arr = tr.spill(vs[0], fc, 'a');
                const vals = vs.slice(1).map(v => ir_1.E.var(tr.bindTemp(v, fc, 'v')));
                args.forEach((e, i) => {
                    if (ts.isSpreadElement(e)) {
                        const el = (0, ir_1.mkVar)('x', t);
                        fc.pre.push((0, ir_1.stmtItem)({ k: 'forOf', e: vals[i], v: el, body: [(0, ir_1.stmtItem)(ir_1.S.expr(B(`(.arrPush ${st(t)})`, [arr, ir_1.E.var(el)], [at, t], ty_1.T.num)))] }));
                    }
                    else
                        fc.pre.push((0, ir_1.stmtItem)(ir_1.S.expr(B(`(.arrPush ${st(t)})`, [arr, vals[i]], [at, t], ty_1.T.num))));
                });
                return B(`(.arrLength ${st(t)})`, [arr], [at], ty_1.T.num);
            }
            argc(call, 1, 1000, 'push');
            if (args.length === 1) {
                const [x, v] = S2([() => tr.lowerExpr(args[0], fc, t)]);
                return B(`(.arrPush ${st(t)})`, [x, v], [at, t], ty_1.T.num);
            }
            const vs = S2(args.map(e => () => tr.lowerExpr(e, fc, t)));
            const arr = tr.spill(vs[0], fc, 'a');
            const vals = vs.slice(1).map(v => tr.spill(v, fc, 'v'));
            let acc = B(`(.arrPush ${st(t)})`, [arr, vals[vals.length - 1]], [at, t], ty_1.T.num);
            for (let i = vals.length - 2; i >= 0; i--) {
                acc = ir_1.E.letE((0, ir_1.mkVar)('_', ty_1.T.num), B(`(.arrPush ${st(t)})`, [arr, vals[i]], [at, t], ty_1.T.num), acc);
            }
            return acc;
        }
        case 'pop':
            argc(call, 0, 0, 'pop');
            return B(`(.arrPop ${st(t)})`, [a], [at], ty_1.T.opt(t));
        case 'shift':
            argc(call, 0, 0, 'shift');
            return B(`(.arrShift ${st(t)})`, [a], [at], ty_1.T.opt(t));
        case 'unshift': {
            argc(call, 1, 1, 'unshift');
            const [x, v] = S2([() => tr.lowerExpr(args[0], fc, t)]);
            return B(`(.arrUnshift ${st(t)})`, [x, v], [at, t], ty_1.T.num);
        }
        case 'slice': {
            argc(call, 0, 2, 'slice');
            const vs = S2([() => args[0] ? tr.lowerExpr(args[0], fc, ty_1.T.num) : (0, core_1.numLit)(0), () => args[1] ? tr.lowerExpr(args[1], fc, ty_1.T.opt(ty_1.T.num)) : ir_1.E.none(ty_1.T.num)]);
            return B(`(.arrSlice ${st(t)})`, vs, [at, ty_1.T.num, ty_1.T.opt(ty_1.T.num)], at);
        }
        case 'splice': {
            argc(call, 1, 1000, 'splice');
            const items = args.slice(2);
            const vs = S2([() => tr.lowerExpr(args[0], fc, ty_1.T.num), () => args[1] ? tr.lowerExpr(args[1], fc, ty_1.T.num) : (0, core_1.numLit)(Infinity),
                () => { const xs = tr.seq(items.map(e => () => tr.lowerExpr(e, fc, t)), fc); return B(`(.arrOf ${st(t)} ${xs.length})`, xs, xs.map(() => t), at); }]);
            return B(`(.arrSplice ${st(t)})`, vs, [at, ty_1.T.num, ty_1.T.num, at], at);
        }
        case 'concat': {
            argc(call, 1, 1000, 'concat');
            // concat spreads array arguments (decided at run time by IsArray) and appends the others; an
            // array that TypeScript types as one element of an array of arrays fails the conversion to `at`
            const isArrNode = (e) => {
                const et = tr.checker.getTypeAtLocation(e);
                return tr.checker.isArrayType(et) || tr.checker.isTupleType(et);
            };
            const vs = S2(args.map(e => () => {
                if (isArrNode(e))
                    return tr.lowerExpr(e, fc, at);
                return B(`(.arrOf ${st(t)} 1)`, [tr.lowerExpr(e, fc, t)], [t], at);
            }));
            let acc = vs[0];
            for (let i = 1; i < vs.length; i++)
                acc = B(`(.arrConcat ${st(t)})`, [acc, vs[i]], [at, at], at);
            return acc;
        }
        case 'indexOf':
        case 'lastIndexOf': {
            argc(call, 1, 2, name);
            if (!(0, ty_1.eqable)(t))
                (0, diag_1.reject)(call, 'no-record-eq', `${name} compares elements with === (${(0, ty_1.prettyTy)(t)} values have no identity); use findIndex`);
            const dflt = name === 'indexOf' ? (0, core_1.numLit)(0) : (0, core_1.numLit)(Infinity);
            const vs = S2([() => tr.lowerExpr(args[0], fc, t), () => args[1] ? tr.lowerExpr(args[1], fc, ty_1.T.num) : dflt]);
            return B(`(.${name === 'indexOf' ? 'arrIndexOf' : 'arrLastIndexOf'} ${st(t)})`, vs, [at, t, ty_1.T.num], ty_1.T.num);
        }
        case 'includes': {
            argc(call, 1, 1, 'includes (with fromIndex)');
            if (!(0, ty_1.eqable)(t))
                (0, diag_1.reject)(call, 'no-record-eq', `includes compares elements with SameValueZero (${(0, ty_1.prettyTy)(t)} values have no identity); use some`);
            const vs = S2([() => tr.lowerExpr(args[0], fc, t)]);
            return B(`(.arrIncludes ${st(t)})`, vs, [at, t], ty_1.T.bool);
        }
        case 'join':
        case 'toString': {
            if (name === 'toString')
                argc(call, 0, 0, 'toString');
            else
                argc(call, 0, 1, 'join');
            const vs = S2([() => args[0] ? tr.lowerExpr(args[0], fc, ty_1.T.str) : (0, core_1.strLit)(',')]);
            let arr = vs[0];
            if (t.k !== 'str') {
                const ps = [(0, ir_1.mkVar)('x', t), (0, ir_1.mkVar)('i', ty_1.T.num), (0, ir_1.mkVar)('a', at)];
                const conv = ir_1.E.lam(false, ps, ty_1.T.str, [(0, ir_1.stmtItem)(ir_1.S.ret(tr.toStr(ir_1.E.var(ps[0]), call)))]);
                arr = B(`(.arrMap ${st(t)} .str)`, [arr, conv], [at, cbTy3(t, ty_1.T.str)], ty_1.T.arr(ty_1.T.str));
            }
            return B('.arrJoin', [arr, vs[1]], [ty_1.T.arr(ty_1.T.str), ty_1.T.str], ty_1.T.str);
        }
        case 'reverse':
            argc(call, 0, 0, 'reverse');
            return B(`(.arrReverse ${st(t)})`, [a], [at], at);
        case 'fill': {
            argc(call, 1, 3, 'fill');
            const vs = S2([() => tr.lowerExpr(args[0], fc, t), () => args[1] ? tr.lowerExpr(args[1], fc, ty_1.T.num) : (0, core_1.numLit)(0),
                () => args[2] ? tr.lowerExpr(args[2], fc, ty_1.T.opt(ty_1.T.num)) : ir_1.E.none(ty_1.T.num)]);
            return B(`(.arrFill ${st(t)})`, vs, [at, t, ty_1.T.num, ty_1.T.opt(ty_1.T.num)], at);
        }
        case 'sort': {
            argc(call, 0, 1, 'sort');
            if (!args.length) {
                if (t.k !== 'str')
                    (0, diag_1.reject)(call, 'unsupported-builtin', 'sort() without a comparator compares string forms; pass a comparator');
                return B('.arrSortStr', [a], [at], at);
            }
            const ft = ty_1.T.fn([t, t], ty_1.T.num);
            const vs = S2([() => tr.lowerCallback(args[0], fc, ft)]);
            return B(`(.arrSort ${st(t)})`, vs, [at, ft], at);
        }
        case 'map':
        case 'flatMap': {
            argc(call, 1, 1, name);
            const r = resultArr();
            const u = r.t;
            const ft = cbTy3(t, name === 'map' ? u : ty_1.T.arr(u));
            const vs = S2([() => tr.lowerCallback(args[0], fc, ft)]);
            return B(`(.${name === 'map' ? 'arrMap' : 'arrFlatMap'} ${st(t)} ${st(u)})`, vs, [at, ft], r);
        }
        case 'flat': {
            argc(call, 0, 0, 'flat (with depth)');
            if (t.k !== 'arr')
                (0, diag_1.reject)(call, 'unsupported-builtin', 'flat on a non-nested array');
            const ps = [(0, ir_1.mkVar)('x', t), (0, ir_1.mkVar)('i', ty_1.T.num), (0, ir_1.mkVar)('a', at)];
            const id = ir_1.E.lam(false, ps, t, [(0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.var(ps[0])))]);
            return B(`(.arrFlatMap ${st(t)} ${st(t.t)})`, [a, id], [at, cbTy3(t, t)], t);
        }
        case 'filter':
        case 'find':
        case 'findIndex':
        case 'findLast':
        case 'findLastIndex':
        case 'some':
        case 'every': {
            argc(call, 1, 1, name);
            const ft = cbTy3(t, ty_1.T.bool);
            if (name === 'filter') {
                const r = exp && exp.k === 'arr' ? exp : tr.tyAt(call, fc);
                if (!(0, ty_1.tyEq)(r, at)) {
                    // a type-guard callback narrows the kept elements: filter, then convert each of them
                    // (the filtered array is fresh, so converting it into another fresh array is not
                    // observable; a wrong guard makes the conversion panic)
                    const conv = r.k === 'arr' ? tr.convert(ir_1.E.var((0, ir_1.mkVar)('x', t)), r.t, call, true, 0) : null;
                    if (r.k !== 'arr' || !conv)
                        (0, diag_1.reject)(call, 'unsupported-builtin', 'filter with a type-guard callback that changes the element type');
                    const vs0 = S2([() => tr.lowerCallback(args[0], fc, ft)]);
                    const kept = B(`(.arrFilter ${st(t)})`, vs0, [at, ft], at);
                    const x = (0, ir_1.mkVar)('x', t), i = (0, ir_1.mkVar)('i', ty_1.T.num), a = (0, ir_1.mkVar)('a', at);
                    const body = tr.convert(ir_1.E.var(x), r.t, call, true, 0);
                    const mt = ty_1.T.fn([t, ty_1.T.num, at], r.t);
                    return B(`(.arrMap ${st(t)} ${st(r.t)})`, [kept, ir_1.E.lam(false, [x, i, a], r.t, [(0, ir_1.stmtItem)(ir_1.S.ret(body))])], [at, mt], r);
                }
            }
            const vs = S2([() => tr.lowerCallback(args[0], fc, ft)]);
            const ret = name === 'filter' ? at : (name === 'find' || name === 'findLast') ? ty_1.T.opt(t) : (name === 'some' || name === 'every') ? ty_1.T.bool : ty_1.T.num;
            const op = { filter: 'arrFilter', find: 'arrFind', findIndex: 'arrFindIndex', findLast: 'arrFindLast', findLastIndex: 'arrFindLastIndex', some: 'arrSome', every: 'arrEvery' }[name];
            return B(`(.${op} ${st(t)})`, vs, [at, ft], ret);
        }
        case 'forEach': {
            argc(call, 1, 1, 'forEach');
            const ft = cbTy3(t, ty_1.T.undef);
            const vs = S2([() => tr.lowerCallback(args[0], fc, ft)]);
            return B(`(.arrForEach ${st(t)})`, vs, [at, ft], ty_1.T.undef);
        }
        case 'reduce':
        case 'reduceRight': {
            argc(call, 1, 2, name);
            if (args.length === 1) {
                if (name === 'reduceRight')
                    (0, diag_1.reject)(call, 'unsupported-builtin', 'reduceRight without an initial value');
                const ft = ty_1.T.fn([t, t, ty_1.T.num, at], t);
                const vs = S2([() => tr.lowerCallback(args[0], fc, ft)]);
                return B(`(.arrReduce1 ${st(t)})`, vs, [at, ft], t);
            }
            const u = exp ?? tr.tyAt(call, fc);
            const ft = ty_1.T.fn([u, t, ty_1.T.num, at], u);
            const vs = S2([() => tr.lowerCallback(args[0], fc, ft), () => tr.lowerExpr(args[1], fc, u)]);
            return B(`(.${name === 'reduce' ? 'arrReduce' : 'arrReduceRight'} ${st(t)} ${st(u)})`, vs, [at, ft, u], u);
        }
        case 'at': {
            argc(call, 1, 1, 'at');
            const vs = S2([() => tr.lowerExpr(args[0], fc, ty_1.T.num)]);
            return B(`(.arrAt ${st(t)})`, vs, [at, ty_1.T.num], ty_1.T.opt(t));
        }
    }
    (0, diag_1.reject)(call, 'unsupported-builtin', `array method ${name} is not supported`);
}
function stringMethod(tr, s, name, call, fc) {
    const args = call.arguments;
    const S2 = (thunks) => tr.seq([() => s, ...thunks], fc);
    const num = (i, dflt) => () => args[i] ? tr.lowerExpr(args[i], fc, ty_1.T.num) : dflt;
    const optNum = (i) => () => args[i] ? tr.lowerExpr(args[i], fc, ty_1.T.opt(ty_1.T.num)) : ir_1.E.none(ty_1.T.num);
    const str = (i) => () => tr.lowerExpr(args[i], fc, ty_1.T.str);
    switch (name) {
        case 'charAt':
        case 'charCodeAt':
            argc(call, 0, 1, name);
            return Pr(`.${name}`, S2([num(0, (0, core_1.numLit)(0))]), [ty_1.T.str, ty_1.T.num], name === 'charAt' ? ty_1.T.str : ty_1.T.num);
        case 'codePointAt':
            argc(call, 1, 1, name);
            return Pr('.codePointAt', S2([num(0, (0, core_1.numLit)(0))]), [ty_1.T.str, ty_1.T.num], ty_1.T.opt(ty_1.T.num));
        case 'at':
            argc(call, 1, 1, name);
            return Pr('.strAt', S2([num(0, (0, core_1.numLit)(0))]), [ty_1.T.str, ty_1.T.num], ty_1.T.opt(ty_1.T.str));
        case 'slice':
            argc(call, 0, 2, name);
            return Pr('.strSlice', S2([num(0, (0, core_1.numLit)(0)), optNum(1)]), [ty_1.T.str, ty_1.T.num, ty_1.T.opt(ty_1.T.num)], ty_1.T.str);
        case 'substring':
            argc(call, 1, 2, name);
            return Pr('.substring', S2([num(0, (0, core_1.numLit)(0)), optNum(1)]), [ty_1.T.str, ty_1.T.num, ty_1.T.opt(ty_1.T.num)], ty_1.T.str);
        case 'indexOf':
            argc(call, 1, 2, name);
            return Pr('.indexOf', S2([str(0), num(1, (0, core_1.numLit)(0))]), [ty_1.T.str, ty_1.T.str, ty_1.T.num], ty_1.T.num);
        case 'lastIndexOf':
            argc(call, 1, 2, name);
            return Pr('.lastIndexOf', S2([str(0), num(1, (0, core_1.numLit)(Infinity))]), [ty_1.T.str, ty_1.T.str, ty_1.T.num], ty_1.T.num);
        case 'includes':
            argc(call, 1, 2, name);
            return Pr('.strIncludes', S2([str(0), num(1, (0, core_1.numLit)(0))]), [ty_1.T.str, ty_1.T.str, ty_1.T.num], ty_1.T.bool);
        case 'startsWith':
            argc(call, 1, 2, name);
            return Pr('.startsWith', S2([str(0), num(1, (0, core_1.numLit)(0))]), [ty_1.T.str, ty_1.T.str, ty_1.T.num], ty_1.T.bool);
        case 'endsWith':
            argc(call, 1, 2, name);
            return Pr('.endsWith', S2([str(0), optNum(1)]), [ty_1.T.str, ty_1.T.str, ty_1.T.opt(ty_1.T.num)], ty_1.T.bool);
        case 'trim':
        case 'trimStart':
        case 'trimEnd':
            argc(call, 0, 0, name);
            return Pr(`.${name}`, [s], [ty_1.T.str], ty_1.T.str);
        case 'normalize': {
            // Unicode normalization (tables outside the semantics): an external call
            argc(call, 0, 1, name);
            const vs = S2([() => args[0] ? tr.toStr(tr.lowerExpr(args[0], fc), args[0]) : (0, core_1.strLit)('NFC')]);
            if (tr.coverage)
                tr.covExternals.add('String.normalize');
            return ir_1.E.extern('String.normalize', [vs[0], vs[1]], ty_1.T.str);
        }
        case 'padStart':
        case 'padEnd':
            argc(call, 1, 2, name);
            return Pr(`.${name}`, S2([num(0, (0, core_1.numLit)(0)), () => args[1] ? tr.lowerExpr(args[1], fc, ty_1.T.str) : (0, core_1.strLit)(' ')]), [ty_1.T.str, ty_1.T.num, ty_1.T.str], ty_1.T.str);
        case 'repeat':
            argc(call, 1, 1, name);
            return Pr('.strRepeat', S2([num(0, (0, core_1.numLit)(0))]), [ty_1.T.str, ty_1.T.num], ty_1.T.str);
        case 'replace':
        case 'replaceAll': {
            argc(call, 2, 2, name);
            const r = tr.unfoldTy(tr.tyAt(args[1], fc));
            if (r.k === 'fn')
                (0, diag_1.reject)(args[1], 'unsupported-builtin', `${name} with a replacer function`);
            return Pr(`.${name}`, S2([str(0), str(1)]), [ty_1.T.str, ty_1.T.str, ty_1.T.str], ty_1.T.str);
        }
        case 'toUpperCase':
        case 'toLowerCase':
            argc(call, 0, 0, name);
            return Pr(name === 'toUpperCase' ? '.toUpper' : '.toLower', [s], [ty_1.T.str], ty_1.T.str);
        case 'localeCompare':
            argc(call, 1, 1, name);
            return Pr('.localeCompare', S2([str(0)]), [ty_1.T.str, ty_1.T.str], ty_1.T.num);
        case 'split': {
            argc(call, 1, 1, 'split (with a limit)');
            const vs = S2([str(0)]);
            return ir_1.E.call(tr.splitHelper(), vs);
        }
        case 'concat': {
            const vs = S2(args.map(a => () => tr.toStr(tr.lowerExpr(a, fc), a)));
            return vs.reduce((acc, x) => Pr('.strConcat', [acc, x], [ty_1.T.str, ty_1.T.str], ty_1.T.str));
        }
        case 'toString':
        case 'valueOf':
            argc(call, 0, 0, name);
            return s;
    }
    (0, diag_1.reject)(call, 'unsupported-builtin', `string method ${name} is not supported`);
}
function mapMethod(tr, m, mt, name, call, fc) {
    const args = call.arguments;
    const K = mt.key, V = mt.val, ks = `${st(K)} ${st(V)}`;
    const S2 = (thunks) => tr.seq([() => m, ...thunks], fc);
    switch (name) {
        case 'get':
            argc(call, 1, 1, name);
            return B(`(.mapGet ${ks})`, S2([() => tr.lowerExpr(args[0], fc, K)]), [mt, K], ty_1.T.opt(V));
        case 'set':
            argc(call, 2, 2, name);
            return B(`(.mapSet ${ks})`, S2([() => tr.lowerExpr(args[0], fc, K), () => tr.lowerExpr(args[1], fc, V)]), [mt, K, V], mt);
        case 'has':
            argc(call, 1, 1, name);
            return B(`(.mapHas ${ks})`, S2([() => tr.lowerExpr(args[0], fc, K)]), [mt, K], ty_1.T.bool);
        case 'delete':
            argc(call, 1, 1, name);
            return B(`(.mapDelete ${ks})`, S2([() => tr.lowerExpr(args[0], fc, K)]), [mt, K], ty_1.T.bool);
        case 'clear':
            argc(call, 0, 0, name);
            return B(`(.mapClear ${ks})`, [m], [mt], ty_1.T.undef);
        case 'forEach': {
            argc(call, 1, 1, name);
            const ft = ty_1.T.fn([V, K, mt], ty_1.T.undef);
            return B(`(.mapForEach ${ks})`, S2([() => tr.lowerCallback(args[0], fc, ft)]), [mt, ft], ty_1.T.undef);
        }
    }
    (0, diag_1.reject)(call, 'unsupported-builtin', `Map method ${name} is not supported here`);
}
function setMethod(tr, s, sty, name, call, fc) {
    const args = call.arguments;
    const t = sty.t;
    const S2 = (thunks) => tr.seq([() => s, ...thunks], fc);
    switch (name) {
        case 'add':
            argc(call, 1, 1, name);
            return B(`(.setAdd ${st(t)})`, S2([() => tr.lowerExpr(args[0], fc, t)]), [sty, t], sty);
        case 'has':
            argc(call, 1, 1, name);
            return B(`(.setHas ${st(t)})`, S2([() => tr.lowerExpr(args[0], fc, t)]), [sty, t], ty_1.T.bool);
        case 'delete':
            argc(call, 1, 1, name);
            return B(`(.setDelete ${st(t)})`, S2([() => tr.lowerExpr(args[0], fc, t)]), [sty, t], ty_1.T.bool);
        case 'clear':
            argc(call, 0, 0, name);
            return B(`(.setClear ${st(t)})`, [s], [sty], ty_1.T.undef);
        case 'forEach': {
            argc(call, 1, 1, name);
            const ft = ty_1.T.fn([t, t, sty], ty_1.T.undef);
            return B(`(.setForEach ${st(t)})`, S2([() => tr.lowerCallback(args[0], fc, ft)]), [sty, ft], ty_1.T.undef);
        }
    }
    (0, diag_1.reject)(call, 'unsupported-builtin', `Set method ${name} is not supported here`);
}
function callbackRet(tr, arg, fc) {
    const t = tr.checker.getTypeAtLocation(arg);
    const sigs = t.getCallSignatures();
    if (sigs.length !== 1)
        return null;
    return tr.types.map(sigs[0].getReturnType(), fc.subst, arg);
}
function promiseMethod(tr, p, pt, name, call, fc, exp) {
    const args = call.arguments;
    const t = pt.t;
    const S2 = (thunks) => tr.seq([() => p, ...thunks], fc);
    switch (name) {
        case 'then': {
            argc(call, 1, 1, 'then (with a rejection handler)');
            const rr = tr.tyAt(call, fc);
            if (rr.k !== 'promise')
                (0, diag_1.reject)(call, 'unsupported-builtin', 'then result');
            const u = rr.t;
            const cr = callbackRet(tr, args[0], fc);
            if (cr && cr.k === 'promise') {
                const ft = ty_1.T.fn([t], ty_1.T.promise(u));
                return B(`(.promThenP ${st(t)} ${st(u)})`, S2([() => tr.lowerCallback(args[0], fc, ft)]), [pt, ft], ty_1.T.promise(u));
            }
            const ft = ty_1.T.fn([t], u);
            return B(`(.promThen ${st(t)} ${st(u)})`, S2([() => tr.lowerCallback(args[0], fc, ft)]), [pt, ft], ty_1.T.promise(u));
        }
        case 'catch': {
            argc(call, 1, 1, 'catch');
            const cr = callbackRet(tr, args[0], fc);
            if (cr && cr.k === 'promise')
                (0, diag_1.reject)(call, 'unsupported-builtin', 'catch handler returning a promise');
            if (cr && !(0, ty_1.tyEq)(cr, t) && !(t.k === 'undef' && cr.k === 'undef') && !tr.convert(ir_1.E.unreachable(cr), t, call, false, 0)) {
                (0, diag_1.reject)(call, 'catch-type', `catch handler returning ${(0, ty_1.prettyTy)(cr)} on a Promise<${(0, ty_1.prettyTy)(t)}> (the result type changes)`);
            }
            const ft = ty_1.T.fn([ty_1.T.err], t);
            return B(`(.promCatch ${st(t)})`, S2([() => tr.lowerCallback(args[0], fc, ft, true)]), [pt, ft], pt);
        }
        case 'finally': {
            argc(call, 1, 1, 'finally');
            const ft = ty_1.T.fn([], ty_1.T.undef);
            return B(`(.promFinally ${st(t)})`, S2([() => tr.lowerCallback(args[0], fc, ft)]), [pt, ft], pt);
        }
    }
    void exp;
    (0, diag_1.reject)(call, 'unsupported-builtin', `Promise method ${name} is not supported`);
}
function numberMethod(tr, n, name, call, fc) {
    const args = call.arguments;
    const S2 = (thunks) => tr.seq([() => n, ...thunks], fc);
    switch (name) {
        case 'toString':
            argc(call, 0, 1, name);
            if (!args.length)
                return Pr('.numToStr', [n], [ty_1.T.num], ty_1.T.str);
            return Pr('.numToStrRadix', S2([() => tr.lowerExpr(args[0], fc, ty_1.T.num)]), [ty_1.T.num, ty_1.T.num], ty_1.T.str);
        case 'toFixed':
            argc(call, 0, 1, name);
            return Pr('.toFixed', S2([() => args[0] ? tr.lowerExpr(args[0], fc, ty_1.T.num) : (0, core_1.numLit)(0)]), [ty_1.T.num, ty_1.T.num], ty_1.T.str);
        case 'toPrecision':
            argc(call, 0, 1, name);
            if (!args.length)
                return Pr('.numToStr', [n], [ty_1.T.num], ty_1.T.str);
            return Pr('.toPrecision', S2([() => tr.lowerExpr(args[0], fc, ty_1.T.num)]), [ty_1.T.num, ty_1.T.num], ty_1.T.str);
        case 'toExponential':
            argc(call, 0, 1, name);
            return Pr('.toExponential', S2([() => args[0] ? tr.lowerExpr(args[0], fc, ty_1.T.opt(ty_1.T.num)) : ir_1.E.none(ty_1.T.num)]), [ty_1.T.num, ty_1.T.opt(ty_1.T.num)], ty_1.T.str);
    }
    (0, diag_1.reject)(call, 'unsupported-builtin', `number method ${name} is not supported`);
}
function typedArrayMethod(tr, a, at, name, call, fc) {
    const args = call.arguments;
    const el = at.kind === 'bi64' || at.kind === 'bu64' ? ty_1.T.bigint : ty_1.T.num;
    const S2 = (thunks) => tr.seq([() => a, ...thunks], fc);
    if (name === 'fill') {
        argc(call, 1, 1, 'fill (with range)');
        return B(`(.taFill .${at.kind})`, S2([() => tr.lowerExpr(args[0], fc, el)]), [at, el], at);
    }
    if (name === 'slice') {
        argc(call, 0, 2, 'slice');
        return B(`(.taSlice .${at.kind})`, S2([() => args[0] ? tr.lowerExpr(args[0], fc, ty_1.T.num) : (0, core_1.numLit)(0), () => args[1] ? tr.lowerExpr(args[1], fc, ty_1.T.opt(ty_1.T.num)) : ir_1.E.none(ty_1.T.num)]), [at, ty_1.T.num, ty_1.T.opt(ty_1.T.num)], at);
    }
    (0, diag_1.reject)(call, 'unsupported-builtin', `typed array method ${name} is not supported`);
}
// ---------------------------------------------------------------------------------------
// new
P.lowerNew = function (n, fc, exp) {
    const callee = (0, stmts_1.skipParens)(n.expression);
    if (this.coverage) {
        const csym = ts.isIdentifier(callee) ? this.symAt(callee) : this.resolveSym(this.checker.getSymbolAtLocation(callee));
        const decls = csym?.declarations ?? [];
        if (csym && decls.some(d => this.isProjectDecl(d))) {
            this.lowerLoose(n, fc);
            return this.placeholderFor(n, fc, exp);
        }
    }
    {
        const csym = ts.isIdentifier(callee) ? this.symAt(callee) : this.resolveSym(this.checker.getSymbolAtLocation(callee));
        const decls = csym?.declarations ?? [];
        const cname = ts.isIdentifier(callee) ? callee.text : '';
        const project = !!csym && decls.some(d => this.isProjectDecl(d));
        if (!project && !(csym && MODELLED_FNS.has(cname) && isLib(this, csym))) {
            if (!csym || !decls.length)
                (0, diag_1.reject)(n, 'external-call', `constructs ${callee.getText()} (no TypeScript declaration)`);
            return this.lowerExternCall(n, fc, exp, `${this.externMemberName(csym, false).replace(/:([^:]*)$/, ':$1')}.new`, undefined);
        }
    }
    const viaNs = ts.isPropertyAccessExpression(callee) && this.isNamespaceRef(callee.expression);
    if (!ts.isIdentifier(callee) && !viaNs)
        (0, diag_1.reject)(n, 'unsupported', '`new` of a computed constructor');
    const sym = viaNs ? this.resolveSym(this.checker.getSymbolAtLocation(callee)) : this.symAt(callee);
    const args = n.arguments ?? ts.factory.createNodeArray();
    if (sym && isLib(this, sym)) {
        const name = ts.isIdentifier(callee) ? callee.text : callee.name.text;
        const rt = this.tyAt(n, fc);
        if (Object.hasOwn(ERR_KINDS, name)) {
            argc(n, 0, 1, `new ${name}`);
            const msg = args[0] ? this.lowerExpr(args[0], fc, ty_1.T.str) : (0, core_1.strLit)('');
            return Pr(`(.errNew .${ERR_KINDS[name]})`, [msg], [ty_1.T.str], ty_1.T.err);
        }
        if (name === 'Map') {
            if (rt.k !== 'map')
                (0, diag_1.reject)(n, 'unsupported-builtin', 'Map type');
            const ks = `${st(rt.key)} ${st(rt.val)}`;
            argc(n, 0, 1, 'new Map');
            if (!args.length)
                return B(`(.mapNew ${ks})`, [], [], rt);
            const et = ty_1.T.arr(ty_1.T.tup([rt.key, rt.val]));
            const src = this.unfoldE(this.lowerExpr(args[0], fc, this.unfoldTy(this.tyAt(args[0], fc)).k === 'map' ? undefined : et));
            const entries = src.ty.k === 'map' ? this.collectionSnapshot(src, 'entries', args[0]) : src;
            return B(`(.mapOfEntries ${ks})`, [this.coerce(entries, et, args[0])], [et], rt);
        }
        if (name === 'Set') {
            if (rt.k !== 'set')
                (0, diag_1.reject)(n, 'unsupported-builtin', 'Set type');
            argc(n, 0, 1, 'new Set');
            if (!args.length)
                return B(`(.setNew ${st(rt.t)})`, [], [], rt);
            const src = this.unfoldE(this.lowerExpr(args[0], fc, this.unfoldTy(this.tyAt(args[0], fc)).k === 'arr' ? ty_1.T.arr(rt.t) : undefined));
            const arr = src.ty.k === 'set' || src.ty.k === 'map' ? this.collectionSnapshot(src, src.ty.k === 'set' ? 'values' : 'keys', args[0]) : src;
            return B(`(.setOfArr ${st(rt.t)})`, [this.coerce(arr, ty_1.T.arr(rt.t), args[0])], [ty_1.T.arr(rt.t)], rt);
        }
        if (name === 'Promise') {
            if (rt.k !== 'promise')
                (0, diag_1.reject)(n, 'unsupported-builtin', 'Promise type');
            argc(n, 1, 1, 'new Promise');
            const t = rt.t;
            const exTy = ty_1.T.fn([ty_1.T.fn([t], ty_1.T.undef), ty_1.T.fn([ty_1.T.err], ty_1.T.undef)], ty_1.T.undef);
            return B(`(.promNew ${st(t)})`, [this.lowerCallback(args[0], fc, exTy, true)], [exTy], rt);
        }
        if (name === 'Array')
            (0, diag_1.reject)(n, 'unsupported-builtin', '`new Array(n)` creates holes; use `new Array(n).fill(x)` or Array.from');
        if (rt.k === 'tarr') {
            argc(n, 1, 1, `new ${name}`);
            const a0 = this.unfoldTy(this.tyAt(args[0], fc));
            const el = rt.kind === 'bi64' || rt.kind === 'bu64' ? ty_1.T.bigint : ty_1.T.num;
            if (a0.k === 'num')
                return B(`(.taNew .${rt.kind})`, [this.lowerExpr(args[0], fc, ty_1.T.num)], [ty_1.T.num], rt);
            return B(`(.taOfArr .${rt.kind})`, [this.lowerExpr(args[0], fc, ty_1.T.arr(el))], [ty_1.T.arr(el)], rt);
        }
        (0, diag_1.reject)(n, 'unsupported-builtin', `new ${name} is not supported`);
    }
    if (!sym || !(sym.flags & ts.SymbolFlags.Class))
        (0, diag_1.reject)(n, 'unsupported', '`new` of a non-class');
    const t = this.checker.getTypeAtLocation(n);
    const ci = this.types.classInst(t, fc.subst, n);
    const f = this.classCtor(ci, n);
    const ctor = ci.decl.members.find(ts.isConstructorDeclaration);
    const a = this.lowerCallArgs(ctor ? this.paramSpecs(ctor, ci.subst) : [], args, fc, n, []);
    return ir_1.E.call(f, a);
};
// ---------------------------------------------------------------------------------------
// helpers written directly in IR
P.splitHelper = function () {
    const known = this.helpers.get('split');
    if (known)
        return known;
    const s = (0, ir_1.mkVar)('s', ty_1.T.str), sep = (0, ir_1.mkVar)('sep', ty_1.T.str);
    const f = this.newFun('String.prototype.split', 'strSplit', [s, sep], ty_1.T.arr(ty_1.T.str), false);
    this.funDocs.set(f, 'split(s: string, sep: string): string[]  (String.prototype.split with a string separator)');
    this.helpers.set('split', f);
    const AS = ty_1.T.arr(ty_1.T.str);
    const out = (0, ir_1.mkVar)('out', AS);
    const push = (x) => (0, ir_1.stmtItem)(ir_1.S.expr(B('(.arrPush .str)', [ir_1.E.var(out), x], [AS, ty_1.T.str], ty_1.T.num)));
    const len = (x) => Pr('.strLength', [x], [ty_1.T.str], ty_1.T.num);
    const i = (0, ir_1.mkVar)('i', ty_1.T.num, true);
    const start = (0, ir_1.mkVar)('start', ty_1.T.num, true);
    const j = (0, ir_1.mkVar)('j', ty_1.T.num);
    const units = [
        (0, ir_1.declItem)(i, (0, core_1.numLit)(0)),
        (0, ir_1.stmtItem)({ k: 'forLoop', c: Pr('(.numCmp .lt)', [ir_1.E.var(i), len(ir_1.E.var(s))], [ty_1.T.num, ty_1.T.num], ty_1.T.bool),
            body: [push(Pr('.charAt', [ir_1.E.var(s), ir_1.E.var(i)], [ty_1.T.str, ty_1.T.num], ty_1.T.str))],
            step: [(0, ir_1.stmtItem)(ir_1.S.assign(i, Pr('(.numBin .add)', [ir_1.E.var(i), (0, core_1.numLit)(1)], [ty_1.T.num, ty_1.T.num], ty_1.T.num)))] }),
        (0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.var(out))),
    ];
    const loopBody = [
        (0, ir_1.declItem)(j, Pr('.indexOf', [ir_1.E.var(s), ir_1.E.var(sep), ir_1.E.var(start)], [ty_1.T.str, ty_1.T.str, ty_1.T.num], ty_1.T.num)),
        (0, ir_1.stmtItem)(ir_1.S.ite(Pr('(.numCmp .lt)', [ir_1.E.var(j), (0, core_1.numLit)(0)], [ty_1.T.num, ty_1.T.num], ty_1.T.bool), [push(Pr('.substring', [ir_1.E.var(s), ir_1.E.var(start), ir_1.E.none(ty_1.T.num)], [ty_1.T.str, ty_1.T.num, ty_1.T.opt(ty_1.T.num)], ty_1.T.str)), (0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.var(out)))], [])),
        push(Pr('.substring', [ir_1.E.var(s), ir_1.E.var(start), ir_1.E.some(ir_1.E.var(j))], [ty_1.T.str, ty_1.T.num, ty_1.T.opt(ty_1.T.num)], ty_1.T.str)),
        (0, ir_1.stmtItem)(ir_1.S.assign(start, Pr('(.numBin .add)', [ir_1.E.var(j), len(ir_1.E.var(sep))], [ty_1.T.num, ty_1.T.num], ty_1.T.num))),
    ];
    f.body = [
        (0, ir_1.declItem)(out, B('(.arrOf .str 0)', [], [], AS)),
        (0, ir_1.stmtItem)(ir_1.S.ite(ir_1.E.seq(ir_1.E.var(sep), (0, core_1.strLit)('')), [(0, ir_1.stmtItem)({ k: 'block', b: units })], [])),
        (0, ir_1.declItem)(start, (0, core_1.numLit)(0)),
        (0, ir_1.stmtItem)({ k: 'while', c: ir_1.E.bool(true), body: loopBody }),
        (0, ir_1.stmtItem)(ir_1.S.ret(ir_1.E.var(out))),
    ];
    return f;
};
void ir_1.InternalError;
void ty_1.tyEq;

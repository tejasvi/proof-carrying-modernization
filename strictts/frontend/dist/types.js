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
exports.TypeMapper = exports.NEVER = void 0;
exports.substKey = substKey;
exports.typeId = typeId;
exports.isLibDecl = isLibDecl;
// TypeScript checker types -> StrictTS types.
const ts = __importStar(require("typescript"));
const ty_1 = require("./ty");
const diag_1 = require("./diag");
function substKey(s) {
    return [...s.entries()].map(([k, v]) => `${k.id}=${(0, ty_1.tyKey)(v)}`).join(',');
}
const TYPED_ARRAYS = {
    Int8Array: 'i8', Uint8Array: 'u8', Uint8ClampedArray: 'u8c', Int16Array: 'i16', Uint16Array: 'u16',
    Int32Array: 'i32', Uint32Array: 'u32', Float32Array: 'f32', Float64Array: 'f64',
    BigInt64Array: 'bi64', BigUint64Array: 'bu64',
};
const ERROR_TYPES = new Set(['Error', 'TypeError', 'RangeError', 'SyntaxError', 'ReferenceError', 'EvalError', 'URIError']);
/** The type of values that cannot exist (dropped from unions). */
exports.NEVER = { k: 'undef' };
function typeId(t) { return t.id ?? -1; }
function isLibDecl(program, d) {
    if (!d)
        return false;
    const sf = d.getSourceFile();
    return program.isSourceFileDefaultLibrary(sf) || sf.isDeclarationFile;
}
class TypeMapper {
    checker;
    program;
    analysis;
    /** the original subset (`--strict`): `unknown` and `any` are rejected, there is no `dyn` */
    strict = false;
    /** function types whose values are compared by identity somewhere in the program (keys of
     * `stripIdBoxes`): their values are `box (fn …)` cells (identity.ts) */
    boxedFns = new Set();
    /** record types whose values are compared by identity (keys of `stripIdBoxes`): their values
     * are `box (record …)` cells (identity.ts) */
    boxedRecs = new Set();
    /** coverage mode: called with the name of an external object type that has no IR type */
    onExternalType = () => { };
    aliases = new Map();
    /** emitted `TT.fields` (classes and mutable structures), in creation order */
    classFields = new Map();
    classes = new Map();
    mutStructs = [];
    memo = new Map();
    recursive = new Set();
    recursionScanned = new Set();
    namedNames = new Map(); // type key (id+subst) -> alias name
    usedNames = new Set();
    aliasInProgress = new Set();
    /** TypeScript names of record types (for readable names of generic instances) */
    recordNames = new Map();
    /** A short identifier-friendly name of a type (generic instance names). */
    shortName(t) {
        switch (t.k) {
            case 'num': return 'number';
            case 'str': return 'string';
            case 'bigint':
            case 'bool':
            case 'undef':
            case 'null':
            case 'err': return t.k;
            case 'arr': return `${this.shortName(t.t)}Arr`;
            case 'set': return `Set_${this.shortName(t.t)}`;
            case 'map': return `Map_${this.shortName(t.key)}_${this.shortName(t.val)}`;
            case 'dict': return `Dict_${this.shortName(t.t)}`;
            case 'opt': return `opt_${this.shortName(t.t)}`;
            case 'promise': return `Promise_${this.shortName(t.t)}`;
            case 'obj': return t.c.replace(/[^A-Za-z0-9_]/g, '_');
            case 'named': return t.n.replace(/[^A-Za-z0-9_]/g, '_');
            case 'record': return this.recordNames.get((0, ty_1.tyKey)(t)) ?? `rec${t.fs.length}`;
            case 'tup': return `tup${t.ts.length}`;
            case 'union': return `union${t.ts.length}`;
            case 'enum': return `enum${t.cases.length}`;
            case 'fn': return `fn${t.args.length}`;
            default: return t.k;
        }
    }
    constructor(checker, program, analysis) {
        this.checker = checker;
        this.program = program;
        this.analysis = analysis;
    }
    // -------------------------------------------------------------------------------------
    // Recursion detection over the structural type graph (immutable object types and unions
    // on a cycle become `named`).
    edges(t) {
        const out = [];
        if (t.isUnion() || t.isIntersection())
            return [...t.types];
        if (!(t.flags & ts.TypeFlags.Object))
            return out;
        // package and host types are not traversed (they have no IR type; e.g. React, DOM)
        const sym = t.getSymbol() ?? t.aliasSymbol;
        if (sym && sym.name && !sym.name.startsWith('__') && this.isExternalDecl(sym.declarations?.[0]) && !this.knownLib(sym.name))
            return out;
        if (this.isClassInstance(t) || this.isMutableStructure(t))
            return out;
        const obj = t;
        if (obj.objectFlags & ts.ObjectFlags.Reference) {
            const args = this.checker.getTypeArguments(t);
            const sym = t.getSymbol();
            if (this.checker.isArrayType(t) || this.checker.isTupleType(t) ||
                (sym && ['Map', 'ReadonlyMap', 'Set', 'ReadonlySet', 'Promise'].includes(sym.name) && isLibDecl(this.program, sym.declarations?.[0]))) {
                return [...args];
            }
        }
        for (const sig of t.getCallSignatures()) {
            for (const p of sig.getParameters())
                out.push(this.checker.getTypeOfSymbol(p));
            out.push(sig.getReturnType());
        }
        for (const p of this.checker.getPropertiesOfType(t))
            out.push(this.checker.getTypeOfSymbol(p));
        return out;
    }
    scanRecursion(root) {
        if (this.recursionScanned.has(typeId(root)))
            return;
        const stack = [];
        const onStack = new Set();
        const visit = (t, depth) => {
            const id = typeId(t);
            if (onStack.has(id)) {
                for (let i = stack.length - 1; i >= 0; i--) {
                    this.recursive.add(typeId(stack[i]));
                    if (typeId(stack[i]) === id)
                        break;
                }
                return;
            }
            if (this.recursionScanned.has(id) || depth > 200)
                return;
            stack.push(t);
            onStack.add(id);
            for (const e of this.edges(t))
                visit(e, depth + 1);
            stack.pop();
            onStack.delete(id);
            this.recursionScanned.add(id);
        };
        visit(root, 0);
    }
    isRecursive(t) {
        this.scanRecursion(t);
        return this.recursive.has(typeId(t));
    }
    // -------------------------------------------------------------------------------------
    /** Declared in a package or in the host library (not the program's own code)? */
    isExternalDecl(d) {
        if (!d)
            return false;
        const sf = d.getSourceFile();
        return sf.fileName.includes('/node_modules/') || this.program.isSourceFileDefaultLibrary(sf);
    }
    /** The name of an external type: `<package>:<TypeName>`, or the qualified name for host
     * types (`Date`, `NodeJS.Timeout`, `React.JSX.Element`). Type arguments are erased. */
    externalTypeName(sym) {
        const d = sym.declarations?.[0];
        const pkg = d?.getSourceFile().fileName.match(/node_modules\/((?:@[^/]+\/)?[^/]+)\//)?.[1];
        if (pkg && !pkg.startsWith('@types/') && pkg !== 'typescript')
            return `${pkg}:${sym.name}`;
        return this.externalSymName(sym);
    }
    /** `package:Qualified.Name` (or `Qualified.Name` for the host library and @types). */
    externalSymName(sym) {
        const d = sym.declarations?.[0];
        // `"/abs/path/module".name` -> name;  `"node:fs/promises".mkdir` -> node:fs/promises.mkdir
        let q = this.checker.getFullyQualifiedName(sym);
        const whole = q.match(/^"([^"]*)"$/);
        if (whole) {
            // a module itself: `firebase-functions/lib/logger/index` -> firebase-functions/logger
            const m = whole[1].match(/node_modules\/(.*)$/);
            const p = m ? m[1].replace(/\/(lib|dist|build|cjs|esm)\//g, '/').replace(/\/index$/, '').replace(/\.d\.ts$/, '') : whole[1];
            return p.replace(/^@types\//, '');
        }
        q = q.replace(/"(\/[^"]*)"\./g, '').replace(/"([^"]*)"\./g, '$1.').replace(/^global\./, '');
        const pkg = d?.getSourceFile().fileName.match(/node_modules\/((?:@[^/]+\/)?[^/]+)\//)?.[1];
        if (!pkg || pkg === 'typescript')
            q = q.replace(/^(\w+)Constructor\./, '$1.');
        return pkg && !pkg.startsWith('@types/') && pkg !== 'typescript' ? `${pkg}:${q}` : q;
    }
    /** Library object types the IR models (others are host types such as Response). */
    knownLib(name) {
        // (the results of Promise.allSettled are plain records: Ty.settled)
        return ['Array', 'ReadonlyArray', 'Map', 'ReadonlyMap', 'Set', 'ReadonlySet', 'Promise', 'PromiseLike', 'Error', 'TypeError',
            'RangeError', 'SyntaxError', 'ReferenceError', 'EvalError', 'URIError', 'String', 'Number', 'Boolean', 'BigInt',
            'PromiseFulfilledResult', 'PromiseRejectedResult'].includes(name) || Object.hasOwn(TYPED_ARRAYS, name);
    }
    isClassInstance(t) {
        const sym = t.getSymbol();
        return !!sym && !!(sym.flags & ts.SymbolFlags.Class) && !isLibDecl(this.program, sym.declarations?.[0]);
    }
    /** Is `t` an object type whose fields are assigned somewhere (directly, or through a
     * structurally identical type)? */
    /** A dictionary type with named properties (`{ v: number; [k: string]: unknown }`): its
     * values are not copied into records (later writes through the dictionary would not show). */
    isNamedDict(t) {
        const parts = t.isUnion() ? t.types : [t];
        return parts.some(p => !!(p.flags & ts.TypeFlags.Object) && this.checker.getIndexInfosOfType(p).length > 0 &&
            this.checker.getPropertiesOfType(p).length > 0);
    }
    isMutableStructure(t) {
        if (!(t.flags & ts.TypeFlags.Object) || this.isClassInstance(t))
            return false;
        if (this.analysis.isMutatedId(t))
            return true;
        for (const m of this.analysis.mutatedTypes)
            if (this.sameStructure(m, t))
                return true;
        return false;
    }
    sameStructure(a, b) {
        const pa = this.checker.getPropertiesOfType(a).map(p => p.name).sort();
        const pb = this.checker.getPropertiesOfType(b).map(p => p.name).sort();
        if (pa.join('\0') !== pb.join('\0'))
            return false;
        return this.checker.isTypeAssignableTo(a, b) && this.checker.isTypeAssignableTo(b, a);
    }
    freshName(base) {
        let n = base, i = 2;
        while (this.usedNames.has(n))
            n = `${base}${i++}`;
        this.usedNames.add(n);
        return n;
    }
    typeArgsSuffix(args, subst, site) {
        if (!args.length)
            return '';
        return `<${args.map(a => (0, ty_1.prettyTy)(this.map(a, subst, site))).join(', ')}>`;
    }
    /** Display name of a named object/union type. */
    nameOf(t, subst, site) {
        const key = `${typeId(t)}|${substKey(subst)}`;
        const known = this.namedNames.get(key);
        if (known)
            return known;
        let base = 'Anon';
        let args = [];
        if (t.aliasSymbol) {
            base = t.aliasSymbol.name;
            args = t.aliasTypeArguments ?? [];
        }
        else {
            const sym = t.getSymbol();
            if (sym && sym.name && !sym.name.startsWith('__'))
                base = sym.name;
            if (t.objectFlags & ts.ObjectFlags.Reference)
                args = this.checker.getTypeArguments(t);
        }
        const n = this.freshName(base + this.typeArgsSuffix(args, subst, site));
        this.namedNames.set(key, n);
        return n;
    }
    depth = 0;
    map(t, subst, site) {
        const key = `${typeId(t)}|${substKey(subst)}`;
        const m = this.memo.get(key);
        if (m)
            return m;
        if (this.depth > 60)
            (0, diag_1.reject)(site, 'unsupported-type', `type ${this.checker.typeToString(t).slice(0, 80)} is too deeply nested (an unnamed recursive type?)`);
        this.depth++;
        try {
            const r = this.map1(t, subst, site);
            this.memo.set(key, r);
            return r;
        }
        finally {
            this.depth--;
        }
    }
    map1(t, subst, site) {
        const F = ts.TypeFlags;
        // `unknown` / `any`: a value with its runtime type (StrictTS/Lib/Dyn.lean), except in the
        // original subset (`--strict`; STRICTTS_ANY_REJECT=1 rejects only `any`, for measurements)
        if (t.flags & (F.Any | F.Unknown) && this.strict)
            (0, diag_1.reject)(site, 'any-type', `a value of type ${t.flags & F.Any ? 'any' : 'unknown'} (any/unknown are not allowed)`);
        if (t.flags & F.Unknown)
            return ty_1.T.dyn;
        if (t.flags & F.Any) {
            if (process.env.STRICTTS_ANY_REJECT)
                (0, diag_1.reject)(site, 'any-type', 'a value of type any (any is not allowed)');
            return ty_1.T.dyn;
        }
        if (t.flags & F.TypeParameter) {
            const s = subst.get(t);
            if (!s)
                (0, diag_1.reject)(site, 'unsupported-generic', `type parameter ${this.checker.typeToString(t)} is not instantiated here`);
            return s;
        }
        if (t.flags & (F.EnumLiteral | F.Enum))
            (0, diag_1.reject)(site, 'no-enum-decl', 'TypeScript `enum` declarations are not supported');
        if (t.flags & (F.Number | F.NumberLiteral))
            return ty_1.T.num;
        if (t.flags & (F.BigInt | F.BigIntLiteral))
            return ty_1.T.bigint;
        if (t.flags & (F.Boolean | F.BooleanLiteral))
            return ty_1.T.bool;
        if (t.flags & (F.String | F.StringLiteral | F.TemplateLiteral | F.StringMapping))
            return ty_1.T.str;
        if (t.flags & (F.Undefined | F.Void))
            return ty_1.T.undef;
        if (t.flags & F.Null)
            return ty_1.T.null;
        if (t.flags & F.Never)
            return ty_1.T.undef;
        if (t.flags & (F.ESSymbol | F.UniqueESSymbol))
            (0, diag_1.reject)(site, 'no-symbol', '`symbol` is not supported');
        // `object`: any non-primitive value, kept with its runtime type (not in the strict subset)
        if (t.flags & F.NonPrimitive) {
            if (this.strict)
                (0, diag_1.reject)(site, 'no-object-type', 'the `object` type is not allowed');
            return ty_1.T.dyn;
        }
        if ((t.flags & F.Conditional) && t.aliasSymbol?.name === 'Awaited' && t.aliasTypeArguments?.length === 1) {
            // Awaited<T> of a type parameter: the substitution decides
            const inner = this.map(t.aliasTypeArguments[0], subst, site);
            return inner.k === 'promise' ? inner.t : inner;
        }
        if (t.isUnion())
            return this.mapUnion(t, subst, site);
        if (t.isIntersection()) {
            if (t.types.every(x => x.flags & F.Object))
                return this.mapObjectType(t, subst, site);
            return this.mapIntersection(t, subst, site);
        }
        if (t.flags & F.Object)
            return this.mapObject(t, subst, site);
        (0, diag_1.reject)(site, 'unsupported-type', `type ${this.checker.typeToString(t)} is not supported`);
    }
    /** `T & {}` (T without undefined/null) and `T & null` (null or nothing), as produced by
     * TypeScript's narrowing of type parameters. */
    mapIntersection(t, subst, site) {
        const F = ts.TypeFlags;
        const isEmptyObj = (x) => !!(x.flags & F.Object) && this.checker.getPropertiesOfType(x).length === 0 &&
            x.getCallSignatures().length === 0 && this.checker.getIndexInfosOfType(x).length === 0;
        const core = t.types.filter(x => !isEmptyObj(x) && !(x.flags & (F.Null | F.Undefined)));
        if (core.length !== 1)
            (0, diag_1.reject)(site, 'unsupported-type', `intersection type ${this.checker.typeToString(t)} is not supported`);
        let c = this.map(core[0], subst, site);
        if (t.types.some(isEmptyObj)) {
            if (c.k === 'opt')
                c = c.t;
            if (c.k === 'union') {
                const r = c.ts.filter(m => m.k !== 'null');
                c = r.length === 1 ? r[0] : ty_1.T.union(r);
            }
            if (c.k === 'undef' || c.k === 'null')
                return exports.NEVER;
        }
        if (t.types.some(x => x.flags & F.Null)) {
            const hasNull = c.k === 'null' || (c.k === 'union' && c.ts.some(m => m.k === 'null')) || (c.k === 'opt' && (c.t.k === 'null' || (c.t.k === 'union' && c.t.ts.some(m => m.k === 'null'))));
            return hasNull ? ty_1.T.null : exports.NEVER;
        }
        if (t.types.some(x => x.flags & F.Undefined))
            return c.k === 'opt' || c.k === 'undef' ? ty_1.T.undef : exports.NEVER;
        return c;
    }
    mapUnion(t, subst, site) {
        const F = ts.TypeFlags;
        // a recursive union alias is named before its members are mapped
        let recName;
        if (t.aliasSymbol && this.isRecursive(t)) {
            recName = this.nameOf(t, subst, site);
            const undefPart = t.types.some(m => m.flags & (F.Undefined | F.Void));
            if (this.aliasInProgress.has(recName))
                return undefPart ? ty_1.T.opt(ty_1.T.named(recName)) : ty_1.T.named(recName);
            this.aliasInProgress.add(recName);
            this.memo.set(`${typeId(t)}|${substKey(subst)}`, undefPart ? ty_1.T.opt(ty_1.T.named(recName)) : ty_1.T.named(recName));
        }
        try {
            return this.mapUnion1(t, subst, site, recName);
        }
        finally {
            if (recName)
                this.aliasInProgress.delete(recName);
        }
    }
    mapUnion1(t, subst, site, recName) {
        const F = ts.TypeFlags;
        let hasUndef = false, hasNull = false;
        const lits = [];
        const rest = [];
        for (const m of t.types) {
            if (m.flags & (F.Undefined | F.Void))
                hasUndef = true;
            else if (m.flags & F.Null)
                hasNull = true;
            else if (m.flags & F.StringLiteral)
                lits.push(m.value);
            else
                rest.push(m);
        }
        const members = [];
        if (lits.length === 1)
            members.push(ty_1.T.str);
        else if (lits.length > 1)
            members.push(ty_1.T.enum([...new Set(lits)].sort()));
        for (const m of rest) {
            const mt = this.map(m, subst, site);
            if (mt === exports.NEVER)
                continue;
            // members that are themselves optional/nullable (from narrowed type parameters)
            if (mt.k === 'opt') {
                hasUndef = true;
                members.push(mt.t);
                continue;
            }
            if (mt.k === 'undef') {
                hasUndef = true;
                continue;
            }
            if (mt.k === 'null') {
                hasNull = true;
                continue;
            }
            members.push(mt);
        }
        let ms = (0, ty_1.sortTys)(members);
        // `string | "a"`-like collapses
        if (ms.some(x => x.k === 'str'))
            ms = ms.filter(x => x.k !== 'enum');
        if (hasNull)
            ms = (0, ty_1.sortTys)([...ms, ty_1.T.null]);
        let core;
        if (ms.length === 0)
            core = ty_1.T.undef;
        else if (ms.length === 1)
            core = ms[0];
        else
            core = ty_1.T.union(ms);
        if (recName) {
            if (core.k === 'undef')
                (0, diag_1.reject)(site, 'unsupported-type', 'recursive alias of undefined');
            this.aliases.set(recName, core);
            core = ty_1.T.named(recName);
        }
        if (hasUndef)
            return ms.length === 0 ? ty_1.T.undef : ty_1.T.opt(core);
        return core;
    }
    namedFor(t, structure, subst, site) {
        const n = this.nameOf(t, subst, site);
        this.aliases.set(n, structure);
        return ty_1.T.named(n);
    }
    mapObject(t, subst, site) {
        const sym = t.getSymbol();
        const lib = sym && isLibDecl(this.program, sym.declarations?.[0]);
        if (t.objectFlags & ts.ObjectFlags.Reference) {
            const ref = t;
            const args = this.checker.getTypeArguments(ref);
            if (this.checker.isArrayType(t))
                return ty_1.T.arr(this.map(args[0], subst, site));
            if (this.checker.isTupleType(t)) {
                const target = ref.target;
                if (target.elementFlags.some(f => !(f & ts.ElementFlags.Required)))
                    (0, diag_1.reject)(site, 'unsupported-type', 'tuples with optional or rest elements are not supported');
                return ty_1.T.tup(args.slice(0, target.fixedLength).map(a => this.map(a, subst, site)));
            }
            if (sym && lib) {
                switch (sym.name) {
                    case 'Map':
                    case 'ReadonlyMap': {
                        const k = this.map(args[0], subst, site), v = this.map(args[1], subst, site);
                        if (!(0, ty_1.eqable)(k))
                            (0, diag_1.reject)(site, 'map-key', `Map keys of type ${(0, ty_1.prettyTy)(k)} are not comparable with SameValueZero`);
                        return ty_1.T.map(k, v);
                    }
                    case 'Set':
                    case 'ReadonlySet': {
                        const e = this.map(args[0], subst, site);
                        if (!(0, ty_1.eqable)(e))
                            (0, diag_1.reject)(site, 'map-key', `Set elements of type ${(0, ty_1.prettyTy)(e)} are not comparable with SameValueZero`);
                        return ty_1.T.set(e);
                    }
                    case 'Promise': return ty_1.T.promise(this.map(args[0], subst, site));
                }
            }
        }
        if (sym && lib) {
            if (ERROR_TYPES.has(sym.name))
                return ty_1.T.err;
            if (Object.hasOwn(TYPED_ARRAYS, sym.name))
                return ty_1.T.tarr(TYPED_ARRAYS[sym.name]);
            if (sym.name === 'RegExpMatchArray' || sym.name === 'RegExpExecArray')
                return ty_1.T.ext(sym.name);
            if (sym.name === 'RegExp')
                return ty_1.REGEXP_TY;
            if (sym.name === 'Function' || sym.name === 'Object')
                (0, diag_1.reject)(site, 'no-object-type', `the type ${sym.name} is not allowed`);
            if (sym.name === 'Symbol')
                (0, diag_1.reject)(site, 'no-symbol', '`symbol` is not supported');
            // `Iterator<T, TReturn, TNext>`: the record of its methods, `next` (called without the
            // TNext argument), `return?` and `throw?` (called without the error), returning the union
            // of the yield and return results; the methods are closures (`this` in an object literal
            // method is rejected, so calls through the fields need no receiver). IteratorObject (the
            // Iterator.prototype helpers), iterable iterators (Symbol.iterator), Map / Set / Array
            // iterators and generators stay unsupported.
            if (sym.name === 'Iterator' || sym.name === 'IteratorYieldResult' || sym.name === 'IteratorReturnResult') {
                const args = (t.flags & ts.TypeFlags.Object) ? this.checker.getTypeArguments(t) : [];
                if (sym.name === 'IteratorYieldResult')
                    return ty_1.T.record([{ name: 'done', ty: ty_1.T.opt(ty_1.T.bool) }, { name: 'value', ty: this.map(args[0], subst, site) }]);
                if (sym.name === 'IteratorReturnResult')
                    return ty_1.T.record([{ name: 'done', ty: ty_1.T.bool }, { name: 'value', ty: this.iterReturnValue(args[0], subst, site) }]);
                const res = ty_1.T.union((0, ty_1.sortTys)([
                    ty_1.T.record([{ name: 'done', ty: ty_1.T.opt(ty_1.T.bool) }, { name: 'value', ty: this.map(args[0], subst, site) }]),
                    ty_1.T.record([{ name: 'done', ty: ty_1.T.bool }, { name: 'value', ty: this.iterReturnValue(args[1], subst, site) }]),
                ]));
                return ty_1.T.record([
                    { name: 'next', ty: ty_1.T.fn([], res) },
                    { name: 'return', ty: ty_1.T.opt(ty_1.T.fn([ty_1.T.opt(this.iterReturnValue(args[1], subst, site))], res)) },
                    { name: 'throw', ty: ty_1.T.opt(ty_1.T.fn([ty_1.T.opt(ty_1.T.undef)], res)) },
                ]);
            }
            if (['IterableIterator', 'MapIterator', 'SetIterator', 'ArrayIterator', 'Generator', 'AsyncGenerator', 'AsyncIterableIterator'].includes(sym.name)) {
                (0, diag_1.reject)(site, 'unsupported-type', `type ${sym.name} is not supported (iterators)`);
            }
        }
        // Node's timer handle (also when a program declares the type itself): TIMER_TY
        if (sym && (sym.name === 'Timeout' || sym.name === 'Timer') && /^(global\.)?NodeJS\.(Timeout|Timer)$/.test(this.checker.getFullyQualifiedName(sym)))
            return ty_1.TIMER_TY;
        // a named object type of a package (firebase, express, react, ...) or of the host
        // (DOM, Node): no IR representation
        // (aliases of the default library — Record, Partial, Pick, ... — are type operators that
        // TypeScript resolves to structural types; only package aliases are external API types)
        const asym = !sym || sym.name.startsWith('__') ? t.aliasSymbol : undefined;
        const asymDecl = asym?.declarations?.[0];
        // (plain function types declared outside — `typeof Date.now`, React.Dispatch — stay
        // function types)
        const plainFn = t.getCallSignatures().length === 1 && this.checker.getPropertiesOfType(t).length === 0;
        // an external object type that is only a string index signature (Firestore's
        // `DocumentData`): a plain object used as a dictionary, like `Record<string, …>`
        const infos0 = this.checker.getIndexInfosOfType(t);
        if (infos0.length === 1 && (infos0[0].keyType.flags & ts.TypeFlags.String) && this.checker.getPropertiesOfType(t).length === 0 &&
            t.getCallSignatures().length === 0 && t.getConstructSignatures().length === 0) {
            return ty_1.T.dict(this.map(infos0[0].type, subst, site));
        }
        const extSym = plainFn ? undefined
            : asym && asymDecl && this.isExternalDecl(asymDecl) && !this.program.isSourceFileDefaultLibrary(asymDecl.getSourceFile()) && !this.knownLib(asym.name) ? asym
                : sym && sym.name && !sym.name.startsWith('__') && this.isExternalDecl(sym.declarations?.[0]) && !this.knownLib(sym.name) ? sym : undefined;
        if (extSym) {
            const name = this.externalTypeName(extSym);
            // (STRICTTS_NO_EXT_TYPES=1: the earlier behaviour, for coverage comparisons)
            if (process.env.STRICTTS_NO_EXT_TYPES)
                (0, diag_1.reject)(site, 'external-type', `values of the external type ${name} have no StrictTS representation`, name);
            return ty_1.T.ext(name);
        }
        if (this.isClassInstance(t))
            return ty_1.T.obj(this.classInst(t, subst, site).name);
        // function types
        const calls = t.getCallSignatures();
        const props = this.checker.getPropertiesOfType(t);
        if (calls.length > 0) {
            if (props.length > 0 || calls.length > 1)
                (0, diag_1.reject)(site, 'unsupported-type', `type ${this.checker.typeToString(t)} (overloaded or with properties) is not supported`);
            return this.mapSignature(calls[0], subst, site);
        }
        if (t.getConstructSignatures().length)
            (0, diag_1.reject)(site, 'unsupported-type', 'constructor types are not supported');
        return this.mapObjectType(t, subst, site);
    }
    /** The value of an iterator's return result (TReturn): in the strict subset the default `any`
     * is undefined, which no program can observe there (reads at type any are rejected). */
    iterReturnValue(x, subst, site) {
        return !x || (this.strict && (x.flags & ts.TypeFlags.Any)) ? ty_1.T.undef : this.map(x, subst, site);
    }
    mapSignature(sig, subst, site) {
        // a method of `Iterator<…>` read as a value (`it.return`): the type of the record's field
        const d = sig.getDeclaration();
        if (d && d.parent && ts.isInterfaceDeclaration(d.parent) && d.parent.name.text === 'Iterator' && isLibDecl(this.program, d.parent)) {
            const res = this.map(sig.getReturnType(), subst, site);
            const name = d.name && ts.isIdentifier(d.name) ? d.name.text : '';
            if (name === 'next')
                return ty_1.T.fn([], res);
            if (name === 'throw')
                return ty_1.T.fn([ty_1.T.opt(ty_1.T.undef)], res);
            if (name === 'return') {
                const p = sig.getParameters()[0];
                return ty_1.T.fn([ty_1.T.opt(this.iterReturnValue(p ? this.checker.getTypeOfSymbol(p).getNonNullableType() : undefined, subst, site))], res);
            }
        }
        if (sig.typeParameters?.length)
            (0, diag_1.reject)(site, 'unsupported-generic', 'generic function values are not supported (only generic functions that are called directly)');
        const args = [];
        for (const p of sig.getParameters()) {
            const d = p.valueDeclaration;
            if (d && d.dotDotDotToken)
                (0, diag_1.reject)(site, 'fn-type-rest', 'rest parameters in function types are not supported');
            if (d && ts.isIdentifier(d.name) && d.name.text === 'this')
                continue;
            let pt = this.map(this.checker.getTypeOfSymbol(p), subst, site);
            if (d && (d.questionToken || d.initializer) && pt.k !== 'opt')
                pt = ty_1.T.opt(pt);
            args.push(pt);
        }
        const f = ty_1.T.fn(args, this.map(sig.getReturnType(), subst, site));
        return this.boxedFns.size && this.boxedFns.has((0, ty_1.tyKey)((0, ty_1.stripIdBoxes)(f))) ? ty_1.T.box(f) : f;
    }
    /** Records, mutable structures and named recursive object types. */
    mapObjectType(t, subst, site) {
        const infos = this.checker.getIndexInfosOfType(t);
        if (infos.length) {
            // an object used as a dictionary: one string index signature, alone or with named
            // properties whose types fit it (TypeScript checks that for interfaces and object literal
            // types, not for intersections); a named property is read as a dictionary entry at the
            // type TypeScript gives it (a checked cast where that is narrower than the index type)
            if (infos.length === 1 && (infos[0].keyType.flags & ts.TypeFlags.String) &&
                this.checker.getPropertiesOfType(t).every(p => this.checker.isTypeAssignableTo(this.checker.getTypeOfSymbol(p), infos[0].type))) {
                return ty_1.T.dict(this.map(infos[0].type, subst, site));
            }
            (0, diag_1.reject)(site, 'index-signature', `index signatures (${this.checker.typeToString(t)}) are only supported with string keys and named properties of the index type (dictionaries)`);
        }
        if (this.isMutableStructure(t))
            return ty_1.T.obj(this.mutStruct(t, subst, site).name);
        const props = this.checker.getPropertiesOfType(t);
        if (props.length === 0) {
            // `{}` without call signatures: the record without fields (an object literal `{}`; a value
            // given at this type is seen through no properties); not in the strict subset
            if (this.strict || t.getCallSignatures().length || t.getConstructSignatures().length)
                (0, diag_1.reject)(site, 'no-object-type', `the empty object type ${this.checker.typeToString(t)} is not allowed`);
            return ty_1.T.record([]);
        }
        // only types with a name (alias or interface) become `named`: every recursive cycle of
        // TypeScript types passes through a named type, so anonymous members expand finitely
        const sym = t.getSymbol();
        const hasName = !!t.aliasSymbol || (!!sym && !!sym.name && !sym.name.startsWith('__'));
        const rec = hasName && this.isRecursive(t);
        let name;
        if (rec) {
            name = this.nameOf(t, subst, site);
            if (this.aliasInProgress.has(name))
                return ty_1.T.named(name);
            this.aliasInProgress.add(name);
            this.memo.set(`${typeId(t)}|${substKey(subst)}`, ty_1.T.named(name));
        }
        const fs = [];
        for (const p of props) {
            if (p.flags & (ts.SymbolFlags.GetAccessor | ts.SymbolFlags.SetAccessor))
                (0, diag_1.reject)(site, 'unsupported-type', `accessor ${p.name} in object type`);
            let ft = this.map(this.checker.getTypeOfSymbol(p), subst, site);
            if ((p.flags & ts.SymbolFlags.Optional) && ft.k !== 'opt')
                ft = ty_1.T.opt(ft);
            fs.push({ name: p.name, ty: ft });
        }
        const r = ty_1.T.record((0, ty_1.sortFields)(fs));
        const disp = t.aliasSymbol?.name ?? (sym && sym.name && !sym.name.startsWith('__') ? sym.name : undefined);
        if (disp && !this.recordNames.has((0, ty_1.tyKey)(r)))
            this.recordNames.set((0, ty_1.tyKey)(r), disp);
        if (name) {
            this.aliases.set(name, r);
            this.aliasInProgress.delete(name);
            return ty_1.T.named(name);
        }
        return this.boxedRecs.size && this.boxedRecs.has((0, ty_1.tyKey)((0, ty_1.stripIdBoxes)(r))) ? ty_1.T.box(r) : r;
    }
    mutStruct(t, subst, site) {
        for (const m of this.mutStructs)
            if (m.rep === t || this.sameStructure(m.rep, t))
                return m;
        const name = this.nameOf(t, subst, site);
        const failed = this.typeFail.get(name);
        if (failed)
            this.rethrow(failed, site);
        const ms = { name, fields: [], fieldIdx: new Map(), rep: t };
        // registered before the fields are mapped (recursive structures); removed on failure
        this.mutStructs.push(ms);
        this.classFields.set(name, ms.fields);
        try {
            const fs = [];
            for (const p of this.checker.getPropertiesOfType(t)) {
                let ft = this.map(this.checker.getTypeOfSymbol(p), subst, site);
                if ((p.flags & ts.SymbolFlags.Optional) && ft.k !== 'opt')
                    ft = ty_1.T.opt(ft);
                fs.push({ name: p.name, ty: ft });
            }
            for (const f of (0, ty_1.sortFields)(fs)) {
                ms.fieldIdx.set(f.name, ms.fields.length);
                ms.fields.push(f);
            }
        }
        catch (e) {
            this.mutStructs.splice(this.mutStructs.indexOf(ms), 1);
            this.classFields.delete(name);
            this.typeFail.set(name, e);
            throw e;
        }
        return ms;
    }
    /** types (classes, heap structures) whose fields have no IR type, with the reason */
    typeFail = new Map();
    /** Re-raise a remembered failure at a new site (same rule and message). */
    rethrow(e, site) {
        const r = e;
        (0, diag_1.reject)(site, r.rule ?? 'unsupported-type', r.message ?? String(e), r.extName);
    }
    /** The class instantiation of a class instance type. */
    classInst(t, subst, site) {
        const sym = t.getSymbol();
        const decl = sym.declarations?.find(d => ts.isClassDeclaration(d) || ts.isClassExpression(d));
        if (!decl)
            (0, diag_1.reject)(site, 'unsupported-type', `class ${sym.name} without declaration`);
        const tparams = decl.typeParameters?.map(tp => this.checker.getTypeAtLocation(tp)) ?? [];
        const args = t.objectFlags & ts.ObjectFlags.Reference ? this.checker.getTypeArguments(t) : [];
        const csubst = new Map();
        tparams.forEach((tp, i) => { if (args[i])
            csubst.set(tp, this.map(args[i], subst, site)); });
        const name = (sym.name) + (tparams.length ? `<${tparams.map(tp => (0, ty_1.prettyTy)(csubst.get(tp))).join(', ')}>` : '');
        const known = this.classes.get(name);
        if (known)
            return known;
        const failed = this.typeFail.get(name);
        if (failed)
            this.rethrow(failed, site);
        if (decl.heritageClauses?.some(h => h.token === ts.SyntaxKind.ExtendsKeyword))
            (0, diag_1.reject)(site, 'no-extends', `class ${sym.name} extends another class`);
        const ci = { name, decl, subst: csubst, instType: t, fields: [], fieldIdx: new Map() };
        this.classes.set(name, ci);
        try {
            this.classFieldsOf(ci, decl, csubst);
        }
        catch (e) {
            this.classes.delete(name);
            this.classFields.delete(name);
            this.typeFail.set(name, e);
            throw e;
        }
        return ci;
    }
    classFieldsOf(ci, decl, csubst) {
        const name = ci.name;
        this.classFields.set(name, ci.fields);
        // fields: parameter properties first, then property declarations (declaration order)
        const ctor = decl.members.find(ts.isConstructorDeclaration);
        const fieldDecls = [];
        if (ctor)
            for (const p of ctor.parameters) {
                if (ts.getModifiers(p)?.some(m => [ts.SyntaxKind.PublicKeyword, ts.SyntaxKind.PrivateKeyword, ts.SyntaxKind.ProtectedKeyword, ts.SyntaxKind.ReadonlyKeyword].includes(m.kind))) {
                    if (!ts.isIdentifier(p.name))
                        (0, diag_1.reject)(p, 'unsupported-syntax', 'destructured parameter property');
                    fieldDecls.push({ name: p.name.text, node: p });
                }
            }
        for (const m of decl.members) {
            if (ts.isPropertyDeclaration(m) && !ts.getModifiers(m)?.some(x => x.kind === ts.SyntaxKind.StaticKeyword)) {
                if (!ts.isIdentifier(m.name) && !ts.isPrivateIdentifier(m.name))
                    (0, diag_1.reject)(m, 'unsupported-syntax', 'computed property name');
                fieldDecls.push({ name: m.name.text, node: m });
            }
        }
        for (const fd of fieldDecls) {
            const ptype = this.checker.getTypeAtLocation(fd.node);
            let ft = this.map(ptype, csubst, fd.node);
            if (ts.isPropertyDeclaration(fd.node) && fd.node.questionToken && ft.k !== 'opt')
                ft = ty_1.T.opt(ft);
            ci.fieldIdx.set(fd.name, ci.fields.length);
            ci.fields.push({ name: fd.name, ty: ft });
        }
    }
}
exports.TypeMapper = TypeMapper;

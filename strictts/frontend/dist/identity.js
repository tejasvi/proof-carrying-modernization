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
// Identity of functions and records. JavaScript functions and objects have identity: a `Set` of
// listeners, a `Map` keyed by objects, `===` between two objects and `indexOf` / `includes` /
// `lastIndexOf` over arrays of them compare them by identity, while StrictTS closures and
// records are values. A function type or record type whose values are compared like that
// anywhere in the program is translated, everywhere, as `box (fn …)` / `box (record …)`: a heap
// cell holding the closure or the record, compared by its address.
//   - creation: an arrow or function expression of such a type is `boxNew` of the closure at each
//     evaluation (two evaluations, two objects); a top-level function (or a module-level const
//     arrow translated as one) used as a value is one cell created when the module starts; an
//     object literal of such a record type (spreads included) is a new cell at each evaluation,
//     as is the rest of an object pattern;
//   - use: a call through a cell is `boxGet` and the call, a field read `boxGet` and the read;
//     where a plain function or record is expected (library callbacks, records of another type,
//     unknown values, arguments of externs) the cell is read (`boxGet`) at the boundary;
//   - a value of another type becoming such a cell (which could create two cells for one
//     object: a record of a wider type, an unknown value, the result of an extern) is rejected
//     (`fn-identity`, `record-identity`); the cells are never written.
// Comparing with `undefined`, `null` or a primitive value does not compare objects. Recursive
// (named) record types stay values. Programs without such comparisons translate as before.
const ts = __importStar(require("typescript"));
const ty_1 = require("./ty");
const core_1 = require("./core");
const types_1 = require("./types");
const P = core_1.Translator.prototype;
const COLLECTIONS = new Set(['Set', 'ReadonlySet', 'WeakSet', 'Map', 'ReadonlyMap', 'WeakMap']);
const OBJECT_FLAGS = ts.TypeFlags.Object | ts.TypeFlags.NonPrimitive | ts.TypeFlags.Intersection;
P.analyzeIdentity = function (files) {
    // (a separate mapper: types are mapped without the boxing, and its caches stay apart)
    const am = new types_1.TypeMapper(this.checker, this.program, this.analysis);
    am.strict = this.types.strict;
    const fns = new Set(), recs = new Set();
    const add = (t, site) => {
        const members = t.isUnion() ? t.types : [t];
        for (const m of members) {
            if (!(m.flags & ts.TypeFlags.Object))
                continue;
            // (regular expressions stay records: `===` on them is rejected)
            const sym = m.getSymbol();
            if (sym && sym.name === 'RegExp' && (0, types_1.isLibDecl)(this.program, sym.declarations?.[0]))
                continue;
            let ty;
            try {
                ty = am.map(m, new Map(), site);
            }
            catch {
                ty = undefined;
            }
            if (ty && ty.k === 'fn')
                fns.add((0, ty_1.tyKey)((0, ty_1.stripIdBoxes)(ty)));
            // (mutable objects are heap objects already)
            else if (ty && ty.k === 'record' && ty.fs.length && !(0, ty_1.tyEq)(ty, ty_1.REGEXP_TY) && !(0, ty_1.tyEq)(ty, ty_1.TIMER_TY))
                recs.add((0, ty_1.tyKey)((0, ty_1.stripIdBoxes)(ty)));
        }
    };
    const canBeObject = (t) => (t.isUnion() ? t.types : [t]).some(m => (m.flags & OBJECT_FLAGS) !== 0);
    const collectionArg = (t, site) => {
        const members = t.isUnion() ? t.types : [t];
        for (const m of members) {
            const sym = m.getSymbol();
            if (!sym || !COLLECTIONS.has(sym.name) || !(0, types_1.isLibDecl)(this.program, sym.declarations?.[0]))
                continue;
            const args = (m.flags & ts.TypeFlags.Object) ? this.checker.getTypeArguments(m) : [];
            if (args.length)
                add(args[0], site);
        }
    };
    const visit = (n) => {
        // (JSX is not translated; asking for the type of an intrinsic tag name such as `img` would
        // even add a "Cannot find name" diagnostic to the program)
        if (ts.isJsxElement(n) || ts.isJsxSelfClosingElement(n) || ts.isJsxFragment(n))
            return;
        if (ts.isIdentifier(n) || ts.isNewExpression(n)) {
            try {
                collectionArg(this.checker.getTypeAtLocation(n), n);
            }
            catch { /* no type */ }
        }
        else if (ts.isBinaryExpression(n) && (n.operatorToken.kind === ts.SyntaxKind.EqualsEqualsEqualsToken || n.operatorToken.kind === ts.SyntaxKind.ExclamationEqualsEqualsToken)) {
            const lt = this.checker.getTypeAtLocation(n.left), rt = this.checker.getTypeAtLocation(n.right);
            if (canBeObject(lt) && canBeObject(rt)) {
                add(lt, n);
                add(rt, n);
            }
        }
        else if (ts.isCallExpression(n) && ts.isPropertyAccessExpression(n.expression) && ['indexOf', 'includes', 'lastIndexOf'].includes(n.expression.name.text)) {
            const rt = this.checker.getTypeAtLocation(n.expression.expression);
            if (this.checker.isArrayType(rt)) {
                const args = this.checker.getTypeArguments(rt);
                if (args.length)
                    add(args[0], n);
            }
        }
        ts.forEachChild(n, visit);
    };
    for (const sf of files)
        visit(sf);
    for (const k of fns)
        this.types.boxedFns.add(k);
    for (const k of recs)
        this.types.boxedRecs.add(k);
};

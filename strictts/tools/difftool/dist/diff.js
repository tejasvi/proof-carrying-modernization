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
exports.makeProject = exports.MONO_NAME = exports.RET_NAME = exports.COMPAT_NAME = void 0;
exports.pairUnits = pairUnits;
exports.prepare = prepare;
exports.fuzzUnit = fuzzUnit;
exports.proofSlices = proofSlices;
exports.compatWrapper = compatWrapper;
exports.retWrapper = retWrapper;
exports.monoWrapper = monoWrapper;
// The semantic diff pipeline: pair the function units of two file sets, slice every changed
// unit, fuzz old against new in Node, then confirm counterexamples or attempt proofs in Lean.
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const ts = __importStar(require("typescript"));
const project_1 = require("./project");
Object.defineProperty(exports, "makeProject", { enumerable: true, get: function () { return project_1.makeProject; } });
const units_1 = require("./units");
const slice_1 = require("./slice");
const typedesc_1 = require("./typedesc");
const fuzz_1 = require("./fuzz");
const util_1 = require("./util");
function moduleKey(set, rel) {
    return set.single ? '<file>' : rel;
}
function safeName(s) {
    return s.replace(/[^A-Za-z0-9_]/g, '_').replace(/_+/g, '_').slice(0, 60);
}
function pairUnits(oldP, newP, opts) {
    const collect = (p) => {
        const m = new Map();
        const files = p.set.single ? p.set.roots : p.set.roots;
        for (const f of files)
            for (const u of (0, units_1.unitsOf)(p, f, moduleKey(p.set, f)))
                if (!m.has(u.key))
                    m.set(u.key, u);
        return m;
    };
    const om = collect(oldP), nm = collect(newP);
    const out = [];
    let n = 0;
    for (const [k, ou] of om) {
        if (opts.only && !opts.only.test(k))
            continue;
        const nu = nm.get(k);
        if (!nu) {
            out.push({ key: k, file: ou.file, name: ou.name, kind: ou.kind, status: 'removed', reasons: [], notes: [] });
            continue;
        }
        if (nu.text === ou.text)
            continue;
        const dir = path.join(opts.work, 'units', `${String(++n).padStart(3, '0')}_${safeName(ou.name)}`);
        out.push({ key: k, file: nu.file, name: nu.name, kind: nu.kind, status: 'changed', reasons: [], notes: [], ctx: { oldUnit: ou, newUnit: nu, dir } });
    }
    for (const [k, nu] of nm) {
        if (opts.only && !opts.only.test(k))
            continue;
        if (!om.has(k))
            out.push({ key: k, file: nu.file, name: nu.name, kind: nu.kind, status: 'added', reasons: [], notes: [] });
    }
    return out;
}
function version(sl, u) {
    return { files: sl.files, entry: sl.entry, exportName: sl.exportName, kind: u.kind, method: u.cls ? u.name.slice(u.cls.length + 1) : undefined, hostGlobals: sl.hostGlobals };
}
/** Slices and signatures of a changed unit; returns false (with reasons) when it cannot be fuzzed. */
function prepare(r, oldP, newP) {
    const c = r.ctx;
    (0, util_1.mkdirp)(c.dir);
    c.oldSlice = (0, slice_1.sliceUnit)(oldP, c.oldUnit, path.join(c.dir, 'old'));
    c.newSlice = (0, slice_1.sliceUnit)(newP, c.newUnit, path.join(c.dir, 'new'));
    for (const [which, sl] of [['old', c.oldSlice], ['new', c.newSlice]]) {
        if (!sl.ok)
            r.reasons.push(`${which} slice: ${sl.reason}`);
        if (sl.hostGlobals.length)
            r.notes.push(`${which} uses host globals: ${sl.hostGlobals.join(', ')}`);
    }
    if (r.reasons.length)
        return false;
    if (c.oldUnit.kind !== c.newUnit.kind) {
        r.reasons.push(`kind changed (${c.oldUnit.kind} -> ${c.newUnit.kind})`);
        return false;
    }
    try {
        c.sig = (0, typedesc_1.signatureOf)(oldP, c.oldUnit);
        const ns = (0, typedesc_1.signatureOf)(newP, c.newUnit);
        const cp = (0, typedesc_1.compatibleParams)(c.sig.params, c.sig.table, ns.params, ns.table);
        if (!cp.ok) {
            r.reasons.push(`signature changed (${cp.reason}): (${c.sig.params.map(p => p.text).join(', ')}) -> (${ns.params.map(p => p.text).join(', ')})`);
            return false;
        }
        if (cp.widened)
            r.notes.push('parameter types widened; inputs come from the old parameter types');
        if (c.sig.self && ns.self) {
            const cs = (0, typedesc_1.compatibleParams)(c.sig.self.ctor, c.sig.table, ns.self.ctor, ns.table);
            if (!cs.ok) {
                r.reasons.push(`constructor of the receiver class changed (${cs.reason})`);
                return false;
            }
        }
        r.notes.push(...c.sig.notes);
    }
    catch (e) {
        r.reasons.push(`signature: ${e.message}`);
        return false;
    }
    for (const p of [...c.sig.params, ...(c.sig.self?.ctor ?? [])]) {
        if (p.opt && p.t.k === 'unsupported')
            continue;
        const bad = (0, typedesc_1.unsupportedIn)(p.rest && p.t.k === 'arr' ? p.t.t : p.t, c.sig.table);
        if (bad) {
            r.reasons.push(`parameter ${p.name}: inputs of this type are not generated (${bad})`);
            return false;
        }
    }
    return true;
}
async function fuzzUnit(r, opts) {
    const c = r.ctx;
    const lits = (0, fuzz_1.mineLiterals)([...c.oldSlice.files.values(), ...c.newSlice.files.values()]);
    c.fuzz = await (0, fuzz_1.fuzzPair)(version(c.oldSlice, c.oldUnit), version(c.newSlice, c.newUnit), c.sig, {
        runs: opts.runs, seed: opts.seed, timeoutMs: opts.timeoutMs, shrinkBudget: opts.shrinkBudget, nums: lits.nums, strs: lits.strs, props: lits.props,
    });
    r.fuzz = { runs: c.fuzz.runs, inconclusive: c.fuzz.inconclusive, ms: c.fuzz.ms };
    r.notes.push(...c.fuzz.notes);
    if (c.fuzz.status === 'error')
        r.reasons.push(`fuzzing: ${c.fuzz.error}`);
}
function proofSlices(r) {
    const c = r.ctx;
    c.oldProof = (0, slice_1.inlineConstants)(c.oldSlice, c.oldUnit.name, path.join(c.dir, 'old_proof'));
    c.newProof = (0, slice_1.inlineConstants)(c.newSlice, c.newUnit.name, path.join(c.dir, 'new_proof'));
}
/** Name of the wrapper that `compatWrapper` adds to the new version's proof slice. */
exports.COMPAT_NAME = '__difftool_compat';
/** Compatibility wrapper for a change that widens a function's parameters (a parameter made
 * optional, a union widened): `COMPAT_NAME` takes the OLD version's parameters (their declared
 * types, from the old source; for a generic function at the instance of `monoWrapper`) and calls the
 * new version with them; appended to the new version's proof slice, so that the proof compares the
 * two versions on the old version's inputs. TypeScript checks that the call is well typed (otherwise
 * the translation fails and the pair stays UNKNOWN). */
function compatWrapper(oldU, newName, sl) {
    if ((oldU.kind !== 'function' && oldU.kind !== 'arrow') || oldU.name.includes('.'))
        return { error: `no compatibility wrapper for ${oldU.kind} ${oldU.name}` };
    const pl = paramList(oldU, 'old');
    if ('error' in pl)
        return pl;
    return appendWrapper(sl, exports.COMPAT_NAME, `(${pl.params.join(', ')})`, `${newName}(${pl.args.join(', ')})`);
}
/** Name of the wrapper that `retWrapper` adds to a proof slice. */
exports.RET_NAME = '__difftool_ret';
/** Return-type wrapper for a change of the declared return type (e.g. `T` to `T | undefined`, a type
 * widened to `unknown`): `RET_NAME` takes `u`'s parameters (at the instance of `monoWrapper` for a
 * generic function), calls `u`, and is declared with the OTHER version's return type (at its instance),
 * so that the proof compares the two versions at that type. Appended to `u`'s proof slice. TypeScript
 * checks that `u`'s result has that type (otherwise the translation fails and the pair stays UNKNOWN). */
function retWrapper(u, other, sl) {
    if ((u.kind !== 'function' && u.kind !== 'arrow') || u.name.includes('.'))
        return { error: `no return-type wrapper for ${u.kind} ${u.name}` };
    if (!other.fn.type)
        return { error: `${other.name}: no declared return type` };
    const pl = paramList(u, 'wrapped');
    if ('error' in pl)
        return pl;
    const so = instSubst(other);
    if ('error' in so)
        return so;
    const ret = [...so.map].reduce((t, [k, v]) => t.replace(new RegExp(`\\b${k}\\b`, 'g'), v), other.fn.type.getText());
    return appendWrapper(sl, exports.RET_NAME, `(${pl.params.join(', ')}): ${ret}`, `${u.name}(${pl.args.join(', ')})`);
}
/** `u`'s parameter list with declared types (at the instance of `monoWrapper`) and the matching
 * argument list. */
function paramList(u, which) {
    const subst = instSubst(u);
    if ('error' in subst)
        return subst;
    const sub = (s) => [...subst.map].reduce((t, [k, v]) => t.replace(new RegExp(`\\b${k}\\b`, 'g'), v), s);
    const params = [], args = [];
    for (const [pi, p] of u.fn.parameters.entries()) {
        if (ts.isIdentifier(p.name) && p.name.text === 'this')
            return { error: `${which} parameter this` };
        // (a destructured parameter is passed whole under a name of its own)
        const nm = ts.isIdentifier(p.name) ? p.name.text : `__difftool_p${pi}`;
        let ty = p.type ? sub(p.type.getText()) : undefined;
        if (!ty && p.initializer) {
            const i = p.initializer;
            ty = ts.isNumericLiteral(i) || (ts.isPrefixUnaryExpression(i) && ts.isNumericLiteral(i.operand)) ? 'number'
                : ts.isStringLiteral(i) || ts.isNoSubstitutionTemplateLiteral(i) ? 'string'
                    : i.kind === ts.SyntaxKind.TrueKeyword || i.kind === ts.SyntaxKind.FalseKeyword ? 'boolean' : undefined;
        }
        if (!ty && u.paramTypes[pi])
            ty = sub(u.paramTypes[pi]);
        if (!ty)
            return { error: `${which} parameter ${nm} has no type` };
        const rest = !!p.dotDotDotToken;
        params.push(`${rest ? '...' : ''}${nm}${!rest && (p.questionToken || p.initializer) ? '?' : ''}: ${ty}`);
        args.push(`${rest ? '...' : ''}${nm}`);
    }
    return { params, args };
}
/** Append `export function NAME<signature> { return <call>; }` to the slice's entry file. */
function appendWrapper(sl, name, signature, call) {
    const file = path.join(sl.dir, sl.entry);
    const text = fs.readFileSync(file, 'utf8');
    if (new RegExp(`\\b${name}\\b`).test(text))
        return { error: `${name} already defined in ${sl.entry}` };
    const wrapper = `\nexport function ${name}${signature} {\n  return ${call};\n}\n`;
    fs.writeFileSync(file, text + wrapper);
    sl.files.set(sl.entry, text + wrapper);
    return { ok: true };
}
/** Name of the monomorphic wrapper that `monoWrapper` adds to a proof slice. */
exports.MONO_NAME = '__difftool_inst';
/** The type a type parameter with this constraint (its text, spaces collapsed) is instantiated
 * with; '' = no constraint. Arrays and array-like containers become arrays of numbers, objects and
 * records a record of numbers, top types a number. */
const INSTANCES = {
    '': 'number', PropertyKey: 'string', string: 'string', number: 'number', any: 'number', unknown: 'number', '{}': 'number',
    'unknown[]': 'number[]', 'readonly unknown[]': 'readonly number[]', 'ReadonlyArray<unknown>': 'readonly number[]',
    IterableContainer: 'readonly number[]', 'ReadonlyArray<bigint> | ReadonlyArray<number>': 'readonly number[]',
    object: 'Record<string, number>', 'Record<string, unknown>': 'Record<string, number>', 'Record<PropertyKey, any>': 'Record<string, number>',
};
/** The instance of `monoWrapper`: each type parameter of `u` and its type (empty for a non-generic
 * function). */
function instSubst(u) {
    const map = new Map();
    for (const tp of u.fn.typeParameters ?? []) {
        const c = tp.constraint ? tp.constraint.getText().replace(/\s+/g, ' ') : '';
        const inst = INSTANCES[c];
        if (!inst)
            return { error: `generic ${u.name}: no instance for the constraint ${tp.name.text} extends ${c}` };
        map.set(tp.name.text, inst);
    }
    return { map };
}
/** Monomorphic wrapper for a generic top-level function (the IR is monomorphic, and a slice has
 * no call site that fixes the type arguments): `MONO_NAME` calls the target at one instance (the
 * type of `INSTANCES` for each type parameter's constraint; other constraints are not
 * instantiated), appended to the proof slice's entry file. Both versions get the wrapper of their
 * own signature; the proof is then about the two wrappers. Returns the instance (for the report)
 * or the reason no wrapper was written. */
function monoWrapper(u, sl) {
    if ((u.kind !== 'function' && u.kind !== 'arrow') || u.name.includes('.'))
        return { error: `generic ${u.kind} ${u.name}: no instance for methods` };
    const s = instSubst(u);
    if ('error' in s)
        return s;
    const subst = s.map;
    const sub = (s) => [...subst].reduce((t, [k, v]) => t.replace(new RegExp(`\\b${k}\\b`, 'g'), v), s);
    const params = [], args = [];
    for (const [pi, p] of u.fn.parameters.entries()) {
        if (ts.isIdentifier(p.name) && p.name.text === 'this')
            return { error: `generic ${u.name}: parameter this` };
        const nm = ts.isIdentifier(p.name) ? p.name.text : `__difftool_p${pi}`;
        let ty = p.type ? sub(p.type.getText()) : undefined;
        if (!ty && p.initializer) {
            const i = p.initializer;
            ty = ts.isNumericLiteral(i) || (ts.isPrefixUnaryExpression(i) && ts.isNumericLiteral(i.operand)) ? 'number'
                : ts.isStringLiteral(i) || ts.isNoSubstitutionTemplateLiteral(i) ? 'string'
                    : i.kind === ts.SyntaxKind.TrueKeyword || i.kind === ts.SyntaxKind.FalseKeyword ? 'boolean' : undefined;
        }
        if (!ty && u.paramTypes[pi])
            ty = sub(u.paramTypes[pi]);
        if (!ty)
            return { error: `generic ${u.name}: parameter ${nm} has no type to instantiate` };
        const rest = !!p.dotDotDotToken;
        params.push(`${rest ? '...' : ''}${nm}${!rest && (p.questionToken || p.initializer) ? '?' : ''}: ${ty}`);
        args.push(`${rest ? '...' : ''}${nm}`);
    }
    const file = path.join(sl.dir, sl.entry);
    const text = fs.readFileSync(file, 'utf8');
    if (new RegExp(`\\b${exports.MONO_NAME}\\b`).test(text))
        return { error: `${exports.MONO_NAME} already defined in ${sl.entry}` };
    const wrapper = `\nexport function ${exports.MONO_NAME}(${params.join(', ')}) {\n  return ${u.name}(${args.join(', ')});\n}\n`;
    fs.writeFileSync(file, text + wrapper);
    sl.files.set(sl.entry, text + wrapper);
    return { inst: [...subst].map(([k, v]) => `${k} := ${v}`).join(', ') };
}

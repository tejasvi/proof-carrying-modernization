"use strict";
// StrictTS types (mirror of `StrictTS/Core/Ty.lean`), printing to Lean, canonical order.
Object.defineProperty(exports, "__esModule", { value: true });
exports.TA_ELEM_BIG = exports.TIMER_TY = exports.REGEXP_TY = exports.T = void 0;
exports.leanStrLit = leanStrLit;
exports.hasLoneSurrogate = hasLoneSurrogate;
exports.leanJSStr = leanJSStr;
exports.tyEq = tyEq;
exports.tyKey = tyKey;
exports.showFields = showFields;
exports.showTy = showTy;
exports.showTys = showTys;
exports.prettyTy = prettyTy;
exports.stripIdBoxes = stripIdBoxes;
exports.eqable = eqable;
exports.sortTys = sortTys;
exports.sortFields = sortFields;
exports.isObjectLike = isObjectLike;
exports.taElem = taElem;
exports.T = {
    num: { k: 'num' },
    bigint: { k: 'bigint' },
    bool: { k: 'bool' },
    str: { k: 'str' },
    undef: { k: 'undef' },
    null: { k: 'null' },
    err: { k: 'err' },
    arr: (t) => ({ k: 'arr', t }),
    tarr: (kind) => ({ k: 'tarr', kind }),
    map: (key, val) => ({ k: 'map', key, val }),
    set: (t) => ({ k: 'set', t }),
    tup: (ts) => ({ k: 'tup', ts }),
    record: (fs) => ({ k: 'record', fs }),
    obj: (c) => ({ k: 'obj', c }),
    named: (n) => ({ k: 'named', n }),
    opt: (t) => ({ k: 'opt', t }),
    union: (ts) => ({ k: 'union', ts }),
    enum: (cases) => ({ k: 'enum', cases }),
    fn: (args, ret) => ({ k: 'fn', args, ret }),
    promise: (t) => ({ k: 'promise', t }),
    box: (t) => ({ k: 'box', t }),
    ext: (name) => ({ k: 'ext', name }),
    dict: (t) => ({ k: 'dict', t }),
    dyn: { k: 'dyn' },
};
/** A `RegExp` value: the record of its flags and source (regex.ts). Its `lastIndex` is not
 * modelled: `test` / `exec` on a global or sticky one are rejected or panic. */
exports.REGEXP_TY = exports.T.record([{ name: 'flags', ty: exports.T.str }, { name: 'source', ty: exports.T.str }]);
/** Node's timer handle (`NodeJS.Timeout`, an object in Node) holding the number the semantics'
 * `setTimeout` returns: it can be stored, passed, tested for `null` / `undefined` and for
 * truthiness (an object: always true); its number (Node's `Symbol.toPrimitive`) is not
 * observable (no strings, arithmetic, comparisons, methods or unknown values: `timer-handle`). */
exports.TIMER_TY = exports.T.record([{ name: '$timer', ty: exports.T.num }]);
/** A Lean string literal. Lean strings cannot hold lone surrogates; callers that may meet
 * them use `leanJSStr`. */
function leanStrLit(s) {
    let out = '"';
    for (const ch of s) {
        const c = ch.codePointAt(0);
        if (ch === '"')
            out += '\\"';
        else if (ch === '\\')
            out += '\\\\';
        else if (ch === '\n')
            out += '\\n';
        else if (ch === '\t')
            out += '\\t';
        else if (ch === '\r')
            out += '\\r';
        else if (c < 0x20 || c === 0x7f)
            out += '\\x' + c.toString(16).padStart(2, '0');
        else if (c >= 0xd800 && c < 0xe000)
            throw new Error('lone surrogate in Lean string');
        else
            out += ch;
    }
    return out + '"';
}
function hasLoneSurrogate(s) {
    for (let i = 0; i < s.length; i++) {
        const c = s.charCodeAt(i);
        if (c >= 0xd800 && c < 0xdc00) {
            const d = i + 1 < s.length ? s.charCodeAt(i + 1) : 0;
            if (d >= 0xdc00 && d < 0xe000) {
                i++;
                continue;
            }
            return true;
        }
        if (c >= 0xdc00 && c < 0xe000)
            return true;
    }
    return false;
}
/** A `JSStr` term for a JavaScript string (UTF-16 units). */
function leanJSStr(s) {
    if (hasLoneSurrogate(s)) {
        const units = [];
        for (let i = 0; i < s.length; i++)
            units.push(s.charCodeAt(i));
        return `(⟨[${units.join(', ')}]⟩ : JSStr)`;
    }
    return `(js! ${leanStrLit(s)})`;
}
function tyEq(a, b) {
    return tyKey(a) === tyKey(b);
}
/** Canonical key of a type (also its Lean printing). */
function tyKey(t) {
    return showTy(t);
}
function showTys(ts) {
    return `tys[${ts.map(showTy).join(', ')}]`;
}
function showFields(fs) {
    return `flds[${fs.map(f => `${leanStrLit(f.name)} : ${showTy(f.ty)}`).join(', ')}]`;
}
/** Lean term of type `Ty`, always self-delimiting (atomic or parenthesised). */
function showTy(t) {
    switch (t.k) {
        case 'num':
        case 'bigint':
        case 'bool':
        case 'str':
        case 'undef':
        case 'null':
        case 'err':
            return '.' + t.k;
        case 'arr': return `(.arr ${showTy(t.t)})`;
        case 'tarr': return `(.tarr .${t.kind})`;
        case 'map': return `(.map ${showTy(t.key)} ${showTy(t.val)})`;
        case 'set': return `(.set ${showTy(t.t)})`;
        case 'tup': return `(.tup ${showTys(t.ts)})`;
        case 'record': return `(.record ${showFields(t.fs)})`;
        case 'obj': return `(.obj ${leanStrLit(t.c)})`;
        case 'named': return `(.named ${leanStrLit(t.n)})`;
        case 'opt': return `(.opt ${showTy(t.t)})`;
        case 'union': return `(.union ${showTys(t.ts)})`;
        case 'enum': return `(.enum [${t.cases.map(leanStrLit).join(', ')}])`;
        case 'fn': return `(.fn ${showTys(t.args)} ${showTy(t.ret)})`;
        case 'promise': return `(.promise ${showTy(t.t)})`;
        case 'box': return `(.box ${showTy(t.t)})`;
        case 'ext': return `(.ext ${leanStrLit(t.name)})`;
        case 'dict': return `(.dict ${showTy(t.t)})`;
        case 'dyn': return '.dyn';
    }
}
/** Human-readable TypeScript-like rendering (diagnostics). */
function prettyTy(t) {
    if (t.k === 'record' && t.fs.length === 1 && t.fs[0].name === '$timer')
        return 'NodeJS.Timeout';
    switch (t.k) {
        case 'num': return 'number';
        case 'bigint': return 'bigint';
        case 'bool': return 'boolean';
        case 'str': return 'string';
        case 'undef': return 'undefined';
        case 'null': return 'null';
        case 'err': return 'Error';
        case 'arr': return `${prettyTy(t.t)}[]`;
        case 'tarr': return `TypedArray<${t.kind}>`;
        case 'map': return `Map<${prettyTy(t.key)}, ${prettyTy(t.val)}>`;
        case 'set': return `Set<${prettyTy(t.t)}>`;
        case 'tup': return `[${t.ts.map(prettyTy).join(', ')}]`;
        case 'record': return `{ ${t.fs.map(f => `${f.name}: ${prettyTy(f.ty)}`).join('; ')} }`;
        case 'obj': return t.c;
        case 'named': return t.n;
        case 'opt': return `${prettyTy(t.t)} | undefined`;
        case 'union': return t.ts.map(prettyTy).join(' | ');
        case 'enum': return t.cases.map(c => JSON.stringify(c)).join(' | ');
        case 'fn': return `(${t.args.map(prettyTy).join(', ')}) => ${prettyTy(t.ret)}`;
        case 'promise': return `Promise<${prettyTy(t.t)}>`;
        case 'box': return `Box<${prettyTy(t.t)}>`;
        case 'ext': return t.name;
        case 'dict': return `Record<string, ${prettyTy(t.t)}>`;
        case 'dyn': return 'unknown';
    }
}
/** The type with every `box (fn …)` / `box (record …)` (a function or object with identity, see
 * identity.ts) replaced by the function or record type: the key for the identity analysis. */
function stripIdBoxes(t) {
    switch (t.k) {
        case 'box': return t.t.k === 'fn' || t.t.k === 'record' ? stripIdBoxes(t.t) : exports.T.box(stripIdBoxes(t.t));
        case 'fn': return exports.T.fn(t.args.map(stripIdBoxes), stripIdBoxes(t.ret));
        case 'arr': return exports.T.arr(stripIdBoxes(t.t));
        case 'set': return exports.T.set(stripIdBoxes(t.t));
        case 'opt': return exports.T.opt(stripIdBoxes(t.t));
        case 'promise': return exports.T.promise(stripIdBoxes(t.t));
        case 'dict': return exports.T.dict(stripIdBoxes(t.t));
        case 'map': return exports.T.map(stripIdBoxes(t.key), stripIdBoxes(t.val));
        case 'tup': return exports.T.tup(t.ts.map(stripIdBoxes));
        case 'union': return exports.T.union(t.ts.map(stripIdBoxes));
        case 'record': return exports.T.record(t.fs.map(f => ({ name: f.name, ty: stripIdBoxes(f.ty) })));
        default: return t;
    }
}
/** `Ty.eqable` of the Lean development. */
function eqable(t) {
    switch (t.k) {
        case 'num':
        case 'bigint':
        case 'bool':
        case 'str':
        case 'undef':
        case 'null': return true;
        case 'arr':
        case 'tarr':
        case 'map':
        case 'set':
        case 'obj':
        case 'promise':
        case 'box':
        case 'ext':
        case 'dict': return true;
        case 'enum': return true;
        case 'opt': return eqable(t.t);
        case 'union': return t.ts.every(eqable);
        default: return false;
    }
}
/** Canonical order of union members. */
function sortTys(ts) {
    const seen = new Map();
    for (const t of ts)
        seen.set(tyKey(t), t);
    return [...seen.keys()].sort().map(k => seen.get(k));
}
function sortFields(fs) {
    return [...fs].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}
/** Types that are object-like for truthiness (pure null tests). */
function isObjectLike(t) {
    switch (t.k) {
        case 'arr':
        case 'tarr':
        case 'map':
        case 'set':
        case 'obj':
        case 'record':
        case 'tup':
        case 'fn':
        case 'promise':
        case 'err':
        case 'named':
        case 'ext':
        case 'dict':
        case 'box':
            return true;
        case 'union': return t.ts.every(isObjectLike);
        default: return false;
    }
}
exports.TA_ELEM_BIG = new Set(['bi64', 'bu64']);
function taElem(k) {
    return exports.TA_ELEM_BIG.has(k) ? exports.T.bigint : exports.T.num;
}

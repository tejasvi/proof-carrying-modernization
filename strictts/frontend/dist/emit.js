"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.Emitter = void 0;
exports.lamFreeVars = lamFreeVars;
exports.q = q;
exports.fieldsName = fieldsName;
exports.typeTableLines = typeTableLines;
exports.funRefLines = funRefLines;
exports.globalRefLine = globalRefLine;
exports.funDefLines = funDefLines;
exports.mainBlockLines = mainBlockLines;
exports.externAbbrevLine = externAbbrevLine;
exports.argList = argList;
exports.emitProgram = emitProgram;
// Lean emission: named IR -> de Bruijn IR terms of `StrictTS/Core/Syntax.lean`.
const ty_1 = require("./ty");
const ir_1 = require("./ir");
function slot(v) {
    return `⟨${(0, ty_1.showTy)(v.ty)}, ${v.assigned}⟩`;
}
function lookup(ctx, v, what) {
    const i = ctx.indexOf(v);
    if (i < 0)
        throw new ir_1.InternalError(`unbound variable ${v.name}#${v.id} (${what})`);
    return i;
}
// ---------------------------------------------------------------------------------------
// Free variables of closures (binders are unique objects, so "referenced minus bound"
// gives the free variables; order = first reference).
function collectE(e, refs, bound) {
    switch (e.k) {
        case 'lit':
        case 'gget':
        case 'funVal':
        case 'newObj':
        case 'none':
        case 'enumLit': return;
        case 'var':
            refs.push(e.v);
            return;
        case 'prim':
        case 'builtin':
        case 'mkTup':
        case 'mkRec':
        case 'call':
        case 'extern':
            e.args.forEach(a => collectE(a, refs, bound));
            return;
        case 'app':
            collectE(e.f, refs, bound);
            e.args.forEach(a => collectE(a, refs, bound));
            return;
        case 'and':
        case 'or':
            collectE(e.a, refs, bound);
            collectE(e.b, refs, bound);
            return;
        case 'cond':
            collectE(e.c, refs, bound);
            collectE(e.a, refs, bound);
            collectE(e.b, refs, bound);
            return;
        case 'letE':
            bound.add(e.v);
            collectE(e.init, refs, bound);
            collectE(e.body, refs, bound);
            return;
        case 'lam':
            e.params.forEach(p => bound.add(p));
            collectB(e.body, refs, bound);
            return;
        case 'getTup':
        case 'getRec':
        case 'getField':
        case 'fold':
        case 'unfold':
        case 'some':
        case 'unwrap':
        case 'inj':
            collectE(e.e, refs, bound);
            return;
        case 'caseOpt':
            bound.add(e.v);
            collectE(e.e, refs, bound);
            collectE(e.none, refs, bound);
            collectE(e.some, refs, bound);
            return;
        case 'caseU':
            collectE(e.e, refs, bound);
            e.alts.forEach(a => { bound.add(a.v); collectE(a.body, refs, bound); });
            return;
    }
}
function collectS(s, refs, bound) {
    switch (s.k) {
        case 'expr':
        case 'ret':
        case 'retP':
        case 'throw':
            collectE(s.e, refs, bound);
            return;
        case 'assign':
            refs.push(s.v);
            collectE(s.e, refs, bound);
            return;
        case 'gset':
            collectE(s.e, refs, bound);
            return;
        case 'setField':
            collectE(s.o, refs, bound);
            collectE(s.e, refs, bound);
            return;
        case 'ite':
            collectE(s.c, refs, bound);
            collectB(s.t, refs, bound);
            collectB(s.f, refs, bound);
            return;
        case 'while':
            collectE(s.c, refs, bound);
            collectB(s.body, refs, bound);
            return;
        case 'doWhile':
            collectB(s.body, refs, bound);
            collectE(s.c, refs, bound);
            return;
        case 'forLoop':
            collectE(s.c, refs, bound);
            collectB(s.body, refs, bound);
            collectB(s.step, refs, bound);
            return;
        case 'forOf':
        case 'forOfMap':
        case 'forOfSet':
        case 'forOfStr':
            bound.add(s.v);
            collectE(s.e, refs, bound);
            collectB(s.body, refs, bound);
            return;
        case 'brk':
        case 'cont': return;
        case 'try':
            bound.add(s.v);
            collectB(s.body, refs, bound);
            collectB(s.handler, refs, bound);
            collectB(s.fin, refs, bound);
            return;
        case 'tryFin':
            collectB(s.body, refs, bound);
            collectB(s.fin, refs, bound);
            return;
        case 'caseOptS':
            bound.add(s.v);
            collectE(s.e, refs, bound);
            collectB(s.none, refs, bound);
            collectB(s.some, refs, bound);
            return;
        case 'caseUS':
            collectE(s.e, refs, bound);
            s.alts.forEach(a => { bound.add(a.v); collectB(a.body, refs, bound); });
            return;
        case 'block':
        case 'breakable':
            collectB(s.b, refs, bound);
            return;
    }
}
function collectB(b, refs, bound) {
    for (const it of b) {
        if (it.k === 'stmt')
            collectS(it.s, refs, bound);
        else {
            bound.add(it.v);
            collectE(it.init, refs, bound);
        }
    }
}
const freeCache = new WeakMap();
function lamFreeVars(e) {
    const cached = freeCache.get(e);
    if (cached)
        return cached;
    const refs = [];
    const bound = new Set(e.params);
    collectB(e.body, refs, bound);
    const seen = new Set();
    const free = [];
    for (const v of refs) {
        if (bound.has(v) || seen.has(v))
            continue;
        seen.add(v);
        free.push(v);
    }
    freeCache.set(e, free);
    return free;
}
// ---------------------------------------------------------------------------------------
function paren(s) { return `(${s})`; }
/** Expressions whose type Lean infers without help (so projections need no annotation). */
function obviousTy(e) {
    switch (e.k) {
        case 'var':
        case 'gget':
        case 'call':
        case 'lit': return true;
        case 'unfold': return true;
        default: return false;
    }
}
/** A generated (user-derived) Lean identifier, escaped so that keywords are fine. */
function q(name) { return `«${name}»`; }
/** The field list abbreviation of a class / heap object type: `«C».fields`. */
function fieldsName(c) { return `${q(c.replace(/[^A-Za-z0-9_]/g, '_'))}.fields`; }
class Emitter {
    /** the signatures of the `extern` nodes emitted so far (name, argument types, result) */
    externs = new Map();
    emitExpr(e, ctx) {
        switch (e.k) {
            case 'lit': return `.lit ${e.lean}`;
            case 'var': return `var! ${lookup(ctx, e.v, 'read')}`;
            case 'gget': return `.gget ${q(e.g.leanName)}`;
            case 'prim': return `.prim ${e.op} ${this.args(e.args, ctx)}`;
            case 'builtin': return `.builtin ${e.op} ${this.args(e.args, ctx)}`;
            case 'and': return `.and ${paren(this.emitExpr(e.a, ctx))} ${paren(this.emitExpr(e.b, ctx))}`;
            case 'or': return `.or ${paren(this.emitExpr(e.a, ctx))} ${paren(this.emitExpr(e.b, ctx))}`;
            case 'cond': return `.cond ${paren(this.emitExpr(e.c, ctx))} ${paren(this.emitExpr(e.a, ctx))} ${paren(this.emitExpr(e.b, ctx))}`;
            case 'letE': {
                if (e.v.assigned)
                    throw new ir_1.InternalError('assignment to a letE binder');
                return `.letE ${(0, ty_1.showTy)(e.v.ty)} ${paren(this.emitExpr(e.init, ctx))} ${paren(this.emitExpr(e.body, [e.v, ...ctx]))}`;
            }
            case 'call': return `.call ${q(e.f.leanName + 'Ref')} ${this.args(e.args, ctx)}`;
            // (the argument types are given: `Args … (Tys.toList ?args)` cannot be unified with `[]`;
            // so is the result type of a lambda applied directly, e.g. an async IIFE whose value is
            // discarded, from which Lean could not infer it)
            case 'app': {
                const ft = e.f.ty;
                const ret = e.f.k === 'lam' ? ` (t := ${(0, ty_1.showTy)(ft.ret)})` : '';
                return `.app (args := ${(0, ty_1.showTys)(ft.args)})${ret} ${paren(this.emitExpr(e.f, ctx))} ${this.args(e.args, ctx)}`;
            }
            case 'lam': {
                const free = lamFreeVars(e);
                const caps = free.map(v => {
                    if (v.assigned)
                        throw new ir_1.InternalError(`closure captures assigned variable ${v.name}`);
                    return `cvar! ${lookup(ctx, v, 'capture')}`;
                });
                const delta = `[${free.map(v => `⟨${(0, ty_1.showTy)(v.ty)}, false⟩`).join(', ')}]`;
                const inner = [...e.params, ...free];
                const params = `[${e.params.map(slot).join(', ')}]`;
                const body = this.emitBlock(e.body, inner, '  ');
                return `.lam ${delta} caps[${caps.join(', ')}] (.${e.async ? 'async' : 'sync'} ${params} rfl\n${body})`;
            }
            case 'funVal': return `.funVal ${q(e.f.leanName + 'Ref')}`;
            case 'mkTup': return `.mkTup ${this.args(e.args, ctx)}`;
            case 'getTup': {
                const ts = e.e.ty.ts;
                const ann = obviousTy(e.e) ? '' : ` (ts := ${(0, ty_1.showTys)(ts)})`;
                return `.getTup${ann} ${paren(this.emitExpr(e.e, ctx))} (mem! ${e.idx})`;
            }
            case 'mkRec': return `.mkRec ${this.args(e.args, ctx)}`;
            case 'getRec': {
                const fs = e.e.ty.fs;
                const ann = obviousTy(e.e) ? '' : ` (fs := ${(0, ty_1.showFields)(fs)})`;
                return `.getRec${ann} ${paren(this.emitExpr(e.e, ctx))} (mem! ${e.idx})`;
            }
            case 'newObj': return `.newObj ${(0, ty_1.leanStrLit)(e.c)} ${fieldsName(e.c)}`;
            case 'getField': return `.getField (fs := ${fieldsName(e.c)}) ${paren(this.emitExpr(e.e, ctx))} (mem! ${e.idx})`;
            case 'fold': return `.fold ${paren(this.emitExpr(e.e, ctx))}`;
            case 'unfold': return `.unfold ${paren(this.emitExpr(e.e, ctx))}`;
            case 'none': return `.none`;
            case 'some': return `.some ${paren(this.emitExpr(e.e, ctx))}`;
            case 'unwrap': return `.unwrap ${paren(this.emitExpr(e.e, ctx))}`;
            case 'caseOpt': {
                if (e.v.assigned)
                    throw new ir_1.InternalError('assignment to a caseOpt binder');
                const t = e.e.ty.t;
                return `.caseOpt (t := ${(0, ty_1.showTy)(t)}) ${paren(this.emitExpr(e.e, ctx))} ${paren(this.emitExpr(e.none, ctx))} ${paren(this.emitExpr(e.some, [e.v, ...ctx]))}`;
            }
            case 'inj': return `.inj (mem! ${e.idx}) ${paren(this.emitExpr(e.e, ctx))}`;
            case 'caseU': {
                const ts = e.e.ty.ts;
                const alts = e.alts.map(a => {
                    if (a.v.assigned)
                        throw new ir_1.InternalError('assignment to a caseU binder');
                    return this.emitExpr(a.body, [a.v, ...ctx]);
                });
                return `.caseU (ts := ${(0, ty_1.showTys)(ts)}) ${paren(this.emitExpr(e.e, ctx))} alts[${alts.join(', ')}]`;
            }
            case 'enumLit': return `.enumLit ⟨${e.idx}, by decide⟩`;
            case 'extern': {
                const t = e.async ? e.ty.t : e.ty;
                const sig = { name: e.name, args: e.args.map(a => a.ty), ret: t };
                this.externs.set(`${e.name} ${(0, ty_1.showTys)(sig.args)} ${(0, ty_1.showTy)(t)}`, sig);
                return `.${e.async ? 'externAsync' : 'extern'} (args := [${e.args.map(a => (0, ty_1.showTy)(a.ty)).join(', ')}]) (t := ${(0, ty_1.showTy)(t)}) ${(0, ty_1.leanStrLit)(e.name)} ${this.args(e.args, ctx)}`;
            }
        }
    }
    args(as, ctx) {
        return `args[${as.map(a => this.emitExpr(a, ctx)).join(', ')}]`;
    }
    emitStmt(s, ctx, ind) {
        const E = (e) => paren(this.emitExpr(e, ctx));
        const B = (b, c = ctx) => paren('\n' + this.emitBlock(b, c, ind + '  '));
        switch (s.k) {
            case 'expr': return `.expr ${E(s.e)}`;
            case 'assign': {
                const i = lookup(ctx, s.v, 'assign');
                if (!s.v.assigned)
                    throw new ir_1.InternalError('assign to immutable slot');
                return `.assign (mvar! ${i}) ${E(s.e)}`;
            }
            case 'gset': return `.gset ${q(s.g.leanName)} ${E(s.e)}`;
            case 'setField': return `.setField (fs := ${fieldsName(s.c)}) ${E(s.o)} (mem! ${s.idx}) ${E(s.e)}`;
            case 'ite': return `.ite ${E(s.c)} ${B(s.t)} ${B(s.f)}`;
            case 'while': return `.while ${E(s.c)} ${B(s.body)}`;
            case 'doWhile': return `.doWhile ${B(s.body)} ${E(s.c)}`;
            case 'forLoop': return `.forLoop ${E(s.c)} ${B(s.body)} ${B(s.step)}`;
            case 'forOf':
            case 'forOfMap':
            case 'forOfSet':
            case 'forOfStr':
                if (s.v.assigned)
                    throw new ir_1.InternalError('assignment to a for-of binder');
                return `.${s.k} ${E(s.e)} ${B(s.body, [s.v, ...ctx])}`;
            case 'brk': return `.brk ${s.n}`;
            case 'cont': return `.cont ${s.n}`;
            case 'ret': return `.ret ${E(s.e)}`;
            case 'retP': return `.retP ${E(s.e)}`;
            case 'throw': return `.throw ${E(s.e)}`;
            case 'try':
                if (s.v.assigned)
                    throw new ir_1.InternalError('assignment to a catch binder');
                return `.try ${B(s.body)} ${B(s.handler, [s.v, ...ctx])} ${B(s.fin)}`;
            case 'tryFin': return `.tryFin ${B(s.body)} ${B(s.fin)}`;
            case 'caseOptS': {
                if (s.v.assigned)
                    throw new ir_1.InternalError('assignment to a caseOptS binder');
                const t = s.e.ty.t;
                return `.caseOptS (t := ${(0, ty_1.showTy)(t)}) ${E(s.e)} ${B(s.none)} ${B(s.some, [s.v, ...ctx])}`;
            }
            case 'caseUS': {
                const ts = s.e.ty.ts;
                const alts = s.alts.map(a => {
                    if (a.v.assigned)
                        throw new ir_1.InternalError('assignment to a caseUS binder');
                    return B(a.body, [a.v, ...ctx]);
                });
                return `.caseUS (ts := ${(0, ty_1.showTys)(ts)}) ${E(s.e)} altsS[${alts.join(', ')}]`;
            }
            case 'block': return `.block ${B(s.b)}`;
            case 'breakable': return `.breakable ${B(s.b)}`;
        }
    }
    emitBlock(b, ctx, ind) {
        const lines = [];
        let c = ctx;
        for (const it of b) {
            switch (it.k) {
                case 'stmt':
                    lines.push(`${ind}(.seq (${this.emitStmt(it.s, c, ind)})`);
                    break;
                case 'decl':
                    lines.push(`${ind}(.decl ${slot(it.v)} (${this.emitExpr(it.init, c)})`);
                    c = [it.v, ...c];
                    break;
                case 'await':
                    lines.push(`${ind}(.await ${slot(it.v)} (${this.emitExpr(it.init, c)})`);
                    c = [it.v, ...c];
                    break;
            }
        }
        lines.push(`${ind}.nil${')'.repeat(b.length)}`);
        return lines.join('\n');
    }
}
exports.Emitter = Emitter;
// ---------------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------------
// type abbreviations: large types that occur several times are named once (`abbrev`s are
// reducible, so elaboration and `simp` see through them)
function collectTyStrings(t, out) {
    switch (t.k) {
        case 'arr':
        case 'set':
        case 'opt':
        case 'promise':
        case 'box':
        case 'dict':
            collectTyStrings(t.t, out);
            break;
        case 'map':
            collectTyStrings(t.key, out);
            collectTyStrings(t.val, out);
            break;
        case 'tup':
        case 'union':
            t.ts.forEach(x => collectTyStrings(x, out));
            break;
        case 'record':
            t.fs.forEach(f => collectTyStrings(f.ty, out));
            break;
        case 'fn':
            t.args.forEach(x => collectTyStrings(x, out));
            collectTyStrings(t.ret, out);
            break;
        default: return;
    }
    out.add((0, ty_1.showTy)(t));
}
function abbrevName(str, used) {
    const m = str.match(/^\(\.(\w+)/);
    const kind = m ? m[1] : 'ty';
    const fields = [...str.matchAll(/"([A-Za-z_][A-Za-z0-9_]*)" :/g)].map(x => x[1]).slice(0, 3);
    let base = `ty_${kind}${fields.length ? '_' + fields.join('_') : ''}`;
    let n = base, i = 2;
    while (used.has(n))
        n = `${base}${i++}`;
    used.add(n);
    return n;
}
function countOcc(text, sub) {
    let n = 0, i = 0;
    while ((i = text.indexOf(sub, i)) >= 0) {
        n++;
        i += sub.length;
    }
    return n;
}
function abbreviateTypes(body, tys) {
    const cands = [...tys].filter(x => x.length >= 40).sort((a, b) => a.length - b.length);
    const defs = [];
    const used = new Set();
    let cur = cands.slice();
    for (let i = 0; i < cur.length; i++) {
        const str = cur[i];
        const occ = countOcc(body, str);
        if (occ < 2 && !(occ === 1 && str.length >= 160))
            continue;
        const name = abbrevName(str, used);
        defs.push(`abbrev ${name} : Ty := ${str}`);
        body = body.split(str).join(name);
        for (let j = i + 1; j < cur.length; j++)
            cur[j] = cur[j].split(str).join(name);
    }
    return { body, defs };
}
function programTys(p) {
    const out = new Set();
    const addVar = (v) => collectTyStrings(v.ty, out);
    const walkE = (e) => {
        collectTyStrings(e.ty, out);
        switch (e.k) {
            case 'prim':
            case 'builtin':
            case 'mkTup':
            case 'mkRec':
            case 'call':
            case 'extern':
                e.args.forEach(walkE);
                break;
            case 'app':
                walkE(e.f);
                e.args.forEach(walkE);
                break;
            case 'and':
            case 'or':
                walkE(e.a);
                walkE(e.b);
                break;
            case 'cond':
                walkE(e.c);
                walkE(e.a);
                walkE(e.b);
                break;
            case 'letE':
                addVar(e.v);
                walkE(e.init);
                walkE(e.body);
                break;
            case 'lam':
                e.params.forEach(addVar);
                walkB(e.body);
                break;
            case 'getTup':
            case 'getRec':
            case 'getField':
            case 'fold':
            case 'unfold':
            case 'some':
            case 'unwrap':
            case 'inj':
                walkE(e.e);
                break;
            case 'caseOpt':
                addVar(e.v);
                walkE(e.e);
                walkE(e.none);
                walkE(e.some);
                break;
            case 'caseU':
                walkE(e.e);
                e.alts.forEach(a => { addVar(a.v); walkE(a.body); });
                break;
            default: break;
        }
    };
    const walkS = (st) => {
        switch (st.k) {
            case 'expr':
            case 'ret':
            case 'retP':
            case 'throw':
            case 'assign':
            case 'gset':
                walkE(st.e);
                break;
            case 'setField':
                walkE(st.o);
                walkE(st.e);
                break;
            case 'ite':
                walkE(st.c);
                walkB(st.t);
                walkB(st.f);
                break;
            case 'while':
                walkE(st.c);
                walkB(st.body);
                break;
            case 'doWhile':
                walkB(st.body);
                walkE(st.c);
                break;
            case 'forLoop':
                walkE(st.c);
                walkB(st.body);
                walkB(st.step);
                break;
            case 'forOf':
            case 'forOfMap':
            case 'forOfSet':
            case 'forOfStr':
                addVar(st.v);
                walkE(st.e);
                walkB(st.body);
                break;
            case 'try':
                addVar(st.v);
                walkB(st.body);
                walkB(st.handler);
                walkB(st.fin);
                break;
            case 'tryFin':
                walkB(st.body);
                walkB(st.fin);
                break;
            case 'caseOptS':
                addVar(st.v);
                walkE(st.e);
                walkB(st.none);
                walkB(st.some);
                break;
            case 'caseUS':
                walkE(st.e);
                st.alts.forEach(a => { addVar(a.v); walkB(a.body); });
                break;
            case 'block':
            case 'breakable':
                walkB(st.b);
                break;
            default: break;
        }
    };
    const walkB = (b) => { for (const it of b) {
        if (it.k === 'stmt')
            walkS(it.s);
        else {
            addVar(it.v);
            walkE(it.init);
        }
    } };
    for (const f of p.funs) {
        f.params.forEach(addVar);
        collectTyStrings(f.ret, out);
        if (f.body)
            walkB(f.body);
    }
    for (const g of p.globals)
        collectTyStrings(g.ty, out);
    for (const t of p.aliases.values())
        collectTyStrings(t, out);
    for (const fs of p.classes.values())
        fs.forEach(f => collectTyStrings(f.ty, out));
    walkB(p.main);
    return out;
}
// ---------------------------------------------------------------------------------------
// Pieces of the output shared by the single-file and the modular output (`modular.ts`)
/** The type table `TT` and the field lists `«C».fields` of the classes. */
function typeTableLines(p) {
    const out = [];
    out.push('/-- Named (recursive) types and classes of the program (the IR refers to the');
    out.push('field lists `«C».fields` below directly; `fields` is kept as documentation). -/');
    out.push('abbrev TT : TypeTable where');
    if (p.aliases.size === 0)
        out.push('  alias := fun _ => .undef');
    else {
        out.push('  alias := fun n => match n with');
        for (const [n, t] of p.aliases)
            out.push(`    | ${(0, ty_1.leanStrLit)(n)} => ${(0, ty_1.showTy)(t)}`);
        out.push('    | _ => .undef');
    }
    if (p.classes.size === 0)
        out.push('  fields := fun _ => .nil');
    else {
        out.push('  fields := fun c => match c with');
        for (const [c, fs] of p.classes)
            out.push(`    | ${(0, ty_1.leanStrLit)(c)} => ${(0, ty_1.showFields)(fs)}`);
        out.push('    | _ => .nil');
    }
    out.push('');
    for (const [c, fs] of p.classes)
        out.push(`abbrev ${fieldsName(c)} : Fields := ${(0, ty_1.showFields)(fs)}`);
    if (p.classes.size)
        out.push('');
    return out;
}
/** The reference of a function with index `idx` in `Program.funs` (doc: its TypeScript signature). */
function funRefLines(p, f, idx) {
    const out = [];
    const doc = p.funDocs.get(f);
    if (doc)
        out.push(`/-- \`${doc.replace(/`/g, "'").replace(/-\//g, '- /')}\` -/`);
    out.push(`def ${q(f.leanName + 'Ref')} : FunRef ${(0, ty_1.showTys)(f.params.map(x => x.ty))} ${(0, ty_1.showTy)(f.ret)} := ⟨${idx}, ${(0, ty_1.leanStrLit)(f.name)}⟩`);
    return out;
}
/** The reference of a module-level variable stored in heap cell `idx`. */
function globalRefLine(g, idx) {
    return `def ${q(g.leanName)} : GRef ${(0, ty_1.showTy)(g.ty)} := ⟨${idx}, ${(0, ty_1.leanStrLit)(g.name)}⟩`;
}
/** The IR of a function. */
function funDefLines(em, f) {
    if (!f.body)
        throw new ir_1.InternalError(`function ${f.name} has no body`);
    return [
        `def ${q(f.leanName + 'Def')} : FunDef TT where`,
        `  name := ${(0, ty_1.leanStrLit)(f.name)}`,
        `  args := ${(0, ty_1.showTys)(f.params.map(x => x.ty))}`,
        `  ret := ${(0, ty_1.showTy)(f.ret)}`,
        `  lam := .${f.async ? 'async' : 'sync'} [${f.params.map(slot).join(', ')}] rfl`,
        em.emitBlock(f.body, [...f.params], '    '),
    ];
}
/** The module bodies. */
function mainBlockLines(em, p) {
    return ['def mainBlock : Block TT [] .undef :=', em.emitBlock(p.main, [], '  ')];
}
/** The signature of an external function called by `extern` nodes, named for stating oracle answers. */
function externAbbrevLine(name, x) {
    return `abbrev ${q(name)} : ExtFun := ⟨${(0, ty_1.leanStrLit)(x.name)}, [${x.args.map(ty_1.showTy).join(', ')}], ${(0, ty_1.showTy)(x.ret)}⟩`;
}
/** `[t₁, …]`: the argument types of a function as the index of its argument values (`Vals TT …`). */
function argList(f) {
    return `[${f.params.map(x => (0, ty_1.showTy)(x.ty)).join(', ')}]`;
}
function emitProgram(p, opts = {}) {
    const em = new Emitter();
    const out = [];
    out.push(`/- Generated by the StrictTS frontend from ${p.sources.join(', ')}. Do not edit. -/`);
    out.push('import StrictTS.Frontend.Prelude');
    out.push('set_option maxRecDepth 100000');
    out.push('open StrictTS StrictTS.Frontend');
    out.push('');
    out.push(`namespace ${p.namespace}`);
    out.push('');
    let headerLen = out.length;
    out.push(...typeTableLines(p));
    for (const f of p.funs)
        out.push(...funRefLines(p, f, f.idx));
    if (p.funs.length)
        out.push('');
    for (const g of p.globals)
        out.push(globalRefLine(g, g.idx));
    if (p.globals.length)
        out.push('');
    for (const f of p.funs) {
        out.push(...funDefLines(em, f));
        out.push('');
    }
    out.push(...mainBlockLines(em, p));
    out.push('');
    out.push('def program : Program TT where');
    out.push(`  funs := [${p.funs.map(f => q(f.leanName + 'Def')).join(', ')}]`);
    out.push(`  globals := [${p.globals.map(g => (0, ty_1.showTy)(g.ty)).join(', ')}]`);
    out.push('  main := mainBlock');
    out.push('');
    if (em.externs.size) {
        out.splice(2, 0, 'import StrictTS.Proof.Extern');
        headerLen++;
        out.push('/-! External functions called by the program, with the signatures of its `extern` nodes (for');
        out.push('stating oracle answers: `w.answer «f_ext» vs n = .ok v`). -/');
        out.push('');
        const seen = new Map();
        for (const x of em.externs.values()) {
            const k = (seen.get(x.name) ?? 0) + 1;
            seen.set(x.name, k);
            out.push(externAbbrevLine(`${x.name}_ext${k > 1 ? k : ''}`, x));
        }
        out.push('');
    }
    if (p.funs.length) {
        out.push('/-! Call-unfolding lemmas: a call of a top-level function runs its body. -/');
        out.push('');
    }
    for (const f of p.funs) {
        out.push(`theorem ${q(f.leanName + '_call')} (I : Impl) (vs : Vals TT ${argList(f)}) :`);
        out.push(`    callFun I program ${q(f.leanName + 'Ref')} vs = applyLam I program ${q(f.leanName + 'Def')}.lam .nil vs := by`);
        out.push('  rw [callFun.eq_1]; rfl');
        out.push('');
    }
    out.push(`end ${p.namespace}`);
    if (opts.eval) {
        out.push('');
        out.push(`#eval runMain ${p.namespace}.program ${(0, ty_1.leanStrLit)(p.namespace)}`);
    }
    out.push('');
    if (!opts.abbreviate)
        return out.join('\n');
    // (optional: measured slower to elaborate than the inline types, see report)
    const header = out.slice(0, headerLen).join('\n');
    const { body, defs } = abbreviateTypes(out.slice(headerLen).join('\n'), programTys(p));
    const abbrevs = defs.length ? `/-! Type abbreviations. -/\n\n${defs.join('\n')}\n\n` : '';
    return `${header}\n${abbrevs}${body}`;
}

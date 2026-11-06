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
// Partial programs (`--coverage --emit-lean OUT.lean`): the IR of a set of functions of a
// project that is not translatable as a whole. The given units (top-level functions, methods,
// constructors, accessors, module-level arrows and handler arrows) are translated with the
// normal (non-coverage) translator; callees, classes and module-level variables they need are
// translated on demand. A function whose body, or the body of anything it calls, fails to
// translate is left out; so is the initialiser of a module variable that fails or calls a left-out
// function (the variable is then uninitialised: reading it throws, as in its temporal dead zone).
const ts = __importStar(require("typescript"));
const core_1 = require("./core");
const ty_1 = require("./ty");
const P = core_1.Translator.prototype;
function refs(b, funs, globals) {
    const e = (x) => {
        switch (x.k) {
            case 'gget':
                globals.add(x.g);
                return;
            case 'call':
                funs.add(x.f);
                x.args.forEach(e);
                return;
            case 'funVal':
                funs.add(x.f);
                return;
            case 'prim':
            case 'builtin':
            case 'mkTup':
            case 'mkRec':
            case 'extern':
                x.args.forEach(e);
                return;
            case 'app':
                e(x.f);
                x.args.forEach(e);
                return;
            case 'and':
            case 'or':
                e(x.a);
                e(x.b);
                return;
            case 'cond':
                e(x.c);
                e(x.a);
                e(x.b);
                return;
            case 'letE':
                e(x.init);
                e(x.body);
                return;
            case 'lam':
                blk(x.body);
                return;
            case 'getTup':
            case 'getRec':
            case 'getField':
            case 'fold':
            case 'unfold':
            case 'some':
            case 'unwrap':
            case 'inj':
                e(x.e);
                return;
            case 'caseOpt':
                e(x.e);
                e(x.none);
                e(x.some);
                return;
            case 'caseU':
                e(x.e);
                x.alts.forEach(a => e(a.body));
                return;
            default: return;
        }
    };
    const s = (x) => {
        switch (x.k) {
            case 'expr':
            case 'ret':
            case 'retP':
            case 'throw':
                e(x.e);
                return;
            case 'assign':
                e(x.e);
                return;
            case 'gset':
                globals.add(x.g);
                e(x.e);
                return;
            case 'setField':
                e(x.o);
                e(x.e);
                return;
            case 'ite':
                e(x.c);
                blk(x.t);
                blk(x.f);
                return;
            case 'while':
            case 'doWhile':
                e(x.c);
                blk(x.body);
                return;
            case 'forLoop':
                e(x.c);
                blk(x.body);
                blk(x.step);
                return;
            case 'forOf':
            case 'forOfMap':
            case 'forOfSet':
            case 'forOfStr':
                e(x.e);
                blk(x.body);
                return;
            case 'try':
                blk(x.body);
                blk(x.handler);
                blk(x.fin);
                return;
            case 'tryFin':
                blk(x.body);
                blk(x.fin);
                return;
            case 'caseOptS':
                e(x.e);
                blk(x.none);
                blk(x.some);
                return;
            case 'caseUS':
                e(x.e);
                x.alts.forEach(a => blk(a.body));
                return;
            case 'block':
            case 'breakable':
                blk(x.b);
                return;
            default: return;
        }
    };
    const blk = (xs) => {
        for (const it of xs) {
            if (it.k === 'stmt')
                s(it.s);
            else
                e(it.init);
        }
    };
    blk(b);
}
/** The instance of a generic function's type parameters (`--emit-generics number`, the convention
 * of tools/public/mono.js): unconstrained := number, `extends PropertyKey` / `extends string` :=
 * string, `extends number` := number; another constraint: the reason it is not instantiated. */
function genericInstance(tr, tps) {
    const subst = new Map(), inst = {};
    for (const tp of tps) {
        const c = tp.constraint ? tp.constraint.getText().replace(/\s+/g, ' ') : undefined;
        const t = c === undefined ? 'number' : { PropertyKey: 'string', string: 'string', number: 'number' }[c];
        if (!t)
            return `type parameter ${tp.name.text} extends ${c}`;
        subst.set(tr.checker.getTypeAtLocation(tp), t === 'string' ? ty_1.T.str : ty_1.T.num);
        inst[tp.name.text] = t;
    }
    return { subst, inst };
}
P.translatePartial = function (units, generics) {
    this.unitNames ??= new Map();
    this.genericUnits ??= new Map();
    const files = this.files;
    this.analysis.run(files);
    this.analyzeIdentity(files);
    const failures = [];
    const attempt = (node, what, f) => {
        const before = this.diags.count;
        let ok = false;
        this.guard(node, () => { f(); ok = true; });
        if (!ok) {
            const d = this.diags.count > before ? this.diags.list[this.diags.count - 1] : undefined;
            failures.push(`${what}: ${d ? `${d.file}:${d.line}:${d.col} [${d.rule}] ${d.msg}` : '(as above)'}`);
        }
        return ok;
    };
    // module-level variables (not regex constants or arrows, which are not values here)
    const initOf = [];
    for (const sf of files) {
        for (const st of sf.statements) {
            if (!ts.isVariableStatement(st))
                continue;
            const sets = [];
            for (const d of st.declarationList.declarations) {
                if (this.isRegexConst(d) || this.liftedArrow(d))
                    continue;
                const ids = [];
                const collect = (b) => { if (ts.isIdentifier(b))
                    ids.push(b);
                else
                    b.elements.forEach(el => { if (!ts.isOmittedExpression(el))
                        collect(el.name); }); };
                collect(d.name);
                for (const id of ids) {
                    attempt(id, `module-level ${id.text}`, () => {
                        const sym = this.symAt(id);
                        const g = this.newGlobal(id.text, this.types.map(this.checker.getTypeOfSymbol(sym), new Map(), id));
                        this.globalOf.set(sym, g);
                        sets.push(g);
                    });
                }
            }
            if (sets.length)
                initOf.push({ st, sets });
        }
    }
    // the units (a generic function: left out, or with `generics` at one instance, the one a call
    // site with these type arguments makes)
    const unitFun = new Map();
    const instantiate = (u, decl) => {
        const tps = decl.typeParameters ?? [];
        if (!tps.length)
            return this.funInfoFor(decl, new Map(), decl);
        if (!generics)
            return undefined;
        const g = genericInstance(this, tps);
        if (typeof g === 'string') {
            failures.push(`${u.name}: generic, not instantiated: ${g}`);
            return undefined;
        }
        const f = this.funInfoFor(decl, g.subst, decl);
        this.genericUnits.set(f, { name: u.name, kind: u.kind, inst: g.inst });
        return f;
    };
    for (const u of units) {
        attempt(u.node, u.name, () => {
            const n = u.node;
            if (u.kind === 'function') {
                const f = instantiate(u, n);
                if (f)
                    unitFun.set(u, f);
            }
            else if (u.kind === 'arrow' || u.kind === 'handler') {
                const a = n;
                if (a.typeParameters?.length && !generics)
                    return;
                if (!this.unitNames.has(a))
                    this.unitNames.set(a, u.name.replace(/[^A-Za-z0-9_]/g, '_'));
                const f = instantiate(u, a);
                if (f)
                    unitFun.set(u, f);
            }
            else if (u.cls) {
                if (u.cls.typeParameters?.length)
                    return;
                const ci = this.types.classInst(this.checker.getTypeAtLocation(u.cls), new Map(), u.cls);
                const m = n;
                const name = m.name && (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name) || ts.isStringLiteral(m.name)) ? m.name.text : '';
                let f;
                if (u.kind === 'constructor')
                    f = this.classCtor(ci, u.cls);
                else if (u.kind === 'method')
                    f = u.isStatic ? this.classStatic(ci, name, m) : this.classMember(ci, name, 'method', m);
                else if (u.kind === 'accessor' && !u.isStatic)
                    f = this.classMember(ci, name, ts.isGetAccessorDeclaration(m) ? 'getter' : 'setter', m);
                if (f)
                    unitFun.set(u, f);
            }
        });
    }
    // initialisers of module-level variables, one statement at a time
    const main = new core_1.FnCtx(null, 'main', false, ty_1.T.undef, new Map(), files[0]);
    const inits = [];
    for (const { st, sets } of initOf) {
        const items = [];
        if (attempt(st, `initialiser of ${sets.map(g => g.name).join(', ')}`, () => this.lowerStmt(st, main, items)))
            inits.push({ items, sets });
    }
    // bodies (instantiations may enqueue more)
    for (let i = 0; i < this.queue.length; i++) {
        const inst = this.queue[i];
        attempt(inst.decl, inst.info.name, () => this.lowerFunBody(inst));
    }
    // cells of top-level functions compared by identity: set first, like hoisted declarations
    this.fnBoxes.forEach((g, f) => {
        inits.unshift({ items: this.fnBoxInits.filter(it => it.k === 'stmt' && it.s.k === 'gset' && it.s.g === g), sets: [g] });
        void f;
    });
    // left out: failed bodies, and everything that needs them
    const bad = new Set(this.funs.filter(f => !f.body));
    const funsFailed = bad.size;
    const funRefs = new Map();
    const globRefs = new Map();
    for (const f of this.funs) {
        if (!f.body)
            continue;
        const fs = new Set(), gs = new Set();
        refs(f.body, fs, gs);
        funRefs.set(f, fs);
        globRefs.set(f, gs);
    }
    for (let changed = true; changed;) {
        changed = false;
        for (const [f, fs] of funRefs)
            if (!bad.has(f) && [...fs].some(x => bad.has(x))) {
                bad.add(f);
                changed = true;
            }
    }
    // initialisers that call left-out functions are dropped
    const goodInits = inits.filter(ini => {
        const fs = new Set(), gs = new Set();
        refs(ini.items, fs, gs);
        return ![...fs].some(x => bad.has(x));
    });
    // what the kept units need: functions, globals, and the initialisers of those globals
    const keepF = new Set(), keepG = new Set();
    const work = [...unitFun.values()].filter(f => !bad.has(f));
    const keepInit = new Set();
    const addGlobal = (g) => {
        if (keepG.has(g))
            return;
        keepG.add(g);
        goodInits.forEach((ini, i) => {
            if (keepInit.has(i) || !ini.sets.includes(g))
                return;
            keepInit.add(i);
            const fs = new Set(), gs = new Set();
            refs(ini.items, fs, gs);
            ini.sets.forEach(x => keepG.add(x));
            fs.forEach(f => work.push(f));
            gs.forEach(addGlobal);
        });
    };
    while (work.length) {
        const f = work.pop();
        if (keepF.has(f))
            continue;
        keepF.add(f);
        funRefs.get(f)?.forEach(x => work.push(x));
        globRefs.get(f)?.forEach(addGlobal);
    }
    const funs = this.funs.filter(f => keepF.has(f));
    const globals = this.globals.filter(g => keepG.has(g));
    funs.forEach((f, i) => { f.idx = i; });
    globals.forEach((g, i) => { g.idx = i; });
    const mainItems = [];
    goodInits.forEach((ini, i) => { if (keepInit.has(i))
        mainItems.push(...ini.items); });
    const initialised = new Set();
    goodInits.forEach((ini, i) => { if (keepInit.has(i))
        ini.sets.forEach(g => initialised.add(g)); });
    const unitsEmitted = [...unitFun.values()].filter(f => keepF.has(f)).length;
    const ir = {
        namespace: '', sources: files.map(f => f.fileName), aliases: this.types.aliases, classes: this.types.classFields,
        funs, globals, main: mainItems, funDocs: this.funDocs,
    };
    return {
        ir,
        stats: {
            units: units.length, unitsEmitted, funs: funs.length, funsFailed, funsDropped: bad.size - funsFailed,
            globals: globals.length, globalsUninitialised: globals.filter(g => !initialised.has(g)).length, failures,
        },
    };
};

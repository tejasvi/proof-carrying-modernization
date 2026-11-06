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
exports.TACTIC_PRELUDE = exports.OBS_SCRIPT = exports.DEFAULT_SCRIPT_WF = exports.DEFAULT_SCRIPT = void 0;
exports.translateSlice = translateSlice;
exports.recursiveBases = recursiveBases;
exports.parseLTy = parseLTy;
exports.splitTys = splitTys;
exports.destructPattern = destructPattern;
exports.theoremFor = theoremFor;
exports.aliasNewTypes = aliasNewTypes;
exports.runLeanBatch = runLeanBatch;
exports.leanAvailable = leanAvailable;
// Lean stage: translation of slices (through the frontend's `translate`), generated Lean
// files with confirmation runs (`#eval runMain`) and equivalence theorems, batched Lean runs
// and the parsing of their results.
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const util_1 = require("./util");
// eslint-disable-next-line @typescript-eslint/no-var-requires
const frontend = require(path.join(util_1.ROOT, 'frontend', 'dist', 'index.js'));
function translateSlice(dir, entry, ns, withEval) {
    let r;
    try {
        r = frontend.translate({ files: [path.join(dir, entry)], namespace: ns, eval: withEval, cwd: dir });
    }
    catch (e) {
        r = { ok: false, diagnostics: `internal error: ${e.message}`, count: 1 };
    }
    const t = { ok: r.ok, ns, body: '', rules: [], diagnostics: r.diagnostics, refs: new Map(), callArgs: new Map(), defs: [], calls: new Map(), moduleState: '' };
    if (!r.ok || !r.lean) {
        const rules = new Set();
        for (const m of r.diagnostics.matchAll(/\[([a-z0-9-]+)\]/g))
            rules.add(m[1]);
        if (/internal error/.test(r.diagnostics))
            rules.add('translator-internal-error');
        t.rules = [...rules];
        return t;
    }
    const text = r.lean;
    t.body = text.slice(text.indexOf('\nnamespace ') + 1);
    for (const m of text.matchAll(/^def «(.+?)Ref» : FunRef (tys\[.*?\]) (.+?) := ⟨\d+, "(.+?)"⟩$/gm))
        t.refs.set(m[4], { base: m[1], args: m[2], ret: m[3] });
    for (const m of text.matchAll(/^theorem «(.+?)_call» \(I : Impl\) \(vs : Vals TT (\[.*\])\) :$/gm))
        t.callArgs.set(m[1], m[2]);
    for (const m of text.matchAll(/^def «(.+?)Def» : FunDef TT where$/gm))
        t.defs.push(m[1]);
    // call graph
    const defStarts = [...text.matchAll(/^def «(.+?)Def» : FunDef TT where$/gm)];
    defStarts.forEach((m, i) => {
        const end = i + 1 < defStarts.length ? defStarts[i + 1].index : text.indexOf('\ndef mainBlock');
        const body = text.slice(m.index, end);
        const cs = new Set();
        for (const c of body.matchAll(/«(.+?)Ref»/g))
            cs.add(c[1]);
        t.calls.set(m[1], cs);
    });
    const gi = text.indexOf('\ndef «g_');
    const mb = text.indexOf('\ndef mainBlock');
    const pr = text.indexOf('\ndef program');
    // the program ends at the lemma sections, or at the end of the namespace when it has none (no
    // top-level functions, no externs): the `end <ns>` line names the version and is not state
    const ls = text.indexOf('\n/-!', pr);
    const pe = ls >= 0 ? ls : text.indexOf(`\nend ${ns}`, pr);
    const strip = (s) => s.split(ns + '.').join('');
    t.moduleState = strip((gi >= 0 ? text.slice(gi, text.indexOf('\n\n', gi)) : '') + text.slice(mb, pr) + text.slice(text.indexOf('  globals :=', pr), pe));
    return t;
}
/** Functions on a call cycle (their call lemmas must not be used as rewrite rules). */
function recursiveBases(t) {
    const rec = new Set();
    for (const [b] of t.calls) {
        const seen = new Set();
        const stack = [...(t.calls.get(b) ?? [])];
        while (stack.length) {
            const x = stack.pop();
            if (x === b) {
                rec.add(b);
                break;
            }
            if (seen.has(x))
                continue;
            seen.add(x);
            stack.push(...(t.calls.get(x) ?? []));
        }
    }
    return rec;
}
function parseLTy(src) {
    let i = 0;
    const ws = () => { while (i < src.length && /\s/.test(src[i]))
        i++; };
    const ident = () => { const m = /^[A-Za-z_][A-Za-z0-9_]*/.exec(src.slice(i)); if (!m)
        throw new Error(`type syntax at ${i}: ${src.slice(i, i + 20)}`); i += m[0].length; return m[0]; };
    const str = () => { ws(); if (src[i] !== '"')
        throw new Error('string expected'); let j = i + 1; while (src[j] !== '"') {
        if (src[j] === '\\')
            j++;
        j++;
    } const v = JSON.parse(src.slice(i, j + 1)); i = j + 1; return v; };
    const list = (open, item) => {
        ws();
        if (!src.startsWith(open, i))
            throw new Error(`${open} expected`);
        i += open.length;
        const out = [];
        ws();
        if (src[i] === ']') {
            i++;
            return out;
        }
        for (;;) {
            out.push(item());
            ws();
            if (src[i] === ',') {
                i++;
                continue;
            }
            if (src[i] === ']') {
                i++;
                return out;
            }
            throw new Error('list syntax');
        }
    };
    const ty = () => {
        ws();
        const start = i;
        if (src[i] === '(') {
            i++;
            ws();
            const t = ty();
            ws();
            if (src[i] !== ')')
                throw new Error(') expected');
            i++;
            return { ...t, text: src.slice(start, i) };
        }
        if (src[i] !== '.')
            throw new Error(`type expected at ${i}: ${src.slice(i, i + 20)}`);
        i++;
        const k = ident();
        const args = [];
        let names;
        const atom = () => { ws(); return i < src.length && (src[i] === '.' || src[i] === '(') && !src.startsWith('..', i); };
        switch (k) {
            case 'arr':
            case 'opt':
            case 'set':
            case 'promise':
            case 'box':
                args.push(ty());
                break;
            case 'map':
                args.push(ty(), ty());
                break;
            case 'tup':
            case 'union':
                ws();
                args.push(...list('tys[', ty));
                break;
            case 'fn':
                ws();
                args.push(...list('tys[', ty), ty());
                break;
            case 'record': {
                names = [];
                const fs = list('flds[', () => { const n = str(); ws(); if (src[i] !== ':')
                    throw new Error(': expected'); i++; return { n, t: ty() }; });
                for (const f of fs) {
                    names.push(f.n);
                    args.push(f.t);
                }
                break;
            }
            case 'enum':
                names = list('[', str);
                break;
            case 'obj':
            case 'named':
                names = [str()];
                break;
            case 'tarr':
                ws();
                ident();
                break;
            default:
                void atom;
                break;
        }
        return { k, args, names, text: src.slice(start, i) };
    };
    const t = ty();
    return t;
}
const SINGLE = new Set(['num', 'bigint', 'bool', 'str', 'err', 'arr', 'tarr', 'map', 'set', 'obj', 'promise', 'box', 'enum', 'undef', 'null']);
/** rcases pattern for one value: single-constructor types expose their payload, records and
 * tuples their fields, optionals split into none/some; at most `budget` cases in total. */
function patFor(t, name, budget) {
    if (t.k === 'undef' || t.k === 'null')
        return '⟨⟩';
    if (SINGLE.has(t.k))
        return `⟨${name}⟩`;
    if (t.k === 'record' || t.k === 'tup')
        return `⟨${valsPat(t.args, name, budget)}⟩`;
    if (t.k === 'opt' && budget.cases * 2 <= 16) {
        budget.cases *= 2;
        return `_ | ⟨${patFor(t.args[0], name, budget)}⟩`;
    }
    return name;
}
function valsPat(ts, name, budget) {
    let pat = '_ | _';
    for (let i = ts.length - 1; i >= 0; i--)
        pat = `_ | ⟨${patFor(ts[i], `${name}_${i}`, budget)}, ${pat}⟩`;
    return pat;
}
/** Split a Lean list literal of types at top-level commas. */
function splitTys(list) {
    const s = list.trim().replace(/^\[/, '').replace(/\]$/, '');
    const out = [];
    let depth = 0, cur = '', inStr = false;
    for (const ch of s) {
        if (ch === '"')
            inStr = !inStr;
        if (!inStr) {
            if ('([{⟨'.includes(ch))
                depth++;
            if (')]}⟩'.includes(ch))
                depth--;
        }
        if (ch === ',' && depth === 0 && !inStr) {
            out.push(cur.trim());
            cur = '';
        }
        else
            cur += ch;
    }
    if (cur.trim())
        out.push(cur.trim());
    return out;
}
/** rcases pattern for `vs : Vals TT [t0, …]`: `_ | ⟨p0, _ | ⟨p1, _ | _⟩⟩` (impossible cases vanish). */
function destructPattern(argList) {
    const budget = { cases: 1 };
    let tys;
    try {
        tys = splitTys(argList).map(parseLTy);
    }
    catch {
        return valsPat(splitTys(argList).map(() => ({ k: '?', args: [], text: '' })), 'x', budget);
    }
    return valsPat(tys, 'x', budget);
}
function parseMessages(text) {
    const out = [];
    let cur = null;
    for (const l of text.split('\n')) {
        const m = l.match(/^.+?\.lean:(\d+):(\d+): (error|warning|info): ?(.*)$/);
        if (m) {
            if (cur)
                out.push(cur);
            cur = { line: Number(m[1]), kind: m[3], msg: m[4] };
            continue;
        }
        if (/^'equiv_|^=====STRICTTS/.test(l)) {
            if (cur)
                out.push(cur);
            cur = null;
            continue;
        }
        if (cur)
            cur.msg += '\n' + l;
    }
    if (cur)
        out.push(cur);
    return out;
}
/** Body of both default scripts. Argument values are taken apart and enum values split into their
members (`ts_enum_cases`: the narrowing of a string-literal union then evaluates); argument cells
are split (present or dangling); `ts_auto` (the automatic recipe of StrictTS.Proof.Auto) is tried
first; dangling cells make both versions panic at their first read; otherwise loop and callback
summaries are interleaved with case splits on conditions and heap reads, then closers. A goal
`ts_auto` leaves after a case split is retried with the case's equations substituted
(`subst_vars`: e.g. an array that is the empty literal also in the bounds of a fold). A number
argument validated as an integer in a small range is split into its values, and each case runs
concretely (`dt_int_cases`, `dt_eval_calls`, `dt_eval_loops` in lean/DiffPrelude.lean). The cheapest
alternative comes first (unfold, then `rfl` or `simp`): the alternatives share one heartbeat budget, and
pairs whose versions agree after unfolding (e.g. `x == null` against `x === undefined` at a type
without `null`) used to time out in the costlier ones. */
const BODY = `ts_destruct
ts_enum_cases
ts_cells
all_goals first
  | (dt_unfold; first | rfl | (simp [ts_sym, *]; done) | (dt_typeof_cases; all_goals first | rfl | (simp [ts_sym, *]; done) | (simp (config := { decide := true }) [ts_sym, *]; done)))
  | (dt_int_guard; dt_unfold; dt_int_cases; dt_eval_calls; all_goals dt_eval_loops)
  | (ts_auto [Array.size_push]; all_goals (subst_vars; first | (simp [ts_sym, *]; done) | (simp_all [ts_sym]; done)))
  | (dt_unfold; first | rfl | (simp [ts_sym, *]; done) | (simp [ts_sym, *, F64.min_comm, F64.max_comm]; done))
  | (dt_auto
     all_goals (repeat' (first | ts_summarize | ts_callbacks | dt_ite_split | dt_heap_split))
     all_goals first | rfl | dt_contra | ts_int32 | dt_int32 | (simp [ts_sym, *]; done) | grind | omega | (simp_all; done) | (simp_all [dt_size_le_lit, dt_size_lt_lit, dt_size_le_ofNat, dt_size_lt_ofNat, dt_pop_small]; done) | fail "difftool: residual goal")
  | (dt_unfold
     all_goals (repeat' (first | dt_ite_split | dt_heap_split))
     all_goals first | rfl | dt_contra | ts_int32 | dt_int32 | (simp [ts_sym, *]; done) | grind | omega | (simp_all; done) | (simp_all [dt_size_le_lit, dt_size_lt_lit, dt_size_le_ofNat, dt_size_lt_ofNat, dt_pop_small]; done) | fail "difftool: residual goal")`;
/** Default script for the statement over every argument list and world. */
exports.DEFAULT_SCRIPT = `intro vs w
${BODY}`;
/** Default script for the statement over worlds in which the argument arrays (maps, sets) are
allocated cells (hypotheses \`hw : w.heap.get? (.arr T, a) = some c\` and \`hn : a < w.next\`), which
summaries of loops that allocate (push into a fresh array, map, filter) need. */
exports.DEFAULT_SCRIPT_WF = BODY;
/** Script of the observational statement (\`_obs\`): the default body, where \`ts_auto\` also reads an
argument cell through the callee's allocations (\`dtFreshRead\` in lean/DiffPrelude.lean: \`omega\`
proves the argument's address below \`w.next\` different from \`w.next + k\`) and converts positions
that \`omega\` bounds by 2^53 (\`dtToIntOfNat\`, e.g. \`s.charAt(i)\` in a loop over a string), and the
goals it leaves get one more closer: the fold lemmas of a reversed string (\`foldrFstUnit\`,
\`foldr_val_str\`, \`foldl_append_eq_foldr\` in StrictTS/Proof/LibLemmas.lean: \`join("")\` of the
reversed parts against a backwards \`charAt\` loop). */
exports.OBS_SCRIPT = BODY
    .replace('ts_auto [Array.size_push]', 'ts_auto [Array.size_push, dtFreshRead, dtToIntOfNat]')
    .replace('| (simp_all [ts_sym]; done)))', '| (simp_all [ts_sym]; done) | (simp_all [ts_sym, foldrFstUnit, foldr_val_str, foldl_append_eq_foldr, Function.comp_def]; done)))');
/** Types whose values hold no heap reference: numbers, strings, booleans, errors, enums, and
tuples, records, optionals and unions of these. */
function refFree(t) {
    if (['num', 'bigint', 'bool', 'str', 'err', 'enum', 'undef', 'null'].includes(t.k))
        return true;
    if (['tup', 'record', 'opt', 'union'].includes(t.k))
        return t.args.every(refFree);
    return false;
}
/** Constructs that schedule asynchronous work (promises, jobs, timers): the observational
relations do not compare the job queue, the timers or unhandled rejections. */
const ASYNC_RE = /\.(async|externAsync|prom[A-Z]\w*|queueMicrotask|setTimeout|await|retP)\b/;
/** Tactics and lemmas included after the imports of every generated Lean file (lean/DiffPrelude.lean). */
exports.TACTIC_PRELUDE = fs.readFileSync(path.join(__dirname, '..', 'lean', 'DiffPrelude.lean'), 'utf8');
function fillScript(script, j, o, n, argsO, defs) {
    return script
        .split('{OLDCALL}').join(`${j.oldT.ns}.«${o.base}_call»`)
        .split('{NEWCALL}').join(`${j.newT.ns}.«${n.base}_call»`)
        .split('{OLD}').join(j.oldT.ns).split('{NEW}').join(j.newT.ns)
        .split('{F}').join(o.base)
        .split('{DESTRUCT}').join(destructPattern(argsO))
        .split('{DEFS}').join(defs.join(', '))
        .split('\n').map(l => '  ' + l).join('\n');
}
function theoremFor(j) {
    const o = j.oldT.refs.get(j.target), n = j.newT.refs.get(j.targetNew ?? j.target);
    if (!o || !n)
        return { error: `target ${!o ? j.target : j.targetNew ?? j.target} not found in the translation` };
    const argsO = j.oldT.callArgs.get(o.base), argsN = j.newT.callArgs.get(n.base);
    if (!argsO || argsO !== argsN || o.ret !== n.ret)
        return { error: `translated signatures differ (${argsO} ${o.ret} vs ${argsN} ${n.ret})` };
    const recO = recursiveBases(j.oldT), recN = recursiveBases(j.newT);
    const defs = [];
    for (const [t, rec] of [[j.oldT, recO], [j.newT, recN]]) {
        for (const d of t.defs) {
            defs.push(`${t.ns}.«${d}Def»`);
            const isTarget = d === (t === j.oldT ? o.base : n.base);
            if (!isTarget && !rec.has(d))
                defs.push(`${t.ns}.«${d}_call»`);
        }
    }
    const TT = `${j.oldT.ns}.TT`;
    const call = (t, base, vs) => `JS.exec (callFun I ${t.ns}.program ${t.ns}.«${base}Ref» ${vs}) w`;
    const main = `set_option maxHeartbeats ${j.heartbeats} in
theorem equiv_${j.id} (I : Impl) : ∀ (vs : Vals ${TT} ${argsO}) (w : World ${TT}),
    ${call(j.oldT, o.base, 'vs')} =
      ${call(j.newT, n.base, 'vs')} := by
${fillScript(j.script, j, o, n, argsO, defs)}

#print axioms equiv_${j.id}
`;
    // the statement where the old version does not panic (`_np`, statement old-no-panic, WEAKER than
    // equality): the two runs are equal, or the old version's run panics (a read that the TypeScript types
    // exclude, `x!` on undefined, ...), where the new version may do anything
    const np = `set_option maxHeartbeats ${j.heartbeats} in
theorem equiv_${j.id}_np (I : Impl) : ∀ (vs : Vals ${TT} ${argsO}) (w : World ${TT}),
    ${call(j.oldT, o.base, 'vs')} =
      ${call(j.newT, n.base, 'vs')} ∨
    ∃ (s : String) (w' : World ${TT}), ${call(j.oldT, o.base, 'vs')} = some (.error (.panic s), w') := by
${fillScript(j.script, j, o, n, argsO, defs)}

#print axioms equiv_${j.id}_np
`;
    // the same statement for worlds in which the argument arrays, maps and sets are allocated
    // (`_wf`, statement allocated-arguments) and, when the function takes strings, also for string
    // arguments within the ECMAScript maximum length (`_wfs`, allocated-arguments-strlen)
    let tys;
    try {
        tys = splitTys(argsO).map(parseLTy);
    }
    catch {
        return { main, np };
    }
    // field lists of the classes (`abbrev «C».fields : Fields := flds[…]` in the old translation)
    const classFields = (c) => {
        const m = new RegExp(`^abbrev «${c.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}»\\.fields : Fields := flds\\[(.*)\\]$`, 'm').exec(j.oldT.body);
        if (!m)
            return undefined;
        try {
            return parseLTy(`.record flds[${m[1]}]`).args;
        }
        catch {
            return undefined;
        }
    };
    const variant = (strlen, objects = false, obs) => {
        const binders = [], hyps = [], vals = [];
        let refs = 0, strs = 0, objs = 0;
        tys.forEach((t, i) => {
            const fields = objects && t.k === 'obj' ? classFields(t.names[0]) : undefined;
            if (fields) {
                // an allocated object whose fields are initialised; its array fields are allocated cells
                // with room for one more element (JavaScript arrays stay below 2^32 elements)
                objs++;
                binders.push(`(a${i} : Nat)`);
                const fv = fields.map((f, k) => {
                    if (f.k === 'arr') {
                        binders.push(`(b${i}_${k} : Nat) (c${i}_${k} : Array (Val ${TT} ${f.args[0].text}))`);
                        hyps.push(`(hw${i}_${k} : w.heap.get? (.arr ${f.args[0].text}, b${i}_${k}) = some c${i}_${k}) (hn${i}_${k} : b${i}_${k} < w.next) (hs${i}_${k} : c${i}_${k}.size < 2 ^ 32 - 1)`);
                        return `(.arr b${i}_${k})`;
                    }
                    binders.push(`(f${i}_${k} : Val ${TT} ${f.text})`);
                    return `f${i}_${k}`;
                });
                const ovals = fv.reduceRight((acc, v) => `(.cons (some ${v}) ${acc})`, '.nil');
                hyps.push(`(ho${i} : w.heap.get? (.obj "${t.names[0]}" ${j.oldT.ns}.«${t.names[0]}».fields.types, a${i}) = some ${ovals}) (hno${i} : a${i} < w.next)`);
                vals.push(`(.obj a${i})`);
                return;
            }
            const cell = t.k === 'arr' ? `Array (Val ${TT} ${t.args[0].text})` :
                t.k === 'map' ? `JSMap (Val ${TT} ${t.args[0].text}) (Val ${TT} ${t.args[1].text})` :
                    t.k === 'set' ? `JSMap (Val ${TT} ${t.args[0].text}) Unit` : null;
            if (cell) {
                refs++;
                const kind = t.k === 'arr' ? `.arr ${t.args[0].text}` : t.k === 'map' ? `.map ${t.args[0].text} ${t.args[1].text}` : `.set ${t.args[0].text}`;
                binders.push(`(a${i} : Nat) (c${i} : ${cell})`);
                // JavaScript arrays have fewer than 2^32 elements (counted loops index them with doubles)
                hyps.push(`(hw${i} : w.heap.get? (${kind}, a${i}) = some c${i}) (hn${i} : a${i} < w.next)` + (t.k === 'arr' ? ` (hs${i} : c${i}.size < 2 ^ 32)` : ''));
                vals.push(`(.${t.k} a${i})`);
            }
            else if (strlen && t.k === 'str') {
                strs++;
                binders.push(`(s${i} : JSStr)`);
                // ECMA-262 6.1.4: a String has at most 2^53 - 1 code units; the model has no bound, and a
                // longer length would round when it becomes a number
                hyps.push(`(hl${i} : s${i}.length < 2 ^ 53)`);
                vals.push(`(.str s${i})`);
            }
            else {
                binders.push(`(v${i} : Val ${TT} ${t.text})`);
                vals.push(`v${i}`);
            }
        });
        if (!obs && (objects ? !objs : strlen ? !strs : !refs))
            return undefined;
        const name = `equiv_${j.id}_${obs ? 'obs' : objects ? 'wfo' : strlen ? 'wfs' : 'wf'}`;
        const vs = vals.reduceRight((acc, v) => `(.cons ${v} ${acc})`, '.nil');
        const stmt = obs ? `Obs.Equiv (${obs} w.next)
      (${call(j.oldT, o.base, vs)})
      (${call(j.newT, n.base, vs)})` : `${call(j.oldT, o.base, vs)} =
      ${call(j.newT, n.base, vs)}`;
        return { hyps: hyps.join(' '), text: `set_option maxHeartbeats ${j.heartbeats} in
theorem ${name} (I : Impl) (w : World ${TT}) ${binders.join(' ')}
    ${hyps.join(' ')} :
    ${stmt} := by
${fillScript(obs ? exports.OBS_SCRIPT : j.scriptWf, j, o, n, argsO, defs)}

#print axioms ${name}
` };
    };
    const wf = variant(false), wfs = variant(true), wfo = variant(false, true);
    // the observational statement (\`_obs\`, see StrictTS/Proof/Obs.lean): a result without references
    // related by \`ObsEq w.next\`, an array of such values by \`ArrObs w.next\` (the same caller array, or
    // fresh arrays with equal contents), for functions that schedule no asynchronous work; argument
    // cells allocated (one at or above \`w.next\` would be overwritten by the callee's allocations) and
    // string lengths bounded as in \`_wfs\`
    let ret;
    try {
        ret = parseLTy(o.ret);
    }
    catch {
        ret = undefined;
    }
    const rel = !ret ? undefined : refFree(ret) ? 'Obs.ObsEq' : ret.k === 'arr' && refFree(ret.args[0]) ? 'Obs.ArrObs' : undefined;
    const obs = rel && !ASYNC_RE.test(j.oldT.body) && !ASYNC_RE.test(j.newT.body) ? variant(true, false, rel) : undefined;
    return { main, np, wf: wf?.text, wfHyps: wf?.hyps, wfs: wfs?.text, wfo: wfo?.text, obs: obs?.text };
}
/** The new version's type table and class field lists as aliases of the old version's when their
text is the same: the two translations then share one `TT` up to reducible unfolding (a field
list of the new version is otherwise a different heap key, and `Val New.TT` a different type to
`simp`). */
function aliasNewTypes(oldBody, newBody, oldNs) {
    const block = (b) => { const m = /^abbrev TT : TypeTable where\n(?:  .*\n)*/m.exec(b); return m ? m[0] : undefined; };
    const ob = block(oldBody), nb = block(newBody);
    let out = newBody;
    if (ob && nb && ob === nb)
        out = out.replace(nb, `abbrev TT : TypeTable := ${oldNs}.TT\n`);
    out = out.replace(/^abbrev «([^»]+)»\.fields : Fields := (.*)$/gm, (line, c) => oldBody.split('\n').includes(line) ? `abbrev «${c}».fields : Fields := ${oldNs}.«${c}».fields` : line);
    return out;
}
function runLeanBatch(file, proofs, evals, timeoutS) {
    const header = ['import StrictTS', 'import StrictTS.Proof.Literals', 'set_option maxRecDepth 100000', 'open StrictTS StrictTS.Frontend', exports.TACTIC_PRELUDE];
    const lines = [...header.join('\n').split('\n')];
    const ranges = [];
    const push = (id, kind, text, ns) => {
        lines.push(`-- @@BEGIN ${kind} ${id}`);
        const from = lines.length + 1;
        lines.push(...text.split('\n'));
        ranges.push({ id, kind, from, to: lines.length, ns });
        lines.push(`-- @@END ${kind} ${id}`);
    };
    for (const e of evals)
        push(e.id, 'eval', e.t.body, e.t.ns);
    for (const p of proofs)
        push(p.id, 'proof', p.text);
    (0, util_1.writeFile)(file, lines.join('\n') + '\n');
    const r = (0, util_1.run)('lean', ['--tstack=262144', file], { env: (0, util_1.leanEnv)(), timeoutS, cwd: util_1.ROOT });
    const text = r.stdout + r.stderr;
    (0, util_1.writeFile)(file.replace(/\.lean$/, '.out'), text);
    const res = { proofs: new Map(), evals: new Map(), secs: r.secs, timedOut: r.timedOut, file };
    const msgs = parseMessages(text);
    const errs = msgs.filter(x => x.kind === 'error').map(x => ({ line: x.line, msg: x.msg.trim() }));
    const infos = msgs.filter(x => x.kind === 'info').map(x => ({ line: x.line, msg: x.msg.trim() }));
    for (const rg of ranges) {
        const mine = errs.filter(e => e.line >= rg.from && e.line <= rg.to).map(e => e.msg);
        if (rg.kind === 'eval') {
            const b = text.indexOf(`=====STRICTTS-BEGIN ${rg.ns}=====`);
            const e = text.indexOf(`=====STRICTTS-END ${rg.ns}=====`);
            if (b >= 0 && e > b)
                res.evals.set(rg.id, { ok: true, out: text.slice(b + `=====STRICTTS-BEGIN ${rg.ns}=====`.length + 1, e), errors: mine });
            else
                res.evals.set(rg.id, { ok: false, out: '', errors: mine.length ? mine : [r.timedOut ? 'lean timed out' : 'no output'] });
        }
        else {
            const am = text.match(new RegExp(`'equiv_${rg.id}' (?:depends on axioms: \\[([^\\]]*)\\]|does not depend on any axioms)`));
            const axioms = am ? (am[1] ?? '').split(',').map(s => s.trim()).filter(Boolean) : [];
            const goals = infos.filter(e => e.line >= rg.from && e.line <= rg.to).map(e => e.msg);
            res.proofs.set(rg.id, { ok: !!am && mine.length === 0 && !axioms.includes('sorryAx'), axioms, goals, errors: am ? mine : (mine.length ? mine : [r.timedOut ? 'lean timed out' : 'theorem not checked']) });
        }
    }
    return res;
}
function leanAvailable() {
    try {
        (0, util_1.leanEnv)();
        return fs.existsSync(path.join(util_1.ROOT, '.lake', 'build', 'lib', 'lean', 'StrictTS', 'Proof', 'Tactics.olean'));
    }
    catch {
        return false;
    }
}

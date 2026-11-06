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
exports.DEFAULTS = void 0;
exports.driverSlice = driverSlice;
exports.runProgramNode = runProgramNode;
exports.programText = programText;
exports.analyzePair = analyzePair;
exports.leanPhase = leanPhase;
exports.finalize = finalize;
exports.runPipeline = runPipeline;
exports.classifyProofFailure = classifyProofFailure;
// End-to-end: materialize OLD and NEW, pair functions, fuzz each changed one, then a batched
// Lean stage (confirmation runs for counterexamples, equivalence theorems otherwise).
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const spec_1 = require("./spec");
const project_1 = require("./project");
const diff_1 = require("./diff");
const typedesc_1 = require("./typedesc");
const driver_1 = require("./driver");
const literal_1 = require("./literal");
const fuzz_1 = require("./fuzz");
const lean_1 = require("./lean");
const util_1 = require("./util");
exports.DEFAULTS = {
    runs: 1500, seed: 1, timeoutMs: 1000, shrinkBudget: 400, lean: true, script: lean_1.DEFAULT_SCRIPT, scriptWf: lean_1.DEFAULT_SCRIPT_WF, heartbeats: 400000,
    leanTimeoutS: 400, leanBatch: 8,
};
/** Copy of a slice with a driver appended to its entry file. */
/** Class names used by tagged input values. */
function classesIn(t, out) {
    if (!t)
        return;
    switch (t.t) {
        case 'c':
            out.add(t.cls);
            t.args.forEach(a => classesIn(a, out));
            break;
        case 'a':
        case 'S':
        case 'ta':
            t.v.forEach(a => classesIn(a, out));
            break;
        case 'o':
            t.v.forEach(([, a]) => classesIn(a, out));
            break;
        case 'm':
            t.v.forEach(([k, a]) => { classesIn(k, out); classesIn(a, out); });
            break;
        case 'p':
            classesIn(t.v, out);
            break;
    }
}
function driverSlice(sl, dir, u, sig, inputs) {
    fs.rmSync(dir, { recursive: true, force: true });
    const files = new Map(sl.files);
    const entryText = files.get(sl.entry) ?? '';
    // classes built by the inputs but declared in another file of the slice are imported
    const cls = new Set();
    for (const inp of inputs) {
        inp.args.forEach(a => classesIn(a, cls));
        (inp.self ?? []).forEach(a => classesIn(a, cls));
    }
    const imports = [];
    for (const c of cls) {
        const decl = new RegExp(`\\bclass\\s+${c}\\b`);
        if (decl.test(entryText))
            continue;
        const home = [...files.keys()].find(f => decl.test(files.get(f)));
        if (!home)
            continue;
        let rel = path.posix.relative(path.posix.dirname(sl.entry), home).replace(/\.tsx?$/, '');
        if (!rel.startsWith('.'))
            rel = './' + rel;
        imports.push(`import { ${c} } from ${JSON.stringify(rel)};`);
    }
    files.set(sl.entry, entryText + imports.map(i => '\n' + i).join('') + (0, driver_1.driverSource)(u, sig, inputs));
    for (const [rel, text] of files)
        (0, util_1.writeFile)(path.join(dir, rel), text);
    return { ...sl, dir, files };
}
async function runProgramNode(sl, timeoutMs = 5000) {
    const r = new fuzz_1.Runner((0, fuzz_1.initMsg)({ files: sl.files, entry: sl.entry, exportName: '', kind: 'program' }, timeoutMs));
    try {
        const [o] = await r.run([{ args: [] }]);
        return programText(o);
    }
    finally {
        r.kill();
    }
}
function programText(o) {
    if (o.kind !== 'ok')
        return [...o.out, `[${o.o}]`].join('\n');
    const st = o.unhandled.length && o.o === '[ok]' ? `[uncaught ${o.unhandled[0]}]` : o.o;
    return [...o.out, st].join('\n');
}
function lines(s) {
    return s.replace(/\r/g, '').split('\n').filter((l, i, a) => !(i === a.length - 1 && l === ''));
}
/** Materialize, pair, slice, fuzz and prepare the Lean jobs of one OLD/NEW pair. */
async function analyzePair(oldSpec, newSpec, opts, idPrefix = 'u') {
    (0, util_1.mkdirp)(opts.work);
    const oldSet = (0, spec_1.materialize)(oldSpec, path.join(opts.work, 'src_old'), { repo: opts.repo });
    const newSet = (0, spec_1.materialize)(newSpec, path.join(opts.work, 'src_new'), { repo: opts.repo });
    const oldP = (0, project_1.makeProject)(oldSet), newP = (0, project_1.makeProject)(newSet);
    const reports = (0, diff_1.pairUnits)(oldP, newP, opts);
    const changed = reports.filter(r => r.status === 'changed');
    opts.log(`${changed.length} changed function(s), ${reports.filter(r => r.status === 'added').length} added, ${reports.filter(r => r.status === 'removed').length} removed`);
    const pend = [];
    const useLean = opts.lean && (0, lean_1.leanAvailable)();
    if (opts.lean && !useLean)
        opts.log('Lean build not found (lake build StrictTS): Lean stage skipped');
    let idx = 0;
    for (const r of changed) {
        idx++;
        const c = r.ctx;
        const id = `${idPrefix}${String(idx).padStart(3, '0')}`;
        opts.log(`[${idx}/${changed.length}] ${r.key}`);
        let canFuzz = false;
        try {
            canFuzz = (0, diff_1.prepare)(r, oldP, newP);
        }
        catch (e) {
            r.reasons.push(`slicing: ${e.message}`);
        }
        if (canFuzz)
            await (0, diff_1.fuzzUnit)(r, opts);
        const f = c.fuzz;
        if (f?.status === 'diff' && f.cex) {
            const cx = f.cex;
            r.cex = {
                input: cx.input, inputText: (0, literal_1.callText)(r.name, cx.input.args, cx.input.self, c.oldUnit.cls, c.oldUnit.kind),
                old: describeObs(cx.old, cx.new), new: describeObs(cx.new, cx.old), parts: cx.parts,
                oldObs: obsView(cx.old), newObs: obsView(cx.new),
            };
            r.verdict = 'REFUTED';
            r.confirmedBy = ['node'];
            if (useLean) {
                // confirmation: the same call through a driver, under Node and under the Lean semantics
                try {
                    const newSig = (0, typedesc_1.signatureOf)(newP, c.newUnit);
                    const od = driverSlice(c.oldSlice, path.join(c.dir, 'old_drv'), c.oldUnit, c.sig, [cx.input]);
                    const nd = driverSlice(c.newSlice, path.join(c.dir, 'new_drv'), c.newUnit, newSig, [cx.input]);
                    const p = { r, kind: 'confirm', id };
                    p.nodeOld = await runProgramNode(od);
                    p.nodeNew = await runProgramNode(nd);
                    p.oldT = (0, lean_1.translateSlice)(od.dir, od.entry, `OldC_${id}`, true);
                    p.newT = (0, lean_1.translateSlice)(nd.dir, nd.entry, `NewC_${id}`, true);
                    if (p.oldT.ok && p.newT.ok)
                        pend.push(p);
                    else
                        r.notes.push(`Lean confirmation not run: ${!p.oldT.ok ? 'old' : 'new'} driver outside the subset [${(!p.oldT.ok ? p.oldT : p.newT).rules.join(', ')}]: ${firstDiag((!p.oldT.ok ? p.oldT : p.newT).diagnostics)}`);
                }
                catch (e) {
                    r.notes.push(`Lean confirmation not run: ${e.message}`);
                }
            }
            continue;
        }
        // no counterexample: attempt a proof
        if (!c.oldSlice?.ok || !c.newSlice?.ok) {
            r.verdict = 'UNKNOWN';
            continue;
        }
        if (!useLean) {
            r.verdict = 'UNKNOWN';
            r.reasons.push('no counterexample found; Lean stage disabled');
            continue;
        }
        try {
            (0, diff_1.proofSlices)(r);
            let target = c.oldUnit.name;
            if (c.oldUnit.isGeneric || c.newUnit.isGeneric) {
                const mo = (0, diff_1.monoWrapper)(c.oldUnit, c.oldProof), mn = (0, diff_1.monoWrapper)(c.newUnit, c.newProof);
                if ('error' in mo || 'error' in mn) {
                    r.reasons.push(('error' in mo ? mo : mn).error);
                    r.verdict = 'UNKNOWN';
                    continue;
                }
                // instances that differ in their type parameters (or one version not generic) are compared when
                // the two wrappers' translated signatures agree; otherwise the compat wrappers below are tried
                r.notes.push(`generic: compared at the instance ${mo.inst === mn.inst ? mo.inst : !mn.inst ? `${mo.inst}; the new version is not generic` : !mo.inst ? `${mn.inst}; the old version is not generic` : `${mo.inst} (old) and ${mn.inst} (new)`} (wrapper ${diff_1.MONO_NAME})`);
                target = diff_1.MONO_NAME;
            }
            const oldT = (0, lean_1.translateSlice)(c.oldProof.dir, c.oldProof.entry, `Old_${id}`, false);
            const newT = (0, lean_1.translateSlice)(c.newProof.dir, c.newProof.entry, `New_${id}`, false);
            if (c.oldProof.inlined.length || c.newProof.inlined.length)
                r.notes.push(`inlined module constants: ${[...new Set([...c.oldProof.inlined, ...c.newProof.inlined])].join(', ')}`);
            if (!oldT.ok || !newT.ok) {
                const rules = [...new Set([...oldT.rules, ...newT.rules])];
                r.reasons.push(`outside the StrictTS subset: ${rules.join(', ')}${!oldT.ok ? ` (old: ${firstDiag(oldT.diagnostics)})` : ''}${!newT.ok ? ` (new: ${firstDiag(newT.diagnostics)})` : ''}`);
                r.verdict = 'UNKNOWN';
                continue;
            }
            if (oldT.moduleState !== newT.moduleState) {
                r.reasons.push('module-level state (globals or their initialisers) differs between the versions; no ∀-world theorem');
                r.verdict = 'UNKNOWN';
                continue;
            }
            let thm = (0, lean_1.theoremFor)({ id, oldT, newT, target, script: opts.script, scriptWf: opts.scriptWf, heartbeats: opts.heartbeats });
            let newTp = newT;
            // a widened parameter list: compare on the old version's inputs, through a wrapper in the new slice
            // (for a generic function: the old wrapper's instance against the new version called at it)
            if ('error' in thm && /^translated signatures differ/.test(thm.error)) {
                const why = thm.error;
                const cw = (0, diff_1.compatWrapper)(c.oldUnit, c.newUnit.name, c.newProof);
                const t2 = 'error' in cw ? null : (0, lean_1.translateSlice)(c.newProof.dir, c.newProof.entry, `New_${id}`, false);
                if (t2 && t2.ok && t2.moduleState === oldT.moduleState) {
                    const thm2 = (0, lean_1.theoremFor)({ id, oldT, newT: t2, target, targetNew: diff_1.COMPAT_NAME, script: opts.script, scriptWf: opts.scriptWf, heartbeats: opts.heartbeats });
                    if (!('error' in thm2)) {
                        thm = thm2;
                        newTp = t2;
                        r.notes.push(`compared on the old version's inputs (wrapper ${diff_1.COMPAT_NAME}): ${why.replace(/^translated signatures differ/, 'the signature widened')}`);
                    }
                }
            }
            let oldTp = oldT;
            // a changed return type (T to T | undefined, a type widened to unknown): compare at the other
            // version's return type, through a wrapper of one version declared with it (first the old one)
            if ('error' in thm && /^translated signatures differ/.test(thm.error)) {
                const why = thm.error;
                for (const side of ['old', 'new']) {
                    const [u, other, sl] = side === 'old' ? [c.oldUnit, c.newUnit, c.oldProof] : [c.newUnit, c.oldUnit, c.newProof];
                    if ('error' in (0, diff_1.retWrapper)(u, other, sl))
                        continue;
                    const tw = (0, lean_1.translateSlice)(sl.dir, sl.entry, `${side === 'old' ? 'Old' : 'New'}_${id}`, false);
                    const [o, n] = side === 'old' ? [tw, newT] : [oldT, tw];
                    if (!tw.ok || o.moduleState !== n.moduleState)
                        continue;
                    const thm3 = (0, lean_1.theoremFor)({ id, oldT: o, newT: n, target: side === 'old' ? diff_1.RET_NAME : target, targetNew: side === 'old' ? target : diff_1.RET_NAME, script: opts.script, scriptWf: opts.scriptWf, heartbeats: opts.heartbeats });
                    if ('error' in thm3)
                        continue;
                    thm = thm3;
                    oldTp = o;
                    newTp = n;
                    r.notes.push(`compared at the ${side === 'old' ? 'new' : 'old'} version's return type (wrapper ${diff_1.RET_NAME} around the ${side} version): ${why.replace(/^translated signatures differ/, 'the return type changed')}`);
                    break;
                }
            }
            if ('error' in thm) {
                r.reasons.push(thm.error);
                r.verdict = 'UNKNOWN';
                continue;
            }
            pend.push({ r, kind: 'proof', oldT: oldTp, newT: newTp, theorem: thm.main, theoremWf: thm.wf, theoremWfs: thm.wfs, theoremWfo: thm.wfo, theoremObs: thm.obs, theoremNp: thm.np, id });
        }
        catch (e) {
            r.reasons.push(`Lean preparation: ${e.message}`);
            r.verdict = 'UNKNOWN';
        }
    }
    return { reports, pend, oldSet, newSet };
}
/** Lean blocks of a proof job: the translations with the main theorem, then the allocated-arguments
theorems (without and with the string-length hypotheses). */
function proofBlocks(p) {
    const out = [{ id: p.id, text: p.oldT.body + '\n' + (0, lean_1.aliasNewTypes)(p.oldT.body, p.newT.body, p.oldT.ns) + '\n' + p.theorem }];
    if (p.theoremWf)
        out.push({ id: p.id + '_wf', text: p.theoremWf });
    if (p.theoremWfs)
        out.push({ id: p.id + '_wfs', text: p.theoremWfs });
    if (p.theoremWfo)
        out.push({ id: p.id + '_wfo', text: p.theoremWfo });
    return out;
}
/** Lean blocks of the weaker statements (second pass): the observational statement and the one where
the old version does not panic, each with the translations. */
function weakBlocks(p) {
    const tr = p.oldT.body + '\n' + (0, lean_1.aliasNewTypes)(p.oldT.body, p.newT.body, p.oldT.ns) + '\n';
    // the translations once, in the first block (a later block uses them)
    return [...(p.theoremObs ? [{ id: p.id + '_obs', text: tr + p.theoremObs }] : []),
        ...(p.theoremNp ? [{ id: p.id + '_np', text: (p.theoremObs ? '' : tr) + p.theoremNp }] : [])];
}
/** Ids of the equality statements of a proof job. */
function eqIds(p) {
    return [p.id, ...(p.theoremWf ? [p.id + '_wf'] : []), ...(p.theoremWfs ? [p.id + '_wfs'] : []), ...(p.theoremWfo ? [p.id + '_wfo'] : [])];
}
const lost = (res, id) => (res.proofs.get(id)?.errors ?? ['no result']).some(e => /theorem not checked|no output|timed out/.test(e));
/** Run the Lean jobs in batches (one Lean process per batch; a timed-out batch is retried unit by
unit), then, in a second pass, the observational statements of the functions for which no
equality statement was proved. */
function leanPhase(pend, opts, leanDir) {
    const later = [];
    const finish = (p, res) => {
        if (p.kind === 'proof' && (p.theoremObs || p.theoremNp) && !eqIds(p).some(id => res.proofs.get(id)?.ok))
            later.push({ p, res });
        else
            finishPending(p, res, opts);
    };
    for (let i = 0; i < pend.length; i += opts.leanBatch) {
        const chunk = pend.slice(i, i + opts.leanBatch);
        const evals = [];
        const proofs = [];
        for (const p of chunk) {
            if (p.kind === 'confirm') {
                evals.push({ id: p.id + 'o', t: p.oldT }, { id: p.id + 'n', t: p.newT });
            }
            else
                proofs.push(...proofBlocks(p));
        }
        const file = path.join(leanDir, `batch_${String(i / opts.leanBatch).padStart(2, '0')}.lean`);
        opts.log(`Lean batch ${i / opts.leanBatch + 1}/${Math.ceil(pend.length / opts.leanBatch)}: ${evals.length / 2} confirmation(s), ${proofs.length} proof(s)`);
        const res = (0, lean_1.runLeanBatch)(file, proofs, evals, opts.leanTimeoutS);
        opts.log(`  ${res.secs.toFixed(1)} s${res.timedOut ? ' (timed out)' : ''}`);
        // a timed-out or crashed batch (e.g. Lean out of memory) is retried unit by unit
        const crashed = chunk.some(p => p.kind === 'confirm'
            ? !(res.evals.get(p.id + 'o')?.ok && res.evals.get(p.id + 'n')?.ok)
            : eqIds(p).some(id => lost(res, id)));
        if ((res.timedOut || crashed) && chunk.length > 1) {
            for (const p of chunk) {
                const f1 = path.join(leanDir, `unit_${p.id}.lean`);
                const r1 = p.kind === 'confirm'
                    ? (0, lean_1.runLeanBatch)(f1, [], [{ id: p.id + 'o', t: p.oldT }, { id: p.id + 'n', t: p.newT }], opts.leanTimeoutS)
                    : (0, lean_1.runLeanBatch)(f1, proofBlocks(p), [], opts.leanTimeoutS);
                for (const [k, v] of r1.proofs)
                    res.proofs.set(k, v);
                for (const [k, v] of r1.evals)
                    res.evals.set(k, v);
                if (p.kind === 'proof')
                    res.file = f1;
                finish(p, { ...res, file: f1 });
            }
            continue;
        }
        for (const p of chunk)
            finish(p, res);
    }
    for (let i = 0; i < later.length; i += opts.leanBatch) {
        const chunk = later.slice(i, i + opts.leanBatch);
        const file = path.join(leanDir, `obs_${String(i / opts.leanBatch).padStart(2, '0')}.lean`);
        opts.log(`Lean observational batch ${i / opts.leanBatch + 1}/${Math.ceil(later.length / opts.leanBatch)}: ${chunk.length} proof(s)`);
        const res = (0, lean_1.runLeanBatch)(file, chunk.flatMap(x => weakBlocks(x.p)), [], opts.leanTimeoutS);
        opts.log(`  ${res.secs.toFixed(1)} s${res.timedOut ? ' (timed out)' : ''}`);
        for (const x of chunk) {
            let r1 = res;
            const ids = weakBlocks(x.p).map(b => b.id);
            // a unit lost in a timed-out or crashed batch is retried alone
            if (chunk.length > 1 && ids.some(id => lost(res, id))) {
                const f1 = path.join(leanDir, `unit_${x.p.id}_obs.lean`);
                r1 = (0, lean_1.runLeanBatch)(f1, weakBlocks(x.p), [], opts.leanTimeoutS);
            }
            for (const id of ids) {
                const o = r1.proofs.get(id);
                if (o)
                    x.res.proofs.set(id, o);
            }
            finishPending(x.p, x.res, opts, r1.file);
        }
    }
}
function finalize(reports) {
    for (const r of reports.filter(x => x.status === 'changed')) {
        if (!r.verdict)
            r.verdict = 'UNKNOWN';
        if (r.verdict === 'UNKNOWN' && !r.reasons.length && r.ctx?.fuzz?.status === 'same')
            r.reasons.push(`no counterexample in ${r.ctx.fuzz.runs} runs; no proof`);
    }
}
async function runPipeline(oldSpec, newSpec, opts) {
    const a = await analyzePair(oldSpec, newSpec, opts);
    leanPhase(a.pend, opts, path.join(opts.work, 'lean'));
    finalize(a.reports);
    return a;
}
function firstDiag(d) {
    const l = d.split('\n').find(x => x.trim()) ?? '';
    return l.length > 200 ? l.slice(0, 200) + '…' : l;
}
function obsView(o) {
    return { outcome: o.o, console: o.out, args: o.args, receiver: o.self ?? null, unhandled: o.unhandled };
}
/** The observation, restricted to the outcome and the parts that differ from `other`. */
function describeObs(o, other) {
    const parts = [o.o];
    if (o.out.join('\n') !== other.out.join('\n'))
        parts.push(`console ${JSON.stringify(o.out)}`);
    if (o.args.join('\u0001') !== other.args.join('\u0001'))
        parts.push(`args after (${o.args.join(', ')})`);
    if ((o.self ?? '') !== (other.self ?? ''))
        parts.push(`this after ${o.self}`);
    if (o.unhandled.join('\n') !== other.unhandled.join('\n'))
        parts.push(`unhandled ${o.unhandled.join('; ') || 'none'}`);
    return parts.join('; ');
}
function finishPending(p, res, opts, obsFile) {
    const r = p.r;
    if (p.kind === 'confirm') {
        const eo = res.evals.get(p.id + 'o'), en = res.evals.get(p.id + 'n');
        if (!eo?.ok || !en?.ok) {
            r.notes.push(`Lean confirmation failed to run: ${(eo?.errors ?? en?.errors ?? ['?']).join(' / ').slice(0, 300)}`);
            return;
        }
        const lo = lines(eo.out).join('\n'), ln = lines(en.out).join('\n');
        const no = lines(p.nodeOld).join('\n'), nn = lines(p.nodeNew).join('\n');
        r.cex.lean = { old: lo, new: ln };
        if (lo !== no || ln !== nn) {
            r.notes.push(`LEAN/NODE MISMATCH on the driver (translator or semantics bug): ${lo !== no ? `old: node ${JSON.stringify(no)} lean ${JSON.stringify(lo)}` : `new: node ${JSON.stringify(nn)} lean ${JSON.stringify(ln)}`}`);
            return;
        }
        if (lo === ln) {
            r.notes.push('Lean confirmation inconclusive: the driver does not print the differing part (e.g. object identity or private state)');
            return;
        }
        r.confirmedBy = ['node', 'lean'];
        return;
    }
    const pr = res.proofs.get(p.id);
    if (!pr) {
        r.reasons.push('proof: no result');
        r.verdict = 'UNKNOWN';
        return;
    }
    const pw = p.theoremWf ? res.proofs.get(p.id + '_wf') : undefined;
    const ps = p.theoremWfs ? res.proofs.get(p.id + '_wfs') : undefined;
    const po = p.theoremWfo ? res.proofs.get(p.id + '_wfo') : undefined;
    const pb = p.theoremObs ? res.proofs.get(p.id + '_obs') : undefined;
    const pn = p.theoremNp ? res.proofs.get(p.id + '_np') : undefined;
    const residual = (x) => (x.errors.find(e => e.includes('difftool: residual goal')) ?? x.goals[0] ?? '').slice(0, 4000) || undefined;
    // the strongest statement checked: every world, allocated arguments, then also string lengths,
    // object arguments; then the observational statement (weaker: equality up to fresh cells), last
    // equality where the old version does not panic
    const kind = pr.ok ? 'all-worlds' : pw?.ok ? 'allocated-arguments' : ps?.ok ? 'allocated-arguments-strlen' :
        po?.ok ? 'allocated-arguments-objects' : pb?.ok ? 'observational' : pn?.ok ? 'old-no-panic' : 'all-worlds';
    const best = kind === 'allocated-arguments' ? pw : kind === 'allocated-arguments-strlen' ? ps :
        kind === 'allocated-arguments-objects' ? po : kind === 'observational' ? pb : kind === 'old-no-panic' ? pn : pr;
    const suffix = kind === 'allocated-arguments' ? '_wf' : kind === 'allocated-arguments-strlen' ? '_wfs' :
        kind === 'allocated-arguments-objects' ? '_wfo' : kind === 'observational' ? '_obs' : kind === 'old-no-panic' ? '_np' : '';
    const second = kind === 'observational' || kind === 'old-no-panic';
    r.proof = { file: second ? obsFile : res.file, theorem: `equiv_${p.id}${suffix}`, axioms: best.axioms,
        script: kind === 'observational' ? lean_1.OBS_SCRIPT : kind === 'old-no-panic' ? opts.script : suffix ? opts.scriptWf : opts.script, residual: best.ok ? undefined : residual(pr),
        statement: kind, wf: pw ? { ok: pw.ok, residual: pw.ok ? undefined : residual(pw) } : undefined,
        wfs: ps ? { ok: ps.ok, residual: ps.ok ? undefined : residual(ps) } : undefined,
        wfo: po ? { ok: po.ok, residual: po.ok ? undefined : residual(po) } : undefined,
        obs: pb ? { ok: pb.ok, residual: pb.ok ? undefined : residual(pb) } : undefined,
        np: pn ? { ok: pn.ok, residual: pn.ok ? undefined : residual(pn) } : undefined };
    if (best.ok) {
        if (r.ctx?.fuzz?.status === 'diff') {
            r.verdict = 'UNKNOWN';
            r.reasons.push('SOUNDNESS ALERT: proof checked although fuzzing found a difference');
            return;
        }
        // the old-no-panic statement is not an equivalence: verdict UNKNOWN, with that proof attached
        r.verdict = kind === 'old-no-panic' ? 'UNKNOWN' : 'PROVED';
        if (kind === 'old-no-panic')
            r.reasons.push('only the weaker old-no-panic statement was proved (equal runs, or the old run panics); no equivalence statement was proved');
        if (kind === 'allocated-arguments')
            r.notes.push('proved for every world in which the argument arrays, maps and sets are allocated cells (hw: the cell exists, hn: its address is below the allocation counter), as in every state a run reaches; the statement over all worlds was not proved');
        if (kind === 'allocated-arguments-objects')
            r.notes.push('proved for every world in which the argument arrays, maps and sets and the object arguments are allocated cells, the objects\' fields initialised and their array fields allocated cells with fewer than 2^32 - 1 elements (JavaScript arrays stay below 2^32 elements), as in every state a run reaches; no statement without the object hypotheses was proved');
        if (kind === 'allocated-arguments-strlen')
            r.notes.push('proved for every world in which the argument arrays, maps and sets are allocated cells and the string arguments have at most 2^53 - 1 code units (the maximum length of an ECMAScript String, ECMA-262 6.1.4), as in every state a run reaches; neither the statement over all worlds nor the one without the string lengths was proved');
        if (kind === 'observational')
            r.notes.push(`proved only up to observation (statement observational, WEAKER than equality of worlds): in every world in which the argument arrays, maps and sets are allocated cells and the string arguments have at most 2^53 - 1 code units, the two runs both fail to terminate, or end with ${/Obs\.ArrObs/.test(p.theoremObs) ? 'the same error, or with the same caller array or two fresh arrays with equal contents' : 'the same result'}, the same console output, the same cells below the caller's allocation counter and the same numbers of Math.random/Date.now/external-call answers consumed; the cells the callee allocated (other than a returned array) and the allocation counter are not compared (the functions schedule no asynchronous work); no equality statement was proved`);
        if (kind === 'old-no-panic')
            r.notes.push('proved only where the old version does not panic (statement old-no-panic, WEAKER than equality of worlds): for every argument list and every world, the two runs are equal or the old run panics (a read the TypeScript types exclude, a non-null assertion on undefined, or another designed panic); where the old version panics, the new one may do anything; no other statement was proved');
        if (best.axioms.some(a => /ofReduceBool|trustCompiler/.test(a)))
            r.notes.push(`proof uses the native-code axiom (${best.axioms.filter(a => /ofReduceBool|trustCompiler/.test(a)).join(', ')}) via bv_decide`);
    }
    else {
        r.verdict = 'UNKNOWN';
        r.reasons.push(`no proof: ${classifyProofFailure(pr.errors, pr.goals)}${pw ? `; allocated-arguments statement: ${classifyProofFailure(pw.errors, pw.goals)}` : ''}${ps ? `; allocated-arguments-strlen statement: ${classifyProofFailure(ps.errors, ps.goals)}` : ''}${po ? `; allocated-arguments-objects statement: ${classifyProofFailure(po.errors, po.goals)}` : ''}${pb ? `; observational statement: ${classifyProofFailure(pb.errors, pb.goals)}` : ''}${pn ? `; old-no-panic statement: ${classifyProofFailure(pn.errors, pn.goals)}` : ''}`);
    }
}
function classifyProofFailure(errors, goals = []) {
    const all = errors.join('\n');
    if (/maximum number of heartbeats|deterministic\) timeout/.test(all))
        return 'proof search timed out (heartbeats)';
    if (/lean timed out/.test(all))
        return 'Lean process timed out';
    if (/theorem not checked/.test(all))
        return 'theorem not checked (elaboration error)';
    const g = [...goals, ...errors].join('\n');
    const hints = [];
    if (/evalLoop|evalForOf|evalDo|forOfA|loopA|evalForOfStr|evalForOfMap|evalForOfSet/.test(g))
        hints.push('loops (needs loop summarization or a lockstep rule)');
    if (/arrReduce|arrMap|arrFilter|arrSome|arrEvery|arrFind|arrForEach|sortL|arrSort|arrFromFn|arrFlatMap/.test(g))
        hints.push('array library calls with callbacks');
    if (/mapForEachL|readMap|JSMap|mapGet|mapSet/.test(g))
        hints.push('Map operations');
    if (/drain|runJob|eventLoop|PromiseCell|settle|newPromise|handleStep|execAB|applyK/.test(g))
        hints.push('async/promise machinery');
    if (/callFun|applyLam|applyFn/.test(g))
        hints.push('a call that was not unfolded (recursion or closure)');
    if (/next := |\.next \+|alloc/.test(g))
        hints.push('allocation differs (equivalence modulo fresh allocation)');
    if (!hints.length && /JSStr|strConcat|toJSString|strSlice|startsWith|indexOf|strIncludes/.test(g))
        hints.push('string-library reasoning left open');
    if (!hints.length && /F64|\.lt |\.le |\.min|\.max|floor|\.add|\.mul|\.div/.test(g))
        hints.push('number (F64) reasoning left open');
    if (!hints.length && g)
        hints.push('residual goal');
    if (!hints.length)
        hints.push('proof failed: ' + (errors[0] ?? '').split('\n')[0].slice(0, 160));
    return hints.join('; ');
}

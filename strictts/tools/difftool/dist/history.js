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
exports.scanHistory = scanHistory;
exports.summarizeScan = summarizeScan;
exports.runHistoryPairs = runHistoryPairs;
// Real history: scan the commits of a repository (read-only git commands only) for functions
// whose old and new versions can be sliced; classify them (external dependencies, input types,
// StrictTS subset rules), extract the self-contained pairs into an output directory and run
// the semantic diff on them.
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const ts = __importStar(require("typescript"));
const spec_1 = require("./spec");
const project_1 = require("./project");
const units_1 = require("./units");
const slice_1 = require("./slice");
const typedesc_1 = require("./typedesc");
const lean_1 = require("./lean");
const diff_1 = require("./diff");
const pipeline_1 = require("./pipeline");
const report_1 = require("./report");
const util_1 = require("./util");
const SECRET_RES = [/AIza[0-9A-Za-z_-]{30,}/, /\bsk-[A-Za-z0-9]{20,}/, /-----BEGIN [A-Z ]*PRIVATE KEY-----/,
    /(api[_-]?key|secret|passw(or)?d|token|credential)\w*\s*[:=]\s*["'`][^"'`\s]{12,}["'`]/i, /\b[0-9a-f]{40,}\b/i];
function git(repo, args) {
    const r = (0, util_1.run)('git', ['-C', repo, ...args], { timeoutS: 120 });
    if (r.status !== 0)
        throw new Error(`git ${args.join(' ')}: ${r.stderr.trim()}`);
    return r.stdout;
}
function unitTexts(text, file) {
    const sf = ts.createSourceFile(file, text, ts.ScriptTarget.ES2022, true, file.endsWith('.tsx') ? ts.ScriptKind.TSX : ts.ScriptKind.TS);
    const m = new Map();
    const add = (name, n) => { if (!m.has(name))
        m.set(name, (0, units_1.normText)(n, sf)); };
    for (const st of sf.statements) {
        if (ts.isFunctionDeclaration(st) && st.name && st.body)
            add(st.name.text, st);
        else if (ts.isVariableStatement(st)) {
            for (const d of st.declarationList.declarations) {
                if (!ts.isIdentifier(d.name) || !d.initializer)
                    continue;
                let init = d.initializer;
                while (ts.isParenthesizedExpression(init) || ts.isAsExpression(init) || ts.isSatisfiesExpression(init))
                    init = init.expression;
                if (ts.isArrowFunction(init) || ts.isFunctionExpression(init))
                    add(d.name.text, d);
            }
        }
        else if (ts.isClassDeclaration(st) && st.name) {
            for (const mm of st.members) {
                if (ts.isConstructorDeclaration(mm) && mm.body)
                    add(`${st.name.text}.constructor`, mm);
                else if (ts.isMethodDeclaration(mm) && mm.body && (ts.isIdentifier(mm.name) || ts.isPrivateIdentifier(mm.name)))
                    add(`${st.name.text}.${mm.name.text}`, mm);
            }
        }
    }
    return m;
}
function hasSecret(files) {
    for (const [, t] of files)
        for (const re of SECRET_RES)
            if (re.test(t))
                return true;
    return false;
}
function copySlice(sl, dest) {
    fs.rmSync(dest, { recursive: true, force: true });
    for (const [rel, text] of sl.files)
        (0, util_1.writeFile)(path.join(dest, rel), text);
}
async function scanHistory(h, opts) {
    const scanFile = path.join(h.out, 'scan.jsonl');
    (0, util_1.mkdirp)(h.out);
    const done = new Set();
    const records = [];
    if (fs.existsSync(scanFile)) {
        for (const l of fs.readFileSync(scanFile, 'utf8').split('\n').filter(Boolean)) {
            const r = JSON.parse(l);
            if (r.done)
                done.add(r.done);
            else
                records.push(r);
        }
    }
    const log = git(h.repo, ['log', '--no-merges', '--reverse', '--date=short', '--format=C%x09%H%x09%P%x09%ad%x09%s', '--name-status', '--', ...h.paths.map(p => p.endsWith('.ts') ? p : `${p.replace(/\/$/, '')}/*.ts`)]);
    const pairs = [];
    let cur = null;
    for (const l of log.split('\n')) {
        if (l.startsWith('C\t')) {
            const [, c, p, d, ...s] = l.split('\t');
            cur = { commit: c, parent: p.split(' ')[0], date: d, subject: s.join('\t') };
            continue;
        }
        const m = l.match(/^M\t(.+\.ts)$/);
        if (m && cur && cur.parent && !m[1].endsWith('.d.ts') && (!h.commits || h.commits.some(c => cur.commit.startsWith(c))))
            pairs.push({ ...cur, file: m[1] });
    }
    opts.log(`${pairs.length} modified .ts files in ${new Set(pairs.map(p => p.commit)).size} commits; ${done.size} already scanned`);
    let processed = 0;
    const append = (o) => fs.appendFileSync(scanFile, JSON.stringify(o) + '\n');
    for (const pr of pairs) {
        const key = `${pr.commit}:${pr.file}`;
        if (done.has(key))
            continue;
        if (processed >= h.maxPairs)
            break;
        processed++;
        let oldText, newText;
        try {
            oldText = git(h.repo, ['show', `${pr.parent}:${pr.file}`]);
            newText = git(h.repo, ['show', `${pr.commit}:${pr.file}`]);
        }
        catch {
            append({ done: key });
            continue;
        }
        const ou = unitTexts(oldText, pr.file), nu = unitTexts(newText, pr.file);
        const changed = [...ou.keys()].filter(k => nu.has(k) && nu.get(k) !== ou.get(k));
        if (!changed.length) {
            append({ done: key });
            continue;
        }
        const work = path.join(opts.work, 'scan', `${pr.commit.slice(0, 10)}_${pr.file.replace(/[^A-Za-z0-9]/g, '_')}`);
        try {
            const oldSet = (0, spec_1.materialize)(`git:${pr.parent}:${pr.file}`, path.join(work, 'src_old'), { repo: h.repo });
            const newSet = (0, spec_1.materialize)(`git:${pr.commit}:${pr.file}`, path.join(work, 'src_new'), { repo: h.repo });
            const oldP = (0, project_1.makeProject)(oldSet), newP = (0, project_1.makeProject)(newSet);
            const oUnits = new Map((0, units_1.unitsOf)(oldP, oldSet.roots[0], 'm').map(u => [u.name, u]));
            const nUnits = new Map((0, units_1.unitsOf)(newP, newSet.roots[0], 'm').map(u => [u.name, u]));
            let idx = 0;
            for (const name of changed) {
                const o = oUnits.get(name), n = nUnits.get(name);
                if (!o || !n)
                    continue;
                idx++;
                const rec = { commit: pr.commit, date: pr.date, subject: pr.subject, file: pr.file, name, kind: n.kind, cls: '', detail: '', rules: [], externals: [], hostGlobals: [], fuzzable: false, inSubset: false };
                try {
                    const udir = path.join(work, 'units', `${idx}_${name.replace(/[^A-Za-z0-9_]/g, '_')}`);
                    const os = (0, slice_1.sliceUnit)(oldP, o, path.join(udir, 'old')), ns = (0, slice_1.sliceUnit)(newP, n, path.join(udir, 'new'));
                    rec.externals = [...new Set([...os.externals, ...ns.externals])];
                    rec.hostGlobals = [...new Set([...os.hostGlobals, ...ns.hostGlobals])];
                    if (!os.ok || !ns.ok) {
                        rec.cls = 'external';
                        rec.detail = rec.externals.join(', ');
                    }
                    else {
                        const so = (0, typedesc_1.signatureOf)(oldP, o), sn = (0, typedesc_1.signatureOf)(newP, n);
                        const bad = [...so.params, ...(so.self?.ctor ?? [])].map(p => (0, typedesc_1.unsupportedIn)(p.rest && p.t.k === 'arr' ? p.t.t : p.t, so.table)).find(x => x);
                        const cp = (0, typedesc_1.compatibleParams)(so.params, so.table, sn.params, sn.table);
                        const cs = so.self && sn.self ? (0, typedesc_1.compatibleParams)(so.self.ctor, so.table, sn.self.ctor, sn.table) : { ok: true };
                        if (!cp.ok || !cs.ok || o.kind !== n.kind) {
                            rec.cls = 'signature';
                            rec.detail = `signature changed (${cp.reason ?? cs.reason ?? 'kind'})`;
                        }
                        else if (bad) {
                            rec.cls = 'inputs';
                            rec.detail = bad;
                        }
                        else
                            rec.fuzzable = true;
                        // a generic function is checked at the instance its proof uses (an uncalled generic
                        // function is not translated at all, so the slice alone would pass vacuously)
                        const inst = (u, sl, sub) => {
                            if (!u.isGeneric)
                                return { sl };
                            const dest = path.join(udir, sub);
                            copySlice(sl, dest);
                            const c = { ...sl, dir: dest, files: new Map(sl.files) };
                            const m = (0, diff_1.monoWrapper)(u, c);
                            return 'error' in m ? m : { sl: c };
                        };
                        const io = inst(o, os, 'old_inst'), inn = inst(n, ns, 'new_inst');
                        if ('error' in io || 'error' in inn) {
                            rec.rules = ['generic-instance'];
                            rec.inSubset = false;
                            if (!rec.cls) {
                                rec.cls = 'subset';
                                rec.detail = ('error' in io ? io : inn).error;
                            }
                        }
                        else {
                            const to = (0, lean_1.translateSlice)(io.sl.dir, io.sl.entry, 'HO', false), tn = (0, lean_1.translateSlice)(inn.sl.dir, inn.sl.entry, 'HN', false);
                            rec.rules = [...new Set([...to.rules, ...tn.rules])];
                            rec.inSubset = to.ok && tn.ok;
                            if (!rec.inSubset && !rec.cls)
                                rec.detail = (0, util_1.truncate)((!to.ok ? to.diagnostics : tn.diagnostics).split('\n')[0] ?? '', 200);
                            // a proof compares the target's FunRef, so a slice that translates without it is not provable
                            const tgt = (u) => u.isGeneric ? diff_1.MONO_NAME : u.name;
                            const missing = !rec.inSubset ? undefined : !to.refs.has(tgt(o)) ? `old: ${tgt(o)}` : !tn.refs.has(tgt(n)) ? `new: ${tgt(n)}` : undefined;
                            if (missing) {
                                rec.inSubset = false;
                                rec.rules = [...rec.rules, 'target-not-translated'];
                                if (!rec.cls)
                                    rec.detail = `the translation has no function for the target (${missing})`;
                            }
                        }
                        if (!rec.cls)
                            rec.cls = rec.inSubset ? 'in-subset' : 'subset';
                        if (rec.fuzzable) {
                            const files = new Map([...os.files, ...ns.files]);
                            if (hasSecret(files)) {
                                rec.fuzzable = false;
                                rec.detail = 'not extracted: text resembling a credential';
                            }
                            else {
                                let id = `${pr.date}_${pr.commit.slice(0, 8)}_${name.replace(/[^A-Za-z0-9_]/g, '_')}`;
                                // the same function name in two files of one commit
                                const prev = path.join(h.out, id, 'meta.json');
                                if (fs.existsSync(prev) && JSON.parse(fs.readFileSync(prev, 'utf8')).file !== pr.file)
                                    id += '_' + (0, util_1.sha1)(pr.file).slice(0, 6);
                                copySlice(os, path.join(h.out, id, 'old'));
                                copySlice(ns, path.join(h.out, id, 'new'));
                                (0, util_1.writeFile)(path.join(h.out, id, 'meta.json'), JSON.stringify({ repo: path.basename(h.repo), commit: pr.commit, parent: pr.parent, date: pr.date, subject: pr.subject, file: pr.file, entry: os.entry, function: name, inSubset: rec.inSubset, rules: rec.rules }, null, 2) + '\n');
                                rec.pair = id;
                            }
                        }
                    }
                }
                catch (e) {
                    rec.cls = 'error';
                    rec.detail = (0, util_1.truncate)(e.message, 200);
                }
                records.push(rec);
                append(rec);
            }
        }
        catch (e) {
            const rec = { commit: pr.commit, date: pr.date, subject: pr.subject, file: pr.file, name: '*', kind: '', cls: 'error', detail: (0, util_1.truncate)(e.message, 200), rules: [], externals: [], hostGlobals: [], fuzzable: false, inSubset: false };
            records.push(rec);
            append(rec);
        }
        append({ done: key });
        fs.rmSync(work, { recursive: true, force: true });
    }
    opts.log(`scanned ${processed} file change(s) in this run`);
    return records;
}
function summarizeScan(records) {
    const out = [];
    const by = (k) => records.filter(r => r.cls === k).length;
    out.push(`${records.length} changed functions: ${by('external')} use external modules, ${by('signature')} change their signature, ${by('inputs')} take inputs that are not generated, ${by('subset')} self-contained but outside the StrictTS subset, ${by('in-subset')} inside the subset (old and new), ${by('error')} errors`);
    out.push(`fuzzable (self-contained, generated inputs): ${records.filter(r => r.fuzzable).length}; extracted pairs: ${records.filter(r => r.pair).length}`);
    const rules = new Map();
    for (const r of records.filter(x => x.cls === 'subset' || (x.fuzzable && !x.inSubset)))
        for (const x of r.rules)
            rules.set(x, (rules.get(x) ?? 0) + 1);
    out.push('subset rules hit by self-contained functions: ' + [...rules].sort((a, b) => b[1] - a[1]).map(([k, v]) => `${k} ${v}`).join(', '));
    const ext = new Map();
    for (const r of records.filter(x => x.cls === 'external'))
        for (const x of r.externals)
            ext.set(x, (ext.get(x) ?? 0) + 1);
    out.push('external modules: ' + [...ext].sort((a, b) => b[1] - a[1]).slice(0, 12).map(([k, v]) => `${k} ${v}`).join(', '));
    return out.join('\n');
}
async function runHistoryPairs(h, opts, json) {
    const ids = fs.readdirSync(h.out).filter(d => fs.existsSync(path.join(h.out, d, 'meta.json'))).sort();
    const sel = opts.only ? ids.filter(d => opts.only.test(d)) : ids;
    const rows = [];
    const pend = [];
    for (const [i, id] of sel.entries()) {
        const meta = JSON.parse(fs.readFileSync(path.join(h.out, id, 'meta.json'), 'utf8'));
        const pOpts = { ...opts, only: undefined, work: path.join(opts.work, id), log: s => opts.log(`[${id}] ${s}`) };
        const a = await (0, pipeline_1.analyzePair)(path.join(h.out, id, 'old', meta.entry), path.join(h.out, id, 'new', meta.entry), pOpts, `h${String(i).padStart(3, '0')}u`);
        // only the function the commit changed (the slices also contain its dependencies)
        a.reports = a.reports.filter(r => r.name === meta.function);
        a.pend = a.pend.filter(p => p.r.name === meta.function);
        pend.push(...a.pend);
        rows.push({ id, meta, a });
    }
    (0, pipeline_1.leanPhase)(pend, opts, path.join(opts.work, 'lean'));
    const out = [];
    out.push(`${'pair'.padEnd(52)} ${'verdict'.padEnd(9)} evidence`);
    for (const r of rows) {
        (0, pipeline_1.finalize)(r.a.reports);
        const f = r.a.reports.find(x => x.status === 'changed');
        const v = f ? (f.verdict ?? 'UNKNOWN') + (f.verdict === 'REFUTED' && !(f.confirmedBy ?? []).includes('lean') ? '*' : '') : 'UNCHANGED';
        out.push(`${r.id.padEnd(52)} ${v.padEnd(9)} ${f ? (0, util_1.truncate)((0, report_1.evidence)(f), 220) : ''}`);
    }
    const vs = rows.map(r => r.a.reports.find(x => x.status === 'changed')?.verdict ?? 'UNCHANGED');
    out.push(`\n${rows.length} pairs: ${vs.filter(v => v === 'PROVED').length} PROVED, ${vs.filter(v => v === 'REFUTED').length} REFUTED, ${vs.filter(v => v === 'UNKNOWN').length} UNKNOWN`);
    process.stdout.write(out.join('\n') + '\n');
    if (json)
        (0, util_1.writeFile)(json, JSON.stringify(rows.map(r => ({ id: r.id, meta: r.meta, functions: (0, report_1.toJSON)(r.a.reports) })), null, 2) + '\n');
    return 0;
}

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
exports.runBench = runBench;
// Equivalence benchmark: DIR/NN_name/{old.ts,new.ts,expected} where `expected` starts with
// `equivalent` or `different`. All pairs are fuzzed first, then one shared Lean phase runs.
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const pipeline_1 = require("./pipeline");
const report_1 = require("./report");
const util_1 = require("./util");
function pairVerdict(a) {
    const ch = a.reports.filter(r => r.status === 'changed');
    if (!ch.length)
        return { verdict: 'UNCHANGED', lean: false, ev: 'no changed function' };
    const ref = ch.find(r => r.verdict === 'REFUTED');
    if (ref)
        return { verdict: 'REFUTED', lean: (ref.confirmedBy ?? []).includes('lean'), ev: `${ref.name}: ${(0, report_1.evidence)(ref)}` };
    if (ch.every(r => r.verdict === 'PROVED'))
        return { verdict: 'PROVED', lean: false, ev: ch.map(r => `${r.name}: ${(0, report_1.evidence)(r)}`).join('; ') };
    return { verdict: 'UNKNOWN', lean: false, ev: ch.filter(r => r.verdict !== 'PROVED').map(r => `${r.name}: ${(0, report_1.evidence)(r)}`).join('; ') };
}
async function runBench(dir, opts, json) {
    const root = path.resolve(dir);
    const names = fs.readdirSync(root).filter(d => /^\d+_/.test(d) && fs.existsSync(path.join(root, d, 'old.ts')) && fs.existsSync(path.join(root, d, 'new.ts'))).sort();
    const only = opts.only;
    const rows = [];
    const pend = [];
    for (const [i, name] of names.entries()) {
        if (only && !only.test(name))
            continue;
        const exp = fs.readFileSync(path.join(root, name, 'expected'), 'utf8').trim();
        const expected = exp.split(/\s+/)[0];
        const pOpts = { ...opts, only: undefined, work: path.join(opts.work, name), log: s => opts.log(`[${name}] ${s}`) };
        const a = await (0, pipeline_1.analyzePair)(path.join(root, name, 'old.ts'), path.join(root, name, 'new.ts'), pOpts, `b${String(i).padStart(2, '0')}u`);
        pend.push(...a.pend);
        rows.push({ name, expected, desc: exp.slice(expected.length).trim(), verdict: '', leanConfirmed: false, ok: 'unknown', evidence: '', a });
    }
    (0, pipeline_1.leanPhase)(pend, opts, path.join(opts.work, 'lean'));
    for (const r of rows) {
        (0, pipeline_1.finalize)(r.a.reports);
        const v = pairVerdict(r.a);
        r.verdict = v.verdict;
        r.leanConfirmed = v.lean;
        r.evidence = v.ev;
        if (v.verdict === 'UNKNOWN' || v.verdict === 'UNCHANGED')
            r.ok = 'unknown';
        else if ((v.verdict === 'PROVED') === (r.expected === 'equivalent'))
            r.ok = 'correct';
        else
            r.ok = 'WRONG';
    }
    // table
    const out = [];
    out.push(`${'pair'.padEnd(34)} ${'expected'.padEnd(10)} ${'verdict'.padEnd(9)} result   evidence`);
    for (const r of rows) {
        const v = r.verdict + (r.verdict === 'REFUTED' && !r.leanConfirmed ? '*' : '');
        out.push(`${r.name.padEnd(34)} ${r.expected.padEnd(10)} ${v.padEnd(9)} ${r.ok.padEnd(8)} ${(0, util_1.truncate)(r.evidence, 160)}`);
    }
    const eq = rows.filter(r => r.expected === 'equivalent'), ne = rows.filter(r => r.expected === 'different');
    const c = (xs, v) => xs.filter(r => r.verdict === v).length;
    out.push('');
    out.push(`equivalent pairs: ${eq.length}: PROVED ${c(eq, 'PROVED')}, UNKNOWN ${eq.length - c(eq, 'PROVED') - c(eq, 'REFUTED')}, REFUTED (wrong) ${c(eq, 'REFUTED')}`);
    // the statements of the proofs, strongest first (a pair counts under its weakest function)
    const order = ['all-worlds', 'allocated-arguments', 'allocated-arguments-strlen', 'allocated-arguments-objects', 'observational', 'old-no-panic'];
    const stmt = (r) => order[Math.max(...r.a.reports.filter(x => x.status === 'changed').map(x => order.indexOf(x.proof?.statement ?? 'all-worlds')))];
    const proved = eq.filter(r => r.verdict === 'PROVED');
    out.push(`  PROVED by statement: ${order.map(k => `${k} ${proved.filter(r => stmt(r) === k).length}`).join(', ')}`);
    out.push(`non-equivalent pairs: ${ne.length}: REFUTED ${c(ne, 'REFUTED')} (${ne.filter(r => r.verdict === 'REFUTED' && r.leanConfirmed).length} confirmed by Lean), UNKNOWN ${ne.length - c(ne, 'REFUTED') - c(ne, 'PROVED')}, PROVED (wrong) ${c(ne, 'PROVED')}`);
    const wrong = rows.filter(r => r.ok === 'WRONG');
    const decided = rows.filter(r => r.ok !== 'unknown');
    out.push(`precision ${decided.length ? ((decided.length - wrong.length) / decided.length * 100).toFixed(1) : '-'}% (${decided.length - wrong.length}/${decided.length} decided verdicts correct); ` +
        `recall: equivalences ${eq.length ? (c(eq, 'PROVED') / eq.length * 100).toFixed(1) : '-'}%, differences ${ne.length ? (c(ne, 'REFUTED') / ne.length * 100).toFixed(1) : '-'}%; WRONG verdicts: ${wrong.length}${wrong.length ? ' (' + wrong.map(r => r.name).join(', ') + ')' : ''}`);
    process.stdout.write(out.join('\n') + '\n');
    if (json)
        (0, util_1.writeFile)(json, JSON.stringify(rows.map(r => ({ name: r.name, expected: r.expected, desc: r.desc, verdict: r.verdict, leanConfirmed: r.leanConfirmed, result: r.ok, evidence: r.evidence, functions: (0, report_1.toJSON)(r.a.reports) })), null, 2) + '\n');
    return wrong.length ? 1 : 0;
}

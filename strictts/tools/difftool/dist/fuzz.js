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
exports.conclusive = exports.Runner = void 0;
exports.transpile = transpile;
exports.initMsg = initMsg;
exports.sameObs = sameObs;
exports.diffParts = diffParts;
exports.mineLiterals = mineLiterals;
exports.fuzzPair = fuzzPair;
// Differential fuzzing in Node: both versions of a slice run in their own child process on
// the same type-directed inputs; differing observations are shrunk and re-checked in fresh
// processes before they count as a counterexample.
const path = __importStar(require("path"));
const ts = __importStar(require("typescript"));
const child_process_1 = require("child_process");
const gen_1 = require("./gen");
const util_1 = require("./util");
/** Globals the runner's sandbox provides itself. */
const SANDBOX_GLOBALS = new Set(['console', 'setTimeout', 'setInterval', 'setImmediate', 'clearTimeout', 'clearInterval', 'clearImmediate',
    'queueMicrotask', 'structuredClone', 'URL', 'URLSearchParams', 'TextEncoder', 'TextDecoder', 'atob', 'btoa', 'performance']);
function transpile(files) {
    const out = {};
    for (const [rel, text] of files) {
        if (rel.endsWith('.d.ts'))
            continue;
        out[rel] = ts.transpileModule(text, {
            compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.CommonJS, alwaysStrict: true, esModuleInterop: false, jsx: ts.JsxEmit.React },
            fileName: rel,
        }).outputText;
    }
    return out;
}
class Runner {
    init;
    proc = null;
    seq = 0;
    waiters = new Map();
    readyP = null;
    constructor(init) {
        this.init = init;
    }
    start() {
        if (this.readyP)
            return this.readyP;
        this.readyP = new Promise((resolve, reject) => {
            const p = (0, child_process_1.fork)(path.join(__dirname, 'child.js'), [], {
                execArgv: ['--max-old-space-size=1024', '--stack-size=984'],
                stdio: ['ignore', 'ignore', 'pipe', 'ipc'],
            });
            this.proc = p;
            let stderr = '';
            p.stderr?.on('data', d => { stderr += String(d); if (stderr.length > 20000)
                stderr = stderr.slice(-20000); });
            p.on('message', (m) => {
                if (m.type === 'ready')
                    resolve();
                else if (m.type === 'result') {
                    const w = this.waiters.get(m.id);
                    this.waiters.delete(m.id);
                    w?.resolve(m.obs);
                }
                else if (m.type === 'error') {
                    const e = new Error(`runner: ${m.message}`);
                    reject(e);
                    for (const [, w] of this.waiters)
                        w.reject(e);
                    this.waiters.clear();
                }
            });
            p.on('exit', (code, sig) => {
                const e = new Error(`runner exited (${code ?? sig})${stderr ? ': ' + stderr.trim().split('\n').slice(-3).join(' / ') : ''}`);
                reject(e);
                for (const [, w] of this.waiters)
                    w.reject(e);
                this.waiters.clear();
                this.proc = null;
                this.readyP = null;
            });
            p.send(this.init);
        });
        return this.readyP;
    }
    async batch(inputs) {
        await this.start();
        const id = ++this.seq;
        const limit = 15000 + inputs.length * this.init.timeoutMs * 3;
        return new Promise((resolve, reject) => {
            const timer = setTimeout(() => { this.kill(); reject(new Error('runner batch timed out')); }, limit);
            this.waiters.set(id, { resolve: o => { clearTimeout(timer); resolve(o); }, reject: e => { clearTimeout(timer); reject(e); } });
            this.proc.send({ type: 'run', id, inputs });
        });
    }
    /** Run inputs; a crash (out of memory, …) is isolated to the input that caused it. */
    async run(inputs) {
        try {
            return await this.batch(inputs);
        }
        catch (e) {
            if (inputs.length === 1)
                return [{ kind: 'crash', o: `crash: ${e.message}`, out: [], args: [], strict: '', unhandled: [] }];
            const out = [];
            for (const inp of inputs)
                out.push(...await this.run([inp]));
            return out;
        }
    }
    kill() { if (this.proc) {
        this.proc.kill('SIGKILL');
        this.proc = null;
        this.readyP = null;
    } }
}
exports.Runner = Runner;
function initMsg(v, timeoutMs) {
    return { type: 'init', files: transpile(v.files), entry: v.entry, exportName: v.exportName, kind: v.kind, method: v.method, timeoutMs,
        hostGlobals: (v.hostGlobals ?? []).filter(g => !SANDBOX_GLOBALS.has(g)) };
}
function sameObs(a, b) {
    return a.o === b.o && a.out.join('\n') === b.out.join('\n') && a.args.join('\u0001') === b.args.join('\u0001') &&
        (a.self ?? '') === (b.self ?? '') && a.unhandled.join('\n') === b.unhandled.join('\n');
}
const conclusive = (o) => o.kind === 'ok' && !(o.host && o.host.length);
exports.conclusive = conclusive;
/** Which parts of two observations differ. */
function diffParts(a, b) {
    const d = [];
    if (a.o !== b.o)
        d.push('outcome');
    if (a.out.join('\n') !== b.out.join('\n'))
        d.push('console');
    if (a.args.join('\u0001') !== b.args.join('\u0001'))
        d.push('arguments after the call');
    if ((a.self ?? '') !== (b.self ?? ''))
        d.push('receiver after the call');
    if (a.unhandled.join('\n') !== b.unhandled.join('\n'))
        d.push('unhandled rejections');
    return d;
}
/** Literals of the sources (for input generation). */
/** Method names of the standard library (not used as candidate keys of client objects). */
const LIB_MEMBERS = new Set(['length', 'push', 'pop', 'shift', 'unshift', 'slice', 'splice', 'concat', 'join', 'map', 'filter', 'reduce', 'forEach',
    'find', 'findIndex', 'some', 'every', 'includes', 'indexOf', 'lastIndexOf', 'sort', 'reverse', 'flat', 'flatMap', 'fill', 'keys', 'values',
    'entries', 'get', 'set', 'has', 'delete', 'clear', 'add', 'size', 'trim', 'trimStart', 'trimEnd', 'toLowerCase', 'toUpperCase', 'split', 'replace',
    'replaceAll', 'startsWith', 'endsWith', 'charAt', 'charCodeAt', 'codePointAt', 'padStart', 'padEnd', 'repeat', 'substring', 'match', 'test',
    'toString', 'toFixed', 'then', 'catch', 'finally', 'log', 'floor', 'ceil', 'round', 'min', 'max', 'abs', 'now', 'isArray', 'from', 'of', 'assign',
    'hasOwn', 'is', 'parse', 'stringify', 'normalize', 'at', 'exec', 'apply', 'call', 'bind']);
function mineLiterals(texts) {
    const nums = new Set(), strs = new Set();
    const props = new Map();
    for (const text of texts) {
        const sf = ts.createSourceFile('x.ts', text, ts.ScriptTarget.ES2022, false);
        const walk = (n) => {
            if (ts.isNumericLiteral(n)) {
                const v = Number(n.text);
                if (Number.isFinite(v))
                    nums.add(v);
            }
            else if (ts.isStringLiteral(n) || ts.isNoSubstitutionTemplateLiteral(n)) {
                if (n.text.length <= 40 && !(n.parent && (ts.isImportDeclaration(n.parent) || ts.isExportDeclaration(n.parent))))
                    strs.add(n.text);
            }
            else if (ts.isTemplateHead(n) || ts.isTemplateMiddle(n) || ts.isTemplateTail(n)) {
                if (n.text && n.text.length <= 40)
                    strs.add(n.text);
            }
            else if (ts.isPropertyAccessExpression(n) && ts.isIdentifier(n.name) && !LIB_MEMBERS.has(n.name.text))
                props.set(n.name.text, (props.get(n.name.text) ?? 0) + 1);
            else if (ts.isElementAccessExpression(n) && ts.isStringLiteral(n.argumentExpression))
                props.set(n.argumentExpression.text, (props.get(n.argumentExpression.text) ?? 0) + 1);
            ts.forEachChild(n, walk);
        };
        walk(sf);
    }
    return { nums: [...nums].slice(0, 300), strs: [...strs].slice(0, 300), props: [...props].sort((a, b) => b[1] - a[1]).map(e => e[0]).slice(0, 16) };
}
async function fuzzPair(oldV, newV, sig, opts) {
    const t0 = Date.now();
    const res = { status: 'same', runs: 0, inconclusive: 0, notes: [], ms: 0 };
    const g = { rng: new util_1.Rng(opts.seed), table: sig.table, nums: opts.nums, strs: opts.strs, props: opts.props };
    const ro = new Runner(initMsg(oldV, opts.timeoutMs));
    const rn = new Runner(initMsg(newV, opts.timeoutMs));
    const both = async (inputs) => Promise.all([ro.run(inputs), rn.run(inputs)]);
    try {
        let inputs;
        try {
            inputs = (0, gen_1.boundaryInputs)(sig, g);
        }
        catch {
            inputs = [];
        }
        const seen = new Set();
        const fresh = (inp) => { const k = JSON.stringify(inp); if (seen.has(k))
            return false; seen.add(k); return true; };
        inputs = inputs.filter(fresh);
        const diffs = [];
        let strictOnly;
        let sameThrow;
        let harness = 0;
        let genFail = 0;
        let hostRuns = 0;
        const hostNames = new Set();
        // budget: slow or hanging functions (every run times out) must not stall a whole history run
        const budgetMs = 60000;
        while (res.runs < opts.runs && !diffs.length) {
            if (Date.now() - t0 > budgetMs || res.inconclusive >= 50) {
                res.notes.push(`fuzzing stopped after ${res.runs} runs (${res.inconclusive >= 50 ? 'too many inconclusive runs' : 'time budget'})`);
                break;
            }
            while (inputs.length < 100 && res.runs + inputs.length < opts.runs && genFail < 20 * opts.runs) {
                try {
                    const inp = (0, gen_1.genInput)(sig, g);
                    if (fresh(inp))
                        inputs.push(inp);
                    else
                        genFail++;
                }
                catch (e) {
                    res.status = 'error';
                    res.error = `input generation: ${e.message}`;
                    return res;
                }
            }
            if (!inputs.length)
                break;
            const batch = inputs.splice(0, res.inconclusive > 0 ? 20 : 100);
            const [oo, on] = await both(batch);
            res.runs += batch.length;
            batch.forEach((inp, i) => {
                const a = oo[i], b = on[i];
                if (a.kind === 'harness' || b.kind === 'harness') {
                    harness++;
                    if (harness === 1)
                        res.notes.push(a.kind === 'harness' ? a.o : b.o);
                    return;
                }
                if ((a.host ?? []).length || (b.host ?? []).length) {
                    hostRuns++;
                    for (const x of [...(a.host ?? []), ...(b.host ?? [])])
                        hostNames.add(x);
                }
                if (!(0, exports.conclusive)(a) || !(0, exports.conclusive)(b)) {
                    res.inconclusive++;
                    return;
                }
                if (!sameObs(a, b))
                    diffs.push({ input: inp, old: a, new: b, parts: diffParts(a, b), shrinkSteps: 0 });
                else if (a.strict !== b.strict && !strictOnly)
                    strictOnly = { input: inp, old: a, new: b, parts: ['key order or undefined-valued keys'], shrinkSteps: 0 };
                const thr = a.o.startsWith('throw ') ? a.o : null;
                sameThrow = sameThrow === undefined ? thr : (sameThrow === thr ? sameThrow : null);
            });
            if (genFail >= 20 * opts.runs && !inputs.length)
                break;
        }
        if (harness && harness === res.runs) {
            res.status = 'error';
            res.error = res.notes[0] ?? 'harness error';
            return res;
        }
        if (sameThrow)
            res.notes.push(`every run threw ${sameThrow.slice(6)} in both versions`);
        if (hostRuns)
            res.notes.push(`${hostRuns} run(s) touched host globals not modelled by the sandbox (${[...hostNames].join(', ')}); inconclusive`);
        if (res.inconclusive > hostRuns)
            res.notes.push(`${res.inconclusive - hostRuns} inconclusive run(s) (timeout, stack overflow or crash)`);
        if (strictOnly && !diffs.length) {
            res.strictOnly = strictOnly;
            res.notes.push('results differ only in object key order or undefined-valued keys (not observable in StrictTS)');
        }
        if (!diffs.length)
            return res;
        // shrink the smallest counterexample
        diffs.sort((x, y) => (0, gen_1.inputSize)(x.input) - (0, gen_1.inputSize)(y.input));
        let best = diffs[0];
        let budget = opts.shrinkBudget;
        let improved = true;
        while (improved && budget > 0) {
            improved = false;
            const cands = (0, gen_1.shrinkInput)(sig, best.input, g).filter(c => (0, gen_1.inputSize)(c) < (0, gen_1.inputSize)(best.input) || JSON.stringify(c).length < JSON.stringify(best.input).length);
            for (let i = 0; i < cands.length && budget > 0 && !improved; i += 25) {
                const chunk = cands.slice(i, i + 25);
                budget -= chunk.length;
                const [oo, on] = await both(chunk);
                for (let j = 0; j < chunk.length; j++) {
                    if ((0, exports.conclusive)(oo[j]) && (0, exports.conclusive)(on[j]) && !sameObs(oo[j], on[j])) {
                        best = { input: chunk[j], old: oo[j], new: on[j], parts: diffParts(oo[j], on[j]), shrinkSteps: best.shrinkSteps + 1 };
                        improved = true;
                        break;
                    }
                }
            }
        }
        // determinism: re-run in fresh processes
        ro.kill();
        rn.kill();
        const fo = new Runner(initMsg(oldV, opts.timeoutMs)), fn = new Runner(initMsg(newV, opts.timeoutMs));
        try {
            const [[o1], [n1]] = await Promise.all([fo.run([best.input]), fn.run([best.input])]);
            if (!sameObs(o1, best.old) || !sameObs(n1, best.new)) {
                res.notes.push('a difference was observed but did not reproduce in a fresh process (nondeterminism); not reported');
                return res;
            }
        }
        finally {
            fo.kill();
            fn.kill();
        }
        res.status = 'diff';
        res.cex = best;
        return res;
    }
    catch (e) {
        res.status = 'error';
        res.error = e.message;
        return res;
    }
    finally {
        ro.kill();
        rn.kill();
        res.ms = Date.now() - t0;
    }
}

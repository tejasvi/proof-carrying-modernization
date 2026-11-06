#!/usr/bin/env node
// Translation validation against Node: every function that the public-project modules emit
// (tools/public: es-toolkit and TheAlgorithms, strict and dyn, generic functions at <number>,
// callback functions with a fixed pure callback) runs on the same inputs under Node, on the
// original TypeScript, and under the Lean interpreter, on the translation (`#eval`, compiled
// code). Per input it compares the result value (printed deeply; -0 and NaN distinguished),
// normal return vs throw, console output, and the final contents of the arguments.
//
//   tools/run.sh 0.1 300 node tools/validate/validate.js plan
//   tools/run.sh 0.3 590 node tools/validate/validate.js run --shard I/N [--budget S] [--only REGEX] [--redo]
//   tools/run.sh 0.1 300 node tools/validate/validate.js report
//   VALIDATE_WORK=DIR ... run --panicked --single --record   (the functions with designed panics again: one driver
//                                  per input after a panic, every input's outcome kept)
//   VALIDATE_WORK=DIR ... sites [--shard I/N]     (Lean: the read where each designed panic happens)
//   VALIDATE_WORK=DIR ... checked                 (Node: the same inputs on tools/public/node's checked build)
//
// `plan` reads the emitted-function lists that `--emit-lean` writes next to each module
// (scratch/public/lean/Cov_*.funs.json; tools/public/coverage.sh and mono_emit.sh) and
// selects the functions a driver can call: top-level functions, arrows, methods and
// constructors that are not generic (generic functions are emitted as instances, reached
// through their <number> or callback wrappers; lifted inner functions through their parent).
// `run` validates the targets of one shard until the time budget is used (results are
// appended to scratch/validate/results/, so a shard can be resumed); `report` writes
// tools/validate/RESULTS.md and tools/validate/results.tsv.
//
// The machinery is strictts-diff's (tools/difftool): materialized copies of the sources,
// slices, type-directed inputs (boundary values, then random ones), a driver appended to the
// slice that builds each input with literals, calls the function and prints the outcome and
// the arguments with subset-only helpers, Node runs in a sandboxed child, batched Lean runs.
// Added here: more edge inputs (Maps and Sets with -0/0/NaN keys, arrays with NaN/-0, lone
// surrogates and surrogate pairs), the strict translation next to the dyn one (one Lean run
// when the two texts agree), and external calls (regular expressions, JSON, String.normalize):
// such drivers run under tests/difftest's harness, which records the calls, and the Lean run
// replays them (runMainTrace). Nothing runs in the projects' trees: the sources are copied
// into scratch/validate/t/<id>/ first.
'use strict';
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { spawnSync } = require('child_process');

const ROOT = path.resolve(__dirname, '..', '..');
const HERE = path.join(ROOT, 'tools', 'validate');
const WORK = process.env.VALIDATE_WORK ? path.resolve(process.env.VALIDATE_WORK) : path.join(ROOT, 'scratch', 'validate');
// VALIDATE_SUITES=FILE.json: another list of modules (e.g. tools/validate/suites_private.json, with
// `lean` the directory of the modules and `root` the directory their file paths are relative to;
// ${CM_ROOT} and ${NP_ROOT} as in tests/coverage/run_all.sh, ${LEAN} = VALIDATE_LEAN, default
// tests/coverage/lean)
const LEAN_DIR = path.join(ROOT, 'scratch', 'public', 'lean');
const HARNESS = path.join(HERE, 'harness.cjs');
require(path.join(ROOT, 'tools', 'difftool', 'dist', 'boot.js')); // `typescript` = the translator's copy
const dt = (m) => require(path.join(ROOT, 'tools', 'difftool', 'dist', m));
const { materialize } = dt('spec.js');
const { makeProject } = dt('project.js');
const { unitsOf } = dt('units.js');
const { sliceUnit } = dt('slice.js');
const { signatureOf, unsupportedIn } = dt('typedesc.js');
const { genInput, boundaryInputs, gen, num } = dt('gen.js');
const { mineLiterals, Runner, initMsg, conclusive, transpile } = dt('fuzz.js');
const { driverSlice, runProgramNode, programText } = dt('pipeline.js');
const { runLeanBatch } = dt('lean.js');
const { callText } = dt('literal.js');
const { Rng } = dt('util.js');
const frontend = require(path.join(ROOT, 'frontend', 'dist', 'index.js'));
const { f64Lean } = require(path.join(ROOT, 'frontend', 'dist', 'core.js'));
const ts = require('typescript');
const { leanJSStr, leanStrLit } = require(path.join(ROOT, 'frontend', 'dist', 'ty.js'));

/** The emitted modules: suite name, module, translator mode, directory the module's file paths are relative to. */
const SUITES = [
  { suite: 'es-toolkit strict', project: 'es-toolkit', kind: 'strict', mode: 'strict', module: 'Cov_es_toolkit_strict', root: 'scratch/projects/es-toolkit' },
  { suite: 'es-toolkit dyn', project: 'es-toolkit', kind: 'dyn', mode: 'dyn', module: 'Cov_es_toolkit_dyn', root: 'scratch/projects/es-toolkit' },
  { suite: 'es-toolkit generic@number', project: 'es-toolkit', kind: 'mono', mode: 'dyn', module: 'Cov_es_toolkit_mono_dyn', root: 'scratch/public/mono/es-toolkit-dyn' },
  { suite: 'es-toolkit fixed callbacks', project: 'es-toolkit', kind: 'cb', mode: 'dyn', module: 'Cov_es_toolkit_cb_dyn', root: 'scratch/public/mono/es-toolkit-cb-dyn' },
  { suite: 'TheAlgorithms strict', project: 'thealgorithms-ts', kind: 'strict', mode: 'strict', module: 'Cov_thealgorithms_ts_strict', root: 'scratch/projects/thealgorithms-ts' },
  { suite: 'TheAlgorithms dyn', project: 'thealgorithms-ts', kind: 'dyn', mode: 'dyn', module: 'Cov_thealgorithms_ts_dyn', root: 'scratch/projects/thealgorithms-ts' },
  { suite: 'TheAlgorithms generic@number', project: 'thealgorithms-ts', kind: 'mono', mode: 'dyn', module: 'Cov_thealgorithms_ts_mono_dyn', root: 'scratch/public/mono/thealgorithms-ts-dyn' },
];

function suites() {
  if (!process.env.VALIDATE_SUITES) return SUITES.map(x => ({ ...x, lean: LEAN_DIR }));
  const env = { CM_ROOT: process.env.CM_ROOT || '/home/user/another-project-app', NP_ROOT: process.env.NP_ROOT || '/home/user/Downloads/second-project',
    LEAN: process.env.VALIDATE_LEAN || 'tests/coverage/lean' };
  const sub = (x) => x.replace(/\$\{(\w+)\}/g, (_, k) => env[k] ?? '');
  return JSON.parse(fs.readFileSync(path.resolve(ROOT, process.env.VALIDATE_SUITES), 'utf8'))
    .map(x => ({ ...x, root: sub(x.root), lean: path.resolve(ROOT, sub(x.lean)) }));
}

const PER_FN = 40;        // inputs per function (boundary values first)
const NODE_MS = 50;       // inputs that take longer under Node are not sent to Lean
// The driver's main function holds every input as a literal, with each record and union type
// written out at every node: inputs of large record types make it megabytes of Lean text, and
// Lean's time grows with it. Above this size the driver keeps only its first inputs (boundary
// values first), at least MIN_INPUTS.
const MAIN_CAP = 150000;  // bytes of Lean text of the driver's main function
const MIN_INPUTS = 8;
const TRACE_CAP = 2e6;     // bytes of the JSON record of a driver's external calls
const LEAN_BATCH = Number(process.env.VALIDATE_LEAN_BATCH || 6);        // drivers per Lean process
const LEAN_TIMEOUT_S = Number(process.env.VALIDATE_LEAN_TIMEOUT || 300);
// (a driver of more Lean text than this is not run: its elaboration would not finish in a job)
const MAX_JOB_BYTES = Number(process.env.VALIDATE_MAX_JOB_BYTES || Infinity);

const sha1 = (s) => crypto.createHash('sha1').update(s).digest('hex');
const relWork = (abs) => path.relative(path.join(ROOT, 'scratch'), abs);
function writeFile(f, text) { fs.mkdirSync(path.dirname(f), { recursive: true }); fs.writeFileSync(f, text); }
/** Only directories below scratch/validate/t/ are ever replaced (difftool's materialize and driverSlice clear their destination). */
function under(dir, base) { const r = path.relative(base, dir); if (!r || r.startsWith('..') || path.isAbsolute(r)) throw new Error(`refusing ${dir}`); return dir; }

// ---------------------------------------------------------------------------------------
// plan

function plan() {
  const targets = new Map();
  const others = [];
  const emitted = {};
  const names = {};
  const SU = suites();
  for (const s of SU) {
    const file = path.join(s.lean, s.module + '.funs.json');
    if (!fs.existsSync(file)) throw new Error(`missing ${file} (tools/public/coverage.sh / mono_emit.sh with this translator)`);
    const funs = JSON.parse(fs.readFileSync(file, 'utf8'));
    emitted[s.suite] = funs.length;
    names[s.suite] = [...new Set(funs.map(f => f.name))];
    for (const f of funs) {
      const abs = f.file ? path.resolve(ROOT, s.root, f.file) : null;
      const direct = abs && !f.generic && ['fun', 'ctor', 'method', 'static'].includes(f.role);
      if (!direct) { others.push({ suite: s.suite, name: f.name, role: f.role, generic: f.generic, file: abs ? relWork(abs) : null }); continue; }
      const key = `${abs}:${f.line}`;
      let t = targets.get(key);
      if (!t) {
        const rel = s.relPrefix ? path.join(s.relPrefix, path.relative(s.root, abs)) : relWork(abs);
        t = { id: 't' + sha1(key).slice(0, 10), file: abs, rel, line: f.line, name: f.name, role: f.role, suites: [], modes: [] };
        targets.set(key, t);
      }
      if (!t.suites.includes(s.suite)) t.suites.push(s.suite);
      if (!t.modes.includes(s.mode)) t.modes.push(s.mode);
    }
  }
  const p = { created: new Date().toISOString(), suites: SU.map(s => ({ ...s, emitted: emitted[s.suite], names: names[s.suite] })), targets: [...targets.values()], others };
  writeFile(path.join(WORK, 'plan.json'), JSON.stringify(p, null, 1) + '\n');
  console.log(`plan: ${p.targets.length} functions to drive, ${others.length} emitted functions reached through callers; ` +
    SU.map(s => `${s.suite} ${emitted[s.suite]}`).join(', '));
}

// ---------------------------------------------------------------------------------------
// inputs

function resolve(d, table) { let x = d; for (let i = 0; x && x.k === 'ref' && i < 50; i++) x = table.get(x.id); return x; }

function simple(d0, table) {
  const d = resolve(d0, table);
  switch (d && d.k) {
    case 'num': return num(1); case 'str': return { t: 's', v: 'a' }; case 'bool': return { t: 'B', v: true };
    case 'big': return { t: 'b', v: '1' }; case 'undef': return { t: 'u' }; case 'null': return { t: 'z' }; case 'lit': return d.v;
    case 'arr': return { t: 'a', v: [] }; case 'map': return { t: 'm', v: [] }; case 'set': return { t: 'S', v: [] };
    default: return null;
  }
}

/** Collection elements that exercise SameValueZero, -0 printing and UTF-16 code units. */
function elemEdges(d0, table) {
  const d = resolve(d0, table);
  if (!d) return null;
  if (d.k === 'num') return [num(0), num(-0), num(NaN), num(NaN), num(-0), num(1)];
  if (d.k === 'str') return ['', '\ud800', '😀', '\udc00', '', '__proto__'].map(v => ({ t: 's', v }));
  return null;
}

function edgeValues(d0, g) {
  const d = resolve(d0, g.table);
  if (!d) return [];
  const tryGen = (x) => { try { return gen(x, g); } catch { return null; } };
  switch (d.k) {
    case 'set': { const e = elemEdges(d.t, g.table); return e ? [{ t: 'S', v: e }] : []; }
    case 'arr': { const e = elemEdges(d.t, g.table); return e ? [{ t: 'a', v: e }] : []; }
    case 'map': {
      const ks = elemEdges(d.key, g.table);
      if (!ks) return [];
      const vs = ks.map(() => tryGen(d.val));
      return vs.every(v => v) ? [{ t: 'm', v: ks.map((k, i) => [k, vs[i]]) }] : [];
    }
    case 'str': return ['😀😀', 'a\udc00b', '\udfff\ud800', 'x\u0000y'].map(v => ({ t: 's', v }));
    default: return [];
  }
}

/** One parameter at a time at an edge value, the others at simple values. */
function edgeInputs(sig, g) {
  const ps = sig.params.filter(p => !p.rest);
  const base = ps.map(p => simple(p.t, g.table) ?? (() => { try { return gen(p.t, g); } catch { return null; } })());
  if (base.some(b => b === null)) return [];
  const out = [];
  ps.forEach((p, i) => {
    for (const v of edgeValues(p.t, g)) {
      const args = base.slice();
      args[i] = v;
      const inp = { args };
      if (sig.self) inp.self = genInput(sig, g).self;
      out.push(inp);
    }
  });
  return out;
}

// ---------------------------------------------------------------------------------------
// private code (VALIDATE_SUITES set). Only slices copied into WORK run, each Node run a one-shot
// process inside a network namespace (bubblewrap --unshare-net; Node 22's permission model has no
// network switch) under Node's permission model: reads only inside WORK, no writes, no child
// processes, workers or addons, and a minimal environment. strictts-diff's runner (child.js: a vm
// context with its own module loader, no fs and no network globals) is copied into WORK and
// driven through a shim instead of an IPC fork. Excluded and counted: slices that import a
// package (or any non-relative module), slices that read process.env, and drivers whose external
// calls are not pure built-ins (only those are replayed: their recording calls nothing out).

const PRIVATE = !!process.env.VALIDATE_SUITES;
const RUNNER_DIR = path.join(WORK, 'runner');
const PURE_EXTERN = /^(RegExp\.(new|test|exec)|RegExpExecArray\.get:.*|RegExpMatchArray\.get:.*|String\.(match|matchAll|replace|replaceAll|split|search|normalize)|JSON\.(parse|stringify)|ArrayBuffer\.isView|encodeURIComponent|decodeURIComponent|encodeURI|decodeURI)$/;
const READS_ENV = /\bprocess\s*(\.\s*env\b|\[\s*['"`]env['"`]\s*\])|import\.meta\.env/;
const SHIM = `'use strict';
// one-shot driver of child.js (strictts-diff's runner) without an IPC channel
const fs = require('fs');
const msg = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const got = [];
process.send = (m) => { got.push(m); return true; };
require('./child.js');
(async () => {
  process.emit('message', msg.init);
  while (!got.some(m => m.type === 'ready' || m.type === 'error')) await new Promise(r => setTimeout(r, 2));
  if (!got.some(m => m.type === 'error')) process.emit('message', { type: 'run', id: 1, inputs: msg.inputs });
  while (!got.some(m => m.type === 'result' || m.type === 'error')) await new Promise(r => setTimeout(r, 2));
  process.stdout.write(JSON.stringify(got.find(m => m.type === 'result' || m.type === 'error')) + '\\n', () => process.exit(0));
})();
`;
let runnerReady = false;
function setupRunner() {
  if (runnerReady) return;
  fs.mkdirSync(RUNNER_DIR, { recursive: true });
  fs.copyFileSync(path.join(ROOT, 'tools', 'difftool', 'dist', 'child.js'), path.join(RUNNER_DIR, 'child.js'));
  fs.copyFileSync(path.join(ROOT, 'tests', 'difftest', 'harness.cjs'), path.join(RUNNER_DIR, 'difftest_harness.cjs'));
  writeFile(path.join(RUNNER_DIR, 'harness.cjs'), "'use strict';\nMath.random = () => 0;\nrequire('./difftest_harness.cjs');\n");
  writeFile(path.join(RUNNER_DIR, 'shim.js'), SHIM);
  runnerReady = true;
}
function sandboxed(args, opts) {
  setupRunner();
  const env = { PATH: process.env.PATH, LANG: 'C.UTF-8', ...(opts.env || {}) };
  return spawnSync('bwrap', ['--unshare-net', '--die-with-parent', '--ro-bind', '/', '/', '--dev', '/dev', '--proc', '/proc', '--',
    process.execPath, '--permission', `--allow-fs-read=${WORK}`, '--stack-size=984', '--max-old-space-size=1024', ...args],
    { encoding: 'utf8', maxBuffer: 64 << 20, ...opts, env });
}
let msgN = 0;
/** child.js on inputs (as Runner.run), sandboxed; a crash is isolated to its input. */
function sandboxRun(init, inputs) {
  const f = path.join(RUNNER_DIR, `msg_${process.pid}_${msgN++}.json`);
  setupRunner();
  fs.writeFileSync(f, JSON.stringify({ init, inputs }));
  const r = sandboxed([path.join(RUNNER_DIR, 'shim.js'), f], { timeout: 20000 + inputs.length * init.timeoutMs * 3 });
  fs.unlinkSync(f);
  let m = null;
  try { m = JSON.parse((r.stdout || '').trim().split('\n').pop()); } catch { m = null; }
  if (m && m.type === 'result') return m.obs;
  if (inputs.length > 1) return inputs.flatMap(i => sandboxRun(init, [i]));
  return [{ kind: 'crash', o: `crash: ${r.error ? r.error.message : (m && m.message ? m.message.slice(0, 200) : (r.stderr || '').slice(-200))}`, out: [], args: [], strict: '', unhandled: [] }];
}

// ---------------------------------------------------------------------------------------
// one target: inputs, Node run, translations

/** Edits of the slice copy that keep its runtime behaviour, so that the driver translates as the
 * emitted module does: (1) class members that the module leaves out (outside the subset) are
 * removed; the emitted functions never call them, since a function whose callee fails is left
 * out; (2) overload signatures are removed: they have no runtime effect, the module translates
 * the implementation, and the translator rejects calls of overloaded functions. */
function adaptSlice(sl, keep0, targetName) {
  // (instances of generic classes are emitted as `C<number>.m`)
  const keep = new Set([...keep0].map(n => n.replace(/<[^<>]*>/g, '')));
  const files = new Map(sl.files);
  const notes = [];
  for (const [rel, text] of sl.files) {
    if (!/\.(ts|tsx|mts|cts)$/.test(rel) || rel.endsWith('.d.ts')) continue;
    const sf = ts.createSourceFile(rel, text, ts.ScriptTarget.ES2022, true);
    const cuts = [];
    const withBody = new Set(sf.statements.filter(st => ts.isFunctionDeclaration(st) && st.name && st.body).map(st => st.name.text));
    for (const st of sf.statements) {
      if (ts.isFunctionDeclaration(st) && st.name && !st.body && withBody.has(st.name.text)) {
        cuts.push([st.getFullStart(), st.getEnd()]);
        notes.push(`overload signature of ${st.name.text} removed`);
      }
      if (!ts.isClassDeclaration(st) || !st.name) continue;
      const c = st.name.text;
      const memberName = (m) => m.name && (ts.isIdentifier(m.name) || ts.isPrivateIdentifier(m.name)) ? m.name.text : null;
      const implemented = new Set(st.members.filter(m => ts.isMethodDeclaration(m) && m.body).map(memberName));
      for (const m of st.members) {
        const mn = memberName(m);
        if (!mn) continue;
        let nm = null;
        if (ts.isMethodDeclaration(m) && !m.body && implemented.has(mn)) { cuts.push([m.getFullStart(), m.getEnd()]); notes.push(`overload signature of ${c}.${mn} removed`); continue; }
        if (ts.isMethodDeclaration(m) && m.body) nm = `${c}.${mn}`;
        else if (ts.isGetAccessorDeclaration(m)) nm = `${c}.get ${mn}`;
        else if (ts.isSetAccessorDeclaration(m)) nm = `${c}.set ${mn}`;
        if (nm && nm !== targetName && !keep.has(nm)) { cuts.push([m.getFullStart(), m.getEnd()]); notes.push(`${nm} removed (not in the emitted module)`); }
      }
      // (the class no longer has every member of the interfaces it implements: the clause, which
      // has no runtime effect, goes too)
      const imp = (st.heritageClauses || []).find(h => h.token === ts.SyntaxKind.ImplementsKeyword);
      if (imp && cuts.some(([a]) => a >= st.getStart() && a < st.getEnd())) { cuts.push([imp.getFullStart(), imp.getEnd()]); notes.push(`implements clause of ${c} removed`); }
    }
    if (!cuts.length) continue;
    let out = text;
    for (const [a, b] of cuts.sort((x, y) => y[0] - x[0])) out = out.slice(0, a) + out.slice(b);
    files.set(rel, out);
  }
  return { sl: { ...sl, files }, notes };
}

function blocks(out) {
  const res = [];
  let cur = null;
  for (const l of out.replace(/\r/g, '').split('\n')) {
    if (/^#\d+$/.test(l)) { if (cur) res.push(cur.join('\n')); cur = []; continue; }
    if (cur) cur.push(l); else cur = [l];
  }
  if (cur) res.push(cur.join('\n').replace(/\n+$/, ''));
  return res;
}

function recLean(v) {
  if (v === null) return '.null';
  if (v === true || v === false) return `(.bool ${v})`;
  if (v.u) return '.undef';
  if (v.n !== undefined) return `(.num ${f64Lean(v.n === '-0' ? -0 : Number(v.n))})`;
  if (v.s !== undefined) return `(.str ${leanJSStr(v.s)})`;
  if (v.h !== undefined) return `(.handle ${v.h})`;
  if (v.o) return `(.fields [${v.o.map(([k, x]) => `(${leanStrLitSafe(k)}, ${recLean(x)})`).join(', ')}])`;
  if (v.a) return `(.list [${v.a.map(recLean).join(', ')}])`;
  return '.other';
}

/** The replay of a recorded Node run (as tests/difftest/run.js does it). */
const loneSur = /[\ud800-\udbff](?![\udc00-\udfff])|(?<![\ud800-\udbff])[\udc00-\udfff]/g;
const leanStrLitSafe = (x) => leanStrLit(String(x).replace(loneSur, '\ufffd'));
function traceLean(ns, trace) {
  const calls = trace.calls.map(c => `{ name := ${leanStrLit(c.name)}, args := [${c.args.map(recLean).join(', ')}], ` +
    `out := ${c.err ? `.error (${leanStrLitSafe(c.err[0])}, ${leanStrLitSafe(c.err[1])})` : `.ok ${recLean(c.out)}`} }`);
  const nows = trace.nows.map(v => f64Lean(v.n === '-0' ? -0 : Number(v.n)));
  return [`def ${ns}.traceCalls : Array RecCall := #[${calls.join(',\n  ')}]`,
    `def ${ns}.traceNows : Array F64 := #[${nows.join(', ')}]`,
    `#eval runMainTrace ${ns}.program "${ns}" ${ns}.traceCalls ${ns}.traceNows`].join('\n');
}

/** Node run of a driver under the difftest harness (records external calls). */
function harnessRun(ds, dir, extra) {
  const js = transpile(ds.files);
  for (const [rel, code] of Object.entries(js)) {
    writeFile(path.join(dir, rel.replace(/\.(ts|tsx|mts|cts)$/, '.js')), code.replace(/require\("(\.\.?\/[^"]*?)\.(ts|tsx|mts|cts)"\)/g, 'require("$1.js")'));
  }
  const entry = path.join(dir, ds.entry.replace(/\.(ts|tsx|mts|cts)$/, '.js'));
  const r = PRIVATE
    ? sandboxed([path.join(RUNNER_DIR, 'harness.cjs'), entry], { env: { STRICTTS_TRACE: '1', STRICTTS_TRACE_EXTRA: extra.join(',') }, timeout: 60000, cwd: dir })
    : spawnSync(process.execPath, ['--stack-size=984', HARNESS, entry], { env: { ...process.env, STRICTTS_TRACE: '1', STRICTTS_TRACE_EXTRA: extra.join(',') }, encoding: 'utf8', timeout: 60000, cwd: dir, maxBuffer: 64 << 20 });
  const k = (r.stderr || '').indexOf('=====TRACE=====\n');
  const line = k >= 0 ? r.stderr.slice(k + 16).split('\n')[0] : null;
  // (a record of megabytes would be as many megabytes of Lean text to elaborate)
  if (line !== null && line.length > TRACE_CAP) return { out: (r.stdout || '').replace(/\n$/, ''), trace: null, tooLarge: line.length };
  const trace = line !== null ? JSON.parse(line) : null;
  return { out: (r.stdout || '').replace(/\n$/, ''), trace, err: r.error ? r.error.message : (r.status !== 0 && !r.stdout ? (r.stderr || '').slice(-500) : null) };
}

function translateDriver(ds, ns, mode) {
  const tr = (project) => {
    try { return frontend.translate({ files: project ? [] : [path.join(ds.dir, ds.entry)], project, namespace: ns, eval: true, strict: mode === 'strict', cwd: ds.dir }); }
    catch (e) { return { ok: false, diagnostics: `internal error: ${e.message}` }; }
  };
  let r = tr();
  // a slice that uses Node's globals (Buffer, URL, AbortSignal): the modules were emitted with
  // their projects' types, a driver by default has only the translator's host declarations; try
  // again with Node's types (the translator's copy of @types/node)
  if (!(r.ok && r.lean) && /\[ts(2304|2552|2591)\]/.test(r.diagnostics || '')) {
    const cfg = path.join(ds.dir, 'tsconfig.driver.json');
    writeFile(cfg, JSON.stringify({ compilerOptions: { target: 'ES2022', module: 'ESNext', moduleResolution: 'Bundler', lib: ['es2023'],
      types: ['node'], typeRoots: [path.join(ROOT, 'frontend', 'node_modules', '@types')], allowImportingTsExtensions: true, noEmit: true },
      files: [path.join(ds.dir, ds.entry)] }));
    const r2 = tr(cfg);
    if (r2.ok && r2.lean) r = r2;
  }
  // a slice of browser code (window, document, localStorage): the DOM's declarations
  if (!(r.ok && r.lean) && /\[ts(2304|2552|2584)\]/.test(r.diagnostics || '')) {
    const cfg = path.join(ds.dir, 'tsconfig.driver_dom.json');
    writeFile(cfg, JSON.stringify({ compilerOptions: { target: 'ES2022', module: 'ESNext', moduleResolution: 'Bundler', lib: ['es2023', 'dom'],
      types: [], allowImportingTsExtensions: true, noEmit: true }, files: [path.join(ds.dir, ds.entry)] }));
    const r3 = tr(cfg);
    if (r3.ok && r3.lean) r = r3;
  }
  if (!r.ok || !r.lean) return { ok: false, diag: (r.diagnostics || '').split('\n')[0].slice(0, 300) };
  return { ok: true, text: r.lean };
}

/** The function, its slice, signature and inputs (those that finish quickly under Node). */
async function prepUnit(t, seed, keep) {
  const tdir = under(path.join(WORK, 't', t.id), path.join(WORK, 't'));
  const res = { id: t.id, rel: t.rel, line: t.line, name: t.name, suites: t.suites, modes: t.modes, status: 'skipped', inputs: 0, perMode: {}, notes: [] };
  const set = materialize(t.file, under(path.join(tdir, 'src'), tdir), { repo: ROOT });
  const p = makeProject(set);
  const root = set.roots[0];
  const units = unitsOf(p, root, root);
  const u = units.find(x => x.line === t.line && x.name === t.name) ?? units.find(x => x.line === t.line) ?? units.find(x => x.name === t.name);
  if (!u) { res.reason = 'no function unit at this declaration'; return { res }; }
  if (u.isGeneric) { res.reason = 'generic'; return { res }; }
  if (u.isPrivate) { res.reason = 'private method (not callable from a driver)'; return { res }; }
  const sl0 = sliceUnit(p, u, under(path.join(tdir, 'slice'), tdir));
  if (!sl0.ok) { res.reason = `slice: ${sl0.reason}`; return { res }; }
  if (PRIVATE) {
    if (sl0.externals.length) { res.reason = 'excluded: imports a package or a non-relative module'; return { res }; }
    if ([...sl0.files.keys()].some(f => !/\.(ts|tsx|mts|cts)$/.test(f))) { res.reason = 'excluded: slice has a file that is not TypeScript'; return { res }; }
    if ([...sl0.files.values()].some(x => READS_ENV.test(x))) { res.reason = 'excluded: reads process.env'; return { res }; }
  }
  const ad = adaptSlice(sl0, keep, u.name);
  const sl = ad.sl;
  res.notes.push(...ad.notes);
  const sig = signatureOf(p, u);
  const bad = [...sig.params, ...(sig.self ? sig.self.ctor : [])].map(q => unsupportedIn(q.rest && q.t.k === 'arr' ? q.t.t : q.t, sig.table)).find(x => x);
  if (bad) { res.reason = `inputs not generated (${bad})`; return { res }; }
  const lits = mineLiterals([...sl.files.values()]);
  // (private code: string literals that look like keys or tokens are not used as inputs)
  const secretish = (x) => /^(sk-|sk_|AIza|ghp_|gho_|xox[abp]-|-----BEGIN)/.test(x) || (x.length >= 20 && !/\s/.test(x));
  if (process.env.VALIDATE_SUITES) lits.strs = lits.strs.filter(x => !secretish(x));
  const g = { rng: new Rng(seed), table: sig.table, nums: lits.nums, strs: lits.strs, props: lits.props };
  const inputs = [];
  const seen = new Set();
  const add = (i) => { const k = JSON.stringify(i); if (!seen.has(k)) { seen.add(k); inputs.push(i); } };
  try { boundaryInputs(sig, g).slice(0, PER_FN >> 1).forEach(add); } catch { /* none */ }
  try { edgeInputs(sig, g).forEach(add); } catch { /* none */ }
  for (let k = 0; inputs.length < PER_FN + 8 && k < PER_FN * 5; k++) { try { add(genInput(sig, g)); } catch { break; } }
  if (!inputs.length) { res.reason = 'no input generated'; return { res }; }
  // inputs that finish quickly under Node (the Lean interpreter is much slower)
  const im = initMsg({ files: sl.files, entry: sl.entry, exportName: sl.exportName, kind: u.kind, method: u.cls ? u.name.slice(u.cls.length + 1) : undefined }, 500);
  let obs;
  if (PRIVATE) obs = sandboxRun(im, inputs);
  else { const runner = new Runner(im); try { obs = await runner.run(inputs); } finally { runner.kill(); } }
  const limit = (o) => /Invalid (string|array) length|Array buffer allocation failed/.test(o.o);
  const kept = inputs.filter((_, k) => conclusive(obs[k]) && (obs[k].ms ?? 0) < NODE_MS && !limit(obs[k]));
  const slow = inputs.filter((_, k) => conclusive(obs[k]) && (obs[k].ms ?? 0) >= NODE_MS).length;
  const inconcl = inputs.filter((_, k) => !conclusive(obs[k])).length;
  const limited = obs.filter(limit).length;
  if (slow) res.notes.push(`${slow} input(s) slower than ${NODE_MS} ms under Node`);
  if (inconcl) res.notes.push(`${inconcl} input(s) inconclusive under Node: ${[...new Set(obs.filter(o => !conclusive(o)).map(o => o.kind + (o.host && o.host.length ? ' ' + o.host.join(',') : '')))].join('; ')}`);
  if (limited) res.notes.push(`${limited} input(s) hit an engine length limit`);
  if (!kept.length) { res.reason = `no input finishes quickly under Node (${obs[0] ? obs[0].o : '?'})`; return { res }; }
  res.generated = inputs.length;
  return { res, t, tdir, u, sl, sig, kept };
}

/** A driver for `inputs` (round `round`): its Node output and one Lean job per distinct translation. */
async function prepDriver(ctx, inputs, round) {
  const { t, tdir, u, sl, sig, res } = ctx;
  const ds = driverSlice(sl, under(path.join(tdir, `drv${round}`), tdir), u, sig, inputs);
  const jobs = [];
  let extern = false;
  const externNames = new Set();
  const skippedModes = {};
  for (const mode of t.modes) {
    const ns = `V_${t.id}_${mode}_${round}`;
    const tr = translateDriver(ds, ns, mode);
    if (!tr.ok) { skippedModes[mode] = `driver outside the subset: ${tr.diag}`; continue; }
    if (/\.extern(Async)? \(args/.test(tr.text)) extern = true;
    for (const m of tr.text.matchAll(/\.extern(?:Async)? \(args := .*?\) \(t := .*?\) "([^"]+)"/g)) externNames.add(m[1]);
    const norm = tr.text.split(ns).join('§NS');
    const same = jobs.find(j => j.norm === norm);
    if (same) { same.modes.push(mode); res.sharedModes = true; continue; }
    jobs.push({ ns, modes: [mode], norm, text: tr.text });
  }
  if (!jobs.length) return { skippedModes };
  if (jobs.some(j => j.text.length > MAX_JOB_BYTES)) return { error: `not run: driver over ${Math.round(MAX_JOB_BYTES / 1000)} KB of Lean text`, skippedModes, excluded: true };
  if (round === 0 && inputs.length > MIN_INPUTS) {
    const mainSize = Math.max(...jobs.map(j => { const i = j.text.indexOf('def «__dt_mainDef» : FunDef'); if (i < 0) return 0; const e = j.text.indexOf('\ndef ', i + 1); return (e < 0 ? j.text.length : e) - i; }));
    if (mainSize > MAIN_CAP) {
      const k = Math.max(MIN_INPUTS, Math.floor(inputs.length * MAIN_CAP / mainSize));
      if (k < inputs.length) {
        res.notes.push(`${inputs.length - k} input(s) over the driver size cap`);
        ctx.kept = inputs.slice(0, k);
        return prepDriver(ctx, ctx.kept, round);
      }
    }
  }
  let nodeOut, trace = null;
  if (PRIVATE && extern) {
    const impure = [...externNames].filter(n => !PURE_EXTERN.test(n));
    if (impure.length) return { error: `excluded: external call that is not a pure built-in (${impure.length} name(s))`, skippedModes, excluded: true };
  }
  if (extern) {
    // the harness records regular expressions, JSON and String.normalize itself; other host functions by name
    const extra = [...externNames].filter(n => !/^(RegExp|RegExpExecArray|RegExpMatchArray|String|JSON)\./.test(n) && /^[A-Za-z_$][\w$]*(\.[A-Za-z_$][\w$]*)?$/.test(n));
    const h = harnessRun(ds, under(path.join(tdir, `js${round}`), tdir), extra);
    if (h.tooLarge) return { error: `excluded: record of the external calls over ${TRACE_CAP / 1e6} MB (too large to replay in Lean)`, skippedModes, excluded: true };
    if (h.err && !h.out) return { error: `node harness: ${h.err}`, skippedModes };
    if (!h.trace) return { error: 'node harness: no trace recorded', skippedModes };
    nodeOut = h.out; trace = h.trace;
  } else if (PRIVATE) nodeOut = programText(sandboxRun(initMsg({ files: ds.files, entry: ds.entry, exportName: '', kind: 'program' }, 30000), [{ args: [] }])[0]);
  else nodeOut = await runProgramNode(ds, 30000);
  res.extern = res.extern || extern;
  for (const j of jobs) {
    // (the call-unfolding lemmas are not needed to run the program; for large programs they are
    // most of the elaboration time)
    let body = j.text.slice(j.text.indexOf('\nnamespace ') + 1);
    const cl = body.indexOf('/-! Call-unfolding lemmas');
    if (cl >= 0) body = body.slice(0, cl) + body.slice(body.indexOf(`\nend ${j.ns}\n`, cl) + 1);
    const ev = `#eval runMain ${j.ns}.program "${j.ns}"`;
    // (large programs: the elaboration of their call lemmas can need more than the default heartbeats)
    j.body = 'set_option maxHeartbeats 2000000\n' + (extern ? body.replace(ev, () => traceLean(j.ns, trace)) : body);
    j.names = [...j.text.matchAll(/^def «.+?Ref» : FunRef .* := ⟨\d+, "(.+?)"⟩$/gm)].map(m => m[1]);
    delete j.norm; delete j.text;
  }
  return { jobs, nodeBlocks: blocks(nodeOut), inputs, skippedModes };
}

// ---------------------------------------------------------------------------------------
// comparison

const OUTCOME = /^(return|throw|resolve|reject) /;
/** Panics of the semantics where TypeScript's typing is unsound and JavaScript continues with
 * `undefined` (DESIGN.md §1.4): a difference by design, not a translation error. */
const DESIGNED_PANIC = /^\[PANIC (array index out of bounds|typed array index out of bounds|non-null assertion on undefined|read of an uninitialised field|array write would create a hole|array length extension would create holes|array read at a non-index key|typed array read at a non-index key|read of an inherited Object\.prototype property|assignment to __proto__)\]$/;

/** Which observations differ between a Node block and a Lean block. */
function diffParts(nb, lb) {
  const split = (b) => {
    const ls = (b ?? '').split('\n');
    const o = ls.findIndex(l => OUTCOME.test(l));
    const pick = (re) => ls.filter(l => re.test(l)).join('\n');
    return { console: (o >= 0 ? ls.slice(0, o) : ls.filter(l => !/^(args|self) /.test(l) && !/^\[/.test(l))).join('\n'), outcome: o >= 0 ? ls[o] : '', args: pick(/^args /), self: pick(/^self /), status: pick(/^\[/) };
  };
  const a = split(nb), b = split(lb);
  return ['outcome', 'console', 'args', 'self', 'status'].filter(k => a[k] !== b[k]);
}

/** Compare one driver run; a run that the semantics stops with a panic at input k is compared up to k. */
function compareRun(d, leanOut, acc, u) {
  const nb = d.nodeBlocks, lb = blocks(leanOut);
  const last = lb.length - 1;
  const lastLines = (lb[last] ?? '').split('\n');
  // (after a panic, a replayed run adds `[TRACE: k of the n external calls …]` lines)
  const pIdx = lastLines.findIndex(l => /^\[PANIC /.test(l));
  const panic = pIdx >= 0 && lastLines.slice(pIdx + 1).every(l => /^\[TRACE: /.test(l)) ? lastLines[pIdx] : null;
  const upto = panic ? last : Math.max(nb.length, lb.length) - 1;
  for (let k = 0; k <= upto && k < d.inputs.length; k++) {
    acc.inputs++;
    const nk = nb[k] ?? '', lk = lb[k] ?? '';
    if (panic && k === last) {
      // Lean stopped here: its block is the console output before the panic
      const nls = nk.split('\n');
      const o = nls.findIndex(l => OUTCOME.test(l));
      const before = lastLines.slice(0, pIdx).join('\n');
      const nodeBefore = (o >= 0 ? nls.slice(0, o) : nls).join('\n');
      if (DESIGNED_PANIC.test(panic) && before === nodeBefore) { acc.designed.push({ input: callText(u.name, d.inputs[k].args, d.inputs[k].self, u.cls, u.kind), panic, node: nk }); acc.per.push({ input: d.inputs[k], status: 'designed', panic }); continue; }
    }
    if (nk === lk) { acc.match++; acc.per.push({ input: d.inputs[k], status: 'match' }); continue; }
    acc.mismatch.push({ k: acc.inputs - 1, input: callText(u.name, d.inputs[k].args, d.inputs[k].self, u.cls, u.kind), node: nk || '<missing>', lean: lk || '<missing>', parts: diffParts(nk, lk) });
    acc.per.push({ input: d.inputs[k], status: 'mismatch' });
  }
  // inputs after a panic are run again in a further driver
  return panic && last + 1 < d.inputs.length ? d.inputs.slice(last + 1) : null;
}

// ---------------------------------------------------------------------------------------
// run

let SINGLE = false;      // --single: after a panic, one driver per remaining input
let RECORD = false;      // --record: keep every input's outcome in the result
const MAX_DRIVERS = 16;   // drivers per function (a panic ends a Lean run: the inputs after it go to further drivers)

const DEFAULT_WORK = path.join(ROOT, 'scratch', 'validate');
/** The plan of WORK, else of the default work directory (VALIDATE_WORK for a second pass). */
function loadPlan() {
  const f = fs.existsSync(path.join(WORK, 'plan.json')) ? path.join(WORK, 'plan.json') : path.join(DEFAULT_WORK, 'plan.json');
  return JSON.parse(fs.readFileSync(f, 'utf8'));
}

function resultsFile(shard) { return path.join(WORK, 'results', `shard_${shard.i}_of_${shard.n}.jsonl`); }

function loadResults(work = WORK) {
  const dir = path.join(work, 'results');
  const by = new Map();
  if (!fs.existsSync(dir)) return by;
  for (const f of fs.readdirSync(dir).sort()) {
    if (!f.endsWith('.jsonl')) continue;
    for (const l of fs.readFileSync(path.join(dir, f), 'utf8').split('\n')) {
      if (!l.trim()) continue;
      const r = JSON.parse(l);
      by.set(r.id, r);
    }
  }
  return by;
}

function finish(ctx) {
  const r = ctx.res;
  for (const mode of r.modes) {
    if (ctx.skippedModes[mode] && !ctx.acc[mode]) { r.perMode[mode] = { status: 'skipped', reason: ctx.skippedModes[mode] }; continue; }
    const a = ctx.acc[mode];
    if (!a) { r.perMode[mode] = { status: 'error', reason: ctx.error || 'no result' }; continue; }
    if (a.error && !a.inputs) { r.perMode[mode] = { status: 'error', reason: a.error }; continue; }
    r.perMode[mode] = {
      status: a.mismatch.length ? 'MISMATCH' : 'match', inputs: a.inputs, match: a.match, mismatchedInputs: a.mismatch.length,
      designedPanics: a.designed.length, drivers: a.rounds, notCompared: a.notCompared || 0,
      first: a.mismatch[0], partsAll: [...new Set(a.mismatch.flatMap(m => m.parts))], mismatches: a.mismatch.slice(0, 5),
      perInput: RECORD ? a.per : undefined,
      panics: [...new Set(a.designed.map(x => x.panic))], designedFirst: a.designed[0], error: a.error,
    };
  }
  const st = Object.values(r.perMode).map(x => x.status);
  r.status = st.includes('MISMATCH') ? 'MISMATCH' : st.includes('error') ? 'error' : st.includes('match') ? 'match' : 'skipped';
  r.inputs = Math.max(0, ...Object.values(r.perMode).map(x => x.inputs || 0));
  r.names = [...new Set(ctx.names)];
  if (r.status === 'skipped' && !r.reason) r.reason = Object.values(r.perMode).map(m => m.reason).filter(Boolean)[0];
  if (r.status === 'error' && !r.reason) r.reason = Object.values(r.perMode).map(m => m.reason).filter(Boolean)[0];
  return r;
}

async function runShard(args) {
  const t0 = Date.now();
  const m = (args.shard ?? '0/1').match(/^(\d+)\/(\d+)$/);
  if (!m) throw new Error('--shard I/N');
  const shard = { i: Number(m[1]), n: Number(m[2]) };
  const budget = Number(args.budget ?? 420) * 1000;
  const p = loadPlan();
  const done = args.redo ? new Map() : loadResults();
  const only = args.only ? new RegExp(args.only) : null;
  const namesOf = new Map(p.suites.map(s => [s.suite, s.names || []]));
  // --panicked: the functions whose drivers stopped at designed panics in the main run
  const main = args.panicked ? loadResults(DEFAULT_WORK) : null;
  const panicked = (t) => { const r = main.get(t.id); return !!r && Object.values(r.perMode).some(m => (m.designedPanics || 0) > 0 || (m.notCompared || 0) > 0); };
  const mine = p.targets.filter((t, i) => i % shard.n === shard.i && (!only || only.test(`${t.rel}:${t.name}`)) && (!main || panicked(t)) && !done.has(t.id));
  const out = resultsFile(shard);
  fs.mkdirSync(path.dirname(out), { recursive: true });
  const record = (r) => fs.appendFileSync(out, JSON.stringify(r) + '\n');
  const log = (r) => console.log(`  ${r.status} ${r.rel}:${r.line} ${r.name}${r.status === 'match' || r.status === 'MISMATCH' ? ` (${r.inputs} inputs${r.extern ? ', externs replayed' : ''})` : ''}` +
    `${r.reason ? ': ' + r.reason.slice(0, 200) : ''}${r.status === 'MISMATCH' ? ' ' + JSON.stringify(Object.values(r.perMode).find(x => x.first).first).slice(0, 400) : ''}`);
  console.log(`shard ${shard.i}/${shard.n}: ${mine.length} functions to validate`);
  let n = 0, next = 0, batchNo = 0;
  let queue = [];   // drivers waiting for Lean: { ctx, d }
  while (next < mine.length || queue.length) {
    const over = Date.now() - t0 > budget;
    // fill a batch: follow-up drivers first, then new functions (not after the budget)
    while (queue.length < LEAN_BATCH && next < mine.length && !over) {
      const t = mine[next++];
      const ts0 = Date.now();
      let ctx;
      try { ctx = await prepUnit(t, parseInt(t.id.slice(1, 9), 16), new Set(t.suites.flatMap(s => namesOf.get(s) || []))); }
      catch (e) { ctx = { res: { id: t.id, rel: t.rel, line: t.line, name: t.name, suites: t.suites, modes: t.modes, status: 'error', inputs: 0, perMode: {}, reason: `prepare: ${e.message.slice(0, 300)}` } }; }
      if (!ctx.kept) { ctx.res.prepSecs = (Date.now() - ts0) / 1000; record(ctx.res); n++; log(ctx.res); continue; }
      ctx.acc = {}; ctx.names = []; ctx.skippedModes = {}; ctx.drivers = 1; ctx.pending = 1; ctx.t0 = ts0;
      let d;
      try { d = await prepDriver(ctx, ctx.kept, 0); } catch (e) { d = { error: `driver: ${e.message.slice(0, 300)}`, skippedModes: {} }; }
      Object.assign(ctx.skippedModes, d.skippedModes);
      if (!d.jobs) { ctx.error = d.error; const r = finish(ctx); if (d.error) { r.status = d.excluded ? 'skipped' : 'error'; r.reason = d.error; } r.prepSecs = (Date.now() - ts0) / 1000; record(r); n++; log(r); continue; }
      queue.push({ ctx, d });
    }
    if (!queue.length) break;
    const batch = queue.splice(0, LEAN_BATCH);
    const evals = batch.flatMap(b => b.d.jobs.map(j => ({ id: j.ns, t: { ns: j.ns, body: j.body } })));
    const batchFile = path.join(WORK, 'lean', `s${shard.i}of${shard.n}_${String(batchNo++).padStart(4, '0')}.lean`);
    const res = runLeanBatch(batchFile, [], evals, LEAN_TIMEOUT_S);
    if (evals.length > 1 && evals.some(e => !(res.evals.get(e.id) || {}).ok)) {
      for (const e of evals) {
        if ((res.evals.get(e.id) || {}).ok) continue;
        const r1 = runLeanBatch(batchFile.replace(/\.lean$/, `_${e.id}.lean`), [], [e], Math.min(200, LEAN_TIMEOUT_S));
        res.evals.set(e.id, r1.evals.get(e.id) || { ok: false, out: '', errors: ['no result'] });
      }
    }
    for (const { ctx, d } of batch) {
      ctx.pending--;
      let rest = null;
      for (const j of d.jobs) {
        ctx.names.push(...j.names);
        const e = res.evals.get(j.ns);
        for (const mode of j.modes) {
          const a = ctx.acc[mode] ?? (ctx.acc[mode] = { inputs: 0, match: 0, mismatch: [], designed: [], rounds: 0, per: [] });
          a.rounds++;
          if (!e || !e.ok) { a.error = `lean: ${((e && e.errors) || ['no result']).join(' / ').slice(0, 400)}`; a.notCompared = (a.notCompared || 0) + d.inputs.length; continue; }
        }
        if (!e || !e.ok) continue;
        // modes sharing one translation share the comparison
        const acc0 = ctx.acc[j.modes[0]];
        const r0 = compareRun(d, e.out, acc0, ctx.u);
        for (const mode of j.modes.slice(1)) {
          const a = ctx.acc[mode];
          Object.assign(a, { inputs: acc0.inputs, match: acc0.match, mismatch: acc0.mismatch, designed: acc0.designed, per: acc0.per });
        }
        if (r0) rest = r0;
      }
      if (rest) {
        // the inputs after the panic: in two further drivers when there are many (a panic in one
        // half does not stop the other)
        const chunks = SINGLE ? rest.map(x => [x]) : rest.length > 6 ? [rest.slice(0, rest.length >> 1), rest.slice(rest.length >> 1)] : [rest];
        for (const ch of chunks) {
          if (ctx.drivers < (SINGLE ? 200 : MAX_DRIVERS) && Date.now() - t0 < budget + 60000) {
            let d2;
            try { d2 = await prepDriver(ctx, ch, ctx.drivers++); } catch (e) { d2 = { error: `driver: ${e.message.slice(0, 300)}` }; }
            if (d2.jobs) { queue.unshift({ ctx, d: d2 }); ctx.pending++; continue; }
            for (const a of Object.values(ctx.acc)) a.note = d2.error || 'follow-up driver not translated';
          }
          for (const a of Object.values(ctx.acc)) a.notCompared = (a.notCompared || 0) + ch.length;
        }
      }
      if (ctx.pending > 0) continue;
      const r = finish(ctx);
      r.secs = (Date.now() - ctx.t0) / 1000;
      record(r); n++; log(r);
    }
  }
  console.log(`shard ${shard.i}/${shard.n}: ${n} functions recorded in ${((Date.now() - t0) / 1000).toFixed(0)} s` + (next < mine.length ? `; ${mine.length - next} left (run again)` : ''));
}

// ---------------------------------------------------------------------------------------
// sites: where the designed panics happen. The Lean side runs each designed-panic input again
// on a copy of the slice whose checked reads (the reads that tools/public/node/build.js checks:
// `a[i]` whose type excludes undefined, `x!`, declared class fields) first print their source
// position: the last position printed before the panic is the read where Lean stopped. The
// Node side runs every recorded input on the checked build (tools/validate/checked_run.js),
// which throws at the first read whose value the type excludes.

const BAD_FLAGS = ts.TypeFlags.Undefined | ts.TypeFlags.Void | ts.TypeFlags.Any | ts.TypeFlags.Unknown | ts.TypeFlags.Null;
function excludesUndefined(checker, node, typeParamsToo = false) {
  const t = checker.getTypeAtLocation(node);
  const parts = t.isUnion() ? t.types : [t];
  return !parts.some(q => (q.flags & BAD_FLAGS) || (!typeParamsToo && (q.flags & ts.TypeFlags.TypeParameter)));
}
const ASSIGN_OPS = new Set([ts.SyntaxKind.EqualsToken, ts.SyntaxKind.PlusEqualsToken, ts.SyntaxKind.MinusEqualsToken,
  ts.SyntaxKind.AsteriskEqualsToken, ts.SyntaxKind.SlashEqualsToken, ts.SyntaxKind.PercentEqualsToken,
  ts.SyntaxKind.AsteriskAsteriskEqualsToken, ts.SyntaxKind.LessThanLessThanEqualsToken,
  ts.SyntaxKind.GreaterThanGreaterThanEqualsToken, ts.SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken,
  ts.SyntaxKind.AmpersandEqualsToken, ts.SyntaxKind.BarEqualsToken, ts.SyntaxKind.CaretEqualsToken,
  ts.SyntaxKind.AmpersandAmpersandEqualsToken, ts.SyntaxKind.BarBarEqualsToken, ts.SyntaxKind.QuestionQuestionEqualsToken]);
/** (as tools/public/node/build.js) is `n` written, deleted or called rather than read? */
function notARead(n) {
  let c = n, q = n.parent;
  while (q && (ts.isParenthesizedExpression(q) || ts.isArrayLiteralExpression(q) || ts.isObjectLiteralExpression(q)
      || ts.isPropertyAssignment(q) || ts.isShorthandPropertyAssignment(q) || ts.isSpreadElement(q) || ts.isSpreadAssignment(q))) {
    if (ts.isBinaryExpression(q.parent) && q.parent.left === q && q.parent.operatorToken.kind === ts.SyntaxKind.EqualsToken) return true;
    c = q; q = q.parent;
  }
  if (!q) return false;
  if (ts.isBinaryExpression(q) && q.left === c && ASSIGN_OPS.has(q.operatorToken.kind)) return true;
  if ((ts.isPrefixUnaryExpression(q) || ts.isPostfixUnaryExpression(q))
      && (q.operator === ts.SyntaxKind.PlusPlusToken || q.operator === ts.SyntaxKind.MinusMinusToken)) return true;
  if (ts.isDeleteExpression(q) || ts.isTypeOfExpression(q)) return true;
  if (ts.isCallExpression(q) && q.expression === c) return true;
  if ((ts.isForOfStatement(q) || ts.isForInStatement(q)) && q.initializer === c) return true;
  return false;
}
function isClassField(checker, n) {
  const sym = checker.getSymbolAtLocation(n.name);
  const d = sym && sym.valueDeclaration;
  return !!d && (ts.isPropertyDeclaration(d) || (ts.isParameter(d) && ts.isConstructorDeclaration(d.parent)));
}

/** The file with a position marker before every checked read (`basename:line:col` as build.js reports it). */
function markSites(p, rel) {
  const sf = p.sf(rel);
  const checker = p.checker;
  const base = path.basename(rel);
  const where = (n) => { const q = sf.getLineAndCharacterOfPosition(n.getStart(sf)); return `${base}:${q.line + 1}:${q.character + 1}`; };
  let used = false;
  const tr = (ctx) => (root) => {
    const f = ctx.factory;
    // (`this` gets its class as the type argument: the translator does not instantiate a type
    // parameter at the polymorphic `this` type)
    const mark = (s, e, orig) => {
      used = true;
      let targs;
      if (orig && orig.kind === ts.SyntaxKind.ThisKeyword) {
        let c = orig.parent;
        while (c && !ts.isClassDeclaration(c)) c = c.parent;
        if (c && c.name) targs = [f.createTypeReferenceNode(c.name.text, c.typeParameters ? c.typeParameters.map(tp => f.createTypeReferenceNode(tp.name.text)) : undefined)];
      }
      return f.createCallExpression(f.createIdentifier('__vsite'), targs, [f.createStringLiteral(s), e]);
    };
    const visit = (n) => {
      if (ts.isElementAccessExpression(n) && !n.questionDotToken && !notARead(n) && excludesUndefined(checker, n, true)) {
        const s = where(n);
        return f.updateElementAccessExpression(n, ts.visitNode(n.expression, visit), mark(s, ts.visitNode(n.argumentExpression, visit)));
      }
      if (ts.isNonNullExpression(n) && !notARead(n)) { const s = where(n); return f.updateNonNullExpression(n, mark(s, ts.visitNode(n.expression, visit), n.expression)); }
      if (ts.isPropertyAccessExpression(n) && !n.questionDotToken && !notARead(n) && isClassField(checker, n) && excludesUndefined(checker, n)) {
        const s = where(n);
        return f.updatePropertyAccessExpression(n, mark(s, ts.visitNode(n.expression, visit), n.expression), n.name);
      }
      return ts.visitEachChild(n, visit, ctx);
    };
    return ts.visitEachChild(root, visit, ctx);
  };
  const out = ts.transform(sf, [tr]).transformed[0];
  const text = ts.createPrinter().printFile(out);
  return used ? text + '\nfunction __vsite<T>(s: string, x: T): T {\n  console.log("@" + s);\n  return x;\n}\n' : text;
}

/** The function's slice from site-marked copies of its sources. */
function prepMarked(t, keep) {
  const tdir = under(path.join(WORK, 't', t.id), path.join(WORK, 't'));
  const set = materialize(t.file, under(path.join(tdir, 'ssrc'), tdir), { repo: ROOT });
  const p = makeProject(set);
  const idir = under(path.join(tdir, 'isrc'), tdir);
  for (const rel of set.files) writeFile(path.join(idir, rel), /\.(ts|tsx)$/.test(rel) && !rel.endsWith('.d.ts') ? markSites(p, rel) : fs.readFileSync(path.join(set.dir, rel), 'utf8'));
  const set2 = { ...set, dir: idir };
  const p2 = makeProject(set2);
  const root = set2.roots[0];
  const u = unitsOf(p2, root, root).find(x => x.name === t.name);
  if (!u) throw new Error('no unit in the marked copy');
  const sl0 = sliceUnit(p2, u, under(path.join(tdir, 'islice'), tdir));
  if (!sl0.ok) throw new Error(`slice of the marked copy: ${sl0.reason}`);
  return { tdir, u, sl: adaptSlice(sl0, keep, u.name).sl, sig: signatureOf(p2, u) };
}

async function sites(args) {
  const t0 = Date.now();
  const budget = Number(args.budget ?? 400) * 1000;
  const m0 = (args.shard ?? '0/1').match(/^(\d+)\/(\d+)$/);
  const shard = { i: Number(m0[1]), n: Number(m0[2]) };
  const p = loadPlan();
  const res = loadResults();
  const namesOf = new Map(p.suites.map(s => [s.suite, s.names || []]));
  const out = path.join(WORK, 'sites.jsonl');
  const done = new Set(fs.existsSync(out) ? fs.readFileSync(out, 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l).key) : []);
  const fns = p.targets.filter(t => res.get(t.id) && Object.values(res.get(t.id).perMode).some(x => x.perInput && x.perInput.some(y => y.status === 'designed')))
    .filter((t, i) => i % shard.n === shard.i);
  let pending = [], n = 0, left = 0;
  const flush = () => {
    if (!pending.length) return;
    const chunk = pending; pending = [];
    const r = runLeanBatch(path.join(WORK, 'lean', `sites_s${shard.i}_${String(n++).padStart(4, '0')}.lean`), [], chunk.map(j => ({ id: j.ns, t: { ns: j.ns, body: j.body } })), LEAN_TIMEOUT_S);
    for (const j of chunk) {
      const e = r.evals.get(j.ns);
      const lines = e && e.ok ? e.out.replace(/\r/g, '').split('\n') : [];
      const pi = lines.findIndex(l => /^\[PANIC /.test(l));
      const before = pi >= 0 ? lines.slice(0, pi).filter(l => l.startsWith('@')) : [];
      fs.appendFileSync(out, JSON.stringify({ key: j.key, id: j.t.id, name: j.t.name, rel: j.t.rel, i: j.x.i, panic: pi >= 0 ? lines[pi] : null,
        leanSite: before.length ? before[before.length - 1].slice(1) : null, error: e && e.ok ? undefined : ((e && e.errors) || ['no result']).join(' / ').slice(0, 300) }) + '\n');
    }
  };
  for (const t of fns) {
    const m = Object.values(res.get(t.id).perMode).find(x => x.perInput);
    const designed = m.perInput.map((x, i) => ({ ...x, i })).filter(x => x.status === 'designed' && !done.has(`${t.id}:${x.i}`));
    if (!designed.length) continue;
    let mk;
    try { mk = prepMarked(t, new Set(t.suites.flatMap(s => namesOf.get(s) || []))); }
    catch (e) { console.log(`  ${t.name}: ${e.message}`); continue; }
    const mode = t.modes.includes('dyn') ? 'dyn' : t.modes[0];
    for (const x of designed) {
      if (Date.now() - t0 > budget) { left++; continue; }
      const key = `${t.id}:${x.i}`;
      const ds = driverSlice(mk.sl, under(path.join(mk.tdir, `sd${x.i}`), mk.tdir), mk.u, mk.sig, [x.input]);
      const ns = `S_${t.id}_${x.i}`;
      const tr = translateDriver(ds, ns, mode);
      if (!tr.ok) { fs.appendFileSync(out, JSON.stringify({ key, id: t.id, name: t.name, i: x.i, error: `marked driver: ${tr.diag}` }) + '\n'); continue; }
      pending.push({ key, t, x, ns, body: tr.text.slice(tr.text.indexOf('\nnamespace ') + 1) });
      if (pending.length >= 8) flush();
    }
    console.log(`  ${t.name}: done`);
  }
  flush();
  console.log(`sites shard ${shard.i}/${shard.n}: ${left} designed-panic inputs left (run again)`);
}

/** Node side of `sites`: every recorded input of the functions with designed panics on the checked build. */
function checked(args) {
  const p = loadPlan();
  const res = loadResults();
  const siteOf = new Map(fs.existsSync(path.join(WORK, 'sites.jsonl')) ? fs.readFileSync(path.join(WORK, 'sites.jsonl'), 'utf8').split('\n').filter(Boolean).map(l => { const x = JSON.parse(l); return [x.key, x]; }) : []);
  // the checked build of the target's project (tools/public/node/build.js), made when missing:
  // projects/NAME/... from its tsconfig.strictts.json, public/mono/DIR/... (wrappers) from theirs
  const checkedDir = path.join(ROOT, 'scratch', 'validate', 'checked');
  const buildFor = (rel) => {
    let m = rel.match(/^projects\/([^/]+)\//);
    const b = m ? { out: path.join(checkedDir, m[1]), root: path.join(ROOT, 'scratch', 'projects', m[1]), cfg: path.join(ROOT, 'scratch', 'projects', m[1], 'tsconfig.strictts.json') }
      : (m = rel.match(/^public\/mono\/([^/]+)\//)) ? { out: path.join(checkedDir, `mono-${m[1]}`), root: path.join(ROOT, 'scratch'), cfg: path.join(ROOT, 'scratch', 'public', 'mono', m[1], 'tsconfig.json') } : null;
    if (b && !fs.existsSync(path.join(b.out, 'index.json'))) {
      const r = spawnSync(process.execPath, [path.join(ROOT, 'tools', 'public', 'node', 'build.js'), b.cfg, b.out, b.root], { encoding: 'utf8', timeout: 300000, maxBuffer: 64 << 20 });
      console.log(`  checked build ${path.relative(ROOT, b.out)}: ${(r.stdout || r.stderr || '').trim().split('\n').pop()}`);
    }
    return b;
  };
  const inDir = path.join(checkedDir, 'inputs');
  fs.mkdirSync(inDir, { recursive: true });
  const rows = [];
  for (const t of p.targets) {
    const r = res.get(t.id);
    const m = r && Object.values(r.perMode).find(x => x.perInput);
    if (!m) continue;
    const b = buildFor(t.rel);
    if (!b) { console.log(`  ${t.name}: no checked build for ${t.rel}`); continue; }
    const file = path.relative(b.root, t.file).replace(/\.ts$/, '.js');
    const idx = JSON.parse(fs.readFileSync(path.join(b.out, 'index.json'), 'utf8'))[file] || [];
    const it = idx.find(x => x.name === t.name);
    if (!it) { console.log(`  ${t.name}: not in the checked build's index`); continue; }
    const kind = { function: 'function', arrow: 'arrow', method: 'method', static: 'static', constructor: 'ctor' }[it.kind];
    const inputsFile = path.join(inDir, `${t.id}.json`);
    fs.writeFileSync(inputsFile, JSON.stringify(m.perInput.map(x => x.input)));
    const run = spawnSync(process.execPath, ['--permission', `--allow-fs-read=${b.out}`, `--allow-fs-read=${HERE}`, `--allow-fs-read=${inDir}`,
      path.join(HERE, 'checked_run.js'), b.out, file, t.name, kind, inputsFile], { encoding: 'utf8', timeout: 120000, maxBuffer: 64 << 20 });
    const outs = (run.stdout || '').split('\n').filter(Boolean).map(l => JSON.parse(l));
    if (outs.length !== m.perInput.length) { console.log(`  ${t.name}: checked run gave ${outs.length} of ${m.perInput.length} results: ${(run.stderr || '').slice(-300)}`); continue; }
    m.perInput.forEach((x, i) => {
      const o = outs[i];
      const site = siteOf.get(`${t.id}:${i}`);
      const nodeSite = o.outcome === 'violation' ? (() => { const w = o.where.split(' ')[0].split(':'); return `${path.basename(w[0])}:${w[1]}:${w[2]}`; })() : null;
      rows.push({ id: t.id, name: t.name, rel: t.rel, i, lean: x.status, panic: x.panic, node: o.outcome, nodeWhere: o.where, nodeSite, leanSite: site ? site.leanSite : undefined,
        siteError: site && site.error, sameSite: site && site.leanSite ? site.leanSite === nodeSite : null });
    });
  }
  fs.writeFileSync(path.join(WORK, 'checked.jsonl'), rows.map(r => JSON.stringify(r)).join('\n') + '\n');
  const designed = rows.filter(r => r.lean === 'designed');
  const others = rows.filter(r => r.lean !== 'designed');
  const c = (xs, f) => xs.filter(f).length;
  console.log(`designed-panic inputs: ${designed.length}; Node checked read fails: ${c(designed, r => r.node === 'violation')}; at the read where Lean panics: ${c(designed, r => r.sameSite === true)}; ` +
    `site differs: ${c(designed, r => r.sameSite === false)}; Lean site unknown: ${c(designed, r => r.sameSite === null)}`);
  console.log(`other inputs of these functions: ${others.length} (Lean ${[...new Set(others.map(r => r.lean))].join('/')}); Node checked read fails on ${c(others, r => r.node === 'violation')}`);
  for (const r of rows.filter(r => (r.lean === 'designed') !== (r.node === 'violation') || r.sameSite === false)) console.log(`  ${r.name} #${r.i}: Lean ${r.lean} ${r.panic || ''} site ${r.leanSite} / Node ${r.node} ${r.nodeWhere || ''}`);
}

// ---------------------------------------------------------------------------------------
// report

/** Private code (VALIDATE_SUITES): aggregates only. The counts (no names or paths of the private
 * code) go to WORK/AGGREGATES.md for the tracked RESULTS.md section; WORK/DETAILS.md (untracked)
 * lists every function that is not a match, for the investigation. */
function reportPrivate() {
  // causes established by hand, by target id or `rel:name` (untracked: WORK/causes.json)
  const causesPrivate = fs.existsSync(path.join(WORK, 'causes.json')) ? JSON.parse(fs.readFileSync(path.join(WORK, 'causes.json'), 'utf8')) : {};
  const p = loadPlan();
  const res = loadResults();
  const rows = p.targets.map(t => res.get(t.id) || { ...t, status: 'pending', inputs: 0, perMode: {} });
  const sum = (xs) => xs.reduce((a, b) => a + (b || 0), 0);
  const isVal = (m) => m && (m.status === 'match' || m.status === 'MISMATCH');
  const best = (r) => Object.values(r.perMode).filter(isVal).sort((a, b) => (b.inputs || 0) - (a.inputs || 0))[0] || {};
  const line = (label, rs, pick) => {
    const ms = rs.map(r => ({ r, m: pick(r) }));
    const val = ms.filter(x => isVal(x.m));
    const mis = ms.filter(x => x.m && x.m.status === 'MISMATCH');
    return `| ${label} | ${rs.length} | ${val.length} | ${sum(val.map(x => x.m.inputs))} | ${sum(val.map(x => x.m.match))} | ${sum(val.map(x => x.m.designedPanics))} | ${sum(mis.map(x => x.m.mismatchedInputs))} (${mis.length}) | ${rs.length - val.length} |`;
  };
  const lines = ['| private code (another project + a second project) | functions with a driver | validated | inputs compared | agree | designed panics | mismatching inputs (functions) | not validated |', '|---|---:|---:|---:|---:|---:|---:|---:|'];
  for (const mode of ['strict', 'dyn']) lines.push(line(`emitted in ${mode} mode`, rows.filter(r => r.modes.includes(mode)), r => r.perMode[mode] || { status: r.status }));
  lines.push(line('**distinct functions**', rows, r => { const b = best(r); return b.status ? b : { status: r.status }; }));
  const vals = rows.filter(r => r.status === 'match' || r.status === 'MISMATCH');
  const emitted = sum(p.suites.filter(s => s.mode === 'dyn').map(s => s.emitted));
  const emittedStrict = sum(p.suites.filter(s => s.mode === 'strict').map(s => s.emitted));
  const exercised = new Set(vals.flatMap(r => r.names || []));
  const others = [...new Map(p.others.map(o => [`${o.file}:${o.name}`, o])).values()];
  lines.push('');
  lines.push(`* Emitted functions: ${emitted} (dyn), ${emittedStrict} (strict), in ten modules; ${others.length} distinct have no driver of their own (generic instances, constructors of mutable records, getters, lifted functions, helpers), of which ${others.filter(o => exercised.has(o.name)).length} run inside a validated driver.`);
  const notesSum = (re) => sum(vals.map(r => { const n = (r.notes || []).find(x => re.test(x)); return n ? Number(n.match(/^\d+/)[0]) : 0; }));
  lines.push(`* Inputs generated for the validated functions: ${sum(vals.map(r => r.generated))}; not sent to Lean: ${notesSum(/slower than/)} slower than ${NODE_MS} ms under Node, ${notesSum(/inconclusive/)} inconclusive there (timeout, stack overflow, crash, host access), ${notesSum(/length limit/)} at an engine length limit, ${notesSum(/driver size cap/)} over the driver size cap (${vals.filter(r => (r.notes || []).some(x => /driver size cap/.test(x))).length} functions with inputs of large record types).`);
  lines.push(`* External calls replayed: ${vals.filter(r => r.extern).length} functions (pure built-ins only).`);
  // designed panics by kind (functions, inputs)
  const kinds = new Map();
  for (const r of vals) {
    const b = best(r);
    if (!b.designedPanics) continue;
    for (const k of new Set(b.panics || [])) { const e = kinds.get(k) || { fns: 0 }; e.fns++; kinds.set(k, e); }
  }
  lines.push(`* Designed panics: ${sum(vals.map(r => best(r).designedPanics))} inputs of ${vals.filter(r => best(r).designedPanics).length} functions; kinds (functions): ${[...kinds].sort((a, b) => b[1].fns - a[1].fns).map(([k, e]) => `${k.replace(/^\[PANIC |\]$/g, '')} (${e.fns})`).join(', ')}.`);
  lines.push(`* Strict and dyn translations: ${rows.filter(r => r.modes.length > 1).length} functions in both modes, the same Lean text for ${vals.filter(r => r.modes.length > 1 && r.sharedModes).length} validated ones.`);
  lines.push(`* Inputs not compared after designed panics: ${sum(vals.map(r => best(r).notCompared))}.`);
  // reasons, by category (no module names)
  const cat = (r) => {
    const x = (r.reason || r.status || '').replace(/\s+/g, ' ');
    if (/uses external module|imports a package/.test(x)) return 'imports a package or a non-relative module (not run)';
    if (/reads process\.env/.test(x)) return 'reads process.env (excluded)';
    if (/not a pure built-in/.test(x)) return 'calls an external function other than a pure built-in (excluded)';
    if (/record of the external calls over/.test(x)) return 'record of the external calls too large to replay (excluded)';
    if (/not run: driver over/.test(x)) return 'driver too large for the Lean time limit (not run)';
    // (the reason names parameters and fields: only its last part, the kind of value, is kept)
    if (/^inputs not generated/.test(x)) return `inputs not generated: ${((x.match(/\((.*)\)/) || [])[1] || '?').split(': ').pop()}`;
    if (/driver outside the subset/.test(x)) { const m = x.match(/\[([a-z0-9-]+)\]/); return `driver not translatable [${m ? m[1] : '?'}]`; }
    if (/no input finishes quickly/.test(x)) return 'no input finishes quickly under Node';
    if (/private method/.test(x)) return 'private method';
    if (/^slice/.test(x)) return 'not sliceable';
    if (/^lean: no output/.test(x)) return 'Lean ran out of memory (a typed array V8 allocates lazily)';
    if (/^lean/.test(x)) return 'Lean error';
    return x.replace(/:.*$/, '').slice(0, 60) || r.status;
  };
  const reasons = new Map();
  for (const r of rows) if (r.status !== 'match' && r.status !== 'MISMATCH') { const k = cat(r); reasons.set(k, (reasons.get(k) || 0) + 1); }
  lines.push('', '| not validated | functions |', '|---|---:|');
  for (const [k, v] of [...reasons].sort((a, b) => b[1] - a[1])) lines.push(`| ${k} | ${v} |`);
  // mismatching inputs by cause (classified from the first recorded mismatch of each function)
  const lastBit = (x) => {
    const nb = x.node.split('\n'), lb = x.lean.split('\n');
    if (nb.length !== lb.length) return false;
    let anyNum = false;
    for (let i = 0; i < nb.length; i++) {
      if (nb[i] === lb[i]) continue;
      const num = /(-?\d+(?:\.\d+)?(?:e[-+]\d+)?)/;
      const tn = nb[i].split(num), tl = lb[i].split(num);
      if (tn.length !== tl.length) return false;
      for (let k = 0; k < tn.length; k++) {
        if (tn[k] === tl[k]) continue;
        if (k % 2 === 0) return false;
        const u = Number(tn[k]), v = Number(tl[k]);
        if (!(Math.abs(u - v) <= 4 * Number.EPSILON * Math.max(Math.abs(u), Math.abs(v)))) return false;
        anyNum = true;
      }
    }
    return anyNum;
  };
  const cause = (x) => {
    if (!x) return 'unclassified';
    if (/\[PANIC toString\(radix\) of a non-integer is implementation-approximated\]/.test(x.lean)) return 'model limitation: toString(radix) of a non-integer (implementation-approximated in ECMA-262)';
    if (lastBit(x)) return 'model limitation: last bit of an implementation-approximated Math function (Impl.host: the C library, V8: its own)';
    if (/\[PANIC comparison of values without identity\]/.test(x.lean)) return 'model limitation: === on records inside unknown values (records have no identity)';
    if (/\[PANIC (typeof|Array\.isArray) of an external object\]/.test(x.lean)) return 'model limitation: typeof / Array.isArray of an external object';
    if (/TraceMismatch/.test(x.lean)) return 'external answer outside its declared TypeScript type (replay)';
    return 'unclassified';
  };
  const byCause = new Map();
  for (const r of rows.filter(r => r.status === 'MISMATCH')) {
    const m = Object.values(r.perMode).find(y => y.first);
    const cp = causesPrivate[r.id] || causesPrivate[`${r.rel}:${r.name}`];
    const k = (cp && cp.cause) || cause(m.first);
    const e = byCause.get(k) || { fns: 0, inputs: 0 };
    e.fns++; e.inputs += m.mismatchedInputs;
    byCause.set(k, e);
  }
  lines.push('', '| mismatches by cause | functions | inputs |', '|---|---:|---:|');
  for (const [k, e] of [...byCause].sort((a, b) => b[1].inputs - a[1].inputs)) lines.push(`| ${k} | ${e.fns} | ${e.inputs} |`);
  writeFile(path.join(WORK, 'AGGREGATES.md'), lines.join('\n') + '\n');
  // details (untracked)
  const det = ['# details (private, untracked)', ''];
  for (const r of rows.filter(r => r.status === 'MISMATCH' || r.status === 'error')) det.push(`- ${r.status} ${r.rel}:${r.line} ${r.name}: ${JSON.stringify(Object.values(r.perMode).find(m => m.first || m.reason) || r.reason).slice(0, 600)}`);
  det.push('', '## designed panics', '');
  for (const r of vals.filter(r => best(r).designedPanics)) det.push(`- ${r.rel}:${r.line} ${r.name}: ${best(r).designedPanics}/${best(r).inputs} ${(best(r).panics || []).join(', ')}`);
  writeFile(path.join(WORK, 'DETAILS.md'), det.join('\n') + '\n');
  console.log(lines.join('\n'));
}

function report() {
  const p = loadPlan();
  const res = loadResults();
  const causesFile = path.join(HERE, 'causes.json');
  const causes = fs.existsSync(causesFile) ? JSON.parse(fs.readFileSync(causesFile, 'utf8')) : {};
  const rows = p.targets.map(t => res.get(t.id) || { ...t, status: 'pending', inputs: 0, perMode: {} });
  const sum = (xs) => xs.reduce((a, b) => a + (b || 0), 0);
  const isVal = (m) => m && (m.status === 'match' || m.status === 'MISMATCH');
  // observations a driver prints as a placeholder (values of types the printer does not show)
  const placeholders = (r) => {
    const d = path.join(WORK, 't', r.id, 'drv0');
    const out = { outcome: false, args: false };
    if (!fs.existsSync(d)) return out;
    const walk = (x) => fs.readdirSync(x, { withFileTypes: true }).flatMap(e => e.isDirectory() ? walk(path.join(x, e.name)) : [path.join(x, e.name)]);
    for (const f of walk(d)) {
      const txt = fs.readFileSync(f, 'utf8');
      if (!txt.includes('---- difftool driver ----')) continue;
      for (const l of txt.split('\n')) {
        if (!/"<value>"|"<union>"/.test(l)) continue;
        if (/console\.log\("(return|resolve) "/.test(l)) out.outcome = true;
        if (/console\.log\("(args|self) "/.test(l)) out.args = true;
      }
    }
    return out;
  };
  const lines = [];
  const tsv = ['suite\tfile\tline\tfunction\tmode\tstatus\tinputs_compared\tagree\tdesigned_panics\tmismatching_inputs\tnot_compared\treason'];
  lines.push('| module | emitted functions | with a driver | validated | inputs compared | agree | designed panics | mismatching inputs (functions) | not validated |');
  lines.push('|---|---:|---:|---:|---:|---:|---:|---:|---:|');
  for (const s of p.suites) {
    const mine = rows.filter(r => r.suites.includes(s.suite));
    const pm = mine.map(r => ({ r, m: r.perMode[s.mode] || { status: r.status, reason: r.reason } }));
    const val = pm.filter(x => isVal(x.m));
    const mis = pm.filter(x => x.m.status === 'MISMATCH');
    lines.push(`| ${s.suite} | ${s.emitted} | ${mine.length} | ${val.length} | ${sum(val.map(x => x.m.inputs))} | ${sum(val.map(x => x.m.match))} | ${sum(val.map(x => x.m.designedPanics))} | ${sum(mis.map(x => x.m.mismatchedInputs))} (${mis.length}) | ${pm.length - val.length} |`);
    for (const x of pm) tsv.push([s.suite, x.r.rel, x.r.line, x.r.name, s.mode, x.m.status, x.m.inputs || 0, x.m.match || 0, x.m.designedPanics || 0, x.m.mismatchedInputs || 0, x.m.notCompared || 0, (x.m.reason || x.r.reason || '').replace(/\s+/g, ' ')].join('\t'));
  }
  const vals = rows.filter(r => r.status === 'match' || r.status === 'MISMATCH');
  const best = (r) => Object.values(r.perMode).filter(isVal).sort((a, b) => (b.inputs || 0) - (a.inputs || 0))[0] || {};
  const ph = new Map(vals.map(r => [r.id, placeholders(r)]));
  lines.push(`| **distinct functions** | | **${rows.length}** | **${vals.length}** | **${sum(vals.map(r => best(r).inputs))}** | **${sum(vals.map(r => best(r).match))}** | **${sum(vals.map(r => best(r).designedPanics))}** | **${sum(vals.map(r => best(r).mismatchedInputs))} (${rows.filter(r => r.status === 'MISMATCH').length})** | **${rows.length - vals.length}** |`);
  lines.push('');
  const exercised = new Set(vals.flatMap(r => r.names || []));
  // (one entry per module: a function emitted in several modules counts once)
  const others = [...new Map(p.others.map(o => [`${o.file}:${o.name}`, o])).values()];
  const reached = others.filter(o => exercised.has(o.name));
  const notesSum = (re) => sum(vals.map(r => { const n = (r.notes || []).find(x => re.test(x)); return n ? Number(n.match(/^\d+/)[0]) : 0; }));
  lines.push(`* Inputs generated for the validated functions: ${sum(vals.map(r => r.generated))}; not sent to Lean: ${notesSum(/slower than/)} slower than ${NODE_MS} ms under Node, ${notesSum(/inconclusive/)} inconclusive there (timeout, stack overflow, crash, host access), ${notesSum(/length limit/)} at an engine length limit.`);
  lines.push(`* External calls replayed from the Node run: ${vals.filter(r => r.extern).length} functions.`);
  lines.push(`* Strict and dyn translations of a function compared: ${rows.filter(r => r.modes.length > 1).length} functions are emitted in both modes; their two drivers translate to the same Lean text in ${vals.filter(r => r.modes.length > 1 && r.sharedModes).length} validated cases (one Lean run), separately otherwise.`);
  lines.push(`* Emitted functions without a driver of their own (generic instances, lifted inner functions, getters, helpers): ${others.length} distinct; ${reached.length} run inside a validated driver.`);
  lines.push(`* Inputs not compared because the drivers of a function (at most ${MAX_DRIVERS}) all stopped at designed panics before reaching them: ${sum(vals.map(r => best(r).notCompared))}.`);
  lines.push(`* Partially observable results: ${vals.filter(r => ph.get(r.id).outcome).length} validated functions return a value the printer shows only as \`<value>\`/\`<union>\` (a value of type \`unknown\`, a function, a union of objects), ${vals.filter(r => ph.get(r.id).args.valueOf() && !ph.get(r.id).outcome).length} more print some argument that way; for those, the comparison covers return vs throw, the console and the other observations.`);
  // reasons
  const reasons = new Map();
  for (const r of rows) {
    if (r.status === 'match' || r.status === 'MISMATCH') continue;
    let k = (r.reason || r.status).replace(/\s+/g, ' ');
    const rule = k.match(/\[([a-z0-9-]+)\]/);
    if (/driver outside the subset/.test(k)) k = `driver outside the subset [${rule ? rule[1] : '?'}]: ${k.replace(/^.*\] /, '').slice(0, 70)}`;
    else if (/^inputs not generated/.test(k)) k = k.replace(/\)$/, '').replace('(', '— ');
    else k = k.replace(/\(.*$/, '').replace(/: .*$/, '').trim();
    reasons.set(k, (reasons.get(k) || 0) + 1);
  }
  lines.push('');
  lines.push('| not validated: reason | functions |', '|---|---:|');
  for (const [k, v] of [...reasons].sort((a, b) => b[1] - a[1])) lines.push(`| ${k.replace(/\|/g, '\\|')} | ${v} |`);
  // mismatches
  const esc = (x) => String(x).replace(/\|/g, '\\|').replace(/\n/g, ' ⏎ ');
  const mm = rows.filter(r => r.status === 'MISMATCH');
  lines.push('');
  lines.push('| mismatching function | inputs (mismatching) | differs in | first mismatching input: Node / Lean | cause |', '|---|---:|---|---|---|');
  for (const r of mm) {
    const x = Object.values(r.perMode).find(m => m.first);
    const c = causes[`${r.rel}:${r.name}`];
    lines.push(`| ${r.rel}:${r.line} ${r.name} | ${x.inputs} (${x.mismatchedInputs}) | ${x.partsAll.join(', ')} | \`${esc(x.first.input).slice(0, 100)}\`: ${esc(x.first.node).slice(0, 90)} / ${esc(x.first.lean).slice(0, 90)} | ${c ? c.cause : 'not yet classified'} |`);
  }
  // designed panics
  const dp = vals.filter(r => best(r).designedPanics);
  lines.push('');
  lines.push('| function with designed panics | inputs | panics | panic | example input |', '|---|---:|---:|---|---|');
  for (const r of dp) { const b = best(r); lines.push(`| ${r.rel}:${r.line} ${r.name} | ${b.inputs} | ${b.designedPanics} | ${(b.panics || []).join(', ')} | \`${esc(b.designedFirst ? b.designedFirst.input : '').slice(0, 90)}\` |`); }
  writeFile(path.join(HERE, 'results.tsv'), tsv.join('\n') + '\n');
  const md = path.join(HERE, 'RESULTS.md');
  const prev = fs.existsSync(md) ? fs.readFileSync(md, 'utf8') : '';
  const begin = '<!-- BEGIN GENERATED (node tools/validate/validate.js report) -->', end = '<!-- END GENERATED -->';
  const gen = `${begin}\n${lines.join('\n')}\n${end}`;
  const text = prev.includes(begin) ? prev.slice(0, prev.indexOf(begin)) + gen + prev.slice(prev.indexOf(end) + end.length) : `# Translation validation against Node\n\n${gen}\n`;
  writeFile(md, text);
  console.log(lines.join('\n'));
}

// ---------------------------------------------------------------------------------------

async function main() {
  const [cmd, ...rest] = process.argv.slice(2);
  const args = {};
  for (let i = 0; i < rest.length; i++) {
    const a = rest[i];
    if (a === '--redo') args.redo = true;
    else if (a === '--single') SINGLE = true;
    else if (a === '--record') RECORD = true;
    else if (a === '--panicked') args.panicked = true;
    else if (a.startsWith('--')) args[a.slice(2)] = rest[++i];
  }
  if (cmd === 'plan') plan();
  // (a stray child of the Node runner can keep the event loop alive: exit once the output is written)
  else if (cmd === 'run') { await runShard(args); process.stdout.write('', () => process.exit(0)); }
  else if (cmd === 'report') { if (PRIVATE) reportPrivate(); else report(); }
  else if (cmd === 'sites') { await sites(args); process.stdout.write('', () => process.exit(0)); }
  else if (cmd === 'checked') checked(args);
  else { process.stderr.write('usage: validate.js plan | run --shard I/N [--budget S] [--only REGEX] [--redo] | report\n'); process.exit(2); }
}

main().catch(e => { process.stderr.write(`internal error: ${e.stack || e}\n`); process.exit(2); });

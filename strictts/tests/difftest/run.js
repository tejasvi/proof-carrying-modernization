#!/usr/bin/env node
// Differential tester: runs every program of tests/corpus on Node (types stripped with
// typescript's transpileModule) and on the Lean interpreter of the StrictTS semantics
// (after translation by frontend/), and compares stdout line by line.
//
//   tools/run.sh 0.2 590 node tests/difftest/run.js [--only REGEX] [--shard I/N] [--batch K] [--keep]
//
// A program is a file tests/corpus/NAME.ts, or a directory tests/corpus/NAME/ with main.ts.
// Header markers (first comment lines of the program):
//   // @numbers      uses number/string operations whose Lean model is pending; a Lean run
//                    that panics with "pending" is reported as SKIP instead of FAIL
//   // @extern       external calls (regexes, JSON, Date.now): the Lean run replays the
//                    outcomes recorded in the Node run (harness.cjs, Prelude runMainTrace)
//   // @strict       (reject tests) translated in the original subset (--strict: no unknown/any)
//   // @skip REASON  not run
//   // @gap REASON   a known difference between Node and the StrictTS semantics (not a
//                    translator bug): reported as SKIP when the outputs differ as expected
//   // @panic [TEXT] a designed panic: the program's last output line prints a value its
//                    types exclude (Node prints it); the Lean run must print everything before
//                    it and then panic there (a `[PANIC …]` line containing TEXT, its last)
// Negative tests live in tests/corpus/reject/*.ts with a marker `// @reject RULE-ID`: the
// translator must exit 1 and report that rule.
'use strict';
const fs = require('fs');
const path = require('path');
const { spawnSync } = require('child_process');

const ROOT = path.resolve(__dirname, '..', '..');
const CORPUS = path.join(ROOT, 'tests', 'corpus');
const OUT = path.join(ROOT, 'tests', 'difftest', 'out');
const ts = require(path.join(ROOT, 'frontend', 'node_modules', 'typescript'));
const { translate } = require(path.join(ROOT, 'frontend', 'dist', 'index.js'));
const { runCoverage } = require(path.join(ROOT, 'frontend', 'dist', 'coverage.js'));
const { f64Lean } = require(path.join(ROOT, 'frontend', 'dist', 'core.js'));
const { leanJSStr, leanStrLit } = require(path.join(ROOT, 'frontend', 'dist', 'ty.js'));

const args = process.argv.slice(2);
const opt = (name, dflt) => { const i = args.indexOf(name); return i >= 0 ? args[i + 1] : dflt; };
const only = opt('--only') ? new RegExp(opt('--only')) : null;
const shard = opt('--shard');
const batchSize = Number(opt('--batch', '12'));
const leanTimeout = Number(opt('--lean-timeout', '180'));

function discover() {
  const progs = [];
  for (const ent of fs.readdirSync(CORPUS, { withFileTypes: true }).sort((a, b) => a.name < b.name ? -1 : 1)) {
    if (ent.name === 'reject') continue;
    if (ent.isFile() && ent.name.endsWith('.ts')) progs.push({ name: ent.name.slice(0, -3), dir: null, entry: path.join(CORPUS, ent.name) });
    else if (ent.isDirectory() && fs.existsSync(path.join(CORPUS, ent.name, 'main.ts'))) {
      progs.push({ name: ent.name, dir: path.join(CORPUS, ent.name), entry: path.join(CORPUS, ent.name, 'main.ts') });
    }
  }
  return progs;
}

function markers(src) {
  const m = { numbers: false, skip: null, reject: null, gap: null };
  for (const line of src.split('\n')) {
    const t = line.trim();
    if (!t.startsWith('//')) { if (t) break; else continue; }
    if (/@numbers\b/.test(t)) m.numbers = true;
    if (/@extern\b/.test(t)) m.extern = true;
    if (/@strict\b/.test(t)) m.strict = true;
    const s = t.match(/@skip\s+(.*)/); if (s) m.skip = s[1];
    const r = t.match(/@reject\s+(\S+)/); if (r) m.reject = r[1];
    const g = t.match(/@gap\s+(.*)/); if (g) m.gap = g[1];
    const pn = t.match(/@panic(?:\s+(.*))?$/); if (pn) m.panic = pn[1] || '';
  }
  return m;
}

const HARNESS = path.join(__dirname, 'harness.cjs');

function runNode(p, mk = {}) {
  const jsDir = path.join(OUT, 'js', p.name);
  fs.rmSync(jsDir, { recursive: true, force: true });
  fs.mkdirSync(jsDir, { recursive: true });
  const files = p.dir ? fs.readdirSync(p.dir).filter(f => f.endsWith('.ts')).map(f => path.join(p.dir, f)) : [p.entry];
  for (const f of files) {
    const js = ts.transpileModule(fs.readFileSync(f, 'utf8'), {
      compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.CommonJS, alwaysStrict: true, esModuleInterop: false },
      fileName: f,
    }).outputText;
    fs.writeFileSync(path.join(jsDir, path.basename(f).replace(/\.ts$/, '.js')), js);
  }
  const entry = path.join(jsDir, path.basename(p.entry).replace(/\.ts$/, '.js'));
  const env = mk.extern ? { ...process.env, STRICTTS_TRACE: '1' } : process.env;
  const r = spawnSync(process.execPath, [HARNESS, entry], { encoding: 'utf8', timeout: 20000, env });
  if (r.error) return { ok: false, out: `node error: ${r.error.message}` };
  const k = (r.stderr || '').indexOf('=====TRACE=====\n');
  const trace = k >= 0 ? JSON.parse(r.stderr.slice(k + 16).split('\n')[0]) : undefined;
  return { ok: true, out: r.stdout, trace };
}

/** Lean terms of a recorded Node run (StrictTS.Frontend.RecCall), see harness.cjs. */
function recLean(v) {
  if (v === null) return '.null';
  if (v === true || v === false) return `(.bool ${v})`;
  if (v.u) return '.undef';
  if (v.n !== undefined) return `(.num ${f64Lean(v.n === '-0' ? -0 : Number(v.n))})`;
  if (v.s !== undefined) return `(.str ${leanJSStr(v.s)})`;
  if (v.h !== undefined) return `(.handle ${v.h})`;
  if (v.o) return `(.fields [${v.o.map(([k, x]) => `(${leanStrLit(k)}, ${recLean(x)})`).join(', ')}])`;
  if (v.a) return `(.list [${v.a.map(recLean).join(', ')}])`;
  return '.other';
}

function traceLean(ns, trace) {
  const calls = trace.calls.map(c => `{ name := ${leanStrLit(c.name)}, args := [${c.args.map(recLean).join(', ')}], ` +
    `out := ${c.err ? `.error (${leanStrLit(c.err[0])}, ${leanStrLit(c.err[1])})` : `.ok ${recLean(c.out)}`} }`);
  const nows = trace.nows.map(v => f64Lean(v.n === '-0' ? -0 : Number(v.n)));
  return [`def ${ns}.traceCalls : Array RecCall := #[${calls.join(',\n  ')}]`,
    `def ${ns}.traceNows : Array F64 := #[${nows.join(', ')}]`,
    `#eval runMainTrace ${ns}.program "${ns}" ${ns}.traceCalls ${ns}.traceNows`].join('\n');
}

function translateProg(p, trace) {
  const files = p.dir ? [p.entry] : [p.entry];
  const ns = 'Prog_' + p.name.replace(/[^A-Za-z0-9_]/g, '_');
  try {
    const r = translate({ files, namespace: ns, eval: true, cwd: ROOT });
    if (!r.ok) return { ok: false, err: r.diagnostics };
    const file = path.join(OUT, p.name + '.lean');
    if (trace) {
      // answer the external calls from the Node run
      const ev = `#eval runMain ${ns}.program "${ns}"`;
      if (!r.lean.includes(ev)) return { ok: false, err: `no '${ev}' line to replace` };
      r.lean = r.lean.replace(ev, () => traceLean(ns, trace)); // (a function: `$&` in a recorded string is not a pattern)
    }
    fs.writeFileSync(file, r.lean);
    return { ok: true, file, ns, lines: r.lean.split('\n').length };
  } catch (e) {
    return { ok: false, err: `internal error: ${e.stack}` };
  }
}

// `lean` is run directly (not through `lake env`) so that a timeout kills the process itself
let LEAN_ENV = null;
function leanEnv() {
  if (LEAN_ENV) return LEAN_ENV;
  const r = spawnSync('lake', ['env', 'printenv', 'LEAN_PATH'], { cwd: ROOT, encoding: 'utf8' });
  LEAN_ENV = { ...process.env, LEAN_PATH: (r.stdout || '').trim() };
  return LEAN_ENV;
}

/** Run several translated programs in one Lean process (one import of the semantics). */
function runLeanBatch(items, timeoutS = leanTimeout) {
  const header = ['import StrictTS.Frontend.Prelude', 'import StrictTS.Proof.Extern', 'set_option maxRecDepth 100000', 'open StrictTS StrictTS.Frontend', ''];
  const body = [];
  const ranges = [];
  for (const it of items) {
    const text = fs.readFileSync(it.tr.file, 'utf8').split('\n');
    const start = text.findIndex(l => l.startsWith('namespace '));
    const lines = text.slice(start);
    const from = header.length + body.length + 1;
    body.push(...lines);
    ranges.push({ it, from, to: header.length + body.length });
  }
  const batchFile = path.join(OUT, `_batch_${process.pid}_${Date.now()}.lean`);
  fs.writeFileSync(batchFile, [...header, ...body].join('\n'));
  const t0 = Date.now();
  // (no asynchronous elaboration: faster here, and no thread creation failures on a busy machine)
  const r = spawnSync('lean', ['-DElab.async=false', batchFile], { cwd: ROOT, env: leanEnv(), encoding: 'utf8', timeout: timeoutS * 1000, killSignal: 'SIGKILL', maxBuffer: 64 << 20 });
  const secs = (Date.now() - t0) / 1000;
  if (!args.includes('--keep')) fs.rmSync(batchFile, { force: true });
  const text = (r.stdout || '') + (r.stderr || '');
  const res = new Map();
  for (const { it, from, to } of ranges) {
    const ns = it.tr.ns;
    const b = text.indexOf(`=====STRICTTS-BEGIN ${ns}=====`);
    const e = text.indexOf(`=====STRICTTS-END ${ns}=====`);
    const errs = [];
    const re = /:(\d+):(\d+): error: ([^\n]*)/g;
    let m;
    while ((m = re.exec(text))) { const ln = Number(m[1]); if (ln >= from && ln <= to) errs.push(`line ${ln - from + 1}: ${m[3]}`); }
    if (b >= 0 && e > b) res.set(it, { ok: true, out: text.slice(b + `=====STRICTTS-BEGIN ${ns}=====`.length + 1, e), errs });
    else res.set(it, { ok: false, out: '', errs: errs.length ? errs : [r.error ? `lean: ${r.error.message}` : 'no output (crash or timeout?)'] });
  }
  return { res, secs, timedOut: !!r.error };
}

function lines(s) { return s.replace(/\r/g, '').split('\n').filter((l, i, a) => !(i === a.length - 1 && l === '')); }

function main() {
  fs.mkdirSync(OUT, { recursive: true });
  // the generated files import StrictTS.Frontend.Prelude (and StrictTS.Proof.Extern if they call externs)
  const b = spawnSync('lake', ['build', 'StrictTS.Frontend.Prelude', 'StrictTS.Proof.Extern'], { cwd: ROOT, encoding: 'utf8' });
  if (b.status !== 0) { console.log(`lake build StrictTS.Frontend.Prelude StrictTS.Proof.Extern failed:\n${b.stdout}${b.stderr}`); process.exit(2); }
  let progs = discover();
  if (only) progs = progs.filter(p => only.test(p.name));
  if (shard) {
    const [i, n] = shard.split('/').map(Number);
    progs = progs.filter((_, k) => k % n === i - 1);
  }
  const rows = [];
  const toLean = [];
  for (const p of progs) {
    const src = fs.readFileSync(p.entry, 'utf8');
    const mk = markers(src);
    const row = { name: p.name, mk, status: '', note: '' };
    rows.push(row);
    if (mk.skip) { row.status = 'SKIP'; row.note = mk.skip; continue; }
    row.node = runNode(p, mk);
    if (mk.extern && !row.node.trace) { row.status = 'FAIL'; row.note = 'node: no trace recorded'; continue; }
    row.tr = translateProg(p, mk.extern ? row.node.trace : undefined);
    if (!row.tr.ok) { row.status = 'FAIL'; row.note = 'translation: ' + row.tr.err.split('\n')[0]; row.detail = row.tr.err; continue; }
    toLean.push(row);
  }
  // Lean, in batches
  let leanSecs = 0;
  for (let i = 0; i < toLean.length; i += batchSize) {
    const batch = toLean.slice(i, i + batchSize);
    let { res, secs, timedOut } = runLeanBatch(batch);
    leanSecs += secs;
    if (timedOut && batch.length > 1) {
      // isolate the slow program
      res = new Map();
      for (const it of batch) { const r1 = runLeanBatch([it], 60); leanSecs += r1.secs; res.set(it, r1.res.get(it)); }
    }
    for (const row of batch) row.lean = res.get(row);
  }
  for (const row of toLean) {
    const L = row.lean;
    // any elaboration error in the generated code fails the program, even if it still ran
    if (!L.ok || L.errs.length) { row.status = 'FAIL'; row.note = 'lean: ' + (L.errs[0] || '?'); row.detail = L.errs.join('\n'); continue; }
    const exp = lines(row.node.out), got = lines(L.out);
    const pending = got.some(l => l.includes('PANIC pending'));
    if (row.mk.numbers && pending) { row.status = 'SKIP'; row.note = 'number/string model pending'; continue; }
    let diff = -1;
    for (let k = 0; k < Math.max(exp.length, got.length); k++) if (exp[k] !== got[k]) { diff = k; break; }
    if (row.mk.panic !== undefined) {
      // the designed panic: at Node's last output line (before its final `[ok]`), as Lean's last line
      const at = exp.length - 2;
      // (an @extern run then reports the Node run's calls it did not make: `[TRACE: …]`)
      const rest = got.slice(at + 1);
      const ok = diff >= 0 && diff === at && got[at].includes('PANIC') && got[at].includes(row.mk.panic) &&
        (rest.length === 0 || (rest.length === 1 && rest[0].startsWith('[TRACE:')));
      row.status = ok ? 'PASS' : 'FAIL';
      row.note = ok ? `${at} lines, then the designed panic where node prints ${JSON.stringify(exp[at])}`
        : diff < 0 ? 'no panic (expected one at the last line)' : `line ${diff + 1}: node ${JSON.stringify(exp[diff] ?? '<eof>')} vs lean ${JSON.stringify(got[diff] ?? '<eof>')}`;
      if (!ok) row.detail = `--- node\n${exp.join('\n')}\n--- lean\n${got.join('\n')}`;
      continue;
    }
    if (diff < 0) { row.status = 'PASS'; row.note = `${exp.length} lines${row.mk.gap ? ' (documented gap no longer observed)' : ''}`; }
    else if (row.mk.gap) {
      row.status = 'SKIP';
      row.note = `known semantic gap (${row.mk.gap}); line ${diff + 1}: node ${JSON.stringify(exp[diff] ?? '<eof>')} vs lean ${JSON.stringify(got[diff] ?? '<eof>')}`;
    } else {
      row.status = 'FAIL';
      row.note = `line ${diff + 1}: node ${JSON.stringify(exp[diff] ?? '<eof>')} vs lean ${JSON.stringify(got[diff] ?? '<eof>')}`;
      row.detail = `--- node\n${exp.join('\n')}\n--- lean\n${got.join('\n')}`;
    }
  }
  // negative tests
  const rejDir = path.join(CORPUS, 'reject');
  if (fs.existsSync(rejDir) && !shard) {
    for (const f of fs.readdirSync(rejDir).filter(f => f.endsWith('.ts')).sort()) {
      const name = 'reject/' + f.slice(0, -3);
      if (only && !only.test(name)) continue;
      const file = path.join(rejDir, f);
      const mk = markers(fs.readFileSync(file, 'utf8'));
      const row = { name, mk, status: '', note: '' };
      rows.push(row);
      let r;
      try { r = translate({ files: [file], cwd: ROOT, strict: !!mk.strict }); } catch (e) { r = { ok: false, diagnostics: `internal error: ${e.message}` }; }
      if (r.ok) { row.status = 'FAIL'; row.note = 'accepted, expected rejection'; }
      else if (mk.reject && !r.diagnostics.includes(`[${mk.reject}]`)) { row.status = 'FAIL'; row.note = `expected [${mk.reject}], got ${r.diagnostics.split('\n')[0]}`; }
      else { row.status = 'PASS'; row.note = r.diagnostics.split('\n')[0]; }
    }
  }
  // `--coverage --emit-lean` on a small project: the emitted partial program must elaborate
  if (!shard && (!only || only.test('coverage/smoke'))) {
    const row = { name: 'coverage/smoke', mk: {}, status: '', note: '' };
    rows.push(row);
    try {
      const file = path.join(OUT, 'coverage_smoke.lean');
      const res = runCoverage({ project: path.join(ROOT, 'tests', 'coverage', 'smoke', 'tsconfig.json'), cwd: ROOT, label: 'smoke', emitLean: file });
      const e = res.emit;
      const t0 = Date.now();
      const r = spawnSync('lean', ['-DElab.async=false', file], { cwd: ROOT, env: leanEnv(), encoding: 'utf8', timeout: leanTimeout * 1000, killSignal: 'SIGKILL' });
      leanSecs += (Date.now() - t0) / 1000;
      const errs = ((r.stdout || '') + (r.stderr || '')).split('\n').filter(l => / error/.test(l));
      if (!e || e.unitsEmitted !== 5 || e.funs !== 6) { row.status = 'FAIL'; row.note = `emitted ${e ? `${e.unitsEmitted} units, ${e.funs} functions` : 'nothing'}, expected 5 units, 6 functions`; }
      else if (r.status !== 0 || errs.length) { row.status = 'FAIL'; row.note = `lean: ${errs[0] || r.error?.message || `exit ${r.status}`}`; }
      else { row.status = 'PASS'; row.note = `${e.unitsEmitted}/${e.units} covered units, ${e.funs} functions, ${e.lines} lines elaborated`; }
    } catch (err) { row.status = 'FAIL'; row.note = `internal error: ${err.message}`; }
  }
  // `--coverage --emit-lean` on a project of generic functions without call sites: each covered one
  // is emitted at its instance, the same definition as the use-site monomorphization in a whole
  // program (use.ts), and the module elaborates; `--no-emit-generics` leaves them out
  if (!shard && (!only || only.test('coverage/generics'))) {
    const row = { name: 'coverage/generics', mk: {}, status: '', note: '' };
    rows.push(row);
    try {
      const dir = path.join(ROOT, 'tests', 'coverage', 'generics');
      const file = path.join(OUT, 'coverage_generics.lean');
      const off = runCoverage({ project: path.join(dir, 'tsconfig.json'), cwd: ROOT, label: 'generics', emitLean: file, emitGenerics: false }).emit;
      runCoverage({ project: path.join(dir, 'tsconfig.json'), cwd: ROOT, label: 'generics', emitLean: file });
      const funs = JSON.parse(fs.readFileSync(file.replace(/\.lean$/, '.funs.json'), 'utf8')).filter(f => f.inst);
      const got = funs.map(f => `${f.name}/${f.kind}:${f.line}=${f.lean}${JSON.stringify(f.inst)}`).join(' ');
      const want = 'chunkBy/function:4=chunkBy_number{"T":"number"} firstOr/arrow:9=firstOr_number{"T":"number"} ' +
        'longest/function:10=longest_string{"S":"string"} clampAll/function:15=clampAll_number{"N":"number"}';
      const use = translate({ files: [path.join(dir, 'use.ts')], cwd: ROOT });
      const defs = (lean) => new Map(lean.split(/\n(?=def |theorem |abbrev |end |\/-)/).map(b => [b.match(/^def «(.+)Def» : FunDef TT where/)?.[1], b.trim()]).filter(([k]) => k));
      const cov = defs(fs.readFileSync(file, 'utf8'));
      const mono = use.ok ? defs(use.lean) : new Map();
      const differ = funs.filter(f => !cov.has(f.lean) || cov.get(f.lean) !== mono.get(f.lean)).map(f => f.lean);
      const t0 = Date.now();
      const r = spawnSync('lean', ['-DElab.async=false', file], { cwd: ROOT, env: leanEnv(), encoding: 'utf8', timeout: leanTimeout * 1000, killSignal: 'SIGKILL' });
      leanSecs += (Date.now() - t0) / 1000;
      const errs = ((r.stdout || '') + (r.stderr || '')).split('\n').filter(l => / error/.test(l));
      if (!off || off.unitsEmitted !== 0) { row.status = 'FAIL'; row.note = `--no-emit-generics emitted ${off ? off.unitsEmitted : '?'} units, expected 0`; }
      else if (got !== want) { row.status = 'FAIL'; row.note = `instances ${got}, expected ${want}`; }
      else if (!use.ok) { row.status = 'FAIL'; row.note = `use.ts: ${use.diagnostics.split('\n')[0]}`; }
      else if (differ.length) { row.status = 'FAIL'; row.note = `differ from the use-site monomorphization: ${differ.join(', ')}`; }
      else if (r.status !== 0 || errs.length) { row.status = 'FAIL'; row.note = `lean: ${errs[0] || r.error?.message || `exit ${r.status}`}`; }
      else { row.status = 'PASS'; row.note = `${funs.length} instances, each the use-site definition; elaborated; none with --no-emit-generics`; }
    } catch (err) { row.status = 'FAIL'; row.note = `internal error: ${err.message}`; }
  }
  // report
  const w = Math.max(...rows.map(r => r.name.length), 8);
  console.log(`${'program'.padEnd(w)}  status  note`);
  for (const r of rows) console.log(`${r.name.padEnd(w)}  ${r.status.padEnd(6)}  ${r.note}`);
  if (args.includes('--details')) {
    for (const r of rows) if (r.status === 'FAIL' && r.detail) console.log(`\n=== ${r.name}\n${r.detail}`);
  }
  const n = s => rows.filter(r => r.status === s).length;
  console.log(`\nlean time ${leanSecs.toFixed(1)} s`);
  console.log(`PASS ${n('PASS')} / FAIL ${n('FAIL')} / SKIP ${n('SKIP')}`);
  fs.writeFileSync(path.join(OUT, `summary${shard ? '_' + shard.replace('/', 'of') : ''}.txt`),
    rows.map(r => `${r.name}\t${r.status}\t${r.note}`).join('\n') + `\nPASS ${n('PASS')} / FAIL ${n('FAIL')} / SKIP ${n('SKIP')}\n`);
}

main();

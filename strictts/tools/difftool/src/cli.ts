#!/usr/bin/env node
// strictts-diff: semantic diff of two versions of a TypeScript project.
//   node tools/difftool/dist/cli.js [diff] OLD NEW [options]     (OLD/NEW: file, directory or git:REV:path)
//   node tools/difftool/dist/cli.js validate FILE.ts [options]   (Node vs the Lean semantics on the same functions)
//   node tools/difftool/dist/cli.js bench DIR [options]          (equivalence benchmark: DIR/NN_name/{old.ts,new.ts,expected})
import './boot';
import * as fs from 'fs';
import * as path from 'path';
import { runPipeline, DEFAULTS, PipelineOpts } from './pipeline';
import { table, details } from './report';
import { SCRATCH, timestamp, writeFile } from './util';
import { runValidate } from './validate';
import { runBench } from './bench';
import { toResultV1 } from './interface';
import { runSelftest } from './selftest';
import { scanHistory, summarizeScan, runHistoryPairs, HistOpts } from './history';

function usage(): never {
  process.stderr.write(`usage:
  strictts-diff [diff] OLD NEW [options]     compare two versions (file, directory or git:REV:path)
  strictts-diff validate FILE.ts... [options] compare Node with the Lean semantics on every function of FILE
  strictts-diff bench DIR [options]           run the equivalence benchmark DIR/NN_name/{old.ts,new.ts,expected}
  strictts-diff selftest                       run the interface fixture (tools/difftool/test/fixture) and check its JSON
  strictts-diff history --repo DIR --out DIR [--paths a,b] [--phase scan|run|both] [--max-pairs N] [--commits c1,c2]
                                              scan a repository's history (read-only git), extract self-contained
                                              changed functions into OUT/<date>_<commit>_<fn>/{old,new}, run the diff
options:
  --repo DIR          repository for git:REV:path specs (default: current directory)
  --work DIR          scratch directory (default: scratch/difftool/run-<time>)
  --json FILE         write the result as JSON (schema strictts-diff/v1, INTERFACE.md); '-' = stdout
  --runs N            fuzzing runs per function (default ${DEFAULTS.runs})
  --seed N            random seed (default ${DEFAULTS.seed})
  --timeout-ms N      per-call timeout in Node (default ${DEFAULTS.timeoutMs})
  --no-lean           skip the Lean stage (fuzzing only)
  --tactic FILE       proof script (placeholders {OLDCALL} {NEWCALL} {OLD} {NEW} {F} {DESTRUCT} {DEFS})
  --tactic-wf FILE    proof script of the statement for worlds with allocated argument arrays
  --heartbeats N      maxHeartbeats per theorem (default ${DEFAULTS.heartbeats})
  --lean-timeout S    seconds per Lean process (default ${DEFAULTS.leanTimeoutS})
  --only REGEX        only functions whose key (module::name) matches
  --details           print details for every changed function
  -q, --quiet         no progress messages
exit status: 0 = no REFUTED function, 1 = some function REFUTED, 2 = usage or internal error
`);
  process.exit(2);
}

export interface CliArgs { cmd: string; pos: string[]; opts: PipelineOpts; json?: string; details: boolean; hist: HistOpts; tactics: { tactic: 'default' | 'custom'; tacticWf: 'default' | 'custom' } }

export function parseArgs(argv: string[]): CliArgs {
  const pos: string[] = [];
  let quiet = false, json: string | undefined, det = false;
  const hist: HistOpts = { repo: process.cwd(), out: '', paths: ['.'], maxPairs: 1e9, phase: 'both' };
  const tactics: { tactic: 'default' | 'custom'; tacticWf: 'default' | 'custom' } = { tactic: 'default', tacticWf: 'default' };
  const o: PipelineOpts = {
    ...DEFAULTS, repo: process.cwd(), work: '', log: (s: string) => process.stderr.write(s + '\n'),
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    const val = () => { const v = argv[++i]; if (v === undefined) usage(); return v; };
    switch (a) {
      case '--repo': o.repo = path.resolve(val()); hist.repo = o.repo; break;
      case '--out': hist.out = path.resolve(val()); break;
      case '--paths': hist.paths = val().split(',').filter(Boolean); break;
      case '--phase': { const v = val(); if (v !== 'scan' && v !== 'run' && v !== 'both') usage(); hist.phase = v; break; }
      case '--max-pairs': hist.maxPairs = Number(val()); break;
      case '--commits': hist.commits = val().split(',').filter(Boolean); break;
      case '--work': o.work = path.resolve(val()); break;
      case '--json': { const v = val(); json = v === '-' ? '-' : path.resolve(v); break; }
      case '--runs': o.runs = Number(val()); break;
      case '--seed': o.seed = Number(val()); break;
      case '--timeout-ms': o.timeoutMs = Number(val()); break;
      case '--no-lean': o.lean = false; break;
      case '--tactic': { const f = val(); o.script = fs.readFileSync(f, 'utf8').replace(/\s+$/, ''); tactics.tactic = 'custom'; break; }
      case '--tactic-wf': { const f = val(); o.scriptWf = fs.readFileSync(f, 'utf8').replace(/\s+$/, ''); tactics.tacticWf = 'custom'; break; }
      case '--heartbeats': o.heartbeats = Number(val()); break;
      case '--lean-timeout': o.leanTimeoutS = Number(val()); break;
      case '--lean-batch': o.leanBatch = Number(val()); break;
      case '--only': o.only = new RegExp(val()); break;
      case '--details': det = true; break;
      case '-q': case '--quiet': quiet = true; break;
      case '-h': case '--help': usage();
      default: if (a.startsWith('-')) usage(); pos.push(a);
    }
  }
  if (quiet) o.log = () => {};
  let cmd = 'diff';
  if (pos[0] === 'diff' || pos[0] === 'validate' || pos[0] === 'bench' || pos[0] === 'history' || pos[0] === 'selftest') cmd = pos.shift()!;
  if (!o.work) o.work = path.join(SCRATCH, `${cmd}-${timestamp()}-${process.pid}`);
  return { cmd, pos, opts: o, json, details: det, hist, tactics };
}

async function main(): Promise<number> {
  const a = parseArgs(process.argv.slice(2));
  if (a.cmd === 'validate') { if (!a.pos.length) usage(); return runValidate(a.pos, a.opts, a.json); }
  if (a.cmd === 'bench') { if (a.pos.length !== 1) usage(); return runBench(a.pos[0], a.opts, a.json); }
  if (a.cmd === 'history') {
    if (!a.hist.out) usage();
    if (a.hist.phase !== 'run') {
      const recs = await scanHistory(a.hist, a.opts);
      process.stdout.write(summarizeScan(recs) + '\n');
      writeFile(path.join(a.hist.out, 'scan_summary.txt'), summarizeScan(recs) + '\n');
    }
    if (a.hist.phase !== 'scan') return runHistoryPairs(a.hist, a.opts, a.json);
    return 0;
  }
  if (a.cmd === 'selftest') return runSelftest(a.opts);
  if (a.pos.length !== 2) usage();
  // with `--json -` the result goes to stdout and the table to stderr
  const human = (t: string) => (a.json === '-' ? process.stderr : process.stdout).write(t + '\n');
  const { reports } = await runPipeline(a.pos[0], a.pos[1], a.opts);
  human(table(reports));
  if (a.details) human(details(reports));
  if (a.json) {
    const res = toResultV1(reports, { old: a.pos[0], new: a.pos[1], seed: a.opts.seed, runs: a.opts.runs, lean: a.opts.lean, ...a.tactics });
    const text = JSON.stringify(res, null, 2) + '\n';
    if (a.json === '-') process.stdout.write(text); else writeFile(a.json, text);
  }
  return reports.some(r => r.verdict === 'REFUTED') ? 1 : 0;
}

if (require.main === module) {
  main().then(code => process.exit(code), e => { process.stderr.write(`internal error: ${(e as Error).stack ?? e}\n`); process.exit(2); });
}

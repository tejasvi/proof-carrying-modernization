# R6: a certified refactoring audit of es-toolkit's history (StrictTS)

Not pre-registered: designed on 2026-10-26 after a first look at 31 pairs (disclosed below). Inputs
frozen by the paper's evidence owner before the full run: `~/fv_paper/prereg/ADDENDUM_R6_inputs.md`
(sha256 8733b38d89ddb81a86bf420b5e039332fed43ebb84cd0f144bbbed596ff90ad6).

## Claim

es-toolkit (toss/es-toolkit, MIT), every commit from v1.0.0 (7203b563, 2024-05-31) to v1.52.0
(32f4c8fb) that touches `src/`: 1,163 commits, 1,071 changed functions. For each of the 415 changed
functions whose old and new versions are self-contained and take generated inputs, the semantic diff
`strictts-diff` (commit 10ec829, zero human proof lines) gives one of:

| verdict | pairs | meaning |
|---|---:|---|
| PROVED | 46 | a Lean theorem: old and new give equal results (return value or exception, console output, final arguments) for every input of the declared types; 43 in every world, 3 in worlds whose argument arrays are allocated |
| REFUTED, confirmed by Lean | 9 | a concrete input on which old and new differ in Node, and the StrictTS semantics gives the same two different outcomes |
| REFUTED, Node only | 77 | a concrete input on which old and new differ in Node; 73 of these functions are outside the StrictTS subset, 4 are inside but Lean cannot confirm (below) |
| UNKNOWN | 283 | no counterexample (up to 1,500 random inputs; 226 of these pairs ran all 1,500, the others fewer because inputs timed out or could not run) and no proof; the reason per pair is in `r6_table.tsv` |

Of the 79 pairs whose old and new versions lie in the subset: 46 PROVED (58%), 9 REFUTED with Lean
confirmation, 4 REFUTED in Node only, 20 UNKNOWN. Every one of the 86 counterexamples was replayed in
plain `node`, outside the tool, and reproduced (86/86).

### Behaviour changes in commits whose type promises the same behaviour

Six commits typed `perf`, `refactor` or `style` changed observable behaviour (old | new):

| commit | type | function | input | old | new | confirmation |
|---|---|---|---|---|---|---|
| d7c37c9f | perf | uniq | `uniq([-0])` | `[-0]` | `[0]` | Lean + Node |
| 0f26a676 | perf | zip | `zip()` | `[]` | throws RangeError: Invalid array length | Node |
| e37b2957 | perf | zipWith | `zipWith([], 8, undefined)` | `[]` | throws RangeError: Invalid array length | Node |
| 0edff252 | perf | toPath | `toPath("..")` | `["", "", "", ""]` | `["", "", ""]` | Node |
| c739a739 | perf | toPath | `toPath("]")` | `[]` | `["]"]` | Node |
| 5cb0b788 | style | areObjectsEqual | `areObjectsEqual({ buffer: undefined }, { hasOwnProperty: undefined })` | throws TypeError | `false` | Node |

Three more behaviour changes came in commits typed `docs`, `test` and `bench`: `trimEnd("", "")`
went from `""` to throwing (4069aa6b, docs; Lean + Node), `takeRight([8, 8], -1)` from `[8]` to `[]`
(25cd782b, test; Lean + Node), and `divide(0, 1)` stopped printing `0 1` to the console (25841dca,
bench: a leftover `console.log` was removed; Node).

Conversely, 29 changes in `fix` and `feat` commits are PROVED equivalent for every input of the declared
types: they change types, not behaviour (`readonly` array parameters, a type predicate, signatures made
compatible with `@types/lodash`, a function moved between modules).

## Method

1. Scan (read-only `git log`/`git show` of a full clone; `strictts-diff history --phase scan`): every
   changed top-level function is sliced with its in-repository dependencies and classified: signature
   changed (162), inputs that cannot be generated, mostly function-typed parameters (494), outside the
   StrictTS subset (336), inside the subset in both versions (79). The 415 self-contained pairs with
   generated inputs form the testable list; the 79 in-subset pairs the provable list.
2. Run (`--phase run`, chunks of at most 30 pairs, one guarded job each): up to 1,500 random inputs per pair
   compare old and new under Node (fresh module instances per input, `Math.random` fixed to 0, virtual
   timers); a difference is reduced to a small counterexample and, for in-subset pairs, run again
   through the StrictTS semantics (Lean confirmation). Without a difference, in-subset pairs get a Lean
   proof attempt of the equality statement (then the allocated-arguments variants); generic functions
   are compared through a wrapper at one instance (each type parameter := number; `extends
   PropertyKey`/`string` := string; `extends unknown[]` := number[]); the instance is in `r6_table.tsv`
   (22 PROVED at T := number, 1 at T := string).
3. Replay: every counterexample was transpiled to plain ES modules (TypeScript's `transpileModule`) with
   one driver per version that decodes the recorded input, calls the function and prints the outcome,
   the final arguments and the console, and was run with `node` (86/86 reproduce).
4. Recheck: every Lean file that holds a PROVED theorem was checked again with
   `lake env lean --tstack=262144` at commit 10ec829: 46/46 theorems print exactly
   `[propext, Classical.choice, Quot.sound]` and have no error inside their lines.

## Statements and axioms

For a PROVED pair with statement `all-worlds` the theorem has the form

    theorem equiv_<id> (I : Impl) : ∀ (vs : Vals TT <argument types>) (w : World TT),
        JS.exec (callFun I Old.program Old.«fRef» vs) w = JS.exec (callFun I New.program New.«fRef» vs) w

(the same final world, result or exception and output, for every host model `I`, argument values of
the declared types and world); `allocated-arguments` adds the hypothesis that the arguments' arrays are
allocated cells. Axioms: the three standard ones only (checked per theorem). Trusted beyond the Lean
kernel: the StrictTS semantics as a model of TypeScript (validated against Node: corpus 180/0/0, 0
mismatches over ≈ 600k cases per number operation and 1.85M string checks), the translator from
TypeScript to the IR, and the host models `Impl.host`.

## Why some pairs are not decided

- REFUTED in Node only although in the subset (4): object identity (the old `shuffle([])` returns its
  argument, the new a copy: the confirmation driver does not print identity); designed panics (2:
  `pullAt` and `at` read an array at a non-index key such as -2 or 0.5, where Node yields `undefined`
  and the StrictTS semantics stops, by design, at a read outside the types); an external call without a
  recorded answer (`deburr` uses `String.prototype.normalize`).
- UNKNOWN in the subset (20): translated signatures differ (9, e.g. a parameter that became optional);
  proof search timed out (4); results that allocate differently (2); loops and Map operations (1);
  string-library reasoning (1); generic in one version only (1); module-level tables changed (1); a
  target not found in the translation (1).
- UNKNOWN outside the subset (263): no counterexample in the random inputs; the subset rule that excludes
  the function is in the reason column.

## First look (disclosed)

On the 31 pairs that the first scan called in-subset (refactor/perf/style/chore commits), before the
tool fixes: 4 PROVED, 3 REFUTED in Node, 24 UNKNOWN (21 of them from two tool gaps: the module-state
comparison counted the versioned `end <ns>` line; generic functions were not emitted). After the
fixes: 9 PROVED, 3 REFUTED, 19 UNKNOWN, and `uniq([-0])` Lean-confirmed after the driver fix. The first
scan's subset check passed generic functions vacuously; the frozen scan checks them at their instance
(113 in-subset pairs became 79). All 31 are in the frozen testable list and in the counts above.

## Cost

Compute: ≈ 1.1 core-hours in all (guard logs: scans, runs, regressions, replay, recheck). Agents: the
StrictTS lead alone, no helpers; well under the $500 budget.

## Files

Tool: commit 10ec829 (branch rally-hist; worktree `~/strictts_ws/rally`); this directory holds the
scripts as run, the frozen lists, `pairs_SHA256SUMS` and `r6_table.tsv` (one row per testable pair:
verdict, statement, theorem and file, axioms, counterexample, plain-node replay, reason, generic
instance, commit subject). Evidence (not in git; `R6_EVIDENCE_SHA256SUMS` lists every file):
`~/strictts_ws/rally/scratch/r6/` with `chunks/` (the run's strictts-diff/v1 JSON per chunk),
`evidence/` (the Lean files with the 46 PROVED theorems, the run's and the recheck's outputs,
`proofs.tsv`), `replay_v2/` (per refutation: transpiled old/new, `driver.mjs`, `out.json`;
`replay.tsv`). Pair sources: `~/strictts/scratch/hist_es/scan2_{rpsc,other}/` (checked by
`pairs_SHA256SUMS`).

## Replay

- A PROVED theorem: `cd ~/strictts_ws/rally && lake env lean --tstack=262144 scratch/r6/evidence/<file>`
  prints `'equiv_<id>' depends on axioms: [propext, Classical.choice, Quot.sound]` (file and theorem per
  pair in `proofs.tsv` and `r6_table.tsv`).
- A counterexample: `node scratch/r6/replay_v2/<pair>/old/driver.mjs` and `.../new/driver.mjs` print the
  two outcomes (`replay.tsv` holds the recorded and replayed values).
- The whole run: `bash tools/difftool/r6/run_chain_v2.sh` on the frozen pair directories.

# R6r: the R6 audit run on remeda's history with the R6b tool

This study was not pre-registered. The paper's evidence owner recorded the inputs and the tool before the run, in
`~/fv_paper/prereg/ADDENDUM_R6r_remeda_inputs.md` (sha256 e19195aa...). StrictTS's working name for it was R7.

- Library: remeda (MIT). Read from a no-checkout clone (objects only, no working tree):
  `~/strictts/scratch/projects_hist/remeda`, HEAD d02c3bdb5e18cfa53e76f33f4ae525adce515379 (2026-10-25).
- Tool: master bbe90b4. Its tool code is that of 2ea47b8, the commit named in the addendum:
  `git diff --stat 2ea47b8 bbe90b4` lists only HANDOFF_20261023.md and tools/difftool/r6b/. The difftool
  dist hash is dbe5a9c27002f8aa (the first 16 hex digits of the sha256 of the concatenated dist/*.js), the
  same as for R6b.
- Frozen lists, with the hashes the addendum gives (unchanged): `r7_testable.txt` (862 pairs, fec09171...),
  `r7_provable.txt` (160 pairs, 14c45704...), `pairs_SHA256SUMS` (41e73814...).

## Scan

The scan covered every commit that touches src/ or packages/remeda/src/: 397 commits. 388 of them modify .ts
files, for 4,424 file changes in all. They change 1,308 functions:
- 4 use external modules;
- 108 change their signature;
- 334 take inputs that the fuzzer does not generate;
- 702 are self-contained but outside the StrictTS subset;
- 160 are inside the subset in both versions.

The 862 self-contained functions are the testable pairs. The 160 inside the subset are the provable pairs.
Source: `~/strictts/scratch/hist_remeda/scan/scan_summary.txt` and `scan.jsonl`.

## Results

One row per pair: `r6r_table.tsv`, sha256 a0d92081bcfa02f89453e02fad521dad7af3c7c6c4ed88cb44e5145372a2c3fe.
Every pair has a verdict. Every UNKNOWN pair, and every refutation without a Lean confirmation, has its
reason in the table. All 54 PROVED statements are all-worlds.

All 862 testable pairs:

| commit intent | pairs | PROVED | REFUTED, Lean-confirmed | REFUTED, Node only | UNKNOWN |
|---|---:|---:|---:|---:|---:|
| preserve (refactor/perf/style/chore) | 269 | 27 | 2 | 1 | 239 |
| change (fix/feat/revert) | 561 | 23 | 6 | 49 | 483 |
| other (docs/test/other) | 32 | 4 | 1 | 5 | 22 |
| all | 862 | 54 | 9 | 55 | 744 |

The 160 provable pairs:

| commit intent | pairs | PROVED | REFUTED, Lean-confirmed | REFUTED, Node only | UNKNOWN |
|---|---:|---:|---:|---:|---:|
| preserve | 60 | 27 | 2 | 0 | 31 |
| change | 89 | 23 | 6 | 2 | 58 |
| other | 11 | 4 | 1 | 0 | 6 |
| all | 160 | 54 | 9 | 2 | 95 |

## Limits of these counts

1. **81 of the 160 provable pairs have no target in the translation.** In all 81, the changed function is a
   module-level `const` bound to an arrow function (`target_kind.tsv`, written by `target_kind.sh`). The
   translator makes such a constant a top-level function only when code in the slice calls it or refers to
   it (`frontend/src/functions.ts`, `topFunDecl`). Nothing in these slices does. So the translation has no
   function of that name, and the difftool reports "target ... not found in the translation".

   A probe shows the gap: the one-line module `export const f = (x: number): number => x + 1;` translates
   to a program with no functions (`~/strictts/scratch/probe_lazy_r6r/t4.*`, against t5 written with
   `function`).

   The scan's subset check accepted these slices, so the frozen list counts them as provable. For these 81
   pairs the label means nothing. 26 of them are remeda's `_lazy` helpers.

   The other 79 provable pairs have a translated target:
   - 54 PROVED;
   - 9 refuted with a Lean confirmation;
   - 2 refuted in Node only;
   - 14 UNKNOWN: proof search timed out (4), loops (3), translated signatures differ (3), generic instances
     differ (2), number (1), module-level state (1).

2. **35 of the 54 proofs hold only at one instance of a generic function.** The `inst` column marks them.
   As in R6, the wrapper `__difftool_inst` calls the function at one instance (for example `T := number`) in
   both versions, and the theorem says nothing about other instances.

   **No proof used the compatibility wrapper.** The `domain` column is empty in every row. The wrapper
   applies only to non-generic functions, and the three provable pairs whose translated signatures differ
   are all generic.

3. **7 of the 54 PROVED pairs are helpers in test files**, so 47 are library source. The 7:
   - `isNumber` (src/filter.test.ts);
   - `defaultTo`, three times (src/first.test.ts);
   - `func1` and `func2` (src/equals.test.ts);
   - `sub` (src/purry.test.ts).

4. **Refutations: 64** (9 Lean-confirmed, 55 Node only). All 64 reproduce in plain node
   (`replay_v2/replay.tsv`, 64/64).

   Each counterexample call was type-checked against the declared signatures of its function in both
   versions, using the overloads where the function has them (`tscheck.tsv`):
   - **27 calls type-check in both versions.**
     - 24 of them call module-internal functions, which neither version's module exports
       (`refuted_export.tsv`, written by `export_check.sh`). Most are the `...Implementation` helpers behind
       remeda's exported functions. Two are the test helpers `func1`/`func2`.
     - 3 call exported functions:
       - `flat` (ac358851, feat): at depth 2.2e-16 the old version flattens one level and the new built-in
         flat does not;
       - `randomInteger` (47b323c0, a docs commit): only the text of the error message changes, from
         "randomInt:" to "randomInteger:";
       - `stringToPath` (0fde627f, feat): `"0"` becomes the number 0, in line with the commit's stated aim
         of Lodash compatibility.
   - **36 calls type-check in neither version.** All 36 call exported, overloaded functions with
     arguments that no overload accepts:
     - 19 pass no arguments, for example `difference()`;
     - 17 pass undefined, null or another value of the wrong type, for example `zip({}, {})`.

     As in the R6 erratum, the difftool takes its inputs from the implementation's own parameter list,
     which is wider than the overloads.
   - **1 call type-checks only in the new version**: `isEmpty(undefined)`. The feat commit 9c79944e widened
     the parameter type to accept undefined.

5. **Commits whose type promises the same behaviour (refactor/perf/style/chore): 269 pairs, 27 PROVED**
   (21 chore and 6 style, one of them the test helper `isNumber`). There are 3 refutations, and none of them
   is a change that a typed caller of the library can see:
   - `zipWith()` (bf52b3c2, chore): neither version's signatures accept a call without arguments;
   - `func1` and `func2` (0149aeda, chore "vitest 2"): test helpers in src/isDeepEqual.test.ts that the
     commit changed to throw "This function should never be called!".

6. **Lean confirmations.** There are 11 confirmation blocks for the provable refutations
   (`evidence_confirm/confirmations.tsv`). Each block names its pair's function and prints the
   counterexample's arguments. They are the 9 confirmed refutations plus 2 attempts that did not confirm,
   with the reason in the table:
   - `sampleImplementation` (b08a667d): the old version returns its argument array itself, the new one a
     fresh array. The driver prints values, not identity, so Lean prints `return []` for both.
   - `swapArray` (035ae147): the old version reads `data[1]` of a one-element array. StrictTS panics on every
     out-of-bounds array read (DESIGN.md, principle 4). Node returns undefined there, and the write that
     follows grows the copy.

   R6's report generator added "the read is outside the types" to this reason, which is false for an
   `unknown[]` element. R6r's generator, `r6r_report.js`, drops that clause. That is its only change from
   R6's r6_report.js.

Possible tool fixes, not part of R6r: translate every safely liftable module-level `const` arrow of the
entry file, and count a pair as provable only when its target is in the translation. A re-run after such a
fix would be a labelled re-run, as R6b was.

## Evidence

Directory `~/strictts/scratch/r7/`. Manifest R6R_EVIDENCE_SHA256SUMS, 1,902 files, sha256
a95639c91d04f7fd5b463e779450b6592c01e8e79f5f11b325d2c98e5b7247d2.

- `chunks/`: the run's strictts-diff/v1 JSON and log for each of the 29 chunks, with the chunk lists. All 29
  ended with rc=0 and none needed a retry.
- `evidence/`: the 18 Lean batch files with the 54 PROVED theorems, their run outputs, `proofs.tsv`, and the
  recheck outputs (`*.recheck.out`, `recheck.log`).
  - The recheck ran `lake env lean --tstack=262144` at dd93572. Its Lean sources are those of bbe90b4: the
    diff lists only tools/difftool/r6b/.
  - 54/54 theorems print exactly `[propext, Classical.choice, Quot.sound]`.
  - 54/54 have no error inside the theorem.
  - The recheck reproduces all 93 axiom lines of the run's own outputs.
- `evidence_confirm/`: the 7 Lean files that hold the 11 confirmation blocks, their outputs, and
  `confirmations.tsv` (sha256 27eb6949...).
- `replay_v2/`: the replay driver and output for each pair, and `replay.tsv` (sha256 ed254301...).
- `tscheck_work/`, `tscheck.tsv` (sha256 81ac872f...), `tscheck.err`: the type check. For each version it
  uses the pair's slice plus a file `check.ts` with the call.
- The lists, `r6r_table.tsv`, the draft tables `R6R_draft.md`, `target_kind.tsv`, `refuted_export.tsv`, the
  run and recheck logs, and `guard_secs.txt` (metered core-seconds per guarded job).
- The scripts as run: `run_chain.sh`, `recheck.sh`, `r6r_report.js`, `cex_replay_v2.js`, `tscheck_cex.js`,
  `collect_confirm.js`, `target_kind.sh`, `export_check.sh`.
  - `collect.js` and `recheck_verify_v2.js` are R6's own (tools/difftool/r6/, identical by sha256).
  - `cex_replay_v2.js` and `tscheck_cex.js` are R6's with the scan directory name changed.

Copies of the scripts, lists and tables are in this directory.

## Cost

- **Compute: 1.13 core-h**, summed from the 101 guarded jobs between the scan's start (02:24Z) and the
  delivery:

  | step | core-h |
  |---|---:|
  | scan and list preparation | 0.19 |
  | run | 0.82 |
  | confirmations, replay and type check | 0.01 |
  | recheck | 0.11 |

  The addendum estimated about 2 core-h and about 1 h of wall time. The run itself took 36 min of wall time
  (02:34:25Z to 03:10:01Z).
- **Model:** the StrictTS lead session alone (claude-opus-5-5), with no helper agents. The tool makes no
  model calls.
- **Tokens:** the lead session's tokens from 01:50Z to 03:30Z cost $26.27 (Opus 5.5 list prices,
  deduplicated by message id; 148 calls). That window also covers the R6b addendum.

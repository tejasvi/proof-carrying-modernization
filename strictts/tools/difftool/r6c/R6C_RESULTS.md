# R6c: R6's frozen es-toolkit pairs re-run with the const-arrow tool

This is a labelled re-run, not pre-registered. Its inputs and tool were recorded by the paper's evidence
owner before the run, in `~/fv_paper/prereg/ADDENDUM_R6c_R6rb_inputs.md` (sha256 6ecf67c4...).

- **Pairs.** R6's 415 frozen pairs, with the lists that `ADDENDUM_R6_inputs.md` gives:
  - `r6_testable.txt`, sha256 408069f7...;
  - `r6_provable.txt`, 79 pairs, f2f81a47...;
  - pair sources checked by `pairs_SHA256SUMS`, bf561176..., verified before the run.
- **Tool.** Branch const-arrow at 9e54bdbc34af6edfd0d784d39a89944ad4307b80, difftool dist hash
  baf07b296e82b4bf. It is master d57b59f (the R6b tool, 2ea47b8, plus documents) and two commits:
  - 09d1e8c: a safely liftable, non-generic module-level `const f = (...) => ...` is translated even
    when nothing calls it, and the history scan requires the target in the translation;
  - 9e54bdb: `StrictTS/Proof/DynOpt.lean`, ts_sym lemmas for an unknown value passed to a
    `value?: unknown` parameter.

  Regressions at 9e54bdb: full build 159 jobs, corpus 181/0/0, selftest PASS, bench 43/44 + 23/23.
- **Clone.** `~/strictts_ws/constarrow/scratch/rescan/clone_es`, a no-checkout clone of R6's clone,
  HEAD 9c0cac2ee6c0f807099723d7b226f3b65e976d5c.
- **Not blind.** Before the registration I had run 8 of these pairs one by one with the new tool. These
  were the 6 that changed below, plus isArrayLike and isArrayLikeObject, which stayed UNKNOWN. The
  addendum records this.

## Results

One row per pair: `r6c_table.tsv`, sha256 075508b4d0988f264d5ef0cd866136349a06c1722d95735e227362ba123d6c0e.

| verdict | R6 (10ec829) | R6b (43132a8) | R6c (9e54bdb) |
|---|---:|---:|---:|
| PROVED | 46 | 54 | 60 (57 all-worlds, 3 allocated-arguments) |
| REFUTED, confirmed by Lean | 9 | 10 | 10 |
| REFUTED, Node only | 77 | 76 | 76 |
| UNKNOWN | 283 | 275 | 269 |

Against R6b, pair by pair (`compare_r6b.tsv`): 6 pairs change, all from UNKNOWN to PROVED (all-worlds),
and every other pair has the same verdict.
- `startsWith` (4c285773, a style commit). R6b's reason was "target startsWith not found in the
  translation": the function is an uncalled `export const startsWith = (...) => ...`. 09d1e8c translates
  it.
- `isNaN`, `isFinite`, `isObject`, `isObjectLike` (8db96e45, a docs commit) and `isLength` (e3525153, a
  fix commit). R6b's reason was "a call that was not unfolded". The new versions take `value?: unknown`,
  and the compatibility wrapper passes the old `unknown` argument through the cast that the new lemmas
  evaluate. As for endsWith and startsWith at e3525153, these 5 are proved on the old version's parameter
  types, which the `domain` column marks.

PROVED by commit intent:
- refactor/perf/style/chore: 14 (R6b: 13). They are 7 style, 3 chore, 3 perf and 1 refactor.
- fix/feat/revert: 33 (R6b: 32).
- docs/test/other: 13 (R6b: 9).

Of the 79 frozen provable pairs, 52 are PROVED (R6b: 46). All 6 changes are in that list. With the new
tool, no provable pair lacks its target.

The 60 PROVED pairs:
- 59 are library source. 1 is a test helper: `greet` in src/function/spread.spec.ts, as in R6 and R6b.
- 25 are proved at one instance of a generic function (`inst` column).
- 7 are proved on the old version's parameter types (`domain` column): endsWith, startsWith (e3525153),
  isNaN, isFinite, isObject, isObjectLike and isLength.

## The 86 refutations

They are the same 86 pairs as in R6 and R6b, with the same counterexamples:
- all 86 reproduce in plain node (`replay_v2/replay.tsv`);
- the type check (`tscheck.tsv`) is byte-identical to R6's: 76 calls type-check against the declared
  signatures in both versions, and 10 do not (the R6 erratum);
- there are 14 confirmation blocks (`evidence_confirm/confirmations.tsv`) with the same pair-to-block
  mapping as R6b: the 10 Lean-confirmed refutations, plus shuffle, pullAt, at and deburr with R6's
  reasons.

New in R6c is the export status (`refuted_export.tsv`, written by `export_check.sh` from git show of the
original sources):
- 82 refuted functions are exported by their module in both versions;
- 4 are module-internal: areObjectsEqual, flattenObjectImpl (twice) and assignInImpl.
- Of the 76 type-valid calls, 72 call exported functions. All 10 invalid calls are to exported functions.

`export_check.sh` gives grep the source as a here-string. R6r's version piped the source into
`grep -q`. Under pipefail, grep stops at the first match, so the pipe can close early and a match is
then read as none. R6c's first try marked mergeWith as internal that way. Rerun with the fixed script,
R6r's classification is byte-identical to its delivered `refuted_export.tsv`.

## Recheck

The 16 Lean batch files were rechecked with `lake env lean --tstack=262144` at 9e54bdb:
- 60/60 PROVED theorems print exactly `[propext, Classical.choice, Quot.sound]`;
- 60/60 have no error inside the theorem.

108 of the 109 axiom lines in the run's own outputs reproduce. The one that does not belongs to a theorem
that is not PROVED: `equiv_h005u001` (intersection 576b136a, a perf commit), a heartbeat timeout both
times.
- In the run, the limit was hit inside the tactic block, and the theorem printed `sorryAx`.
- In the recheck, it was hit at the theorem's first line. Lean reported that error and then printed
  "does not depend on any axioms" for the theorem.

The difftool counts a proof only when no error lies inside the theorem (src/lean.ts, runLeanBatch), so
both outputs give the same verdict. This is a Lean behaviour worth knowing: a theorem whose elaboration
hits the heartbeat limit at the top level can print no axioms. A check on `#print axioms` alone would
count it.

## Evidence

Directory `~/strictts_ws/constarrow/scratch/r6c/`. Manifest R6C_EVIDENCE_SHA256SUMS: 2,123 files, sha256
175ed99a97dc0df0a745d7b238bbf4aa4a3ef322ba1498a636974505ac8d87f1. It holds:
- `chunks/`: 15 chunks, all rc=0, no retries;
- `evidence/`: 16 batch files, their outputs, recheck outputs and `proofs.tsv`;
- `evidence_confirm/`;
- `replay_v2/`;
- `tscheck_work/`;
- the table, the comparison and the draft tables;
- the scripts as run: `run_chain.sh`, `post_run.sh`, `report.js` (R6r's generator), `cex_replay_v2.js`,
  `tscheck_cex.js`, `collect_confirm.js`, `export_check.sh`, `compare_tables.sh`;
- the logs, and `guard_secs.txt` (metered core-seconds per guarded job).

Copies of the scripts and tables are in this directory.

## Cost

- **Compute: 0.86 core-h**, over the 37 guarded jobs from 04:10:53Z to 04:53Z: run 0.67, post-processing
  and recheck 0.19. The run took 28 min of wall time.
- **Tool development, regressions and the first looks** (const-arrow, DynOpt): 0.56 core-h in the same
  worktree before 04:10Z, over 40 guarded jobs. That covers the builds, two regression runs, the
  rescans of first look (b) and the probes.
- **Model:** the StrictTS lead session alone (claude-opus-5-5), with no helpers; the tool makes no model
  calls.
- **Tokens:** the lead session's tokens from 03:30Z to 04:55Z cost $14.16 (173 calls). That window also
  covers the tool development, the R6r follow-ups and the NoPanic merge.

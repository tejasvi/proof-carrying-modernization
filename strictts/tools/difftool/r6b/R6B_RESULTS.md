# R6b: the R6 audit of es-toolkit's history re-run with the improved tool

Same inputs as R6: the 415 frozen pairs (`~/fv_paper/prereg/ADDENDUM_R6_inputs.md`; pair sources checked
by `tools/difftool/r6/pairs_SHA256SUMS`, sha256 bf561176...). Tool: commit 43132a8 (merged into master
as 2ea47b8). It differs from R6's 10ec829 in four places:
- the translator accepts the nullish test `x == null` / `x != undefined`;
- `Dyn.eq` against undefined/null always answers (new lemmas, `StrictTS/Proof/DynNullish.lean`);
- `ts_destruct` splits optional and union values;
- the difftool compares a widened parameter list on the old version's inputs.
Regressions at 43132a8 match 10ec829: full build, corpus 181/0/0, selftest, bench 43/44 + 23/23.
Not pre-registered: a re-run of R6's frozen inputs after tool changes.

## Results (one row per pair: `r6b_table.tsv`, sha256 0b7167cb2fa550dab2dcd21cbb4eccd74dd8f9e742764b9206ca491d022111a0)

| verdict | R6 (10ec829) | R6b (43132a8) |
|---|---:|---:|
| PROVED | 46 (43 all-worlds, 3 allocated-arguments) | 54 (51 all-worlds, 3 allocated-arguments) |
| REFUTED, confirmed by Lean | 9 | 10 |
| REFUTED, Node only | 77 | 76 |
| UNKNOWN | 283 | 275 |

Changes, pair by pair (every other pair has the same verdict):
- newly PROVED (8), all through the nullish test:
  - `isNil` (523e5592, 489ac76f);
  - `isNotNil` (523e5592, 72589819);
  - `isArrayLike` (925ee3be, be4162dc);
  - `endsWith` and `startsWith` (e3525153).
- newly Lean-confirmed (1): `toString` (43932e61).
The 86 refuted pairs are the same pairs as in R6, so the R6 erratum applies unchanged: 76 counterexamples are
calls the public TypeScript signatures admit, 10 are not (`tools/difftool/r6/R6_ERRATUM_20261027.md`).

By commit intent: refactor/perf/style/chore 13 PROVED (R6: 9); fix/feat/revert 32 (R6: 29);
docs/test/other 9 (R6: 8).

## Evidence (`~/strictts_ws/loosenull/scratch/r6b/`, manifest R6B_EVIDENCE_SHA256SUMS, 1,180 files, sha256 7019a18751d71711eca2670bf5a50a707625b1d381f4be9f8b92086d8e57636d)

- `chunks/`: the run's strictts-diff/v1 JSON per chunk.
- `evidence/`: the Lean files holding the 54 PROVED theorems and `proofs.tsv`. The recheck with
  `lake env lean --tstack=262144` at 43132a8 gives 54/54 printing exactly
  `[propext, Classical.choice, Quot.sound]` and 54/54 with no error inside the theorem.
- `replay_v2/`: the 86 counterexamples replayed in plain node (86/86 reproduce).

## Cost

- R6b run, replay and recheck: 0.84 core-h.
- Tool development and regressions: 0.48 core-h.
- Lead session tokens from 00:13Z to 01:50Z: $33.58 (Opus 5.5 list prices, deduplicated by message id; 141 calls). That window also covers the R6 merge, the erratum and the es-toolkit report draft.
- No helpers, and no model calls by the tool.

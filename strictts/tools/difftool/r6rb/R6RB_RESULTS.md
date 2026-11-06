# R6rb: R6r's frozen remeda pairs re-run with the const-arrow tool

This is a labelled re-run, not pre-registered. Its inputs and tool were recorded by the paper's evidence
owner before the run, in `~/fv_paper/prereg/ADDENDUM_R6c_R6rb_inputs.md` (sha256 6ecf67c4...).

- **Pairs.** R6r's 862 frozen pairs, with the lists that `ADDENDUM_R6r_remeda_inputs.md` gives:
  - `r7_testable.txt`, sha256 fec09171...;
  - `r7_provable.txt`, 160 pairs, 14c45704...;
  - pair sources checked by `pairs_SHA256SUMS`, 41e73814..., verified before the run.
- **Tool.** Branch const-arrow at 9e54bdbc34af6edfd0d784d39a89944ad4307b80, difftool dist hash
  baf07b296e82b4bf. This is the R6c tool; tools/difftool/r6c/R6C_RESULTS.md describes its two commits.
  The worktree's HEAD moved to 8716145 during the run, but that commit adds only tools/difftool/r6c/.
- **Clone.** `~/strictts_ws/constarrow/scratch/rescan/clone_remeda`, a no-checkout clone of R6r's clone,
  HEAD d02c3bdb5e18cfa53e76f33f4ae525adce515379.
- **Disclosed before the run.** A rescan of remeda's history with 09d1e8c (first look (b) in the
  addendum) put 85 of the 160 frozen provable pairs in the subset. The run reads only the frozen lists.

## Results

One row per pair: `r6rb_table.tsv`, sha256 19b207064ac8b6dcf54747d5b723d7ca5638ba8aba4d5a690a562e910c54e9fd.

| verdict | R6r (bbe90b4) | R6rb (9e54bdb) |
|---|---:|---:|
| PROVED | 54 | 59 (all all-worlds) |
| REFUTED, confirmed by Lean | 9 | 9 |
| REFUTED, Node only | 55 | 55 |
| UNKNOWN | 744 | 739 |

Against R6r, pair by pair (`compare_r6r.tsv`): 5 pairs change, all from UNKNOWN to PROVED (all-worlds),
and every other pair has the same verdict. All 5 were module-level `const` arrows that R6r could not
compare ("target ... not found in the translation"):
- `sliceString` (eab73291, style);
- `noop`, `randomChar`, `trivialDefaultCase` (b08a667d, feat);
- `joinImplementation` (a5b389b8, chore).

What happened to R6r's 81 pairs with no translated target (`target_kind.tsv` in tools/difftool/r6r/):
- 5 are PROVED, as above.
- 75 are now UNKNOWN with a translation reason. For 68 it is only `unsupported-generic`: the curried
  helpers such as `_lazy` return generic function values, which StrictTS does not translate. For 7 it
  is `unsupported-generic`, `any-op`, `no-symbol` or `unsupported-conversion`, alone or two together.
- 1, `noop` at d1bae988, is UNKNOWN because the translated signatures differ: `() => undefined as any`
  became `() => undefined`.

No pair has "target not found" any more. The "provable" label of R6r's frozen list stays as frozen.
Translated with the new tool, 85 of those 160 pairs are in the subset; the other 75 are now rejected.

PROVED by commit intent:
- refactor/perf/style/chore: 29 (R6r: 27);
- fix/feat/revert: 26 (R6r: 23);
- docs/test/other: 4 (R6r: 4).

The 59 PROVED pairs:
- 52 are library source and 7 are the same test helpers as in R6r.
- 35 are proved at one generic instance (`inst` column). The 5 new proofs are of non-generic functions.
- No proof used the compatibility wrapper.

## The 64 refutations

They are the same 64 pairs as in R6r, with the same counterexamples:
- `replay_v2/replay.tsv` is byte-identical to R6r's, and all 64 reproduce;
- `tscheck.tsv` is byte-identical to R6r's: 27 calls type-check in both versions, 36 in neither and 1
  in the new version only;
- `refuted_export.tsv` is byte-identical to R6r's: 24 internal, 40 exported.

`refuted_export.tsv` was written by the fixed `export_check.sh` (a grep without a pipe; see R6c). The
same fixed script run on R6r's tscheck gives R6r's delivered table byte for byte
(`r6r_refuted_export_v2.tsv`).

The 11 confirmation blocks have the same pair-to-block mapping as R6r: the 9 confirmed refutations,
plus sampleImplementation (object identity) and swapArray (a designed panic).

## Recheck

The 19 Lean batch files were rechecked with `lake env lean --tstack=262144` at 8716145, whose Lean
sources are 9e54bdb's:
- 59/59 PROVED theorems print exactly `[propext, Classical.choice, Quot.sound]`;
- 59/59 have no error inside the theorem;
- all 100 axiom lines of the run's own outputs reproduce.

## Evidence

Directory `~/strictts_ws/constarrow/scratch/r6rb/`. Manifest R6RB_EVIDENCE_SHA256SUMS: 1,907 files,
sha256 178744873efaa4f5a522a27475f661df8a1d30d102fbda21b74d191a14b4f04e. It holds:
- `chunks/`: 29 chunks, all rc=0, no retries;
- `evidence/`: 19 batch files with their outputs and recheck outputs;
- `evidence_confirm/` (confirmations.tsv sha256 7f05987d...);
- `replay_v2/`;
- `tscheck_work/`;
- the table, the comparison, the draft tables and `refuted_export.tsv`;
- the scripts as run: `run_chain.sh`, `post_run.sh`, `report.js`, `cex_replay_v2.js`, `tscheck_cex.js`,
  `collect_confirm.js`, `export_check.sh`, `compare_tables.sh`;
- the logs, and `guard_secs.txt`.

Copies of the scripts and tables are in this directory.

## Cost

- **Compute: 0.92 core-h** over the 55 guarded jobs from 04:53:14Z to 05:40Z: run 0.79,
  post-processing and recheck 0.13. The run took 38 min of wall time.
- **Model:** the StrictTS lead session alone (claude-opus-5-5), with no helpers; the tool makes no model
  calls.
- **Tokens:** see R6c. R6rb ran within the same session window, and the two runs' token use is not split.

RESULT: R6 replay: all 46 PROVED es-toolkit theorems now also pass a kernel replay. Their 15 proof files, compiled to
oleans (7 of them after removing only the 16 failing non-PROVED theorem blocks), replay 15/15 rc 0 in leanchecker, and
the whole import closure (47 StrictTS modules at 10ec829) replays 47/47 rc 0; negative control BadCtl rc 1, GoodCtl rc 0.

# Kernel replay of the R6 proofs (an agent of the evidence owner; written 2026-10-26T22:54Z by date -u)
Gap closed: checks/r6-20261026T2004Z re-elaborated the 46 PROVED theorems with lake env lean but did not replay the
modules they import (claims audit, finding 3).

## Inputs
- Copy ~/fv_paper/replay/r6-20261026T2004Z (tree = StrictTS at 10ec829 with its build; 0 symlinks); the 15 proof files
  recheck/history-*.lean = the run's batch files (checks/r6-20261026T2004Z: 30/30 .lean/.out equal).
- Verbatim copies as modules R6Proof.B00-B14 in /home/user/fv_paper/replay/r6-20261026T2004Z/r6replay/orig (batch_map.tsv: name, file, sha256; copies identical).

## Proof files -> oleans (compile/, compile_one.sh; lean --tstack=262144 -R, LEAN_NUM_THREADS=1, guarded, pjobs N = 2)
- 8 files had no errors and compile unchanged (B01, B03, B04, B07, B08, B09, B11, B14).
- 7 files (B00, B02, B05, B06, B10, B12, B13) contain theorems that fail to elaborate, all non-PROVED: the 8 provable
  "no proof" UNKNOWN pairs and the all-worlds variants of the 3 pairs PROVED as allocated-arguments
  (= checks/r6-20261026T2004Z/recheck_error_theorems.tsv, 16 theorems). lean writes no olean for a file with errors, so
  derive.awk removed exactly those 16 blocks ([set_option ... in] theorem NAME ... #print axioms NAME, 20 lines each;
  derive_ranges.txt); diff shows deletions only (0 added lines).
- proved_blocks_identity.tsv: each of the 46 PROVED theorem blocks (theorem line through its #print axioms line) is
  byte-identical in the verbatim and the derived file (46/46 same).
- Compile: 15/15 rc 0 (compile/*.rc); the outputs print exactly [propext, Classical.choice, Quot.sound] for all 46 PROVED
  theorems; the word "Error" in B02/B05 outputs is #eval output of JavaScript throw messages, not a Lean error.

## Kernel replay (leancheck1lp.sh, explicit LEAN_PATH, guarded, pjobs_v3 2 450 150 2)
- R6Proof.B00-B14 (LEAN_PATH olean dir : tree build : toolchain): 15/15 rc 0 (replay_proofs/).
- Import closure of StrictTS and StrictTS.Proof.Literals (closure.py on the tree; closure_strictts.txt): 47 modules,
  47/47 replayed rc 0, none reused, none import-only (replay_strictts/). The proof files import nothing else.
- Negative control (evidence/controls/lc_neg oleans, read only): BadCtl rc 1 ("declaration type mismatch"), GoodCtl rc 0.
- Compute: 0.091 core-h (compile scheduler 0.060 + replay scheduler 0.031, all jobs guarded); replay wall sum 97 s.

## Disclosures
- Two test compiles (B00 failed as expected, B01 ok) ran under guards before the batch run; their olean outputs were
  overwritten by the batch run. Nothing was written outside this dir and /home/user/fv_paper/replay/r6-20261026T2004Z/r6replay.

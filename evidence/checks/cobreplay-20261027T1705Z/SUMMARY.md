# cobreplay: kernel replay of the coblean package at snapshot 20261024T2306Z (referee item M9(a))

An agent of the evidence owner (the evidence-owner session), 2026-10-27 17:04Z-17:2xZ (date -u). Copy: ~/fv_paper/replay/cobreplay-20261027T1705Z/coblean.

## Copy
- Source ~/coblean_snapshots/coblean-20261024T2306Z has no manifest of its own; I hashed it (find -L, 1,828 files;
  manifest_source.sha256 2f802e43...). cp -rL; 0 symlinks in the copy (the 4 source links are libcob/changelog links in
  third_party/gnucobol); the copy's manifest equals the source's file for file.
- lake build --no-build Cobol Examples cobolrun in the copy: "All targets up-to-date (115 jobs)" (lake_nobuild.log).
- All 68 module oleans of the copy are byte-identical to the from-source rebuild of the 10-24 check
  (replay/cobE3-20261024T2338Z; olean_vs_cobE3.tsv, 68/68 same).

## Which coblean modules were already in the migration replay
- The migration replay (checks/eqA8-20261025T1158Z): union of delta.replay (529 = 481 replayed + 48 import-only) and
  delta.reused.tsv (395) = 924 modules: 607 EquivLean, 249 Aeneas, 43 Cobol, 25 Jimple.
- The package has 68 modules: 43 Cobol.* (with the root Cobol), CobolRun, 24 Examples.* (with the root Examples).
  All 43 Cobol modules are inside the 924 (modules_in_924.txt): 42 reused (passed on the earlier copy, olean and closure
  identical) and the root Cobol import-only. CobolRun and the 24 Examples modules are outside (modules_outside_924.txt).
- The equiv-lean copy builds against its vendored coblean-20261024T2306Z: its 43 Cobol oleans and 43 Cobol sources are
  byte-identical to the snapshot's (vendored_vs_snapshot_oleans.txt).

## Replay
- leanchecker via tools/leancheck1lp.sh (LEAN_NUM_THREADS=1, timeout 1500 s, LEAN_PATH = the copy's .lake/build/lib/lean),
  each job under coreh_guard_v2 (cap 0.45), nice 10, ulimit -v 32 GiB; pjobs_v3.py N=2, load 450, 150 GB, floor 0 (the
  parent's instruction while an agent held the two always-allowed slots).
- 68/68 rc 0 (replay/*.tsv). Slowest: the root Examples module (imports only) 372.8 s; Examples.Cbtrn03cEvery 54.3 s.
- Controls (control/): BadCtl (a false theorem added with the kernel check skipped; compiled, #print axioms reports none)
  rc 1, "(kernel) declaration type mismatch"; GoodCtl rc 0.
- bv_decide: the one theorem with its native-evaluation axiom is bincnt_equiv in Examples.Binary, proved with the cobol_bv
  tactic (a macro in Cobol.Target.Bits, which defines no theorem with bv_decide). Examples.* is outside the 924, so the
  axiom is outside the module closure of every migration theorem. Examples.Binary replays rc 0.
- Core-h: 0.250 (outer guard of pjobs) + about 0.003 (copy, controls, no-build check). Disk: 559 MB (the copy).

## Proposed note a
"The 43 modules of the COBOL semantics library are part of the 924 modules above. The other 25 modules of the coblean
package, the COBOL-side program theorems, were replayed separately with leanchecker: 68 of 68 package modules return 0. One
theorem of the package, outside the closure of every claimed theorem, uses the native-evaluation axiom of bv_decide."

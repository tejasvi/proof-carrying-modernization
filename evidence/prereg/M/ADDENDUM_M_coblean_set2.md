# Addendum M, coblean, set 2 (PREREG_M_v1; DEVIATIONS 2026-10-25T18:11Z)

Written by the paper's evidence owner at 2026-10-25T19:07:15Z, after coblean froze the extended suite and before any set 2 candidate
is drawn by anyone else or run. This file is never edited; changes go to DEVIATIONS.md. Copies in `M/coblean_set2/`.

- Extended suite, frozen by coblean: set 1's 14 rows plus 9 new GnuCOBOL-differential rows with exact comparisons
  (X.cond, X.search, X.file2, X.func, X.refmod, X.sync, X.edsize, X.divrem, X.us2), on the same pin (coblean snapshot
  20261024T2306Z) and the same narrowed cobolrun. Harness mut_one_v3.py cd2204c493b4c28e..., run_order_v2.py
  63381fdb75e0c4df..., analyze_v3.py cfcd6d0f2ee6690e..., controls_v3.sh 1dc64246e3ba6305..., controls_v3.tsv
  0198158d6605da80....
- Manifest MANIFEST_reads.sha256, sha256 005257d21bbf04912f8f15c7e92c20ec83f5e61d7998446e5ef4222819c1f96b, 810 files.
  The evidence owner re-hashed every line: the base/ files equal the snapshot's, except the narrowed CobolRun.lean and
  the built cobolrun, which equal those of the prepared base (ws/base), as in set 1; the harness, suite, candidate and
  order files equal coblean's frozen copies.
- Baseline rows.json, sha256 446b0eec6bbfee15a638b87ee51e09e69c5e4b6bdf01769aefdb36be22278187: each new row 100 of 100
  cases ok; 12 old rows identical to set 1's baseline (runs/baseline_v2); V.hand and V.stm keep their outcomes (28 equal
  lines in 4 programs, none differing; AGREE) and now record the fields that set 1's analysis recomputed.
- Secret released: S2M = `fv-paper-prereg-M-coblean-set2-d08838f893de2147bb23c08a4872718faa861ecdbf92b4ffac1f588ab56173d2`; its sha256 equals the one committed at DEVIATIONS 2026-10-25T18:11Z
  (3bd54091bd5dadf03b6d4873a1c58b979e8bc20cd52999f48fbe0f63be52065a).
- Set 2 order: `M/draw_m.py candidates_m_coblean.tsv coblean order2_full.tsv --seed S2M --exclude set1_attempted_ids.tsv`
  (candidates e13311bd..., set 1's list; set1_attempted_ids.tsv 4dc827a4...: set 1's 30 attempted ids, equal to the
  first 30 of M/coblean/order.tsv) -> M/coblean_set2/order2.tsv (columns order, id; 1,081 ids, none from set 1), sha256
  8e8d5f9ac42ac3a004c08678130524ca6d4687142095e0c667416d8c78b4953c, checked by an independent recomputation.
- Runs, as DEVIATIONS 18:11Z fixes them, all on the 2306Z pin (the later fixes in coblean's live tree do not apply):
  the first 30 tested candidates of order2 on the old suite and on the extended suite (the headline compares the two on
  these mutants); set 1 on the extended suite in the order of order_set1.tsv (c6bb56bd...), labelled as not independent
  of the added tests. Set 1's 15 of 30 stays reported as is, and #4's equivalence label stays apart.

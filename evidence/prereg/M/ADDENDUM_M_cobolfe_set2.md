# Addendum M, coblean's front end, set 2 (PREREG_M_v1, Part FE)

Written by the paper's evidence owner at 2026-10-25T18:25:40Z, after coblean froze the extended suite and before any set 2 candidate
is drawn by anyone else or run. This file is never edited; changes go to DEVIATIONS.md. Copies in `M/cobolfe_set2/`.

- Extended suite, frozen by coblean: suite_ext_v1.json sha256 5308aa71673ff251040ed54ee5ac3cb935e6045403d1ae46c9c4a8923a1e4692
  (28 testers: the old 14 unchanged; X.hp, 22 hand-written programs compared line by line with GnuCOBOL, including the
  4 V.hand programs; 10 old front-end testers at new seeds; X.usfix, the fixed unstringtest at seeds 1, 11, 21). Freeze
  note FREEZE_NOTE_ext_v1.md 772959c3...; manifests SHA256SUMS_ext_frozen_v1.txt b5588d28... (33 files, verified by the
  evidence owner from ext_frozen_v1/) and inputs_ext_v1.sha256 1feecd2e... (967 files); baseline base_ext_v1.json
  c6db8ef1... (the old rows equal set 1's baseline; new cases ok except 6 named control-flow declines).
- Secret released: S2 = `fv-paper-prereg-M-FE-set2-8b8bb66c6bd04c98203e8fb674aee7739780bf069dc4a40dd6a869e9346e7da3`; its sha256 equals the one committed in PREREG_M_v1
  (e6e93c3f5a720ac5c188c0f4f7b7a3838497608ef522069357d0fa93c8b8e5c2).
- Set 2 order: `M/draw_m.py cands_cobolfe_v1.tsv cobolfe ... --seed S2 --exclude attempted.tsv` (attempted.tsv
  06cd7489...: set 1's 30 attempted candidates, all tested, equal to the first 30 of order_set1.tsv) ->
  M/cobolfe_set2/order_set2.tsv (columns order, id; 3,760 ids, none from set 1), sha256
  d2a136723885d90435ba80003298d6e7e46fd18e54e34338064d6ea5a7309380, checked by an independent recomputation.
- Runs, as PREREG_M_v1 fixes them: the first 30 tested candidates of order_set2 on the old suite and on the extended
  suite (the headline compares the two on these mutants); set 1 on the extended suite, labelled as not independent of
  the added tests.

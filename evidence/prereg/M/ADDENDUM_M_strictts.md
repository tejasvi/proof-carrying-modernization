# Addendum M, StrictTS (PREREG_M_v1)

Written by the paper's evidence owner at 2026-10-25T17:00:36Z, before any population mutant is built. This file is never edited;
changes go to DEVIATIONS.md. Copies of the files named here are in `M/strictts/`.

- StrictTS's draft of the frozen inputs, adopted as part of this addendum: ADDENDUM_M_strictts_draft.md, sha256
  8069cef60cb422caf21a448ada795e59e158ef937a054c83ad8564ddc8e96fb4 (pin ff30e09ba18d8b07b71246c49e6f6a2297f09f72; the
  five in-scope files with their sha256; the enumeration tool, the candidate list and the order; the harness at commit
  c833c55 of branch modular; the stillborn and sorry rules; the suite: corpus 180 programs, F64Diff mode all seed 1
  count 2,000,000, StrDiff seeds 1-6 on case files written once from the unmutated copy; the kill criterion; the
  extended suite for survivors with its cap rule; the stop rule).
- Checked by the evidence owner: the five files' sha256 equal those of a git archive of the pin; run_m.py
  (b8a63634...), suite_m.sh (ba1f00a3...) and config_strictts.json (afceac98...) have the stated sha256 at c833c55 and
  in the working tree; the tool's re-run gives the candidate list (a81f1cbb..., 1,601 candidates) byte for byte; the
  order is order.tsv (730900793ae7751931927f24d635752d0f30eec92f85bfe814e4d4e7f3efb8e9).
- Condition: the controls are re-run with the frozen harness (c833c55) before the first population mutant and must give
  the recorded verdicts (baseline passes everything; the no-op comment in Num/F64.lean survives; the Num/Format.lean
  edit outside the population is killed). The re-run's records and sha256 are sent with the results.

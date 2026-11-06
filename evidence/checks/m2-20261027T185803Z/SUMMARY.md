# Check by an agent: cirlean M2 delivery check (fork of the evidence-owner session)
Against prereg/M/ADDENDUM_M2_cirlean.md (bf94540c), plan v2 (67f301ef), PREREG_M_v1 kill criterion, DEVIATIONS 17:13:59Z
and the blinding re-seal (8649f149). Read-only; awk/sha256sum/grep only.

1. Seal PASS: ~/cirlean_work/mutation/M2/SHA256SUMS 05e0eb6a, 808/808 OK, no file outside it (788 files writable:
   hash-list seal). results_m2_delivery.tsv 2a0960e4, SUMMARY_M2.md 1bab709e, results_m2a.tsv 4126394c, results_m2b.tsv
   e31be885, GUARD_LOGS.txt 1ff0bce3.
2. Inputs PASS: suite/cases_m2.txt = 175 original cases (identical to frozen cases.txt 09a7dfe6) + 238 t_* lines equal to
   the t_* lines of fmt (85), fpx (63), strconv (90) case files in order; 0 ub_* lines (18 excluded: 10+4+4). New files =
   registered shas (list fba182fc). Tools: run_mutant_m_v3 aea36217, run_suite_m f3282ce8, case_m.sh d476943e,
   build_cirrun_v4 b92667cb, suite_build_m 14cc3eb9, enum_m_cirlean abec0384, drive_m2_v2 941b4f2d, prep_suite_m2_v2
   f259aaa6, compare_m2_v2 90a460e5 (registered); unregistered analysis scripts classify_baseline_m2_v1, delivery_m2_v1,
   summary_m2_v1. Baseline: rows 1-175 identical to M's control_baseline (174 MATCH + 1 UB); new part 157 MATCH, 4 MISMATCH,
   77 UB, identical case by case to baseline_classes (da9fec4c) at ffab71e. 157 new cases can kill.
3. M2a PASS: 30 rows = M's built orders; outcome, sorried list, original-part verdict and mutated sha256 equal M's
   (results_cirlean.tsv 29b12c0e, M's result.json files) 30/30. Kills: old 7, extended 17, new-only 10 (8 Float.lean, 2
   Eval.lean); orders 9 and 19 survived.
4. M2b PASS: 33 rows = order.tsv (c0eb75d1) orders 35-67; 3 stillborn (41, 56, 59: Basic.lean AOR, invalid pattern);
   30 built (prefix rule stops at 67). Kills: old 10, extended 24, new-only 14 (all Float.lean); survivors 3 Basic.lean,
   3 Eval.lean. Delivery table verdicts = my recount for all 60 built rows.
5. Order 37: suite row 266 (fpx t_lim 5) UB after 184.98 s; watchdog.txt "killed pid (cirrun) at VmRSS 24.1 GiB"; the
   unmutated cirrun passes it in 0.32 s (MATCH). The watchdog (rss_limit_gib 24, SIGKILL) is the same as M's driver
   drive_m_v4 (DEVIATIONS 2026-10-25T17:39Z); M had no watchdog event. The suite records UB where the baseline is MATCH,
   so the verbatim criterion counts it as a kill. With it 24/30, without it 23/30.
6. Controls PASS: no-op survived 413 cases (331/4/78 = baseline); known-bad killed at case 57. Guards: 75/75 log shas OK;
   outer M2a 1.095, M2b 1.067; all non-nested logs 2.305 core-h (delivery 2.293; prep nesting); no cap event.
7. Wilson 95%: 7/30 0.233 [0.118, 0.409]; 17/30 0.567 [0.392, 0.726]; 10/30 0.333 [0.192, 0.512]; 24/30 0.800
   [0.627, 0.905]; 23/30 0.767 [0.591, 0.882].
8. Baseline classes (238 defined new cases): ffab71e 157 MATCH; failures missing model 43, format/subset 30, unsupported
   op 4, documented limit 3 (long double as binary64), wrong value 1 (fpx t_lim 8: float division into the deep subnormal
   range gives +inf). e6ac99a 158 MATCH; 43, 30, 1, 6 (3 long double, 3 NaN sign), 0. ub_* lines MATCH at both pins: 3
   (fmt ub_fmt 3 "%#d", 4 "%.3c", 6 sprintf of a buffer into itself); rog's run files = inputs.sha256 (OK).

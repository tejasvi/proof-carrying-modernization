# Check by an agent: IBM-variant tester delivery of coblean (sealed_20261027T1813Z), checked 2026-10-27T18:22:32Z
Against prereg/ADDENDUM_IBMVAR_coblean.md (3853d1b4) and PRERUN_LIST_v1.txt (baff99bb; DEVIATIONS 18:02:00Z). Read-only; awk/sha256sum only.
1 PASS seal: SHA256SUMS 9e029500..., 221/221 OK, 222 files (= 221 + SUMS), 0 writable, 0 symlinks; runs/ 7777/7777 = RUNS_MANIFEST, 0 writable.
2 PASS inputs: testers in ~/coblean_ibmvar = 2306Z snapshot (difftest 0c25260b, ctrltest 8916bf7e, filetest af9b7b63, inspecttest
  92eda4a8, stringtest dfb968d6, unstringtest 8aa8c217; hand cases e6ebd229, 9087324f, 32840a41, 052f9411); runner v1 8625598f, v2
  036f12db = one-line diff (prerun/diff_run_v1_v2.txt), ctrltest only; table a99f6bfb; meta.json of all runs: IBM flags as listed,
  seeds 1/2 (+101/102 filetest), n=60, E2 n=4; the usual flags are in the unchanged testers (-fbinary-truncate string present in the
  dtstd binaries). Guard first stamps: every tester run 18:05:04Z or later (> 18:02:00Z); preparatory b1..self2 before 18:00:47Z;
  cov1 18:03:23Z and pkey1 18:04:04Z = D-1.
3 PASS recount (runs/*/results.jsonl, status and flagged fields; recount_status.txt): = delivery table. 964 programs: 953 agree
  (ok-negzero 4 = dtstd s1 2 + dtbin s1 2; ok-abend 7 = file s1 5 + s102 2; hv:ok-hvbyte 4; rawref ok 120 (stringtest receiver
  "01 R PIC X(8)", name collision)), 11 declined (ctrltest: 10 lean-unsupported-recursion, 1 resume), 0 mismatch outside CTL-A.
4 PASS controls: CTL-A (planted front end) caught 23 = exactly the 23 programs with an embedded-sign zoned DISPLAY field (my cross-tab
  from the layouts: emb caught 23, noemb agree 37); CTL-B 4 runs and CTL-C 17 runs: each expected = caught, missed 0, extra 0.
5 PASS E1: re-extracted IBM IR ab_ibm.json 2c5ba72b = shipped cbstm03ab.ir.json = 2306Z snapshot's; stmt 1212 / html 6082 records,
  0 differ; 0 displays after the walk on both sides; AGREE.
6 PASS probes: DISPSIGN pb.cob prints digits + separate sign (D1 000000000150-) under F0 (-std=ibm), F1, F2 (full IBM set), F3;
  probe_key1: indexed-file key order 1A 9Z A1 B2 Z9 (native) under F0 and F2, so EBCDIC key order cannot be checked with GnuCOBOL.
7 PASS coverage: COVERAGE.txt = delivery items 9-10 (classes covered; per-program untested list). "Covered" = construct class generated
  and compared, not the program's own instances; only E1 runs CardDemo programs (CBSTM03A + CBSTM03B).
8 PASS deviations/slips: D-1 as above; D-2 ctrl_s1/ctrl_s2 v1 guard exit 1, 0 results, kept; v2 exit 0; S-1 lane logs rc 0 vs guard
  exit 1 for ctrl_s1/s2; S-2 typed "about 18:06Z" corrected to 18:05:04Z in the next entry; S-3 as stated. Core-h 0.051 in 52 jobs.

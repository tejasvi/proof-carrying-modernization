RESULT: coblean 0050Z re-check AGREES with coblean's report: manifest 307/307 (de3366e5), source changes vs 1055Z exactly the INSPECT fix (Inspect.lean, Exec.lean, Eval.lean 1 line = coblean's diffs_live) + tester/evidence row/README, TH0 from source "Build completed successfully (115 jobs). | standard: 24 | bv_decide: 1" with the 25 axiom lines identical to the 1055Z re-check, Cobol.olean be3132eb, only Logic/Eval, Logic/FuelMono, Sem/Exec, Sem/Inspect oleans differ from 1055Z, 9 CardDemo IRs identical, TSV 191 identical + 3 line counts + 2 new rows, 78/78 re-run rows match, controls as stated (inspecttest on 1055Z 0/60 and 1/60; NC216A pass 57/57 on 0050Z, fail 56/57 on 1055Z).

# coblean live snapshot coblean-20261027T0050Z (INSPECT fix): evidence owner re-check (fork of the evidence-owner session)
Check dir: this directory; copies: ~/fv_paper/replay/cob0050-20261027T0052Z/{coblean, coblean_1055Z, nist_0050, nist_1055}.
Work 00:52Z-02:05Z on 2026-10-27 (date -u). Method as checks/cob1055-20261026T2004Z.

## 1. Manifest and copies
- Manifest ~/coblean_runs/c2fix/manifest_coblean-20261027T0050Z_v2.sha256: sha256 de3366e5c38cb325fa5b481a7897e5683c0d1cb1c67a235b949713c1508def46
  (= announced), 307 entries (264 sources + 43 Cobol oleans); sha256sum -c in the snapshot 307/307 OK before and after the runs.
- Full copies (cp -a) of 0050Z and of 1055Z (for the controls; 1055Z still 305/305 against its manifest a49973ce): diff -rq
  against the snapshots empty before and after all runs; 4 relative symlinks each, inside third_party/gnucobol.
- Live ~/coblean has moved on since 0050Z (Frontend/IR/Sem files differ; coblean's next items): diff_snapshot_vs_live_now.txt.

## 2. Diff 1055Z -> 0050Z (diff_1055Z_0050Z.txt)
- Lean: Cobol/Sem/Inspect.lean (+75/-1: doc line, InspView, unsignByte, inspView, resignByte, inspUnview), Cobol/Sem/Exec.lean
  (+42/-30: the .inspect and .convert arms read the item through inspView and store through inspUnview, BEFORE/AFTER regions
  located in the viewed bytes), Cobol/Logic/Eval.lean (+1: the four new definitions added to the cobol_eval attribute list).
  The three per-file diffs equal ~/coblean_runs/c2fix/diffs_live (bodies after the headers; src_diff_*.diff).
- Other files: tools/evidence/make_evidence.py (+4: rows V.ins.s1, V.ins.s2), new tools/difftest/inspecttest_signed.py
  (207 lines), README.md (+17/-3), HANDOFF_20261023.md, the new TSV. Nothing else outside .lake.
- Build products: Cobol oleans Logic/Eval, Logic/FuelMono, Sem/Exec, Sem/Inspect (oleans_vs_1055Z.txt; FuelMono rebuilt as a
  dependant, source unchanged), 5 Examples theorem-module oleans (not in the manifest; covered by TH0 and the TH rows), cobolrun.

## 3. TH0, oleans, IRs
- TH0 (cob_evidence_run.py, one CPU, LEAN_NUM_THREADS=1): rc 0, 1,740 s, "Build completed successfully (115 jobs). | standard: 24 |
  bv_decide: 1"; 0 error lines; the 25 axiom lines (th0_axiom_lines.txt) identical to the 1055Z re-check's; the bv_decide line is
  bincnt_equiv (BINCNT example), as before.
- Cobol.olean be3132eb...; exactly 4 Cobol oleans differ from 1055Z (above). The 9 CardDemo IRs are cmp-identical to 1055Z's and
  2306Z's (carddemo_irs.txt).

## 4. TSV (tsv_compare.txt) and re-run rows (results/, results_table.tsv, all_cmds.txt, pjobs.log)
- ~/coblean/docs/EVIDENCE_carddemo_live_20261027T0049Z.tsv sha256 e839d28f894f61f2... (= announced, = the snapshot's docs copy),
  196 rows. Against 1055Z's 3309d648: 191 rows identical apart from checked_utc; changed T4 3128->3191, T6 2118->2119,
  E4 6666->6730; new V.ins.s1, V.ins.s2 {"ok":60}.
- Re-run from my copy (78 rows, each under coreh_guard_v2, ulimit -v 32 GiB, one CPU): TH0 1/1, TH*.ax 25/25, TH*.st 25/25,
  IR.* 11/11, IRFE.* 9/9, IRB.examples 1/1, T4 3191, T6 2119, T7 3234, E4 6730, V.ins.s1 and V.ins.s2 {"ok":60} "60 cases,
  tester exit 0": 78/78 match the TSV's expected values.

## 5. Controls
- inspecttest_signed.py (0050Z's tester) with --tree the 1055Z copy: seed 1 {"ok": 0, "mismatch": 60}, seed 2 {"ok": 1,
  "mismatch": 59} (control/), = coblean's recorded controls.
- NC216A (NIST runner as in N2): NIST-variant copies of both snapshots made with the two NIST-pin diffs (parser.py D2;
  CobolRun.lean open-error hook, = the N2 tree's CobolRun.lean after patching) and the N2 tree's tools/nist; cobolrun built in
  each (88 jobs, one CPU); run_nist.py ~/nist_work/extract5 ~/nist_work/gc4 --only NC216A: 0050Z pass, 57 of 57 verdicts
  matching (PASS 57); 1055Z fail, 56 of 57 (one FAIL at INS-TEST-F1-23, the N2 failure). nist/.

## 6. The INSPECT model (read in Cobol/Sem/Inspect.lean and Exec.lean)
- inspView applies only to numeric USAGE DISPLAY signed items. A separate leading or trailing sign byte is left out of the bytes
  that INSPECT examines and put back unchanged afterwards. An embedded leading or trailing sign is removed from its byte
  (unsignByte: the byte becomes its plain digit; a byte that encodes no signed digit is invalidData); after REPLACING or
  CONVERTING, inspUnview puts the item's sign back on that byte (resignByte), and a replacement that leaves a non-digit there is
  unsupported. All other items are examined as their bytes, as before. TALLYING, REPLACING, CONVERTING and the BEFORE/AFTER
  delimiters work on the viewed bytes.
- This is IBM 6.4's table-1 rule as coblean cites it (examined as an unsigned DISPLAY item of the same length; a separate sign
  byte not examined and not replaced). For the copy-back of an embedded sign, on which IBM is silent, the model keeps the sign,
  as GnuCOBOL does; the module's doc comment states this.

## Compute and slips
- 0.938 core-h for the 78-row run (guard_outer.log) + about 0.05 core-h for the two cobolrun builds, NC216A runs and the
  inspecttest controls (nist/guard_*, control/guard_*).
- No slips. Written 2026-10-27T02:05Z.

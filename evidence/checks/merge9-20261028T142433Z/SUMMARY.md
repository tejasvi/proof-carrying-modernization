RESULT: PASS. Merge 9 (snapshot 20261028T1421Z) agrees with the COBOL maintainer session's report: the only front-end change is one condition in
tools/cobolfe/lexer.py, no theorem representation changes, defect E is absent on 1421Z and present on 1223Z, and the NIST
census is unchanged from merge 8.

# coblean snapshot coblean-20261028T1421Z (merge 9: lc-fix for defect E onto 1223Z): evidence-owner check (written 2026-10-28T14:32:09Z)
An agent of the evidence-owner session; check dir: this directory; replay dir ~/.claude/jobs/8a4f16ec/tmp/merge9_replay (fe1421Z, irs, probe,
tree, clm9m, root1421Z, lc). Read only on the snapshots and on the COBOL maintainer session's files. Guarded jobs (scripts/g_mine.sh: coreh_guard_v2,
ulimit -v 32 GiB); 25 guard logs, 0.024 core-h in all.

## 1. Inputs: PASS
- Producer manifest manifest_coblean-20261028T1421Z.sha256 (0ab8f11a2b4aaf1e, 583 entries): sha256sum -c in the snapshot,
  0 failures (manifest_check_snapshot.txt). d0_files_SHA256SUMS.txt (e2df2c6d8cac7819) 29/29 OK, checked from
  ~/coblean_runs/w3merge9 where its relative paths resolve (d0_files_check.txt).
- Source 1223Z -> 1421Z outside .lake (src_changed.txt, src_added.txt, src_removed.txt; src_changed_diffs.txt): changed
  tools/cobolfe/lexer.py (one condition: a ',' right after PIC / PICTURE [IS] that a non-space follows is no longer taken as
  a separator; plus a comment) and its __pycache__ .pyc, tools/difftest/editpttest.py (comments), tools/evidence/
  make_evidence.py (new V.lc rows), README.md, HANDOFF; added tools/difftest/lctest.py, lctest_mutants.md, lc_cases/
  (g_editlc, v_lc1, v_lcsep) and docs/EVIDENCE_carddemo_live_20261028T1421Z.tsv; removed none. Nothing under Cobol/ or
  Examples/. The 68 compiled oleans are byte-identical to 1223Z's (oleans_1223Z_to_1421Z.diff empty); Cobol.olean
  be3132eb.

## 2. Theorem rows (stored representations): PASS
- The nine stored CardDemo IR files of 1421Z are byte-identical to 1223Z's and to 2306Z's (the version of the migration
  theorems). With a copy of the 1421Z front end, the 8 programs, CBSTM03A + CBSTM03B linked, and CBSTM03B alone (= the
  pin2306Z-cbstm03b IR, 38fa862f) regenerate byte for byte; CSUTLDTC = the pinM3 IR (b38f9a39) and COBSWAIT = the pinM7 IR
  (f2ae5593) byte for byte (item2_irs.txt).

## 3. The fix of defect E: PASS
- The session's probe probe_efc1.cob (76b68fa2; probe/): the 1223Z front end reads E1 PIC ,ZZ9 as numEdited [z, z, nine]
  (3 positions, the comma lost); the 1421Z front end reads it as [comma, z, z, nine] (4 positions); E2 PIC B,ZZ9 is
  [b, comma, z, z, nine] in both (probe/fe_1223Z.json, fe_1421Z.json).
- End to end on a copy of 1421Z (tools, scripts, third_party, cobolrun e25416a4) against GnuCOBOL -std=ibm (lctest --run):
  the semantics prints C01 [,  5] and C02 [ ,  5] (IBM: the leading comma is written), GnuCOBOL [   5] and [    5]
  (the documented GnuCOBOL departure G-editlc: GnuCOBOL writes a space for a ',' with no digit position on its left).
- lctest.py (seeds 1 and 2, 60 programs each): {ok 19, ok-g 41} and {ok 29, ok-g 31}, i.e. 60/60 each (ok-g = lines where
  GnuCOBOL departs as G-editlc and the tester's IBM mirror accepts the semantics' line). results.jsonl and coverage.json are
  byte-identical to the session's runs w3merge9/t_lc_s1, t_lc_s2 and lcfix/ev_v4 (lctest_vs_producer.txt). The hand cases
  v_lc1 and v_lcsep: ok (lctest/hand.log).

## 4. NIST census on 1421Z: PASS
- scripts/build_m9_mine.sh: cp -rL of our merge-8 N3-recipe tree (checks/merge8-20261028T122832Z; 1223Z library, 1223Z
  parser.py with N2's D2 diff, the NIST pin's tools/nist, cobolrun 6f8a8f56), then tools/cobolfe/lexer.py replaced by
  1421Z's (e222a6ca = 1223Z -> e9af1d07 = 1421Z); parser.py, cobolfe.py and link.py are identical in 1223Z and 1421Z. No Lean
  file differs between the two snapshots, so cobolrun was not rebuilt.
- scripts/census_m9_mine.sh: the N3 commands (frozen run_nist.py 6635004c, COB_SWITCH_1=ON COB_SWITCH_2=OFF, no SYSIN;
  abend_status_v2, mechanism_v3, summarize_nist_v2), all six modules.
- Census: pass 236, fail 10, unsupported 61, undefined 1, timeout 0, error 1; per test 5,515 of 5,570
  (final_census_mine.txt). Equal, after normalising run paths, to our merge-8 census (census_m8_vs_m9.diff empty) and,
  in its totals and counted lines, to the producer's w3merge9/nist/final_census_w9m.txt (census_producer_vs_mine.diff empty).
- Our per-test parser (scripts/pertest_mine_v2.py) against our merge-8 run: 309 programs, 0 outcome changes, 0 entry
  changes (pertest_m8_vs_m9.txt). Run-time-dependent output lines were not compared.

## What rests on the session
- TH0 (the package's 25 in-repo theorems with the same 25 axiom lines) was not rebuilt here; no olean changed.
- The IBM expectations inside lctest's mirror are the session's reading of IBM's manual.

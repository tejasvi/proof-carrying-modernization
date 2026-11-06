RESULT: PASS. Merge 8 (snapshot 20261028T1223Z) agrees with the COBOL maintainer session's report: no stored theorem representation changes (all regenerate byte for byte, pins included), the 13 EditPoint theorems use only the standard axioms and replay, fixes A-D are present on 1223Z and absent on 0551Z, and the NIST census changes only NC107A (fail -> pass), giving 236/10/61/1/1.

# coblean snapshot coblean-20261028T1223Z (merge 8: editpoint-fix A, D, B, C onto 0551Z): evidence-owner check (written 2026-10-28T12:40:03Z)
An agent of the evidence-owner session; check dir: this directory; replay dir ~/.claude/jobs/8a4f16ec/tmp/merge8_replay (tree, irs, fe1223Z,
snap0551Z, snap1223Z copies (cp -rL, 0 links), testers, clm8m, editpt_lib/src). Read only on the snapshots and on the COBOL maintainer session's
files (~/coblean_runs/w3merge8, ~/coblean_runs/editfix). Guarded jobs (scripts/g_mine.sh: coreh_guard_v2, ulimit -v 32 GiB).

## 1. Inputs: PASS
- Producer manifest (194548170719e398, 577 entries): sha256sum -c in the snapshot, 0 failures (manifest_check_snapshot.txt);
  d0_files_SHA256SUMS.txt (e1ab846a) 25/25 OK (d0_files_check.txt); Cobol.olean be3132eb.
- Source 0551Z -> 1223Z (outside .lake): 9 changed, 16 added, 0 removed (src_changes_0551Z_to_1223Z.txt;
  src_change_linecounts.txt): Cobol/Edit.lean (+11/-3), Cobol/Sem/Data.lean (+7/-2), Cobol/Sem/Exec.lean (+4/-5),
  tools/cobolfe/parser.py (+5/-2), README.md, HANDOFF, tools/difftest/cov/cov_f4disp.py, deedittest.py,
  tools/evidence/make_evidence.py; added: tests/EditPoint.lean, editpttest.py, justtest.py, displittest.py with their cases
  and mutant notes, the new TSV. Nothing under Examples/ (the theorem sources) changed.
- Compiled oleans 0551Z -> 1223Z (oleans_0551Z_to_1223Z.txt): Cobol/Edit, Cobol/Logic/Eval, Cobol/Sem/Data, Cobol/Sem/Exec
  and 16 Examples/*.olean (the in-repo evidence theorems, rebuilt against the changed library; their sources unchanged);
  Cobol.olean unchanged (be3132eb). The four changed Cobol oleans that I built independently (section 5) are
  byte-identical to the snapshot's (oleans_mine_vs_snapshot.txt).

## 2. Theorem rows (stored representations): PASS
- The nine stored CardDemo IR files of 1223Z are byte-identical to 0551Z's and to 2306Z's (the version of the migration
  theorems). With a copy of the 1223Z front end, the 8 programs, CBSTM03A + CBSTM03B linked, and CBSTM03B alone
  (= pin2306Z-cbstm03b, 38fa862f) regenerate byte for byte; CSUTLDTC = the pinM3 IR (b38f9a39) and COBSWAIT = the
  pinM7 IR (f2ae5593) byte for byte (item2_irs.txt).
- So no theorem-relevant stored representation changes; the theorem pins are separate snapshots and are not touched. The
  library change does alter the compiled Examples oleans of this snapshot (section 1), whose 25 in-repo theorems the
  producer reports as building with the same 25 axiom lines (not rebuilt here).

## 3. tests/EditPoint.lean (fixes A and D leave the theorem pictures unchanged): PASS
- Compiled verbatim (as module EditPointCheck) against my independently built Cobol library, Lean v4.35.0, the lakefile's
  options, one thread (editpoint/compile.txt): rc 0. Its #eval compares old (0551Z, copied verbatim) and new editing on the
  four numeric-edited pictures of the theorem IRs: 880,040 comparisons each, 0 differences.
- The 13 theorems (gen_eq, editOpt_eq, minus_all, plus_all, z_all, nine_all; cs_comma_zero, star_comma, z_slash_implied,
  zero_lead, zero_lead_cs, comma_after_head, cs_comma_zero_deedit) each depend on exactly [propext, Classical.choice,
  Quot.sound]. Statements: old and new Edit.editOpt agree for every configuration, BLANK WHEN ZERO, value and scale on every
  picture without the changed cases (editOpt_eq); the four theorem pictures (CBTRN03C's -ZZZ,ZZZ,ZZZ.ZZ and +ZZZ,ZZZ,ZZZ.ZZ,
  CBSTM03A's Z(9).99- and 9(9).99-) satisfy that hypothesis (minus_all .. nine_all); the fixed cases give IBM's results
  (decide +kernel on concrete pictures and values).
- Planted controls: a sorry -> [sorryAx], a custom axiom -> [plantedAx] (both flagged).
- leanchecker --fresh EditPointCheck (its whole import closure from an empty environment): rc 0, 89 s (editpoint/fresh.txt); planted controls BadCtl rc 1 (declaration type mismatch), GoodCtl rc 0 (control/).

## 4. The fixes A-D on 0551Z and 1223Z: PASS
- Testers of the merge (my copies of both snapshots; testers.txt): editpttest (A, D) s1 {ok-g 60}, s2 {ok 3, ok-g 57},
  control on 0551Z s1 {mismatch 60}; justtest (B) s1 and s2 {ok 60}, control {mismatch 60}; displittest (C) s1 {ok 47,
  ok-unsup 13}, s2 {ok 48, ok-unsup 12}, control {mismatch 47, unsup-missing 13}. All 21 output files are byte-identical to
  the editfix runs mainD/ctlD, mainB/ctlB, mainC/ctlC (testers_vs_editfix.txt).
- Probe cases (--run on both copies): v_editpt1 (A) and v_editlead (D): ok on 1223Z, mismatch on 0551Z (for example L12
  "0  3.00" against 0551Z's "   3.00"); v_just1 (B): ok / mismatch; v_displit1 (C): ok on 1223Z (DISPLAY 2.5 shows 25),
  mismatch on 0551Z (2.5); u_displit_minus/plus: the 1223Z front end names a signed decimal literal unsupported, 0551Z
  printed -1.5 / 15 against GnuCOBOL.
- Known departures that remain: g_editins_pt (G-editins: GnuCOBOL keeps a 0 or / insertion character inside or right after
  a suppression or floating string, where IBM replaces it) and g_editptb mismatch against GnuCOBOL on both versions, as
  documented; the ok-g tallies are GnuCOBOL departures that the testers' IBM mirror accepts.

## 5. NIST census on 1223Z: PASS
- scripts/build_m8_mine.sh: cp -rL of our N3 replay tree (checks/nist3-20261028T072837Z; 0551Z + D2 + cobolrun_files_v3 +
  the NIST pin's tools/nist), the three 1223Z library files copied in (hashes before = 0551Z's), the 1223Z parser.py with
  N2's D2 diff (192a4e0f) applied at --fuzz=0 (offset only), lake build cobolrun rc 0 (88 jobs; cobolrun 6f8a8f56).
- scripts/census_m8_mine.sh: the N3 commands (frozen run_nist.py 6635004c, COB_SWITCH_1=ON COB_SWITCH_2=OFF, no SYSIN;
  abend_status_v2, mechanism_v3, summarize_nist_v2), all six modules, 12:32-12:34Z.
- Census: pass 236, fail 10, unsupported 61, undefined 1, timeout 0, error 1; per test 5,515 of 5,570
  (final_census_mine.txt). The census text equals the producer's final_census_w8m.txt after normalising run paths
  (census_compare_norm.txt empty).
- Our own per-test parser (pertest_mine_v2.py) against our N3 replay run: 309 programs, 1 outcome change, NC107A
  fail -> pass; 2 entry changes, JUST-TEST-04 #0 and #2 FAIL -> PASS, both equal to GnuCOBOL's PASS; nothing else
  (pertest_n3_vs_m8.txt). (Run-time-dependent output lines were not compared, only outcomes and per-test entries.)

## 6. TSV: as the producer states
- docs/EVIDENCE_carddemo_live_20261028T1223Z.tsv (07d3f2f6) against 0551Z's, columns 1-7 (checked_utc excluded): 257
  rows identical; values changed in E4, S2, T4, T7 (line counts +2, S2 a hash); claim text changed in V.cov.f4lit.s1/s2;
  11 new rows V.editpt.*, V.just.*, V.displit.* (tsv_compare.txt).

## 7. What rests on the COBOL maintainer session's statements
- The 25 in-repo theorems of this snapshot (TH0) were not rebuilt here; their axiom lines are the producer's report.
- The probes' expected IBM results are the session's reading of the IBM manuals as written in the testers.

## 8. Cost
- 0.166 core-h over 26 guard logs (guard_totals.txt); the snapshot copies, file hashing and comparisons ran as short unguarded commands.

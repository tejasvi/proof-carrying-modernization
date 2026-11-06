RESULT: coblean 2008Z (merge 3) re-check AGREES with coblean's report (all ten items PASS; no undeclared change). Written 2026-10-27T20:43Z (date -u).

# coblean snapshot coblean-20261027T2008Z (merge 3: collate-fix + odo-fix + 3 declared cleanups): evidence owner re-check (an agent of the evidence-owner session)
Check dir: this directory; copies ~/fv_paper/replay/cob2008-20261027T2011Z/{coblean (cp -rL of the snapshot), nist (tree, build, cl),
feid, irb, csutldtc_ir, out, results}. Method as checks/cob1730-20261027T1734Z (cob_evidence_run.py; pjobs_v3.py N=2 floor 0 under
load 450 / 150 GB; coreh_guard_v2 per job via scripts/g_mine.sh; ulimit -v 32 GiB).

1. Files and manifest: w3merge3/d0_files_SHA256SUMS.txt (92b45bc6) 14/14 OK. Manifest a59e8b4b, 406 entries: -c OK in the snapshot
   (before and after) and in my copy (0 symlinks) before and after the runs. Snapshot vs live: HANDOFF only. My copy after the runs
   differs from the snapshot only in 9 tools/cobolfe/__pycache__ files (not in the manifest).
2. Source 1730Z -> 2008Z (diff_1730Z_2008Z.txt; src_diff_*.diff): Lean IR.lean (+18: chr, amax, ord, ordA, alnumCmpSeq), Sem/Arith
   (+28), Sem/Data (+86: cmpSeq and the sequence functions), Sem/Exec (+2): collating sequences only, no ODO term. Frontend Surface
   (+30: AlphaPhrase, collating, afn; OdoDecl, odo, odoCheck), Resolve (+215/-5: Collation, alphaChars/alphaGroups/collation,
   seqValues; odoTable/odoDesc/odoDeclOk/odoCheck; ordMinMax), Load (+2 deriving). Layout.lean and Sem/File.lean unchanged: ODO lives in
   the front end (Python odo.py, parser.py, datadiv.py and the Lean Frontend), as declared. Python: parser.py (+244/-10; final sha
   c4b5d2b9 = progress.md cleanup 3), datadiv.py (+78/-8; hidden_num for ACCEPT FROM DAY), link.py (+4/-1: ODO tables of both linked
   programs), new odo.py, testers and cases; one SEARCH ALL key line ("a KEY names the table entry itself") is documented in
   progress.md as RO-P3, part of odo-fix. Cleanups match progress.md: tools/cobolfe/0 (aa4f8710) gone; g_initindex.cob 6e99394b ->
   0268000e (comment lines only); irindex2.cob 912ea85a new; initrepl_checks.sh 8b89de60 -> b3361d00. README E1-E3 present
   (SQ214A, IC207A, NC401M lines). No undeclared change.
3. TH0 from source in my copy (one CPU): rc 0, 1,587 s, "Build completed successfully (115 jobs). | standard: 24 | bv_decide: 1".
   th0_axiom_lines.txt (25) = the 1730Z check's = the 0518Z check's (normalised) = the TSV's TH*.ax expected lines = 2306Z's; the
   bv_decide line is bincnt_equiv. TH*.st expected hashes = 2306Z's (25); all 25 re-run match.
4. Oleans (oleans_*.txt): Cobol/* changed vs 1730Z 13, vs 0518Z 14, vs 2306Z 17 (CobolRun.olean also differs in each); Cobol.olean
   be3132ebc333738c.
5. IRs: the nine stored CardDemo IR files are cmp-identical to 2306Z's and 1730Z's (carddemo_irs.txt); regenerated with the 2008Z
   front end they are byte-identical (irfe_bytes2.txt; the linked cbstm03ab as ab.json), all 9 IRFE rows match; CBSTM03B alone
   (--sub --tab-width 4 -I app/cpy) = pin2306Z-cbstm03b's 38fa862f byte for byte (ir_cbstm03b.txt).
6. Front-end identity (scripts/identity_mine.sh; B = 1730Z tools/cobolfe, A = my copy; 459 NIST extract5 + 44 CardDemo): 503
   programs, 472 identical, 31 differ, 0 unexplained; the 31 names = coblean's identity_changed_programs.txt (20 collating, 11 ODO
   incl. IC207A, IC208A, CSUTLDTC); the CardDemo changes are CSUTLDTC (ODO) and DBUNLDGS, PAUDBLOD, PAUDBUNL (ACCEPT FROM DAY): none
   of the ten theorem programs.
7. TSV (tsv_compare.txt): EVIDENCE_carddemo_live_20261027T2008Z.tsv 4c670769, 237 rows; vs 1730Z's: 218 identical, 11 differ (T4
   3468, T5 1135, T7 4933, T9 "100 208", E4 7262, S2, CV.CSUTLDTC, CV.DBUNLDGS, CV.PAUDBLOD, CV.PAUDBUNL, CV.sum; value and expected
   only, commands unchanged), 8 new (V.coll.s1/s2, V.coll.hand, V.coll.gdep, V.acceptday, V.odo.s1/s2/mixed), 0 missing. Re-run in my
   copy (results_table.tsv, all_cmds.txt, pjobs.log): TH0, 25 TH*.st, 9 IRFE, the 11 changed and the 8 new rows: 54/54 rc 0, all match.
8. NIST (scripts/build_nist_mine.sh with cobolrun_files_v3.diff d1406e94 and the pin's D2 change; run_nist_mine2.sh;
   nist_final_mine.txt): IF105A IF119A IF123A IF127A IF128A IF129A NC114M NC214M NC219A NC235A NC247A SQ214A pass (SQ214A is
   standalone, no producer); NC401M stops at a level-66 RENAMES (front end); IC207A unsupported (fault at the unsupported CALL).
9. CSUTLDTC: CV row fe=ok, unsupported=0, resolves=yes, signal fault unsupported "CALL CEEDAYS" (run alone); CV.sum batch 14: front end
   ok 14, 0 unsupported 13, resolve 12, covered 11 (3938 lines). IR from the unmodified CardDemo source (CSUTLDTC.cbl 58c165dc) with the
   2008Z front end (-I app/cpy --tab-width 4; --sub gives the same bytes): raw sha256
   b38f9a39598bc1bfff7660da5e98e936d9d156c7e386a16f70327441dbefef16, jq -S 22b6eec9438d3a45f5aec610a2d3e9f72b6245f5741fba7ce675c1423edccce8
   (csutldtc_ir.txt).
10. link.py defect: coblean's exposure_g2_w4m_v1.sh (d36ba7db) re-run read-only from exposure/ (its two list files written there): output
   = coblean's exposure_g2.out (17cf69eb) byte for byte; 24 NIST callees and 19 callers all coll=0; CBSTM03A, CBSTM03B coll=0; the 8
   link cases coll=0; every program declaring COLLATING SEQUENCE is standalone. No exposure.

Cost: 61 guard logs, 0.478 core-h (guard_totals.txt; TH0 0.441), plus a few g1.sh calls (copy, IR generation, exposure scan).
Leftover: irfe_bytes.tmp (a first comparison pass, superseded by irfe_bytes2.txt; not removed under the no-rm rule).

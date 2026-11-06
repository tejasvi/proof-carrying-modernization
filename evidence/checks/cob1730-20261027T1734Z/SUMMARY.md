RESULT: coblean 1730Z re-check AGREES with coblean's report (all nine items PASS; no undeclared change). Written 2026-10-27T18:06Z (date -u).

# coblean snapshot coblean-20261027T1730Z (merge 1 + merge 2 since 0518Z): evidence owner re-check (an agent of the evidence-owner session)
Check dir: this directory; copies: ~/fv_paper/replay/cob1730-20261027T1734Z/{coblean (cp -rL of the snapshot), nist (tree,
build, cl, cl_sw, cl_sq2), feid, irb, out, results}. Method as checks/cob0518-20261027T0520Z (cob_evidence_run.py,
pjobs_v3.py N=2 floor 0 under load 450 / 150 GB, coreh_guard_v2 per job, ulimit -v 32 GiB).

1. Files and manifest: w3merge2/d0_files_SHA256SUMS.txt (d9a16d44) 12/12 OK (d0_files_check.txt). Manifest
   manifest_coblean-20261027T1730Z.sha256 = 6f20c167..., 365 entries; sha256sum -c OK in the snapshot, and in my copy
   (0 symlinks) before and after the runs. Snapshot vs live ~/coblean: only HANDOFF_20261023.md. My copy after the runs differs
   from the snapshot only in 8 tools/cobolfe/__pycache__ files (not in the manifest; copy_identity_after.txt).
2. Source 0518Z -> 1730Z (diff_0518Z_1730Z.txt; per merge diff_step1_0518Z_1626Z.txt, diff_step2_1626Z_1730Z.txt; per file
   src_diff_*.diff): Lean: Frontend/Resolve.lean (+35/-5: initLeaves/initTargets ignore the root's own REDEFINES;
   initRefMod gives SPACE to a reference-modified target, COMP/COMP-3/COMP-5 unsupported; FileDecl optional; varyingIdx),
   Frontend/Surface.lean (+6/-1: varyingIdx, optional), IR.lean (+9: optional, created, Env.absent), Sem/File.lean (+11/-3:
   status 05 on OPEN of an absent OPTIONAL file), CobolRun.lean (+15/-1: --absent). Python: tools/cobolfe parser.py
   (+586/-54), datadiv.py (+150/-4), cobolfe.py (+16/-2), link.py (+6), tools/evidence/make_evidence.py (+35); new tester
   files and cases under tools/difftest. All hunks fall under the declared changes (INITIALIZE (a)/(b), SELECT OPTIONAL,
   key clauses / reference modifiers / switches / INITIALIZE REPLACING / VALUE ALL ZERO, USAGE INDEX and PERFORM VARYING
   index names, the POINTER lowering in parser.py: "IBM rule 1a: a pointer is no receiver ..."); README documents each.
   tools/cobolfe/0 (junk) is in both 0518Z and 1730Z (declared). No undeclared change.
3. TH0 from source in my copy (one CPU): rc 0, 1,628 s, "Build completed successfully (115 jobs). | standard: 24 | bv_decide:
   1", no error lines. th0_axiom_lines.txt (25) = the 0518Z check's (normalised) = coblean's th0_axiom_lines_live_sorted_nopos;
   the bv_decide line is bincnt_equiv. TH*.st expected hashes in the 1730Z TSV = 2306Z's (th_st_2306Z.txt = th_st_1730Z.txt),
   all 25 re-run match; TH*.ax expected lines = 2306Z's.
4. Oleans (oleans_*.txt): vs 2306Z 15 Cobol/* oleans + CobolRun.olean differ, the same set as 0518Z vs 2306Z; vs 0518Z 7
   (Frontend/Load, Resolve, Surface, IR, Logic/Eval, Sem/Exec, Sem/File) + CobolRun; vs 1626Z 3 (Load, Resolve, Surface);
   Cobol.olean be3132ebc333738c in 2306Z, 0518Z, 1626Z and 1730Z.
5. IRs: the nine stored CardDemo IRs are cmp-identical to 2306Z's and 0518Z's (carddemo_irs.txt); regenerated with the 1730Z
   front end they are byte-identical (IRFE rows "same"; irfe_bytes.txt incl. the linked cbstm03ab ab.json), and CBSTM03B
   alone (--sub --tab-width 4 -I app/cpy) is byte-identical to pin2306Z-cbstm03b's IR 38fa862f (ir_cbstm03b.txt).
6. Front-end identity (scripts/identity_mine.sh, B = 1626Z tools/cobolfe = coblean's fe_premerge except the junk file "0",
   A = my copy): 503 programs (459 NIST extract5 + 44 CardDemo), 492 identical, 11 differ, all USAGE INDEX / PERFORM VARYING
   an index name (IC106A, IC107A, IC207A, IC208A, NC131A, NC133A, NC135A, NC206A, NC236A, NC241A, NC243A), 0 unexpected,
   0 CardDemo, 0 tied to POINTER and INITIALIZE (feid_summary.txt, feid_differ.txt) = coblean's identity_changed_programs.txt.
7. TSV (tsv_compare.txt): EVIDENCE_carddemo_live_20261027T1730Z.tsv 34223c3f, 229 rows; vs 0518Z's (754dfa69): 203 identical,
   5 differ (T4 3352->3360, T5 938->962, T7 3594->4240, E4 6949->6981, S2 53cf4dc1->81003962; value and expected only,
   commands unchanged), 21 new, 0 missing. Re-run in my copy (results_table.tsv; pjobs.log): the 5 changed rows, the 21 new rows
   (V.opt, V.reckey, V.rmexpr, V.sw, V.initrepl, V.ix, V.initptr, V.init at s1/s2, V.ix.mixed, V.hand_fes, V.swchk, V.irchk,
   V.ptrchk), TH0, the 25 TH*.st and the 9 IRFE rows: 61/61 rc 0, all match their expected values.
8. NIST (scripts/build_nist_mine.sh with cobolrun_files_v3.diff d1406e94 and the pin's D2 change; run_nist_mine.sh;
   nist_final_mine.txt): NC131A, NC133A, NC135A, NC206A, NC236A, NC241A, NC243A pass; IC106A and IC207A unsupported;
   IX217A (status 05) and IX218A pass; NC211A passes with COB_SWITCH_1=ON COB_SWITCH_2=OFF. SQ203A run alone fails at
   READ-TEST-GF-01 ("FILE PRESENT" in GnuCOBOL) because its producer did not run; with its SUBPRG group (SQ202A, SQ203A)
   both pass (cl_sq2). My harness artifact, not a semantics difference.
9. The three INITIALIZE defects of sec-limits are fixed at 1730Z: reference-modified target (initRefMod; rows V.init.s1/s2),
   a target with its own REDEFINES (initTargets ignores the root's clause; V.init.s1/s2, V.irchk), pointers set to zero
   (front-end lowering keeps pointers out of the MOVEs; V.initptr.s1/s2, V.ptrchk). CardDemo IRs unchanged.

Cost: 73 guard logs, 0.519 core-h (guard_totals.txt; TH0 0.452). Disk: copy 0.6 GB + NIST tree 0.6 GB + TH0 tree.
Process: the NIST build script's LRUN_AS was lowered from coblean's 64 GiB to 32 GiB (my brief's cap) before its run.

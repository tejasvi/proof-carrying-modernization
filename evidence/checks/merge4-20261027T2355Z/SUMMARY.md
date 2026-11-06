RESULT: coblean 2231Z (merge 4) re-check AGREES with coblean's report: all ten items PASS; no undeclared change (merge-conflict resolutions only). Written 2026-10-28T00:27:04Z (date -u).

# coblean snapshot coblean-20261027T2231Z (merge 4: nested-fix + altkey-fix + dynread-fix + merge fixes G1a-G4 + README E1-E5): evidence owner re-check (an agent of the evidence-owner session)
Check dir: this directory; copies ~/fv_paper/replay/merge4-20261027T2355Z/{coblean (cp -rL of the snapshot, 0 links), feid, irs, dynprobe,
gates, nist (tree, build, cl), nist_before, out, results}. Method as checks/cob2008-20261027T2011Z (cob_evidence_run.py; pjobs_v3.py
N=8 floor 2 under load 450 / 150 GB; coreh_guard_v2 per job via scripts/g_mine.sh; ulimit -v 32 GiB; LEAN_NUM_THREADS=1).

1. Files and manifest: w3merge4/d0_files_SHA256SUMS.txt (e3934417) 24/24 OK. Manifest c44a4d2e, 437 entries: -c OK in the snapshot and
   in my copy; copy = snapshot (diff -rq, 0 lines). Snapshot vs live now: HANDOFF_20261023.md only.
2. Source 2008Z -> 2231Z (diff_2008Z_2231Z.txt, set_*.txt, src_diff_*.diff, hunks/): 56 files differ, every one in the declared union
   (nested 1626Z->~/coblean_nested 37 files, altkey 1730Z->~/coblean_altkey 17, dynread ~/coblean_altkey->~/coblean_dynread 7, the six
   fix diffs, README_e1_e5.diff, the new docs TSV, 5 unsup cases renamed). Line containment (scripts/hunk_contain.sh): 1,416 added and
   144 removed lines; all but 15 added / 21 removed appear among the declared sources' changed lines; those are merge resolutions:
   link.py (2/1: the linked-program dict combining nested's inits/variants with merge 3's odo key), parser.py (1/2: odo key comma,
   combined import line), README (rewrapped unsupported-constructs paragraph from both sides; unsup_check row 51/51 -> 58/58, 10 -> 16
   controls). New files: 29 byte-identical to the branch files (19 nested, 8 altkey, 2 dynread); unit.py = nested's + 16 changed
   lines, all from fix_G1a/G2/G3/G4; renamed unsup cases n13_use_global, n14_external, u46_external_value, u47_external_size,
   n15_same_record = the branches' n08_use_global, n10_external, u24_external_value, u25_external_size, n08_same_record byte for byte;
   removed u01_declaratives, u09_initial, u19_data_external, u23_global (nested-fix) and u07_same_record (altkey-fix)
   (unsup_rename_check.txt, new_files_check.txt). Lean changes: Resolve +42/-4, Surface +10, IR +27, Logic/Eval +2, Sem/File
   +228/-12 (src_diff_counts.txt).
3. TH0 from source in my copy (one CPU): rc 0, 1,568 s, "Build completed successfully (115 jobs). | standard: 24 | bv_decide: 1".
   th0_axiom_lines.txt (25) = the 2008Z check's = the TSV's TH*.ax expected lines (th_ax_2231Z_tsv.txt); the bv_decide line is
   bincnt_equiv. The 25 TH*.st rows re-run: all match (= 2306Z's statement hashes).
4. Oleans and IRs: 43 Cobol oleans; changed vs 2008Z 7, vs 0518Z 14, vs 2306Z 17; Cobol.olean be3132ebc333738c (oleans_*.txt). The nine
   stored CardDemo IR files are cmp-identical to 2306Z's, 1730Z's and 2008Z's (carddemo_irs.txt); the 9 IRFE rows (regeneration with
   the 2231Z front end, jq -S equal) and the 11 IR.* rows match. CSUTLDTC regenerated from CSUTLDTC.cbl (-I app/cpy --tab-width 4):
   raw sha256 b38f9a39598bc1bf... = pin (csutldtc_ir.txt); CBSTM03B alone (--sub) = 38fa862f... = pin2306Z-cbstm03b (ir_cbstm03b.txt).
5. Front-end identity (scripts/identity_mine.sh; B = 2008Z tools/cobolfe, A = my copy; 459 NIST extract5 + 44 CardDemo): 503 programs,
   475 identical, 28 differ; the 28 names = coblean's identity_changed_programs.txt exactly (feid_names_*.txt); 0 CardDemo programs
   differ. Attribution: 19 nested (IC201A..IC401M; OBNC1M holds two programs, batched), 9 SAME RECORD AREA / alternate keys (IX205A,
   IX206A, RL401M, SG204A, SM203A via copybook K3IOB, SQ206A, ST131A, ST134A, ST135A) (feid_differ.txt).
6. TSV (tsv_compare.txt): EVIDENCE_carddemo_live_20261027T2231Z.tsv 888beeca, 243 rows; vs 2008Z's (columns 2-7): 227 identical, 4
   claim text only (V.decl.s1/s2, V.opt.s1/s2: "G-readfail left out"), 6 value and expected (T4 3468->3634, T5 1135->1168, T6
   2138->2140, T7 4933->6220, S2, E4 7262->7463), 6 new (V.nest/V.alt/V.dyn s1/s2, each {"ok":60}), 0 missing. Re-run in my copy
   (all_cmds.txt, pjobs.log, results_table.tsv): TH0, 25 TH*.st, 11 IR.*, 9 IRFE, IRB.examples, the 6 changed rows, the 10 tester rows
   V.nest/V.alt/V.dyn/V.decl/V.opt s1/s2, CV.CSUTLDTC and CV.sum: 65/65 rc 0, all match.
7. NIST (scripts/build_nist_mine.sh: D2 applied, CobolRun diff d1406e94, pin tools/nist, cobolrun rebuilt 363b39c8; run_nist_mine.sh):
   68 programs (IC module whole, 19 IX, SM203A/SM204A, 4 SQ, 6 IF, 12 NC): 59 pass, 8 unsupported, 1 error (IX401M), the same outcome as
   coblean's merged runs for all 68 (nist_coblean_merged.txt). The same lists on the 2008Z NIST tree of checks/cob2008 (read-only;
   run_nist_before.sh): 33 pass; 26 programs change, all to pass (nist_before_after.txt): IC201A IC203A IC209A IC213A IC223A IC224A
   IC225A IC226A IC228A IC233A IC235A IC237A (IC module 7 -> 19 pass), IX205A-IX215A (11, incl. IX210A/214A/215A), SM203A, SM204A
   (fail -> pass) and SQ206A. No run got worse.
8. Dynamic READ NEXT defect (the first post-check defect of sec-limits): probe coblean_runs/dynread/probe1/pr1_dynread.cob (5a5a4804),
   front end + cobolrun of each snapshot (dynprobe/, scripts/decode_displays.py): at 2231Z READ NEXT after a failed keyed READ gives
   status 46 (T04, T05, T11, T28; decoded output = coblean's fixed2/model.txt); at 2008Z it continues with 00 (= GnuCOBOL's output).
9. Gates (gates_mine.txt; fixes reversed per file with patch -R in replay gates/fe_noG2, fe_noG4): G2: fixed front end -> link.py
   refuses the callee ("PROGRAM COLLATING SEQUENCE differs from the caller's"); without G2 it links and the model prints Z>=A; the
   batch case under nestedtest.py --run: without G2 a mismatch (GnuCOBOL Z<A, model Z>=A), with G2 a fault unsupported. G4: fixed
   front end -> CSUTLDTC IR b38f9a39; without G4 the front end fails (rc 1, AttributeError).
10. Paper: (a) sec-limits, after the 2008Z sentences: "A later snapshot, 20261027T2231Z, which we re-checked as a labelled result,
   adds nested and batched programs with GLOBAL, EXTERNAL, INITIAL, CANCEL and CALL of a program named by a data item, START and READ
   by alternate record keys, and SAME RECORD AREA. Of the NIST programs we re-ran, 26 more pass, 12 of them in the IC module, and the
   representations of the ten CardDemo programs and of CSUTLDTC are unchanged." (b) the linker sentence: our gate re-check shows that
   the linker of 2231Z refuses a callee with another collating sequence (now ours, not only the session's report). (c) the first
   post-check defect: "Snapshot 20261027T2231Z fixes it; our probe gives status 46 there and 00 at 20261027T2008Z." (then the rule
   "sentences that begin with 'Our'" must cover it). (d) "In snapshot 20261027T2008Z, the latest we checked, ..." -> 20261027T2231Z
   (axioms, statements and IRs as in items 3-4). (e) Appendix A: add coblean 20261027T2231Z to the later COBOL versions. sec-stack's
   NIST numbers are for the theorem version and do not change.

Cost: 81 guard logs, 0.502 core-h (guard_totals.txt; TH0 0.435), plus g1.sh calls (copy, hunk containment).

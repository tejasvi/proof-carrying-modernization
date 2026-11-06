RESULT: coblean 0109Z (merge 5) re-check AGREES with coblean's report: items 1-9 PASS; both sec-limits defects (continued literal, de-editing MOVE) fixed by our probe runs; no undeclared change (README merge rewraps only). Written 2026-10-28T01:41:19Z (date -u).

# coblean snapshot coblean-20261028T0109Z (merge 5: corr-fix + copyrepl-fix with contlit + deedit-fix + merge fix R1 + README edits): evidence owner re-check (an agent of the evidence-owner session)
Check dir: this directory; copies ~/fv_paper/replay/merge5-20261028T0112Z/{coblean (cp -rL of the snapshot, 0 links), feid, gates, irs,
nist (tree, build, after, before_m4), probes (contlit, deedit, edit18, editpoint, cbexport), deedit_sound, out, results}. Method as
checks/merge4-20261027T2355Z (cob_evidence_run.py; pjobs_v3.py N=8 floor 2 under load 450 / 150 GB; coreh_guard_v2 per job via
scripts/g_mine.sh; ulimit -v 32 GiB; LEAN_NUM_THREADS=1). Read-only on the snapshot, the producer's files and merge 4's replay.

1. Files and manifest: w3merge5/d0_files_SHA256SUMS.txt (412d1339) 23/23 OK. Manifest 75429d92, 511 entries: sha256sum -c gives 0
   failures in the snapshot and in my copy (cp -rL, 0 symlinks); copy = snapshot (diff -rq, 0 lines); snapshot vs live now: 0 lines
   (.lake and __pycache__ excluded).
2. Source 2231Z -> 0109Z (files_*.sha256, set_changes*.txt, diff_2231Z_0109Z.txt, hunks/): 75 files added, 9 changed, 1 removed
   (unsup case u08_replace.cob); every path is in the declared union (declared_union.txt; HANDOFF aside). Changed: Cobol/Sem/Data.lean
   (+75/-2), Cobol/Logic/Eval.lean (+3), tools/cobolfe/parser.py (+195/-3), datadiv.py (+138/-1), copybook.py (+50/-2), source.py
   (+22/-10), README.md, tools/evidence/make_evidence.py, HANDOFF. Line containment (scripts/hunk_contain.sh against the corr, copyrepl
   and deedit branches and the fix diffs fix_R1_textmanip, README_R1, README_e1_e5): 729 added and 38 removed lines; not among the
   declared changed lines: 36 added / 17 removed, all in README.md (paragraphs rewrapped from both sides: the unsupported-constructs
   list, the front-end paragraph, the unsup_check row 16 -> 18 controls); 0 in code or Lean files. New files: 68 byte-identical to
   branch files; the other 7: the new TSV (derived), textmanip.py (= copyrepl's + the R1 fix exactly; textmanip_check.txt),
   g_replbatch.cob (= the producer's reproducer), and 4 renamed unsup cases (n16_corr_renames, u48_ren_index, u49_ren_odo,
   n17_replace = the branches' n11_corr_renames, u46_ren_index, u47_ren_odo, n09_replace byte for byte). tests/DeEditSound.lean
   (e13a7401) is new and not a lake target.
3. TH0 from source in my copy (row TH0): rc 0, 1,515 s, "Build completed successfully (115 jobs). | standard: 24 | bv_decide: 1".
   th0_axiom_lines.txt (25) = the TSV's TH*.ax expected lines (th_ax_0109Z_tsv.txt) = the merge 4 check's lines; the bv_decide line
   is bincnt_equiv. The 25 TH*.st rows re-run: all match; the TH*.st and TH*.ax rows are unchanged from 2231Z's TSV.
4. IRs: the nine stored CardDemo IR files are cmp-identical to 2231Z's and 2306Z's (carddemo_irs.txt); the 9 IRFE rows (regeneration
   with the 0109Z front end) and the 11 IR.* rows match. CSUTLDTC regenerated from the unmodified CSUTLDTC.cbl: raw sha256
   b38f9a39598bc1bf... = pin (csutldtc_ir.txt); CBSTM03B alone (--sub) = 38fa862f... (ir_cbstm03b.txt).
5. Front-end identity (scripts/identity_mine.sh; B = 2231Z tools/cobolfe, A = my copy; 459 NIST extract5 + 44 CardDemo): 503 programs,
   198 identical, 305 differ; the 305 names = coblean's identity_changed_programs.txt exactly; 0 CardDemo programs differ. Each of the
   305 contains a construct of a declared fix by my scan (feid_differ.txt): a literal continued over 3+ lines in the source or a
   copied copybook 302, a CORRESPONDING/RENAMES/level-66 word 10, a REPLACING/REPLACE word 12 (overlapping); no differing program has
   REPLACE with END PROGRAM (R1: 0). coblean's step attribution (corr 9, copyrepl 8, contlit 295, 7 programs in two steps, R1 0) was
   not re-run step by step; it is consistent with these sets (its corr 9 are 9 of my 10, the 10th SG101A; its copyrepl 8 include
   SM207A, whose COPY ... OF my pattern does not match).
6. TSV (tsv_compare.txt): EVIDENCE_carddemo_live_20261028T0109Z.tsv 1790ecef, 252 rows; vs 2231Z's (columns 2-7): 238 identical,
   5 changed values (T4 3634 -> 3676, T6 2140 -> 2142, T7 6220 -> 6937, E4 7463 -> 7507, S2 the README unsupported-section hash),
   9 new (V.corr s1/s2, V.crepl s1/s2, V.deedit s1/s2, V.crepl.hand, V.crepl.gdep, V.contlit), 0 missing. Re-run in my copy
   (all_cmds.txt, pjobs.log, results_table.tsv): TH0, 25 TH*.st, 11 IR.*, 9 IRFE, IRB.examples, CV.CSUTLDTC, CV.sum, the 5 changed
   and the 9 new rows: 63/63 rc 0, all match. The paper quotes none of the changed counts.
7. NIST (nist_check.txt; my tree: D2, CobolRun diff d1406e94, pin tools/nist; parts R S L K D M as the producer's
   nist_singles_w5m_v1.sh): newly pass NC207A NC208A NC209A NC222A SM201A SM202A SM206A SM207A SM208A SM401M (NC222A 8 of 8 tests,
   its two de-editing MOVEs included); NC401M now stops at "program: SPECIAL-NAMES SYMBOLIC"; NC252A passes RENAM-TEST-1..18 and
   stops at a COMPUTE exponent; NC202A and NC253A run to the end and fail exactly three tests, each after an ADD/SUBTRACT
   CORRESPONDING with NOT ON SIZE ERROR alone (cause C1). All 64 runs and the 25 IC-module programs equal the producer's after3; K, D
   and the IC module equal merge 4's after2. Before column, my own run of R S L on merge 4's NIST tree: 36 runs, 22 the same,
   14 differ (the 10 above to pass, NC202A/NC253A to fail, NC252A/NC401M later stops); none got worse.
8. The two sec-limits defects. (a) Continued literal (probe_contlit.txt): the session's probe v_contlit.cob at 0109Z: 5/5 lines =
   GnuCOBOL (middle lines keep their spaces to column 72); with 2231Z's front end, same runtime: 4 of 5 differ (L3, L4, C3, M4).
   (b) De-editing MOVE (probe_deedit.txt): the session's probe pr1_deedit.cob (1cf133b7), 37 MOVEs from numeric-edited items: 0109Z
   runs to stop with 74 lines; 2231Z faults invalidData at the first such MOVE. Against GnuCOBOL 3 lines differ: two de-edited
   values (a DB sign, README G-deedit-db; a 0 insertion character, G-deedit-zero; GnuCOBOL departs from IBM, as the README states)
   and one edited value (MOVE -0.001 to PIC -9.99: model -0.00, GnuCOBOL 0.00), which predates merge 5 (probe_edit18: the same at
   2231Z, for a literal and for a data item) and falls under the README's not-modelled negative zero.
   deEdit_sound (tests/DeEditSound.lean), elaborated against TH0's from-source tree (scripts/deedit_sound_mine.sh): rc 0, axioms
   [propext, Classical.choice, Quot.sound]; statement: for all c pic bwz bs w t, Sem.deEdit c pic bwz bs = .ok (w, t) ->
   Edit.edit c pic bwz w t = some bs or (w = 0 and Edit.edit c pic bwz (-1) (t + 1) = some bs). Proof status: proved; it restates
   the check that Sem.deEdit makes before it returns (Cobol/Sem/Data.lean:454-466: edit the candidate back and compare), so it bounds
   what a returned value can be and says nothing on which value IBM gives or on contents the model rejects. Agreement with IBM rests
   on the testers (V.deedit rows) and the probe, not on a proof.
9. Gates (sample; each fix fails without it): R1 (gate_r1.txt): the fixed front end makes g_replbatch differ from GnuCOBOL on
   L02-L04 (REPLACE ends at END PROGRAM, as IBM); with copyrepl's textmanip.py (no R1) it agrees with GnuCOBOL. contlit, deedit:
   2231Z fails the probes of item 8. corr, copyrepl: on merge 4's NIST tree the 10 programs of item 7 are unsupported (front end
   rejects level-66 RENAMES, REPLACING without BY, COPY ... OF, REPLACE; MOVE/ADD/SUBTRACT CORRESPONDING unsupported); on 0109Z
   they pass.
10. Proposed paper edits (not applied; sentences that begin with "Our" are ours):
   (a) sec-limits, after "...and of CSUTLDTC are unchanged." (line 112): "The next snapshot, \code{20261028T0109Z}, which we also
   re-checked as a labelled result, adds \code{MOVE}, \code{ADD} and \code{SUBTRACT CORRESPONDING}, level-66 \code{RENAMES},
   \code{COPY} with \code{REPLACING}, \code{OF} or \code{IN}, and \code{REPLACE}. Of the NIST programs we re-ran, ten more pass,
   and the representations of the ten CardDemo programs and of CSUTLDTC are unchanged."
   (b) second defect, after "...continues a literal over more than two lines.": "Our run of the session's probe shows that snapshot
   \code{20261028T0109Z} fixes it: there, the probe's five lines agree with GnuCOBOL; at \code{20261027T2231Z}, four differ."
   (c) third defect, after "...stops before its two such moves.": "Our run of the session's probe shows that snapshot
   \code{20261028T0109Z} fixes it: there, the probe's 37 such moves run to the end, where \code{20261027T2231Z} faults at the
   first, and the moved values differ from GnuCOBOL's only for a \code{DB} sign and a \code{0} insertion character, where the
   session reports that GnuCOBOL departs from IBM. Our NIST run of that snapshot passes all eight tests of NC222A."
   (d) fourth defect, append: "Our probe shows that snapshot \code{20261028T0109Z} still has it." (probe_editpoint.txt; its README
   names it M-editpoint.)
   (e) "In snapshot \code{20261027T2231Z}, the latest we checked" -> \code{20261028T0109Z} (items 3-4: same axioms and statements,
   IRs byte-identical and regenerated up to key order).
   (f) Appendix A, lines 15-17: "... \code{20261027T2008Z} (collating sequences and \code{OCCURS DEPENDING ON}),
   \code{20261027T2231Z} (nested programs, alternate keys and the fix of \code{READ NEXT} after a failed keyed read) and
   \code{20261028T0109Z} (\code{CORRESPONDING}, \code{RENAMES}, \code{COPY} \ldots{} \code{REPLACING} and \code{REPLACE}, and the
   fixes of continued literals and de-editing);"
   (g) optional, with its bound: "That snapshot also proves in Lean that a value the model de-edits edits back to the item's
   content; the theorem restates the model's own check, so it does not show that the value is IBM's."
   Unchanged: the defect list's opening (versions 20261024T2306Z to 20261027T2008Z, the session's report) and sec-stack's NIST
   numbers (theorem version).

Other checks
- The COBOL maintainer session's CBEXPORT/CBIMPORT RECORD KEY note (cbexport_cbimport_note.txt): SUPPORTED. Both name RECORD KEY EXPORT-SEQUENCE-NUM
  (CBEXPORT.cbl line 68, CBIMPORT.cbl line 40), defined in CVEXPORT.cpy (line 16), which both copy into WORKING-STORAGE; their FD
  records are PIC X(500). IBM Enterprise COBOL 6.4 Language Reference (local igy6lr40.txt b6f5e4f9, line 7888): "data-name-2 must
  be described within a record description entry associated with the file." Run: my copy's front end writes both IRs; cobolrun
  rc 1, "key EXPORT-SEQUENCE-NUM is outside the record area of file 6" (CBEXPORT) and "... file 1" (CBIMPORT), as the README says
  (the resolver rejects them).
- sec-migration lines 4-5 ("CardDemo has 44 COBOL programs. By a source-text rule (no CICS, DB2 or IMS calls), 14 of them are batch
  programs, and our front end covers 10 of these"): SUPPORTED. 44 .cbl/.CBL files; 14 with no EXEC CICS/SQL/DLI, CBLTDLI, AIBTDLI
  or DSNTIAR (carddemo_batch_rule.txt: the 12 CB* programs, COBSWAIT, CSUTLDTC); at the theorem version 10 covered: CBEXPORT and
  CBIMPORT rejected (above), COBSWAIT unsupported (ACCEPT FROM SYSIN, line 36), CSUTLDTC only from 20261027T2008Z (sec-migration
  line 227). A sentence giving CBEXPORT/CBIMPORT's reason (a RECORD KEY outside the file's record, which IBM does not allow) is
  also supported.
- Fourth post-check defect (edit point): still present at 0109Z (probe_editpoint.txt: PIC $$,.99 with 0 gives " $,.00", GnuCOBOL
  "  $.00"; the same at 2231Z), named in its README (M-editpoint).

Cost: 79 guard logs, 0.449 core-h (guard_totals.txt; TH0 0.408); the copy, hashing, diff, containment and comparison steps ran as
short commands without a per-job guard.

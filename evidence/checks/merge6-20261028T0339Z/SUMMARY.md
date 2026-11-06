RESULT: coblean 0336Z (merge 6) re-check AGREES with coblean's report: items 1-8 PASS; NIST: 6 programs newly pass (NC108M NC134A NC174A NC254A SM103A from unsupported, SM104A from fail), NC107A now runs and fails 2 of its 177 tests (both JUST-TEST-04), nothing worse; no undeclared change (README: two list joins and the derived unsup_check counts only). Written 2026-10-28T04:11:20Z (date -u).

# coblean snapshot coblean-20261028T0336Z (merge 6: class-fix + merge fixes N1 and N2 + README edits): evidence owner re-check (an agent of the evidence-owner session)
Check dir: this directory; copies ~/fv_paper/replay/merge6-20261028T0339Z/{coblean (cp -rL of the snapshot, 0 links), feid, irs,
gates (front ends nofix, n1, n2; runs), nist (tree, build, after, before_m5), probes/editpoint, out, results}. Method as
checks/merge5-20261028T0112Z (cob_evidence_run.py; pjobs_v3.py N=8 floor 2 under load 450 / 150 GB; coreh_guard_v2 per job via
scripts/g_mine.sh; ulimit -v 33554432 KiB = 32 GiB in the launching shell and in each row command; LEAN_NUM_THREADS=1).
Read-only on the snapshots, the producer's files and merge 5's replay (0 files there newer than this check's STAMP).
Hard links: none. lake-manifest.json lists no packages, and merge 5's build trees are 0109Z builds (8 of 43 Cobol oleans differ,
the producer's oleans_20261028T0336Z_vs_0109Z.txt), which lake would rewrite in place; third_party is 7.5 MB. So my copy and the
NIST after tree are fresh cp -rL copies (594 MB each), and merge 5's NIST tree served in place, read-only, as the before tree.

1. Files and manifest: w3merge6/d0_files_SHA256SUMS.txt (0f7edaff) 21/21 OK. Manifest 23568bf2, 536 entries: sha256sum -c gives
   0 failures in the snapshot and in my copy, before and after all runs; copy = snapshot (diff -rq, 0 lines) before the runs;
   after them only the 10 bytecode caches tools/cobolfe/__pycache__/*.pyc differ (not in the manifest; Python rewrote them
   because cp -rL gave the sources new mtimes). Snapshot vs live now: HANDOFF_20261023.md only (.lake and __pycache__ excluded).
2. Source 0109Z -> 0336Z (files_*.sha256, hunks/, readme_words/, newfiles_classdiff/): 27 files added, 10 changed, 2 removed;
   every path is in the declared union of 37 paths (hunks/declared_union.txt: class diff class_vs_2008Z_v1.diff eda3ef20,
   fix_N_parser.diff c89e1d45, README_N.diff 3d11cac4, README_postedit.diff 50aaabe3; HANDOFF and the new TSV aside). Added: the
   TSV and 26 class files; removed: unsup cases u02_class, u04_currency; each of these 28 equals its section of the class diff
   byte for byte, and the 26 added files equal ~/coblean_class's. Changed: Cobol/Data.lean (+3), Cobol/Edit.lean (+18/-3),
   tools/cobolfe/parser.py (+287/-4), datadiv.py (+51/-6), lexer.py (+9), tools/difftest/firstdiff.py (+1/-1), tools/records.py
   (+2/-1), tools/evidence/make_evidence.py (+36), README.md (+132/-49), HANDOFF. Line containment (scripts/item2_srcdiff.sh):
   539 added and 64 removed lines; not among the declared diffs' lines for the same path: 42 added / 35 removed, all in
   README.md; 0 in code or Lean files. Word level (scripts/readme_words.sh): of 1,223 README word changes, all but 4
   substitutions are word changes of the declared diffs, in order; the 4: unsup_check row 18 -> 22 controls and 69/69 -> 77/77
   (derived: 77 cases, 22 n-controls in tools/difftest/unsup_cases), and two list joins ("(G-editfloatsign)." -> ";",
   "unique." -> "unique,"); the other unplaced lines are the *Unsupported programs* paragraph rewrapped.
3. TH0 from source in my copy (row TH0): rc 0, 1,390 s, "Build completed successfully (115 jobs). | standard: 24 | bv_decide: 1".
   th0_axiom_lines.txt (25) = the TSV's TH*.ax expected lines (th_ax_0336Z_tsv.txt) = 0109Z's = merge 5's check = the producer's
   live lines (278e3cce); the bv_decide line is bincnt_equiv. The 25 TH*.st rows re-run: all match; the 50 TH .st/.ax rows are
   identical to 0109Z's TSV.
4. IRs (item4_irs.txt): the nine stored CardDemo IR files are cmp-identical to 0109Z's and 2306Z's; regenerated with my copy's
   front end, the 8 programs and the linked cbstm03ab are byte-equal to them; CBSTM03B alone = 38fa862f... = pin2306Z-cbstm03b;
   CSUTLDTC raw sha256 b38f9a39598bc1bf... = pin. The 9 IRFE and 11 IR.* rows match.
5. Front-end identity (scripts/identity_mine.sh; B = 0109Z tools/cobolfe, A = my copy; 459 NIST extract5 + 44 CardDemo): 503
   programs, 497 identical, 6 differ; the 6 = coblean's identity_changed_programs.txt (cb85451c) exactly; 0 CardDemo programs.
   Each has a merge-6 construct by my scan (feid_differ.txt): NC107A (DECIMAL-POINT IS COMMA, CURRENCY, BLANK WHEN ZERO), NC108M
   (CURRENCY, BLANK WHEN ZERO), NC134A (BLANK WHEN ZERO), NC174A and NC254A (CLASS), SM103A (DECIMAL-POINT IS COMMA in copybook
   K3SNA). N1/N2 exposure in the corpus: 0 (all 8 sources with such a construct have one PROGRAM-ID; feid_exposure.txt).
6. TSV (tsv_compare.txt): EVIDENCE_carddemo_live_20261028T0336Z.tsv 6946e352, 260 rows, vs 0109Z's 1790ecef, 252 rows (columns
   2-7): 248 identical, 4 changed values (T4 3676 -> 3683, T7 6937 -> 7226, E4 7507 -> 7514, S2 the README unsupported-section
   hash bce2f67a -> 5d217fc7), 8 new (V.class.s1/s2 and V.dpc.s1/s2 {"ok":60}; V.class.hand 2 programs, 38 lines, 0 differ;
   V.class.unsup 4 fe-unsupported; V.dpc.hand 3 programs, 50 lines, 0 differ; V.dpc.gdep g_ins0/g_floatcs/g_bwzv mismatches as
   listed and u_dpc_display fe-unsupported), 0 missing. Re-run in my copy (all_cmds.txt, pjobs.log, results_table.tsv): TH0,
   25 TH*.st, 11 IR.*, 9 IRFE, IRB.examples, CV.CSUTLDTC, CV.sum, the 4 changed and the 8 new rows: 61/61 rc 0, all match. The
   four tester runs' 60 generated programs and front-end outputs each are byte-identical to the producer's and to the class
   branch's runs (tester_programs_bytes.txt). The paper quotes none of the changed counts.
7. NIST (nist_check_v2.txt; my after tree from the snapshot: D2 at offset 1882, CobolRun diff d1406e94, pin tools/nist, lake build
   cobolrun rc 0; parts Q R S L B C O X A N K D as the producer's nist_singles_w6m_v1.sh; before = the same parts on merge 5's
   NIST tree, 0109Z): 173 program runs on each tree, 162 the same, 11 differ = 7 programs (some in two parts): NC108M (14/14),
   NC134A (20/20), NC174A (77/77), NC254A (9/9), SM103A (6/6) unsupported -> pass; SM104A fail (io 35) -> pass (7/7); NC107A
   unsupported -> fail, 175 of 177 tests agree, the two others JUST-TEST-04 .01 and .03 (nist_nc107a.txt). None got worse. All
   173 after runs equal the producer's (w3merge6/nist/after; 5 of them under other directory names); my before runs equal merge
   5's check runs on the same tree in all 89 shared runs.
8. Gates (gates_mine.txt; the producer's hand runner, byte copy 42467acc; front ends built here from my copy: nofix = the whole
   fix reversed = the producer's fe_nofix parser.py b161185a; n1 = nofix + hunks 2 3 5; n2 = nofix + hunks 1 4; nofix + n1 + n2
   hunks = my copy's parser.py). N1 (a contained program takes its outermost program's DPC, currency sign and classes): h3a, h3b,
   h3c fail with nofix and n2 (mismatch or front-end error), pass with n1 and with the fix; h3g goes from a front-end error to a
   named unsupported with n1. N2 (the DPC literal rewrite ends at the program's own END PROGRAM): h3d, h3e2, h3i, h3j fail with
   nofix and n1, pass with n2 and with the fix; h3h (nested and batched) needs both. Controls h3f2, h1c, h2a, h2b pass with all
   four front ends. The nofix and fix columns equal the producer's gates3.out.
9. Proof status and bounds: the 25 theorems are proved from source with unchanged statements and axioms (items 3, 6). The trusted
   semantics grows by 7 counted lines (T4): Cobol/Data.lean adds the picture symbol ESym.chars, and Cobol/Edit.lean maps the
   edited bytes of a picture that starts with it; on any other picture, Edit.edit is the old editOpt and classify is unchanged.
   No stored CardDemo representation has such a picture (they are byte-identical, item 4), and no theorem program uses CLASS,
   DECIMAL-POINT IS COMMA, CURRENCY SIGN or BLANK WHEN ZERO on numbers. The new constructs rest on the testers (V.class, V.dpc:
   60 of 60 at each of two seeds, hand cases, the GnuCOBOL departures named in V.dpc.gdep) and on NIST, not on a proof.
10. Proposed paper edits (not applied):
   (a) sec-limits, Table tab:snapshots, a new last row after 20261028T0109Z's:
       "\code{20261028T0336Z} & \code{SPECIAL-NAMES CLASS} and class conditions; \code{DECIMAL-POINT IS COMMA}; one-character
       \code{CURRENCY SIGN}; \code{BLANK WHEN ZERO} on unsigned \code{DISPLAY} numbers & 6 \\"
       (6 = programs newly passing; NC107A newly runs but fails, so it is not counted.)
   (b) sec-limits line 90: "Table~\ref{tab:snapshots} lists four later snapshots" -> "five later snapshots"; the shared facts of
       that paragraph hold for 0336Z (items 3-4).
   (c) No sentence "In snapshot ..., the latest we checked" exists in the paper now (search of every .tex except sec-ub.tex):
       nothing to change.
   (d) Appendix A (sec-appendix.tex lines 16-18): "... \code{20261027T2231Z} (nested programs, alternate keys and the fix of
       \code{READ NEXT} after a failed keyed read), \code{20261028T0109Z} (\code{CORRESPONDING}, \code{RENAMES}, more forms of
       \code{COPY}, \code{REPLACE}, and the fixes of continued literals and of de-editing) and \code{20261028T0336Z} (class
       conditions, \code{DECIMAL-POINT IS COMMA}, currency signs and \code{BLANK WHEN ZERO} on unsigned numbers);"
   (e) optional, sec-limits line 209: "still present in \code{20261028T0109Z}" -> "\code{20261028T0336Z}" (Other checks).
   No other paper sentence names these constructs (search of every .tex except sec-ub.tex).

Other checks
- Fourth post-check defect (edit point): still present at 0336Z (probe_editpoint.stdout: PIC $$,.99 with 0 gives " $,.00" and
  with 0.5 " $,.50", GnuCOBOL "  $.00" and "  $.50"; the same at 0109Z); the 0336Z README names it (M-editpoint, line 1279).
- Session findings, noted and not proposed for the paper: (a) JUSTIFIED: the 0336Z README (lines 1170-1172) reports that NC107A's
  two failing tests (JUST-TEST-04) move a group to a JUSTIFIED item, which the model's group MOVE fills from the left while
  GnuCOBOL justifies it on the right. Our NIST run agrees: the source names the form "MOVE GROUP ITEM TO ALPHABETIC JUSTIFIED
  ITEM"; .01 gives "ABC" at the left where the test expects "    ABC"; .03 also fails. (b) DISPLAY of a numeric literal with
  decimal places under DECIMAL-POINT IS COMMA: the README (lines 1164, 1719) states that the front end makes it unsupported and
  that how it shows is not checked (the model writes 1.5 without the clause, GnuCOBOL 3.2 writes 15 with and without it, IBM
  gives no rule); our V.dpc.gdep re-run shows u_dpc_display.cob fe-unsupported.
- Slips (disclosed): the short scripts item2_srcdiff, readme_words, newfiles_vs_classdiff, item4_irs, probe_editpoint and
  nist_compare(_v2) ran under their guards but without ulimit -v; the NIST tree's lake build cobolrun (5 s) ran under its own
  guard inside build_nist_mine.sh, not through pjobs_v3 (as merge 5's build script); one bare python3 call of
  cob_evidence_run.py without arguments printed its argument error and wrote nothing.

Cost: 75 guard logs, 0.460 core-h (guard_totals_final.txt; TH0 0.387); the copy, hashing, diff and summary steps ran as short
commands without a per-job guard.

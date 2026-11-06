RESULT: coblean 0518Z re-check AGREES with coblean's report: manifest 316/316 (1c63b866); source changes vs 0050Z are exactly the three merges (intrinsic functions, PERFORM VARYING AFTER + alphanumeric-edited, DECLARATIVES); TH0 from source in my copy builds (115 jobs) and its 25 axiom lines equal 2306Z's 25 TH*.ax lines exactly (24 standard + bincnt_equiv with bv_decide); TH*.st 25/25 equal 2306Z's; the nine CardDemo IRs are cmp-identical to 2306Z and 0050Z; 15 Cobol oleans differ from 2306Z and 13 from 0050Z, Cobol.olean be3132eb unchanged; 91/91 evidence rows re-run from my copy match (the 7 changed and the 12 new rows included); the controls fail as stated; the 43 NIST DECLARATIVES programs give 39 pass and 4 unsupported, per program equal to coblean's.

# coblean snapshot coblean-20261027T0518Z (three merges): evidence owner re-check (fork of the evidence-owner session)
Check dir: this directory; copies: ~/fv_paper/replay/cob0518-20261027T0520Z/{coblean (0518Z), coblean_0327Z, coblean_0050Z,
mut_ifn, mut1_decl, mut3_decl, nist}. Work 05:20Z-06:12Z on 2026-10-27 (date -u). Method as checks/cob0050-20261027T0052Z and
checks/cob1055-20261026T2004Z (tools/cob_evidence_run.py, pjobs_v3.py, coreh_guard_v2).

## 1. Manifest and copies (manifest_check.txt)
- Manifest ~/coblean_runs/decl/merge/manifest_coblean-20261027T0518Z.sha256: sha256 1c63b866d8b54653... (= announced), 316 entries;
  sha256sum -c 316/316 OK in the snapshot and in my copy, before and after all runs.
- Copies with cp -rL (the snapshot's 4 symlinks are relative and internal: libcob.so, libcob.so.4, two changelogs): 0 symlinks
  in each copy; diff -rq snapshot vs copy empty before the runs. 0327Z copy 314/314 against its manifest (70e85fc3...), 0050Z copy
  307/307 (de3366e5...).
- After the runs, my 0518Z copy differs from the snapshot only in 8 Python bytecode caches under tools/cobolfe/__pycache__
  (copy_identity_after.txt; not in the manifest; manifest still 316/316).
- Snapshot vs live ~/coblean now: only HANDOFF_20261023.md differs (diff_snapshot_vs_live_now.txt).

## 2. Source changes 0050Z -> 0518Z (diff_0050Z_0518Z.txt, 27 entries; per merge diff_step_*.txt; per file src_diff_*.diff)
- Intrinsic functions (0050Z -> 0245Z): Cobol/Frontend/{Load,Resolve,Surface}.lean, Cobol/IR.lean, Cobol/Sem/{Arith,Data,Exec}.lean,
  tools/cobolfe/{cobolfe,parser}.py, new tools/difftest/fntest_{num,date,alnum}.py, make_evidence.py, README, HANDOFF, TSV.
- PERFORM VARYING AFTER + alphanumeric-edited (0245Z -> 0327Z): front end only: tools/cobolfe/{datadiv,parser,pic}.py, new
  tools/difftest/{aftertest,aetest}.py, make_evidence.py, README, HANDOFF, TSV. No Lean source change.
- DECLARATIVES (0327Z -> 0518Z): Cobol/Frontend/{Load,Resolve,Surface}.lean, Cobol/IR.lean, Cobol/Logic/{Eval,FuelMono}.lean,
  Cobol/Sem/Exec.lean, tools/cobolfe/{link,parser}.py, new tools/difftest/decltest.py, unsup_cases/u01_declaratives.cob (now a
  USE GLOBAL case), make_evidence.py, README, HANDOFF, TSV.
- Lean lines vs 0050Z: Load +11/-3, Resolve +31/-3, Surface +12, IR +44, Eval +1, FuelMono +27/-6, Arith +103, Data +46,
  Exec +51/-12.

## 3. TH0, statements, oleans, IRs
- TH0 (row TH0 = scripts/recheck_build.sh: a fresh tree under out/TH0 without .lake, lake build Cobol Examples cobolrun, one
  CPU, LEAN_NUM_THREADS=1): rc 0, 1,455 s, "Build completed successfully (115 jobs). | standard: 24 | bv_decide: 1"; no error lines.
  The 25 axiom lines (th0_axiom_lines.txt) equal, line for line with names, the 25 TH*.ax expected lines of 2306Z's
  docs/EVIDENCE_carddemo.tsv (th_ax_2306Z_tsv.txt); the bv_decide line is bincnt_equiv (bincnt_equiv._native.bv_decide.ax_7).
  The multiset of axiom lists also equals the 0050Z re-check's.
- TH*.st: the 25 expected statement hashes are identical to 2306Z's (th_st_2306Z.txt = th_st_0518Z.txt), and all 25 re-run match.
- Cobol oleans (oleans_vs_2306Z_0050Z.txt): 15 of 43 differ from 2306Z (Edit, Layout, IR, Frontend/{Load,Resolve,Surface},
  Logic/{Eval,FuelMono}, Sem/{Arith,Data,Exec,File,Inspect,StringInto,Unstring}); 13 differ from 0050Z (the same without Edit and
  Layout); Cobol.olean be3132ebc333738c... unchanged. = coblean's lists.
- The nine CardDemo IR files (eight theorem programs + cbstm03ab) are cmp-identical to 2306Z's and 0050Z's (carddemo_irs.txt).

## 4. TSV and re-run rows (results/, results_table.tsv, all_cmds.txt, pjobs.log)
- ~/coblean/docs/EVIDENCE_carddemo_live_20261027T0518Z.tsv sha256 754dfa69f7efe87e... (= announced, = the snapshot's copy), 208
  rows. Against 0050Z's TSV (e839d28f): 189 rows identical (value, command, expected); changed expected values T4 3191->3352,
  T5 899->938, T6 2119->2138, T7 3234->3594, E4 6730->6949, T9 "91 199"->"98 206", S2 69d6b1c7...->53cf4dc1...; 12 new rows
  V.fn.{num,date,alnum}.s{1,2}, V.after.s{1,2}, V.ae.s{1,2}, V.decl.s{1,2}; none removed (tsv_compare.txt). = coblean's list.
- Re-run from my copy (91 rows, pjobs_v3 N=2, each under coreh_guard_v2, ulimit -v 32 GiB, one CPU): TH0 1, TH*.ax 25, TH*.st 25,
  IR.* 11, IRFE.* 9, IRB.examples 1, T4, T5, T6, T7, E4, T9, S2 and the 12 new V rows: 91/91 match the TSV's expected values
  (V.fn.* and V.after/ae {"ok":60}; V.decl.s1 {"ok":58,"ok-abend":2}, V.decl.s2 {"ok":57,"ok-abend":3}; tester exit 0).

## 5. Controls (control/, scripts/controls.sh; each job guarded, one CPU)
- DECLARATIVES: decltest.py copied into my 0327Z copy (its own front end and cobolrun): s1 and s2 {"frontend-unsupported": 60}
  (= coblean). Mutants on copies of 0518Z, recipes from ~/coblean_runs/decl/merge_progress.md: mut1 (the two find? predicates
  of useProc? swapped, file-named USE no longer first), build 88 jobs, s1 4 mismatch, s2 6 mismatch (= coblean 4+6); mut3 (ioErr
  returns dflt whenever dflt is a normal end, i.e. no USE when the file has FILE STATUS; CobolRun imports Cobol.Frontend.Load
  so that the FuelMono proofs, which break, are not built), build 50 jobs, s1 50, s2 41 mismatch (= coblean 50+41).
- Intrinsic functions: fntest_{num,date,alnum}.py with --root my 0050Z copy, seeds 1 and 2: all 360 programs fe-unsupported
  (= coblean). Planted errors on a copy of 0518Z (control/mut_ifn.diff; coblean's exact recipes are not recorded, so these are
  mine, from the README's description): RANGE as MIN - MAX (Resolve.lean), 1700/1800/1900 leap years (leapYear also true
  for y < 2000), z not upper-cased (ASCII upperByte up to 0x79). Build 88 jobs; seed 1: num 59 mismatch, date 28 mismatch,
  alnum 11 mismatch (coblean reports 59, 33, 11; the date count differs because the leap-year mutants differ).
- PERFORM AFTER / alphanumeric-edited (not asked, cheap): aftertest.py and aetest.py copied into my 0050Z copy: aftertest s1, s2
  0 ok / 60 mismatch; aetest s1, s2 0 ok / 60 error (coblean: 0/60 on 1055Z).

## 6. NIST, the 43 DECLARATIVES programs (nist_final_mine.txt; scripts/nist_decl_mine.sh, build_n2_v2_mine.sh)
- As coblean's nist_declmerge_v1.sh (side "after"), on my 0518Z copy: N2 tree built with my copy of nist_work/tools/build_n2_v2.sh
  (only its guard wrapper path changed, so that guard logs go to this check dir): D2 and the CobolRun.lean file-options diff apply
  by patch, tools/nist equals the NIST pin's, lake build cobolrun rc 0; frozen run_nist.py per module (SQ, IX) with --only the 43
  programs of ~/coblean_runs/decl/n2_decl_programs.txt; post-step abend_status_v2.py.
- Result: 39 pass, 4 unsupported: SQ203A and IX218A (a runtime unsupported fault; coblean: SELECT OPTIONAL), IX208A (START by an
  alternate key), SQ215A (CLOSE ... WITH LOCK). Per program identical to coblean's ~/nist_work/decl/merge/final_after.txt; coblean's
  final_before.txt (0327Z) has all 43 unsupported.

## 7. What the paper's limits section can now say (sec-limits.tex, "Validation by testing")
- The sentence that the front end drops declaratives with only a warning stays true of the versions of the paper. The sentence
  "A later front end ... stops every such program instead" is now superseded: in this later version, USE AFTER STANDARD
  EXCEPTION/ERROR declaratives are modelled (decltest 60/60 on two seeds with controls and mutants as above), 39 of the 43 NIST
  programs that use declaratives pass, and the other 4 stop on other unsupported statements; USE GLOBAL (declaratives of nested
  programs) is still stopped as unsupported (unsup case u01).
- This version also adds 12 intrinsic functions and PERFORM VARYING AFTER and alphanumeric-edited pictures; their testers pass
  (6 rows) and fail as expected on the older trees. I did not re-run the NIST IF module or the 21 previously blocked programs
  (coblean reports IF 4 -> 16 pass and 12 of 21 pass, on live).
- Unchanged and confirmed at this version: the COBOL package's own theorems build from source with the same 25 axiom lines and
  the same statements; the nine CardDemo IR files are byte-identical to 2306Z's and the front end regenerates them (IRFE 9/9);
  the 0050Z INSPECT fix and the earlier fixes are kept (their rows are among the 189 identical rows and the re-run rows).
- The closure oleans of the migration theorems are not the 2306Z ones at this version (15 Cobol oleans differ), so this is a
  re-check of the COBOL package and its evidence, not of the migration theorems, which stay at 2306Z.

## Compute and disclosures
- Rows: 0.887 core-h (91 guarded rows, guard_cob0518.log). Controls and NIST: 0.091 core-h (26 guarded jobs, guard/). Total about
  0.98 core-h.
- First attempt of the controls and the NIST run (05:57Z-05:59Z) failed at once because my guard wrapper scripts/g_mine.sh was
  not executable (rc 126, control/controls_attempt1.out, nist_decl_attempt1.out); fixed by calling it through bash. That attempt
  left a partial NIST tree (nist/tree_after, nist/build_after) in my replay dir, unused; the run used the *2 names.
- Written outside my two directories: nothing. Copies of decltest.py (into my 0327Z copy) and of aftertest.py/aetest.py (into my
  0050Z copy) are in my replay dir. Git was not used. Written 2026-10-27T06:12Z.

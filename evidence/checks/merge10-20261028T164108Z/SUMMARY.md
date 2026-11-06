# merge-10 check (an agent): coblean-20261028T1636Z

Written 2026-10-28T16:56:17Z; check started 2026-10-28T16:41:08Z. Directory: /home/user/fv_paper/evidence/checks/merge10-20261028T164108Z

Verdict: CONFIRMED. All six obligations discharged; every compared output equals the producer's (bytes, or after run/tree path
reduction), with one explained difference class (powtest control details.jsonl: detail strings cut at a fixed length of the
unreduced work path).

## 1 Inputs (manifest_check_snapshot.txt, d0_files_check.txt, src_*.txt, src_changed_diffs.txt, src_change_linecounts.txt)
- Producer manifest manifest_coblean-20261028T1636Z.sha256 (sha 349d588b, 619 entries), sha256sum -c in the 1636Z snapshot: 0 failures.
- d0_files_SHA256SUMS.txt (sha 1d1f0d13): 45 of 45 OK.
- Source diff 1421Z -> 1636Z: 19 changed, 36 added, 0 removed; no file under Examples/ changed or added.
  Changed: Cobol/Frontend/Load.lean (+1), Resolve.lean (+26), Surface.lean (+8), Cobol/IR.lean (+30), Cobol/Logic/FuelMono.lean (+6),
  Cobol/Sem/Arith.lean (+32), Exec.lean (+19), File.lean (-2 +66); tools/cobolfe/parser.py (-8 +163), link.py (-1 +5), unit.py (-1 +5)
  and two pyc files; tools/difftest/filetest.py, filetest_cases/fe_close_phrases.cob, g_lockclose.cob; tools/evidence/make_evidence.py;
  README.md; HANDOFF_20261023.md.
  Added: tools/difftest/closetest.py, closetest_mutants.md, close_cases/ (14), powtest.py, powtest_mutants.md, pow_cases/ (17),
  docs/EVIDENCE_carddemo_live_20261028T1636Z.tsv.

## 2 Theorem rows (item2_irs.txt, oleans_1421Z_to_1636Z.diff)
- The 9 stored CardDemo IRs are byte-equal to 1421Z's (and 2306Z's), and the 1636Z front end regenerates each byte for byte:
  cbact01c 26ab6e5f, cbact02c 1c4c76c9, cbact03c 0b595702, cbact04c 59d5918d, cbcus01c 60216395, cbtrn01c fe0ffd1e, cbtrn02c 20ac4c44,
  cbtrn03c e04dea09, cbstm03ab 2c5ba72b; CBSTM03B alone 38fa862f (pin 2306Z); CSUTLDTC b38f9a39 (pinM3); COBSWAIT f2ae5593 (pinM7).
- Compiled modules: 32 .olean files differ in bytes from 1421Z: 9 library modules (Frontend Load, Resolve, Surface; IR; Logic Eval,
  FuelMono; Sem Arith, Exec, File) and 23 Examples modules (AcctInt, AcctIntRust, Binary, RecSum and 19 CardDemo modules) whose sources
  are unchanged: they were recompiled against the changed library. Theorem-relevant compiled modules therefore changed; the theorem
  sources and their IR inputs did not. Their proof status on the 1636Z oleans is item 3.

## 3 FuelMono (fuelmono.diff, lake_build.txt, oleans_mine_vs_snapshot.txt, axioms/)
- Diff: two new arms of the execStmt monotonicity proof (268a269,274), .fcloseOpt and .fopenRev, each closed by simp only [execStmt]
  and the same repeat'/first tactic as the existing I/O arms (ResLe.refl or ioFinishU_mono, split). No other proof text changed.
- Own N3 tree (build.log): a fresh cp -rL of the merge-9 check's tree (0 links), the eight changed Lean files, link.py and unit.py
  from 1636Z (each old copy asserted equal to 1421Z first), parser.py = 1636Z + D2. lake build cobolrun Cobol.Logic.FuelMono: 88
  jobs, rc 0; the 10 library oleans (Load, Resolve, Surface, IR, Eval, FuelMono, Arith, Exec, File, Cobol) equal the snapshot's
  byte for byte.
- #print axioms in a fresh process (AxM10.lean, AxM10b.lean): of FuelMono's 6 theorems, execStmt_mono, execStmts_mono, runFrom_mono,
  Program.run_resLe and Program.run_mono depend on exactly [propext, Classical.choice, Quot.sound]; ioFinishU_mono on [propext] only.
  Of the 25 in-repo COBOL theorems (TH0 list, including the two primed names), 24 depend on exactly the standard three; bincnt_equiv
  also on bincnt_equiv._native.bv_decide.ax_7. These 25 lines equal the producer's check_th0_ax_sorted_nopos_w10m.txt line for line.
- Planted controls (AxCtl.lean): a theorem closed by sorry prints [sorryAx]; a theorem using a declared axiom prints [plantedAx].

## 4 Features (feat_close.stdout, feat_pow.stdout, pow_ctl_details_check.txt)
- The testers in the snapshot equal the producer's scratch copies (bytes). Both snapshots used read only (testers and front end run
  with -I -B); no file in either snapshot is newer than each run's start marker.
- 1636Z: closetest s1 60 ok, s2 60 ok; powtest s1 4 ok, 37 ok-g, 19 ok-unsup; s2 3 ok, 40 ok-g, 17 ok-unsup. results.jsonl and
  coverage.json (and powtest details.jsonl) byte-equal to the producer's runs; per-case statuses equal.
- Controls (same testers, --root = 1421Z): closetest s1 45 frontend-error, 14 frontend-unsupported, 1 ok; s2 44, 14, 2; powtest s1
  19 unsup-mismatch, 41 fe-unsupported; s2 17, 43. results.jsonl and coverage.json byte-equal to the producer's; per-case statuses
  equal. powtest control details.jsonl: every field except detail equal; in 60 of 60 lines per seed one detail string is a prefix
  of the other after path reduction (the tester cuts it at a fixed length of the unreduced work path); the producer's own comparison
  of these files with ifn2's ctl2 reports the same DIFFERS line.
- Hand rows on 1636Z: close hand (4 programs), unsup (8), gdep (2); pow hand (1), gdep (4), unsup (12): each text equals the
  producer's after run/tree path reduction.

## 5 NIST (census_run.stdout, final_census_mine.txt, census_producer_vs_mine.diff, pertest_m9_vs_m10.txt)
- All 309 programs re-run with the N3 commands on my copy of 1636Z (D2 front-end diff applied, --fuzz=0; run_nist.py 6635004c;
  COB_SWITCH_1=ON, COB_SWITCH_2=OFF; abend_status_v2, mechanism_v3, summarize_nist_v2).
- Census: pass 246, fail 11, unsupported 50, undefined 1, timeout 0, error 1; per test 5780 of 5836. The normalized census equals
  the producer's (diff empty).
- Against our merge-9 run (merge9-20261028T142433Z): 11 outcome changes, as listed: NC250A unsupported -> fail; NC252A, SQ109M,
  SQ110M, SQ123A, SQ124A, SQ211A, SQ215A, SQ303M, IX204A, IX216A unsupported -> pass. 100 per-test entry changes, all inside these 11
  programs, all to PASS. NC250A: 114 of 115; its one failing test is IF--TEST-28 (defect G), an entry unchanged from our merge-9
  run's partial NC250A report. No other program or test changed. SQ401M stays unsupported (LINAGE clause).

## Limits
- The 23 Examples oleans were not rebuilt independently: the axiom check loads the snapshot's Examples oleans together with library
  oleans byte-equal to my rebuild.
- cobolrun binaries differ in bytes (mine 35d6fc36, snapshot 7022112a): my N3 tree's driver CobolRun.lean is N3's cobolrun_files_v3
  copy (05522fe7; the snapshot's is b532231d). NIST ran on mine (the N3 recipe), the feature tests on the snapshot's; both agree
  with the producer's outputs.
- Mutants (MC2, MP7) not re-run; run-time lines not compared; paper text not checked.
- Compute: 0.065 core-h over all guarded runs (guard_coreh.txt).

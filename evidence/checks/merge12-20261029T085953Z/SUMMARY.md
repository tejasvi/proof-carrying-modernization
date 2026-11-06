Verdict: CONFIRMED. All eight obligations discharged and every producer claim holds: TH0 115 jobs, 24 + 1 axiom lines equal to
the producer's and merge 11's; the 6 changed oleans reproduced byte for byte; resolver checks byte-equal to the producer's;
pins, identity 503/503, all tester runs, both mutants and the NIST census equal; the probes stop with their named messages.
Three explained differences: 9 same-source oleans record their absolute build path; T7 is 1 lower on my tree (D2 diff, as in
merge 11); the snapshot's cobolrun binary is not byte-equal to the producer's scratch build (all outputs equal).

# merge-12 check (an agent, fork of the evidence-owner session): coblean-20261029T0854Z
Check 2026-10-29T08:59:53Z - 2026-10-29T09:41:46Z (date -u). Directory: /home/user/fv_paper/evidence/checks/merge12-20261029T085953Z;
replay dir (own tree, mutant tree, census, tester, probe, identity and TSV runs): /home/user/fv_paper/replay/merge12-20261029T085953Z.
Method: the merge-11 check (merge11-20261028T211008Z, SUMMARY.md with its TSV addendum) adapted to 2106Z -> 0854Z. Snapshots,
the producer's dirs and the earlier replay copies were read only.

## 1 Inputs (scripts/item1_inputs.sh; item1.stdout, manifest_check_snapshot.txt, d0_files_check.txt, src_*.txt, oleans_*)
- Producer manifest manifest_coblean-20261029T0854Z.sha256 (sha 3be9a8c28138f150, 667 entries), sha256sum -c in the 0854Z
  snapshot: 0 failures. d0_files_SHA256SUMS.txt (sha bd1738c2f98693f6): 71 of 71 OK.
- Source diff 2106Z -> 0854Z (outside .lake): 11 changed, 35 added, 0 removed. Changed: Cobol/Frontend/Resolve.lean (-41 +652),
  Cobol/IR.lean (-5 +31), Cobol/Sem/Arith.lean (-9 +44), tools/cobolfe/parser.py (+66) and its pyc, tests/DmaxResolve.lean
  (-11 +548), tools/difftest/dmaxtest.py (-22 +423), dmaxtest_mutants.md (-3 +15), tools/evidence/make_evidence.py (-6 +66),
  README.md (-42 +193), HANDOFF_20261023.md (+152). Added: docs/EVIDENCE_carddemo_live_20261029T0854Z.tsv,
  tests/Ar2Resolve.lean, tools/difftest/ir30test.py, ir30test_mutants.md, case files (ir30 11, powlit 6, pow0 3, c30 8;
  dmax_cases g_fnarg1, v_fnarg1, v_rmode1). No file under Examples/ changed or added.
- Compiled modules: of the snapshot's 68 .olean files exactly 6 differ from 2106Z: Cobol/Frontend/Load (2a9056fa),
  Cobol/Frontend/Resolve (fcc2c7e2), Cobol/IR (db6ebd65), Cobol/Logic/Eval (9219e7de), Cobol/Sem/Arith (1bae4d91),
  Cobol/Sem/Exec (8824071a).

## 2 Theorem rows, pins, resolver checks (scripts/item2_irs.sh, postbuild_m12.sh (c), resolve_mypop_m12.sh; item2_irs.txt,
## postbuild.stdout, dmaxresolve.out, ar2resolve.out, mypop.stdout, dmaxresolve_mypop.out, ar2resolve_mypop.out)
- The 9 stored CardDemo IRs equal 2106Z's (and 2306Z's), and the 0854Z front end (copy, 0 links, -I -B) regenerates each byte
  for byte: cbact01c 26ab6e5f, cbact02c 1c4c76c9, cbact03c 0b595702, cbact04c 59d5918d, cbcus01c 60216395, cbtrn01c fe0ffd1e,
  cbtrn02c 20ac4c44, cbtrn03c e04dea09, cbstm03ab 2c5ba72b; CBSTM03B alone 38fa862f (pin 2306Z); CSUTLDTC b38f9a39 (pinM3)
  and COBSWAIT f2ae5593 (pinM7) regenerate equal to their pins.
- tests/DmaxResolve.lean (dac6cecf) and tests/Ar2Resolve.lean (dacdc7ed), = 0854Z's, run in my tree on my build with the
  producer's final lists: both outputs equal w3merge12/rc_dmax_m4.out and rc_ar2_m4.out byte for byte. DmaxResolve: theorem
  IRs 15 of 15 same (old resolver and 2106Z's), pin IRs 2 of 2 same, R1 list 6 of 11 same, population 415: 409 same vs
  2106Z. Ar2Resolve: theorem IRs 15 of 15 same; 417 files (with plants): 408 same, 9 different.
- My own population (the two pins and the 320 front-end outputs of my census, 0854Z front end + D2; 322 files): both checks
  give 316 same, 6 different: IF119A, IF123A, IF124A, IF133A, IF138A, NC250A, the same six programs as the producer's lists;
  Expr.ir30 nodes only in IF133A (4) and NC250A (9), no ir30open node and no pow0 node anywhere; theorem and pin IRs same.

## 3 Build, oleans, axioms (scripts/build_m12_mine.sh, postbuild_m12.sh (a, b); build.log, lake_build.txt,
## oleans_mine_vs_snapshot.txt, axioms/)
- Own tree: fresh cp -rL of the merge-11 check's tree (0 links; chmod -R u+w in my copy only, then 0 read-only and 0
  hard-linked files); Resolve.lean, IR.lean and Arith.lean asserted = 2106Z, then copied from 0854Z; parser.py asserted =
  2106Z + D2, then 0854Z + D2 (--fuzz=0, offset 2138 lines = the 66 new lines; 66579bdea74c9dae); tests/DmaxResolve.lean and
  tests/Ar2Resolve.lean from 0854Z. lake build cobolrun Cobol Examples, one core: Build completed successfully (115 jobs).
- Oleans: 68 paths on both sides; 58 byte-equal to the snapshot's, among them the 6 changed ones and Cobol.olean (2a9056fa,
  fcc2c7e2, db6ebd65, 9219e7de, 1bae4d91, 8824071a, be3132eb). The other 10: CobolRun (N3's driver, a different source by
  design) and Cobol/Logic/Alnum, Cobol/Logic/Summary, Examples/Cbact01c, Cbact04cAll, Cbact04cEvents, Cbact04cEvery,
  Cbact04cSum, Cbtrn02c, Cbtrn02cDup, whose sources equal 0854Z's (diff -r of Cobol/ and Examples/ empty) and whose oleans
  record the absolute source path (my tree's, the mutant copy's and the snapshot's /home/user/coblean/...
  path each give different bytes; Alnum: b1057cc2 tree, 5e471a7c mutant copy, 767554b7 snapshot).
- TH0: the build log has 25 'depends on axioms' lines. #print axioms in fresh processes (axioms/AxM12.lean = AxM11.lean)
  against my build and, separately, the snapshot's: 25 lines each, 24 x [propext, Classical.choice, Quot.sound], bincnt_equiv
  also bincnt_equiv._native.bv_decide.ax_7; sorted, they equal the producer's check_th0_ax_sorted_nopos_w12m.txt, the
  merge-11 check's axm11_sorted.txt, the snapshot build's lines and my build log's lines. Planted controls (AxCtl.lean):
  sorry -> [sorryAx], declared axiom -> [plantedAx].

## 4 Testers and mutants (scripts/item4_m12.sh, helpers_cmp_m12.sh, mutants_m12.sh; item4_m12.stdout, helpers_cmp.stdout,
## mutants.stdout; runs in R/testers, R/mut)
- 0854Z's dmaxtest.py, ir30test.py, ext_common.py, classtest.py, cobolfe.py and parser.py equal the producer's scratch copies
  (bytes); its cobolrun binary does not equal the scratch's current one (the snapshot holds the live tree's own build).
- ir30test parts ir30, powlit, pow0, c30 at s1, s2 (--root 0854Z) and their controls (--root 2106Z): 16 runs; dmaxtest's 8
  parts at s1, s2: 16 runs; controls for fnarg, fncond, rmode: 6 runs. Every run's results.jsonl, coverage.json,
  details.jsonl and per-case statuses equal the producer's final runs (w3merge12/b3), bytes or after run/tree path
  reduction, and so do the 6 hand texts (ir30 11 programs, powlit 6, pow0 3, c30 8, dmax.hand 8, dmax.gdep 4). On 0854Z every
  generated case is ok, ok-g or ok-stop (e.g. ir30 s1: ok-stop 23, ok-g 33, ok 4; c30 s2: ok 44, ok-stop 16); the controls
  on 2106Z fail as the producer's do (ir30 s1: stop-mismatch 23, mirror 32; fnarg: mirror 60; fncond s2: mismatch 28,
  lean-signal 8; rmode s1: mirror 21).
- The same 38 runs and 6 hand texts compared directly with the helpers' official runs (ar2-fix tA2, tB2, tC4, tC3 with
  controls and hand texts; inr-fix B2_* and ev_rest2; merge 11's d_* for the five old dmaxtest parts): 120 files equal, 0
  differ. No file in either snapshot is newer than the run's start.
- Mutants, own runs of the producer's texts in a copy of my built tree: MC1 (Arith.lean: a zero base to the literal power 0
  never a size error): ir30test pow0 s1 mirror 55, ok-stop 3, ok 2; MB1 (Resolve.lean: option (c) off): dmaxtest rmode s1
  mirror 21, ok-g 20, ok 19 (hand: v_rmode1 mismatch); results, coverage, details, statuses and hand texts equal the
  producer's mu5 runs. After the restore and a rebuild, all 45 build outputs (Cobol oleans, cobolrun) equal my tree's except
  Alnum and Summary (the recorded path, above).

## 5 NIST (scripts/census_m12_mine.sh, census_cmp_m12.sh; clm12m_*, final_census_mine.txt, census_cmp.stdout, census_*,
## per_program_*)
- All 309 programs re-run with the N3 commands on my tree (0854Z + D2, COB_SWITCH_1=ON, COB_SWITCH_2=OFF; frozen run_nist.py;
  abend_status_v2, mechanism_v3, summarize_nist_v2). Census: pass 247, fail 10, unsupported 50, undefined 1, timeout 0,
  error 1; per test 5781 of 5836. The normalized census equals the producer's final_census2_w12m.txt (final tree, nist/c2)
  and final_census_w12m.txt (diffs empty).
- Per program (outcome, kind, model PASS/total, detail) against the merge-11 check's run: all 309 lines identical, so no
  outcome change. Against the producer's c2 run: identical except 6 front-end rejection texts where my 160-character cut of
  the detail falls at a different place (the cut precedes run-path reduction).

## 6 Evidence TSV (tsv/: compare.py, tsv_compare.txt; tsv_rows_m12b.sh, rerun_cmp.py, prep_tree2.log, rerun_compare.txt)
- 325 rows against 2106Z's 300: 293 identical, 7 changed (T4 3780 -> 3807, T5 1248 -> 1675, T7 7413 -> 7467, S2 README
  section sha ce52b585 -> ddf15f7b, E4 7698 -> 8152; the claim text of V.dmax.hand and V.dmax.gdep), 25 new
  (V.dmax.{fnarg,fncond,rmode}.{s1,s2}, V.{ir30,powlit,pow0,c30}.{s1,s2}, hand / gdep / unsup rows of ir30, powlit, pow0,
  hand / unsup of c30), 0 missing (checked_utc ignored).
- Re-run with the 0854Z make_evidence.py on my tree (merge 12's changed and added files copied in from 0854Z, logged; C = my
  tree; in bwrap with /tmp bound to my dir, no network): 42 rows (the 7 changed, the 25 new, V.dmax's 10 unchanged tester
  rows); 41 equal in every column but checked_utc; T7 gives 7466 on my tree because my parser.py carries the D2 diff, and its
  command on the snapshot gives 7467 (as in merge 11). The first attempt stopped at its own guard (HANDOFF_20261023.md in my
  tree is an older N3-lineage copy); v2 logs and replaces such copies.

## 7 D0_EVIDENCE (evidence/: cite_check_m12.py, cite_check.tsv, cite_check_plant.tsv, urls_*; scans/; after_census.stdout)
- D0_EVIDENCE.md da111dc9; ibm/URLS.tsv 1951454d: 50 of 50 cached files match their recorded sha256.
- Own quote checker (cite_check_m12.py): 37 of 37 IBM quotes occur at the cited lines of the cached pages (whitespace
  normalised); planted control (one word of Z0.4 altered): NOTFOUND, 36 of 37.
- ar2-fix's scanners re-run (read only): the theorem IRs and pins (17 files): largest bound 29 (acctint 1000-CALC), no hits;
  with the plants, hits only in the plants (prem30 U30, f4probe1 WALK; pfind Z0 and C30); the producer's population with the
  plant (413 files): Z0 / C30 hits only in pfind.fe.json, output equal to findings_B/pop_plant.out (c87e5223).
- The same scanners on my own population (322 files + plants): Z0 / C30 hits only in the plant; U30 / XDIV 0 outside the
  plants; WALK 20 statements in 6 NIST programs (IF110A 2, IF133A 2, NC120A 4, NC170A 4, NC207A 1, NC250A 7), as stated.
  The census's unsupported count and every program's detail are unchanged from merge 11, so C30 makes no NIST program
  unsupported.
- R3 is stated as an assumption: README.md's list item "the extra decimal place with ROUNDED, an assumption" (IBM: "one more
  decimal place might be carried for accuracy if necessary"), with the model's reading and the open case.

## 8 Probes and identity (scripts/probes_m12.sh, identity_m12.sh; probes.stdout, identity_A.stdout, identity_B.stdout)
- The producer's probes on 0854Z (0854Z ir30test.py --run): pa1, pa2, pa3, pd1 stop-unsup "intermediate result over 30 digits
  inside a function argument, places carried open (inner-dmax)"; po1 stop-unsup "FUNCTION ORD-MAX / ORD-MIN of an argument
  over 30 digits"; each text equals the producer's *_final.txt. Controls on 2106Z: pa1, pa3, pd1, po1 end ok, pa2 stops with
  "FUNCTION MOD of non-integers".
- The 25 nested-REM programs of check/ir30_changed_cases.tsv, looked up in my ir30 runs on 0854Z (fresh front end, cobolrun and
  IBM mirror): all 25 have ar2's verdict (18 ok-g, 3 ok, 4 ok-stop): the model's lines equal the mirror's.
- Front-end identity, own run with the producer's arguments (b = 2106Z front end, a = 0854Z's): 503 programs (NIST 459,
  CardDemo 44), all 503 identical in JSON, stdout, stderr and exit status; the planted control u_c30_add.cob differs (JSON,
  stderr: "ADD (line 12): a composite ...").

## Limits
- Testers, probes and identity ran on the snapshots (their front ends and cobolrun); census, mutants and the TSV rows on my
  tree, whose cobolrun is N3's driver and whose parser.py carries D2 (as in merges 10 and 11).
- The 9 path-recording oleans were compared by source and by the recorded path only; the axiom lines and every run agree.
- The covered-path probe used my ir30 tester runs (the tester's judge: model against IBM mirror), not the producer's
  pc_w12m_v1.py, which is fixed to its scratch tree. The Z0 / C30 and bound scans are ar2-fix's scanners, not
  re-implementations; my population has no IR for NIST programs the front end refuses.
- Compute: 0.783 core-h over 30 guarded runs (guard/*.log).

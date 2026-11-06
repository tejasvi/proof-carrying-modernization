RESULT: CONFIRMED. The C1 attribution run of the NIST census N3 (labelled, exploratory; plan recorded before the run in
prereg/ADDENDUM_C1ATTR_coblean.md b677baab and ADDENDUM_C1ATTR_coblean_tree.md 60553303) reproduces exactly on an
independently rebuilt variant tree, and our own per-test comparison with N3 finds exactly the recorded 55 flips plus the
reported NC251A change, and nothing else.

# C1 attribution run (variant: a size error traps when either SIZE ERROR phrase is present): evidence-owner check
An agent of the evidence-owner session, 2026-10-28T11:13:16Z (date -u). Check dir: this directory; replay dir ~/.claude/jobs/8a4f16ec/tmp/c1var_replay (tree, clc1m).
Read only on the COBOL maintainer session's files (~/coblean_runs/c1var).

## 1. Sealed delivery: PASS
- ~/coblean_runs/c1var/sealed_20261028T110243Z: SHA256SUMS 4b8c115de3bfe74b (as announced), 2424/2424 OK (seal_check.txt);
  sealed tree manifest tree_manifest_c1var.sha256 387a13c03c2669e1 (as recorded before the run).

## 2. Variant tree rebuilt independently: PASS
- scripts/build_c1var_mine.sh: cp -rL of our own N3 replay tree (built from snapshot 20261028T0551Z by
  checks/nist3-20261028T072837Z), 0 links; Resolve.lean 3be4dbc0 before; the recorded patch c1var_resolve.diff (b740d599,
  copy here) with --fuzz=0, -p1: Resolve.lean dd5de241 after; 0 .orig/.rej; lake build cobolrun rc 0 (88 jobs).
- Hashes (hashes.txt): cobolrun 8b0a88db = the producer's (sealed manifest); run_nist.py 6635004c, parser.py 74e35705 and
  CobolRun.lean 05522fe7 = N3's.

## 3. Census re-run (all 309 programs): PASS
- scripts/census_c1_mine.sh: NC SQ IX SM IC IF in order, each after the load/memory gate, frozen run_nist.py with
  COB_SWITCH_1=ON COB_SWITCH_2=OFF, no SYSIN, then abend_status_v2, mechanism_v3, summarize_nist_v2 (11:07:2xZ-11:09:53Z).
- Census text identical to the producer's final_census_c1v.txt (census_compare_raw.txt empty). Per program, 309/309
  outcome, kind, detail, matches and first difference identical to the producer's C1 run after normalising run paths
  (outcomes_mine_vs_producer_c1.txt).
- Totals: pass 245, fail 1, unsupported 62, undefined 0, timeout 0, error 1; per test 5568 of 5570; NC grading PASS 3796,
  FAIL 2 (final_census_mine.txt, census_totals_mine.txt).

## 4. Our own per-test comparison with N3: PASS
- scripts/pertest_mine_v2.py (our parser of the NIST report lines, page headers excluded; it does not read the producer's
  transition tables) on our N3 replay run (cln3m, which reproduced sealed N3) and our C1 run (clc1m): pertest_mine_v2.txt.
- Program outcome changes: 11. Ten programs fail -> pass (NC106A, NC170A, NC171A, NC172A, NC173A, NC175A, NC176A, NC177A,
  NC202A, NC253A) and NC251A undefined (divByZero) -> unsupported (non-numeric DIVIDE remainder). No other program changes.
- Test-entry changes: 91 = 55 FAIL -> PASS in those ten programs (2/7/7/8/8/6/7/7/2/1), equal entry for entry (program,
  paragraph, occurrence) to the recorded expected_flips_55.tsv (flips_vs_expected.diff empty), plus 36 new PASS entries of
  NC251A (DIV-TEST-F5-11 to DIV-TEST-F5-20), each equal to GnuCOBOL's PASS. No other entry changes.
- NC107A unchanged in both runs: fail, 175 matches, first difference at JUST-TEST-04 (the JUSTIFIED defect).
- With our parser's counting, GnuCOBOL entries matched go from 5134 to 5189 of 5191 (+55; the census tool's 5513 -> 5568 of
  5570 counts some entries our parser does not); NC251A's 36 entries are in neither count (it does not run to the end).

## 5. NC251A in plain words
- NIST source extract5/NC/NC251A.CBL, sequence 076500-077600 (file lines 763-774): MOVE ZERO TO 25COUNT, then
  DIVIDE 100 BY 25COUNT GIVING 25ANS REMAINDER 25REM NOT ON SIZE ERROR ... (no ON SIZE ERROR phrase): a division by zero
  with only NOT ON SIZE ERROR. The N3 semantics faults there (undefined, divByZero); the variant treats it as a size error,
  so the program runs on through DIV-TEST-F5-20 (36 more entries, all agreeing with GnuCOBOL) and then stops at
  DIV-TEST-F5-21, a DIVIDE REMAINDER into a non-numeric item, which is outside the modelled subset. (The DIVIDE is at file line
  768, sequence 077000, as the COBOL maintainer session cites.)

## 6. What rests only on the COBOL maintainer session's statements
- The variant's meaning (the trap flag change at the six arithmetic statements) is read from the patch, not proved.
- The run-time-dependent output differences (NC214M ACCEPT TIME; FUNCTION WHEN-COMPILED in IF142A/IF403M front-end JSON)
  and "every other front-end, cobolrun and final-file output is identical" were not compared here (outcomes, details and
  per-test entries were).
- The reading that every remaining N3 fail except NC107A is cause C1 is supported by this run in the sense that the variant
  flips exactly those 55 entries and nothing else; that the variant isolates IBM's rule rather than another change is the
  patch's content as recorded.

## 7. Cost
- guard_totals.txt: 22 guard logs, 0.021 core-h.

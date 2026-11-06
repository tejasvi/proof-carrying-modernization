Verdict: CONFIRMED. All six obligations discharged; every compared output equals the producer's (bytes, or after
run/tree path reduction); the F1 exception changes the resolved IR at exactly CBACT04C 1300-COMPUTE-INTEREST and NC252A
COMP-TEST-32, found two independent ways (own scale scan of the surface IRs; own ME2 mutant with the resolver check).

# merge-11 check (an agent, fork of the evidence-owner session): coblean-20261028T2106Z
Check 2026-10-28T21:10:08Z - 2026-10-28T21:25:47Z (date -u). Directory: /home/user/fv_paper/evidence/checks/merge11-20261028T211008Z; replay dir (own tree, census and tester runs):
/home/user/fv_paper/replay/merge11-20261028T211008Z. Method: the merge-10 check (merge10-20261028T164108Z)
adapted to 1636Z -> 2106Z. Snapshots, the producer's dirs and the earlier replay copies were read only.

## 1 Inputs (scripts/item1_inputs.sh; item1.stdout, manifest_check_snapshot.txt, d0_files_check.txt, src_*.txt, oleans_*)
- Producer manifest manifest_coblean-20261028T2106Z.sha256 (sha 3588a630e5784328, 632 entries), sha256sum -c in the 2106Z
  snapshot: 0 failures. d0_files_SHA256SUMS.txt (sha 2613eefd8eddb459): 52 of 52 OK.
- Source diff 1636Z -> 2106Z (outside .lake): 7 changed, 13 added, 0 removed. Changed: Cobol/Frontend/Resolve.lean (-12 +120),
  Cobol/Frontend/Surface.lean (+4), tools/cobolfe/parser.py (-2 +14) and its pyc, tools/evidence/make_evidence.py (+18),
  README.md, HANDOFF_20261023.md. Added: docs/EVIDENCE_carddemo_live_20261028T2106Z.tsv, tests/DmaxResolve.lean,
  tools/difftest/dmaxtest.py, dmaxtest_mutants.md, dmax_cases/ (9). No file under Examples/ changed or added; under Cobol/
  only the two Frontend files.
- Compiled modules: of 68 .olean files exactly 3 differ from 1636Z: Cobol/Frontend/Load, Resolve, Surface. Cobol.olean
  (be3132ebc333738c) and every Examples olean are byte-identical to 1636Z's.

## 2 Theorem rows (scripts/item2_irs.sh; item2_irs.txt; dmaxresolve.out, dmaxresolve_mypop.out)
- The 9 stored CardDemo IRs equal 1636Z's (and 2306Z's), and the 2106Z front end (copy, 0 links, -I -B) regenerates each byte
  for byte: cbact01c 26ab6e5f, cbact02c 1c4c76c9, cbact03c 0b595702, cbact04c 59d5918d, cbcus01c 60216395, cbtrn01c fe0ffd1e,
  cbtrn02c 20ac4c44, cbtrn03c e04dea09, cbstm03ab 2c5ba72b; CBSTM03B alone 38fa862f (pin 2306Z); CSUTLDTC b38f9a39 (pinM3)
  and COBSWAIT f2ae5593 (pinM7) regenerate equal to their pins.
- tests/DmaxResolve.lean (= 2106Z's), run in my tree on my build: theorem IRs 15 of 15 same; the producer's R1 list (6 IF111A /
  IF114A paragraphs) 6 of 6 same; the producer's population list (407 files) 406 same, 1 different: NC250A IF--TEST-28, the
  level-88 condition with VALUE ALL "BAC", resolved before as a comparison with SPACE and now with ALL [66, 65, 67] (fix G).
  My own population (the two pins and the 320 front-end outputs of my census, 2106Z front end + D2): 322 files, 321 same,
  1 different (the same NC250A paragraph).

## 3 Build, oleans, axioms (scripts/build_m11_mine.sh, build_m11_resume.sh, axioms_m11.sh; build.log, lake_build.txt,
## oleans_mine_vs_snapshot.txt, axioms/)
- Own tree: fresh cp -rL of the merge-10 check's tree (0 links); Resolve.lean and Surface.lean asserted = 1636Z, then copied
  from 2106Z; parser.py asserted = 1636Z + D2, then 2106Z + D2 (--fuzz=0; 9d9b3fb7d8a81aec); tests/DmaxResolve.lean. First
  build attempt stopped at once (rc 126: my guard wrapper was not executable); the resume re-asserted the files and built
  with bash: lake build cobolrun Cobol, 89 jobs, rc 0, one core.
- Load, Resolve, Surface and Cobol oleans equal the snapshot's byte for byte (1acaab83, 56b896da, e8769f5a, be3132eb). 26
  other oleans in my tree differ from the snapshot (Examples/*, Cobol/Logic/Alnum, Summary, CobolRun: carried over from the
  merge-10 tree and not rebuilt; the snapshot's equal 1636Z's, item 1; CobolRun is N3's driver, as in merge 10).
- #print axioms in a fresh process (axioms/AxM11.lean, against the snapshot's build): the 25 TH0 theorems (incl. the two primed
  names): 24 x [propext, Classical.choice, Quot.sound], bincnt_equiv also bincnt_equiv._native.bv_decide.ax_7; the 25 lines
  equal the producer's check_th0_ax_sorted_nopos_w11m.txt and the merge-10 check's lines (both diffs empty). Planted
  controls (AxCtl.lean): sorry -> [sorryAx], declared axiom -> [plantedAx].

## 4 dmaxtest and mutants (scripts/item4_dmax.sh, me1_m11.sh, me2_m11.sh; item4_dmax.stdout, me1_run.stdout, me2_run.stdout)
- dmaxtest.py in the snapshot == the producer's scratch copy (bytes). Parts at seeds 1 and 2 (--n 60 --show 3, --root = 2106Z):
  all88 ok 60 / ok 60; cond ok 9 + ok-g 51 / ok 10 + ok-g 50; edited ok 4 + ok-g 56 / ok 10 + ok-g 50; intfn ok-g 60 / ok-g 60;
  div ok 3 + ok-g 57 / ok 2 + ok-g 58.
- Controls (--root = 1636Z, --show 2), non-passing: all88 60 + 60, cond 50 + 52, edited 60 + 60, intfn 60 + 60, div 58 + 54 =
  120 / 102 / 120 / 120 / 112, as the producer states.
- All 20 runs: results.jsonl, coverage.json, details.jsonl byte-equal to the producer's d_* runs (60 files); per-case statuses
  equal. Hand rows dmax.hand (6 programs) and dmax.gdep (3) equal the producer's texts after path reduction. No file in either
  snapshot is newer than the run's start marker.
- ME1 (own run of the producer's ME1 text in my tree): dmaxtest div s1 mirror 45, ok-g 12, ok 3 = the producer's tally, per-case
  statuses equal; hand cases: v_div1 mismatch (the g_* departure cases differ always), the other v_* ok. ME2 (own edit, the
  exception line replaced by e'): see 6. After each mutant Resolve.lean restored (= 2106Z), rebuilt, and the Load, Resolve,
  Surface and Cobol oleans equal the snapshot's again.

## 5 NIST (scripts/census_m11_mine.sh; clm11m_*, final_census_mine.txt, census_producer_vs_mine.diff, census_m10_vs_mine.diff,
## per_program_m10_vs_m11.txt)
- All 309 programs re-run with the N3 commands on my tree (2106Z + D2, COB_SWITCH_1=ON, COB_SWITCH_2=OFF; frozen run_nist.py;
  abend_status_v2, mechanism_v3, summarize_nist_v2).
- Census: pass 247, fail 10, unsupported 50, undefined 1, timeout 0, error 1; per test 5781 of 5836. Normalized census equals
  the producer's nist/final_census_w11m.txt (diff empty).
- Against the merge-10 check's census and runs: only NC250A changes, fail (114 of 115) -> pass (115 of 115); the per-program
  results.json outcomes of all 309 programs differ only there.

## 6 The F1 exception (scripts/f1scan.py; f1scan_theorems.tsv, f1scan_nist.tsv; me2.diff, me2_dmaxresolve.out)
- Condition (Resolve.lean l.634-641 at 2106Z): a COMPUTE whose surface expression is one division with no extractor scale,
  no ROUNDED receiver, every receiver a numeric item (no reference modification) with at most min(old, sc) places,
  old = max(divisor scale, dmax), sc = max(decPlaces(dividend) - decPlaces(divisor), dmax); it changes the IR only if old != sc.
- Own scan (f1scan.py: own re-implementation of dScales, decPlaces, refScale and Expr.scale over the surface JSON): the 15
  theorem IRs and the two pins hold 3 single-division COMPUTEs: CBACT04C 1300-COMPUTE-INTEREST takes the exception (dmax 2,
  old 2, sc 4: changes); acctint and acctint.gnucobol 1000-CALC are ROUNDED (not taken); the pins have none. The 320
  front-end outputs of my census (299 programs; the others stop in the front end) hold 7: NC252A COMP-TEST-6, -13, -18 take it
  with old = sc (no change), NC252A COMP-TEST-32 takes it with dmax 0, old 2, sc 0 (changes), 3 are not taken.
- Own mutant ME2, built in my tree, then tests/DmaxResolve.lean against the pre-merge-11 resolver: theorem IRs 14 of 15 same
  (cbact04c DIFFERENT in 1300-COMPUTE-INTEREST); my population 320 same, 2 different: NC250A IF--TEST-28 (fix G) and NC252A
  COMP-TEST-32. The producer's ME2 resolver check (w3merge11/dr_mut_ME2.out) shows the same paragraphs.
- So the exception changes the resolved IR at exactly CBACT04C 1300-COMPUTE-INTEREST and NC252A COMP-TEST-32; it also applies,
  without effect, to NC252A COMP-TEST-6, -13 and -18.

## Limits
- The Examples oleans were not rebuilt (unchanged since 1636Z; the axiom check loads the snapshot's build).
- Item 6's population is my census's front-end outputs: NIST programs that the front end refuses have no IR and were not
  scanned; CardDemo programs other than the theorem IRs and the two pins were not scanned.
- f1scan.py re-implements the scale rules for the shapes that occur (no MANUAL case arose); ME2 confirms its result.
- My tree's cobolrun is N3's driver (as in merge 10): NIST and ME1's tester ran on it, the other tester runs on the snapshots'.
- Compute: 0.137 core-h over 26 guarded runs (guard_coreh.txt).

## Addendum (2026-10-28T22:54:31Z by date -u): the merge-11 evidence TSV (tsv/TSV.md)
PASS. 300 rows against 1636Z's 288: 284 identical, 4 changed (T5 1193 -> 1248, T7 7403 -> 7413, S2 README section sha
2b06806d -> ce52b585, E4 7643 -> 7698), 12 new (V.dmax: ten tester rows, hand, gdep), 0 missing, no claim text changed, no CV
row changed: the producer's account. Read-only runs on both snapshots give the old and new values (T5 and E4 +55 from
Resolve.lean +54 and Surface.lean +1; T7 +10 from parser.py; S2: two README items, R1/F7 and R2). Re-run of the 16 rows with
the 2106Z make_evidence.py on my tree: 15 match in claim, value, source, command and expected; T7 gives 7412 there because
my parser.py carries the D2 diff (one line less), and the command on the snapshot gives 7413.

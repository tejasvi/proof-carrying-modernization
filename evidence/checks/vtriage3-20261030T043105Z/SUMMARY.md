RESULT: AGREE with the producer's triage (rog, vpin_triage_rows_final.txt 6fb1ec93, seal 47ef513c OK) on all 8 rows, 0 verdict disagreements: 34 missed UB (ISO C; GNU C defines it), 130 false alarm, 195 real UB at the first UB op, 184 real UB at the first UB op (printf :20 before the shift :22), 158 and 162 real ISO UB at the stop op, printed as "UB: type-punned access (byte-level access not modelled)" and filed UNSUPPORTED (GNU C defines both), 142 false alarm (labelled gap), 1 false alarm (unlabelled). Notes: 130 static 6.9p5 point, 158/162 label nuance, 195 main's form; erratum to our next2 check: 184's first UB is :20, not :22.

# Check by an agent: independent triage of 8 rows of sample V at cirlean next3 (7c73739)
Dir: ~/fv_paper/evidence/checks/vtriage3-20261030T043105Z (stamp from date -u in the mkdir). Every script, compile, run
and multi-file read ran as one pjobs_v3 job under coreh_guard_v2 (jobs/cmd*.txt, jobs/pjobs*.log, guard/*.log).
Spend: 7.7 core-s = 0.0021 core-h over jobs 1-6 (out/cores_sum.txt, last metered value of each guard log); budget 0.3.

## Inputs (read only; sha256 in out/input_hashes.txt)
- Delivery ~/cirlean_work/llvmsub/runV_next3: results.tsv 40b904ec, results.jsonl f4962e77, SHA256SUMS f562ea17, the 8
  rows' main.cir and outputs (copied to cir/ and out/delivery/, cmp-checked, out/copy_hashes.txt). Sources: the runner's
  checkout ~/cirlean_work/llvmsub/dl/cir2c/test/sources/llvm-test-suite (as in our next2 check), copied to src/.
- Addendum ADDENDUM_V_rerun_next3.md 231bc40a; our delivery check Vnext3-20261030T034258Z/SUMMARY.md 2a185f3f; next2
  triage check vtriage-20261028T190635Z (SUMMARY 2782bb22, rows.tsv 5e070041).
- Frozen next3 tree: cirrun 2995b794 (hash checked before the re-runs), CHANGES_next3.md d1e7e695, CirRun.lean,
  CIR/Semantics/Eval.lean, CIR/Semantics/Basic.lean, CIR/Frontend/Varargs.lean (read, not rebuilt).
- Producer: ~/cirlean_work/scratch/soundaudit_n3/out/vpin_triage_SHA256SUMS 47ef513c; its entry for
  vpin_triage_rows_final.txt (6fb1ec93) equals the file. Its n3vt*.c reproductions were not read or run.

## Method and order
1. Read the 8 sources in full and followed main (argc = 1, empty stdin) to the first operation C11 leaves undefined;
   own verdicts written to own_verdicts_pre_triage.txt (sha256 161e5f17...) before reading the producer's triage, the
   next2 triage or our check of it. Already read then: results.tsv kinds and the addendum (inputs to part b).
2. Located the code behind each cirrun message in the frozen tree (job 2, out/msg_grep.txt) and read it.
3. Re-ran the frozen cirrun on our copies of the 8 main.cir with the runner's environment, plain and with CIR_TRACE
   (job 4, out/cirrun/): 8/8 outputs equal the delivery's main.out byte for byte; row 184's loop heads are argc = 0,
   1, 2, then the UB.
4. Native runs (job 3, out/native/, out/native_vs_ref.tsv): gcc 15.2.0 and the runner's pinned clang 24 (4955d32b;
   no system clang; its objects linked against gcc's libubsan), -O0 -std=gnu17 -fsanitize=undefined, each run in an
   empty dir under timeout, </dev/null; plus a warnings-only pass. All 18 runs exit 0; stdout + exit line equals the
   reference except row 1 (the reference comes from real 9/31-bit types). Row 34 also with -fstrict-flex-arrays=3.
5. Then read the producer's triage and compared row by row (rows.tsv, last column).

## Rows (details, clauses and code lines in rows.tsv)
- 34 20080222-1: ISO UB at :29, p->data[4] on data[1] (6.5.2.1p2, 6.5.6p8, J.2). GNU C defines it (trailing [1] array
  as flexible member); UBSan silent by default, "index 4 out of bounds for type unsigned char [1]" at :29 with
  -fstrict-flex-arrays=3 (gcc and clang). cirrun MATCH 0: missed UB in ISO C. Mechanism as the producer says: member
  placement over the char array (Eval.lean placeMember :52-59) and get_element's bound taken from the array in memory
  (6), not the static type (:1026-1033).
- 130 stdarg-4: no UB at any operation; f2 > f2i > f1i forwards the list down a chain, as 7.16p3 allows. cirrun's
  va_list rule keeps one advancing frame (Eval.lean vaArgOp :825-856) and fails f1i's first va_arg (:25, reached from
  f2i :45, main :133): false alarm.
- 195 2006-12-11-LoadConstants: ISO and GNU UB at :178, long for %x (7.21.6.1p9). cirrun's literal-format check fails
  before the first printf call: real UB at the first UB op.
- 184 2003-05-31-LongShifts: ISO UB at :20 in the third iteration, long long -4 for %llx (7.21.6.1p9 with 7.16.1.1p2's
  representable-value latitude), before -4 << 4 at :22 (6.5.7p4; defined in GNU C, still diagnosed by UBSan at 22:46).
  cirrun's fitsCheck stops at :20: real UB at the first UB op (by p9's letter alone the first iteration's :20 call
  is already UB, so the report would be a later UB).
- 158 mayalias-1 (:31 b[1] = 0) and 162 mayalias-2 (:22 p->x = 1): ISO UB, an int object stored through a short
  lvalue (6.5p7). GNU C defines both (may_alias; 158 is the GCC manual's example); the CIR carries no may_alias.
  cirrun prints "UB: type-punned access (byte-level access not modelled)" at that store (Basic.lean punnedAccess
  :218-231); the runner files it UNSUPPORTED.
- 142 pr87053: defined in ISO and GNU C (strlen of the const union's other member reads "1234567\0", 7). cirrun
  UB-STUCK at the decay of u.z: false alarm, the labelled const-union gap (CHANGES_next3.md:157-158).
- 1 union2: defined (bitwidth ignored; union {s16, s32, s32}; every read reinterprets the 4 bytes *ptr stored, -1).
  cirrun's get_member for the read u->i at :53 writes an activation of i (Eval.lean unionMember :1010-1023), so main's
  read of uu.i9 at :64 meets 2 indeterminate bytes: false alarm, not labelled (CHANGES_next3.md:57 says reads do not
  write).

## Disagreements and notes
- Verdicts: none. On every row the producer's rule, operation and classification match ours.
- 130, addition (not a disagreement): f1i and f2i are inline definitions with no external definition in the program
  (CIR linkage available_externally), used in calls, so ISO C 6.9p5's "shall" is not met and the whole program is
  undefined by 4p2, at no operation; always_inline makes this moot in GNU C. It does not make the reported va_arg a
  real UB. The producer does not mention it.
- 158/162, label: my pre-triage label was "correct not-modelled stop" (the runner's UNSUPPORTED filing), the
  producer's is "REAL UB" (cirrun's printed "UB:"). Both hold for ISO C at the same store; under GNU C only the
  not-modelled reading holds. Same verdict, operation and clause.
- 195, note: main(int, const char *[]) is not one of 5.1.2.2.1p1's two forms (an implementation-defined form GCC and
  Clang accept without a diagnostic); not an operation, verdict unchanged.
- Mechanism of 34: my working guess while reading the sources (next3's character-arithmetic rule) was wrong; the CIR
  uses cir.get_element, and the producer's account (placement plus in-memory bound) is the one the code shows. The
  pre-triage file states no mechanism for 34.
- Erratum to our next2 check (vtriage-20261028T190635Z/rows.tsv, row 184, "6.5.7p4: -4 << 4 (:22, Vals[2]); earlier
  rows defined"): the printf at :20 of the same iteration is UB first (7.21.6.1p9, 7.16.1.1p2). The verdict "real UB"
  stands; the site there, and next2's cirrun report (the shift), are a later UB. The next2 producer gave :22 too; the
  producer's next3 entry says so ("next2 had no format check, so it stopped at the shift").
- Counts, for the lead: with the labels of our Vnext3 check (10 real, 3 false among next3's 15 UB rows, plus 130 and
  195 untriaged there), next3's 15 UB rows split 11 real (adding 195) and 4 false alarms (1, 139, 142, 130). The 2
  UNSUPPORTED rows 158 and 162 hold a real ISO UB at the stop; 34 (MATCH) is a missed ISO UB that GNU C defines.

## Files
own_verdicts_pre_triage.txt, rows.tsv, PROGRESS.md, src/ (8 sources + references), cir/ (8 main.cir), out/ (delivery
copies, cirrun re-runs, native runs, msg_grep, hashes, sums), jobs/ (scripts and command files), guard/, bin/ (native
binaries). SHA256SUMS: every file here except SHA256SUMS itself and the sums job's guard/sha_sums.log and
jobs/pjobs8.log (written while it ran).
Written 2026-10-30T04:56:46Z (awk strftime, UTC) by an agent.

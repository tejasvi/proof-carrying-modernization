RESULT: AGREE on all 26 rows (13 real UB, 13 false alarms, as the producer says); 0 disagreements. Four verdicts depend on the dialect: 158 and 162 are undefined only in ISO C11 (GNU __may_alias__ defines them), 157 and 139 are defined only in GNU C (ISO makes them constraint violations); under a uniform GNU C reading the split would be 11 real / 15 false.

# An agent (fork of the evidence-owner session): independent check of the C maintainer session's triage of the 26 UB rows of runV_next2 (cirlean 424e821)
Written 2026-10-28T19:11:53Z by date -u. Dir: checks/vtriage-20261028T190635Z.

## Inputs (read only)
- Producer: ~/cirlean_work/scratch/vtriage_next2, SHA256SUMS sha256 3d300612...86a6c6 (as announced); sha256sum -c 123/123 OK
  (work/sumcheck.txt); vtriage_next2.tsv 69bf80fd..., counts.tsv e552c347... (as announced).
- Run: ~/cirlean_work/llvmsub/runV_next2/results.tsv sha 813c52b6... (= our check Vnext2-20261027T201054Z); its 26 rows
  with cir_kind UB (all NATIVE_OK) are exactly the 26 triaged orders and ids (work/runV_next2_ub_rows.tsv, empty diff
  work/ids.diff).
- Sources: ~/cirlean_work/llvmsub/dl/cir2c/test/sources/llvm-test-suite/... as named in the run (work/sources.tsv); the
  paper's LLVM paragraph sec-stack.tex l.203-240.

## Method
Every source read in full; the executed path from main followed by hand to the first operation that C11 leaves
undefined, or to the end; verdict with clause per row (rows.tsv, sha8 5e070041). For the 7 shift/overflow rows (25, 48, 51,
111, 143, 179, 184), our own native builds with gcc -O0 -fsanitize=undefined (scripts/ubsan.sh; work/ubsan/;
ubsan_results.tsv, sha8 f1e0b205): the first runtime error is at the producer's line in each (shiftdi-2.c:34, shr.c:66,
crc32.be.c:24, 20040409-3w.c:30, pr56051.c:34, bswap-2.c:71, 2003-05-31-LongShifts.c:22).

## Results
- Real UB (13): 15 (6.3.2.1p2), 25, 48, 51, 143, 184 (6.5.7p3/p4), 111 (6.5p5), 34, 36 (6.5.6p8, J.2), 127 (6.5.6p9),
  179 (6.5.7p4 at :71), 158, 162 (6.5p7, ISO only).
- False alarms (13): 102, 131, 196 (6.9.1p12, value unused); 1, 123, 142, 144, 160 (union reinterpretation, 6.5.2.3p3
  fn 95); 52 (char pointer over an int's bytes, 6.3.2.3p7); 80 (int-to-pointer implementation-defined, == defined);
  173 (va_arg types match); 157, 139 (GNU C; ISO constraint violations).
- Reported site or reason differs from the real UB: 34 (struct view vs subscript), 127 (stops at alloca(0), false at
  that site), 179 (stops at the defined union bit-field read :50); also 158, where cirlean's reason is out-of-bounds
  pointer arithmetic (the stride rule) and the ISO reason is 6.5p7 at the same expression (the producer lists it as the
  same construct).
- Not checked here: the producer's patched-probe runs (t1d, t102p, ...) and its attributions of each false alarm to a
  next3 branch ("yes"/"likely"/"partial").

Erratum (2026-10-29T08:59:55Z by date -u, d0): line 7 quotes the producer's SHA256SUMS hash with a wrong tail ('...86a6c6'). The file's sha256, computed now, is 3d30061213a151ddd96c8b741e26a0ec681871bf564e09a3f300be0dc7c8be3f, the same value announced on 10-28 and used in the brief; the 123/123 check result stands.

Erratum 2 (2026-10-30T04:59:45Z by date -u, d0): row 184 (UnitTests 2003-05-31-LongShifts). The first operation with undefined
behaviour in ISO C is the printf at :20 (Test's first statement passes the long long -4 for %llx in the third
iteration, C11 7.21.6.1p9, outside 7.16.1.1p2's latitude; by p9's letter alone already the first iteration's call), not
the shift -4 << 4 at :22 (6.5.7p4), which follows it. The verdict "real UB" stands. cirlean next2 stopped at the shift,
so 184 joins 34, 127 and 179 as a row where the reported site differs from the first UB (at a UB operation, not a
defined one); UBSan reports the shift because it does not check printf argument types. Source: the independent check
checks/vtriage3-20261030T043105Z (SUMMARY.md 26ec1e3d), which agrees with the producer's next3 triage. rows.tsv row 184
is left as written; this erratum supersedes its clause.

Erratum 3 (2026-10-30T05:52:33Z by date -u, d0; from audit v57): erratum 2 wrongly lists 34 among the rows whose reported site
differs from the first UB. In 34 cirlean next2 stops at the first UB operation itself, the subscript p->data[4] (:29),
with another reason ("element access into a non-array"), as rows.tsv says; 158 is of the same kind. The rows where
next2 stops at another operation than the first with undefined behaviour are 127 and 179 (both at defined operations)
and 184 (at the later shift).

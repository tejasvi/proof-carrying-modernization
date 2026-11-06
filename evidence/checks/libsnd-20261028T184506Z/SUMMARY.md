# d0 reproduction of reported library-model gaps of cirlean (stamp 20261028T184506Z, written 2026-10-28T18:46:19Z by date -u)

Inputs: gap descriptions of ~/cirlean_work/scratch/soundaudit/FINDINGS.md (sha16 4742f16c9e67cd52; the C maintainer session/cjlemmas, 130 runs
at 424e821); own cases probe/d0l_cases.c (sha8 f41a92a5; 7 gap cases, 3 controls, k = 1) and probe/d0l_const2.c; native
gcc -O0; CIR from the toolchain clang; cirrun of the 10 frozen builds (266d1ed ... 424e821). Results probe_results.tsv
(sha8 c062b303) and probe_const2.out (sha8 0c7568a2).

RESULT: CONFIRMED for every sampled gap kind (C leaves the behaviour undefined; the model gives the native value):
- memcpy, memset, memcmp with a null pointer and size 0: defined at all 10 builds.
- store to a const-qualified local through a cast (run-time initialiser): the store is visible (2) at all 10 builds.
  (With a constant initialiser the read is folded by the front end and returns 1: not a test of the gap.)
- sprintf with the destination as its own format string, sprintf %d with a long argument, va_arg after va_end:
  defined (native values 349, 5, 12) from 90b9c2f on; 266d1ed and 28e2380 have no sprintf model and stop at the
  variadic call (block argument count) for the va cases.
- Controls (memcpy, sprintf %d-%ld, va_arg sum) match native wherever the models exist.
Not sampled: fprintf with a null stream, the %.Ns overlap, va_start/va_copy twice, VLA sizes, atomic orders, M1, M2.

## Addendum (2026-10-28T18:57:14Z by date -u): cirlean 88e6008, d9ae8e5, ec40522
scripts/probe_extra.sh ran the same cases on the replay-copy interpreters (probe_results_extra.tsv, sha8 5bf67890): mem* with
null and size 0, the const-local store (run-time initialiser: 2), sprintf with its own buffer as format, %d with a long
argument and va_arg after va_end are all defined there too; controls match. Over the 13 versions: mem* null/0 and the
const-local store at all 13; the sprintf and va gaps at all but 266d1ed and 28e2380, which have no sprintf model and stop
at the variadic call.

## Addendum 2 (2026-10-28T19:10:13Z by date -u): va_arg of another type
probe/d0l_vatype.c, scripts/probe_vatype.sh, probe_vatype.out (sha8 4d443ece): va_arg(ap, long) for an int argument (C:
undefined) gives the defined value 5 at 11 of the 13 versions, like the int control; 266d1ed and 28e2380 stop at the
variadic call (block argument count) for both.

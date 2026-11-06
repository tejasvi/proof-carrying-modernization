# Pre-registration V: cirlean's C/C++ semantics on a random sample of the LLVM test-suite programs

Version 1. Written and frozen by the paper's evidence owner on 2026-10-25, before any corpus program is run. The user
asked for this through the coordination session (the coordinating session, 2026-10-25 ~16:00Z, passed on by cirlean, the C maintainer session). cirlean's
description of the inputs (V/PREREG_V_inputs_cirlean.md, sha256 b2beb490...) is part of this file where it is cited.
The files listed in SHA256SUMS_V_v1 belong to it. The sample is drawn by the frozen rule below and recorded in
`V/ADDENDUM_V_sample.md` before the first run. Later changes go to DEVIATIONS.md, which is append-only; this file is
never edited.

## Population and frame

- Corpus: the LLVM test-suite programs vendored in ftsrg/cir2c at eb2a332d0ea03ba144756314f2e405f82475d593.
- Population: the sources that cir2c's test/run_tests.sh runs with RUN_LLVM=1, i.e. every .c or .cpp file under
  test/sources/llvm-test-suite with a .reference_output file: 1,812 programs (1,690 C, 122 C++), listed in V/list.tsv
  (sha256 9ec70e5b0cca6d67c10fcfaf18f48062c5a64df1cfbbdf376de9bc86401b33d6).
- Frame (rule fixed before the draw, V/build_frame_v.py): the population without the programs that cannot build or run
  natively on x86-64 by construction: UnitTests/Vector/{LASX, LSX, Altivec, NEON, HVX} (414 programs, other instruction
  sets) and Benchmarks/Polybench (30, which need polybench.c outside their translation unit). Frame: 1,368 programs.

## Sample

- 200 programs: the frame's ids sorted by sha256("fv-paper-prereg-V-2026-10-25|llvm|<id>") ascending (M/draw_m.py with
  --seed fv-paper-prereg-V-2026-10-25 and bridge llvm), the first 200. The sorted order is the processing order, so
  every prefix is a random sample of the frame.

## Procedure per program (cirlean's section 4, as fixed here)

- Pins: cirrun of cirlean ffab71e (binary sha256 01e5df808f0751e47512fd261843ed4929722b76c7a9dd83dea299e633453ad0);
  clang upstream-4955d32b (clang-24 sha256 8aef898b32480d1f10eb2e055fa125dcc334a5d088f41befbc08584e0a5fc491); libc++
  headers of cir2c eb2a332; the C standard is clang's default (gnu17; C++17); includes as run_tests.sh computes them.
- ClangIR from the source (20 s); cirrun on main (120 s), stdin /dev/null. A program whose main takes (int, char**) runs
  through a harness that calls main(1, {"prog", NULL}), as a native run without arguments (the references were made
  that way).
- Native cross-check: clang -O0 -w, the same includes, -lm; run with stdin /dev/null (10 s); its status S.
- Reference: E, the exit status in the reference's last line, read with run_tests.sh's awk.
- One core per job (taskset, cores 120-123), nice 10, address-space cap for cirrun, no core dumps, LC_ALL=C, every job
  under the core-hour guard; at most 2 programs at a time.

## What is compared, and the oracle's limit

cirrun does not model the output of printf, puts and putchar, so stdout is not compared. Only two things are: main's
value modulo 256 against E, and the absence of undefined behaviour or a stuck state where the native run is fine.
abort, assertion failures and std::terminate count as status 134, a trap as 132. The paper states this limit next to
every number from V.

## Outcomes per program

- native_kind: NATIVE_OK (S = E), REF_DIFF (built and ran, S differs from E), NATIVE_FAIL (build or run failed or
  timed out).
- cir_kind, first match wins, by cirlean's table (section 4 of the inputs) and its UB-message classes
  (tools/ub_classes_ffab71e.tsv, sha256 87a351f4..., 150 message forms): UNSUPPORTED (front end error, CIR parse error,
  a model limit or an external without a model; the sub-reason named), TIMEOUT, CRASH, EXIT (the pin models exit() as
  "UB: exit() called", so the status is unknown: its own kind), EXC (an uncaught C++ exception), MATCH, MISMATCH, UB
  (class UB-C or UB-STUCK, recorded).
- Secondary triage, which does not change cir_kind: every UB, MISMATCH or EXC result is re-run natively with
  -fsanitize=undefined,address; a sanitizer report marks real UB in the program.

## Analysis

- Primary: among the NATIVE_OK programs, the shares of MATCH, MISMATCH, UB, EXC, EXIT, UNSUPPORTED, TIMEOUT and CRASH
  with Wilson 95% intervals; and the MATCH rate among the programs that reached a verdict (MATCH, MISMATCH, UB, EXC).
- Every MISMATCH and every UB on a NATIVE_OK program is listed with its sanitizer result: a UB that no sanitizer reports
  is either real UB the sanitizers miss or a false report of the semantics, and is read by hand with the clause cited.
- The REF_DIFF and NATIVE_FAIL programs are counted and left out of the primary shares.

## Budget and stop rule

Compute only, no model call; at most 15 core-hours. Processing stops at Tue 2026-10-27 03:00Z; the programs not
attempted are reported. Crash fixes only, each recorded, with the affected programs re-run.

## Known before the run (disclosure)

- cirlean read the corpus as text to make the population list and smoke-tested its pipeline on its own difftest
  programs, not on corpus programs. The README's "2,600 programs" counts every source; 830 sources have no reference
  and are not in the population.
- At the pin, exit() is modelled as undefined behaviour (184 translation units call it), and printf output is not
  modelled; both limits are known and stated above.

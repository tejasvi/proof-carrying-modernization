# PREREG_V inputs, cirlean side: LLVM SingleSource subset against native

For d0 (evidence owner), before PREREG_V is frozen and the sample is drawn.
Prepared 2026-10-25 17:30-17:50 UTC. Prep only: **no cirrun, cirscan, CIR
generation, native build or run touched any corpus program.** The corpus was
read as text. The only programs compiled and run are drivers around two of our
own tests/difftest programs (section 6).

## 1. Corpus

- Repository: https://github.com/ftsrg/cir2c
- Commit: `eb2a332d0ea03ba144756314f2e405f82475d593`, committed 2026-09-22T14:19:32+02:00, subject "modified note".
  This is the same commit as the cir2c binary release whose libc++ headers our pipeline already uses
  (`~/cirlean_work/dl_cir2c_eb2a332`).
- Fetch: `git clone --depth 1 --filter=blob:none --sparse`, then `git sparse-checkout set test`.
  Cone mode gives the top-level files plus `test/`: 4589 files, 35 MB.
- Local copy: `~/cirlean_work/llvmsub/dl/cir2c`. Treated as untrusted: nothing from it was executed.
  The scripts `run_tests.sh`, `run-cir2c.sh` and `generate-reference-outputs.py` were read as text.

## 2. Population (as `test/run_tests.sh` with `RUN_LLVM=1`)

### Rule

Taken from `run_tests.sh`, lines 825-834 and 491-504:

- `LLVM_EVAL_DIR=test/sources/llvm-test-suite/`.
- Enumerate with `find "$LLVM_EVAL_DIR" \( -name "*.cpp" -o -name "*.c" \) | sort`.
- Keep `f` only when `${f%.ext}.reference_output` exists as a file.
- Language: `.cpp` is C++, anything else is C (`--lang c`).
- `test_id` is the path relative to `LLVM_EVAL_DIR`, without the extension, with `/` replaced by `__`.

### Count

**1812 programs: 1690 C and 122 C++.** The README's "2600 programs" counts every source, not the population:

- The corpus has 2642 sources (2519 `.c`, 123 `.cpp`).
- 830 sources have no `.reference_output`, so the runner drops them in its pre-filter.
  They never enter `TOTAL_TESTS`. By directory:
  - Regression/C: 823
    - gcc-c-torture/execute: 654
    - …/builtins: 108 (multi-file tests)
    - …/ieee: 33
    - …/builtins/lib: 28
  - UnitTests/Vector: 3
  - Benchmarks/Polybench: 2 (`polybench.c` and the template)
  - UnitTests/Vectorizer: 1
  - UnitTests/SetjmpLongjmp: 1
- 28 `.reference_output` files have no C/C++ source: 26 ObjC/ObjC++ tests (their `.m`/`.mm` files are not
  vendored), `Vectorizer/index-select` and `black-copied-in-cxxobj`.
- `generate-reference-outputs.py` could add references for some of the 830 with the system gcc.
  It was not run, because it executes corpus programs and writes into the corpus.

### Composition by directory

| Directory | Programs |
|---|---|
| Regression/C | 922 (gcc-c-torture/execute 885) |
| UnitTests/Vector | 498 |
| UnitTests/Integer | 59 |
| Regression/C++ | 31 |
| Benchmarks/Polybench | 30 |
| Benchmarks/Misc | 28 |
| Benchmarks/Shootout-C++ | 25 |
| UnitTests/HashRecognize | 14 |
| Benchmarks/Shootout | 14 |
| Benchmarks/Stanford | 11 |
| Smaller directories | the rest |

The 498 UnitTests/Vector programs break down as:

| Subdirectory | Programs |
|---|---|
| LoongArch LASX | 197 |
| LoongArch LSX | 192 |
| AVX512* | 72 |
| Altivec | 23 |
| Generic | 8 |
| SSE | 4 |
| NEON | 1 |
| HVX | 1 |

At least 414 of them (LASX, LSX, Altivec, NEON, HVX) target other ISAs. Expect frontend and native-build
failures for these on x86-64. Their references come from upstream.

### stdin, arguments and RUN_OPTIONS

The runner gives none of them:

- `run_llvm_test` runs `"$binary_file" > out 2>/dev/null` under GNU parallel, with no arguments.
  There is no stdin redirect, so the job inherits whatever stdin parallel passes; this was not verified,
  because parallel is not installed here.
- The checkout has no CMakeLists or Makefiles: only `.c`, `.cpp`, `.h` and `.reference_output` files.
  So the test-suite's RUN_OPTIONS and STDIN_FILENAME are not available.

The references come from two sources that the checkout does not distinguish:

- Upstream llvm-test-suite files, produced by the test suite's own runs.
- `generate-reference-outputs.py`: built with `gcc`/`g++ -lm -w`, run with no arguments and inherited stdin,
  10 s limit. Each file holds the program's stdout followed by `exit N`.

The expected exit E is read from the reference's last line, with the runner's awk:
`END{ if (match($0, /exit [0-9]+$/)) print substr($0, RSTART+5, RLENGTH-5)+0; else print 0 }`.

### `list.tsv`

- Path: `~/cirlean_work/llvmsub/list.tsv`
- sha256 `9ec70e5b0cca6d67c10fcfaf18f48062c5a64df1cfbbdf376de9bc86401b33d6`
- 1812 rows, no header, sorted by bytes (`LC_ALL=C sort -c` passes). Columns:

| Column | Meaning |
|---|---|
| `id` | the runner's `test_id` |
| `path` | relative to the checkout |
| `lang` | `c` or `c++` |
| `stdin?` | 1 when the translation unit's own files name `stdin`/`STDIN_FILENO` or call `scanf`, `getchar`, `gets`, `getline`, `getdelim` or `read(0, …)` (C++ also `std::cin`, `cin >>`, `cin.`); 8 rows |
| `args?` | 1 when a definition of `main` has parameters (243 rows); 0 for `main()`/`main(void)` (1569 rows); no row lacks a definition |

Both flags are static text tests:

- Comments are removed and string/character literals blanked first.
- The translation unit's own files are the source plus the quoted includes it reaches, searched as the
  runner's `-I` list (see section 5).

Tool: `tools/enumerate_v2.py` (sha256 `1262d5d5bc7e91eeb0b4d2c61dffa504b83683678f23aab23edef9ccc66c2705`). Statistics are in `list_stats.txt`
(sha256 `1cc148624512aa7fdb783fd07c60f96c5f9ef8a6175ce6bcf38ad96c52cf34e0`). v1 is superseded: it counted a C array named `cin` as stdin, and it missed
mains with nested parentheses or defined in an included file.

Extra static counts, not in the list (`list_static_calls.tsv`, sha256 `fb08738e6bed21dd1695d0484f1d11a9ff3fe2c6888a443313177aa26ca5da03`):

- 184 translation units call `exit(`.
- 603 call `abort(`.
- 1167 call neither.

## 3. What cirrun can observe, and caveats

Source: `CirRun.lean` at ffab71e. Binary `~/cirlean_frozen/ffab71e_20261025/.lake/build/bin/cirrun`,
sha256 `01e5df808f0751e47512fd261843ed4929722b76c7a9dd83dea299e633453ad0`.

### Invocation and output

- `cirrun FILE.cir FUNCTION ARGS…` runs one function and prints one line, then exits with rc 0.
  The line is one of:
  - the integer result
  - `void`
  - `exception <typeinfo>`
  - `UB: <reason>`
  - `diverges`
  - `abnormal exit`
- rc 2 on usage errors:
  - `no function F in FILE`
  - a wrong argument count: `cirrun: <demangled> takes N arguments`. C's `main` has an empty demangled name,
    so the line reads `cirrun:  takes 2 arguments`.
- A `.cir` file that does not parse raises `CIR parse error`, uncaught. I expect rc 1, but this was not observed.
- printf, puts and putchar are modelled for their return values only and produce no output.
  **stdout is not compared.**

### The comparison

1. Exit status: main's value v is compared as `v mod 256` (0-255) with E. The smoke had 325, which native
   reported as 69.
2. No UB or stuck state where native is fine.

### Caveats

**`main(int, char**)`: 243 of 1812 programs (13.4%).**

- cirrun cannot pass a `char **` argument, so `cirrun P.cir main` fails with rc 2.
- A harness works in C and in C++ (smoke cases d3w and d5w). It is a wrapper translation unit containing
  `#include "<source>"` plus:
  ```c
  int cirrun_main0(void) { static char a0[] = "prog"; char *av[2] = { a0, 0 }; return main(1, av); }
  ```
  It is run with `cirrun W.cir cirrun_main0` and gives argc = 1 and argv = {"prog", NULL}, like a native run
  without arguments.
- For d0 to fix: UNSUPPORTED "main needs args" as in the brief, with or without the harness as a
  pre-registered second arm, or the harness as primary.

**`exit(n)`.** The pin models exit as `UB: exit() called` (`CIR/Std/Models.lean:847`). Reaching exit is
visible, but n is lost. 184 translation units call `exit(` (static count). Proposed: its own kind, EXIT,
which is neither MATCH nor UB.

**abort, assert, terminate, trap.**

- `UB: abort() called`, `UB: assertion failure` and `UB: std::terminate called` count as status 134
  (SIGABRT as the shell reports it).
- `UB: trap` counts as status 132 (SIGILL; `__builtin_trap` is `ud2` on x86-64).
- These are compared with E like a returned value. 603 translation units call `abort(`, mostly on
  gcc-c-torture failure paths.

**Model limits reported as `UB:`.** All 150 UB message forms of the pin are in
`tools/ub_classes_ffab71e.tsv` (sha256 `87a351f434770a00f419c0a46fd31beeddb748f4ce4332adf12ad68c9c9c6dd4`). That is 144 literal strings
(`tools/ub_messages_ffab71e.tsv`) plus 6 interpolated ones. Rules, first match wins:

| Class | Rule |
|---|---|
| EXIT | `exit() called` |
| ABORT134 | `abort() called`, `assertion failure`, `std::terminate called` |
| TRAP132 | `trap` |
| UNSUPPORTED (38) | contains `unsupported`, `not modelled`, `outside the modelled subset`, `without a model`, `unknown function`, `unknown vtable` or `is not modelled`; also covers `call to an external function without a model: f` (rand, srand, time, getchar, scanf, fopen, …) and `unsupported operation <op>` (unknown CIR ops) |
| UB-STUCK (40) | IR-shape or value-typing failures, a fixed list (e.g. `branch to a missing block`, `expected an integer`, `ill-typed store`, `result count mismatch`) |
| UB-C (67) | the rest (e.g. `division by zero`, `integer overflow`, `array index out of bounds`, `invalid memory read`, `read of an indeterminate or ill-typed value`) |

Unknown messages fall into UB-C.

**Polybench (30 programs).** They need `polybench.c`, which is not in the translation unit. Expect native
link failures, and cirrun stopping on an external without a model.

**C++ libraries.** CIR is built against libc++ headers (cir2c release eb2a332); native builds use the
system libstdc++, as in run_pun.sh. Library internals differ; exit statuses should not.

## 4. Pipeline per program (proposal)

### Setup

**Tool variables.**

| Variable | Value |
|---|---|
| `TC` | `~/cirlean_work/toolchain/upstream-4955d32b/bin`: clang 24.0.0git 4955d32b80f8, `clang-24` sha256 `8aef898b32480d1f10eb2e055fa125dcc334a5d088f41befbc08584e0a5fc491`, matching its SHA256SUMS |
| `CX` | `~/cirlean_work/dl_cir2c_eb2a332/cir2c-eb2a332/libcxx/include/c++/v1` |
| `CIRRUN` | the pinned binary above |
| `INC` | `-I` for each directory of the runner's `compute_includes`, in order: the source's directory, its ancestors up to `test/sources/llvm-test-suite`, and `Benchmarks/Polybench/utilities` for Polybench sources |

**Standard.** No `-std` flag, so clang's defaults apply: gnu17 (`__STDC_VERSION__` 201710L) and
C++17 (201703L). cir2c's own runner uses `-std=c23`/`c++23`, which rejects K&R C and other GNU
extensions. Name the choice in PREREG_V.

**Environment.**
- One core: `taskset -c N`, N in 120-123.
- nice 10.
- `ulimit -c 0`: smoke d7 dumped a core.
- `ulimit -v 16777216` for cirrun; checked working in the smoke.
- `</dev/null` as stdin.
- `LC_ALL=C`.
- Everything under `coreh_guard_v2`.

### Steps

1. **CIR.**
   ```
   # C
   timeout -k 5 20 $TC/clang -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering $INC SRC -o P.cir
   # C++
   timeout -k 5 20 $TC/clang++ -nostdinc++ -isystem $CX -fclangir -emit-cir -Xclang -fno-clangir-call-conv-lowering $INC SRC -o P.cir
   ```
2. **cirrun.**
   ```
   timeout -k 5 120 $CIRRUN P.cir main </dev/null >P.out 2>P.err
   ```
   For the harness arm (args? = 1): build `W.c`/`W.cpp` as in section 3 and run `cirrun W.cir cirrun_main0`.
3. **Native cross-check.**
   ```
   timeout -k 5 20 $TC/clang -O0 -w $INC SRC -o P.native -lm      # clang++ for C++
   timeout -k 5 10 ./P.native </dev/null >/dev/null 2>&1          # status S
   ```
   S is 0-255, 128+signal, or 124 on timeout.
4. **E** from the reference, with the runner's awk (section 2).

### Two independent columns per program

So the analysis can be cut either way.

**native_kind**

| Kind | Condition |
|---|---|
| NATIVE_OK | S = E |
| REF_DIFF | built and ran, S ≠ E |
| NATIVE_FAIL | the build failed or timed out, or the run timed out |

**cir_kind** (first match wins)

| Kind | Condition |
|---|---|
| UNSUPPORTED | the CIR build exits non-zero (frontend error; the sub-reason is its first `error:` or NYI line); cirrun rc 1 with `CIR parse error`; rc 2 `takes N arguments` (main needs args); rc 2 `no function`; `UB:` in class UNSUPPORTED; `void` |
| TIMEOUT | the CIR build or cirrun hits its limit (124/137), or `diverges` |
| CRASH | any other cirrun rc (e.g. a Lean panic, a stack overflow, out of memory), empty output, or `abnormal exit` |
| EXIT | `UB: exit() called` |
| EXC | `exception <typeinfo>` (native: terminate, SIGABRT) |
| MATCH | integer v with `v mod 256 = E`; or ABORT134/TRAP132 with 134/132 = E |
| MISMATCH | integer v with `v mod 256 ≠ E`; or ABORT134/TRAP132 with the status ≠ E |
| UB | `UB:` in class UB-C or UB-STUCK (sub-class recorded) |

The stdin? and args? columns of `list.tsv` go into the results file as covariates.

### Secondary triage (proposal)

For each UB, MISMATCH or EXC result: native build with `-O0 -fsanitize=undefined,address` and the same run.
A sanitizer report means the program has real UB. This does not change cir_kind.

### Limits and cost

Limits: CIR build 20 s, native build 20 s, native run 10 s, cirrun 120 s.

Worst case for 200 programs: 200 × 170 s = 34,000 s = 9.4 core-h. The brief's figure counts the CIR build
and cirrun only: 200 × 140 s = 7.8 core-h. The harness arm adds about 0.9 core-h (13% × 200 × 120 s).

Smoke timings on our small drivers:
- CIR build: 0.11-0.21 s.
- cirrun: 0.10-0.50 s, 56-62 MB RSS.

Real corpus programs will be larger; the limits allow for that.

## 5. Open choices for the evidence-owner session

1. **Sampling frame.** Options:
   - all 1812;
   - all 1812, stratified by top-level directory;
   - excluding the 414 non-x86 SIMD tests by a static rule fixed before the draw;
   - native cross-check of all 1812 before the draw. This looks at native outcomes only, not at cirrun.
2. **`main(int, char**)`.** UNSUPPORTED only, or the harness arm.
3. **EXIT.** A separate kind, or reported as "terminated through exit, status unverified".
4. **C standard.** clang default (gnu17), or c23 as cir2c uses.
5. **Primary ratio.** Proposed: among NATIVE_OK programs, the shares of MATCH, MISMATCH, UB, EXC, EXIT,
   UNSUPPORTED, TIMEOUT and CRASH, reported in full. Plus the MATCH rate among programs that reached
   a verdict (MATCH + MISMATCH + UB + EXC).

## 6. Smoke test (own tests/difftest programs only)

Drivers are in `~/cirlean_work/llvmsub/smoke/s1` and `s2`, made by `tools/smoke_v1.sh` (sha256 `b4dae4d1ce45bbc9545f76c5c4dbaf6257f4a58faa2b9a1746c8600235972f42`) and `tools/smoke_v2.sh` (sha256 `0d1a556d30b3111f0dd04edcdbbe7f5906eeb1baf02dff994c6618ccf5997674`). Programs used: `control.cpp`, compiled as C, and `arith.cpp`, compiled as C++. Everything ran on core 120 under the guard.

| Case | What it tests | cirrun | Native exit | Kind |
|---|---|---|---|---|
| d1 | C, `main(void)` returns `t_recursion(10)` | `55` | 55 | MATCH |
| d2 | C++, printf, then returns 325 | `325` (rc 0; printf accepted) | 69 | MATCH under mod 256 |
| d3 | C, `main(int, char**)` | rc 2, `cirrun:  takes 2 arguments` | 4 | UNSUPPORTED |
| d3w | d3 through the C harness | `260` | 4 | MATCH (harness) |
| d4 | C, `exit(t_early_return(50))` | `UB: exit() called` | 8 | EXIT |
| d5 | C++, `main(int, char**)` | rc 2 | 25 | UNSUPPORTED |
| d5w | d5 through the C++ harness | `25` | 25 | MATCH (harness) |
| d6 | C, `srand`/`rand` | `UB: call to an external function without a model: srand` | 2 | UNSUPPORTED |
| d7 | C, `abort()` | `UB: abort() called` | 134 (core dumped) | ABORT134 = 134 |

Prep compute: 8 guarded runs, about 0.003 core-h in total, against a cap of 1 core-h.

Hashes of every prep file (list, statistics, tools, class tables): `~/cirlean_work/llvmsub/SHA256SUMS` (sha256 `0e55cf793ffd522a40484f799e89c92c2fdb8e69f1f0e87d83b877d79217edd7`).

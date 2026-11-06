# Pre-registration D: a random sample of functions from large public code

Version 1. Written and frozen by the paper's evidence owner on 2026-10-24, before any unit of this study was run.
The files listed in SHA256SUMS_v1 are part of this pre-registration. Changes after freezing go to a separate,
dated DEVIATIONS file; this file is never edited.

## Question

On functions drawn at random from real public code, how often does the verification stack (veriforch over the four
semantics) prove, refute, or fail to handle a function, and at what cost?

## Populations (fixed)

| language | population | version | unit | size | how enumerated |
|---|---|---|---|---|---|
| C | zlib | tag v1.3.1, commit 51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf (archive sha256 in D/downloads.sha256) | function definition | 152 | `tools/enum_c_functions.py` with clang (llvm-project 4955d32b), `-std=c11 -DHAVE_UNISTD_H -DHAVE_STDARG_H -D_LARGEFILE64_SOURCE=1 -DHAVE_HIDDEN`, over the 15 library files of zlib's `Makefile.in` (OBJZ + OBJG) |
| C++ | tinyxml2 | tag 10.0.0, commit 321ea883b7190d4e85cae5512a12e5eaa8f8731f | function, method, constructor or destructor definition (a template once) | 395 | same tool, `-std=c++17`, over `tinyxml2.cpp` and `tinyxml2.h` |
| Java | Apache commons-lang3 | 3.14.0 jar (sha256 in D/lang3_jar.sha256) | method with a body; not synthetic, not bridge, not `<clinit>` | 3,901 | `tools/enum_jar_methods.py` on the jar's class files |
| TypeScript | es-toolkit | v1.52.0 (commit 32f4c8f) | function, method, arrow function, constructor or accessor in `src/` | 794 | the rows of StrictTS's public-coverage tool at a15926a (`out/es-toolkit.strict.json`, sha256 in D/estoolkit_rows.sha256) |
| COBOL | AWS CardDemo | commit 59cc6c2fd7ebd7ef7925cad552a01a4b8b6e4d5e | program (every `.cbl`/`.CBL` file tracked by git) | 44 | `git ls-files` (census) |

Population files: `D/pop_<name>.tsv`. A unit's identity is the key in the first column.

## Sample (fixed)

- Seed string `fv-paper-prereg-D-2026-10-24`. `tools/draw_sample.py` seeds Python's `random.Random` with the first
  64 bits of SHA-256("<seed>/<name>") and draws N = 100 units without replacement from the sorted keys of each
  population (zlib, tinyxml2, lang3, estoolkit). CardDemo is a census: all 44 programs, shuffled.
- The drawn files `D/sample_<name>.tsv` are frozen with this document. Their order is the processing order.

## Procedure

1. Tool versions (veriforch, cirlean, JimpleLean, coblean, StrictTS, equiv-lean, Lean) are pinned when the run starts
   and recorded in the run log. No re-pin during the run.
   - Only crash fixes are allowed: a translator exception, a Lean error that is not a verdict, or an internal tactic
     error. Each fix goes on a branch cut from the pinned commit, is recorded (hash, one-line diff summary, units
     affected), and the affected units are re-run.
2. Each sampled unit is processed in sample order by veriforch's standard pipeline for its language. Front end and
   extraction run on the whole library (or program), so callees are available. Bottom-up contracts for callees are
   allowed, and their cost counts toward the sampled unit.
3. Budget per sampled unit, callees included:
   - model spend <= $0.80;
   - <= 3 proof attempts per obligation;
   - Lean check timeout 600 s per module;
   - wall time <= 30 min.
4. Total budget for D <= $500, compute included. If the budget runs out, processing stops in every language at the
   current position. Unattempted units are reported as such and left out of the denominators. The attempted prefix of
   a random order is still a uniform random sample.

## Outcomes (one per unit, decided mechanically from veriforch's records)

- **proved**: status `proved`, trust `kernel` (standard axioms only, kernel replay of the unit's module passing).
  Reported in two parts:
  - **mechanical**: the statement was fixed without the model (bridge template, test unit, type-quantified entry
    point);
  - **model-stated**: the contract was chosen by the model. Unreviewed.
- **refuted**: a concrete input in the unit's mechanical input domain on which the executable semantics reaches an
  error outcome (undefined behaviour, panic, undeclared exception, abend), confirmed by running the semantics. Each
  input is listed. Afterwards, and labelled as post hoc, each refutation is classified as a defect or an undocumented
  precondition.
- **blocked**: the unit is out of scope because of a named gap: a front-end failure, a construct the semantics does not
  model, or a missing library model. The gap name is the bridge's recorded reason.
- **timeout**: in scope, but no proof and no refutation within the budget (statuses `stuck`, `timeout`, `budget`).
- Reported separately, and not counted as proved:
  - `conditional`: relies on unproved callee contracts;
  - `partial`: assumes more than the calling convention guarantees;
  - proofs whose trust is `native`;
  - infrastructure errors (`error`, `llm_error`, `build_failed`), which count in the denominator.

## Analysis (fixed)

- Per language: counts and proportions of proved (with its mechanical and model-stated parts), refuted, blocked,
  timeout and the separately reported categories, each with a Wilson 95% interval. No finite-population correction
  (conservative), although zlib's sample is 100 of 152.
- CardDemo is a census, so only counts are reported.
- Cost per unit (model $ and core-seconds): median, interquartile range, mean and total per language.
- Gap names with their frequencies, per language.
- No pooling across languages in the headline numbers. A pooled line may be added, labelled as such.
- Nothing is excluded after the fact. Every sampled unit appears in the report with its outcome.

## Known before freezing (disclosure)

The evidence owner has seen earlier coverage numbers of the same codebases at other versions:
- StrictTS coverage of es-toolkit: 234/794 in the strict subset;
- JimpleLean's parse of commons-lang3: 0 failures;
- the CardDemo front-end results: 11/12 batch programs extracted, 8 resolved.

No unit of this sample has been verified for this study.

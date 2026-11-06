# Pre-registration D: a random sample of functions from large public code

Version 2. Frozen by the paper's evidence owner on 2026-10-24, before any run of D. It replaces version 1
(PREREG_D_v1.md, sha256 e4c8923e…5a68). The changes fix executability only, as found by veriforch's feasibility check
(~/veriforch/notes/prereg_feasibility.md, §2 R2, R6-R10). Populations, samples, the seed, the processing order and the
outcome definitions are unchanged. They are frozen in SHA256SUMS_v1 (sha256 803550aa…afee). Later changes go to
DEVIATIONS.md, which is append-only.

## Changes from version 1

- **R2:** the kernel replay command is named.
- **R6:** a status-mapping table from veriforch's records to the outcomes. veriforch has no unit-level error status,
  so the infrastructure-error category is defined from the records.
- **R7:** the per-unit command:
  - front end and extraction run once per library;
  - per unit, `vo verify --only` over the unit and its callee closure, with the counterexample step and the replay;
  - callees proved for an earlier unit are reused.
- **R8:** "3 attempts" means 3 model proposals. Free candidates (cached proof, template) are not counted.
- **R9:** the Lean timeout is 600 s per proof module and 900 s per generated module.
- **R10:** veriforch is pinned as a frozen copy with a SHA256 manifest.

## Question

On functions drawn at random from real public code, how often does the verification stack (veriforch over the four
semantics) prove, refute, or fail to handle a function, and at what cost?

## Populations and samples (unchanged from v1)

| language | population | unit | size | sample |
|---|---|---|---|---|
| C | zlib v1.3.1 (51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf) | function definition | 152 | 100 |
| C++ | tinyxml2 10.0.0 (321ea883b7190d4e85cae5512a12e5eaa8f8731f) | function/method/constructor/destructor definition | 395 | 100 |
| Java | commons-lang3 3.14.0 jar | method with a body (not synthetic/bridge/`<clinit>`) | 3,901 | 100 |
| TypeScript | es-toolkit v1.52.0 (32f4c8f) | function in `src/` (StrictTS coverage rows at a15926a) | 794 | 100 |
| COBOL | AWS CardDemo (59cc6c2fd7ebd7ef7925cad552a01a4b8b6e4d5e) | program | 44 | census |

- Enumeration tools, population files `D/pop_<name>.tsv`, seed `fv-paper-prereg-D-2026-10-24`, drawing tool and
  samples `D/sample_<name>.tsv`: as in v1.
- The sample order is the processing order.

## Tool pins

- Recorded when the run starts:
  - cirlean (at least 88e6008) with the matching equiv-lean;
  - JimpleLean snapshot 20261024T0553Z or later, in a mode that reads the pinned jar;
  - StrictTS (b1155cc suggested by its owner), on a checkout of es-toolkit's `src/` at 32f4c8f;
  - coblean snapshot 20261024T0803Z for both the front end and Lean;
  - Lean v4.35.0, clang upstream-4955d32b, Soot 4.7.1, JDK 17;
  - veriforch as a frozen copy with a SHA256 manifest.
- No re-pin during the run. Only crash fixes are allowed, each recorded, and the affected units are re-run.

## Procedure

1. Front end and extraction run once per library (or program) before the first unit, and their cost is reported per
   library.
2. Per unit u, in sample order:
   1. `timeout 1800 vo verify <target> --only <u and every callee in its call-graph closure> --attempts 3
      --check-timeout 600 --budget 0.80`, with generated modules at their fixed 900 s timeout;
   2. if u ends `stuck` and the bridge has an executable semantics (C/C++, COBOL), the counterexample step for u
      within the remaining budget;
   3. the kernel replay of every claimed theorem with `lake env leanchecker <module>` (Lean v4.35.0) in the package
      that built it.

   A callee proved for an earlier unit is reused at no cost, and its cost stays with that unit.
3. "3 attempts" means 3 model proposals. The bridge's free candidates (cached proof, template) are tried first and
   are not counted.
4. Total budget for D <= $500, compute included. If it runs out, processing stops at the current position in every
   language. Unattempted units are reported and left out of the denominators.

## Outcomes (definitions unchanged; mapping from veriforch's records fixed here)

| outcome | veriforch record |
|---|---|
| proved, mechanical | status `proved`, trust `kernel`, replay passes, `statement_origin = mechanical` |
| proved, model-stated | status `proved`, trust `kernel`, replay passes, any other `statement_origin` (unreviewed) |
| native (reported apart) | status `proved`, trust `native` |
| conditional (reported apart) | status `conditional`. By default veriforch assumes the last contract of a stuck callee and the intended contract of a gap callee. |
| partial (reported apart) | status `partial` |
| refuted | `findings/<unit>.json` whose counterexample replays to undefined behaviour or an abend on the semantics. Verdicts `real_bug` and `missing_precondition` give the post-hoc split into defect and undocumented precondition. |
| blocked | status `gap` (gap name = the unit's scope string); or the library/program failed in the front end or extraction (gap name = the tool's error class); or the front end did not emit the unit |
| timeout | status `stuck` or `budget`; or status `blocked` (a callee left without a contract by budget or time); or killed at the 30-min wall |
| infrastructure error (in the denominator, reported apart) | `stuck` where every model attempt failed with an LLM error and no Lean check ran; or a tool crash, before its crash fix and re-run |

## Analysis (unchanged)

- Per language: counts and proportions of every outcome, each with a Wilson 95% interval. There is no
  finite-population correction.
- CardDemo is a census, so it gets counts only.
- Cost per unit (model $ and core-seconds): median, interquartile range, mean and total.
- Gap names with their frequencies.
- No pooling across languages in the headline numbers.
- Nothing is excluded after the fact.
- Observations recorded before the run. These are zero by construction, not results:
  - "proved, mechanical" for C, C++ and COBOL library functions, which have no mechanical statement;
  - "refuted" for Java and TypeScript, whose bridges have no counterexample step.

## Known before the run (disclosure; details in DEVIATIONS.md)

veriforch's feasibility pass, before any proof run, measured front-end scope on the samples:
- zlib: 77 in scope, 23 gap;
- tinyxml2: 53 in scope, 38 gap, 9 not emitted;
- commons-lang3: 39 in scope, 34 gap, 25 gap through a callee, 2 not found;
- es-toolkit: 29 in the subset, 71 blocked;
- CardDemo: 11 of 44 extracted, 9 elaborate.

The feasibility pass also found four tool defects, listed in DEVIATIONS.md. They may be fixed before the pin; no
coverage extension aimed at the sample's gaps is allowed. The run re-measures all of this, and the paper reports the
run.

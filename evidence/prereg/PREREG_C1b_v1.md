# Pre-registration C1b: a declared second pass of the security-fix verdicts with newer automation

Version 1. Written and frozen by the paper's evidence owner on 2026-10-25, before any C1b run. The files listed in
SHA256SUMS_C1b_v1 are part of this pre-registration. Later changes go to DEVIATIONS.md, which is append-only; this
file is never edited.

C1 (PREREG_C_v2) stays the primary pre-registered result and is reported as run ("pass 1"). C1b is "pass 2": the same
units, procedure and outcome definitions, run with tools that gained new automation after C1. Both passes are
reported.

## Question

With cirlean's newer support (lists, strings, %g formatting, translation-unit linking) and equiv-lean's automatic loop
coupling, how many of C1's unknown and blocked commits get a kernel-checked verdict or a confirmed behaviour change?

## Units (frozen)

The 54 C1 commits whose pass-1 outcome was `unknown` (47) or `blocked: build` (7), from the evidence owner's
recomputation of C1's final records (checks/voC-20261024T1438Z/c1_final_outcomes_20261024T1757Z.tsv):
- cJSON: 44 unknown, 7 blocked: build;
- tiny-regex-c: 3 unknown.

List: `C1b/units_c1b.tsv` (order, library, commit, pass-1 outcome, pass-1 per-function verdicts), processed in C1's
order (`C/order_c1.tsv`). The 9 commits with a behaviour change shown in pass 1 are not re-run. Their pass-1 results
stand, including the unknown verdicts of their other functions (order 2 re_compile, order 7 cJSON_SetValuestring).

## Tool pins

- Recorded when the C1b run starts, after cirlean's cJSON work is pinned:
  - cirlean at a commit that has lists, strings, %g and TU linking;
  - equiv-lean at a commit that has automatic loop coupling;
  - Lean v4.35.0, the pinned clang;
  - veriforch as a frozen copy with a SHA256 manifest.
- The changes since C1's pins are listed (commit logs) and reported.
- No re-pin during the run. Crash fixes only, each recorded, and the affected units are re-run.

## The build fix for the 7 blocked commits (one recorded change)

In pass 1, the 7 commits failed to build under `-std=c89` with the pinned clang -fclangir:
- orders 12, 14, 27 and 46: implicit int-to-pointer conversions, an error in the pinned clang;
- orders 48, 53 and 55: FP_ZERO undeclared.

C1b may change the build of the cjson library target once, as one recorded change applied to all 7 commits:
- build flags and predefined macros only (for example, the pinned clang's flag that turns the int-conversion error
  back into a warning, or a feature macro that exposes FP_ZERO);
- no edits to any cJSON source file;
- it is recorded with its diff before the run, together with the reason each flag is needed.

The same flags are used for both the parent and the commit. A commit that still does not build stays
`blocked: build`, with the error.

## Procedure (as C1)

- For each unit c with parent p:
  `vo ci <lib>_lib --base <sha of p> --head <sha of c> --attempts 0 --budget B --check-timeout 600`, with
  B = $0.50 × the number of changed functions.
- The verdict obligations are stated and attempted without the model. The model only proposes distinguishing inputs
  for functions with pointer parameters, 2 proposals per function.
- Total model spend for C1b at most $350 (veriforch's usage logs). If it runs out, the remaining units are reported
  as unattempted.
- Kernel replay of every claimed verdict theorem: axioms printed, and `lake env leanchecker <module>` (Lean v4.35.0)
  in the package that built it.

## Outcomes (unchanged definitions)

- Per changed function:
  - `equivalent`;
  - `changed_only_where_old_unsafe` (kernel-checked EquivOn, Bad = the inputs on which the old version is unsafe);
  - `behaviour_changed` (a distinguishing input confirmed on the semantics);
  - `unknown`, with the reason.
- Per commit: certified conservative, certified equivalent, behaviour change shown, partly certified, unknown,
  blocked: build (definitions of PREREG_C_v2).

## Analysis

- Per unit: pass-1 and pass-2 outcome, per-function verdicts in both passes, and the reason for every remaining
  unknown.
- A transition table, pass 1 to pass 2, per library and in total.
- Every new `behaviour_changed` witness listed. Each witness is checked by the evidence owner for whether it needs an
  input the library's callers never pass (as for C1 order 34).
- Every new kernel verdict listed with its theorem name.
- Counts only, no intervals: C1 is a census of the selected commits.
- Cost per unit and total (model $, core-seconds).
- Nothing is excluded after the fact.

## Known before the run

- C1's complete results (63/63, checked by the evidence owner), including the unknown reasons:
  - no distinguishing input after the proof failed: 34;
  - heartbeat timeout: 19;
  - rewrite failed: 3;
  - maximum recursion depth: 2.
- The 7 blocked builds and their errors.

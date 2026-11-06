# Pre-registration C: verdicts on security fixes, and proof reuse along the same histories

Version 2. Frozen by the paper's evidence owner on 2026-10-24, before any run of C. It replaces version 1
(PREREG_C_v1.md, sha256 a3eec766…c627). The changes fix executability only, as found by veriforch's feasibility check
(~/veriforch/notes/prereg_feasibility.md, §2 R1-R5, R10). Repositories, the selection rule, the selected commits, the
processing order, the C2 sequences and the outcome definitions are unchanged. They are frozen in SHA256SUMS_v1
(sha256 803550aa…afee). Later changes go to DEVIATIONS.md, which is append-only.

## Changes from version 1

- **R1, C1 command:**
  - library-only targets in place of veriforch's test-program targets, which do not exist at most selected revisions
    and lack cJSON_Utils.c;
  - `--attempts 0`, because the verdict obligations are attempted without the model and v1's "3 attempts" had no
    counterpart;
  - a per-commit budget of $0.50 × the number of changed functions, because veriforch's budget is per run.
- **R2:** the kernel replay command is named.
- **R3:** the C2 baseline and step commands are named, and C2 runs with `--no-equiv` (the old ≡ new verdicts belong
  to C1).
- **R4:** the C2 record mapping is fixed, with one guard log per run.
- **R5:** jsmn uses its default build.
- **R10:** veriforch, which is not under git, is pinned as a frozen copy with a SHA256 manifest.

## Questions

- **C1.** For every security-relevant fix commit in cJSON, tiny-regex-c and jsmn, what does veriforch's per-change
  verdict say about each changed function? Verdicts are kernel-checked where they are theorems.
- **C2.** Along the same histories, how much proof work carries over from one commit to the next?

## Repositories, selection rule, selected commits (unchanged from v1)

| library | repository | pinned head | library source files | build flags (head) |
|---|---|---|---|---|
| cJSON | github.com/DaveGamble/cJSON | 6d9f2443ab071f86e5d9b43025a40929ec41c46c | cJSON.c, cJSON.h, cJSON_Utils.c, cJSON_Utils.h | `-std=c89 -DCJSON_API_VISIBILITY -DCJSON_EXPORT_SYMBOLS -fvisibility=hidden` |
| tiny-regex-c | github.com/kokke/tiny-regex-c | f2632c6d9ed25272987471cdb8b70395c2460bdb | re.c, re.h | `-std=c99 -I.` |
| jsmn | github.com/zserge/jsmn | 25647e692c7906b96ffd2b05ca54c097948e879c | jsmn.h | none (default build) |

The selection rule (R1 CVE links, R2 security expression, E1 library file touched, E2 patch-id dedupe) and its output
are as in v1:
- 63 fix commits: cJSON 58, tiny-regex-c 5, jsmn 0;
- `C/select_<lib>.tsv` and `C/selected_all.tsv`;
- processing order `C/order_c1.tsv`;
- C2 sequences `C/c2_seq_<lib>.txt` (50, 33, 30).

## Tool pins

- Recorded when the run starts: cirlean (at least 88e6008, which has `--link`) with the matching equiv-lean, Lean
  v4.35.0, clang upstream-4955d32b, and veriforch as a frozen copy with a SHA256 manifest.
- No re-pin during the run. Only crash fixes are allowed, each a new copy or branch with a recorded diff, followed by a
  re-run of the affected units.

## C1 procedure

1. For each selected commit c with parent p, in the order of `C/order_c1.tsv`, run
   `vo ci <lib>_lib --base <sha of p> --head <sha of c> --attempts 0 --budget B --check-timeout 600`.
   - `<lib>_lib` compiles the library source files of the table alone, linked when there are several, with the flags
     of the table.
   - B = $0.50 × the number of changed functions.
   - The verdict obligations are stated and attempted without the model. The model only proposes distinguishing
     inputs for functions with pointer parameters, 2 proposals per function.
2. If p or c does not build with these flags, the commit's outcome is **blocked: build**, with the error.
3. C1 total <= $350, compute included. If the budget runs out, the remaining commits are reported as unattempted.

## C1 outcomes (unchanged definitions)

Per changed function:
- `equivalent`: a kernel-checked `Equiv` over the mechanical input domain;
- `changed_only_where_old_unsafe`: a kernel-checked `EquivOn`, where `Bad` is the set of inputs on which the old version
  is unsafe;
- `behaviour_changed`: a distinguishing input, confirmed by running both versions on the semantics;
- `unknown`: with the recorded reason.

Per commit:
- **certified conservative**: every changed function is `equivalent` or `changed_only_where_old_unsafe`, at least one
  the latter;
- **certified equivalent**: all `equivalent`;
- **behaviour change shown**: at least one `behaviour_changed`;
- **partly certified**: some kernel verdicts and some `unknown`;
- **unknown**: no kernel verdict;
- **blocked: build**.

For every claimed verdict theorem, the axioms are printed and the module is replayed with `lake env leanchecker
<module>` (Lean v4.35.0) in the package that built it.

## C2 procedure and outcomes

1. Baseline: `vo ci <lib>_lib --base S0 --head S0 --attempts 3 --no-equiv`. It is not counted.
2. Steps: `vo ci <lib>_lib --base S(k-1) --head S(k) --attempts 3 --no-equiv` for each consecutive pair of the frozen
   sequence. Each step uses the caches left by the previous one.
3. Per step, from veriforch's records:
   - changed functions;
   - proofs reused with no Lean run (`cached`);
   - proofs re-checked with the same script (`rechecked`);
   - functions re-proved with a new script (`new:<origin>`, split into without the model (template, reuse, prev) and
     with it (llm));
   - functions that lost a proof (`regression`);
   - model calls and $ (rows of `runs/<t>/llm/usage.jsonl` inside the step);
   - core-seconds, from a guard log dedicated to the run.
4. Budget: C2 total <= $150. Libraries are processed in the order jsmn, tiny-regex-c, cJSON. If the budget runs out,
   the remaining steps are reported as unattempted.

## Analysis (unchanged)

- **C1:** every selected commit is reported with its hash, its first message line, the rules it met, its per-function
  verdicts and its commit-level outcome. Counts are given per library and in total; there are no intervals, since this
  is a census of the selected set. Every `behaviour_changed` witness is listed.
- **C2:** per library, totals plus per-step medians and interquartile ranges, and the share of in-scope proved functions
  whose proofs were reused with no Lean run.
- Observation recorded before the run: 25 of jsmn's 30 C2 commits predate its header-only layout, so those steps will
  report zero functions.
- Nothing is excluded after the fact.

## Known before the run (disclosure; details in DEVIATIONS.md)

Exploratory CI runs by veriforch, in a configuration different from C1, gave verdicts on five selected commits:
- 349ef187 (tiny-regex-c `re_compile`): unknown;
- f28a468e (cJSON_DetachItemViaPointer): unknown;
- b2890c8d (cJSON_SetNumberHelper): unknown, before the v1 freeze;
- a78d9755 (cJSON_DetachItemViaPointer): unknown, before the v1 freeze;
- 5cc0e39f (print_array, print_object): `behaviour_changed`, after the v1 freeze.

The feasibility pass measured which commits build: 51 of 58 cJSON commits on cirlean 88e6008 (7 fail under
`-std=c89` with the pinned clang), and 5 of 5 tiny-regex-c commits. The run re-measures this.

# Pre-registration C: verdicts on security fixes, and proof reuse along the same histories

Version 1. Written and frozen by the paper's evidence owner on 2026-10-24, before any verdict of this study was
produced. The files listed in SHA256SUMS_v1 are part of this pre-registration. Changes after freezing go to a separate,
dated DEVIATIONS file; this file is never edited.

## Questions

- **C1.** For every security-relevant fix commit in cJSON, tiny-regex-c and jsmn, what does veriforch's per-change
  verdict say about each changed function? Verdicts are kernel-checked where they are theorems.
- **C2.** Along the same histories, how much proof work carries over from one commit to the next?

## Repositories (fixed)

| library | repository | pinned head | library source files |
|---|---|---|---|
| cJSON | github.com/DaveGamble/cJSON | 6d9f2443ab071f86e5d9b43025a40929ec41c46c | cJSON.c, cJSON.h, cJSON_Utils.c, cJSON_Utils.h |
| tiny-regex-c | github.com/kokke/tiny-regex-c | f2632c6d9ed25272987471cdb8b70395c2460bdb | re.c, re.h |
| jsmn | github.com/zserge/jsmn | 25647e692c7906b96ffd2b05ca54c097948e879c | jsmn.h |

## Selection rule (fixed; applied by `tools/select_security_commits.py`; outputs frozen as `C/select_<lib>.tsv`)

Unit: a non-merge commit reachable from the pinned head. Its change is the diff against its parent. Its text is its
message plus the message of the merge that brought it in, when that merge brought in at most 5 commits.

A unit is selected if both of the following hold:
1. It meets at least one rule:
   - **R1**: an NVD CVE record that references the repository links it, by a commit URL, by an issue or pull number its
     text references, or by a compare range (in which case it must also match R2). The NVD responses, fetched on
     2026-10-24, are frozen in `C/osv/nvd_*.json`.
   - **R2**: its text matches the security regular expression in the script, case-insensitively: overflow/over-read,
     out of bounds, use after free, double or invalid free, NULL dereference or NULL check, segfault/crash,
     sanitizer/fuzz, undefined behaviour, invalid read/write, uninitialised, leak, denial of service, infinite loop or
     hang, recursion or stack depth, CVE/GHSA, security, vulnerability.
2. **E1**: its change touches a library source file.

**E2**: among selected units with the same `git patch-id`, only the oldest is kept.

Result:
- cJSON: 58 of 955 non-merge commits selected;
- tiny-regex-c: 5 of 127;
- jsmn: 0 of 131. Its two matches change no library file, and its 2026 CVEs are unfixed at the pinned head.

Total: 63 fix commits, listed with the rules they met in the frozen files.

## C1 procedure

1. Tool versions are pinned when the run starts and recorded. Only crash fixes are allowed during the run, on a branch
   cut from the pin, each recorded and followed by a re-run of the affected units (same rule as pre-registration D).
2. For each selected commit c, run `vo ci <target> --base c^ --head c` with the library's veriforch target.
   - If c^ or c does not build in the target's configuration, the commit's outcome is **blocked: build**, with the
     error.
   - Commits are processed in a random order fixed by the seed `fv-paper-prereg-C-2026-10-24`
     (`tools/draw_sample.py`, census mode, over `C/selected_all.tsv`). The order is frozen as `C/order_c1.tsv`.
3. Budget per changed function: model spend <= $0.50 and <= 3 proof attempts per obligation. C1 total <= $350,
   compute included. If the budget runs out, the remaining commits are reported as unattempted.

## C1 outcomes (decided mechanically from veriforch's CI records)

Per changed function, veriforch gives one of four verdicts:
- `equivalent`: a kernel-checked `Equiv` over the mechanical input domain;
- `changed_only_where_old_unsafe`: a kernel-checked `EquivOn`, where `Bad` is the set of inputs on which the old version
  is unsafe;
- `behaviour_changed`: a distinguishing input, confirmed by running both versions on the semantics;
- `unknown`: with the recorded reason (gap name, timeout, error).

Per commit, one of six:
- **certified conservative**: every changed function is `equivalent` or `changed_only_where_old_unsafe`, and at least
  one is the latter;
- **certified equivalent**: every changed function is `equivalent`;
- **behaviour change shown**: at least one `behaviour_changed`;
- **partly certified**: some kernel verdicts and some `unknown`;
- **unknown**: no kernel verdict;
- **blocked: build**.

The axioms of every claimed verdict theorem are printed, and its module is replayed in Lean's kernel checker.

## C2 procedure and outcomes

1. For each library, take the sequence S of the most recent 50 commits (all of them if fewer) of
   `git rev-list --first-parent --reverse <head> -- <library files>`. The sequences are frozen as `C/c2_seq_<lib>.txt`:
   50 commits for cJSON, 33 for tiny-regex-c, 30 for jsmn.
2. Prove the library at the first commit of S as a baseline (not counted), then run `vo ci` on each consecutive pair.
   Each step uses the caches left by the previous one.
3. Per step, record:
   - changed functions;
   - proofs reused with no Lean run;
   - proofs re-checked with the same script;
   - functions re-proved with a new script;
   - functions that lost a proof;
   - model calls, model $ and core-seconds.
4. Budget: C2 total <= $150. Libraries are processed in the order jsmn, tiny-regex-c, cJSON. If the budget runs out,
   the remaining steps are reported as unattempted.

## Analysis (fixed)

- **C1:** every selected commit is reported with its hash, its first message line, the rules it met, its per-function
  verdicts and its commit-level outcome. Counts of commit-level outcomes are given per library and in total. Function
  verdicts are counted the same way. This is a census of the selected set, so no intervals are reported. Each
  `behaviour_changed` witness is listed.
- **C2:** per library, the totals and the per-step medians and interquartile ranges of each recorded quantity. Also the
  share of in-scope proved functions whose proofs were reused with no Lean run.
- Nothing is excluded after the fact.

## Known before freezing (disclosure)

- Earlier exploratory CI runs by veriforch touched two commits of the selected set. tiny-regex-c 349ef187
  (`re_compile`) and cJSON f28a468e (`cJSON_DetachItemViaPointer`) were both recorded as `unknown`.
- The NULL-check patterns of R2 were added before freezing. The evidence owner noticed that f28a468e, a NULL-check
  fix, was missed by the first version of the expression. No other verdict on the selected set was known.
- veriforch's records also contain two defects found by the projects' own tests:
  - tiny-regex-c `matchstar` forms `prepoint - 1`;
  - cJSON `cJSON_SetValuestring` compares pointers into different objects.

  These are not fix commits and are not part of C.

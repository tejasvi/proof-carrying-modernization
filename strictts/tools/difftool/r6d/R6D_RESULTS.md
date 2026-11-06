# R6d: es-toolkit's and remeda's frozen pairs re-run with master 25790c3

This is a labelled re-run, not pre-registered. Its inputs and tool were recorded by the paper's evidence
owner before the run, in `~/fv_paper/prereg/ADDENDUM_R6d_inputs.md` (sha256 7c9230e1...). The addendum
also lists the first looks (a)–(c), so the changes below are not blind.

- **Pairs.**
  - es-toolkit: R6's 415 (`r6_testable.txt` 408069f7..., `r6_provable.txt` 79 pairs, f2f81a47...,
    sources checked by `pairs_SHA256SUMS` bf561176...).
  - remeda: R6r's 862 (`r7_testable.txt` fec09171..., `r7_provable.txt` 160 pairs, 14c45704..., sources
    checked by `pairs_SHA256SUMS` 41e73814...).
  - Both pair sources were verified before the run.
- **Tool.** Master 25790c31dbc3f219b1fe8331167240134ecc001c, difftool dist hash 3f0e0ee59cd91535,
  frontend dist 654dcdf41dd337e5. It ran from the detached worktree `~/strictts_ws/r6d`.
  - Regressions at 25790c3: Lean build 159 jobs, corpus 181/0/0, selftest PASS, bench 43/44 + 23/23, 0
    wrong.
  - New against R6c/R6rb's 9e54bdb (the generic-compat merge):
    - a compat wrapper for generic functions;
    - generic versions with different instances, or one non-generic, compared when the wrappers'
      translated signatures agree;
    - a return-type wrapper `__difftool_ret`;
    - a heap split that reuses a known cell;
    - array-size lemmas (tools/difftool/lean/DiffPrelude.lean);
    - the statement `old-no-panic`.
- **Clones.** Private no-checkout clones: es-toolkit 9c0cac2ee6c0f807099723d7b226f3b65e976d5c, remeda
  d02c3bdb5e18cfa53e76f33f4ae525adce515379, under `~/strictts_ws/constarrow/scratch/rescan/`.

## Results

Per-pair tables: `es/r6d_table.tsv` (sha256 b59bcbc885c7d9a466a11e4d0c7c4c7c884fb70ad339c1d6b2e2f381e7b8961b)
and `re/r6d_table.tsv` (5fca6d306d54ea3c50fc34c001b523f5891bd9030ec30e141e2e95388a00dd9b). The tables add
a `statement` column. The `domain` column marks the compat wrapper and the return wrapper; the `inst`
column marks generic instances.

| | es-toolkit R6c | es-toolkit R6d | remeda R6rb | remeda R6d |
|---|---:|---:|---:|---:|
| PROVED (equivalence) | 60 | 64 | 59 | 60 |
| of which all-worlds / allocated-arguments | 57 / 3 | 60 / 4 | 59 / 0 | 60 / 0 |
| OLD-NO-PANIC (not an equivalence) | - | 1 | - | 2 |
| REFUTED, Lean-confirmed | 10 | 10 | 9 | 9 |
| REFUTED, Node only | 76 | 76 | 55 | 55 |
| UNKNOWN | 269 | 264 | 739 | 736 |

PROVED equivalences by commit intent:

| commit intent | es-toolkit R6c | es-toolkit R6d | remeda R6rb | remeda R6d |
|---|---:|---:|---:|---:|
| refactor/perf/style/chore | 14 | 16 | 29 | 29 |
| fix/feat/revert | 33 | 34 | 26 | 26 |
| docs/test/other | 13 | 14 | 4 | 5 |

The old-no-panic results: es-toolkit has 1 in a fix commit; remeda has 1 in a feat commit and 1 in an
"other" commit.

### The changes, pair by pair (`es/compare_r6c.tsv`, `re/compare_r6rb.tsv`)

Every pair not listed has the same verdict as in R6c or R6rb.

es-toolkit, 5 changes, all from UNKNOWN:
- `isArray` (35fbc4ca, docs): PROVED (all-worlds) at T := number on the old parameter types (generic
  compat wrapper). It was UNKNOWN because the translated signatures differ.
- `isArray` (4bb457ad, feat): PROVED (all-worlds) at T := number on the old parameter types. The new
  version is not generic. It was UNKNOWN because the generic instances differ.
- `initial` (9089b3b4, refactor): PROVED (allocated-arguments) with the new heap split and array-size
  lemmas. It was UNKNOWN: allocation differs.
- `stubObject` (b99176b2, style): PROVED (all-worlds) at the new version's return type (`__difftool_ret`
  around the old version; `{}` becomes `any`). It was UNKNOWN because the translated signatures differ.
- `sample` (fa2afcd6, fix): OLD-NO-PANIC, not an equivalence.

remeda, 3 changes, all from UNKNOWN:
- `isDate` (7900d2c2, other): PROVED (all-worlds) at T := number on the old parameter types. The new
  version is not generic.
- `last` (dbeea0a3, other) and `_last` (b08a667d, feat): OLD-NO-PANIC, not equivalences.

### OLD-NO-PANIC

For every argument list and world, the two runs are equal, or the old run panics. Where it panics,
the new version may do anything. This is WEAKER than equality and is never counted as an equivalence.
It is attempted only in the second Lean pass, when no other statement is proved. The exact statement,
for es-toolkit `sample` (pair h019 of its batch, file
`es/evidence/history-20261027T071639Z-1326872__obs_00.lean`):

```lean
theorem equiv_h019u001_np (I : Impl) : ∀ (vs : Vals Old_h019u001.TT [(.arr .num)]) (w : World Old_h019u001.TT),
    JS.exec (callFun I Old_h019u001.program Old_h019u001.«__difftool_retRef» vs) w =
      JS.exec (callFun I New_h019u001.program New_h019u001.«__difftool_instRef» vs) w ∨
    ∃ (s : String) (w' : World Old_h019u001.TT), JS.exec (callFun I Old_h019u001.program Old_h019u001.«__difftool_retRef» vs) w = some (.error (.panic s), w')
```

Here `__difftool_retRef` is the old version wrapped with the new version's return type, and
`__difftool_instRef` is the new version at T := number. The return types (`np_returns.tsv`):

| pair | commit type | old declared return | new declared return | translated |
|---|---|---|---|---|
| es-toolkit `sample` fa2afcd6 | fix | `T` | `T \| undefined` | `.num` → `(.opt .num)` |
| remeda `last` dbeea0a3 | other | none (inferred `T`) | `T \| undefined` | `.num` → `(.opt .num)` |
| remeda `_last` b08a667d | feat | none (inferred `T`) | `T \| undefined` | `.num` → `(.opt .num)` |

In all three, the old version reads `array[i]` at type `T`. StrictTS panics there when the array is
empty, by design, because the types exclude the `undefined` that JavaScript returns. The new version
returns `undefined` at its widened type.

### Refutations

They are unchanged for both libraries:
- `replay_v2/replay.tsv`, `tscheck.tsv` and `refuted_export.tsv` are byte-identical to R6c's and R6rb's;
- es-toolkit has 86/86 node replays and 14 confirmation blocks; remeda has 64/64 and 11;
- the pair-to-block mappings are the same.

## Recheck

`lake env lean --tstack=262144` at 25790c3. The counts include the old-no-panic theorems.

| library | batch files | standard axioms only | no error inside the theorem | run's axiom lines reproduced |
|---|---:|---:|---:|---:|
| es-toolkit | 17 | 65/65 | 65/65 | 122/122 |
| remeda | 21 | 62/62 | 62/62 | 109/109 |

## Post-processing slips (corrected; none touches the run)

1. es-toolkit's post-processing ran while the remeda run was going in the same checkout. Its collection
   of confirmation files took 3 blocks of the remeda run.
   - Redone (`es_fixup.sh`) with a closed window, from es-toolkit's start to remeda's start.
     `collect_confirm.js` gained an optional end stamp.
   - The mixed attempt is kept outside the evidence directory, in
     `~/strictts_ws/r6d/scratch/r6d_attempts/es_confirm_mixed/`.
2. The replay script sits one directory deeper than in R6c, and its relative path to TypeScript failed.
   - It now uses an absolute path. The replay was redone and the table regenerated (`es_fixup.sh`).
   - remeda's post-processing used the fixed scripts from the start.

## Evidence

Directory `~/strictts_ws/r6d/scratch/r6d/` (both libraries, `es/` and `re/`). Manifest
R6D_EVIDENCE_SHA256SUMS: 4,043 files, sha256 f20925085d5fbe36b73a6d98833e93c9fce884e17a1a8ea4e9f5745955856b95.

For each library it holds:
- `chunks/`;
- `evidence/` (batch files, the obs files with the observational and old-no-panic theorems, their run
  and recheck outputs);
- `evidence_confirm/` (es-toolkit confirmations.tsv fe967d13..., remeda ac11baa1...);
- `replay_v2/`, `tscheck_work/`;
- the table, the comparison, `np_returns.tsv`, `refuted_export.tsv`, the drafts and logs.

It also holds the scripts as run and `guard_secs.txt`. Copies of the scripts and tables are in this
directory.

## Cost

- **Compute: 2.10 core-h** over 99 guarded jobs:
  - es-toolkit run 0.85 (15 chunks, 36 min wall);
  - remeda run 0.86 (29 chunks, 30 min wall);
  - rechecks 0.36 (38 files);
  - other post-processing 0.03.

  The registration estimated about 1.9 core-h.
- **Model:** the StrictTS lead session alone (claude-opus-5-5), with no helpers; the tool makes no model
  calls.
- **Tokens:** the lead session's tokens from 04:55Z to 08:25Z cost $30.07 (221 calls). That window also
  covers R6rb's post-processing, the generic-compat development, the merges and the documentation.

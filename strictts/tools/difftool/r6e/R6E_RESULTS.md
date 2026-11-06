# R6e: es-toolkit's and remeda's frozen pairs re-run with master 4016a4a

This is a labelled re-run, not pre-registered. Its inputs and tool were recorded by the paper's evidence
owner before the run, in `~/fv_paper/prereg/ADDENDUM_R6e_inputs.md` (sha256 5e826840...). The addendum
lists first looks (d)–(h). Every gain below comes from them, so the gains are not blind. R6e is the last
re-run for this paper revision.

- **Pairs.** The same as R6d.
  - es-toolkit: R6's 415 (`r6_testable.txt` 408069f7..., `r6_provable.txt` f2f81a47..., sources checked by
    `pairs_SHA256SUMS` bf561176...).
  - remeda: R6r's 862 (`r7_testable.txt` fec09171..., `r7_provable.txt` 14c45704..., sources checked by
    `pairs_SHA256SUMS` 41e73814...).
  - Both pair sources were verified before the run.
- **Tool.** Master 4016a4a8d8fdaa4f551979cab833d7123e7a0c2b, difftool dist fa8ed9263a105167, frontend dist
  654dcdf41dd337e5. It ran from the detached worktree `~/strictts_ws/r6e`.
  - Regressions at 4016a4a: Lean build 160 jobs, corpus 181/0/0, selftest PASS, bench 43/44 + 23/23, 0
    wrong.
  - New against R6d's 25790c3:
    - the cheapest proof alternative first;
    - the `typeof` case split (`StrictTS/Proof/DynTypeof.lean`, `dt_typeof_cases`);
    - more generic-constraint instances;
    - checker types for unannotated wrapper parameters;
    - an old-no-panic proof gets verdict UNKNOWN in the raw JSON, with the proof attached.
- **Clones.** Unchanged from R6d: es-toolkit 9c0cac2ee6c0f807099723d7b226f3b65e976d5c, remeda
  d02c3bdb5e18cfa53e76f33f4ae525adce515379.
- **Scripts.** R6d's, with paths changed, and these changes:
  - `collect_v2.js` also collects the old-no-panic proofs (verdict UNKNOWN now);
  - `report.js` labels them "OLD-NO-PANIC (not an equivalence)", as R6d's addendum table did;
  - `post_run.sh` takes an end stamp for the confirmation window (`TO`), so es-toolkit's window closes
    when remeda's run starts.

## Results

Tables: `es/r6e_table.tsv` (sha256 e66f5d4e49b65f472926ea736642b533aa84d567b362bad07434a9b23ffc7a72) and
`re/r6e_table.tsv` (e948632d742e407df587fbda1f06bd79713c5f6af67ddcb49cdd133fbcb3760b). They have the
statement, domain and inst columns.

| | es-toolkit R6d | es-toolkit R6e | remeda R6d | remeda R6e |
|---|---:|---:|---:|---:|
| PROVED (equivalence) | 64 | 70 | 60 | 61 |
| of which all-worlds / allocated-arguments | 60 / 4 | 67 / 3 | 60 / 0 | 61 / 0 |
| OLD-NO-PANIC (not an equivalence) | 1 | 1 | 2 | 2 |
| REFUTED, Lean-confirmed | 10 | 10 | 9 | 9 |
| REFUTED, Node only | 76 | 76 | 55 | 55 |
| UNKNOWN | 264 | 258 | 736 | 735 |

PROVED equivalences by commit intent:

| commit intent | es-toolkit R6d | es-toolkit R6e | remeda R6d | remeda R6e |
|---|---:|---:|---:|---:|
| refactor/perf/style/chore | 16 | 16 | 29 | 30 |
| fix/feat/revert | 34 | 36 | 26 | 26 |
| docs/test/other | 14 | 18 | 5 | 5 |

The series of equivalences: es-toolkit R6 46, R6b 54, R6c 60, R6d 64, R6e 70; remeda R6r 54, R6rb 59, R6d
60, R6e 61.

### The changes, pair by pair (`es/compare_r6d.tsv`, `re/compare_r6d.tsv`, against `r6d_table_v2.tsv`)

Every pair not listed has the same verdict and statement as in R6d.

es-toolkit, 6 from UNKNOWN to PROVED (all-worlds) and 1 stronger statement:
- `trim`, `trimEnd`, `trimStart` (ec79293f, a test commit: `chars == null` becomes `chars === undefined`).
  The cheapest alternative now comes first; before, they timed out.
- `padEnd`, `padStart` (e3525153, fix), for the same reason.
- `isObject` (63e3755f, docs: `const type = typeof value` is now inlined). Proved by the typeof case split;
  before, it timed out.
- `xor` (e595e5e0): allocated-arguments in R6d, all-worlds in R6e, through the cheapest alternative.

remeda, 1 from UNKNOWN to PROVED (all-worlds):
- `doesNothing` (a5b389b8: `Args extends ReadonlyArray<unknown>` becomes `readonly unknown[]`). The new
  instance table gives the instance `readonly number[]`. In R6d there was no instance for the constraint.

### OLD-NO-PANIC

The same three pairs as in R6d, now verdict UNKNOWN in the JSON with the proof attached:
- es-toolkit `sample` fa2afcd6;
- remeda `last` dbeea0a3;
- remeda `_last` b08a667d.

The return types are in `np_returns.tsv`, unchanged: `T` (or inferred) becomes `T | undefined`. The
statement is the one in R6D_RESULTS.md. Here, es-toolkit `sample` (theorem `equiv_h019u001_np`,
`es/evidence/history-20261027T103830Z-2771472__obs_00.lean`):

```lean
theorem equiv_h019u001_np (I : Impl) : ∀ (vs : Vals Old_h019u001.TT [(.arr .num)]) (w : World Old_h019u001.TT),
    JS.exec (callFun I Old_h019u001.program Old_h019u001.«__difftool_retRef» vs) w =
      JS.exec (callFun I New_h019u001.program New_h019u001.«__difftool_instRef» vs) w ∨
    ∃ (s : String) (w' : World Old_h019u001.TT), JS.exec (callFun I Old_h019u001.program Old_h019u001.«__difftool_retRef» vs) w = some (.error (.panic s), w')
```

### Refutations

They are unchanged for both libraries:
- `replay_v2/replay.tsv`, `tscheck.tsv` and `refuted_export.tsv` are byte-identical to R6d's;
- es-toolkit has 86/86 node replays and 14 confirmation blocks; remeda has 64/64 and 11;
- the mappings are the same.

## Recheck

`lake env lean --tstack=262144` at 4016a4a. The counts include the 3 old-no-panic theorems.

| library | batch files | standard axioms only | no error inside the theorem | run's axiom lines reproduced |
|---|---:|---:|---:|---:|
| es-toolkit | 18 | 71/71 | 71/71 | 132/132 |
| remeda | 22 | 63/63 | 63/63 | 111/111 |

## Evidence

Directory `~/strictts_ws/r6e/scratch/r6e/` (`es/`, `re/`). Manifest R6E_EVIDENCE_SHA256SUMS: 4,047 files,
sha256 223e550fec330558455137cb16b12d92d099be55b1c887b1092e73a63a936a45. It contains:
- `chunks/`;
- `evidence/` (with `proofs.tsv`, which lists the np theorems with statement old-no-panic);
- `evidence_confirm/` (es-toolkit confirmations.tsv b562aba9..., remeda 2306f5ed...);
- `replay_v2/`, `tscheck_work/`;
- the tables, comparisons, `np_returns.tsv`, `refuted_export.tsv`, drafts and logs;
- the scripts as run and `guard_secs.txt`.

Copies of the scripts and tables are in this directory.

## Cost

- **Compute: 1.86 core-h** over 98 guarded jobs:
  - es-toolkit run 0.67 (15 chunks, 32 min wall);
  - remeda run 0.85 (29 chunks, 28 min wall);
  - rechecks 0.31 (40 files);
  - other post-processing 0.03.

  The estimate was 2.1.
- **Model:** the StrictTS lead session alone (claude-opus-5-5), with no helpers in the run; the tool makes
  no model calls.
- **Tokens:** the lead session's tokens from 08:25Z to 11:37Z cost $26.78 (151 calls). That window also
  covers the tool development, the NoPanic merge and the documentation.

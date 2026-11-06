# deedittest.py: planted errors (Lean mutants of the de-editing MOVE)

Each mutant is one exact text replacement in `Cobol/Sem/Data.lean` (the text occurs once), made
in a separate copy of the tree, never in the work tree. Then `lake build cobolrun` in that copy
and `deedittest.py --root <copy> --n 60 --seed 1`. The fixed tree passes 60 of 60 programs at
seed 1 (ok 20, ok-g 17, ok-fault 23).

| id | replacement in `Cobol/Sem/Data.lean` | what it plants | seed 1 result |
|---|---|---|---|
| M1 | `then .ok (-v, f)` -> `then .ok (v, f)` (the negative branch of `deEdit`) | the sign that editing shows is lost | mismatch 51, mirror 7, ok-g 1, ok-fault 1: caught |
| M2 | `if e == bs then .ok (v, f)` -> `if e == bs then .ok (v, 0)` | the picture's decimal point is ignored (the old reading of an all-digit `V` picture) | mirror 2, mismatch 55, ok-fault 2, ok 1: caught |
| M3 | `else .error .invalidData` -> `else .ok (v, f)` | content that no value edits to is accepted | bad-fault 23 (every program with an invalid step): caught |
| M4 | `\| .numEdited pic bwz => moveListE c bs s pic bwz st dsts` -> `\| .numEdited _ _ => moveList c sv sd st dsts` | no de-editing at all (the version before 2026-10-27) | lean-signal 37, bad-fault 23: caught |
| M5 | after the `.digit` line of `editDigits`, a line `\| .insert .zero :: ps, b :: bs, acc => editDigits c ps bs (acc * 10 + (c.decDigit b).getD 0)` | a `0` insertion character read as a digit (GnuCOBOL's G-deedit-zero) | lean-signal 13, bad-fault 11, ok 19, ok-fault 12, ok-g 5: caught |
| M6 | `else if v == 0 && Edit.edit c pic bwz (-1) (f + 1) == some bs then .ok (0, f)` -> `else if false then .ok (0, f)` | a negative value that editing truncated to zero (`-0.00`) faults | survives the random tester (it generates no such sender, see its docstring); caught by `deedit_cases/v_deedit1.cob` (`--run`): the model stops with `invalidData` at the de-editing of `E18` (`-0.00`), the fixed model runs all 74 lines |

How they were run (2026-10-27, helper deedit-fix): `~/coblean_runs/deedit/scripts/run_mutant_v1.sh ID`
(restore `Data.lean`, apply `mut/ID.old` -> `mut/ID.new` with `mutate_v1.py`, build, run, restore,
sha256 checked) in `~/coblean_runs/deedit/mut/tree`, a copy of the fixed tree; M6's probe run with
`run_mutant_probe_v1.sh M6 probe1/pr1_deedit.cob`. The unified diffs are `mut/ID.diff`.

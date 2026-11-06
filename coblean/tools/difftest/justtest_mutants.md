# justtest.py: planted errors (Lean mutants of the group MOVE into a JUSTIFIED item)

Each mutant is one exact text replacement in `Cobol/Sem/Data.lean` (the text occurs once), made in a
separate copy of the tree, never in the work tree: the new arm of `moveInto` for a group sender,

    | .bytes bs true =>
      match d.kind with
      | .alnum true => .ok (writeBytes st d (padLeft c bs d.len))
      | _ => .ok (writeBytes st d (padRight c bs d.len))

Then `lake build cobolrun` in that copy, `justtest.py --root <copy> --n 60 --seed 1` and the hand
case `just_cases/v_just1.cob` (`--run`). The fixed tree passes 60 of 60 programs at seed 1 and
agrees with GnuCOBOL on all 17 lines of the hand case.

| id | the `.alnum true` line becomes | what it plants | seed 1 | v_just1.cob |
|---|---|---|---|---|
| MB1 | `\| .alnum _ => .ok (writeBytes st d (padLeft c bs d.len))` | every alphanumeric receiver of a group right-justified | mismatch 54, ok 6: caught | U10 |
| MB2 | `\| .alnum true => .ok (writeBytes st d (padRight c bs d.len))` | no justification (the version before the change) | mismatch 60: caught | U01 U02 U04-U07 U09 |
| MB3 | `\| .alnum true => .ok (writeBytes st d (padLeft c (bs.take d.len) d.len))` | the leftmost characters kept when the group is longer | mismatch 59, ok 1: caught | U02 U04 U06 |

How they were run (2026-10-28, helper editpoint-fix):
`~/coblean_runs/editfix/scripts/run_mutant_ef_v4.sh Data.lean.B Cobol/Sem/Data.lean ID justtest
tools/difftest/just_cases/v_just1.cob` (restore `Data.lean`, apply `mut/ID.old` -> `mut/ID.new` with
`mutate_ef_v1.py`, build, run, restore and rebuild, sha256 checked) in `~/coblean_runs/editfix/mut/tree`.
The unified diffs are `mut/ID.diff`.

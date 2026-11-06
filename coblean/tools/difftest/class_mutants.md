# Planted errors for classtest.py and dpctest.py

Each mutant is planted in a separate copy of the tree (never in the work tree) by
`run_mutant_class_v1.sh ID SEED` (class-fix's runs directory, `~/coblean_runs/class/tools`): it restores
`Cobol/Edit.lean`, `tools/cobolfe/parser.py` and `tools/cobolfe/datadiv.py` from the work tree, replaces
the one occurrence of OLD by NEW (`mutate_v1.py` refuses unless OLD occurs exactly once), rebuilds
`cobolrun` and runs the tester (60 programs, seed 1) on the copy. A mutant is caught when some program
of the tester's run is not `ok`.

| Id | File | OLD | NEW | Tester | Planted error |
|---|---|---|---|---|---|
| M1 | `tools/cobolfe/parser.py` | `members \|= set(range(min(a[0], b[0]), max(a[0], b[0]) + 1))` | `members \|= set(range(min(a[0], b[0]), max(a[0], b[0])))` | classtest | `THROUGH` leaves out its upper character |
| M2 | `tools/cobolfe/parser.py` | `alts.append({"and": {"a": rel(">=", byte_at(i), lo), "b": rel("<=", byte_at(i), hi)}})` | `alts.append(rel(">=", byte_at(i), lo))` | classtest | a run of characters tested by its lower bound only |
| M3 | `tools/cobolfe/parser.py` | `out.append(dataclasses.replace(t, val="0." + t.val, sep=False, sepch=""))` | `out.append(dataclasses.replace(t, sep=False, sepch=""))` | dpctest | `,5` read as 5 under `DECIMAL-POINT IS COMMA` |
| M4 | `Cobol/Edit.lean` | `if b == c.chr 0x2E then d else if b == c.chr 0x2C then m else` | `if b == c.chr 0x2E then b else if b == c.chr 0x2C then b else` | dpctest | the decimal point and the comma written with their standard characters |
| M5 | `tools/cobolfe/datadiv.py` | `e.pic, e.cat = {"numEdited": {"pic": [picmod.EDIT_SYM[s] for s in syms]}}, "numEdited"` | `e.pic, e.cat, e.bwz = {"numEdited": {"pic": [picmod.EDIT_SYM[s] for s in syms]}}, "numEdited", False` | dpctest | `BLANK WHEN ZERO` on a numeric item ignored |
| M6 | `Cobol/Edit.lean` | `go false (match pic with \| .chars .. :: rest => rest \| _ => pic)` | `go false pic` | dpctest | `classify` does not skip `ESym.chars`: arithmetic results stored into such pictures get no digit positions |

Results (seed 1, 60 programs; not `ok` = caught): see CLASS_PROGRESS.md and the README paragraph.

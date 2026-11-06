# dyntest.py: planted faults

Each mutant changes one line of `Cobol/Sem/File.lean`: the record-key functions (`fileReadBasic`,
`fileStartBasic`, `fileOpenBasic`, used by the files without `FileDecl.keyRef`) or, for M6, the keyed
`READ` by the record key of the files with `keyRef` (`fileReadK`). `cobolrun` is rebuilt and
`dyntest.py --n 60 --seed 1 --root <tree>` runs on it. The unmutated tree passes 60 of 60 at seeds 1
and 2.

Recipe (one mutant at a time, on the unmutated file): replace the exact text OLD, which must occur
exactly once in the file, by NEW, then `scripts/lrun.sh lake build cobolrun`.

| mutant | function | what it breaks | OLD | NEW | seed 1 |
|---|---|---|---|---|---|
| M1 | `fileReadBasic` (failed keyed `READ`, dynamic access) | the reading restarts at the first record, instead of `READ NEXT` giving 46 | `cur := none, eof := true })` | `cur := none, pos := 0 })` | 28 of 60 status-mismatch |
| M2 | `fileReadBasic` (keyed `READ` found, dynamic access) | a successful keyed `READ` after a failed one leaves `READ NEXT` at 46 | `pos := i + 1, eof := false, cur := some i, bound := boundAt d (some r) false` | `pos := i + 1, cur := some i, bound := boundAt d (some r) false` | 11 of 60 status-mismatch |
| M3 | `fileStartBasic` (record found, dynamic access) | a successful `START` after a failed `READ` leaves `READ NEXT` at 46 | `with pos := i, eof := false, cur := none,` (end of line) | `with pos := i, cur := none,` | 2 of 60 status-mismatch |
| M4 | `fileOpenBasic` (dynamic access) | `OPEN` after a failed `READ` and `CLOSE` leaves `READ NEXT` at 46 | `pos := 0, eof := false, cur := none, recs,` (end of line) | `pos := 0, cur := none, recs,` | 5 of 60 status-mismatch |
| M6 | `fileReadK` (keyed `READ` by the record key, `keyRef` files) | `READ NEXT` after a failed keyed `READ` continues | `kor := 0, eof := code == 23` | `kor := 0, eof := false` | 4 of 60 status-mismatch |
| M8 | `fileStartBasic` (no record found, every access mode) | `READ NEXT` (or `READ` in sequential access) after a failed `START` continues | `\| none => (23, setFile st d.id { s with eof := true, cur := none })` | `\| none => (23, setFile st d.id { s with cur := none })` | 21 of 60 status-mismatch |

"status-mismatch": the model's status on a trace line differs from the one the tester's mirror of
IBM's rules predicts (the mirror is checked first). M1, program DY01000: `T008` file 2 model 00, mirror
46, and M6, DY01003: `T005` file 1 model 10, mirror 46: both on G-readfail lines (a `READ NEXT` after a
failed keyed `READ`), where GnuCOBOL is not compared, so only the mirror catches them. M2, DY01001:
`T027` file 2 model 46, mirror 10; M3, DY01006: `T020` file 2 model 46, mirror 00; M4, DY01007: `T022`
file 1 model 46, mirror 00; M8, DY01000: `T042` file 3 (`ACCESS SEQUENTIAL`) model 10, mirror 46.

The unfixed tree (1730Z with altkey-fix's alternate-key change, where a `READ NEXT` after a failed keyed
`READ` by the record key continues from the earlier position on files without `keyRef`) fails 28 of the
60 programs of seed 1 and 26 of seed 2, all status-mismatch: the model gives 00 (or 10) where the
mirror predicts 46, as GnuCOBOL does.

How the runs were made (2026-10-27): `~/coblean_runs/dynread/scripts/run_mutant_v1.sh ID` in the work
tree itself (the replacement by `~/coblean_runs/dynread/scripts/mutate_v1.py FILE ID`, which fails
unless OLD occurs exactly once; `File.lean` restored from a sha256-checked backup after each run, and
`cobolrun` rebuilt after the last one).

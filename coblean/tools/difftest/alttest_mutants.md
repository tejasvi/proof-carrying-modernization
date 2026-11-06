# alttest.py: planted faults

Each mutant changes one line in a copy of the tree: `Cobol/Sem/File.lean` (M1-M4, the alternate-key
functions of files with `FileDecl.keyRef`) or `tools/cobolfe/parser.py` (M5, `SAME RECORD AREA`).
`cobolrun` is rebuilt in the copy and `alttest.py --n 60 --seed 1 --root <copy>` runs on it. The
unmutated tree passes 60 of 60 at seeds 1 and 2.

Recipe (one mutant at a time, on a fresh copy of the file): replace the exact text OLD, which must occur
exactly once in the file, by NEW, then `scripts/lrun.sh lake build cobolrun` in the copy.

| mutant | file | what it breaks | OLD | NEW | seed 1 |
|---|---|---|---|---|---|
| M1 | File.lean (`altLt`) | duplicates in record-key order instead of the order of placement | `    (p.val == q.val && (stampLt p.stamp q.stamp \|\| (p.stamp == q.stamp && bytesLt p.key q.key)))` | `    (p.val == q.val && bytesLt p.key q.key)` | 14 of 60 mismatch |
| M2 | File.lean (`dupNext`) | no 02 after a `READ` whose next record has the same value of the key | `  then 2 else 0` | `  then 0 else 0` | 46 of 60 status-mismatch |
| M3 | File.lean (`fileStartK`) | `START` by an alternate key finds the first record in record-key order | `      match altFirst d s j a ok with` | `      match firstRec ok s.recs with` | 46 of 60 (45 status-mismatch, 1 mismatch) |
| M4 | File.lean (`fileReadK`) | after `READ NEXT` the file position indicator includes the record read: it is read again | `              { s with cur := some i, abound := some (altPos d s j a r, false) })` | `              { s with cur := some i, abound := some (altPos d s j a r, true) })` | 57 of 60 status-mismatch |
| M5 | parser.py (`same_areas`) | `SAME RECORD AREA` without effect (each file keeps its own record area) | `            if kind != "RECORD":` | `            if True:` | 9 of 60 mismatch (the 9 programs with `SAME RECORD AREA`) |

"mismatch": a DISPLAY line differs from GnuCOBOL's, e.g. M1, program AK01000: `T040 02 00 K01u6Axqpq|…`
where GnuCOBOL shows `T040 00 00 K04u2Axqqp|…` (a `READ NEXT` among the duplicates `Ax`: K04 was placed
before K01). "status-mismatch": the model's status on a trace line differs from the one the tester's mirror
of IBM's rules predicts (the mirror is checked first; GnuCOBOL cannot show the 02s, G-dup02), e.g. M2,
AK01000: `T040 00 …` where the mirror predicts 02, M4, AK01000: `T038 00 …` where it predicts 10 (the
record read again instead of the end of the file).

The unfixed tree (snapshot coblean-20261027T1730Z, where `START` by an alternate key and `READ` by an alternate
key with duplicates are unsupported statements and `SAME RECORD AREA` makes a program unsupported) passes
none of the 60 programs of seed 1: 51 `lean-signal`, 9 `frontend-unsupported`.

How the runs were made (2026-10-27): `~/coblean_runs/altkey/mut/run_mutant_altkey_v1.sh ID 1` on the copy
`~/coblean_runs/altkey/mut/mut_tree`, the replacement done by `~/coblean_runs/altkey/mut/mutate_v1.py FILE OLD
NEW` (fails unless OLD occurs exactly once; copied from optional-fix's).

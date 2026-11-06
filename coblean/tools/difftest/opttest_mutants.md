# opttest.py: planted faults

Each mutant changes one line of `Cobol/Sem/File.lean` (`Sem.fileOpen`, the absent-`OPTIONAL` branch) in a
copy of the tree; `cobolrun` is rebuilt there and `opttest.py --n 60 --seed 1 --root <copy>` runs on it. The
unmutated tree passes 60 of 60 at seeds 1 and 2.

Recipe (one mutant at a time, on a fresh copy of the line): replace the exact text OLD, which must occur
exactly once in the file, by NEW, then `scripts/lrun.sh lake build cobolrun` in the copy.

| mutant | what it breaks | OLD | NEW | seed 1 |
|---|---|---|---|---|
| M1 | absence ignored: an absent `OPTIONAL` file opens as a present empty file, status 00 (the NIST runs before this change) | `      if d.optional && env.absent d.id && !s.created then` | `      if false && d.optional && env.absent d.id && !s.created then` | 46 of 60 mismatch |
| M2 | `OPEN INPUT` creates the absent file (a later `OPEN` gives 00, not 05) | `created := mode != .input })` | `created := true })` | 11 of 60 mismatch |
| M3 | creation forgotten: every `OPEN` of a file absent at the start gives 05 and empties it | `env.absent d.id && !s.created then` | `env.absent d.id then` | 50 of 60 mismatch |
| M4 | `OPEN OUTPUT` of an absent file gives 05 (IBM: 00, the file is created) | `(if mode == .output then 0 else 5,` | `(5,` | 23 of 60 mismatch |

Every mismatch is at the first statement whose status the mutant changes, e.g. M2: `S019 00 …` where
GnuCOBOL shows `S019 05 …` (an `OPEN` after `OPEN INPUT` and `CLOSE` of an absent file); M4: `S002 05 …`
where GnuCOBOL shows `S002 00 …` (`OPEN OUTPUT` of an absent file).

The unfixed tree (snapshot coblean-20261027T0518Z, where `SELECT OPTIONAL` makes a program unsupported)
gives `frontend-unsupported` for all 60 programs of seed 1.

How the runs were made (2026-10-27): `~/coblean_runs/optional/run_mutant_v1.sh ID 1` with the replacement
done by `~/coblean_runs/optional/mutate_v1.py FILE OLD NEW` (fails unless OLD occurs exactly once).

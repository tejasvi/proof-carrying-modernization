# closetest.py mutants

Planted errors in the close-fix scratch (one at a time, built, run, restored and checked by sha256:
~/coblean_runs/closefix/scripts/run_mutants_clo_v1.sh). Each must make `closetest.py --n 60 --seed 1`
fail; the hand cases of `close_cases/` are run too.

## CLOSE ... REEL / UNIT (2026-10-28, guard clo_079_mutA)

| id  | file | planted error | closetest seed 1 | hand cases |
|-----|------|---------------|------------------|------------|
| MA1 | Cobol/Sem/File.lean | `REEL` / `UNIT` gives 00 instead of 07 | mismatch 51, ok 9 | v_closereel1 mismatch |
| MA2 | Cobol/Sem/File.lean | `REEL` / `UNIT` closes the file (07) | lean-signal 17, mismatch 38, ok 5 | v_closereel1 lean-signal |
| MA3 | Cobol/Sem/File.lean | the last `READ` is not forgotten (a `REWRITE` right after gets 00, not 43) | mismatch 14, ok 46 | v_closereel1 mismatch |
| MA4 | Cobol/Sem/File.lean | a closed file gets 07 instead of 42 | mismatch 28, ok 32 | v_closereel1 mismatch |
| MA5 | tools/cobolfe/parser.py | the front end writes a plain `CLOSE` for `REEL` / `UNIT` | lean-signal 17, mismatch 38, ok 5 | v_closereel1 lean-signal; u_closereel_absent ok (GnuCOBOL also closes that file, 00) |

All five are caught. The three phrases `REEL` / `UNIT`, `... NO REWIND` and `... FOR REMOVAL` have
one meaning on a disk file, so a front end that mixes them up is not observable.

## CLOSE ... WITH NO REWIND and WITH LOCK (2026-10-28, guard clo_112_mutB)

Run with the tester of this stage (indexed files and the two phrases added).

| id  | file | planted error | closetest seed 1 | hand cases |
|-----|------|---------------|------------------|------------|
| MB1 | Cobol/Sem/File.lean | `WITH LOCK` closes without locking | mismatch 30, ok 30 | v_closelock1 mismatch B05-B09 C02-C05, v_closelock2 mismatch |
| MB2 | Cobol/Sem/File.lean | an `OPEN` of a locked file gives 37 instead of 38 | mismatch 30, ok 30 | v_closelock1 mismatch B05-B08 C02-C04, v_closelock2 mismatch |
| MB3 | Cobol/Sem/File.lean | `WITH NO REWIND` leaves the file open (07) | mismatch 22, lean-signal 8, ok 30 | v_closelock1 lean-signal |
| MB4 | Cobol/Sem/File.lean | `WITH NO REWIND` gives 00 instead of 07 | mismatch 24, ok 36 | v_closelock1 mismatch A03 |
| MB5 | Cobol/Frontend/Resolve.lean | the resolver never sets `FileDecl.lockable` (the lock is set, never checked) | mismatch 30, ok 30 | as MB1 |
| MB6 | tools/cobolfe/parser.py | the front end writes a plain `CLOSE` for `LOCK` | mismatch 30, ok 30 | as MB1 |

All six are caught.

## OPEN INPUT ... REVERSED (2026-10-28, guard clo_132_mutC)

Run with the tester of this stage (`OPEN INPUT ... REVERSED` added).

| id  | file | planted error | closetest seed 1 | hand cases |
|-----|------|---------------|------------------|------------|
| MC1 | Cobol/Sem/File.lean | `REVERSED` unsupported whenever the `OPEN` succeeds | lean-signal 28, ok 32 | v_openrev1 lean-signal |
| MC2 | Cobol/Sem/File.lean | `REVERSED` of an absent `OPTIONAL` file gives 00 instead of 05 | mismatch 10, ok 50 | v_openrev1 mismatch B01 |
| MC3 | Cobol/Sem/File.lean | `REVERSED` opens the file `OUTPUT` | mismatch 20, lean-signal 2, ok 38 | v_openrev1 lean-signal, u_openrev_many mismatch R03 |
| MC4 | Cobol/Sem/File.lean | `REVERSED` skips the lock (and the key-of-reference) dispatch of `OPEN` | mismatch 8, lean-signal 5, ok 47 | v_openrev1 mismatch C02 |
| MC5 | tools/cobolfe/parser.py | the front end writes a plain `OPEN INPUT` for `REVERSED` | ok 60 (survives) | u_openrev_many ok, u_openrev_var ok (both must be lean-signal: row V.close.unsup fails) |

MC1-MC4 are caught by the tester. MC5 is equivalent to the change on every program the tester
generates (an `OPEN INPUT` of a file of at most one record, or one that fails, reads as `REVERSED`
would); the hand cases catch it, since the model must stop at `REVERSED` for a file of two records
and for a variable-length file.

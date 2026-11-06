# Mutants of the SYSIN feature (`sysintest.py`)

Each mutant changes one line of the feature in a separate copy of the tree (never the work tree):
the line is restored from a saved original (sha256 checked) and replaced once, `cobolrun` is rebuilt
for a Lean file, then `sysintest.py --n 60 --seed 1` and the hand cases (`--run
tools/difftest/sysin_cases/*.cob`) run against the copy, and the line is restored (and `cobolrun`
rebuilt). Results on the first run (2026-10-28):

| Mutant | File | Change | Random tester (seed 1, 60 programs) | Hand cases |
|---|---|---|---|---|
| M1 | `Cobol/Sem/Exec.lean` `sysinRead` | the end of the input before any data pads with spaces (GnuCOBOL's behaviour) instead of leaving the area unchanged | mirror 16 | `g_sysin_empty` 0 and `g_sysin_eof` 1 differing lines (were 1, 2) |
| M2b | `sysinRead` | one record per `ACCEPT`, padded (no further records read) | mirror 11 | `g_sysin_long` 0, `g_sysin_empty` 0 (were 1, 1) |
| M3 | `execStmt` `.accept` | the records read (`pos` of the file entry `0`) not advanced | mirror 38, lean-signal 15, bad-fault 7 | unchanged |
| M4 | `sysinRead` | a record longer than the area keeps its right end | mirror 32, lean-signal 17, bad-fault 6 | unchanged |
| M5 | `sysinRead` | the end of the input after data: no space padding (the rest of the area unchanged) | mirror 5 | `v_sysin_pad` 1 (was 0) |
| M6 | `tools/cobolfe/parser.py` | `SYSIPT` not the system input device | fe-unsupported 53 | unchanged |
| M7 | `parser.py` `device_entry` | mnemonic names of `SYSIN` / `SYSIPT` not recorded | fe-unsupported 50 | unchanged |

Every mutant is caught by the random tester. (A first M2, the recursive call on `[]` instead of
the rest of the records, does not compile: `sysinRead` is structurally recursive.)

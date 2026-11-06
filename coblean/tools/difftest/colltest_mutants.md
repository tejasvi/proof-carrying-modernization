# colltest.py: planted faults

Each mutant changes one place in a copy of the tree: the semantics (`Cobol/Sem/Data.lean`), the
resolver (`Cobol/Frontend/Resolve.lean`) or the front end (`tools/cobolfe/parser.py`). `cobolrun` is
rebuilt in the copy after every plant, and `colltest.py --n 60 --seed 1 --root <copy>` runs on it. The
unmutated tree passes 60 of 60 at seeds 1 and 2 (41 and 46 programs name an `ALPHABET` of literals;
the others are in native order, where M1, M2, M3 and M5 cannot show).

Recipe (one mutant at a time, on fresh copies of the files): replace the exact text OLD, which must
occur exactly once in the file, by NEW, then `scripts/lrun.sh lake build cobolrun` in the copy.

| mutant | file | what it breaks | OLD | NEW | seed 1 |
|---|---|---|---|---|---|
| M1 | `Cobol/Sem/Data.lean` (`cmpSeq`) | comparisons in a program collating sequence use the native order | `    let x := pos.getD a.toNat 0` and the next line `    let y := pos.getD b.toNat 0` | `    let x := a.toNat` and `    let y := b.toNat` | 39 of 60 mismatch |
| M2 | `Cobol/Frontend/Resolve.lean` (`collation`) | `LOW-VALUE` is X'00' whatever the alphabet | `low := (groups.headD []).headD 0 }` | `low := 0 }` | 39 of 60 mismatch |
| M3 | `tools/cobolfe/parser.py` (`alphabet_clause`) | an `ALSO` literal gets a position of its own (before its group) | `                    ph["also"].append(lit)` | `                    phrases.append({"lit": lit, "thru": None, "also": []})` | 27 of 60 mismatch |
| M4 | `Cobol/Sem/Data.lean` (`fnBytes`) | alphanumeric `MAX` / `MIN` return the right argument of two equal ones | `.ok (if (if mx then o == .lt else o == .gt) then y else x)` | `.ok (if (if mx then o != .gt else o != .lt) then y else x)` | 29 of 60 mismatch |
| M5 | `Cobol/Frontend/Resolve.lean` (`collation`) | the characters the alphabet leaves out come before the ones it gives | `let groups := given ++ rest.map ([·])` | `let groups := rest.map ([·]) ++ given` | 39 of 60 mismatch |

The first mismatch of a program is at the first statement whose outcome the mutant changes, e.g. M1:
`S13 Y|` where GnuCOBOL shows `S13 N|` (a relation condition); M2 and M5: the first line, which
displays `VALUE HIGH-VALUE` and `VALUE LOW-VALUE` items (M2: `L2 <00><00>` where GnuCOBOL shows the
alphabet's first character); M3: `S04 01|` where GnuCOBOL shows `S04 04|` (an `ORD-MAX` whose
greatest argument begins with a character given with `ALSO`).

Before the tester had statements that make ties visible (`MAX` / `MIN` DISPLAYed, and `ORD-MAX` /
`ORD-MIN`, of an item and a literal that compare equal but differ), M4 failed 1 of 60 programs; the
first runner also left a Lean mutant's `cobolrun` in place for the front-end mutant M3 (that run is
void). Both are fixed in the runs above.

The unfixed tree (`~/coblean_w3m1`, the merge base, where `PROGRAM COLLATING SEQUENCE` and `ALPHABET`
make a program unsupported and the functions are unsupported statements) gives `fe-unsupported` for
all 60 programs of seeds 1 and 2.

How the runs were made (2026-10-27): `~/coblean_runs/collate/tools/run_mutant_coll_v2.sh ID 1 d`
(chain `mut_chain_v2.sh d`), repeated as chain `e` after the last front-end change (with the same
per-program results), with the replacement done by `~/coblean_runs/collate/tools/mutate_v1.py FILE
OLD NEW` (a copy of optional-fix's; fails unless OLD occurs exactly once).

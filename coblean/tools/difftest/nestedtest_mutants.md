# nestedtest.py: planted faults

Each mutant changes one line of the front end (`tools/cobolfe/parser.py`, `datadiv.py` or `unit.py`) in a copy of
`tools/cobolfe`, and `nestedtest.py --n 60 --seed 1 --frontend <copy>` runs on it (the tree's `cobolrun` and
GnuCOBOL; no Lean change, so no rebuild). The unmutated tree passes 60 of 60 at seeds 1 and 2.

Recipe (one mutant at a time, on a fresh copy of `tools/cobolfe`): replace the exact text OLD, which occurs exactly
once in the file, by NEW.

| mutant | file | what it breaks | OLD | NEW | seed 1 |
|---|---|---|---|---|---|
| M1 | `parser.py` | `BY CONTENT` of an item passed `BY REFERENCE` (the called program's changes reach the caller) | `                        args.append(tmp[1])` | `                        args.append(self.ref_json(x) if x.kind == "ref" else tmp[1])` | 15 of 60 mismatch |
| M2 | `unit.py` | `EXTERNAL` records not shared: each later description gets storage of its own | `                    alias[e.id] = b.id` | `                    pass` | 35 mismatch, 8 lean-signal (invalid data in the unshared copy) |
| M3 | `datadiv.py` | name search: a global name of a containing program wins over the program's own declaration | `        if not found and self.outer is not None:` | `        if self.outer is not None and self.outer.knows_global(names[0]):` | 29 of 60 mismatch |
| M4 | `unit.py` | `NOT ON EXCEPTION` statements dropped after a `CALL` of a program of the source | `"e": out + copy.deepcopy(not_exc)}}]` | `"e": out}}]` | 52 of 60 mismatch |
| M5 | `unit.py` | `CANCEL` of a program of the source does nothing | `"t": [unsup(f"{what(n)}: the program is active")], "e": init}}]` | `"t": [unsup(f"{what(n)}: the program is active")], "e": []}}]` | 16 of 60 mismatch |
| M6 | `unit.py` | the variant for a duplicated argument keeps naming the second parameter (not the `REDEFINES` of the first) | `sentences=prefix_stmts(self.substitute(q["sentences"], v["ids"], v["conds"]), pre))` | `sentences=prefix_stmts(q["sentences"], pre))` | 5 of 60 mismatch |
| M8 | `unit.py` | `INITIAL` ignored: a called `INITIAL` program keeps its storage | `            if t.initial:` | `            if False:` | 8 of 60 mismatch |
| M9 | `unit.py` | `RETURN-CODE` not passed back after a `CALL` of a separately compiled program | `            if t.outermost() is not caller.outermost() and rc_t is not None and rc_c is not None:` | `            if False and t.outermost() is not caller.outermost() and rc_t is not None and rc_c is not None:` | 16 of 60 mismatch |

First differing lines (GnuCOBOL, then the mutant): M1 `N00102B1 IN Q   2Mab …` / `N00102B1 IN Q   Q    …` (the caller's
item changed by the callee); M2 `N00100C0 IN 123 …` / `N00100C0 IN \0\0\0 …` (the other description's bytes); M3
`N00101R IN 1Rabc LOC1Rx` / `… GA50xx` (the hidden global shown); M4 `FLAG NE` / `FLAG --`; M5 a counter not reset
after `CANCEL`; M6 `N00106M OUT … W1X …` / `… 6Ma …` (the duplicated argument's new value lost); M8 a counter of an
`INITIAL` program not reset; M9 `RC N00102B1  0008` / `RC N00102B1  0005` (the caller's earlier value).

The unfixed tree (snapshot coblean-20261027T1626Z, where nested and batched programs are rejected) gives
`frontend-error` for all 60 programs of seed 1.

How the runs were made (2026-10-27): copies under `~/coblean_runs/nested/mut/<M>/cobolfe`, the line replaced with
awk (diffs `~/coblean_runs/nested/mut/<M>.diff`), runs by `~/coblean_runs/nested/mut_chain_v1.sh`.

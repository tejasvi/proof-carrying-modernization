# Planted faults for indextest.py

Each mutant changes one line of a copy of the tree (never the tree itself) and runs
`tools/difftest/indextest.py` on it with the arguments given. The unmutated tree agrees on every
program of each run (seeds 1 and 2: 60 of 60 each; `--mixed --seed 3`: 60 of 60).

## M1, front end: the SEARCH ... VARYING index data item misses the AT END update

The index data item named in `VARYING` takes the hidden index's value at the start of each `WHEN`
phrase and of `AT END` (`st_SEARCH` in `tools/cobolfe/parser.py`). The mutant drops the update
in `AT END`, so after a search that ends there the item keeps its value from before the search.

    cp -a tools/cobolfe MUT1/cobolfe
    # MUT1/cobolfe/parser.py, the one line
    #     at_end = [upd()] + (at_end or [])
    # becomes
    #     at_end = at_end or []
    sed -i 's/^            at_end = \[upd()\] + (at_end or \[\])$/            at_end = at_end or []/' MUT1/cobolfe/parser.py
    COBOLFE=MUT1/cobolfe/cobolfe.py python3 -I -B tools/difftest/indextest.py --n 60 --seed 1 --out OUT

## M2, resolver: PERFORM VARYING an index name steps the wrong way

`varyingIdxParts` (`Cobol/Frontend/Resolve.lean`) makes the augmentation `SET i UP BY b`. The
mutant makes it `SET i DOWN BY b` (the last argument of `setIdxBy`, `down`, becomes `true`).

    cp -a TREE MUT2          # then, in MUT2/Cobol/Frontend/Resolve.lean, the one line
    #   pure ([.setIdx i (← expr ctx 0 false fromE)], [.setIdxBy i (← expr ctx 0 false byE) false])
    # ends in `byE) true])` instead
    sed -i 's/\[\.setIdxBy i (← expr ctx 0 false byE) false\])$/[.setIdxBy i (← expr ctx 0 false byE) true])/' MUT2/Cobol/Frontend/Resolve.lean
    (cd MUT2 && scripts/lrun.sh lake build cobolrun)
    python3 -I -B MUT2/tools/difftest/indextest.py --n 60 --seed 1 --out OUT

## M3, front end: no element-length classes

`ix_finish` (`tools/cobolfe/parser.py`) makes the statements touching index data items whose
values meet index names of several element lengths unsupported. The mutant finds no such class,
so the model runs those statements with occurrence numbers (GnuCOBOL's representation), and the
`--mixed` programs, which expect a stop with `unsupported`, fail.

    cp -a tools/cobolfe MUT3/cobolfe
    sed -i 's/^        mixed = {r: sorted(ls) for r, ls in self.ix_lens.items() if len(ls) > 1 and /        mixed = {r: sorted(ls) for r, ls in self.ix_lens.items() if len(ls) > 99 and /' MUT3/cobolfe/parser.py
    COBOLFE=MUT3/cobolfe/cobolfe.py python3 -I -B tools/difftest/indextest.py --n 60 --seed 3 --mixed --out OUT

## Results (2026-10-27)

| Run | Unmutated | Mutant |
|---|---|---|
| M1, `--seed 1` | 60 of 60 agree | 28 agree, 32 differ (first: program 1, `L6 XK2` 0006 vs 0005) |
| M2, `--seed 1` | 60 of 60 agree | 8 agree, 52 differ (first: program 0, `L1 IC` 0002 vs 0000) |
| M3, `--mixed --seed 3` | 60 of 60 stop as expected | 0 of 60 stop: the model runs on and agrees with GnuCOBOL to the end |

The control, the 0518Z front end (`COBOLFE=` its `tools/cobolfe/cobolfe.py`), agrees on none of
the 60 programs of seed 1 or seed 2: it rejects every program (`USAGE INDEX is not supported`).

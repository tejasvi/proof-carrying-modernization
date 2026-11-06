# Planted faults for odotest.py

Each mutant changes one line of a copy (never the tree itself), written by
`tools/difftest/odo_mutate.py SRC DST OLD NEW`, which refuses unless OLD occurs exactly once in SRC,
and runs `tools/difftest/odotest.py` on it with the arguments given. The unmutated tree agrees on
every program of each run (seeds 1 and 2: 60 of 60 each; `--mixed --seed 3`: 60 of 60 stop as
predicted). TREE is the coblean tree, OUT and MUTk new directories.

## M1, resolver: a group containing the table always has its maximum length

`odoDesc` (`Cobol/Frontend/Resolve.lean`) gives a reference made while the object holds `v` the
group with `v` occurrences. The mutant returns the declared descriptor (the maximum length), as if
the maximum length rule applied to every reference.

    cp -a TREE MUT1
    python3 -I -B TREE/tools/difftest/odo_mutate.py TREE/Cobol/Frontend/Resolve.lean \
        MUT1/Cobol/Frontend/Resolve.lean \
        '    pure { p.desc with len := p.desc.len - (mx - v) * stride }' '    pure p.desc'
    (cd MUT1 && LRUN_AS=67108864 scripts/lrun.sh lake build cobolrun)
    python3 -I -B TREE/tools/difftest/odotest.py --n 60 --seed 1 --root MUT1 --out OUT

## M2, front end: MOVE receivers lose the maximum length rule

`Odo.own_refs` (`tools/cobolfe/odo.py`) marks the receivers of a MOVE as receivers of IBM's
maximum length rule. The mutant does not, so a MOVE into a group that contains its object fills the
group's current length (what GnuCOBOL does with -std=ibm, G-odoslide).

    mkdir MUT2 && cp -a TREE/tools/cobolfe MUT2/cobolfe
    python3 -I -B TREE/tools/difftest/odo_mutate.py TREE/tools/cobolfe/odo.py MUT2/cobolfe/odo.py \
        'scan(d, "recv", False, nxt(), True)' 'scan(d, "recv", False, nxt(), False)'
    COBOLFE=MUT2/cobolfe/cobolfe.py python3 -I -B TREE/tools/difftest/odotest.py --n 60 --seed 1 --out OUT

## M3, front end: no range check of the object

`Odo.check` makes the `odoCheck` condition that faults (range) when an object is outside
integer-1 .. integer-2. The mutant makes it the constant true: the model then runs on (and a
statement split on the object's values does nothing for a value outside them), so the `--mixed`
programs, which expect a stop with a range fault, fail.

    mkdir MUT3 && cp -a TREE/tools/cobolfe MUT3/cobolfe
    python3 -I -B TREE/tools/difftest/odo_mutate.py TREE/tools/cobolfe/odo.py MUT3/cobolfe/odo.py \
        'return {"odoCheck": {"id": t.id}}' 'return {"const": {"b": True}}'
    COBOLFE=MUT3/cobolfe/cobolfe.py python3 -I -B TREE/tools/difftest/odotest.py --n 60 --seed 3 --mixed --out OUT

## M4, front end: SEARCH and SEARCH ALL cover the maximum number of occurrences

In each copy of a split SEARCH / SEARCH ALL the front end sets the number of occurrences to the
object's value. The mutant keeps integer-2.

    mkdir MUT4 && cp -a TREE/tools/cobolfe MUT4/cobolfe
    python3 -I -B TREE/tools/difftest/odo_mutate.py TREE/tools/cobolfe/odo.py MUT4/cobolfe/odo.py \
        'g["occurs"] = vals[tab.id]' 'g["occurs"] = tab.occurs'
    COBOLFE=MUT4/cobolfe/cobolfe.py python3 -I -B TREE/tools/difftest/odotest.py --n 60 --seed 1 --out OUT

## Results (2026-10-27)

| Run | Unmutated | Mutant |
|---|---|---|
| M1, `--seed 1` | 60 of 60 agree | 14 agree, 46 differ (first: program 0, a READ ... INTO shows the record's bytes beyond FN's occurrences) |
| M2, `--seed 1` | 60 of 60 agree | 32 agree, 28 differ (first: program 4, GB after a MOVE into it) |
| M3, `--mixed --seed 3` | 60 of 60 stop as predicted | 0 of 60 stop: the model runs on |
| M4, `--seed 1` | 60 of 60 agree | 43 agree, 17 differ (first: program 2, a serial SEARCH finds an element above NA) |

The control, the front end and cobolrun of the unfixed snapshot coblean-20261027T1626Z (`--root`),
agrees on none of the 60 programs of seed 1 or seed 2: its front end rejects every program
(`OCCURS DEPENDING ON is not supported`).

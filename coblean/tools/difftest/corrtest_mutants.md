# Planted faults for corrtest.py

Each mutant changes one line of a copy of `tools/cobolfe` (never the tree itself) and runs
`tools/difftest/corrtest.py` with the copy's front end (`COBOLFE`). The unmutated tree agrees on
every program of each run (seeds 1 and 2: 60 of 60 each). The copy and the edit were made by
`mk_mutant_v1.sh NAME FILE OLD NEW` (copy `tools/cobolfe` to `NAME/cobolfe`, replace OLD by NEW on
the one line of FILE that contains it, write `NAME.diff`).

## M1, CORRESPONDING pairs: items with REDEFINES are not left out

`corr_pairs` (`tools/cobolfe/parser.py`) leaves out subordinate items described with REDEFINES
(IBM: "The subordinate items do not include a REDEFINES, RENAMES, OCCURS, USAGE INDEX ... clause in
their descriptions."). The mutant drops that test, so a REDEFINES item of the sender is moved to
(or receives from) a REDEFINES item of the same name.

    cp -a tools/cobolfe M1/cobolfe
    # M1/cobolfe/parser.py, in corr_pairs.eligible, the one line
    #     return e.name != "FILLER" and e.redefines is None and e.occurs is None and not e.index \
    # becomes
    #     return e.name != "FILLER" and e.occurs is None and not e.index \
    COBOLFE=M1/cobolfe/cobolfe.py python3 -I -B tools/difftest/corrtest.py --n 60 --seed 1 --k 12 --out OUT

Result (seed 1): 3 mismatch, 1 model-unsupported (a REDEFINES pair whose MOVE the model refuses),
56 ok: programs 0, 33, 48, 50.

## M2, ADD / SUBTRACT CORRESPONDING: a size error stores the truncated result

`arith_corr` gives each pair an empty ON SIZE ERROR phrase when the statement has ON SIZE ERROR, so
that a receiver with a size error keeps its value (IBM: "the value of the resultant identifier
affected by the size error is not altered"). The mutant never traps: every receiver gets the
truncated result (the counter and the final IF are unchanged).

    cp -a tools/cobolfe M2/cobolfe
    # M2/cobolfe/parser.py, in arith_corr, the one line
    #     trap = [] if on is not None else None
    # becomes
    #     trap = None
    COBOLFE=M2/cobolfe/cobolfe.py python3 -I -B tools/difftest/corrtest.py --n 60 --seed 1 --k 12 --out OUT

Result (seed 1): 26 mismatch, 34 ok.

## M3, RENAMES THROUGH: the area is as long as data-name-3 only

`finish_renames` (`tools/cobolfe/datadiv.py`) makes a level-66 item with THROUGH cover the bytes
from the start of data-name-2 to the end of data-name-3. The mutant makes its length that of
data-name-3.

    cp -a tools/cobolfe M3/cobolfe
    # M3/cobolfe/datadiv.py, in finish_renames, the one line
    #     ln = hi3 - lo
    # becomes
    #     ln = item_size(e3)
    COBOLFE=M3/cobolfe/cobolfe.py python3 -I -B tools/difftest/corrtest.py --n 60 --seed 1 --k 12 --out OUT

Result (seed 1): 26 mismatch, 34 ok (a different set of programs from M2's).

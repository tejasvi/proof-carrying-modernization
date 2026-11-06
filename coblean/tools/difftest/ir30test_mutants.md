# ir30test.py mutants

Each mutant changes one place of the fixed code (Cobol/Frontend/Resolve.lean, Cobol/Sem/Arith.lean or, in part c30, the front
end tools/cobolfe/parser.py), is built (lake build
Cobol cobolrun) and run with `ir30test.py --seed 1 --n 60` and the hand cases (`--run tools/difftest/ir30_cases/*.cob`,
compared as a whole text with the run of the fixed code; g_ir30_1.cob is a GnuCOBOL departure and always differs from
GnuCOBOL), and tests/Ar2Resolve.lean against the base resolver: the 15 theorem IRs and the population of the resolver checks
(395 NIST and 17 CardDemo front-end outputs, the CSUTLDTC and COBSWAIT pins, probe f4probe1); the fixed file is then
restored and checked by its sha256, and after the last mutant the rebuilt cobolrun and the oleans of Resolve, Load, Arith,
IR, Exec and Cobol are byte-identical to those before the mutants. Fixed code: run mA (MA1-MA7); MA5 again in run mA2 with
the hand case u_ir30_rndc.cob, written after MA5 survived run mA; MA9 in run mA9 on the final tree. MA8 is no planted
change but the tree before `Resolve.divScaled` (see its row). Part powlit (MB1-MB6, below) runs with `--part powlit` and
the hand cases `tools/difftest/powlit_cases/*.cob`.

| id | change | tester seed 1 | hand cases | resolver check |
|---|---|---|---|---|
| MA1 | row 3 cuts no decimal place | mirror 37, ok-stop 12, ok-g 7, ok 4 | g_ir30_1 G01 G03 G04 as GnuCOBOL | 15 same; population as fixed |
| MA2 | the final result of one receiver without ROUNDED taken as an intermediate result | lean-signal 14, stop-mismatch 4, mirror 4, ok-stop 15, ok-g 19, ok 4 | v_ir30_1 stop-cut (V10, a 36-digit MULTIPLY GIVING final result) | 15 same; 7 different (+ IF110A, NC120A, NC170A, NC207A) |
| MA3 | a cut nonzero high-order digit not reported (Arith.lean) | stop-mismatch 15, ok-stop 8, ok-g 33, ok 4 | u_ir30_cut ok, u_ir30_rem ok | as fixed (no IR change) |
| MA4 | ROUNDED neither widens the places nor leaves rows 3 and 4 open | stop-mismatch 8, ok-stop 15, ok-g 33, ok 4 | u_ir30_open mismatch | as fixed |
| MA5 | the fast path's bound leaves out ROUNDED's places | ok-stop 23, ok-g 33, ok 4 (survives) | run mA: as fixed; run mA2: u_ir30_rndc ok | as fixed |
| MA6 | a cut operand leaves the quotient's places as `expr` took them from the uncut one | ok-stop 23, ok-g 33, ok 4 (survives) | g_ir30_1 G04 420718385588.021736 | as fixed |
| MA7 | the steps of FUNCTION REM not checked (no decomposition) | ok-stop 23, ok-g 33, ok 4 (survives) | u_ir30_rem ok | 15 same; IF133A same (2 different) |
| MA8 | (history) the tree before `Resolve.divScaled`: an expression with a division of the extractor's places (`--div-scale`) also carried by the 30-digit rule | not run | not run | the earlier testers at seed 1 fail: difftest.py lean-signal 36 / 34 / 12 (TRUNC(STD), TRUNC(BIN), front end), cov f3round 33, f3prohib 53 |
| MA9 | `DIVIDE … INTO` without `GIVING` bounds the front end's dividend (the literal 0), not each receiver (stage A's hook, corrected in stage B) | ok-stop 23, ok-g 33, ok 4 (survives: no `DIVIDE` generated) | u_ir30_divinto ok | as fixed |

## Part powlit: powers by a literal exponent

Run mutB2 on the final tree (tester and build as delivered); run mutB had the same six mutants on the tree before the
`DIVIDE ... INTO` correction, with the tester before its steps of 28- and 29-digit powers under `ROUNDED` and its
conditions against IBM's value (there MB3 and MB5 failed only the hand row, MB4 mirror 2, MB6 mirror 5). The resolver check
gives 15 same and the population as the fixed code (3 different: IF133A, NC250A, f4probe1) for every mutant.

| id | change | tester seed 1 (`--part powlit`) | hand cases |
|---|---|---|---|
| MB1 | at i + d = 30 the parity rule reversed (an even number of digits in the base carried exactly, an odd one with `dmax`) | mirror 26, lean-signal 3, stop-mismatch 1, ok-stop 5, ok-g 24, ok 1 | g_powlit_1 G03 as GnuCOBOL |
| MB2 | a power held with `dmax` places stays exact (no `Expr.powInt`) | mirror 50, stop-mismatch 9, ok 1 | g_powlit_1 G01 G02 G03 as GnuCOBOL; u_powlit_cut ok |
| MB3 | under `ROUNDED` the row taken as open from 30 digits on (not 28) | stop-mismatch 3, ok-stop 9, ok-g 47, ok 1 | u_powlit_rnd ok |
| MB4 | a literal base counted as a data name (i = i1 * n, not the integer digits of the power's value) | mirror 2, ok-stop 12, ok-g 45, ok 1 | as fixed |
| MB5 | the fast path's bound of a power reaching 30 digits is 30 (not 31) | mirror 20, ok-stop 10, ok-g 29, ok 1 | u_powlit_rnd ok |
| MB6 | the number of digits of an item base counts its integer places only | mirror 5, ok-stop 10, ok-g 44, ok 1 | as fixed |

## Parts pow0 and c30: powers by the literal 0, the composite of operands, the MULTIPLY hook

Run mutC4 (MC1-MC3, MC7, `--part pow0`, hand cases `tools/difftest/pow0_cases/*.cob`) and run mutC3 (MA10, MC4-MC6,
`--part c30`, hand cases `tools/difftest/c30_cases/*.cob`). MC4-MC6 change the front end (`tools/cobolfe/parser.py`), the
others the semantics or the resolver. The resolver check gives 15 same and the population as the fixed code for every mutant
(no front-end output of the corpus has a power by the literal 0, a composite over 30 digits or a MULTIPLY ... BY whose
product can need more than 30 digits). Run mutC0 had MC1-MC3 on the tree before `Expr.pow0` got its `NOT ON SIZE ERROR`
flag, with the tester before its stop step (mirror 54, ok 6 each); run mutC4 repeats them on the final texts.

| id | change | tester seed 1 | hand cases |
|---|---|---|---|
| MA10 | `MULTIPLY ... BY` without `ROUNDED` bounded too (stage A's hook before its stage C correction) | lean-signal 16, stop-mismatch 11, ok-stop 9, ok 24 | v_c30_1 stops at K06 ("MULTIPLY ROUNDED ...") |
| MC1 | a zero base raised to the literal power 0 never a size error (the ON SIZE ERROR flag ignored; Arith.lean) | mirror 55, ok-stop 3, ok 2 | g_pow0_1 H01 H03 "N" (no size error) |
| MC2 | the `COMPUTE` does not mark its powers by the literal 0 with its `ON SIZE ERROR` (no `markPow0 true false`) | mirror 55, ok-stop 3, ok 2 | g_pow0_1 H01 H03 "N" |
| MC3 | a power by the literal 0 is the literal 1, its base not evaluated (the lowering before stage C) | stop-mismatch 22, mirror 36, ok 2 | g_pow0_1 H01 H03 "N"; u_pow0_not runs (U01 differs) |
| MC7 | a `COMPUTE` with `NOT ON SIZE ERROR` alone does not mark its powers by the literal 0 (a zero base is 1, the phrase runs) | stop-mismatch 22, ok-g 36, ok 2 | u_pow0_not runs (U01 differs) |
| MC4 | a composite of exactly 30 digits refused (`>= 30`; parser.py) | stop-mismatch 20, fe-unsupported 40 | v_c30_1 fe-unsupported |
| MC5 | `ADD ... TO` leaves its receivers out of the composite (parser.py) | stop-mismatch 9, ok-stop 11, ok 40 | u_c30_add, u_c30_lit run (ok) |
| MC6 | `DIVIDE` counts its `REMAINDER` item in the composite (parser.py) | ok-stop 20, ok 40 (survives: no `REMAINDER` generated) | v_c30_1 fe-unsupported (K09) |

# dmaxtest.py mutants

Each mutant changes one place of the fixed code (Cobol/Frontend/Resolve.lean, or tools/cobolfe/parser.py), is built (lake
build Cobol cobolrun, for a Lean file) and run with `dmaxtest.py --part P --seed 1 --n 60` and the hand cases (`--run
tools/difftest/dmax_cases/*.cob`; the g_*.cob cases are GnuCOBOL departures and always differ); for a Lean mutant from stage
B on, also tests/DmaxResolve.lean against the base resolver: the 15 theorem IRs, the six IF111A / IF114A paragraphs that
divide inside INTEGER / INTEGER-PART arguments, and an exposure list (stages B to D: r1probe1.cob and NIST IF111A / IF114A;
stage E: the population of the resolver checks, 388 NIST programs, 17 CardDemo programs and the two pinned IRs). inr-fix's
mutants (ids `inr …`; stage A: R1 and F7, the expressions inside function arguments; stage B: R2, `ROUNDED MODE`) are
checked against both the resolver before dmax-fix and the 2106Z resolver: the 15 theorem IRs, the CSUTLDTC and COBSWAIT
pin IRs, eleven paragraphs (those six and the five NIST statements whose argument quotients change) and the 413 front-end
outputs of merge 11's identity run with the two pins. The fixed file is then restored and checked by its sha256, and after
the last mutant the rebuilt cobolrun and the oleans of Resolve, Load, Surface and Cobol are byte-identical to those before
the mutants.

| id | stage | change | part | tester seed 1 | hand cases |
|---|---|---|---|---|---|
| MA1 | A (G) | `cond88` compares an ALL literal value as a plain literal (padded with spaces, not repeated) | all88 | mismatch 32, ok 28 | v_all88 mismatch, v_all88_nc250a mismatch |
| MA2 | A (G) | `SET ... TO TRUE` moves SPACE for an ALL literal value again | all88 | mismatch 53, ok 7 | v_all88 mismatch, v_all88_nc250a ok |
| MB1 | B (F2) | a relation condition gets dmax 0 again | cond | mismatch 30, ok-g 21, ok 9 | v_cond1 mismatch |
| MB2 | B (F2) | `relOwn` gives both sides the relation's dmax | cond | mismatch 36, ok-g 16, ok 8 | v_cond1 ok |
| MB3 | B (F2) | a sign condition gets dmax 0 again | cond | mismatch 12, ok-g 34, ok 14 | v_cond1 mismatch |
| MB4 | B (F2) | the front end keeps EVALUATE comparisons with a division as `relExpr` (parser.py) | cond | mismatch 40, ok 8, ok-g 12 | v_cond1 mismatch |
| MB5 | B (R1) | function arguments get the statement's dmax | cond | ok-g 43, ok 17 (survives) | all as fixed; caught by the R1 check: r1probe1 DIFFERENT |
| MC1 | C (F3) | a COMPUTE's dmax leaves numeric-edited receivers out again | edited | mirror 60 | v_edited1 mismatch |
| MC2 | C (R1) | a COMPUTE's function arguments get the edited receivers' places too | edited | ok-g 53, ok 7 (survives) | all as fixed; caught by the R1 check: r1probe1 DIFFERENT |
| MC3 | C (F3) | an edited receiver counts all its digit positions, not those after the point | edited | mirror 53, ok 7 | as fixed |
| MD1 | D (F6) | INTEGER, INTEGER-PART and MOD count their arguments' places in dmax again | intfn | mirror 59, ok-g 1 | as fixed (g_intfn1's labels change) |
| MD2 | D (R1) | a COMPUTE's function arguments get the new dmax (`dScales` instead of `dScalesIn`) | intfn | ok-g 60 (survives) | as fixed; caught by the R1 check: 4 of the 6 IF111A / IF114A paragraphs, r1probe1, IF111A and IF114A DIFFERENT |
| ME1 | E (F1) | the quotient's scale is max(divisor places, dmax) again | div | mirror 45, ok-g 12, ok 3 | v_div1 mismatch |
| ME2 | E (F1) | no old scale kept for a `COMPUTE` that is one division | div | ok-g 57, ok 3 (survives: the same stored values) | as fixed; caught by the resolver check: theorem IR cbact04c DIFFERENT (1300-COMPUTE-INTEREST); in the population CardDemo CBACT04C 1300-COMPUTE-INTEREST and NIST NC252A COMP-TEST-32 |
| ME3 | E (F1) | the old scale kept also under `ROUNDED` | div | mirror 28, ok-g 32 | as fixed; the resolver check: theorem IRs acctint and acctint.gnucobol DIFFERENT (1000-CALC), NC252A COMP-TEST-26, COMP-TEST-37, COMP-TEST-045 |
| inr MA1 | inr A (R1) | function arguments take the statement's dmax and `ROUNDED` place | fnarg; fncond | mirror 60; mismatch 22, ok-g 23, ok 15 | as fixed; the population resolves as with the 2106Z resolver |
| inr MA2 | inr A (F7) | function arguments take dmax 0 in every statement | fnarg; fncond | mirror 54, lean-signal 5, ok-g 1; mismatch 28, ok-g 20, ok 10, lean-signal 2 | v_fnarg1 mismatch |
| inr MA3 | inr A (R1) | each argument takes the places of its own operands only | fnarg; fncond | mirror 48, ok-g 11, lean-signal 1; mismatch 12, ok-g 34, ok 13, lean-signal 1 | v_fnarg1 mismatch |
| inr MA4 | inr A (R1) | `ROUNDED`'s extra place reaches the arguments again | fnarg; fncond | mirror 49, ok-g 11; ok-g 45, ok 15 | as fixed |
| inr MA5 | inr A (R1) | INTEGER and INTEGER-PART get inner-dmax 0 too | fnarg; fncond | mirror 16, ok-g 44; mismatch 6, ok-g 40, ok 14 | as fixed |
| inr MB1 | inr B (R2) | a lone quotient keeps IBM's intermediate under every mode again | rmode | mirror 21, ok-g 20, ok 19 | v_rmode1 mismatch |
| inr MB2 | inr B (R2) | a lone quotient takes the `DIVIDE ... GIVING` form for plain `ROUNDED` and truncation too | rmode | ok-g 32, ok 28 (survives: the same stored values) | as fixed; caught by the resolver check: theorem IRs acctint and acctint.gnucobol (1000-CALC) and cbact04c (1300-COMPUTE-INTEREST) DIFFERENT |
| inr MB3 | inr B (R2) | only the first receiver's mode decides the form | rmode | mirror 1, ok-g 31, ok 28 | as fixed |

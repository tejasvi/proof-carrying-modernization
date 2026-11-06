# powtest.py: planted errors (2026-10-28, ifn2-fix)

Each mutant was applied alone to the work tree (one exact replacement: `mutate_v1.py`, and for the front end of the final
sources `mutate_v2.py`), cobolrun was rebuilt for a Lean file, and powtest.py ran at seed 1 (60 programs) together with
the hand cases of `pow_cases/` (`powtest.py --run`); the file was then put back and its sha256 checked, and for a Lean
file cobolrun and the oleans were rebuilt and found byte-identical to those before the mutant. The unmutated tree passes
60 of 60 at seeds 1 and 2.

| mutant | change | powtest.py seed 1 | hand cases |
|---|---|---|---|
| MP1 | `powIntVal`: the power rounded (`nearestAwayFromZero`) to dmax places instead of truncated | mirror 28 of 60 | as unmutated (the hand cases compare with GnuCOBOL only) |
| MP2 | `powIntVal`: for a negative exponent 1 divided by the exact power (GnuCOBOL's way) instead of by ir4 | mirror 18 | g_pownegdiv: U01 now agrees with GnuCOBOL |
| MP3 | `powIntVal`: a power truncated to 0 under a negative exponent gives 0 instead of dividing by zero | mirror 22 | g_pow0neg agrees with GnuCOBOL; g_pownegdiv U04 agrees |
| MP8 | `powIntVal`: the exponent's sign ignored | mirror 47 | v_pow1 P16 P17 differ |
| MP4 | resolver: the power's scale dmax + 1 instead of dmax | mirror 35 | g_powtrunc agrees with GnuCOBOL; g_pownegdiv U01-U03 agree |
| MP5 | front end: a condition with decimal operands takes the new path | unsup-mismatch 3 | u_pow_decrel runs (ok) instead of fe-unsupported |
| MP6 | front end: a ROUNDED receiver takes the new path | unsup-mismatch 1 | u_pow_rounded: cobolrun-error (the resolver refuses ROUNDED) |
| MP7 | front end: a numeric-edited receiver takes the new path | unsup-mismatch 1 | u_pow_edited runs (R01 differs) instead of fe-unsupported |
| MP9 | front end: INTEGER / INTEGER-PART of a decimal argument allowed in the COMPUTE | unsup-mismatch 4 | u_pow_intfn runs (R01 differs) instead of fe-unsupported |
| MP10 | front end: a power under a literal exponent takes the new path | unsup-mismatch 2 | u_pow_litover runs (R01 differs) instead of fe-unsupported |

MP1-MP4 and MP8 ran on the first sources (their Lean files are unchanged since); MP5-MP7, MP9 and MP10 ran on the final
front end (with the first front end MP5 survived the tester at seed 1, which then had no program ending with the decrel
form, and was caught by the hand case). Every mutant fails the tester or a hand-case row (V.pow.gdep, V.pow.unsup,
V.pow.hand); the runs are in `~/coblean_runs/ifn2/mut/<mutant>/`, `~/coblean_runs/ifn2/mut2/<mutant>/`, `mut1.out` and
`mut2.out`.

RESULT: PASS. Our own scan finds exactly one division in a theorem program, CBACT04C's 1300-COMPUTE-INTEREST, where F1 changes
the places carried (model 2, IBM 4); the quotient is stored by truncation into a 2-place receiver, so by a Lean theorem
the stored value is the same under both rules for every input, provided IBM truncates the extra intermediate places.
No theorem IR has F2, F3, F5, F6 or G. The session's probes reproduce its reported outputs.

# Arithmetic departures F1-F6, G (reported by the COBOL maintainer session before any fix): evidence-owner check (an agent of the evidence-owner session; written 2026-10-28T14:11:38Z)
Read only on the snapshots and the COBOL maintainer session's files (~/coblean_ifn2/IFN2_PROGRESS.md, ~/coblean_runs/ifn2). Guarded jobs
(coreh_guard_v2, ulimit -v 32 GiB; guard/). Scanner and Lean files written by us, independently of the COBOL maintainer session's scan_*.py.

## 1. Exposure scan of the theorem IRs (scan/): PASS
- Population (scan/files.txt, hashes scan/files.sha256): the 15 examples/*/*.ir.json of snapshot 20261024T2306Z (the 9
  CardDemo IRs, acctint, bincnt, recsum and their gnucobol variants; the session's 15) plus the pins' csutldtc.ir.json
  (pinM3), cobswait.ir.json (pinM7) and cbstm03b.ir.json (pin2306Z-cbstm03b): 18 files.
- Scanner scan/scan_arith_v1.py: every COMPUTE division (there is no DIVIDE statement in these IRs), dividend, divisor and
  receiver places, statement dmax (receivers' places incl. numeric-edited, operand places outside divisors and
  exponents), model places max(divisor places, dmax) vs IBM max(dividend places - divisor places, dmax); F2 (division in a
  condition), F3 (numeric-edited COMPUTE receiver), F5 (literal power), F6 (INTEGER / INTEGER-PART / MOD with decimal-place
  arguments), G (88-level value with an ALL literal).
- Planted control scan/plant_arith.ir.json (plant.out): all six classes found, including the three F1 verdicts.
- Result (scan.out): 18 files, 12 COMPUTE statements, 3 divisions, 0 powers, 1 MOD reference, 91 88-level conditions.
  - CBACT04C 1300-COMPUTE-INTEREST: WS-MONTHLY-INT (S9(9)V99, not ROUNDED) = (TRAN-CAT-BAL S9(9)V99 * DIS-INT-RATE
    S9(4)V99) / 1200: dividend places 4, divisor 0, dmax 2; model 2 places, IBM 4; lone quotient, receiver places 2 <= both:
    same stored value (section 2).
  - acctint and acctint.gnucobol 1000-CALC (coblean's own example, not a paper theorem program): WS-DAILY-RATE (scale 8,
    ROUNDED) = ACCT-RATE (scale 5) / 365: dmax 8; model 8 = IBM 8 places: no change.
  - F2, F3, F5, F6, G: 0. CBTRN03C's MOD(WS-LINE-COUNTER, WS-PAGE-SIZE) has integer arguments; the 13 ALL literals in the
    IRs are VALUE clauses of ordinary items (CBSTM03A/B, CBTRN03C), not 88-level values. F4 and R1 were not scanned (the
    session reports 0 in the theorem IRs).

## 2. CBACT04C: same stored value (lean/, source citations): PASS, with one assumption about IBM
- lean/TruncComp.lean (Lean v4.35.0, no Mathlib): trunc_comp: for all a b : Int with 0 < b,
  ((a * 10000).tdiv b * 100).tdiv 10000 = (a * 100).tdiv b, i.e. truncating a / b toward zero to 4 places and then to 2
  equals truncating it to 2 places, for every rational, negatives included; cbact04c_interest is the instance
  b = 10000 * 1200 (dividend with 4 places, divisor 1200). #print axioms (lean/trunc.out): each exactly [propext,
  Classical.choice, Quot.sound]; planted controls (lean/Controls.lean, controls.out): [sorryAx], [plantedAx].
- Model side, snapshot 2306Z: Cobol/Frontend/Resolve.lean:140-146 lowers a COMPUTE division to scale
  max(divisor scale, dmax) (+1 only for a ROUNDED receiver with divExtraForRounded) with mode .truncation; :359-363 dmax =
  receivers' scales and dScales (operands outside divisors) = 2 here; :236-237 and :250-251 a receiver without ROUNDED gets
  mode .truncation. Cobol/Sem/Arith.lean:58-60 quot rounds the exact quotient to that scale by divRoundZ; :259-268
  newValue (.giving) rescales into the receiver with its mode. Cobol/Round.lean:53 .truncation rounds toward zero; :66-67
  divRoundZ; :76-77 rescale (exact when the scale does not drop, as here: 2 to 2). So the model stores trunc_2(q).
- IBM side (assumption, as the session states): the intermediate quotient carries 4 places and its extra digits are
  truncated (the manuals give the places carried but say "truncated" explicitly only in DIVIDE's REMAINDER rule), and the
  store into the V99 receiver without ROUNDED truncates. Under that reading IBM stores trunc_2(trunc_4(q)) = trunc_2(q).
  The size-error check and high-order truncation act on the same integer part.

## 3. The session's probes (probes/): PASS
- 2306Z front end (--profile gnucobol --main) and cobolrun, both only read; fe.json hashes equal the session's
  (dprobe1 738b588fa60ff6c1, allprobe1 1d18784882d4a577). GnuCOBOL 3.2 via the snapshot's scripts/cobc.sh.
- dprobe1 (model | GnuCOBOL -std=ibm | -std=default): F3 D3 "2.00" | "2.50" | "2.50"; F1 D1 "001" | "000" | "001";
  F2 D2 "FALSE" | "TRUE" | "TRUE"; D5 (small literal power) "337" | "337" | "33.7".
- allprobe1 (G): A01 N | Y | Y; A02 Y | Y | Y; A03 N | Y | Y; A04 N | N | N.
- So F1, F2, F3 and G are present at the version of the migration theorems, as reported.

## What rests on the session or on IBM's text
- IBM's places rule for division and the 30-digit and integer-function rules are the session's reading of the Enterprise
  COBOL Programming Guide; that IBM truncates the extra intermediate places is an assumption (section 2).
- NIST exposure (NC252A, NC250A, the F4/F6 statements) and the CardDemo programs without front-end JSON were not scanned here.

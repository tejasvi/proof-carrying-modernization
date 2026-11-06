#!/usr/bin/env python3
"""Differential testing of ROUNDED and ROUNDED MODE IS m on COMPUTE, ADD, SUBTRACT, MULTIPLY and
DIVIDE (INTO, BY ... GIVING), for the seven modes GnuCOBOL 3.2 implements: AWAY-FROM-ZERO,
NEAREST-AWAY-FROM-ZERO (plain ROUNDED), NEAREST-EVEN, NEAREST-TOWARD-ZERO, TOWARD-GREATER,
TOWARD-LESSER, TRUNCATION.

ROUNDED MODE IS PROHIBITED (where PREREG_M set 2 survivor #11, Cobol/Sem/Arith.lean quotExact,
sits) is not compared with GnuCOBOL: GnuCOBOL 3.2 raises the size error condition on every
PROHIBITED statement, exact results included (12 / 3, 12.00 * 3; probes/p1bprohib.cob), where the
standard (and coblean) store an exactly representable result. cov_f3prohib.py checks PROHIBITED
against an exact-rational oracle instead.

Each random program runs K statements. Before each, the operands D2 (PIC S9(4)V99) and D3 (PIC
S9(3)V999) get values biased to ties at the receivers' scales (.x5, .xx5, .125, .5, ...),
positive and negative, and the receiver its starting value. Receivers: R0 (S9(5)), R1 (S9(4)V9),
R2 (S9(3)V99), U1 (9(4)V9, unsigned). Literal divisors and factors: 2, 4, 8, 3, 7, 0.5, 1.25. Every
statement has ON SIZE ERROR, and NOT ON SIZE ERROR half the time; the receiver (through PIC
-9(5).9(4)) and the phrase that ran are displayed after each statement. GnuCOBOL with difftest's
TRUNC(STD) flags and the front end with its TRUNC(STD) options (div-scale 30).

usage: cov_f3round.py --root C --out DIR [--n N] [--seed S] [--k K]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cov_common as E  # noqa: E402

MODES = ["AWAY-FROM-ZERO", "NEAREST-AWAY-FROM-ZERO", "NEAREST-EVEN", "NEAREST-TOWARD-ZERO",
         "TOWARD-GREATER", "TOWARD-LESSER", "TRUNCATION"]
RCV = {"R0": (5, 0), "R1": (4, 1), "R2": (3, 2), "U1": (4, 1)}
LITS = ["2", "4", "8", "3", "7", "0.5", "1.25"]
F2 = [".05", ".15", ".25", ".50", ".55", ".95", ".45", ".35"]
F3 = [".005", ".125", ".250", ".375", ".500", ".625", ".995", ".045", ".355"]


def val(rng, ip, fr, rnd_digits):
    i = rng.randint(0, 10 ** ip - 1) if rng.random() < 0.7 else rng.randint(0, 9)
    f = rng.choice(fr) if rng.random() < 0.7 else "." + "".join(rng.choice("0123456789") for _ in range(rnd_digits))
    s = "-" if rng.random() < 0.4 else ""
    return f"{s}{i}{f}"


def rounded(rng):
    r = rng.random()
    if r < 0.15:
        return "ROUNDED"
    return f"ROUNDED MODE IS {rng.choice(MODES)}"


def statement(rng, i):
    rv = rng.choice(list(RCV))
    out = [f"MOVE {val(rng, 4, F2, 2)} TO D2", f"MOVE {val(rng, 3, F3, 3)} TO D3",
           f"MOVE {val(rng, 2, F2, 2)} TO {rv}", "MOVE ' ' TO F"]
    ro = rounded(rng)
    form = rng.randint(1, 7)
    lit = rng.choice(LITS)
    if form == 1:
        expr = rng.choice(["D2 + D3", "D2 - D3", "D2 * D3", f"D2 / {lit}", f"D3 / {lit}",
                           f"D2 * {lit}", f"(D2 + D3) / {lit}"])
        s = f"COMPUTE {rv} {ro} = {expr}"
        end = "END-COMPUTE"
    elif form == 2:
        s = f"ADD {rng.choice(['D2', 'D3'])} TO {rv} {ro}"
        end = "END-ADD"
    elif form == 3:
        s = f"ADD D2 D3 GIVING {rv} {ro}"
        end = "END-ADD"
    elif form == 4:
        s = f"DIVIDE {lit} INTO {rv} {ro}"
        end = "END-DIVIDE"
    elif form == 5:
        s = f"DIVIDE {rng.choice(['D2', 'D3'])} BY {lit} GIVING {rv} {ro}"
        end = "END-DIVIDE"
    elif form == 6:
        s = f"SUBTRACT D3 FROM D2 GIVING {rv} {ro}"
        end = "END-SUBTRACT"
    else:
        s = f"MULTIPLY D2 BY {rng.choice(['D3', lit])} GIVING {rv} {ro}"
        end = "END-MULTIPLY"
    s += " ON SIZE ERROR MOVE 'E' TO F"
    if rng.random() < 0.5:
        s += " NOT ON SIZE ERROR MOVE 'K' TO F"
    s += " " + end
    lines = ["           " + x for x in out] + E.wrap(s)
    lines += [f"           MOVE {rv} TO E", f"           DISPLAY 'C{i:02d} ' E ' ' F '|'"]
    return lines


def program(rng, k):
    L = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. COVF3.",
         "       DATA DIVISION.", "       WORKING-STORAGE SECTION.",
         "       01  D2 PIC S9(4)V99 VALUE 0.", "       01  D3 PIC S9(3)V999 VALUE 0.",
         "       01  R0 PIC S9(5) VALUE 0.", "       01  R1 PIC S9(4)V9 VALUE 0.",
         "       01  R2 PIC S9(3)V99 VALUE 0.", "       01  U1 PIC 9(4)V9 VALUE 0.",
         "       01  E PIC -9(5).9(4).", "       01  F PIC X VALUE ' '.",
         "       PROCEDURE DIVISION."]
    for i in range(k):
        L += statement(rng, i)
    L.append("           STOP RUN.")
    return "\n".join(L) + "\n"


def main():
    ap = E.arg_parser(__doc__, 60, 15)
    args = ap.parse_args()
    E.main_loop(args, program, E.ARITH_COBC, E.ARITH_FE)


if __name__ == "__main__":
    main()

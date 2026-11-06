#!/usr/bin/env python3
"""Differential testing of the numeric intrinsic functions FACTORIAL, SUM, RANGE and LENGTH.

Each random program runs K random statements; every result is displayed, ending with '|':
  * COMPUTE FR = FUNCTION FACTORIAL (0 to 28: a literal or the item F1), FR PIC 9(30);
  * COMPUTE R = FUNCTION SUM / RANGE of 1 to 5 arguments (integer and decimal items, table
    elements, positive and negative literals of mixed scales, sums of an item and a literal),
    alone or added to / subtracted from another function; R PIC S9(12)V9(6), shown through the
    numeric-edited E;
  * COMPUTE N = sums of FUNCTION LENGTH of items (alphanumeric, numeric DISPLAY, COMP-3, group,
    table element) and of literals;
  * IF with a function on each side of a relation.
GnuCOBOL (difftest.py's TRUNC(STD) flags) and the front end + cobolrun (its TRUNC(STD) options)
must agree on every line (ext_common.py).

usage: fntest_num.py --root C --out DIR [--n N] [--seed S] [--k K]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402

ITEMS = {"I1": 0, "I2": 0, "X1": 2, "X2": 3}
LEN_ITEMS = ["A1", "G1", "G1A", "G1B", "T1(2)", "I1", "X2"]


def lit(rng):
    s = rng.choice([0, 0, 1, 2, 3])
    v = rng.randint(0, 99999) if rng.random() < 0.7 else rng.randint(0, 999)
    sign = "-" if rng.random() < 0.4 and v != 0 else ""
    if s == 0:
        return f"{sign}{v}"
    a = str(v).rjust(s + 1, "0")
    return f"{sign}{a[:-s]}.{a[-s:]}"


def arg(rng):
    r = rng.random()
    if r < 0.35:
        return rng.choice(list(ITEMS))
    if r < 0.45:
        return f"T1({rng.randint(1, 4)})"
    if r < 0.55:
        return f"{rng.choice(list(ITEMS))} + {lit(rng).lstrip('-')}"
    return lit(rng)


def sumrange(rng):
    f = rng.choice(["SUM", "RANGE"])
    n = rng.choice([1, 2, 3, 4, 5])
    return f"FUNCTION {f}(" + ", ".join(arg(rng) for _ in range(n)) + ")"


def setup(rng):
    out = []
    for name, s in ITEMS.items():
        v = rng.randint(-99999, 99999)
        sign = "-" if v < 0 else ""
        a = str(abs(v)).rjust(s + 1, "0")
        txt = f"{sign}{a}" if s == 0 else f"{sign}{a[:-s]}.{a[-s:]}"
        out.append(f"           MOVE {txt} TO {name}")
    for i in range(1, 5):
        out.append(f"           MOVE {rng.randint(0, 999)} TO T1({i})")
    out.append(f"           MOVE {rng.randint(0, 28)} TO F1")
    return out


def stmt(rng, i):
    r = rng.random()
    if r < 0.2:
        a = rng.choice(["F1", str(rng.randint(0, 28))])
        return E.wrap(f"COMPUTE FR = FUNCTION FACTORIAL({a})") + [f"           DISPLAY 'F{i:02d} ' FR '|'"]
    if r < 0.6:
        e = sumrange(rng)
        if rng.random() < 0.3:
            op = rng.choice(["+", "-"])
            other = sumrange(rng) if rng.random() < 0.6 else f"FUNCTION FACTORIAL({rng.randint(0, 12)})"
            e = f"{e} {op} {other}"
        return E.wrap(f"COMPUTE R = {e}") + ["           MOVE R TO E", f"           DISPLAY 'S{i:02d} ' E '|'"]
    if r < 0.8:
        parts = []
        for _ in range(rng.choice([1, 2, 3])):
            if rng.random() < 0.6:
                parts.append(f"FUNCTION LENGTH({rng.choice(LEN_ITEMS)})")
            else:
                parts.append(f"FUNCTION LENGTH('{'X' * rng.randint(1, 12)}')")
        return E.wrap("COMPUTE N = " + " + ".join(parts)) + [f"           DISPLAY 'L{i:02d} ' N '|'"]
    op = rng.choice(["=", ">", "<", ">=", "<="])
    return E.wrap(f"IF {sumrange(rng)} {op} {sumrange(rng)}") + [
        f"              DISPLAY 'C{i:02d} Y|'", "           ELSE", f"              DISPLAY 'C{i:02d} N|'",
        "           END-IF"]


def program(rng, k):
    data = ["       01  I1 PIC S9(5).", "       01  I2 PIC S9(5).",
            "       01  X1 PIC S9(4)V99.", "       01  X2 PIC S9(3)V9(3).",
            "       01  F1 PIC 99.", "       01  A1 PIC X(7).",
            "       01  G1.", "           05  G1A PIC X(3).", "           05  G1B PIC S9(5) COMP-3.",
            "       01  TB.", "           05  T1 PIC 9(3) OCCURS 4.",
            "       01  R PIC S9(12)V9(6).", "       01  E PIC -(12)9.9(6).",
            "       01  N PIC 9(4).", "       01  FR PIC 9(30)."]
    lines = E.header("FNNUM", data)
    for i in range(k):
        lines += setup(rng)
        lines += stmt(rng, i)
    lines.append("           STOP RUN.")
    return "\n".join(E.check_lines(lines)) + "\n"


def main():
    args = E.arg_parser(__doc__, 60, 20).parse_args()
    E.main_loop(args, program, E.ARITH_COBC, E.ARITH_FE)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Differential testing of the integer date functions INTEGER-OF-DATE, DATE-OF-INTEGER,
INTEGER-OF-DAY and DAY-OF-INTEGER (integer dates: 1601-01-01 is day 1).

Each random program runs K random statements; every result is displayed, ending with '|'.
Arguments are literals or items (D8 PIC 9(8) YYYYMMDD, D7 PIC 9(7) YYYYDDD, N7 PIC 9(7)),
always inside the functions' domains: valid dates from 1601-01-01 to 9999-12-31, with extra
weight on edges (January 1, December 31, February 28 and 29, the century years 1700, 1800,
1900, 2000, 2100, 2400, and the first and last days 1601-01-01 and 9999-12-31), integer dates
from 1 to 3067671. Statements:
  * COMPUTE R = one function of its argument;
  * COMPUTE R = FUNCTION DATE-OF-INTEGER / DAY-OF-INTEGER (FUNCTION INTEGER-OF-DATE (D8) + K)
    with a small K that keeps the sum in range, and differences of two integer dates;
  * IF comparing a function value with an item.
R PIC S9(9), shown through the edited item E. GnuCOBOL (difftest.py's TRUNC(STD) flags) and the
front end + cobolrun must agree on every line (ext_common.py).

usage: fntest_date.py --root C --out DIR [--n N] [--seed S] [--k K]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402

MAXINT = 3067671


def leap(y):
    return y % 4 == 0 and (y % 100 != 0 or y % 400 == 0)


def mdays(y, m):
    return [31, 29 if leap(y) else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m - 1]


def rand_year(rng):
    r = rng.random()
    if r < 0.25:
        return rng.choice([1601, 1700, 1800, 1900, 2000, 2004, 2100, 2400, 9999, 1604, 1996])
    return rng.randint(1601, 9999)


def rand_date(rng):
    y = rand_year(rng)
    r = rng.random()
    if r < 0.15:
        m, d = 2, mdays(y, 2)
    elif r < 0.25:
        m, d = rng.choice([(1, 1), (12, 31), (3, 1)])
    else:
        m = rng.randint(1, 12)
        d = rng.randint(1, mdays(y, m))
    return y * 10000 + m * 100 + d


def rand_day(rng):
    y = rand_year(rng)
    n = 366 if leap(y) else 365
    d = rng.choice([1, n, 59, 60]) if rng.random() < 0.3 else rng.randint(1, n)
    return y * 1000 + d


def rand_int(rng):
    if rng.random() < 0.2:
        return rng.choice([1, 2, 365, 366, 36524, 36525, 146097, MAXINT, MAXINT - 1])
    return rng.randint(1, MAXINT)


def setup(rng):
    return [f"           MOVE {rand_date(rng)} TO D8", f"           MOVE {rand_day(rng)} TO D7",
            f"           MOVE {rand_int(rng)} TO N7", f"           MOVE {rng.randint(-400, 400)} TO K"]


def one(rng):
    f = rng.choice(["INTEGER-OF-DATE", "DATE-OF-INTEGER", "INTEGER-OF-DAY", "DAY-OF-INTEGER"])
    if f == "INTEGER-OF-DATE":
        a = "D8" if rng.random() < 0.5 else str(rand_date(rng))
    elif f == "INTEGER-OF-DAY":
        a = "D7" if rng.random() < 0.5 else str(rand_day(rng))
    else:
        a = "N7" if rng.random() < 0.5 else str(rand_int(rng))
    return f"FUNCTION {f}({a})"


def stmt(rng, i):
    r = rng.random()
    if r < 0.55:
        e = one(rng)
    elif r < 0.75:
        # D8 is at least 1601-01-01 + 400 days and at most 9999-12-31 - 400 days here
        f = rng.choice(["DATE-OF-INTEGER", "DAY-OF-INTEGER"])
        e = f"FUNCTION {f}(FUNCTION INTEGER-OF-DATE(D8S) + K)"
    elif r < 0.85:
        e = f"FUNCTION INTEGER-OF-DATE(D8) - FUNCTION INTEGER-OF-DAY(D7)"
    else:
        op = rng.choice(["=", ">", "<", ">=", "<="])
        return E.wrap(f"IF {one(rng)} {op} N7") + [
            f"              DISPLAY 'C{i:02d} Y|'", "           ELSE", f"              DISPLAY 'C{i:02d} N|'",
            "           END-IF"]
    return E.wrap(f"COMPUTE R = {e}") + ["           MOVE R TO E", f"           DISPLAY 'D{i:02d} ' E '|'"]


def safe_date(rng):
    while True:
        d = rand_date(rng)
        y = d // 10000
        if 1603 <= y <= 9997:
            return d


def program(rng, k):
    data = ["       01  D8 PIC 9(8).", "       01  D8S PIC 9(8).", "       01  D7 PIC 9(7).",
            "       01  N7 PIC 9(7).", "       01  K PIC S9(5).",
            "       01  R PIC S9(9).", "       01  E PIC -(9)9."]
    lines = E.header("FNDATE", data)
    for i in range(k):
        lines += setup(rng)
        lines.append(f"           MOVE {safe_date(rng)} TO D8S")
        lines += stmt(rng, i)
    lines.append("           STOP RUN.")
    return "\n".join(E.check_lines(lines)) + "\n"


def main():
    args = E.arg_parser(__doc__, 60, 20).parse_args()
    E.main_loop(args, program, E.ARITH_COBC, E.ARITH_FE)


if __name__ == "__main__":
    main()

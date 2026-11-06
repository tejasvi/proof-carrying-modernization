#!/usr/bin/env python3
"""Differential testing of the alphanumeric intrinsic functions UPPER-CASE, LOWER-CASE and
REVERSE, and of FUNCTION WHEN-COMPILED.

Each random program runs K random statements; every result is displayed, ending with '|'.
Texts are drawn from letters of both cases, digits, space and punctuation. Arguments: the
items A1 PIC X(10), A2 PIC X(6), A3 PIC A(8) (alphabetic), reference-modified items, literals,
and one function nested in another. Statements:
  * MOVE FUNCTION f (arg) TO a receiver that is shorter, as long or longer (truncation and space
    padding), then DISPLAY it;
  * DISPLAY FUNCTION f (arg) directly;
  * COMPUTE N = FUNCTION LENGTH (FUNCTION f (arg)) + 1 (arguments without reference modification);
  * IF comparing a function with an item, a literal or another function (the comparison pads
    the shorter operand with spaces);
  * WHEN-COMPILED: MOVE it to W PIC X(21), compare FUNCTION WHEN-COMPILED with W, and display
    FUNCTION LENGTH (FUNCTION WHEN-COMPILED) and W (1:2). Its value is the compilation time of
    each system, so only these value-independent facts are compared.
GnuCOBOL (-std=ibm) and the front end + cobolrun (--profile gnucobol, ASCII) must agree on every
line (ext_common.py). The EBCDIC case mapping (IBM profile) is not exercised here.

usage: fntest_alnum.py --root C --out DIR [--n N] [--seed S] [--k K]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402

CHARS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 -.,;:/*+"
ALPHA = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ  "
SRC = {"A1": 10, "A2": 6, "A3": 8}
RCV = {"B1": 10, "B2": 4, "B3": 16}
FNS = ["UPPER-CASE", "LOWER-CASE", "REVERSE"]


def text(rng, n, chars=CHARS):
    return "".join(rng.choice(chars) for _ in range(n))


def arg(rng, depth=0):
    r = rng.random()
    if r < 0.45:
        return rng.choice(list(SRC))
    if r < 0.6:
        name = rng.choice(list(SRC))
        s = rng.randint(1, SRC[name])
        return f"{name}({s}:{rng.randint(1, SRC[name] - s + 1)})"
    if r < 0.85 or depth > 0:
        return f"'{text(rng, rng.randint(1, 12))}'"
    return fn(rng, depth + 1)


def fn(rng, depth=0):
    return f"FUNCTION {rng.choice(FNS)}({arg(rng, depth)})"


def fn_plain(rng, depth=0):
    """A function whose arguments have no reference modification (for FUNCTION LENGTH)."""
    r = rng.random()
    a = rng.choice(list(SRC)) if r < 0.5 else (f"'{text(rng, rng.randint(1, 12))}'" if r < 0.85 or depth
                                                 else fn_plain(rng, depth + 1))
    return f"FUNCTION {rng.choice(FNS)}({a})"


def setup(rng):
    return [f"           MOVE '{text(rng, SRC['A1'])}' TO A1", f"           MOVE '{text(rng, SRC['A2'])}' TO A2",
            f"           MOVE '{text(rng, SRC['A3'], ALPHA)}' TO A3"]


def stmt(rng, i):
    r = rng.random()
    if r < 0.35:
        b = rng.choice(list(RCV))
        return E.wrap(f"MOVE {fn(rng)} TO {b}") + [f"           DISPLAY 'M{i:02d} ' {b} '|'"]
    if r < 0.5:
        return E.wrap(f"DISPLAY 'D{i:02d} ' {fn(rng)} '|'")
    if r < 0.62:
        return E.wrap(f"COMPUTE N = FUNCTION LENGTH({fn_plain(rng)}) + 1") + [
            f"           DISPLAY 'N{i:02d} ' N '|'"]
    if r < 0.85:
        other = rng.choice([fn(rng), rng.choice(list(SRC)), f"'{text(rng, rng.randint(1, 10))}'"])
        op = rng.choice(["=", "<>", "<", ">", "<=", ">="])
        return E.wrap(f"IF {fn(rng)} {op} {other}") + [
            f"              DISPLAY 'C{i:02d} Y|'", "           ELSE", f"              DISPLAY 'C{i:02d} N|'",
            "           END-IF"]
    return ["           MOVE FUNCTION WHEN-COMPILED TO W",
            "           IF FUNCTION WHEN-COMPILED = W",
            f"              DISPLAY 'W{i:02d} EQ|'", "           ELSE", f"              DISPLAY 'W{i:02d} NE|'",
            "           END-IF",
            "           COMPUTE N = FUNCTION LENGTH(FUNCTION WHEN-COMPILED)",
            f"           DISPLAY 'L{i:02d} ' N ' ' W(1:2) '|'"]


def program(rng, k):
    data = ["       01  A1 PIC X(10).", "       01  A2 PIC X(6).", "       01  A3 PIC A(8).",
            "       01  B1 PIC X(10).", "       01  B2 PIC X(4).", "       01  B3 PIC X(16).",
            "       01  W PIC X(21).", "       01  N PIC 99."]
    lines = E.header("FNALNUM", data)
    for i in range(k):
        lines += setup(rng)
        lines += stmt(rng, i)
    lines.append("           STOP RUN.")
    return "\n".join(E.check_lines(lines)) + "\n"


def main():
    args = E.arg_parser(__doc__, 60, 20).parse_args()
    E.main_loop(args, program, E.PLAIN_COBC, E.PLAIN_FE)


if __name__ == "__main__":
    main()

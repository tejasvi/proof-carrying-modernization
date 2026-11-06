#!/usr/bin/env python3
"""Differential testing of fixed-point intermediate results that can need more than 30 digits.

IBM Enterprise COBOL 6.4 Programming Guide, "Fixed-point data and intermediate results": the
precision of an intermediate result ir is "+ or - (i1 or i2) + 1, whichever is greater | d1 or d2,
whichever is greater", "* i1 + i2 | d1 + d2", "/ i2 + d1 | (d2 - d1) or dmax, whichever is
greater" (op1 the divisor); in compatibility mode (ARITH(COMPAT)) "the number of places the compiler
carries" is: i + d <= 30: i integer and d decimal places; i + d > 30 and d <= dmax: 30-d integer and
d decimal places; d > dmax and i + dmax <= 30: i integer and 30-i decimal places; d > dmax and
i + dmax > 30: 30-dmax integer and dmax decimal places. "Truncated intermediate results": "the
compiler truncates to 30 ... digits and issues a warning. If truncation occurs at run time, a
message is issued and the program continues running"; z/OS LE message IGZ0036W: "The generated code
has truncated an intermediate result ... to 30 digits; some of the truncated digits were not 0."
("Truncation of high order digit positions"). Intermediate results exist (PG "Intermediate results
and arithmetic precision") in a COMPUTE with a series of operations (each one but the last, whose
result is the final result: "Add ir5 to ir1 yielding Y"), with several result fields or ROUNDED
(then the final result too), in a condition (every operation), for a function's steps and result,
and for MULTIPLY / DIVIDE GIVING with several result fields. ROUNDED: "one more integer [decimal]
place might be carried for accuracy if necessary" (Terminology used for intermediate results).

The model (ar2-fix, Resolve.cap30 / Expr.ir30 / Expr.ir30open): an intermediate result over 30
digits is truncated to IBM's carried decimal places; a nonzero integer digit beyond its carried
integer places stops the run with `unsupported` (IGZ0036W, not modelled); where IBM's text leaves
the places open (ROUNDED with an intermediate result of more than 28 digits that is not d <= dmax)
the run stops with `unsupported` ("places carried open").

Each random program sets its operand items (16 to 18 digit PICTUREs, integer and decimal, DISPLAY
and COMP-3, signed and unsigned) by MOVE before every step and runs K steps:
  * COMPUTE R = an expression with intermediate results of 31 to 36 digits (products of large
    items, a product times / plus / minus an item, a product of products, sums of products, a
    quotient of a product, a product of a quotient) into one receiver (the final result is no
    intermediate result) or two (it is), ROUNDED in some steps;
  * COMPUTE R = (A * B) * C, A and B decimal items with a few integer digits and every decimal
    place used, C a moderate integer, into a receiver with 4, 6 or 9 places, values drawn until
    IBM's cut of the product's decimal places shows in the receiver;
  * IF relations whose comparands are such expressions;
  * MULTIPLY A BY B GIVING R1 R2 (the product is an intermediate result);
  * COMPUTE R = FUNCTION REM (FUNCTION REM (A, B), C) and FUNCTION SUM of large items (the steps of
    the functions are intermediate results; IF133A F-REM-TEST-14 has the first shape);
  * a third of the programs end with a step whose intermediate result IBM cuts with a nonzero digit
    (IGZ0036W) or, under ROUNDED, whose places IBM leaves open: the model must stop there with the
    corresponding `unsupported` signal (ok-stop).
Receivers have 0, 2, 4, 6 or 9 places; ON SIZE ERROR / NOT ON SIZE ERROR in most steps (always
where the final result overflows the receiver); receivers are displayed through numeric-edited items.

Part powlit (--part powlit): powers by a literal exponent (PG, same page, exponentiation: "When op2
is an integral literal or constant, the value d is computed as d = d1 * |op2| and the value i is
computed based on the characteristics of op1: When op1 is a data-name or variable, i = i1 * |op2|.
When op1 is a literal or constant, i is set equal to the number of integers in the value of
op1 ** |op2|"; in compatibility mode, i + d < 30: "i integer and d decimal places are carried for
ir"; i + d = 30 and "op1 has an odd number of digits": the same; i + d = 30 and an even number of
digits, or i + d > 30: "Same action as when op2 is an integral data-name or variable", that is
"dmax decimal places and 30-dmax ... integer places are used"). The model (the power arm of
Resolve.capW): the power exact, or held with dmax places (Expr.powInt; beyond 30 digits the run
stops with `unsupported`, IBM truncates there with a message); under ROUNDED a power of 28 or more
digits, and a power whose row of the table depends on an open point, stop the run with
`unsupported` ("power by a literal ..., places carried open"). Each program runs K steps: COMPUTE
R = a power of an item (5 to 18 digits, an odd or even number, DISPLAY and COMP-3), of a literal
(1.5, 1.01, 12.5, 2, 3) or of a sum of two items, by exponents chosen around 30 digits, alone,
times an item or literal, plus or minus an item, divided by an item, or plus another power, into
one or two receivers, ROUNDED in some steps; COMPUTE R = such a power times an item or literal,
values drawn until IBM's cut of the power's decimal places shows in the receiver; IF relations
with such powers, and IF a power = (or NOT =) a literal that holds IBM's value of it, values drawn
until the cut shows; a third of the programs end with a step whose power held with dmax places
exceeds 30 digits (cutpow) or, under ROUNDED, has 28 or more digits (openpow, half of them 28 or
29): the model must stop there with the corresponding `unsupported` signal (ok-stop).

Part pow0 (--part pow0): powers by the literal exponent 0 (Language Reference, "Arithmetic
expressions": "If the value of an expression to be raised to a power is zero, the exponent must
have a value greater than zero. Otherwise, the size error condition exists"; "SIZE ERROR phrases",
zero raised to zero power: "The SIZE ERROR imperative is executed" when a SIZE ERROR clause is
present, otherwise "The value returned is 1, and a message is issued"; with ON SIZE ERROR "the
value of the resultant identifier affected by the size error is not altered", without it "the
value of the affected resultant identifier is computed", and NOT ON SIZE ERROR runs when "a size
error condition does not exist"). The model (Expr.pow0): the base evaluated, the value 1; a zero
base in a COMPUTE with ON SIZE ERROR is its size error, under NOT ON SIZE ERROR alone it is
unsupported (the phrase skipped while 1 is stored). Each program runs K steps: COMPUTE R = B ** 0
alone, plus an item, times 3 or subtracted from an item, B an item set to 0 in two fifths of the
steps, the literal 0, 7 or 1.5, a difference of an item and itself or a sum, into one or two
receivers, ROUNDED in some steps, ON SIZE ERROR in most, NOT ON SIZE ERROR alone in some (a nonzero
base: the phrase runs); IF relations with such a power; a third of the programs end with a zero
base under NOT ON SIZE ERROR alone: the model must stop there with the corresponding `unsupported`
signal (ok-stop). GnuCOBOL runs ON SIZE ERROR for a zero data base but stores 1 all the same
(G-pow00) and folds the literal 0 ** 0 to 1 with no size error (G-litpow00).

Part c30 (--part c30): the composite of operands (Language Reference, "Arithmetic statement
operands": "a hypothetical data item resulting from aligning the operands at the decimal point and
then superimposing them on one another", "If the ARITH(COMPAT) compiler option is in effect, the
composite of operands can be a maximum of 30 digits"; for ADD and SUBTRACT "all operands in a given
statement except those following the word GIVING", for MULTIPLY "all receiving data items", for
DIVIDE "all receiving data items except the REMAINDER data item"). The front end makes a statement
beyond 30 digits unsupported. Each program runs K steps of ADD ... TO, ADD ... GIVING, SUBTRACT ...
FROM, SUBTRACT ... FROM ... GIVING, MULTIPLY ... BY, MULTIPLY ... GIVING, DIVIDE ... INTO, DIVIDE
... GIVING with items of 2 to 18 digits whose integer and decimal places add up to 30 or more, and
literals (digits as written), one or two receivers, ON SIZE ERROR in most steps, composites of
at most 30 digits (30 in a third of the steps); a third of the programs end with a statement whose
composite exceeds 30 digits: the front end reports it and the model stops there (ok-stop). Every
model line equals GnuCOBOL's (the statements are exact there).

Checks (GnuCOBOL -std=ibm -fbinary-truncate -fno-arithmetic-osvs, which computes exactly; the front
end --profile gnucobol --trunc std, then cobolrun):
  * IBM mirror: every model line equals the line of the mirror program, which sets each receiver
    to the value the tester computes by IBM's rules (Fraction arithmetic: the table above, each
    division truncated to its places, the final result truncated or rounded into the receiver, a
    size error leaving it unchanged with ON SIZE ERROR and cut at the high end without), and
    displays the tester's outcome of each condition;
  * every model line equals GnuCOBOL's for the program itself, except the lines of steps where
    GnuCOBOL departs from IBM: G-ir30 (IBM's cut of an intermediate result changes the stored value
    or the condition: PG P02 of probe f4probe1, A9 * B9 * C8 with 9V9 x 9V9, i 18 + d 18 > 30, dmax 9:
    IBM 12 decimal places, 22330437.411120000; GnuCOBOL exact 22330437.411126352), G-exactdiv
    (GnuCOBOL's quotient keeps more places than IBM's "(d2 - d1) or dmax") and, in part powlit,
    G-powlit (IBM's dmax places of a power by a literal change its value; GnuCOBOL's power is exact)
    and G-litpow64 (GnuCOBOL folds an integer literal ** literal in 64-bit binary, wrapping from
    2 ** 63 on: COMPUTE X = 2 ** 64 / 1000 gives 0, 3 ** 40 / 100 gives 62890786146526228), and in
    part pow0 G-pow00 and G-litpow00 (above);
  * a program that ends with a stop step: the model's signal is the expected `unsupported` text
    and its lines equal the mirror's and GnuCOBOL's lines before that step (ok-stop).
Statuses: ok, ok-g, ok-stop, mismatch, mirror, stop-mismatch, and the ext_common statuses. Not
generated: division by zero, unary minus, binary items beyond their PICTURE, index names (their
places are left open by IBM's text; the model's choice is checked by the hand cases).
Never deletes files.

usage: ir30test.py --root C --out DIR [--part ir30|powlit|pow0|c30] [--n N] [--seed S] [--k K] [--show K]
       ir30test.py --root C --out DIR --run PROG.cob...
"""
import json
import os
import random
import subprocess
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402
from classtest import show  # noqa: E402

IR_COBC = E.ARITH_COBC
IR_FE = ["--profile", "gnucobol", "--trunc", "std"]
CUT_MSG = "intermediate result cut to 30 digits with a nonzero high-order digit (IGZ0036W)"
OPEN_MSG = "intermediate result over 30 digits, places carried open"
# part powlit: a power held with dmax places beyond 30 digits (Sem.powIntVal), a power whose places are open
CUTPOW_MSG = "exponentiation: intermediate result of more than 30 digits"
OPENPOW_MSG = "power by a literal"
# part pow0: a zero base raised to the literal power 0 under NOT ON SIZE ERROR alone (Expr.pow0)
POW0NOT_MSG = "zero raised to the literal power 0 under NOT ON SIZE ERROR without ON SIZE ERROR"
STOP_MSG = {"cut": CUT_MSG, "open": OPEN_MSG, "cutpow": CUTPOW_MSG, "openpow": OPENPOW_MSG, "pow0not": POW0NOT_MSG}

# operand items: name, PICTURE, integer places, decimal places, signed
ITEMS = [("L1", "S9(16)", 16, 0, True, ""), ("L2", "9(17)", 17, 0, False, ""),
         ("L3", "S9(18)", 18, 0, True, " COMP-3"), ("L4", "S9(15)", 15, 0, True, ""),
         ("F1", "S9(9)V9(9)", 9, 9, True, ""), ("F2", "9(14)V9(4)", 14, 4, False, ""),
         ("F3", "S9(4)V9(14)", 4, 14, True, ""), ("F4", "S9(12)V9(6)", 12, 6, True, " COMP-3"),
         ("F5", "S9(2)V9(16)", 2, 16, True, ""), ("F6", "S9(16)V99", 16, 2, True, ""),
         ("S1", "S9(3)V99", 3, 2, True, ""), ("S2", "99", 2, 0, False, "")]
# part powlit: more bases, with an even (10) and an odd (5) number of digits
POW_ITEMS = [("P10", "9(6)V9(4)", 6, 4, False, ""), ("P11", "9(5)V9(5)", 5, 5, False, " COMP-3"),
             ("P5", "9(3)V9(2)", 3, 2, False, "")]
# part c30: operands whose integer and decimal places add up to 30 digits or more, and their edited copies
C30_ITEMS = [("A16", "9(16)V99", 16, 2, False, ""), ("B16", "9(2)V9(16)", 2, 16, False, ""),
             ("C15", "9(15)V9(3)", 15, 3, False, ""), ("D15", "9(3)V9(15)", 3, 15, False, ""),
             ("E18", "9(18)", 18, 0, False, ""), ("F12", "9(6)V9(12)", 6, 12, False, ""),
             ("H14", "S9(14)V9(4)", 14, 4, True, " COMP-3"), ("K14", "S9(4)V9(14)", 4, 14, True, " COMP-3"),
             ("M5", "9(3)V99", 3, 2, False, ""), ("N2", "99", 2, 0, False, "")]
C30_EDIT = {"A16": "Z(15)9.99", "B16": "Z9.9(16)", "C15": "Z(14)9.9(3)", "D15": "ZZ9.9(15)", "E18": "Z(17)9",
            "F12": "Z(5)9.9(12)", "H14": "-(14)9.9(4)", "K14": "-(4)9.9(14)", "M5": "ZZ9.99", "N2": "Z9"}
C30_LITS = ["7", "2.5", "123456789012", "0.000001", "000000000000001"]
# part pow0: bases of a power by the literal 0 (items are set to 0 in two fifths of the steps), and the zero bases of
# the stop step (items set to 0)
POW0_BASES = [("item", "S1"), ("item", "S2"), ("item", "F1"), ("item", "L4"), ("item", "P5"), ("lit", "0"),
              ("lit", "7"), ("lit", "1.5"), ("sub", ("item", "S1"), ("item", "S1")), ("add", ("item", "S1"), ("item", "S2"))]
POW0_ZERO = [("item", "S1"), ("item", "S2"), ("item", "F1"), ("item", "L4"), ("item", "P5"), ("lit", "0"),
             ("sub", ("item", "S1"), ("item", "S1"))]
BY = {it[0]: it for it in ITEMS + POW_ITEMS + C30_ITEMS}
# receivers: name, PICTURE, integer places, decimal places, edited PICTURE
RCVS = [("R0", "S9(18)", 18, 0, "-(18)9"), ("R2", "S9(16)V99", 16, 2, "-(16)9.99"),
        ("R4", "S9(14)V9(4)", 14, 4, "-(14)9.9(4)"), ("R6", "S9(12)V9(6)", 12, 6, "-(12)9.9(6)"),
        ("R9", "S9(9)V9(9)", 9, 9, "-(9)9.9(9)")]
RBY = {r[0]: r for r in RCVS}
LITS = ["3", "7", "10", "1000", "0.5", "2.25", "999999999", "123456789012"]
# part powlit: bases and literal exponents around 30 digits (i + d = 30: S1 ** 6, L4 ** 2, P5 ** 6 and 12.5 ** 14 have an
# odd number of digits in the base, S2 ** 15, P10 ** 3, P11 ** 3 and 1.5 ** 25 an even one; around ROUNDED's 28:
# S2 ** 13 has 26 digits, 1.01 ** 13 27, S2 ** 14 28, 1.01 ** 14 29)
POWS = [("F1", [2]), ("F2", [2]), ("F3", [2]), ("F4", [2]), ("F5", [2]), ("F6", [2]), ("L1", [2]), ("L4", [2]),
        ("S1", [3, 5, 6]), ("S2", [8, 13, 14, 15, 16]), ("P10", [2, 3]), ("P11", [2, 3]), ("P5", [5, 6, 7])]
POW_LITS = [("1.5", [20, 25, 26, 30, 40]), ("1.01", [10, 13, 14, 15, 20]), ("12.5", [9, 12, 14]), ("2", [40, 64]),
            ("3", [30, 40, 63])]
# the powers of 28 and 29 digits, where ROUNDED leaves the row open
POW_EDGE = [(("item", "S2"), 14), (("lit", "1.01"), 14)]


class Cut(Exception):
    """IBM cuts a nonzero integer digit of an intermediate result (IGZ0036W)."""


class Open(Exception):
    """IBM's text leaves the places carried open (the model: unsupported)."""


class CutPow(Exception):
    """A power by a literal held with dmax places as for an integral data-name exponent has more than 30 digits."""


class OpenPow(Exception):
    """A power by a literal whose places IBM's text leaves open (the model: unsupported)."""


class SizeErr(Exception):
    """Zero raised to the literal power 0 in a statement with ON SIZE ERROR: the statement's size error."""


def trunc(v, k):
    """The rational v truncated toward zero to k decimal places."""
    s = 10 ** k
    q = abs(v.numerator) * s // v.denominator
    return Fraction(q if v >= 0 else -q, s)


def round_half_away(v, k):
    s = 10 ** k
    q = (2 * abs(v.numerator) * s + v.denominator) // (2 * v.denominator)
    return Fraction(q if v >= 0 else -q, s)


def ndig(n):
    return len(str(n)) if n else 0


def lit_places(text):
    """(integer places by value, decimal places as written) of a literal."""
    d = len(text.split(".")[1]) if "." in text else 0
    v = Fraction(text)
    return ndig(abs(v.numerator) // v.denominator), d


class P:
    """IBM's places of an intermediate result as ranges (Resolve.Places)."""

    def __init__(self, ilo, ihi, dlo, dhi):
        self.ilo, self.ihi, self.dlo, self.dhi = ilo, ihi, dlo, dhi

    @staticmethod
    def exact(i, d):
        return P(i, i, d, d)


def p_add(a, b):
    return P(max(a.ilo, b.ilo) + 1, max(a.ihi, b.ihi) + 1, max(a.dlo, b.dlo), max(a.dhi, b.dhi))


def p_mul(a, b):
    return P(a.ilo + b.ilo, a.ihi + b.ihi, a.dlo + b.dlo, a.dhi + b.dhi)


def lit_vs(text):
    """The front end's numeric literal: (its digits as written as an integer, its decimal places as written)."""
    d = len(text.split(".")[1]) if "." in text else 0
    return int(text.replace(".", "").lstrip("-") or "0"), d


def pow_places(pa, lit, dg, n):
    """Resolve.powPlaces: IBM's places of op1 ** n (op1 of places pa, or the literal lit) and how they are carried:
    "exact", "name" (dmax decimal places as for an integral data-name exponent) or None (open); dg: the candidates
    for the number of digits of op1."""
    if lit is not None:
        v, s = lit_vs(lit)
        p = P.exact(ndig(v ** n // (10 ** (s * n))), max(0, s * n))
    else:
        p = P(pa.ilo * n, pa.ihi * n, pa.dlo * n, pa.dhi * n)
    if p.ihi + p.dhi < 30:
        return p, "exact"
    if 30 < p.ilo + p.dlo:
        return p, "name"
    if p.ilo + p.dlo == 30 and p.ihi + p.dhi == 30:
        if n == 1 and p.dhi == 0 and all(g == 30 for g in dg):
            return p, "exact"
        if all(g % 2 == 1 for g in dg):
            return p, "exact"
        if all(g % 2 == 0 for g in dg):
            return p, "name"
    return p, None


class Env:
    def __init__(self, mlo, mhi, rounded):
        self.mlo, self.mhi, self.rounded = mlo, mhi, rounded


def carry(env, role, p, v, scale, info):
    """IBM's places carried (Resolve.carry30) applied to the value v (at the model scale `scale`):
    (value, places, scale). Raises Cut / Open; info["cap"] collects the rows used."""
    if role == "final":
        return v, p, scale
    if env.rounded:
        p = P(p.ilo, p.ihi + 1, p.dlo, p.dhi + 1)
    if p.ihi + p.dhi <= 30:
        return v, p, scale
    if p.dhi <= env.mlo:
        info["cap"].add("row2")
        k = 30 - p.dhi
        if abs(v) >= Fraction(10) ** k:
            raise Cut()
        return v, P(min(p.ilo, 30 - p.dhi), min(p.ihi, 30 - p.dlo), p.dlo, p.dhi), scale
    if role == "ir" and not env.rounded and env.mhi < p.dlo and 30 < p.ilo + p.dlo:
        if p.ilo == p.ihi and p.ihi + env.mhi <= 30:
            info["cap"].add("row3")
            s = 30 - p.ilo
            w = trunc(v, s)
            if w != v:
                info["cut_lo"] = True
            if abs(w) >= Fraction(10) ** p.ilo:
                raise Cut()
            return w, P.exact(p.ilo, s), s
        if env.mlo == env.mhi and 30 < p.ilo + env.mlo:
            info["cap"].add("row4")
            s = env.mlo
            w = trunc(v, s)
            if w != v:
                info["cut_lo"] = True
            if abs(w) >= Fraction(10) ** (30 - s):
                raise Cut()
            return w, P.exact(30 - s, s), s
    raise Open()


class Expr:
    """("item", name), ("lit", text), ("add"|"sub"|"mul"|"div", a, b), ("rem", a, b), ("sum", [a...]),
    ("lpow", a, n): a ** n for the literal n."""

    @staticmethod
    def text(x):
        k = x[0]
        if k in ("item", "lit"):
            return x[1]
        if k in ("add", "sub", "mul", "div"):
            op = {"add": "+", "sub": "-", "mul": "*", "div": "/"}[k]
            return f"{Expr.wrapped(x[1])} {op} {Expr.wrapped(x[2])}"
        if k == "lpow":
            return f"{Expr.wrapped(x[1])} ** {x[2]}"
        if k == "rem":
            return f"FUNCTION REM ({Expr.text(x[1])}, {Expr.text(x[2])})"
        if k == "sum":
            return "FUNCTION SUM (" + " ".join(Expr.text(a) for a in x[1]) + ")"
        raise ValueError(x)

    @staticmethod
    def wrapped(x):
        t = Expr.text(x)
        return t if x[0] in ("item", "lit", "rem", "sum") else f"({t})"

    @staticmethod
    def dscales(x):
        """Resolve.dScales: decimal places of the leaves outside divisors."""
        k = x[0]
        if k == "item":
            return [BY[x[1]][3]]
        if k == "lit":
            return [lit_places(x[1])[1]]
        if k in ("add", "sub", "mul", "rem"):
            return Expr.dscales(x[1]) + Expr.dscales(x[2])
        if k in ("div", "lpow"):
            return Expr.dscales(x[1])
        if k == "sum":
            return [d for a in x[1] for d in Expr.dscales(a)]
        raise ValueError(x)

    @staticmethod
    def items(x, out):
        if x[0] == "item":
            out.add(x[1])
        elif x[0] == "sum":
            for a in x[1]:
                Expr.items(a, out)
        elif x[0] == "lpow":
            Expr.items(x[1], out)
        elif x[0] != "lit":
            Expr.items(x[1], out)
            Expr.items(x[2], out)
        return out


def env_arg(env, inner, a):
    """The dmax range of a function argument's operations (Resolve.capW, envA)."""
    own = max([0] + Expr.dscales(a))
    return Env(min(env.mlo, own, inner), max(env.mhi, own, inner), env.rounded)


def ev(x, vals, env, role, info, rounded_div):
    """IBM's value of x as the model carries it: (value, places, model scale)."""
    k = x[0]
    if k == "item":
        _, _, i, d, _, _ = BY[x[1]]
        return Fraction(vals[x[1]], 10 ** d), P.exact(i, d), d
    if k == "lit":
        i, d = lit_places(x[1])
        return Fraction(x[1]), P.exact(i, d), d
    if k in ("add", "sub", "mul"):
        va, pa, sa = ev(x[1], vals, env, "ir", info, rounded_div)
        vb, pb, sb = ev(x[2], vals, env, "ir", info, rounded_div)
        if k == "mul":
            return carry(env, role, p_mul(pa, pb), va * vb, sa + sb, info)
        v = va + vb if k == "add" else va - vb
        return carry(env, role, p_add(pa, pb), v, max(sa, sb), info)
    if k == "div":
        va, pa, sa = ev(x[1], vals, env, "ir", info, rounded_div)
        vb, pb, sb = ev(x[2], vals, env, "ir", info, rounded_div)
        # the model's quotient places: "(d2 - d1) or dmax" from the operands as carried, + 1 with ROUNDED
        sc = max(sa - sb, env.mlo) + (1 if rounded_div else 0)
        info["div"] = True
        q = trunc(va / vb, sc)
        if q != va / vb:
            info["div_inexact"] = True
        p = P(pa.ilo + pb.dlo, pa.ihi + pb.dhi, max(pa.dlo - pb.dhi, env.mlo), max(pa.dhi - pb.dlo, env.mhi))
        return carry(env, role, p, q, sc, info)
    if k == "lpow":
        # a power by the literal n, always an intermediate result (the power arm of Resolve.capW)
        a, n = x[1], x[2]
        va, pa, sa = ev(a, vals, env, "ir", info, rounded_div)
        if n == 0:
            # Expr.pow0: the base evaluated, the value 1; a zero base is the size error of a statement with
            # ON SIZE ERROR (env.trap)
            info.setdefault("pow", set()).add("zero")
            if va == 0:
                info["pow00"] = True
                if getattr(env, "trap", False):
                    raise SizeErr()
            return Fraction(1), P.exact(1, 0), 0
        lit = a[1] if a[0] == "lit" else None
        if lit is not None:
            dg = [ndig(lit_vs(lit)[0])]
        elif a[0] == "item":
            dg = [BY[a[1]][2] + BY[a[1]][3]]
        elif pa.ilo == pa.ihi and pa.dlo == pa.dhi:
            dg = [pa.ilo + pa.dlo]
        else:
            dg = [pa.ilo + pa.dlo, pa.ilo + pa.dlo + 1]
        p, how = pow_places(pa, lit, dg, n)
        info.setdefault("pow", set()).add(how or "open")
        if lit is not None and "." not in lit and abs(int(lit)) ** n >= 2 ** 63:
            # GnuCOBOL folds an integer literal ** literal in 64-bit binary, wrapping from 2 ** 63 on
            info["litpow64"] = True
        # ROUNDED: one more integer and decimal place "might be carried": from 28 digits on the row is open
        if env.rounded and 28 <= p.ihi + p.dhi:
            raise OpenPow()
        if how == "exact":
            return va ** n, p, sa * n
        if how == "name" and env.mlo == env.mhi:
            s = env.mlo
            w = trunc(va ** n, s)
            if w != va ** n:
                info["pow_lo"] = True
            if abs(w) >= Fraction(10) ** (30 - s):
                raise CutPow()
            return w, P.exact(30 - s, s), s
        raise OpenPow()
    if k == "rem":
        # FUNCTION REM: divide, remove noninteger digits, multiply, subtract (each an intermediate
        # result; an argument's operations with the statement's, the function's inner or the
        # argument's own dmax, the steps with the statement's or the function's inner dmax)
        info["fn"] = True
        inner = max(max([0] + Expr.dscales(x[1])), max([0] + Expr.dscales(x[2])))
        envf = Env(min(env.mlo, inner), max(env.mhi, inner), env.rounded)
        va, pa, sa = ev(x[1], vals, env_arg(env, inner, x[1]), "ir", info, False)
        vb, pb, sb = ev(x[2], vals, env_arg(env, inner, x[2]), "ir", info, False)
        pq = P(pa.ilo + pb.dlo, pa.ihi + pb.dhi, max(pa.dlo - pb.dhi, envf.mlo), max(pa.dhi - pb.dlo, envf.mhi))
        dq = max(0, pq.dhi)
        q = trunc(va / vb, dq)
        if envf.rounded:
            pq = P(pq.ilo, pq.ihi + 1, pq.dlo, pq.dhi + 1)
        if pq.ihi + pq.dhi > 30:
            kq = 30 - max(pq.dhi, envf.mhi)
            info["cap"].add("remq")
            if abs(q) >= Fraction(10) ** max(kq, 0):
                raise Cut()
            pq = P(min(pq.ilo, kq), pq.ihi, pq.dlo, pq.dhi)
        qi = trunc(q, 0)
        vp, pp, sp = carry(envf, "ir", P(pq.ilo + pb.ilo, pq.ihi + pb.ihi, pb.dlo, pb.dhi), qi * vb, sb, info)
        return carry(envf, "ir", p_add(pa, pp), va - vp, max(sa, sp), info)
    if k == "sum":
        info["fn"] = True
        inner = max([0] + [max([0] + Expr.dscales(a)) for a in x[1]])
        envf = Env(min(env.mlo, inner), max(env.mhi, inner), env.rounded)
        acc = None
        for a in x[1]:
            va, pa, sa = ev(a, vals, env_arg(env, inner, a), "ir", info, False)
            if acc is None:
                acc = carry(envf, "ir", p_add(P.exact(0, 0), pa), va, sa, info)
            else:
                v, p, s = acc
                acc = carry(envf, "ir", p_add(p, pa), v + va, max(s, sa), info)
        return acc
    raise ValueError(x)


def exact(x, vals):
    """The exact value (GnuCOBOL; its quotient keeps all places here)."""
    k = x[0]
    if k == "item":
        return Fraction(vals[x[1]], 10 ** BY[x[1]][3])
    if k == "lit":
        return Fraction(x[1])
    a = None if k == "sum" else exact(x[1], vals)
    if k == "add":
        return a + exact(x[2], vals)
    if k == "sub":
        return a - exact(x[2], vals)
    if k == "mul":
        return a * exact(x[2], vals)
    if k == "div":
        return a / exact(x[2], vals)
    if k == "lpow":
        return a ** x[2]
    if k == "rem":
        b = exact(x[2], vals)
        return a - b * trunc(a / b, 0)
    if k == "sum":
        return sum((exact(c, vals) for c in x[1]), Fraction(0))
    raise ValueError(x)


def lit_text(v, k):
    """A signed literal (for MOVE) of v, which has at most k places, written with k places."""
    n = abs(v) * 10 ** k
    assert n.denominator == 1
    t = str(n.numerator).rjust(k + 1, "0")
    t = t if k == 0 else t[:-k] + "." + t[-k:]
    return f"-{t}" if v < 0 else t


def scaled_text(v, f):
    t = str(abs(v)).rjust(f + 1, "0")
    t = t if f == 0 else t[:-f] + "." + t[-f:]
    return ("-" if v < 0 else "") + t


def store(v, rcv, rounded):
    """IBM's stored value of the final result v into receiver rcv: (value or None for a size
    error, overflow?, value cut at the high end without ON SIZE ERROR)."""
    _, _, i, d, _ = RBY[rcv]
    w = round_half_away(v, d) if rounded else trunc(v, d)
    cap = Fraction(10) ** i
    if abs(w) < cap:
        return w, False, w
    n = abs(w.numerator) * 10 ** d // w.denominator % (10 ** (i + d))
    cut = Fraction(n if w >= 0 else -n, 10 ** d)
    return None, True, cut


def gclass(info):
    """The class of a step whose GnuCOBOL line may differ from IBM's: G-powlit (the dmax places of a power by a
    literal changed its value), G-ir30 (an intermediate result cut by rows 3 and 4), else G-exactdiv."""
    if info.get("pow_lo"):
        return "G-powlit"
    return "G-ir30" if info["cap"] - {"row2"} or info["cut_lo"] else "G-exactdiv"


class Gen:
    def __init__(self, rng, k, part="ir30"):
        self.rng, self.k, self.part = rng, k, part
        self.vals = {nm: 0 for nm in BY}
        self.rvals = {r: 0 for r in RBY}
        self.steps = []
        self.stop = rng.random() < 0.33

    # ------------------------------------------------------------ shapes
    def big(self):
        return ("item", self.rng.choice(["L1", "L2", "L3", "L4", "F1", "F2", "F3", "F4", "F5", "F6"]))

    def any_leaf(self):
        r = self.rng.random()
        if r < 0.7:
            return self.big()
        if r < 0.85:
            return ("item", self.rng.choice(["S1", "S2"]))
        return ("lit", self.rng.choice(LITS))

    def expr(self):
        rng, b, a = self.rng, self.big, self.any_leaf
        r = rng.random()
        if r < 0.18:
            return ("mul", ("mul", b(), b()), a())
        if r < 0.32:
            return (rng.choice(["add", "sub"]), ("mul", b(), b()), a())
        if r < 0.42:
            return ("mul", ("mul", b(), b()), ("mul", b(), a()))
        if r < 0.52:
            return ("add", ("mul", b(), b()), ("mul", b(), b()))
        if r < 0.6:
            return ("mul", (rng.choice(["add", "sub"]), b(), b()), a())
        if r < 0.7:
            return ("div", ("mul", b(), b()), ("item", rng.choice(["S1", "S2", "F1", "L4"])))
        if r < 0.78:
            return ("mul", ("div", b(), ("item", rng.choice(["S1", "S2", "F3"]))), a())
        if r < 0.86:
            return ("sub", ("mul", ("add", b(), b()), a()), a())
        return ("mul", b(), b())

    def pow_base(self, edge=False):
        """Part powlit: a base and a literal exponent (an item, a literal or a sum of two items); edge: half the time
        a power of 28 or 29 digits (POW_EDGE)."""
        rng = self.rng
        if edge and rng.random() < 0.5:
            return rng.choice(POW_EDGE)
        r = rng.random()
        if r < 0.6:
            nm, ns = rng.choice(POWS)
            return ("item", nm), rng.choice(ns)
        if r < 0.85:
            t, ns = rng.choice(POW_LITS)
            return ("lit", t), rng.choice(ns)
        a, b = rng.sample(["S1", "S2", "P5"], 2)
        return ("add", ("item", a), ("item", b)), rng.choice([3, 4, 5, 6])

    def powexpr(self, edge=False):
        """Part powlit: a power by a literal alone or as an operand."""
        rng = self.rng
        b, n = self.pow_base(edge)
        p = ("lpow", b, n)
        r = rng.random()
        if r < 0.3:
            return p
        if r < 0.5:
            return ("mul", p, rng.choice([("item", "S2"), ("lit", "10"), ("lit", "1000"), ("item", "L4")]))
        if r < 0.65:
            return ("add", p, ("item", rng.choice(["S1", "F2"])))
        if r < 0.75:
            return ("sub", ("item", "F6"), p)
        if r < 0.85:
            return ("div", p, ("item", rng.choice(["S1", "S2"])))
        return ("add", p, ("lpow", ("item", "S1"), 2))

    # ------------------------------------------------------------ values
    def setup(self, names, big, moderate=False):
        out = []
        for nm in sorted(names):
            _, pic, i, d, signed, _ = BY[nm]
            n = i + d
            r = 0.3 if moderate else self.rng.random()
            if big or r < 0.25:
                v = self.rng.randint(10 ** (n - 1), 10 ** n - 1)
            elif r < 0.45:
                # a few integer digits and every decimal place used (a cut of decimal places then
                # shows after a product with a moderate integer)
                if d > 0:
                    v = self.rng.randint(10 ** d, 10 ** min(d + 3, n) - 1)
                else:
                    v = self.rng.randint(10 ** min(3, n - 1), 10 ** min(8, n) - 1)
            elif r < 0.6:
                v = self.rng.randint(1, 10 ** self.rng.randint(1, max(1, n - 4)))
            elif r < 0.9:
                v = self.rng.randint(1, 10 ** max(1, n // 2))
            else:
                v = 0
            if signed and self.rng.random() < 0.3:
                v = -v
            if nm in ("S1", "S2", "F1", "F3", "L4") and v == 0:
                v = 7
            self.vals[nm] = v
            out.append(f"MOVE {scaled_text(v, d)} TO {nm}")
        return out

    def outcome(self, x, rcvs, rounded, cond_other=None, trap=False):
        """IBM's outcome of a COMPUTE / condition: ("ok", value, info) | ("cut", ...) | ("open", ...) | ("cutpow", ...)
        | ("openpow", ...) | ("size", ...) (part pow0: a zero base with trap, the statement's ON SIZE ERROR)."""
        info = {"cap": set(), "cut_lo": False}
        if cond_other is None:
            dmax = max([0] + [RBY[r][3] for r in rcvs] + Expr.dscales(x))
            role = "final" if len(rcvs) == 1 and not rounded else "ir"
        else:
            dmax = max([0] + Expr.dscales(x) + Expr.dscales(cond_other))
            role = "ir"
        env = Env(dmax, dmax, rounded)
        env.trap = trap
        try:
            v, _, _ = ev(x, self.vals, env, role, info, rounded)
            if cond_other is not None:
                w, _, _ = ev(cond_other, self.vals, env, "ir", info, False)
                return "ok", (v, w), info, dmax
            return "ok", v, info, dmax
        except Cut:
            return "cut", None, info, dmax
        except Open:
            return "open", None, info, dmax
        except CutPow:
            return "cutpow", None, info, dmax
        except OpenPow:
            return "openpow", None, info, dmax
        except SizeErr:
            return "size", None, info, dmax
        except ZeroDivisionError:
            return "zero", None, info, dmax

    # ------------------------------------------------------------ steps
    def step_visible(self, n, want):
        """A step whose cut of decimal places shows in the receiver (rows 3 and 4: a product of
        two decimal items times a moderate integer; PG example P02 of probe f4probe1; part powlit:
        a power held with dmax places times an item or literal)."""
        return self.step_compute(n, want, visible=True)

    def step_compute(self, n, want, visible=False):
        """want: "ok" (a step the run passes), "cut", "open", "cutpow" or "openpow" (the final stop step)."""
        rng = self.rng
        for _ in range(2000 if visible else 400):
            two = rng.random() < 0.25 and not visible
            rounded = want in ("open", "openpow") or (want == "ok" and rng.random() < 0.15 and not visible)
            rcvs = rng.sample([r[0] for r in RCVS], 2 if two else 1)
            fn = rng.random() < 0.12 and want == "ok" and not visible
            if visible and self.part == "powlit":
                # a power times an item or literal that brings the decimal places IBM cut into the receiver
                rcvs = [rng.choice(["R9", "R6", "R4"])]
                b, k = self.pow_base()
                x = ("mul", ("lpow", b, k), rng.choice([("item", "L4"), ("item", "L1"), ("lit", "1000000"),
                                                       ("lit", "123456789012")]))
            elif visible:
                rcvs = [rng.choice(["R9", "R6", "R4"])]
                x = ("mul", ("mul", ("item", rng.choice(["F1", "F3", "F4", "F5"])),
                             ("item", rng.choice(["F1", "F2", "F3", "F4", "F5"]))),
                     rng.choice([("item", "L1"), ("item", "L4"), ("lit", "999999999"), ("lit", "123456789012")]))
            elif self.part == "powlit":
                x = self.powexpr(edge=want == "openpow")
            elif fn:
                if rng.random() < 0.6:
                    x = ("rem", ("rem", self.big(), ("item", rng.choice(["S1", "F1", "L4"]))),
                         ("item", rng.choice(["S1", "S2", "F1"])))
                else:
                    x = ("sum", [self.big() for _ in range(rng.randint(2, 5))])
            else:
                x = self.expr()
            saved = dict(self.vals)
            lines = self.setup(Expr.items(x, set()), want in ("cut", "cutpow"), moderate=visible)
            st, v, info, dmax = self.outcome(x, rcvs, rounded)
            if st != want:
                self.vals = saved
                continue
            ex = exact(x, self.vals)
            size = rng.random() < 0.7
            res = []
            for r in rcvs:
                if st == "ok":
                    sv, over, cutv = store(v, r, rounded)
                    se, over_e, cut_e = store(ex, r, rounded)
                else:
                    sv = over = cutv = se = over_e = cut_e = None
                res.append((r, sv, over, cutv, se, over_e, cut_e))
            if st == "ok" and any(t[2] for t in res):
                size = True
            tail = f" ON SIZE ERROR DISPLAY 'S{n:02d} Z|' NOT ON SIZE ERROR DISPLAY 'S{n:02d} N|' END-COMPUTE" \
                if size else ""
            rnd = " ROUNDED" if rounded else ""
            orig = lines + [f"MOVE 77 TO {r}" for r in rcvs] + \
                [f"COMPUTE {' '.join(r + rnd for r in rcvs)} = {Expr.text(x)}{tail}"]
            mir = lines + [f"MOVE 77 TO {r}" for r in rcvs]
            g = set()
            if st == "ok":
                if info.get("litpow64"):
                    g.add("G-litpow64")
                any_over = any(t[2] for t in res)
                for (r, sv, over, cutv, se, over_e, cut_e) in res:
                    final = (cutv if over else sv)
                    if not (size and any_over and over):
                        mir.append(f"MOVE {lit_text(final, RBY[r][3])} TO {r}")
                    # GnuCOBOL's stored value from the exact result
                    gfinal = cut_e if over_e else se
                    if (size and over) != (size and over_e) or (not over and not over_e and sv != se) \
                            or (not size and gfinal != final):
                        g.add(gclass(info))
                if size:
                    mir.append(f"DISPLAY 'S{n:02d} {'Z' if any_over else 'N'}|'")
            if visible and ("G-powlit" if self.part == "powlit" else "G-ir30") not in g:
                self.vals = saved
                continue
            show_lines = []
            for r in rcvs:
                show_lines += [f"MOVE {r} TO E{r}", f"DISPLAY 'S{n:02d} {r}[' E{r} ']'"]
            stt = {"step": n, "kind": "visible" if visible else "compute", "rcvs": rcvs, "rounded": rounded, "dmax": dmax,
                   "text": Expr.text(x), "outcome": st, "caps": sorted(info["cap"]), "cut_lo": info["cut_lo"],
                   "div": info.get("div", False), "fn": info.get("fn", False), "size": size, "g": sorted(g)}
            if self.part == "powlit":
                stt.update({"pow": sorted(info.get("pow", set())), "pow_lo": info.get("pow_lo", False)})
            return orig + show_lines, mir + show_lines, stt
        raise RuntimeError(f"no {want} step found")

    def step_cond(self, n, want):
        rng = self.rng
        mk = self.powexpr if self.part == "powlit" else self.expr
        for _ in range(400):
            x = mk()
            other = ("lit", rng.choice(["0", "1000", "7"])) if rng.random() < 0.5 else mk()
            saved = dict(self.vals)
            lines = self.setup(Expr.items(x, set()) | Expr.items(other, set()), want == "cut")
            st, vw, info, dmax = self.outcome(x, [], False, other)
            if st != want:
                self.vals = saved
                continue
            op = rng.choice(["=", ">", "<", ">=", "<=", "NOT ="])
            tail = [f"DISPLAY 'S{n:02d} Y|'", "ELSE", f"DISPLAY 'S{n:02d} N|'", "END-IF"]
            orig = lines + [f"IF {Expr.text(x)} {op} {Expr.text(other)}"] + tail
            g = set()
            if st == "ok":
                v, w = vw
                res = {"=": v == w, ">": v > w, "<": v < w, ">=": v >= w, "<=": v <= w, "NOT =": v != w}[op]
                ve, we = exact(x, self.vals), exact(other, self.vals)
                rese = {"=": ve == we, ">": ve > we, "<": ve < we, ">=": ve >= we, "<=": ve <= we, "NOT =": ve != we}[op]
                if res != rese:
                    g.add(gclass(info))
                if info.get("litpow64"):
                    g.add("G-litpow64")
                mir = lines + [f"DISPLAY 'S{n:02d} {'Y' if res else 'N'}|'"]
            else:
                mir = lines
            stt = {"step": n, "kind": "cond", "dmax": dmax, "text": f"{Expr.text(x)} {op} {Expr.text(other)}",
                   "outcome": st, "caps": sorted(info["cap"]), "cut_lo": info["cut_lo"],
                   "div": info.get("div", False), "fn": False, "size": False, "g": sorted(g)}
            if self.part == "powlit":
                stt.update({"pow": sorted(info.get("pow", set())), "pow_lo": info.get("pow_lo", False)})
            return orig, mir, stt
        raise RuntimeError(f"no {want} condition found")

    def step_viscond(self, n, want):
        """Part powlit: IF a power = (or NOT =) a positive literal that holds IBM's value of it, the power held with
        dmax places (dmax: the power's own decimal places, which the literal's do not exceed), values drawn until
        the cut changes the value, so that the condition shows it (G-powlit)."""
        rng = self.rng
        for _ in range(2000):
            b, k = self.pow_base()
            x = ("lpow", b, k)
            saved = dict(self.vals)
            lines = self.setup(Expr.items(x, set()), False, moderate=True)
            s = max([0] + Expr.dscales(x))
            info = {"cap": set(), "cut_lo": False}
            try:
                v, _, _ = ev(x, self.vals, Env(s, s, False), "ir", info, False)
            except (Cut, Open, CutPow, OpenPow):
                self.vals = saved
                continue
            # a numeric literal has at most 18 digits
            if not info.get("pow_lo") or v <= 0 or ndig(v.numerator * 10 ** s // v.denominator) > 18:
                self.vals = saved
                continue
            lit = lit_text(v, s)
            op = rng.choice(["=", "NOT ="])
            orig = lines + [f"IF {Expr.text(x)} {op} {lit}", f"DISPLAY 'S{n:02d} Y|'", "ELSE",
                            f"DISPLAY 'S{n:02d} N|'", "END-IF"]
            mir = lines + [f"DISPLAY 'S{n:02d} {'Y' if op == '=' else 'N'}|'"]
            stt = {"step": n, "kind": "viscond", "dmax": s, "text": f"{Expr.text(x)} {op} {lit}", "outcome": "ok",
                   "caps": sorted(info["cap"]), "cut_lo": info["cut_lo"], "div": False, "fn": False, "size": False,
                   "g": ["G-powlit"], "pow": sorted(info.get("pow", set())), "pow_lo": True}
            return orig, mir, stt
        raise RuntimeError("no visible power condition found")

    def set_moderate(self, names, zero=(), force=False):
        """MOVEs of moderate values (up to 4 integer digits, every decimal place drawn) into the items names; an
        item of zero is 0 in two fifths of the steps (always with force)."""
        rng = self.rng
        out = []
        for nm in sorted(names):
            _, _, i, d, signed, _ = BY[nm]
            if nm in zero and (force or rng.random() < 0.4):
                v = 0
            else:
                v = rng.randint(1, 10 ** (min(i, 4) + d) - 1)
                if signed and rng.random() < 0.3:
                    v = -v
            self.vals[nm] = v
            out.append(f"MOVE {scaled_text(v, d)} TO {nm}")
        return out

    def step_pow0(self, n, want):
        """Part pow0: COMPUTE with a power by the literal 0 (alone or as an operand) into one or two receivers, ON SIZE
        ERROR in most steps, NOT ON SIZE ERROR alone in some (a nonzero base), or an IF relation with such a power;
        want "pow0not" (the stop step): a zero base under NOT ON SIZE ERROR alone, which the model makes unsupported."""
        rng = self.rng
        stop = want == "pow0not"
        base = rng.choice(POW0_ZERO if stop else POW0_BASES)
        p = ("lpow", base, 0)
        x = rng.choice([p, ("add", p, ("item", "S2")), ("mul", p, ("lit", "3")), ("sub", ("item", "F6"), p)])
        lines = self.set_moderate(Expr.items(x, set()), zero=Expr.items(base, set()), force=stop)
        litzero = base[0] == "lit" and Fraction(base[1]) == 0
        g = set()
        if not stop and rng.random() < 0.25:
            other = ("lit", rng.choice(["1", "0", "4"]))
            st, vw, info, dmax = self.outcome(x, [], False, other)
            op = rng.choice(["=", ">", "<", "NOT ="])
            v, w = vw
            res = {"=": v == w, ">": v > w, "<": v < w, "NOT =": v != w}[op]
            orig = lines + [f"IF {Expr.text(x)} {op} {Expr.text(other)}", f"DISPLAY 'S{n:02d} Y|'", "ELSE",
                            f"DISPLAY 'S{n:02d} N|'", "END-IF"]
            mir = lines + [f"DISPLAY 'S{n:02d} {'Y' if res else 'N'}|'"]
            stt = {"step": n, "kind": "cond", "dmax": dmax, "text": f"{Expr.text(x)} {op} {Expr.text(other)}",
                   "outcome": st, "caps": [], "cut_lo": False, "div": False, "fn": False, "size": False, "g": [],
                   "pow": sorted(info.get("pow", set())), "pow00": info.get("pow00", False)}
            return orig, mir, stt
        rcvs = rng.sample([r[0] for r in RCVS], 2 if rng.random() < 0.25 else 1)
        rounded = rng.random() < 0.2
        size = not stop and rng.random() < 0.7
        st, v, info, dmax = self.outcome(x, rcvs, rounded, trap=size)
        # NOT ON SIZE ERROR alone: with a nonzero base in some steps, with a zero base in the stop step
        notonly = stop or (not size and not info.get("pow00") and rng.random() < 0.5)
        if size:
            tail = f" ON SIZE ERROR DISPLAY 'S{n:02d} Z|' NOT ON SIZE ERROR DISPLAY 'S{n:02d} N|' END-COMPUTE"
        elif notonly:
            tail = f" NOT ON SIZE ERROR DISPLAY 'S{n:02d} N|' END-COMPUTE"
        else:
            tail = ""
        rnd = " ROUNDED" if rounded else ""
        orig = lines + [f"MOVE 77 TO {r}" for r in rcvs] + \
            [f"COMPUTE {' '.join(r + rnd for r in rcvs)} = {Expr.text(x)}{tail}"]
        mir = lines + [f"MOVE 77 TO {r}" for r in rcvs]
        if st == "size":
            # IBM: "the value of the resultant identifier affected by the size error is not altered"
            mir.append(f"DISPLAY 'S{n:02d} Z|'")
            g.add("G-litpow00" if litzero else "G-pow00")
        else:
            res = [(r,) + store(v, r, rounded) for r in rcvs]
            any_over = any(t[2] for t in res)
            for (r, sv, over, cutv) in res:
                if not (size and over):
                    mir.append(f"MOVE {lit_text(cutv if over else sv, RBY[r][3])} TO {r}")
            if size:
                mir.append(f"DISPLAY 'S{n:02d} {'Z' if any_over else 'N'}|'")
            elif notonly and not any_over:
                # IBM: the NOT ON SIZE ERROR phrase runs when "a size error condition does not exist"
                mir.append(f"DISPLAY 'S{n:02d} N|'")
        show_lines = []
        for r in rcvs:
            show_lines += [f"MOVE {r} TO E{r}", f"DISPLAY 'S{n:02d} {r}[' E{r} ']'"]
        stt = {"step": n, "kind": "compute", "rcvs": rcvs, "rounded": rounded, "dmax": dmax, "text": Expr.text(x),
               "outcome": st, "caps": [], "cut_lo": False, "div": False, "fn": False, "size": size, "g": sorted(g),
               "pow": sorted(info.get("pow", set())), "pow00": info.get("pow00", False), "notonly": notonly}
        return orig + show_lines, mir + show_lines, stt

    def c30_places(self, o):
        """(integer places, decimal places) of a part c30 operand: an item's PICTURE, a literal's digits as written."""
        if o[0] == "item":
            _, _, i, d, _, _ = BY[o[1]]
            return i, d
        t = o[1]
        ip, fp = (t.split(".") + [""])[:2]
        return len(ip), len(fp)

    def step_c30(self, n, want):
        """Part c30: one ADD, SUBTRACT, MULTIPLY or DIVIDE (no ROUNDED) whose composite of operands is at most 30
        digits (want "ok") or more (want "c30": the last step, which the front end makes unsupported)."""
        rng = self.rng
        names = [it[0] for it in C30_ITEMS]
        for _ in range(2000):
            form = rng.choice(["add_to", "add_giving", "sub_from", "sub_giving", "mul_by", "mul_giving", "div_into",
                               "div_giving"])
            pool = rng.sample(names, 5)
            nr = 2 if form in ("add_to", "sub_from", "mul_by", "div_into") and rng.random() < 0.4 else 1
            rcvs, rest = pool[:nr], pool[nr:]

            def operand():
                if rng.random() < 0.25:
                    return ("lit", rng.choice(C30_LITS))
                return ("item", rest.pop())
            if form in ("add_to", "sub_from"):
                ops = [operand() for _ in range(rng.choice([1, 2]))]
                members = ops + [("item", r) for r in rcvs]
                verb = "ADD" if form == "add_to" else "SUBTRACT"
                text = f"{verb} {' '.join(o[1] for o in ops)} {'TO' if form == 'add_to' else 'FROM'} {' '.join(rcvs)}"
            elif form == "add_giving":
                ops = [operand(), operand()]
                members = ops
                text = f"ADD {ops[0][1]} {rng.choice(['TO ', ''])}{ops[1][1]} GIVING {rcvs[0]}"
            elif form == "sub_giving":
                ops = [operand(), operand()]
                members = ops
                text = f"SUBTRACT {ops[0][1]} FROM {ops[1][1]} GIVING {rcvs[0]}"
            elif form == "mul_by":
                ops = [operand()]
                members = [("item", r) for r in rcvs]
                text = f"MULTIPLY {ops[0][1]} BY {' '.join(rcvs)}"
            elif form == "mul_giving":
                ops = [operand(), operand()]
                members = [("item", r) for r in rcvs]
                text = f"MULTIPLY {ops[0][1]} BY {ops[1][1]} GIVING {rcvs[0]}"
            elif form == "div_into":
                ops = [operand()]
                members = [("item", r) for r in rcvs]
                text = f"DIVIDE {ops[0][1]} INTO {' '.join(rcvs)}"
            else:
                ops = [operand(), operand()]
                members = [("item", r) for r in rcvs]
                text = rng.choice([f"DIVIDE {ops[0][1]} INTO {ops[1][1]} GIVING {rcvs[0]}",
                                   f"DIVIDE {ops[1][1]} BY {ops[0][1]} GIVING {rcvs[0]}"])
            ps = [self.c30_places(o) for o in members]
            comp = max(i for i, _ in ps) + max(d for _, d in ps)
            if (comp <= 30) != (want == "ok"):
                continue
            # composites of exactly 30 digits in about a third of the accepted steps
            if want == "ok" and comp < 30 and rng.random() < 0.85:
                continue
            items = {o[1] for o in ops if o[0] == "item"} | set(rcvs)
            lines = self.set_moderate(items)
            size = rng.random() < 0.7
            tail = f" ON SIZE ERROR DISPLAY 'S{n:02d} Z|' NOT ON SIZE ERROR DISPLAY 'S{n:02d} N|'" if size else ""
            end = {"ADD": "END-ADD", "SUBTRACT": "END-SUBTRACT", "MULTIPLY": "END-MULTIPLY", "DIVIDE": "END-DIVIDE"}
            stmt = text + tail + (" " + end[text.split()[0]] if size else "")
            show = []
            for r in rcvs:
                show += [f"MOVE {r} TO E{r}", f"DISPLAY 'S{n:02d} {r}[' E{r} ']'"]
            prog = lines + [stmt] + show
            stt = {"step": n, "kind": "c30", "form": form, "composite": comp, "rcvs": rcvs, "rounded": False,
                   "dmax": 0, "text": text, "outcome": "ok" if want == "ok" else "c30", "caps": [], "cut_lo": False,
                   "div": form.startswith("div"), "fn": False, "size": size, "g": []}
            if want == "c30":
                self.stop_msg = f"a composite of operands of {comp} digits"
            return prog, prog, stt
        raise RuntimeError(f"no {want} c30 step found")

    def step_multiply(self, n, want):
        rng = self.rng
        for _ in range(400):
            a, b = self.big(), self.big()
            rcvs = rng.sample([r[0] for r in RCVS], 2)
            x = ("mul", a, b)
            saved = dict(self.vals)
            lines = self.setup(Expr.items(x, set()), want == "cut")
            st, v, info, dmax = self.outcome(x, rcvs, False)
            if st != want:
                self.vals = saved
                continue
            ex = exact(x, self.vals)
            res = [(r,) + store(v, r, False) + store(ex, r, False) if st == "ok" else (r,) for r in rcvs]
            size = st != "ok" or any(t[2] for t in res) or rng.random() < 0.6
            tail = f" ON SIZE ERROR DISPLAY 'S{n:02d} Z|' NOT ON SIZE ERROR DISPLAY 'S{n:02d} N|' END-MULTIPLY" \
                if size else ""
            orig = lines + [f"MOVE 77 TO {r}" for r in rcvs] + \
                [f"MULTIPLY {Expr.text(a)} BY {Expr.text(b)} GIVING {' '.join(rcvs)}{tail}"]
            mir = lines + [f"MOVE 77 TO {r}" for r in rcvs]
            g = set()
            if st == "ok":
                any_over = any(t[2] for t in res)
                for (r, sv, over, cutv, se, over_e, cut_e) in res:
                    final = cutv if over else sv
                    if not (size and over):
                        mir.append(f"MOVE {lit_text(final, RBY[r][3])} TO {r}")
                    if sv != se or over != over_e or cutv != cut_e:
                        g.add(gclass(info))
                if size:
                    mir.append(f"DISPLAY 'S{n:02d} {'Z' if any_over else 'N'}|'")
            show_lines = []
            for r in rcvs:
                show_lines += [f"MOVE {r} TO E{r}", f"DISPLAY 'S{n:02d} {r}[' E{r} ']'"]
            stt = {"step": n, "kind": "multiply", "rcvs": rcvs, "rounded": False, "dmax": dmax,
                   "text": Expr.text(x), "outcome": st, "caps": sorted(info["cap"]), "cut_lo": info["cut_lo"],
                   "div": False, "fn": False, "size": size, "g": sorted(g)}
            return orig + show_lines, mir + show_lines, stt
        raise RuntimeError(f"no {want} multiply found")

    def data(self):
        d = []
        if self.part == "c30":
            for nm, pic, _, _, _, usage in C30_ITEMS:
                d.append(f"       01  {nm} PIC {pic}{usage} VALUE ZERO.")
                d.append(f"       01  E{nm} PIC {C30_EDIT[nm]}.")
            return d
        for nm, pic, _, _, _, usage in ITEMS + (POW_ITEMS if self.part in ("powlit", "pow0") else []):
            d.append(f"       01  {nm} PIC {pic}{usage} VALUE ZERO.")
        for nm, pic, _, _, epic in RCVS:
            d.append(f"       01  {nm} PIC {pic} VALUE ZERO.")
            d.append(f"       01  E{nm} PIC {epic}.")
        return d

    def programs(self):
        """(original source, mirror source); self.steps; self.stop_kind: None, "cut" or "open" (part powlit:
        "cutpow" or "openpow"; part c30: "c30", with self.stop_msg; part pow0: "pow0not")."""
        proc, procm = [], []
        self.stop_kind = None
        self.stop_msg = None
        pl = self.part == "powlit"
        for n in range(self.k):
            want = "ok"
            if self.stop and n == self.k - 1 and self.part in ("c30", "pow0"):
                want = self.stop_kind = "c30" if self.part == "c30" else "pow0not"
            elif self.stop and n == self.k - 1:
                want = self.rng.choice(["cutpow", "cutpow", "openpow"] if pl else ["cut", "cut", "open"])
                self.stop_kind = want
            r = self.rng.random()
            if self.part == "pow0":
                maker = self.step_pow0
            elif self.part == "c30":
                maker = self.step_c30
            elif pl:
                maker = self.step_compute if want != "ok" else \
                    self.step_visible if r < 0.15 else self.step_viscond if r < 0.3 else \
                    self.step_compute if r < 0.7 else self.step_cond
            elif want == "open":
                maker = self.step_compute
            elif want == "ok" and r < 0.15:
                maker = self.step_visible
            elif r < 0.6:
                maker = self.step_compute
            elif r < 0.8:
                maker = self.step_cond
            else:
                maker = self.step_multiply
            orig, mir, st = maker(n, want)
            self.steps.append(st)
            for ln in orig:
                proc += E.wrap(ln)
            for ln in mir:
                procm += E.wrap(ln)
        hdr = E.header({"powlit": "POWLT", "pow0": "POW0T", "c30": "C30T"}.get(self.part, "IR30T"), self.data())
        src = "\n".join(E.check_lines(hdr + proc + ["           STOP RUN."])) + "\n"
        srcm = "\n".join(E.check_lines(hdr + procm + ["           STOP RUN."])) + "\n"
        return src, srcm


def gnucobol(D, src, base):
    """Compile and run one program with GnuCOBOL: (status, lines or detail)."""
    d = os.path.dirname(base)
    with open(base + ".cob", "w", encoding="latin-1") as fh:
        fh.write(src)
    c = subprocess.run([D.COBC, "-x"] + IR_COBC + ["-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return "cobc-error", c.stderr[-2000:]
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    try:
        r = subprocess.run([base], capture_output=True, env=env, timeout=20, cwd=d)
    except subprocess.TimeoutExpired:
        return "gnucobol-timeout", None
    if r.returncode != 0:
        return "gnucobol-abend", (r.stdout[-500:] + r.stderr[-500:]).decode("latin-1")
    g = r.stdout.decode("latin-1").split("\n")
    if g and g[-1] == "":
        g.pop()
    return "ran", g


def model(D, base, fe_unsup_ok=False):
    """The front end + cobolrun on base.cob: (status, lines or detail, signal). fe_unsup_ok (part c30's last step):
    a statement the front end makes unsupported does not stop here; the model runs up to it."""
    d = os.path.dirname(base)
    # -B: no bytecode written into the work copy (the control runs on a read-only base)
    fe = subprocess.run([sys.executable, "-I", "-B", D.COBOLFE, base + ".cob"] + IR_FE +
                        ["--main", "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0:
        return "fe-error", fe.stderr[-2000:], None
    unsup = [ln for ln in fe.stderr.splitlines() if "unsupported" in ln]
    if unsup and not fe_unsup_ok:
        return "fe-unsupported", unsup, None
    try:
        lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True,
                            timeout=60, cwd=d)
    except subprocess.TimeoutExpired:
        return "lean-timeout", None, None
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-2000:], None
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    return "ran", m, res["signal"]


def parse(line):
    """'Snn ...' -> nn."""
    if len(line) >= 4 and line[0] == "S" and line[1:3].isdigit() and line[3] == " ":
        return int(line[1:3])
    return None


def judge(gen, srcs, D, base, tally):
    """Status and detail of one generated program (see the module docstring)."""
    src, srcm = srcs
    s1, g = gnucobol(D, src, base)
    if s1 != "ran":
        return s1, g
    s2, m, signal = model(D, base, fe_unsup_ok=gen.stop_kind == "c30")
    if s2 != "ran":
        return s2, m
    s3, mi = gnucobol(D, srcm, base + "_mirror")
    if s3 != "ran":
        return "mirror-" + s3, mi
    info = {s["step"]: s for s in gen.steps}
    if gen.stop_kind is not None:
        want = gen.stop_msg or STOP_MSG[gen.stop_kind]
        if not (signal.startswith("fault:Cobol.Fault.unsupported") and want in signal):
            return "stop-mismatch", f"expected {gen.stop_kind} ({want}), signal {signal}"
        last = gen.k - 1
        mi = [ln for ln in mi if parse(ln) != last]
        g = [ln for ln in g if parse(ln) is None or parse(ln) < last]
    elif not signal.startswith("stop:"):
        return "lean-signal", signal
    if m != mi:
        i = E.first_diff(mi, m)
        return "mirror", f"line {i}: mirror vs model"
    if len(g) != len(m):
        return "mismatch", f"line counts {len(g)} vs {len(m)}"
    glines = 0
    for a, b in zip(g, m):
        n = parse(b)
        tally["lines"] += 1
        if a == b:
            continue
        st = info.get(n)
        if st is None or not st["g"]:
            return "mismatch", f"step {n}: gnucobol {a!r} model {b!r} ({st['text'] if st else ''})"
        glines += 1
        for c in st["g"]:
            tally["g_lines"][c] = tally["g_lines"].get(c, 0) + 1
    if gen.stop_kind is not None:
        tally["stops"][gen.stop_kind] = tally["stops"].get(gen.stop_kind, 0) + 1
        return "ok-stop", ""
    return ("ok-g" if glines else "ok"), ""


def coverage(gen, cov):
    for s in gen.steps:
        feats = [s["kind"], f"outcome_{s['outcome']}"] + [f"cap_{c}" for c in s["caps"]] + s["g"]
        feats += [f for f, t in (("rounded", s.get("rounded")), ("two_receivers", len(s.get("rcvs", [])) == 2),
                                 ("cut_decimals", s["cut_lo"]), ("division", s["div"]), ("function", s["fn"]),
                                 ("size_phrase", s["size"]), ("pow_cut_decimals", s.get("pow_lo")),
                                 ("not_size_only", s.get("notonly"))) if t]
        feats += [f"pow_{h}" for h in s.get("pow", [])]
        if s.get("pow00"):
            feats.append("pow_zero_base")
        if "form" in s:
            c = s["composite"]
            feats += [f"form_{s['form']}", "composite_30" if c == 30 else "composite_over30" if c > 30 else "composite_under30"]
        for f in feats:
            cov[f] = cov.get(f, 0) + 1


def run_files(args):
    """--run: each program both ways, the lines side by side (classtest's format), and the signal. A model run
    that stops with a fault is stop-cut (the IGZ0036W text), stop-open (places carried open), stop-cutpow (a
    power held with dmax places beyond 30 digits), stop-openpow (a power by a literal whose places are open) or
    stop-unsup (another unsupported text), with -mismatch when its lines are not the first lines of GnuCOBOL's."""
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    worst = 0
    for path in args.run:
        with open(path, encoding="latin-1") as fh:
            src = fh.read()
        base = os.path.join(args.out, "run_" + os.path.splitext(os.path.basename(path))[0])
        s1, g = gnucobol(D, src, base)
        status, m, signal = s1, g, None
        if s1 == "ran":
            s2, m, signal = model(D, base)
            if s2 != "ran":
                status = s2
            elif signal.startswith("stop:"):
                status = "ok" if g == m else "mismatch"
            else:
                kind = "cut" if CUT_MSG in signal else "open" if OPEN_MSG in signal else \
                    "cutpow" if CUTPOW_MSG in signal else "openpow" if OPENPOW_MSG in signal else \
                    "unsup" if signal.startswith("fault:Cobol.Fault.unsupported") else "signal"
                status = f"stop-{kind}" if g[:len(m)] == m else f"stop-{kind}-mismatch"
        print(f"== {path}: {status}")
        if signal is not None and not signal.startswith("stop:"):
            print(f"   model signal: {signal}")
        if s1 == "ran" and signal is not None:
            for i in range(max(len(g), len(m))):
                a, b = (g[i] if i < len(g) else "<none>"), (m[i] if i < len(m) else "<none>")
                print(("   " if a == b else "!! ") + f"{show(a):<44} | {show(b)}")
        else:
            print(str(m)[:2000])
        worst = max(worst, 0 if status == "ok" else 1)
    return worst


def main():
    ap = E.arg_parser(__doc__, 60, 12)
    ap.add_argument("--run", nargs="+", metavar="PROG.cob")
    ap.add_argument("--part", choices=["ir30", "powlit", "pow0", "c30"], default="ir30")
    args = ap.parse_args()
    if args.run:
        sys.exit(run_files(args))
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    open(os.path.join(args.out, "details.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown = {"g_lines": {}, "lines": 0, "stops": {}}, 0
    statuses, cov = {}, {}
    for p in range(args.n):
        gen = Gen(rng, args.k, args.part)
        srcs = gen.programs()
        base = os.path.join(args.out, f"p{args.seed}_{p:04d}")
        status, detail = judge(gen, srcs, D, base, tally)
        coverage(gen, cov)
        statuses[status] = statuses.get(status, 0) + 1
        with open(os.path.join(args.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": p, "status": status}) + "\n")
        if status not in ("ok", "ok-g", "ok-stop"):
            with open(os.path.join(args.out, "details.jsonl"), "a") as fh:
                fh.write(json.dumps({"case": p, "status": status, "detail": str(detail)[:2000],
                                     "steps": gen.steps}) + "\n")
            if shown < args.show:
                shown += 1
                print(f"program {p}: {status}: {str(detail)[:600]}")
    with open(os.path.join(args.out, "coverage.json"), "w") as fh:
        json.dump({"statuses": statuses, "tally": tally, "coverage": cov}, fh, indent=1, sort_keys=True)
    print(json.dumps({"tally": statuses}))
    print(json.dumps({k: tally[k] for k in sorted(tally)}, sort_keys=True))
    # exit status 0 when every program passed (ok, ok-g, ok-stop), 1 otherwise
    sys.exit(0 if all(s in ("ok", "ok-g", "ok-stop") for s in statuses) else 1)


if __name__ == "__main__":
    main()

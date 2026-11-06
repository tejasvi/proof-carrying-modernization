#!/usr/bin/env python3
"""Differential testing of the dmax-fix corrections (one part per correction).

  --part all88   level-88 condition names with VALUE ALL literal (IBM: the figurative constant ALL literal,
                 the literal repeated to the size of the conditional variable), next to plain literal values,
                 THRU ranges and figurative constants, on alphanumeric items of 1, 4 and 7 characters, a group
                 and a table element; IF, IF NOT, EVALUATE TRUE, SET ... TO TRUE and explicit relations with
                 ALL literals; a fifth of the programs name a PROGRAM COLLATING SEQUENCE (an ALPHABET of the
                 letters in reverse order). Every outcome is displayed. Checks: every model line equals the
                 line the tester computes from IBM's rules, and so does every GnuCOBOL (-std=ibm) line.
  --part cond    arithmetic expressions with a division (a quotient alone, of a sum or product, times or plus
                 an operand, nested, by a sum, negated) in IF relations (either side; the other comparand a
                 literal with places, an item or a sum), sign conditions, abbreviated relations (A > x AND < y)
                 and EVALUATE (the expression as the subject with literal / item objects, WHEN ... THRU, or as an
                 object of an item subject); integer and decimal DISPLAY and COMP-3 items set by MOVE before each
                 step. IBM (PG "Arithmetic expressions in nonarithmetic statements"): an explicit relation
                 takes as dmax the most places of any operand of either comparand, divisors excluded, each
                 relation of an abbreviated condition its own; a sign condition and an EVALUATE subject or
                 object have no relational operator: the expression's own operands. The quotient is truncated
                 to max(d2 - d1, dmax) places; the expressions hold an item, and no negative literal or unsigned
                 item stands next to them (G-negconst, G-ucmpneg).
                 Checks: every model line equals the tester's IBM line; every GnuCOBOL line (-std=ibm
                 -fno-arithmetic-osvs, which computes the quotients exactly) too, except in G-exactdiv (the
                 outcome with exact quotients differs from IBM's). GnuCOBOL's OS/VS rules (-std=ibm) depart
                 from IBM's in other ways, among them G-evalown (an EVALUATE subject compared with each object
                 under the relation's dmax): hand cases dmax_cases/g_evalown.cob.
  --part edited  COMPUTE into a numeric-edited receiver (-(5)9.9 to -(4)9.9(4), Z(4)9.999), alone or with a numeric
                 receiver of fewer places, of an expression with a division (integer operands weighted); IBM: dmax
                 counts "the number of decimal places needed for the final result field or fields", the edited
                 receiver's digit positions after the point included.
  --part intfn   COMPUTE with FUNCTION INTEGER or INTEGER-PART of a decimal item or sum, or MOD of integers, next to a
                 division outside the function, into receivers with 0 or 1 places (numeric, or numeric-edited E0 / E1);
                 IBM: an integer function contributes outer-dmax 0, its argument's places do not count.
  --part div     COMPUTE with divisions placed by IBM's rule max(d2 - d1, dmax) (one more place with ROUNDED): a
                 divisor with more places than dmax, a product as the dividend (d2 the sum of its places), nested
                 quotients, a quotient by a sum, two quotients, a quotient alone (there the resolver keeps its old
                 scale max(d1, dmax) when no receiver is ROUNDED and every receiver is numeric: the same stored
                 values), one or two numeric receivers, in a fifth of the steps a numeric-edited one; operands and
                 receivers with few places weighted (dmax below a divisor's places, where the two rules part).
                 For the COMPUTE parts the tester computes each expression's IBM value (quotients truncated to IBM's
                 places, one more with ROUNDED); the IBM mirror is the same program with each expression replaced by an
                 item M1 holding that value. Checks: every model line equals GnuCOBOL's line for the mirror; every line
                 of GnuCOBOL's own run (-std=ibm -fno-arithmetic-osvs: exact quotients) too, except in G-exactdiv (a
                 receiver stores another value when the quotients are exact).
  --part fnarg   (inr-fix, R1) COMPUTE with a division inside a function argument: MAX, MIN, SUM, RANGE, REM, ABS,
                 INTEGER, INTEGER-PART of an argument with a quotient (alone, by a product, plus or times an operand,
                 by a quotient; no argument starts with a parenthesis, which after an item argument the compilers read
                 as a subscript), some with a nested function as another argument, alone or times / plus / divided by
                 / subtracted from an operand, and MOD of INTEGER or INTEGER-PART of such an argument; receivers with 2
                 or 4 places weighted (the statement's dmax above the arguments'). IBM (PG "Terminology used for
                 intermediate results"; LR
                 "Function definition and evaluation", "Arguments"): an argument expression is computed with the
                 function's inner-dmax, the most places of that function's arguments (0 for MOD), never with the
                 statement's receivers, other operands or ROUNDED phrase. Checks as for the COMPUTE parts (IBM mirror;
                 G-exactdiv, GnuCOBOL's line predicted from quotients with 37 places: it divides with about 38 digits,
                 so INTEGER (A * (B / A)) can be one less than with exact quotients); coverage r1_scale / r1_value: an
                 argument's quotient has another scale / a receiver another value under the resolver's rule before
                 inr-fix.
  --part fncond  (inr-fix, F7) the cond part's steps (relations either side, sign conditions, abbreviated relations,
                 EVALUATE subject or object) with such a function expression instead of the quotient; the resolver
                 before inr-fix gave the arguments of a function in a condition the dmax 0. Checks as for cond (with
                 fnarg's 37-place quotients for GnuCOBOL's line).
  --part rmode   (inr-fix, R2) ROUNDED MODE (the five modes IBM does not have; plain ROUNDED and TRUNCATION a fifth of
                 the receivers): a COMPUTE whose whole expression is one quotient (one or two receivers) rounds the
                 exact quotient once into each receiver, as DIVIDE ... GIVING and DIVIDE ... INTO do; ROUNDED MODE
                 PROHIBITED with ON SIZE ERROR: a size error when the exact quotient has more places than the receiver;
                 a quotient inside a larger expression keeps IBM's intermediate (max(d2 - d1, dmax) + 1 places,
                 truncated), the final value rounded by the mode. Checks: every model line equals GnuCOBOL's line for
                 the mirror (each receiver given its expected value); GnuCOBOL's own run too, except in G-exactdiv and
                 G-prohibited (GnuCOBOL raises the size error under PROHIBITED whenever the quotient has more places
                 than the receiver, even all zero; the model only when the value cannot be stored exactly).

Statuses: ok, ok-g, mismatch (a model line differs from the tester's IBM line), mirror (a model line differs
from the IBM mirror's), gnucobol-mismatch (a GnuCOBOL line differs from it outside the named G-classes), and the
ext_common statuses. Never deletes files.

usage: dmaxtest.py --part P --root C --out DIR [--n N] [--seed S] [--k K] [--show K]
       dmaxtest.py --root C --out DIR --run PROG.cob...
"""
import json
import math
import os
import random
import subprocess
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402
from classtest import show  # noqa: E402

PARTS = ["all88", "cond", "edited", "intfn", "div", "fnarg", "fncond", "rmode"]


# ------------------------------------------------------------------ running both ways
def gnucobol(D, src, base, flags):
    """Compile and run one program with GnuCOBOL: (status, lines or detail)."""
    d = os.path.dirname(base)
    with open(base + ".cob", "w", encoding="latin-1") as fh:
        fh.write(src)
    c = subprocess.run([D.COBC, "-x"] + flags + ["-o", base, base + ".cob"],
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


def model(D, base, fe_flags):
    """The front end + cobolrun on base.cob: (status, lines or detail, signal)."""
    d = os.path.dirname(base)
    # -B: no bytecode written into the work copy (the control runs on a read-only base)
    fe = subprocess.run([sys.executable, "-I", "-B", D.COBOLFE, base + ".cob"] + fe_flags +
                        ["--main", "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0:
        return "fe-error", fe.stderr[-2000:], None
    unsup = [ln for ln in fe.stderr.splitlines() if "unsupported" in ln]
    if unsup:
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


def step_of(line):
    """'Snn ...' -> nn."""
    if len(line) >= 4 and line[0] == "S" and line[1:3].isdigit() and line[3] == " ":
        return int(line[1:3])
    return None


# ------------------------------------------------------------------ part all88
LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
REVERSED = LETTERS[::-1]


class All88:
    """Level-88 values with ALL literals (see the module docstring)."""
    COBC = E.PLAIN_COBC
    FE = E.PLAIN_FE
    # parents: name, length, kind (elem / group / table)
    PARENTS = [("X1", 1, "elem"), ("X4", 4, "elem"), ("X7", 7, "elem"), ("G", 5, "group"), ("T", 3, "table")]

    def __init__(self, rng, k):
        self.rng, self.k = rng, k
        self.seq = rng.random() < 0.2
        self.chars = LETTERS[:6] + " " if self.seq else "ABCxy 0Q"
        self.content = {}
        self.conds = []        # (name, parent, values); a value: ("all", lit) | ("lit", lit) | ("thru", lo, hi) | ("fig", w)
        self.steps = []
        n = 0
        for pname, plen, kind in self.PARENTS:
            for _ in range(rng.randint(1, 3)):
                n += 1
                self.conds.append((f"C{n}", pname, self.values(plen)))
        for pname, plen, kind in self.PARENTS:
            self.content[pname] = [" " * plen] * (3 if kind == "table" else 1)

    # -------------------------------------------------------------- values
    def lit(self, maxlen):
        n = self.rng.randint(1, maxlen)
        return "".join(self.rng.choice(self.chars.replace(" ", "") if i == 0 else self.chars) for i in range(n))

    def values(self, plen):
        rng = self.rng
        vals = []
        for _ in range(rng.choice([1, 1, 1, 2, 3])):
            r = rng.random()
            if r < 0.55:
                vals.append(("all", self.lit(min(3, plen + 1))))
            elif r < 0.75:
                vals.append(("lit", self.lit(plen)))
            elif r < 0.9:
                a, b = sorted([self.lit(1), self.lit(1)], key=self.key)
                vals.append(("thru", a, b))
            else:
                vals.append(("fig", rng.choice(["SPACE", "ZERO"])))
        if not any(v[0] == "all" for v in vals) and rng.random() < 0.7:
            vals.insert(0, ("all", self.lit(min(3, plen + 1))))
        return vals

    def key(self, s):
        """Collating key of a string: native (Latin-1) order, or the program's sequence (the letters in
        reverse order first, every other character after them in native order)."""
        if not self.seq:
            return [ord(c) for c in s]
        return [REVERSED.index(c) if c in REVERSED else 26 + ord(c) for c in s]

    @staticmethod
    def rep(lit, n):
        return (lit * (n // len(lit) + 1))[:n]

    def vtext(self, v):
        if v[0] == "all":
            return f"ALL '{v[1]}'"
        if v[0] == "lit":
            return f"'{v[1]}'"
        if v[0] == "thru":
            return f"'{v[1]}' THRU '{v[2]}'"
        return v[1]

    def holds(self, v, x):
        """Value v of a condition holds for the content x (IBM: the shorter operand padded with spaces;
        ALL literal, SPACE and ZERO repeated to the size of x)."""
        n = len(x)
        if v[0] == "all":
            return x == self.rep(v[1], n)
        if v[0] == "lit":
            return x == v[1].ljust(n)
        if v[0] == "fig":
            return x == (" " if v[1] == "SPACE" else "0") * n
        lo, hi = v[1].ljust(n), v[2].ljust(n)
        return self.key(lo) <= self.key(x) <= self.key(hi)

    def moved(self, v, n):
        """The content SET ... TO TRUE gives (the first value; THRU: its first literal)."""
        if v[0] == "all":
            return self.rep(v[1], n)
        if v[0] in ("lit", "thru"):
            return v[1].ljust(n)[:n]
        return (" " if v[1] == "SPACE" else "0") * n

    # -------------------------------------------------------------- program
    def plen(self, pname):
        return next(p[1] for p in self.PARENTS if p[0] == pname)

    def ref(self, pname, occ):
        return f"{pname} ({occ})" if pname == "T" else pname

    def cref(self, cname, pname, occ):
        return f"{cname} ({occ})" if pname == "T" else cname

    def shown(self, pname):
        """DISPLAY operand and the content it shows (the table: the whole group TB)."""
        if pname == "T":
            return "TB", "".join(self.content["T"])
        return pname, self.content[pname][0]

    def new_content(self, pname):
        rng = self.rng
        n = self.plen(pname)
        cs = [c for c in self.conds if c[1] == pname]
        r = rng.random()
        if r < 0.45 and cs:
            v = rng.choice(rng.choice(cs)[2])
            x = self.moved(v, n)
            if rng.random() < 0.35:
                i = rng.randrange(n)
                x = x[:i] + rng.choice(self.chars) + x[i + 1:]
            return x
        if r < 0.6:
            return " " * n
        return "".join(rng.choice(self.chars) for _ in range(n))

    def step(self, s):
        """One step: (COBOL lines, the expected display lines, step record)."""
        rng = self.rng
        name, pname, vals = rng.choice(self.conds)
        occ = rng.randint(1, 3)
        idx = occ - 1 if pname == "T" else 0
        n = self.plen(pname)
        out, exp = [], []
        if rng.random() < 0.5:
            x = self.new_content(pname)
            out.append(f"MOVE '{x}' TO {self.ref(pname, occ)}")
            self.content[pname][idx] = x
        x = self.content[pname][idx]
        kind = rng.choice(["if", "if", "ifnot", "eval", "set", "rel"])
        truth = any(self.holds(v, x) for v in vals)
        c = self.cref(name, pname, occ)
        if kind == "if":
            out += [f"IF {c}", f"DISPLAY 'S{s:02d} Y|'", "ELSE", f"DISPLAY 'S{s:02d} N|'", "END-IF"]
            exp.append(f"S{s:02d} {'Y' if truth else 'N'}|")
        elif kind == "ifnot":
            out += [f"IF NOT {c}", f"DISPLAY 'S{s:02d} Y|'", "ELSE", f"DISPLAY 'S{s:02d} N|'", "END-IF"]
            exp.append(f"S{s:02d} {'N' if truth else 'Y'}|")
        elif kind == "eval":
            out += ["EVALUATE TRUE", f"WHEN {c}", f"DISPLAY 'S{s:02d} W|'", "WHEN OTHER",
                    f"DISPLAY 'S{s:02d} O|'", "END-EVALUATE"]
            exp.append(f"S{s:02d} {'W' if truth else 'O'}|")
        elif kind == "set":
            out.append(f"SET {c} TO TRUE")
            self.content[pname][idx] = self.moved(vals[0], n)
            op, txt = self.shown(pname)
            out.append(f"DISPLAY 'S{s:02d} [' {op} ']|'")
            exp.append(f"S{s:02d} [{txt}]|")
        else:
            alls = [v for v in vals if v[0] == "all"] or [("all", self.lit(3))]
            v = rng.choice(alls)
            out += [f"IF {self.ref(pname, occ)} = ALL '{v[1]}'", f"DISPLAY 'S{s:02d} Y|'", "ELSE",
                    f"DISPLAY 'S{s:02d} N|'", "END-IF"]
            exp.append(f"S{s:02d} {'Y' if self.holds(v, x) else 'N'}|")
        rec = {"step": s, "kind": kind, "cond": name, "parent": pname, "seq": self.seq,
               "values": [v[0] for v in vals], "g": []}
        return out, exp, rec

    def data(self):
        d = []
        by_parent = {}
        for name, pname, vals in self.conds:
            by_parent.setdefault(pname, []).append((name, vals))
        for pname, plen, kind in self.PARENTS:
            cl = [f"88 {name} VALUE {' '.join(self.vtext(v) for v in vals)}." for name, vals in by_parent.get(pname, [])]
            if kind == "elem":
                d.append(f"       01  {pname} PIC X({plen}).")
                d += self.cond_lines(cl, 15)
            elif kind == "group":
                d.append(f"       01  {pname}.")
                d += self.cond_lines(cl, 11)
                d += ["           05 G1 PIC X(2).", "           05 G2 PIC X(3)."]
            else:
                d.append("       01  TB.")
                d.append(f"           05 {pname} PIC X({plen}) OCCURS 3.")
                d += self.cond_lines(cl, 15)
        return d

    @staticmethod
    def cond_lines(cl, indent):
        out = []
        for c in cl:
            out += E.wrap(c, indent=indent)
        return out

    def program(self):
        """(source, expected lines); self.steps filled."""
        proc, exp = [], []
        # initial contents: spaces everywhere
        proc += E.wrap("MOVE SPACES TO X1 X4 X7 G TB")
        for s in range(self.k):
            out, e, rec = self.step(s)
            self.steps.append(rec)
            exp += e
            for ln in out:
                proc += E.wrap(ln)
        hdr = E.header("DMAXA", self.data())
        if self.seq:
            i = hdr.index("       DATA DIVISION.")
            hdr[i:i] = ["       ENVIRONMENT DIVISION.", "       CONFIGURATION SECTION.", "       OBJECT-COMPUTER. X",
                        "           PROGRAM COLLATING SEQUENCE IS ALPH.", "       SPECIAL-NAMES.",
                        f"           ALPHABET ALPH IS '{REVERSED}'."]
        src = "\n".join(E.check_lines(hdr + proc + ["           STOP RUN."])) + "\n"
        return src, exp

    def judge(self, D, base, tally):
        src, exp = self.program()
        s1, g = gnucobol(D, src, base, self.COBC)
        if s1 != "ran":
            return s1, g
        s2, m, signal = model(D, base, self.FE)
        if s2 != "ran":
            return s2, m
        if not signal.startswith("stop:"):
            return "lean-signal", signal
        tally["lines"] = tally.get("lines", 0) + len(exp)
        if m != exp:
            i = E.first_diff(exp, m)
            st = self.steps[step_of(i[2])] if i and step_of(i[2]) is not None else None
            return "mismatch", f"line {i}: IBM vs model ({st})"
        if g != exp:
            i = E.first_diff(exp, g)
            return "gnucobol-mismatch", f"line {i}: IBM vs GnuCOBOL"
        return "ok", ""

    def coverage(self, cov):
        for s in self.steps:
            for f in [s["kind"], "parent_" + s["parent"]] + ["value_" + v for v in s["values"]] + \
                     (["seq"] if s["seq"] else []):
                cov[f] = cov.get(f, 0) + 1


# ------------------------------------------------------------------ arithmetic parts
# operand items: name, PICTURE, places, signed, usage, value range (scaled)
NUM_ITEMS = [("I1", "S9(3)", 0, True, "", (-150, 150)), ("I2", "9(3)", 0, False, "", (0, 300)),
             ("I3", "S9(3)", 0, True, " COMP-3", (-60, 60)), ("D1", "S9V9", 1, True, "", (-99, 99)),
             ("D2", "S99V99", 2, True, "", (-2500, 2500)), ("D3", "9V9(3)", 3, False, "", (0, 9999)),
             ("D4", "S9(3)V9", 1, True, " COMP-3", (-999, 999)), ("D5", "S9V9(4)", 4, True, "", (-20000, 20000))]
NUM = {it[0]: it for it in NUM_ITEMS}
NUM_LITS = ["2", "3", "7", "12", "1.5", "0.25", "2.125", "0.3", "1.75", "4.0"]
# intrinsic functions (IBM PG "Intrinsic functions evaluated in fixed-point arithmetic"): the mixed functions, whose
# outer-dmax equals their inner-dmax, and the functions the table lists with inner-dmax 0
MIXED_FNS = ("MAX", "MIN", "SUM", "RANGE", "REM", "ABS")
INNER0_FNS = ("DATE-OF-INTEGER", "DATE-TO-YYYYMMDD", "DAY-OF-INTEGER", "DAY-TO-YYYYDDD", "FACTORIAL",
              "INTEGER-OF-DATE", "INTEGER-OF-DAY", "MOD", "YEAR-TO-YYYY")
# the resolver before inr-fix (snapshot 2106Z) gave a COMPUTE's function arguments the dmax of its numeric receivers and
# of these places of its operands (its dScalesIn: the arguments of every function count but those of these)
OLD_IN0_FNS = ("FACTORIAL", "INTEGER-OF-DATE", "DATE-OF-INTEGER", "INTEGER-OF-DAY", "DAY-OF-INTEGER", "ORD-MAX",
               "ORD-MIN")


def places_of_lit(t):
    return len(t.split(".")[1]) if "." in t else 0


def trunc(v, k):
    """The rational v truncated toward zero to k decimal places."""
    s = 10 ** k
    q = abs(v.numerator) * s // v.denominator
    return Fraction(q if v >= 0 else -q, s)


def lit_text(v, k):
    """A literal (for MOVE) of the value v, which has at most k places, written with k places."""
    s = 10 ** k
    n = abs(v) * s
    assert n.denominator == 1, (v, k)
    t = str(n.numerator).rjust(k + 1, "0")
    t = t if k == 0 else t[:-k] + "." + t[-k:]
    return f"-{t}" if v < 0 else t


class Ar:
    """Expression trees: ("item", name), ("lit", text), ("add" | "sub" | "mul" | "div", a, b), ("neg", a),
    ("fn", NAME, [args]).
    IBM's fixed-point rules (Enterprise COBOL 6.4 Programming Guide, "Fixed-point data and intermediate results"):
    + and - carry the larger number of places, * their sum, / "(d2 - d1) or dmax, whichever is greater" places
    (d2 the dividend's, d1 the divisor's; one more with ROUNDED), the quotient truncated. old=True: the resolver's
    rule before the F1 fix, max(d1, dmax) (+ 1 with ROUNDED). A function's arguments are computed with its
    inner-dmax ("Terminology used for intermediate results"; Language Reference "Arguments": the computation of an
    argument expression "is affected by other arguments for that function", and by nothing outside it), without the
    ROUNDED place; argdm (not None): the resolver's rule before inr-fix, every argument with the dmax argdm and the
    statement's ROUNDED place. INTEGER, INTEGER-PART, MOD: outer-dmax 0, value floor / truncation / MOD of integers;
    MAX, MIN, SUM, RANGE, REM, ABS (mixed): outer-dmax = inner-dmax, the result's places the most of the
    arguments'. GPREC (parts fnarg and fncond): the places of a quotient for exact=True (GnuCOBOL's line), None = exact;
    GnuCOBOL divides with many but finitely many digits, which INTEGER of A * (B / A) shows."""
    GPREC = None

    @staticmethod
    def text(x):
        k = x[0]
        if k in ("item", "lit"):
            return x[1]
        if k == "fn":
            return f"FUNCTION {x[1]} (" + ", ".join(Ar.text(a) for a in x[2]) + ")"
        if k == "neg":
            return f"(- {Ar.wrapped(x[1])})"
        op = {"add": "+", "sub": "-", "mul": "*", "div": "/"}[k]
        return f"{Ar.wrapped(x[1])} {op} {Ar.wrapped(x[2])}"

    @staticmethod
    def wrapped(x):
        t = Ar.text(x)
        return t if x[0] in ("item", "lit", "neg", "fn") else f"({t})"

    @staticmethod
    def dsc(x):
        """Places of the operands outside divisors (what counts for IBM's dmax)."""
        k = x[0]
        if k == "item":
            return [NUM[x[1]][2]]
        if k == "lit":
            return [places_of_lit(x[1])]
        if k == "fn":
            # the integer functions INTEGER, INTEGER-PART, MOD: outer-dmax 0 (IBM); a mixed function: its inner-dmax
            return [p for a in x[2] for p in Ar.dsc(a)] if x[1] in MIXED_FNS else [0]
        if k in ("neg", "div"):
            return Ar.dsc(x[1])
        return Ar.dsc(x[1]) + Ar.dsc(x[2])

    @staticmethod
    def dsc_old(x):
        """The places the resolver before inr-fix counted for a COMPUTE's function arguments (its dScalesIn)."""
        k = x[0]
        if k == "item":
            return [NUM[x[1]][2]]
        if k == "lit":
            return [places_of_lit(x[1])]
        if k == "fn":
            return [0] if x[1] in OLD_IN0_FNS else [p for a in x[2] for p in Ar.dsc_old(a)]
        if k in ("neg", "div"):
            return Ar.dsc_old(x[1])
        return Ar.dsc_old(x[1]) + Ar.dsc_old(x[2])

    @staticmethod
    def inner(x):
        """IBM's inner-dmax of the function x: the most places of its arguments (0 for the table's 0 rows)."""
        return 0 if x[1] in INNER0_FNS else max([0] + [p for a in x[2] for p in Ar.dsc(a)])

    @staticmethod
    def scale(x, dmax, rounded, old=False, argdm=None):
        k = x[0]
        if k == "item":
            return NUM[x[1]][2]
        if k == "lit":
            return places_of_lit(x[1])
        if k == "fn":
            if x[1] not in MIXED_FNS:
                return 0
            dm, rd = (Ar.inner(x), False) if argdm is None else (argdm, rounded)
            return max(Ar.scale(a, dm, rd, old, argdm) for a in x[2])
        if k == "neg":
            return Ar.scale(x[1], dmax, rounded, old, argdm)
        a = Ar.scale(x[1], dmax, rounded, old, argdm)
        b = Ar.scale(x[2], dmax, rounded, old, argdm)
        if k in ("add", "sub"):
            return max(a, b)
        if k == "mul":
            return a + b
        return (max(b, dmax) if old else max(max(a, 0) - max(b, 0), dmax)) + (1 if rounded else 0)

    @staticmethod
    def value(x, env, dmax, rounded, old=False, exact=False, argdm=None):
        """The value (Fraction) by IBM's rule (old: the resolver's old one; exact: no quotient truncated; argdm: the
        function arguments' dmax before inr-fix); ZeroDivisionError for a zero divisor."""
        k = x[0]
        if k == "item":
            return Fraction(env[x[1]], 10 ** NUM[x[1]][2])
        if k == "lit":
            return Fraction(x[1])
        if k == "fn":
            dm, rd = (Ar.inner(x), False) if argdm is None else (argdm, rounded)
            args = [Ar.value(a, env, dm, rd, old, exact, argdm) for a in x[2]]
            if x[1] == "INTEGER":
                return Fraction(math.floor(args[0]))
            if x[1] == "INTEGER-PART":
                return Fraction(int(args[0]))
            if x[1] == "MAX":
                return max(args)
            if x[1] == "MIN":
                return min(args)
            if x[1] == "SUM":
                return sum(args, Fraction(0))
            if x[1] == "RANGE":
                return max(args) - min(args)
            if x[1] == "ABS":
                return abs(args[0])
            if args[1] == 0:
                raise ZeroDivisionError
            if x[1] == "REM":
                # IBM: argument-1 minus argument-2 times the quotient with its noninteger digits removed
                return args[0] - args[1] * int(args[0] / args[1])
            # MOD of integers: argument-1 - argument-2 * FUNCTION INTEGER (argument-1 / argument-2)
            return args[0] - args[1] * math.floor(args[0] / args[1])
        if k == "neg":
            return -Ar.value(x[1], env, dmax, rounded, old, exact, argdm)
        a = Ar.value(x[1], env, dmax, rounded, old, exact, argdm)
        b = Ar.value(x[2], env, dmax, rounded, old, exact, argdm)
        if k == "add":
            return a + b
        if k == "sub":
            return a - b
        if k == "mul":
            return a * b
        if b == 0:
            raise ZeroDivisionError
        if exact:
            return a / b if Ar.GPREC is None else trunc(a / b, Ar.GPREC)
        return trunc(a / b, Ar.scale(x, dmax, rounded, old, argdm))

    @staticmethod
    def fn_divs(x, dmax, rounded, argdm=None, infn=False):
        """The scales of the divisions of x inside function arguments, in order (argdm as for value)."""
        k = x[0]
        if k in ("item", "lit"):
            return []
        if k == "fn":
            dm, rd = (Ar.inner(x), False) if argdm is None else (argdm, rounded)
            return [s for a in x[2] for s in Ar.fn_divs(a, dm, rd, argdm, True)]
        if k == "neg":
            return Ar.fn_divs(x[1], dmax, rounded, argdm, infn)
        here = [Ar.scale(x, dmax, rounded, argdm=argdm)] if k == "div" and infn else []
        return here + Ar.fn_divs(x[1], dmax, rounded, argdm, infn) + Ar.fn_divs(x[2], dmax, rounded, argdm, infn)

    @staticmethod
    def neutral(x, dmax, rounded):
        """Every division of x has the same scale under IBM's rule and the old one (so both give one value)."""
        k = x[0]
        if k in ("item", "lit"):
            return True
        if k == "fn":
            return all(Ar.neutral(a, Ar.inner(x), False) for a in x[2])
        if k == "neg":
            return Ar.neutral(x[1], dmax, rounded)
        if k == "div" and Ar.scale(x, dmax, rounded) != Ar.scale(x, dmax, rounded, old=True):
            return False
        return Ar.neutral(x[1], dmax, rounded) and Ar.neutral(x[2], dmax, rounded)

    @staticmethod
    def items(x, out):
        if x[0] == "item":
            out.add(x[1])
        for c in x[1:]:
            if isinstance(c, tuple):
                Ar.items(c, out)
            elif isinstance(c, list):
                for a in c:
                    Ar.items(a, out)
        return out


class ArithGen:
    """Shared parts of the arithmetic generators: operands, expressions with a division, fresh values by MOVE."""
    COBC = E.PLAIN_COBC
    FE = ["--profile", "gnucobol", "--trunc", "std"]
    # True: every division of a generated expression keeps one scale under IBM's rule and the resolver's old one
    # (Ar.neutral), expressions that do not are drawn again (the tests of stages B to D, before the F1 fix); since the
    # F1 fix every expression is kept
    F1_NEUTRAL = False

    def __init__(self, rng, k):
        self.rng, self.k = rng, k
        self.env = {nm: 0 for nm in NUM}
        self.steps = []
        self.resampled = 0

    def operand(self):
        rng = self.rng
        if rng.random() < 0.7:
            return ("item", rng.choice(list(NUM)))
        return ("lit", rng.choice(NUM_LITS))

    def div_expr(self):
        """An expression with a division and at least one item (GnuCOBOL 3.2 compares a negative constant
        expression wrongly, G-negconst): (tree, shape)."""
        while True:
            x, shape = self.div_shape()
            if Ar.items(x, set()):
                return x, shape

    def div_shape(self):
        rng = self.rng
        o = self.operand
        shape = rng.choice(["div", "div", "sumdiv", "divsum", "divmul", "muldiv", "nested", "divby", "negdiv", "subdiv"])
        if shape == "div":
            return ("div", o(), o()), shape
        if shape == "sumdiv":
            return ("div", ("add", o(), o()), o()), shape
        if shape == "divsum":
            return ("add", ("div", o(), o()), o()), shape
        if shape == "divmul":
            return ("mul", ("div", o(), o()), o()), shape
        if shape == "muldiv":
            return ("div", ("mul", o(), o()), o()), shape
        if shape == "nested":
            return ("div", ("div", o(), o()), o()), shape
        if shape == "divby":
            return ("div", o(), ("add", o(), ("lit", "1"))), shape
        if shape == "negdiv":
            return ("neg", ("div", o(), o())), shape
        return ("sub", o(), ("div", o(), o())), shape

    def setup(self, names):
        out = []
        for nm in sorted(names):
            _, pic, f, signed, usage, (lo, hi) = NUM[nm]
            v = self.rng.randint(lo, hi)
            self.env[nm] = v
            out.append(f"MOVE {lit_text(Fraction(v, 10 ** f), f)} TO {nm}")
        return out

    def pick(self, make):
        """make() -> (made, [(expression, dmax, rounded), ...]): drawn again until fresh values give no zero divisor
        and (F1_NEUTRAL) only neutral divisions: (made, MOVE lines)."""
        for _ in range(400):
            made, checks = make()
            names = set()
            for x, _, _ in checks:
                Ar.items(x, names)
            saved = dict(self.env)
            lines = self.setup(names)
            try:
                ok = True
                for x, dm, rd in checks:
                    Ar.value(x, self.env, dm, rd)
                    if self.F1_NEUTRAL and not Ar.neutral(x, dm, rd):
                        ok = False
            except ZeroDivisionError:
                ok = False
            if ok:
                return made, lines
            self.env = saved
            self.resampled += 1
        raise RuntimeError("no expression found")

    def data(self):
        return [f"       01  {nm} PIC {pic}{usage} VALUE ZERO." for nm, pic, f, s, usage, _ in NUM_ITEMS] + self.extra_data()

    def extra_data(self):
        return []

    def judge_lines(self, D, base, src, exp, tally):
        """GnuCOBOL and the model on src; the model must give exp (the tester's IBM lines), GnuCOBOL too except the
        lines of steps in a G-class: status, detail."""
        s1, g = gnucobol(D, src, base, self.COBC)
        if s1 != "ran":
            return s1, g
        s2, m, signal = model(D, base, self.FE)
        if s2 != "ran":
            return s2, m
        if not signal.startswith("stop:"):
            return "lean-signal", signal
        tally["lines"] = tally.get("lines", 0) + len(exp)
        tally["resampled"] = tally.get("resampled", 0) + self.resampled
        info = {x["step"]: x for x in self.steps}
        if m != exp:
            i = E.first_diff(exp, m)
            return "mismatch", f"line {i}: IBM vs model ({info.get(step_of(i[1])) if i else None})"
        if len(g) != len(exp):
            return "gnucobol-mismatch", f"line counts {len(g)} vs {len(exp)}"
        glines = 0
        for a, b in zip(g, exp):
            if a == b:
                continue
            st = info.get(step_of(b))
            if st is None or not st["g"]:
                return "gnucobol-mismatch", f"step {step_of(b)}: GnuCOBOL {a!r} IBM {b!r} ({st})"
            glines += 1
            for c in st["g"]:
                tally.setdefault("g_lines", {})[c] = tally.setdefault("g_lines", {}).get(c, 0) + 1
        return ("ok-g" if glines else "ok"), ""


CMP = {"=": lambda a, b: a == b, ">": lambda a, b: a > b, "<": lambda a, b: a < b,
       ">=": lambda a, b: a >= b, "<=": lambda a, b: a <= b, "NOT =": lambda a, b: a != b}


class CondPart(ArithGen):
    """Part cond (see the module docstring)."""
    # GnuCOBOL without its OS/VS intermediate rules computes the quotients exactly (with many places); under
    # -std=ibm's arithmetic-osvs its own rules depart from IBM's in several ways (probe divprobe1.cob, g_evalown.cob)
    COBC = E.ARITH_COBC
    # an EVALUATE subject / object is evaluated on its own (IBM)
    EVAL_OWN = True
    # no negative literal and only signed items next to an expression: GnuCOBOL 3.2 compares a negative literal
    # or an unsigned item with a negative value wrongly (G-negconst, G-ucmpneg; ifn2-fix's pow_cases/g_negcmp.cob)
    REL_LITS = ["1.5", "0.33", "2", "1.666", "0.5", "0", "10.25", "3.1", "0.125"]
    OBJ_LITS = ["1.5", "0.33", "2", "1.6", "0", "1", "3.25", "0.25"]
    SIGNED = [nm for nm, pic, f, signed, usage, _ in NUM_ITEMS if signed]

    @staticmethod
    def rel_dmax(*xs):
        return max([0] + [p for x in xs for p in Ar.dsc(x)])

    def other(self):
        """The other comparand of a relation: a literal with places, a signed item, or a sum without a division."""
        rng = self.rng
        r = rng.random()
        if r < 0.45:
            return ("lit", rng.choice(self.REL_LITS))
        if r < 0.8:
            return ("item", rng.choice(self.SIGNED))
        return ("add", ("item", rng.choice(self.SIGNED)), ("lit", rng.choice(["0.05", "1", "0.125"])))

    def g_exact(self, x, outcome, truth):
        """["G-exactdiv"] when the outcome with x's quotients exact (GnuCOBOL -fno-arithmetic-osvs) differs from IBM's
        (quotients truncated to IBM's places), else []."""
        return ["G-exactdiv"] if outcome(Ar.value(x, self.env, 0, False, exact=True)) != truth else []

    def step(self, s):
        rng = self.rng
        lab = f"S{s:02d}"
        kind = rng.choice(["rel", "rel", "relr", "sign", "abbr", "eval", "eval", "evalobj"])
        rec = {"step": s, "kind": kind, "g": []}
        yes_no = [f"DISPLAY '{lab} Y|'", "ELSE", f"DISPLAY '{lab} N|'", "END-IF"]
        if kind in ("rel", "relr"):
            def make():
                e, shape = self.div_expr()
                o = self.other()
                return (e, o, rng.choice(list(CMP)), shape), [(e, self.rel_dmax(e, o), False), (o, 0, False)]
            (e, o, op, shape), lines = self.pick(make)
            if rng.random() < 0.4:
                # the other comparand: the expression's value under a dmax of 1 to 4 places, written with those places
                # (so the relation's dmax is that), compared by =, >= or <=
                k = max(self.rel_dmax(e), rng.choice([1, 2]))
                try:
                    v = Ar.value(e, self.env, k, False)
                    if (not self.F1_NEUTRAL or Ar.neutral(e, k, False)) and 0 <= v < 100 and \
                            Ar.scale(e, k, False) <= k:
                        o, op = ("lit", lit_text(v, k)), rng.choice(["=", ">=", "<="])
                except ZeroDivisionError:
                    pass
            dm = self.rel_dmax(e, o)
            ve, vo = Ar.value(e, self.env, dm, False), Ar.value(o, self.env, dm, False)
            if kind == "rel":
                text, outc = f"{Ar.text(e)} {op} {Ar.text(o)}", (lambda v: CMP[op](v, vo))
            else:
                text, outc = f"{Ar.text(o)} {op} {Ar.text(e)}", (lambda v: CMP[op](vo, v))
            truth = outc(ve)
            rec.update(dmax=dm, shape=shape, text=text, g=self.g_exact(e, outc, truth), f1=not Ar.neutral(e, dm, False))
            return lines + [f"IF {text}"] + yes_no, [f"{lab} {'Y' if truth else 'N'}|"], rec
        if kind == "sign":
            def make():
                e, shape = self.div_expr()
                return (e, shape), [(e, self.rel_dmax(e), False)]
            (e, shape), lines = self.pick(make)
            dm = self.rel_dmax(e)
            word = rng.choice(["POSITIVE", "NEGATIVE", "ZERO"])
            neg = rng.random() < 0.3
            f = {"POSITIVE": lambda v: v > 0, "NEGATIVE": lambda v: v < 0, "ZERO": lambda v: v == 0}[word]
            outc = lambda v: f(v) != neg  # noqa: E731
            truth = outc(Ar.value(e, self.env, dm, False))
            text = f"{Ar.text(e)} IS {'NOT ' if neg else ''}{word}"
            rec.update(dmax=dm, shape=shape, text=text, g=self.g_exact(e, outc, truth), f1=not Ar.neutral(e, dm, False))
            return lines + [f"IF {text}"] + yes_no, [f"{lab} {'Y' if truth else 'N'}|"], rec
        if kind == "abbr":
            lo, hi = ("lit", rng.choice(["0.5", "1", "1.25", "0.75"])), ("lit", rng.choice(["1.75", "2", "3.5", "10"]))

            def make():
                e, shape = self.div_expr()
                return (e, shape), [(e, self.rel_dmax(e, lo), False), (e, self.rel_dmax(e, hi), False)]
            (e, shape), lines = self.pick(make)
            # IBM: an abbreviated condition is handled as if not abbreviated: each relation with its own dmax
            d1, d2 = self.rel_dmax(e, lo), self.rel_dmax(e, hi)
            truth = Ar.value(e, self.env, d1, False) > Fraction(lo[1]) and Ar.value(e, self.env, d2, False) < Fraction(hi[1])
            text = f"{Ar.text(e)} > {lo[1]} AND < {hi[1]}"
            g = self.g_exact(e, lambda v: Fraction(lo[1]) < v < Fraction(hi[1]), truth)
            rec.update(dmax=max(d1, d2), shape=shape, text=text, g=g,
                       f1=not (Ar.neutral(e, d1, False) and Ar.neutral(e, d2, False)))
            return lines + [f"IF {text}"] + yes_no, [f"{lab} {'Y' if truth else 'N'}|"], rec
        # EVALUATE: the expression as the subject with literal / item objects (eval), or as the object of an item
        # subject (evalobj); WHEN o1 [THRU 9.75] / WHEN o2 / WHEN OTHER
        thru = rng.random() < 0.35
        hi = ("lit", "9.75")

        def make():
            e, shape = self.div_expr()
            objs = [("lit", rng.choice(self.OBJ_LITS)), ("lit", rng.choice(self.OBJ_LITS))]
            if rng.random() < 0.4:
                objs[1] = ("item", rng.choice(self.SIGNED))
            subj = ("item", rng.choice(self.SIGNED))
            pairs = [(e, o) for o in objs] if kind == "eval" else [(subj, e)]
            checks = [(e, self.rel_dmax(e), False)] + [(e, self.rel_dmax(a, b), False) for a, b in pairs] + \
                [(o, 0, False) for o in objs] + [(subj, 0, False)]
            if thru and kind == "eval":
                checks.append((e, self.rel_dmax(e, hi), False))
            return (e, shape, objs, subj), checks
        (e, shape, objs, subj), lines = self.pick(make)
        own_dm = self.rel_dmax(e)
        if rng.random() < 0.5:
            # a value where the two readings part: the expression with 1 or 2 more places than its own operands
            # (the dmax a relation with that many places would give it)
            k = min(own_dm + rng.choice([1, 2]), 6)
            try:
                v = trunc(Ar.value(e, self.env, k, False), k)
                ok = (not self.F1_NEUTRAL or Ar.neutral(e, k, False)) and abs(v) < 100
            except ZeroDivisionError:
                ok = False
            if ok and kind == "eval" and v >= 0:
                objs[0] = ("lit", lit_text(v, k))
            elif ok and kind == "evalobj" and NUM[subj[1]][2] >= k:
                f = NUM[subj[1]][2]
                lo_, hi_ = NUM[subj[1]][5]
                if lo_ <= v * 10 ** f <= hi_:
                    self.env[subj[1]] = int(v * 10 ** f)
                    lines.append(f"MOVE {lit_text(v, f)} TO {subj[1]}")
        if kind == "eval":
            when1 = f"WHEN {Ar.text(objs[0])}" + (f" THRU {hi[1]}" if thru else "")
            out = [f"EVALUATE {Ar.text(e)}", when1, f"DISPLAY '{lab} W1|'", f"WHEN {Ar.text(objs[1])}",
                   f"DISPLAY '{lab} W2|'", "WHEN OTHER", f"DISPLAY '{lab} O|'", "END-EVALUATE"]
            arm = self.eval_arm(e, objs, thru, hi, own=self.EVAL_OWN)
            ex_arm = self.eval_arm(e, objs, thru, hi, own=True, exact=True)
            text = f"EVALUATE {Ar.text(e)} {when1} WHEN {Ar.text(objs[1])}"
        else:
            out = [f"EVALUATE {subj[1]}", f"WHEN {Ar.text(e)}", f"DISPLAY '{lab} W1|'", "WHEN OTHER",
                   f"DISPLAY '{lab} O|'", "END-EVALUATE"]
            vs = Ar.value(subj, self.env, 0, False)
            own = Ar.value(e, self.env, self.rel_dmax(e), False)
            rel = Ar.value(e, self.env, self.rel_dmax(subj, e), False)
            arm = "W1" if vs == (own if self.EVAL_OWN else rel) else "O"
            ex_arm = "W1" if vs == Ar.value(e, self.env, 0, False, exact=True) else "O"
            text = f"EVALUATE {subj[1]} WHEN {Ar.text(e)}"
        rec.update(dmax=own_dm, shape=shape, text=text, g=["G-exactdiv"] if ex_arm != arm else [],
                   f1=not Ar.neutral(e, own_dm, False),
                   parts=(self.eval_arm(e, objs, thru, hi, own=True) != self.eval_arm(e, objs, thru, hi, own=False))
                   if kind == "eval" else (vs == own) != (vs == rel))
        return lines + out, [f"{lab} {arm}|"], rec

    def eval_arm(self, e, objs, thru, hi, own, exact=False):
        """The arm an EVALUATE of subject e takes: e evaluated on its own (own) or with each object's relation dmax
        (exact: its quotients exact)."""
        dm = (lambda o: self.rel_dmax(e)) if own else (lambda o: self.rel_dmax(e, o))
        val = lambda o: Ar.value(e, self.env, dm(o), False, exact=exact)  # noqa: E731
        v1, o1 = val(objs[0]), Ar.value(objs[0], self.env, 0, False)
        if thru:
            w1 = o1 <= v1 and val(hi) <= Fraction(hi[1])
        else:
            w1 = v1 == o1
        if w1:
            return "W1"
        return "W2" if val(objs[1]) == Ar.value(objs[1], self.env, 0, False) else "O"

    def program(self):
        proc, exp = [], []
        for s in range(self.k):
            out, e, rec = self.step(s)
            self.steps.append(rec)
            exp += e
            for ln in out:
                proc += E.wrap(ln)
        hdr = E.header("DMAXB", self.data())
        return "\n".join(E.check_lines(hdr + proc + ["           STOP RUN."])) + "\n", exp

    def judge(self, D, base, tally):
        src, exp = self.program()
        return self.judge_lines(D, base, src, exp, tally)

    def coverage(self, cov):
        for s in self.steps:
            for f in [s["kind"], f"dmax{s.get('dmax', 0)}", "shape_" + s.get("shape", "?")] + s["g"] + \
                     (["readings_part"] if s.get("parts") else []) + (["f1_scale"] if s.get("f1") else []):
                cov[f] = cov.get(f, 0) + 1


def round_half_away(v, k):
    """v rounded to k places, half away from zero (plain ROUNDED)."""
    s = 10 ** k
    q = int(abs(v) * s + Fraction(1, 2))
    return Fraction(q if v >= 0 else -q, s)


class ComputePart(ArithGen):
    """COMPUTE steps (parts edited, intfn, div): the receivers set to 77 by MOVE first, an expression with a division,
    the receivers displayed (numeric ones through a numeric-edited item); ON SIZE ERROR / NOT ON SIZE ERROR in some
    steps. The tester computes each expression's IBM value (Ar.value at IBM's dmax: the receivers' places, numeric-edited
    receivers' digit positions after the point included, and the operands' outside divisors; with ROUNDED one more place
    for a quotient). Mirror: the same program with each COMPUTE's expression replaced by an item M1 holding its IBM value
    (GnuCOBOL then only stores a given value). Checks: every model line equals the mirror's line; every line of GnuCOBOL's
    own run (-fno-arithmetic-osvs: exact quotients) too, except the lines of steps in G-exactdiv (a receiver stores another
    value when the quotients are exact)."""
    COBC = E.ARITH_COBC
    # numeric-edited receivers: name, PICTURE, digit positions after the point
    EDITED = [("E0", "-(5)9", 0), ("E1", "-(5)9.9", 1), ("E2", "-(5)9.99", 2), ("E3", "Z(4)9.999", 3), ("E4", "-(4)9.9(4)", 4)]
    # numeric receivers: name, PICTURE, places, numeric-edited picture showing it
    NUMR = [("N0", "S9(6)", 0, "-(6)9"), ("N1", "S9(5)V9", 1, "-(5)9.9"), ("N2", "S9(4)V99", 2, "-(4)9.99"),
            ("N4", "S9(3)V9(4)", 4, "-(3)9.9(4)")]
    LIMIT = Fraction(10 ** 4)

    def receivers(self):
        """[(name, places, edited?)] of one COMPUTE."""
        raise NotImplementedError

    def expression(self):
        """(tree, shape)."""
        return self.div_expr()

    def step(self, s):
        rng = self.rng
        lab = f"S{s:02d}"
        rcv = self.receivers()
        rounded = rng.random() < 0.25
        rdm = max([0] + [p for _, p, _ in rcv])

        def make():
            while True:
                e, shape = self.expression()
                if Ar.items(e, set()):
                    break
            return (e, shape), [(e, max([rdm] + Ar.dsc(e)), rounded)]
        for _ in range(50):
            (e, shape), lines = self.pick(make)
            dm = max([rdm] + Ar.dsc(e))
            v = Ar.value(e, self.env, dm, rounded)
            if abs(v) < self.LIMIT and Ar.scale(e, dm, rounded) <= 9:
                break
        else:
            raise RuntimeError("no value in range")
        exact = Ar.value(e, self.env, dm, rounded, exact=True)
        try:
            old = Ar.value(e, self.env, dm, rounded, old=True)
        except ZeroDivisionError:
            # (part fnarg) a divisor that is a function of a quotient truncated to 0 under the old rule
            old = None
        stored = lambda x, p: round_half_away(x, p) if rounded else trunc(x, p)  # noqa: E731
        g = ["G-exactdiv"] if any(stored(v, p) != stored(exact, p) for _, p, _ in rcv) or abs(exact) >= self.LIMIT else []
        rtext = " ".join(f"{n}{' ROUNDED' if rounded else ''}" for n, _, _ in rcv)
        moves = [f"MOVE 77 TO {n}" for n, _, _ in rcv]
        size = rng.random() < 0.3
        tail = f" ON SIZE ERROR DISPLAY '{lab} Z|' NOT ON SIZE ERROR DISPLAY '{lab} N|' END-COMPUTE" if size else ""
        show = []
        for n, p, ed in rcv:
            if ed:
                show.append(f"DISPLAY '{lab} [' {n} ']|'")
            else:
                show += [f"MOVE {n} TO E{n}", f"DISPLAY '{lab} [' E{n} ']|'"]
        orig = lines + moves + [f"COMPUTE {rtext} = {Ar.text(e)}{tail}"] + show
        mir = lines + [f"MOVE {lit_text(v, Ar.scale(e, dm, rounded))} TO M1"] + moves + [f"COMPUTE {rtext} = M1{tail}"] + show
        rec = {"step": s, "kind": "compute", "dmax": dm, "shape": shape, "text": f"COMPUTE {rtext} = {Ar.text(e)}",
               "rounded": rounded, "g": g, "edited": any(ed for _, _, ed in rcv), "nrcv": len(rcv),
               # a division's scale differs under the old rule max(d1, dmax); a receiver would store another value
               "f1": not Ar.neutral(e, dm, rounded),
               "f1v": old is None or any(stored(v, p) != stored(old, p) for _, p, _ in rcv)}
        rec.update(self.extra_rec(e, dm, rounded, rcv, v, stored))
        return orig, mir, rec

    def extra_rec(self, e, dm, rounded, rcv, v, stored):
        """More fields of a step's record (part fnarg); none here."""
        return {}

    def extra_data(self):
        d = [f"       01  {n} PIC {pic}." for n, pic, _ in self.EDITED]
        for n, pic, p, epic in self.NUMR:
            d += [f"       01  {n} PIC {pic} VALUE ZERO.", f"       01  E{n} PIC {epic}."]
        return d + ["       01  M1 PIC S9(9)V9(9) VALUE ZERO."]

    def program(self):
        proc, procm = [], []
        for s in range(self.k):
            orig, mir, rec = self.step(s)
            self.steps.append(rec)
            for ln in orig:
                proc += E.wrap(ln)
            for ln in mir:
                procm += E.wrap(ln)
        hdr = E.header("DMAXC", self.data())
        src = "\n".join(E.check_lines(hdr + proc + ["           STOP RUN."])) + "\n"
        srcm = "\n".join(E.check_lines(hdr + procm + ["           STOP RUN."])) + "\n"
        return src, srcm

    def judge(self, D, base, tally):
        src, srcm = self.program()
        s1, g = gnucobol(D, src, base, self.COBC)
        if s1 != "ran":
            return s1, g
        s2, m, signal = model(D, base, self.FE)
        if s2 != "ran":
            return s2, m
        if not signal.startswith("stop:"):
            return "lean-signal", signal
        s3, mi = gnucobol(D, srcm, base + "_mirror", self.COBC)
        if s3 != "ran":
            return "mirror-" + s3, mi
        tally["lines"] = tally.get("lines", 0) + len(m)
        tally["resampled"] = tally.get("resampled", 0) + self.resampled
        info = {x["step"]: x for x in self.steps}
        if m != mi:
            i = E.first_diff(mi, m)
            return "mirror", f"line {i}: mirror vs model ({info.get(step_of(i[1])) if i else None})"
        if len(g) != len(m):
            return "gnucobol-mismatch", f"line counts {len(g)} vs {len(m)}"
        glines = 0
        for a, b in zip(g, m):
            if a == b:
                continue
            st = info.get(step_of(b))
            if st is None or not st["g"]:
                return "gnucobol-mismatch", f"step {step_of(b)}: GnuCOBOL {a!r} model {b!r} ({st})"
            glines += 1
            for c in st["g"]:
                tally.setdefault("g_lines", {})[c] = tally.setdefault("g_lines", {}).get(c, 0) + 1
        return ("ok-g" if glines else "ok"), ""

    def coverage(self, cov):
        for s in self.steps:
            feats = [s["kind"], f"dmax{s['dmax']}", "shape_" + s["shape"], f"receivers{s['nrcv']}"] + s["g"] + \
                (["rounded"] if s["rounded"] else []) + (["edited"] if s["edited"] else []) + \
                (["f1_scale"] if s["f1"] else []) + (["f1_value"] if s["f1v"] else [])
            for f in feats:
                cov[f] = cov.get(f, 0) + 1


class EditedPart(ComputePart):
    """Part edited (see the module docstring)."""

    def receivers(self):
        rng = self.rng
        n, pic, p = rng.choice(self.EDITED[1:])
        rcv = [(n, p, True)]
        if rng.random() < 0.3:
            m, _, q, _ = rng.choice([r for r in self.NUMR if r[2] < p])
            rcv.append((m, q, False))
        return rcv

    def operand(self):
        rng = self.rng
        if rng.random() < 0.75:
            return ("item", rng.choice(["I1", "I2", "I3"] if rng.random() < 0.7 else list(NUM)))
        return ("lit", rng.choice(["2", "3", "7", "12", "1.5", "0.25"]))


class IntfnPart(ComputePart):
    """Part intfn (see the module docstring)."""
    INT_FNS = ["INTEGER", "INTEGER-PART", "MOD"]

    def receivers(self):
        rng = self.rng
        if rng.random() < 0.6:
            n, _, p, _ = rng.choice(self.NUMR[:2])
            return [(n, p, False)]
        n, pic, p = rng.choice(self.EDITED[:2])
        return [(n, p, True)]

    def operand(self):
        rng = self.rng
        if rng.random() < 0.8:
            return ("item", rng.choice(["I1", "I2", "I3", "D1", "D4"]))
        return ("lit", rng.choice(["2", "3", "7", "12", "0.5"]))

    def fn(self):
        """An integer function: INTEGER / INTEGER-PART of a decimal item or sum (2 to 4 places), MOD of integers."""
        rng = self.rng
        name = rng.choice(self.INT_FNS)
        if name == "MOD":
            return ("fn", "MOD", [("item", rng.choice(["I1", "I3"])), ("lit", rng.choice(["3", "7", "-4"]))])
        x = ("item", rng.choice(["D2", "D3", "D5"]))
        if rng.random() < 0.3:
            x = ("add", x, ("item", rng.choice(["D3", "D5"])))
        return ("fn", name, [x])

    def expression(self):
        rng = self.rng
        o = self.operand
        f = self.fn()
        d = ("div", o(), o())
        shape = rng.choice(["fn+div", "fn*div", "div-fn", "div*k+fn", "fn-div*i"])
        if shape == "fn+div":
            return ("add", f, d), shape
        if shape == "fn*div":
            return ("mul", f, d), shape
        if shape == "div-fn":
            return ("sub", d, f), shape
        if shape == "div*k+fn":
            return ("add", ("mul", d, ("lit", rng.choice(["10", "100", "3"]))), f), shape
        return ("sub", f, ("mul", d, ("item", rng.choice(["I1", "D1"])))), shape


class DivPart(ComputePart):
    """Part div (see the module docstring)."""

    def receivers(self):
        rng = self.rng
        if rng.random() < 0.2:
            n, pic, p = rng.choice(self.EDITED)
            return [(n, p, True)]
        rs = rng.sample(self.NUMR[:3] if rng.random() < 0.7 else self.NUMR, rng.choice([1, 1, 2]))
        return [(n, p, False) for n, _, p, _ in rs]

    def operand(self):
        # operands with few places weighted, so that dmax is often below a divisor's places (where the two rules part)
        rng = self.rng
        if rng.random() < 0.75:
            return ("item", rng.choice(["I1", "I2", "I3", "D1", "D4"] if rng.random() < 0.7 else list(NUM)))
        return ("lit", rng.choice(NUM_LITS))

    def expression(self):
        rng = self.rng
        o = self.operand
        deep = ("item", rng.choice(["D3", "D5"]))
        shape = rng.choice(["alone", "alone", "deepdiv", "deepdiv*", "prod/", "prod/*", "nested", "by-sum", "div+div",
                            "shape"])
        if shape == "alone":
            return ("div", o(), o()), shape
        if shape == "deepdiv":
            return ("div", o(), deep), shape
        if shape == "deepdiv*":
            return ("mul", ("div", o(), deep), ("lit", rng.choice(["30", "100", "7"]))), shape
        if shape == "prod/":
            return ("div", ("mul", o(), o()), o()), shape
        if shape == "prod/*":
            return ("mul", ("div", ("mul", o(), o()), o()), ("lit", rng.choice(["10", "100"]))), shape
        if shape == "nested":
            return ("div", ("div", o(), o()), o()), shape
        if shape == "by-sum":
            return ("div", o(), ("add", o(), ("lit", "1"))), shape
        if shape == "div+div":
            return ("add", ("div", o(), o()), ("div", o(), o())), shape
        return self.div_shape()


class FnargPart(ComputePart):
    """Part fnarg (see the module docstring)."""
    FNS = ["MAX", "MIN", "SUM", "RANGE", "REM", "ABS", "INTEGER", "INTEGER-PART"]

    def __init__(self, rng, k):
        super().__init__(rng, k)
        # GnuCOBOL's line (G-exactdiv) from quotients with 37 places: it divides with about 38 digits, not exactly
        Ar.GPREC = 37

    def receivers(self):
        # receivers with more places than the arguments, where the statement's dmax and the inner-dmax part
        rng = self.rng
        if rng.random() < 0.2:
            n, pic, p = rng.choice(self.EDITED[2:])
            return [(n, p, True)]
        rs = rng.sample(self.NUMR[2:] if rng.random() < 0.7 else self.NUMR, rng.choice([1, 1, 2]))
        return [(n, p, False) for n, _, p, _ in rs]

    def operand(self):
        rng = self.rng
        if rng.random() < 0.75:
            return ("item", rng.choice(["I1", "I2", "I3", "D1", "D4"] if rng.random() < 0.7 else list(NUM)))
        return ("lit", rng.choice(["2", "3", "7", "12", "1.5", "0.25"]))

    def arg_div(self):
        """A function argument with a division. Its text never starts with "(": after an item argument the compilers
        would read "I2, (...)" as a subscript of I2."""
        rng = self.rng
        o = self.operand
        shape = rng.choice(["div", "div", "divprod", "adddiv", "muldiv"])
        if shape == "div":
            return ("div", o(), o())
        if shape == "divprod":
            return ("div", o(), ("mul", o(), o()))
        if shape == "adddiv":
            return ("add", o(), ("div", o(), o()))
        return ("mul", o(), ("div", o(), o()))

    def fn(self, depth=0):
        """A function with a division in an argument; in some, another argument is such a function (nested)."""
        rng = self.rng
        name = rng.choice(self.FNS)
        if name in ("ABS", "INTEGER", "INTEGER-PART"):
            return ("fn", name, [self.arg_div()])
        if name == "REM":
            return ("fn", "REM", [self.arg_div(), self.operand()] if rng.random() < 0.7 else [self.operand(), self.arg_div()])
        args = [self.arg_div()] + [self.operand() for _ in range(rng.choice([1, 1, 2]))]
        if depth == 0 and rng.random() < 0.25:
            args[-1] = self.fn(1)
        rng.shuffle(args)
        return ("fn", name, args)

    def expression(self):
        rng = self.rng
        o = self.operand
        shape = rng.choice(["fn", "fn", "fn*k", "fn+o", "fn/o", "o-fn", "modint"])
        if shape == "fn":
            return self.fn(), shape
        if shape == "fn*k":
            return ("mul", self.fn(), ("lit", rng.choice(["10", "100", "3"]))), shape
        if shape == "fn+o":
            return ("add", self.fn(), o()), shape
        if shape == "fn/o":
            return ("div", self.fn(), o()), shape
        if shape == "o-fn":
            return ("sub", o(), self.fn()), shape
        # MOD of an integer function of an expression with a division (NIST IF124A's shape)
        return ("fn", "MOD", [("fn", rng.choice(["INTEGER", "INTEGER-PART"]), [self.arg_div()]),
                              ("lit", rng.choice(["3", "7", "-4"]))]), shape

    def extra_rec(self, e, dm, rounded, rcv, v, stored):
        # the resolver before inr-fix: every argument with the numeric receivers' places and dScalesIn's, and ROUNDED's
        # extra place
        old_in = max([0] + [p for _, p, ed in rcv if not ed] + Ar.dsc_old(e))
        try:
            vo = Ar.value(e, self.env, dm, rounded, argdm=old_in)
        except ZeroDivisionError:
            vo = None
        return {"r1": Ar.fn_divs(e, dm, rounded) != Ar.fn_divs(e, dm, rounded, argdm=old_in),
                "r1v": vo is None or any(stored(v, p) != stored(vo, p) for _, p, _ in rcv)}

    def coverage(self, cov):
        super().coverage(cov)
        for s in self.steps:
            for f in (["r1_scale"] if s["r1"] else []) + (["r1_value"] if s["r1v"] else []):
                cov[f] = cov.get(f, 0) + 1


class FncondPart(CondPart):
    """Part fncond (see the module docstring)."""

    def __init__(self, rng, k):
        super().__init__(rng, k)
        self.fns = FnargPart(rng, k)
        self.last = None

    def div_expr(self):
        rng = self.rng
        while True:
            shape = rng.choice(["fn", "fn", "fn", "fn+o", "fn*k", "modint"])
            if shape == "modint":
                x = ("fn", "MOD", [("fn", rng.choice(["INTEGER", "INTEGER-PART"]), [self.fns.arg_div()]),
                                   ("lit", rng.choice(["3", "7"]))])
            elif shape == "fn+o":
                x = ("add", self.fns.fn(), self.fns.operand())
            elif shape == "fn*k":
                x = ("mul", self.fns.fn(), ("lit", rng.choice(["10", "3"])))
            else:
                x = self.fns.fn()
            if Ar.items(x, set()):
                self.last = x
                return x, shape

    def step(self, s):
        for _ in range(50):
            saved = dict(self.env)
            try:
                out, exp, rec = super().step(s)
                break
            except ZeroDivisionError:
                # an EVALUATE subject that is also an operand of the expression got a value (the cond part's evalobj
                # MOVE) that makes a divisor 0: draw the step again, from the values before it
                self.env = saved
        else:
            raise RuntimeError("no step found")
        x, dm = self.last, rec.get("dmax", 0)
        # the resolver before inr-fix gave the arguments of a function in a condition the dmax 0
        try:
            rec["r1v"] = Ar.value(x, self.env, dm, False) != Ar.value(x, self.env, dm, False, argdm=0)
        except ZeroDivisionError:
            rec["r1v"] = True
        rec["r1"] = Ar.fn_divs(x, dm, False) != Ar.fn_divs(x, dm, False, argdm=0)
        return out, exp, rec

    def coverage(self, cov):
        super().coverage(cov)
        for s in self.steps:
            for f in (["r1_scale"] if s["r1"] else []) + (["r1_value"] if s["r1v"] else []):
                cov[f] = cov.get(f, 0) + 1


# rounding modes: the two IBM has (plain ROUNDED, and none), the other COBOL 2014 modes
MODES_IBM = ("NEAREST-AWAY-FROM-ZERO", "TRUNCATION")
MODES_STD = ("AWAY-FROM-ZERO", "NEAREST-EVEN", "NEAREST-TOWARD-ZERO", "TOWARD-GREATER", "TOWARD-LESSER")


def round_mode(v, k, mode):
    """The rational v rounded to k places by a rounding mode (PROHIBITED: v itself, the caller checks it)."""
    s = 10 ** k
    x = v * s
    fl = math.floor(x)
    if x == fl or mode == "PROHIBITED":
        return v
    ce = fl + 1
    if mode == "TRUNCATION":
        r = int(x)
    elif mode == "AWAY-FROM-ZERO":
        r = ce if x > 0 else fl
    elif mode == "TOWARD-GREATER":
        r = ce
    elif mode == "TOWARD-LESSER":
        r = fl
    elif x - fl != Fraction(1, 2):
        r = ce if x - fl > Fraction(1, 2) else fl
    elif mode == "NEAREST-AWAY-FROM-ZERO":
        r = ce if x > 0 else fl
    elif mode == "NEAREST-TOWARD-ZERO":
        r = fl if x > 0 else ce
    else:
        r = fl if fl % 2 == 0 else ce
    return Fraction(r, s)


class RmodePart(ComputePart):
    """Part rmode (see the module docstring)."""
    # receiver capacity: integer digits per receiver (N0 S9(6), N1 S9(5)V9, N2 S9(4)V99, N4 S9(3)V9(4); E1 -(5)9.9,
    # E2 -(5)9.99, E4 -(4)9.9(4))
    CAP = {"N0": 6, "N1": 5, "N2": 4, "N4": 3, "E1": 5, "E2": 5, "E4": 4}

    def operand(self):
        rng = self.rng
        if rng.random() < 0.75:
            return ("item", rng.choice(["I1", "I2", "I3", "D1", "D4"] if rng.random() < 0.6 else list(NUM)))
        return ("lit", rng.choice(NUM_LITS))

    def receiver(self):
        rng = self.rng
        if rng.random() < 0.2:
            n, _, p = rng.choice([e for e in self.EDITED if e[0] in self.CAP])
            return (n, p, True)
        n, _, p, _ = rng.choice(self.NUMR)
        return (n, p, False)

    def step(self, s):
        rng = self.rng
        lab = f"S{s:02d}"
        kind = rng.choice(["lone", "lone", "lone2", "inner", "divide", "divinto", "prohibited"])
        rcv = [self.receiver()]
        if kind == "divinto":
            # DIVIDE ... INTO: the receiver is the dividend, a numeric item
            n, _, p, _ = rng.choice(self.NUMR)
            rcv = [(n, p, False)]
        if kind == "lone2":
            rcv.append(self.receiver())
            while rcv[1][0] == rcv[0][0]:
                rcv[1] = self.receiver()
        modes = [rng.choice(MODES_STD) if rng.random() < 0.8 else rng.choice(MODES_IBM) for _ in rcv]
        if kind == "prohibited":
            modes = ["PROHIBITED"]
        rdm = max([0] + [p for _, p, _ in rcv])
        o = self.operand

        def make():
            if kind == "inner":
                e = rng.choice([("mul", ("div", o(), o()), ("lit", rng.choice(["10", "3"]))),
                                ("add", ("div", o(), o()), o())])
            elif kind == "divinto":
                # a dividend item the receiver holds exactly (places and integer digits)
                e = ("div", ("item", rng.choice([nm for nm in ("I1", "D1", "D2", "D4") if NUM[nm][2] <= rcv[0][1]])), o())
            else:
                e = ("div", o(), o())
            return e, [(e, max([rdm] + Ar.dsc(e)), True)]
        for _ in range(200):
            e, lines = self.pick(make)
            dm = max([rdm] + Ar.dsc(e))
            q = Ar.value(e, self.env, dm, True, exact=True)
            if kind == "inner":
                # IBM's intermediate: the quotient truncated to max(d2 - d1, dmax) + 1 places (ROUNDED)
                base_v = Ar.value(e, self.env, dm, True)
            else:
                base_v = q
            new = [round_mode(base_v, p, m) for (_, p, _), m in zip(rcv, modes)]
            if all(abs(v) < 10 ** self.CAP[n] for (n, _, _), v in zip(rcv, new)) and abs(q) < self.LIMIT:
                break
        else:
            raise RuntimeError("no value in range")
        # the resolver before inr-fix: a COMPUTE's lone quotient truncated to max(d2 - d1, dmax) + 1 places first
        s1 = Ar.scale(e, dm, True)
        oldv = trunc(q, s1) if kind in ("lone", "lone2", "prohibited") else base_v
        old = [round_mode(oldv, p, m) for (_, p, _), m in zip(rcv, modes)]
        rtext = " ".join(f"{n} ROUNDED MODE {m}" for (n, _, _), m in zip(rcv, modes))
        moves = [f"MOVE 77 TO {n}" for n, _, _ in rcv]
        show = []
        for n, p, ed in rcv:
            if ed:
                show.append(f"DISPLAY '{lab} [' {n} ']|'")
            else:
                show += [f"MOVE {n} TO E{n}", f"DISPLAY '{lab} [' E{n} ']|'"]
        size = f" ON SIZE ERROR DISPLAY '{lab} Z|' NOT ON SIZE ERROR DISPLAY '{lab} N|'"
        if kind == "divide":
            stmt = f"DIVIDE {Ar.text(e[1])} BY {Ar.text(e[2])} GIVING {rtext}"
        elif kind == "divinto":
            n0 = rcv[0][0]
            stmt = f"DIVIDE {Ar.text(e[2])} INTO {n0} ROUNDED MODE {modes[0]}"
            # the receiver holds the dividend: MOVE it there instead of 77
            moves = [f"MOVE {Ar.text(e[1])} TO {n0}"]
        else:
            stmt = f"COMPUTE {rtext} = {Ar.text(e)}"
        if kind == "prohibited":
            n0, p0, _ = rcv[0]
            exact_ok = trunc(q, p0) == q
            orig = lines + moves + [stmt + size + " END-COMPUTE"] + show
            if exact_ok:
                mir = lines + moves + [f"MOVE {lit_text(q, p0)} TO M1", f"COMPUTE {n0} = M1{size} END-COMPUTE"] + show
            else:
                mir = lines + moves + [f"DISPLAY '{lab} Z|'"] + show
            # GnuCOBOL raises the size error whenever the quotient has more places than the receiver, even
            # all zero (G-prohibited; probe r2prohib1.cob: DIVIDE ... GIVING too)
            g = ["G-prohibited"] if exact_ok else []
            r2v = (trunc(oldv, p0) == oldv) != exact_ok
        else:
            orig = lines + moves + [stmt] + show
            mir = lines + moves
            for i, ((n, p, _), v) in enumerate(zip(rcv, new)):
                mir += [f"MOVE {lit_text(v, p)} TO M1", f"COMPUTE {n} = M1"]
            mir += show
            # GnuCOBOL (-fno-arithmetic-osvs) rounds the exact value
            g = ["G-exactdiv"] if any(round_mode(q, p, m) != v for (_, p, _), m, v in zip(rcv, modes, new)) else []
            r2v = old != new
        rec = {"step": s, "kind": kind, "dmax": dm, "modes": modes, "text": stmt, "g": g,
               "nrcv": len(rcv), "edited": any(ed for _, _, ed in rcv), "r2v": r2v}
        return orig, mir, rec

    def coverage(self, cov):
        for s in self.steps:
            feats = [s["kind"], f"receivers{s['nrcv']}"] + ["mode_" + m for m in s["modes"]] + s["g"] + \
                (["edited"] if s["edited"] else []) + (["r2_value"] if s["r2v"] else [])
            for f in feats:
                cov[f] = cov.get(f, 0) + 1


PART_CLASSES = {"all88": All88, "cond": CondPart, "edited": EditedPart, "intfn": IntfnPart, "div": DivPart,
                "fnarg": FnargPart, "fncond": FncondPart, "rmode": RmodePart}


# ------------------------------------------------------------------ driver
def run_files(args):
    """--run: each program both ways (GnuCOBOL -std=ibm; the front end --profile gnucobol), the lines side by
    side (classtest's format)."""
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    worst = 0
    for path in args.run:
        with open(path, encoding="latin-1") as fh:
            src = fh.read()
        base = os.path.join(args.out, "run_" + os.path.splitext(os.path.basename(path))[0])
        s1, g = gnucobol(D, src, base, E.PLAIN_COBC)
        status, m = s1, g
        if s1 == "ran":
            s2, m, signal = model(D, base, E.PLAIN_FE)
            if s2 != "ran":
                status = s2
            elif not signal.startswith("stop:"):
                status, m = "lean-signal", signal
            else:
                status = "ok" if g == m else "mismatch"
        print(f"== {path}: {status}")
        if status in ("ok", "mismatch"):
            for i in range(max(len(g), len(m))):
                a, b = (g[i] if i < len(g) else "<none>"), (m[i] if i < len(m) else "<none>")
                print(("   " if a == b else "!! ") + f"{show(a):<34} | {show(b)}")
        else:
            print(str(m)[:2000])
        worst = max(worst, 0 if status == "ok" else 1)
    return worst


def main():
    ap = E.arg_parser(__doc__, 60, 20)
    ap.add_argument("--part", choices=PARTS)
    ap.add_argument("--run", nargs="+", metavar="PROG.cob")
    args = ap.parse_args()
    if args.run:
        sys.exit(run_files(args))
    if not args.part:
        ap.error("--part is required without --run")
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    open(os.path.join(args.out, "details.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, statuses, cov, shown = {}, {}, {}, 0
    cls = PART_CLASSES[args.part]
    for p in range(args.n):
        gen = cls(rng, args.k)
        base = os.path.join(args.out, f"p{args.seed}_{p:04d}")
        status, detail = gen.judge(D, base, tally)
        gen.coverage(cov)
        statuses[status] = statuses.get(status, 0) + 1
        with open(os.path.join(args.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": p, "status": status}) + "\n")
        if status not in ("ok", "ok-g", "ok-unsup"):
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
    sys.exit(0 if all(s in ("ok", "ok-g", "ok-unsup") for s in statuses) else 1)


if __name__ == "__main__":
    main()

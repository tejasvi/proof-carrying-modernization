#!/usr/bin/env python3
"""Differential testing of exponentiation with an exponent that is an integral data item or
expression, not a literal (`COMPUTE R = B ** N`, `IF 1000 < 10 ** N + 1`).

IBM Enterprise COBOL 6.4 Programming Guide, "Fixed-point data and intermediate results",
Exponentiation: "When op2 is an integral data-name or variable, dmax decimal places and 30-dmax
(compatibility mode) ... integer places are used. op1 is multiplied by itself (|op2| - 1) times for
nonzero op2. If op2 is equal to 0, the result is 1. Division-by-0 and exponentiation SIZE ERROR
conditions apply." Its example ("Example: exponentiation in fixed-point arithmetic") moves the
power to an intermediate result ir4 of dmax decimal places, and for a negative exponent "Divide ir4
into 1 yielding ir5. ir5 has dmax decimal places"; the internal results before ir4 "are much more
precise, ensuring the most accurate result possible in ir4 or ir5". Language Reference, SIZE ERROR
phrases: zero raised to a negative number is a size error (an abend without ON SIZE ERROR). dmax of
a COMPUTE is the largest of the receivers' places and those of its operands outside divisors and
exponents; in a relation condition those of both comparands' operands.

Each random program sets its operand items by MOVE before every step and runs K steps:
  * COMPUTE Rj = an expression with one or two such powers (bases: integer and decimal items,
    signed and unsigned, literals, a sum, product or negation of items, a nested such power;
    exponents: signed and unsigned DISPLAY, COMP-3 and COMP items, their sums with a literal,
    differences, negations and doubles), alone, multiplied by an item or a literal, added to an
    item, minus a literal, negated, added to another, next to a power with a literal exponent;
    into one of four numeric receivers with 0, 1, 2 or 4 places (moved to 77 first), ON SIZE
    ERROR / NOT ON SIZE ERROR in most steps (always where the receiver overflows or a power divides
    by zero); the receiver is displayed through a numeric-edited item;
  * IF relations and sign conditions with such powers whose operands are all integers (dmax 0).

Checks (GnuCOBOL -std=ibm -fbinary-truncate -fno-arithmetic-osvs; the front end --profile
gnucobol --trunc std, then cobolrun):
  * IBM mirror: every model line equals GnuCOBOL's line for the mirror program, in which every such
    power is replaced by its IBM value computed by the tester (ir4: the exact power truncated to
    dmax places; for a negative exponent ir5: 1 / ir4 truncated to dmax places), MOVEd into an
    item M1 .. M4 first (GnuCOBOL 3.2 compares a negative literal or constant expression with an
    item wrongly, G-negconst), and a step whose power divides by zero displays its ON SIZE ERROR
    line instead;
  * every model line equals GnuCOBOL's line for the program itself, except the lines of steps in a
    class where GnuCOBOL departs from IBM (it computes the power exactly):
      G-powtrunc   ir4 drops digits of the exact power (COMPUTE R1 = DA ** N1 * 10, DA 1.5, N1 3:
                   IBM ir4 3.3, so 33.0; GnuCOBOL 33.7),
      G-pownegdiv  a negative exponent whose ir5 differs from 1 / the exact power,
      G-pow0neg    zero raised to a negative power (GnuCOBOL: 0 and no size error);
  * a quarter of the programs end with one statement that the front end must report unsupported
    with "exponent other than a small integer literal" (ok-unsup; GnuCOBOL only compiles these
    programs): ROUNDED, a numeric-edited receiver, an exponent with decimal places, a division in
    the exponent, a condition with a decimal operand, a power inside a function argument, a
    negative literal exponent, INTEGER of a decimal argument in the COMPUTE (IBM gives an integer
    function no decimal places in dmax, the resolver counts its argument's), a literal exponent
    over such a power (IBM then holds the outer power with dmax places too).
Statuses: ok, ok-g, ok-unsup, mismatch, mirror (a model line differs from the mirror's),
unsup-mismatch, and the ext_common statuses. Not generated: 0 ** 0 (unsupported in the model; IBM:
a size error, or 1 with a message), exponents beyond 64 and intermediate results beyond 12 digits
(the model's 30-digit check), a division by zero without ON SIZE ERROR or in a condition (an abend).
Never deletes files.

usage: powtest.py --root C --out DIR [--n N] [--seed S] [--k K] [--show K]
       powtest.py --root C --out DIR --run PROG.cob...
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

POW_COBC = E.ARITH_COBC
POW_FE = ["--profile", "gnucobol", "--trunc", "std"]
UNSUP_MSG = "exponent other than a small integer literal"

# operand items: name, PICTURE, places, signed, usage, value range (scaled)
BASES = [("IA", "S99", 0, True, "", (-12, 12)), ("IB", "9", 0, False, "", (0, 9)),
         ("DA", "S9V9", 1, True, "", (-25, 25)), ("DB", "S9V99", 2, True, "", (-199, 199)),
         ("DC", "9V9(3)", 3, False, "", (0, 2000)), ("DD", "S99V9", 1, True, "", (-125, 125))]
EXPS = [("N1", "S9", 0, True, "", (-4, 4)), ("N2", "9", 0, False, "", (0, 5)),
        ("N3", "S99", 0, True, "", (-6, 6)), ("N4", "S9", 0, True, " COMP-3", (-3, 3)),
        ("N5", "S9(4)", 0, True, " COMP", (-4, 4))]
ITEMS = {it[0]: it for it in BASES + EXPS}
INT_BASES = ["IA", "IB"]
RCVS = [("R0", 0, "S9(9)", "-(9)9"), ("R1", 1, "S9(8)V9", "-(8)9.9"),
        ("R2", 2, "S9(7)V99", "-(7)9.99"), ("R4", 4, "S9(5)V9(4)", "-(5)9.9(4)")]
BASE_LITS = ["2", "3", "10", "1.5", "0.5", "1.1"]
LIMIT = Fraction(10) ** 12


class SizeErr(Exception):
    """A power divides by zero (IBM: a size error)."""


class ZeroZero(Exception):
    """0 ** 0 (not generated)."""


class TooBig(Exception):
    """An exponent or an intermediate value outside the generated range."""


def trunc(v, k):
    """The rational v truncated toward zero to k decimal places."""
    s = 10 ** k
    q = abs(v.numerator) * s // v.denominator
    return Fraction(q if v >= 0 else -q, s)


def lit_text(v, k):
    """A signed literal (for MOVE) of the value v, which has at most k places, written with k."""
    s = 10 ** k
    n = abs(v) * s
    assert n.denominator == 1
    t = str(n.numerator).rjust(k + 1, "0")
    t = t if k == 0 else t[:-k] + "." + t[-k:]
    return f"-{t}" if v < 0 else t


def outer_pows(x, out):
    """The new-path powers of x not inside another one, left to right."""
    if x[0] == "pow":
        out.append(x)
        return out
    for c in x[1:]:
        if isinstance(c, tuple):
            outer_pows(c, out)
    return out


def mirror_of(x, info, k):
    """The mirror's view of x: (text with each outermost power replaced by an item M1, M2, ...,
    MOVE lines setting those items to the powers' IBM values). Items, not literals: GnuCOBOL 3.2
    compares a negative literal or constant expression with an item wrongly (G-negconst:
    IF (0 - 1331) < IA, IA -11, is false there)."""
    names, moves = {}, []
    for j, p in enumerate(outer_pows(x, []), 1):
        names[id(p)] = f"M{j}"
        moves.append(f"MOVE {lit_text(info['ibm'][id(p)], k)} TO M{j}")
    return Expr.text(x, names), moves


def scaled_text(v, f):
    """The literal for the scaled integer v at f places (for MOVE)."""
    t = str(abs(v)).rjust(f + 1, "0")
    t = t if f == 0 else t[:-f] + "." + t[-f:]
    return ("-" if v < 0 else "") + t


class Expr:
    """Expression trees: ("item", name), ("lit", text), ("add"|"sub"|"mul", a, b), ("neg", a),
    ("lpow", a, n) (a literal exponent 1..3), ("pow", a, e) (the new path)."""

    @staticmethod
    def text(x, mirror=None):
        """COBOL text; mirror: id(pow node) -> literal text replacing it."""
        k = x[0]
        if mirror is not None and k == "pow" and id(x) in mirror:
            return mirror[id(x)]
        if k == "item":
            return x[1]
        if k == "lit":
            return x[1]
        if k in ("add", "sub", "mul"):
            op = {"add": "+", "sub": "-", "mul": "*"}[k]
            return f"{Expr.wrapped(x[1], mirror)} {op} {Expr.wrapped(x[2], mirror)}"
        if k == "neg":
            return f"(- {Expr.wrapped(x[1], mirror)})"
        if k == "lpow":
            return f"{Expr.wrapped(x[1], mirror)} ** {x[2]}"
        if k == "pow":
            return f"{Expr.wrapped(x[1], mirror)} ** {Expr.wrapped(x[2], mirror)}"
        raise ValueError(x)

    @staticmethod
    def wrapped(x, mirror):
        t = Expr.text(x, mirror)
        return t if x[0] in ("item", "lit", "neg") or (mirror is not None and x[0] == "pow" and id(x) in mirror) \
            else f"({t})"

    @staticmethod
    def places(x):
        """Places of the operands outside exponents (IBM's dmax contribution)."""
        k = x[0]
        if k == "item":
            return ITEMS[x[1]][2]
        if k == "lit":
            return len(x[1].split(".")[1]) if "." in x[1] else 0
        if k in ("add", "sub", "mul"):
            return max(Expr.places(x[1]), Expr.places(x[2]))
        if k in ("neg", "lpow", "pow"):
            return Expr.places(x[1])
        raise ValueError(x)

    @staticmethod
    def items(x, out):
        k = x[0]
        if k == "item":
            out.add(x[1])
        elif k in ("add", "sub", "mul", "pow"):
            Expr.items(x[1], out)
            Expr.items(x[2], out)
        elif k in ("neg", "lpow"):
            Expr.items(x[1], out)
        return out


def evaluate(x, env, k, ibm, info):
    """Value of x: ibm=True with IBM's rule for the new path at dmax k (ir4 / ir5), else exact
    (GnuCOBOL; 0 ** negative is 0). info collects, per power, its IBM value (by node id) and the
    G-classes of the step."""
    t = x[0]
    if t == "item":
        nm, pic, f = ITEMS[x[1]][:3]
        return Fraction(env[x[1]], 10 ** f)
    if t == "lit":
        return Fraction(x[1])
    if t == "add":
        return evaluate(x[1], env, k, ibm, info) + evaluate(x[2], env, k, ibm, info)
    if t == "sub":
        return evaluate(x[1], env, k, ibm, info) - evaluate(x[2], env, k, ibm, info)
    if t == "mul":
        return evaluate(x[1], env, k, ibm, info) * evaluate(x[2], env, k, ibm, info)
    if t == "neg":
        return -evaluate(x[1], env, k, ibm, info)
    if t == "lpow":
        return evaluate(x[1], env, k, ibm, info) ** x[2]
    if t == "pow":
        b = evaluate(x[1], env, k, ibm, info)
        e = evaluate(x[2], env, k, ibm, info)
        assert e.denominator == 1
        n = e.numerator
        if abs(n) > 64:
            raise TooBig("exponent")
        if abs(b) >= LIMIT:
            raise TooBig("base")
        if n == 0:
            if b == 0:
                raise ZeroZero()
            v = Fraction(1)
            if ibm:
                info["ibm"][id(x)] = v
        elif not ibm:
            v = Fraction(0) if (b == 0 and n < 0) else b ** n
        else:
            exact = b ** abs(n)
            p = trunc(exact, k)
            if n > 0:
                v = p
                if p != exact:
                    info["g"].add("G-powtrunc")
            else:
                if p == 0:
                    # GnuCOBOL: 0 for 0 ** negative, else 1 / the exact power; IBM: a size error
                    info["g"].add("G-pow0neg" if b == 0 else "G-pownegdiv")
                    raise SizeErr()
                v = trunc(1 / p, k)
                if v != 1 / exact:
                    info["g"].add("G-pownegdiv")
            info["ibm"][id(x)] = v
        if abs(v) >= LIMIT:
            raise TooBig("power")
        return v
    raise ValueError(x)


class Gen:
    def __init__(self, rng, k):
        self.rng, self.k = rng, k
        self.env = {nm: 0 for nm in ITEMS}
        self.steps = []
        self.unsup = rng.random() < 0.25

    # -------------------------------------------------------------- expression shapes
    def item(self, names):
        return ("item", self.rng.choice(names))

    def base(self, depth, ints_only):
        rng = self.rng
        names = INT_BASES if ints_only else [b[0] for b in BASES]
        r = rng.random()
        if r < 0.45:
            return self.item(names)
        if r < 0.6:
            lits = ["2", "3", "10"] if ints_only else BASE_LITS
            return ("lit", rng.choice(lits))
        if r < 0.72:
            return ("add", self.item(names), ("lit", rng.choice(["1", "2"])))
        if r < 0.82:
            return ("mul", self.item(names), self.item(names))
        if r < 0.9 and depth == 0:
            return ("pow", self.base(1, ints_only), self.exponent())
        return ("neg", self.item(names))

    def exponent(self):
        rng = self.rng
        names = [e[0] for e in EXPS]
        r = rng.random()
        if r < 0.55:
            return self.item(names)
        if r < 0.7:
            return ("add", self.item(names), ("lit", rng.choice(["1", "2"])))
        if r < 0.8:
            return ("sub", self.item(names), self.item(names))
        if r < 0.9:
            return ("neg", self.item(names))
        return ("mul", self.item(names), ("lit", "2"))

    def power(self, ints_only):
        return ("pow", self.base(0, ints_only), self.exponent())

    def expr(self, ints_only):
        rng = self.rng
        names = INT_BASES if ints_only else [b[0] for b in BASES]
        p = self.power(ints_only)
        r = rng.random()
        if r < 0.3:
            return p
        if r < 0.42:
            return ("mul", p, self.item(names))
        if r < 0.52:
            return ("mul", p, ("lit", rng.choice(["10", "100", "3"] if ints_only else ["10", "0.5", "3"])))
        if r < 0.62:
            return ("add", self.item(names), p)
        if r < 0.7:
            return ("sub", p, ("lit", rng.choice(["1", "25"])))
        if r < 0.77:
            return ("neg", p)
        if r < 0.88:
            return ("add", p, self.power(ints_only))
        return ("add", ("lpow", self.item(names), rng.choice([1, 2, 3])), p)

    # -------------------------------------------------------------- values
    def setup(self, names):
        """MOVE fresh values into the items `names`: lines."""
        out = []
        for nm in sorted(names):
            _, pic, f, signed, usage, (lo, hi) = ITEMS[nm]
            v = self.rng.randint(lo, hi)
            if self.rng.random() < 0.08:
                v = 0
            self.env[nm] = v
            out.append(f"MOVE {scaled_text(v, f)} TO {nm}")
        return out

    def pick(self, make, ints_only, cond):
        """An expression and values for which neither evaluation raises ZeroZero / TooBig (and,
        in a condition, no SizeErr): (expr, setup lines, IBM info, size error?)."""
        for _ in range(200):
            x = make()
            names = Expr.items(x, set())
            saved = dict(self.env)
            lines = self.setup(names)
            k = self.k_of(x)
            info = {"ibm": {}, "g": set()}
            try:
                evaluate(x, self.env, k, False, {"ibm": {}, "g": set()})
                try:
                    evaluate(x, self.env, k, True, info)
                    serr = False
                except SizeErr:
                    serr = True
            except (ZeroZero, TooBig):
                self.env = saved
                continue
            if cond and serr:
                self.env = saved
                continue
            return x, lines, info, serr, k
        raise RuntimeError("no expression found")

    # -------------------------------------------------------------- steps
    def k_of(self, x):
        return self.cur_k(x)

    def step_compute(self, n):
        rng = self.rng
        rname, rf, rpic, epic = rng.choice(RCVS)
        self.cur_k = lambda x: max(rf, Expr.places(x), 0)
        x, lines, info, serr, k = self.pick(lambda: self.expr(False), False, False)
        ibm_val = None if serr else evaluate(x, self.env, k, True, {"ibm": {}, "g": set()})
        exact = evaluate(x, self.env, k, False, {"ibm": {}, "g": set()})
        cap = Fraction(10) ** (9 - rf)
        over = (ibm_val is not None and abs(trunc(ibm_val, rf)) >= cap) or abs(trunc(exact, rf)) >= cap
        size = bool(serr or over or (info["g"] and rng.random() < 0.5) or rng.random() < 0.6)
        tail = f" ON SIZE ERROR DISPLAY 'S{n:02d} Z|' NOT ON SIZE ERROR DISPLAY 'S{n:02d} N|' END-COMPUTE" \
            if size else ""
        orig = lines + [f"MOVE 77 TO {rname}", f"COMPUTE {rname} = {Expr.text(x)}{tail}"]
        if serr:
            mir = lines + [f"MOVE 77 TO {rname}", f"DISPLAY 'S{n:02d} Z|'"]
        else:
            mtext, moves = mirror_of(x, info, k)
            mir = lines + moves + [f"MOVE 77 TO {rname}", f"COMPUTE {rname} = {mtext}{tail}"]
        show_lines = [f"MOVE {rname} TO E{rname}", f"DISPLAY 'S{n:02d} R[' E{rname} ']'"]
        st = {"step": n, "kind": "compute", "rcv": rname, "dmax": k, "text": Expr.text(x),
              "size": size, "serr": serr, "over": bool(over), "g": sorted(info["g"]),
              "neg_exp": self._has_neg(x), "nested": self._nested(x),
              "lpow": self._has(x, "lpow"), "npow": self._count(x, "pow")}
        return orig + show_lines, mir + show_lines, st

    def step_cond(self, n):
        rng = self.rng
        self.cur_k = lambda x: 0
        if rng.random() < 0.7:
            x, lines, info, _, k = self.pick(lambda: self.expr(True), True, True)
            other_lit = rng.choice(["0", "1", "8", "100", "1000", "27"])
            # an item as the other comparand keeps its current value (no MOVE after the setup); a
            # signed one: GnuCOBOL compares an unsigned item with a negative value as if it were
            # positive (G-ucmpneg: PIC 9 holding 4 < -1331 is true there)
            other = ("lit", other_lit) if rng.random() < 0.6 else ("item", "IA")
            op = rng.choice(["=", ">", "<", ">=", "<=", "NOT ="])
            left = rng.random() < 0.5
            mtext, moves = mirror_of(x, info, 0)
            a, b = (Expr.text(x), Expr.text(other)) if left else (Expr.text(other), Expr.text(x))
            am, bm = (mtext, Expr.text(other)) if left else (Expr.text(other), mtext)
            cond, condm = f"{a} {op} {b}", f"{am} {op} {bm}"
            kind = "relation"
        else:
            x, lines, info, _, k = self.pick(lambda: self.expr(True), True, True)
            word = rng.choice(["POSITIVE", "NEGATIVE", "ZERO", "NOT POSITIVE", "NOT NEGATIVE", "NOT ZERO"])
            mtext, moves = mirror_of(x, info, 0)
            cond, condm = f"{Expr.text(x)} IS {word}", f"{mtext} IS {word}"
            kind = "sign"
        tail = [f"DISPLAY 'S{n:02d} Y|'", "ELSE", f"DISPLAY 'S{n:02d} N|'", "END-IF"]
        orig = lines + [f"IF {cond}"] + tail
        mir = lines + moves + [f"IF {condm}"] + tail
        st = {"step": n, "kind": kind, "dmax": 0, "text": cond, "g": sorted(info["g"]),
              "neg_exp": self._has_neg(x), "nested": self._nested(x), "lpow": self._has(x, "lpow"),
              "npow": self._count(x, "pow"), "size": False, "serr": False, "over": False}
        return orig, mir, st

    def _has(self, x, kind):
        return x[0] == kind or any(self._has(c, kind) for c in x[1:] if isinstance(c, tuple))

    def _count(self, x, kind):
        return (1 if x[0] == kind else 0) + sum(self._count(c, kind) for c in x[1:] if isinstance(c, tuple))

    def _nested(self, x):
        if x[0] == "pow" and self._has(x[1], "pow"):
            return True
        return any(self._nested(c) for c in x[1:] if isinstance(c, tuple))

    def _has_neg(self, x):
        if x[0] == "pow":
            e = evaluate(x[2], self.env, 0, False, {"ibm": {}, "g": set()})
            if e < 0:
                return True
        return any(self._has_neg(c) for c in x[1:] if isinstance(c, tuple))

    def unsup_stmt(self):
        """One statement the front end must report unsupported with UNSUP_MSG: (lines, form)."""
        rng = self.rng
        form = rng.choice(["rounded", "edited", "decexp", "divexp", "decrel", "fnarg", "neglit", "intfn", "litover"])
        if form == "intfn":
            return [f"COMPUTE R2 = DA ** N1 + FUNCTION INTEGER(DB)"], form
        if form == "litover":
            return [f"COMPUTE R2 = (DA ** N2) ** 2"], form
        if form == "rounded":
            return [f"COMPUTE R2 ROUNDED = DA ** N1"], form
        if form == "edited":
            return [f"COMPUTE ER2 = DA ** N2"], form
        if form == "decexp":
            return [f"COMPUTE R2 = IA ** DA"], form
        if form == "divexp":
            return [f"COMPUTE R2 = IA ** (N2 / 2)"], form
        if form == "decrel":
            return [f"IF IA ** N2 > 1.5", "DISPLAY 'U Y|'", "END-IF"], form
        if form == "fnarg":
            return [f"COMPUTE R2 = FUNCTION MAX(IA ** N2, 1)"], form
        return [f"COMPUTE R2 = IA ** -2"], form

    def data(self):
        d = []
        for nm, pic, f, signed, usage, _ in BASES + EXPS:
            d.append(f"       01  {nm} PIC {pic}{usage} VALUE ZERO.")
        for nm, f, pic, epic in RCVS:
            d.append(f"       01  {nm} PIC {pic} VALUE ZERO.")
            d.append(f"       01  E{nm} PIC {epic}.")
        # the mirror's items holding the powers' IBM values (unused by the program itself)
        for j in range(1, 5):
            d.append(f"       01  M{j} PIC S9(12)V9(6) VALUE ZERO.")
        return d

    def programs(self):
        """(original source, mirror source); self.steps filled; self.unsup_form, self.unsup_line."""
        proc, procm = [], []
        for n in range(self.k):
            orig, mir, st = (self.step_cond if self.rng.random() < 0.3 else self.step_compute)(n)
            self.steps.append(st)
            for ln in orig:
                proc += E.wrap(ln)
            for ln in mir:
                procm += E.wrap(ln)
        hdr = E.header("POWT", self.data())
        self.unsup_form = self.unsup_line = None
        if self.unsup:
            lines, self.unsup_form = self.unsup_stmt()
            self.unsup_line = len(hdr) + len(proc) + 1
            for ln in lines:
                proc += E.wrap(ln)
        src = "\n".join(E.check_lines(hdr + proc + ["           STOP RUN."])) + "\n"
        srcm = "\n".join(E.check_lines(hdr + procm + ["           STOP RUN."])) + "\n"
        return src, srcm


def gnucobol(D, src, base):
    """Compile and run one program with GnuCOBOL: (status, lines or detail)."""
    d = os.path.dirname(base)
    with open(base + ".cob", "w", encoding="latin-1") as fh:
        fh.write(src)
    c = subprocess.run([D.COBC, "-x"] + POW_COBC + ["-o", base, base + ".cob"],
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


def model(D, base):
    """The front end + cobolrun on base.cob: (status, lines or detail, signal)."""
    d = os.path.dirname(base)
    # -B: no bytecode written into the work copy (the control runs on a read-only base)
    fe = subprocess.run([sys.executable, "-I", "-B", D.COBOLFE, base + ".cob"] + POW_FE +
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


def parse(line):
    """'Snn ...' -> nn."""
    if len(line) >= 4 and line[0] == "S" and line[1:3].isdigit() and line[3] == " ":
        return int(line[1:3])
    return None


def compile_only(D, src, base):
    """Write base.cob and compile it with GnuCOBOL (a valid program): status, detail."""
    with open(base + ".cob", "w", encoding="latin-1") as fh:
        fh.write(src)
    c = subprocess.run([D.COBC, "-x"] + POW_COBC + ["-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    return ("ran", None) if c.returncode == 0 else ("cobc-error", c.stderr[-2000:])


def judge(gen, base_src, D, base, tally):
    """Status and detail of one generated program (see the module docstring)."""
    src, srcm = base_src
    if gen.unsup:
        # the statement the front end must report: GnuCOBOL compiles the program, it is not run
        s1, g = compile_only(D, src, base)
        if s1 != "ran":
            return s1, g
        s2, m, signal = model(D, base)
        if s2 != "fe-unsupported":
            return "unsup-mismatch", f"front end: {s2} (form {gen.unsup_form})"
        want = f":{gen.unsup_line}:"
        if len(m) == 1 and UNSUP_MSG in m[0] and want in m[0]:
            tally["unsup_forms"][gen.unsup_form] = tally["unsup_forms"].get(gen.unsup_form, 0) + 1
            return "ok-unsup", ""
        return "unsup-mismatch", f"form {gen.unsup_form} line {gen.unsup_line}: {m}"
    s1, g = gnucobol(D, src, base)
    if s1 != "ran":
        return s1, g
    s2, m, signal = model(D, base)
    if s2 != "ran":
        return s2, m
    if not signal.startswith("stop:"):
        return "lean-signal", signal
    s3, mi = gnucobol(D, srcm, base + "_mirror")
    if s3 != "ran":
        return "mirror-" + s3, mi
    if m != mi:
        i = E.first_diff(mi, m)
        return "mirror", f"line {i}: mirror vs model"
    if len(g) != len(m):
        return "mismatch", f"line counts {len(g)} vs {len(m)}"
    info = {s["step"]: s for s in gen.steps}
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
    return ("ok-g" if glines else "ok"), ""


def coverage(gen, cov):
    for s in gen.steps:
        feats = [s["kind"], f"dmax{s['dmax']}"]
        feats += [f for f, t in (("size_phrase", s["size"]), ("pow_size_error", s["serr"]),
                                 ("overflow", s["over"]), ("neg_exponent", s["neg_exp"]),
                                 ("nested_power", s["nested"]), ("literal_power_too", s["lpow"]),
                                 ("two_powers", s["npow"] >= 2)) if t]
        feats += s["g"]
        if s["kind"] == "compute":
            feats.append("rcv_" + s["rcv"])
        for f in feats:
            cov[f] = cov.get(f, 0) + 1
    if gen.unsup:
        cov["unsup_" + gen.unsup_form] = cov.get("unsup_" + gen.unsup_form, 0) + 1


def run_files(args):
    """--run: each program both ways (POW flags), the lines side by side (classtest's format)."""
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    worst = 0
    for path in args.run:
        with open(path, encoding="latin-1") as fh:
            src = fh.read()
        base = os.path.join(args.out, "run_" + os.path.splitext(os.path.basename(path))[0])
        s1, g = gnucobol(D, src, base)
        status, m = s1, g
        if s1 == "ran":
            s2, m, signal = model(D, base)
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
    ap.add_argument("--run", nargs="+", metavar="PROG.cob")
    args = ap.parse_args()
    if args.run:
        sys.exit(run_files(args))
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    open(os.path.join(args.out, "details.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown = {"g_lines": {}, "lines": 0, "unsup_forms": {}}, 0
    statuses, cov = {}, {}
    for p in range(args.n):
        gen = Gen(rng, args.k)
        srcs = gen.programs()
        base = os.path.join(args.out, f"p{args.seed}_{p:04d}")
        status, detail = judge(gen, srcs, D, base, tally)
        coverage(gen, cov)
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
    # exit status 0 when every program passed (ok, ok-g, ok-unsup), 1 otherwise
    sys.exit(0 if all(s in ("ok", "ok-g", "ok-unsup") for s in statuses) else 1)


if __name__ == "__main__":
    main()

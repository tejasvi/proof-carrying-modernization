#!/usr/bin/env python3
"""Differential testing of PROGRAM COLLATING SEQUENCE, SPECIAL-NAMES ALPHABET and the functions of
the collating sequence (ORD, CHAR, MAX, MIN, ORD-MAX, ORD-MIN).

Most random programs declare PROGRAM COLLATING SEQUENCE IS SEQ1 in OBJECT-COMPUTER and SEQ1 in
SPECIAL-NAMES as an ALPHABET given by literals: alphanumeric literals of one to four characters,
THROUGH ranges (ascending or descending), ALSO groups, the figurative constants HIGH-VALUE,
LOW-VALUE, SPACE, QUOTE and ZERO, or numeric ordinal positions (a numeric alphabet). The share
--native of the programs is in native order: no PROGRAM COLLATING SEQUENCE (half of them), or
SEQ1 IS NATIVE, STANDARD-1 or STANDARD-2 (the native order with ASCII data). A second, unused
alphabet is declared in some programs (also in some without a PROGRAM COLLATING SEQUENCE). Then K
random statements, each displaying its outcome, every DISPLAY ending with '|':
  * relation conditions (the six operators, NOT, AND, OR) between alphanumeric items of different
    lengths (the shorter is padded with spaces), reference-modified items and a group, an item and
    a literal, an item and a figurative constant, an unsigned numeric DISPLAY item and an
    alphanumeric item or literal; data from the alphabet's characters (characters sharing a
    position included), characters it leaves out, and X'00', X'FE', X'FF';
  * level-88 conditions with values, THRU ranges, HIGH-VALUE and LOW-VALUE; EVALUATE with values
    and THRU ranges; a serial SEARCH and a PERFORM ... UNTIL with alphanumeric conditions;
  * MOVE HIGH-VALUE / LOW-VALUE and VALUE HIGH-VALUE / LOW-VALUE (the alphabet's highest and
    lowest characters), then DISPLAY;
  * MAX and MIN (moved to an item or compared) and ORD-MAX and ORD-MIN of alphanumeric arguments
    (collated, the leftmost on ties); ties on purpose: MAX / MIN DISPLAYed (the value has the
    selected argument's length) and ORD-MAX / ORD-MIN of an item and a literal that compare equal
    (padding, or characters sharing a position); ORD-MAX and ORD-MIN of numeric arguments;
  * INSPECT ... TALLYING for a character that shares its position (matching is not collated);
  * ORD (of an item, a reference-modified character, a literal, CHAR) and CHAR (of a literal or
    an item, moved or compared), in the programs of native order only.
GnuCOBOL (-std=ibm) and the front end + cobolrun (--profile gnucobol, ASCII) must agree on every
line (ext_common.py). Left out, where GnuCOBOL 3.2 departs from IBM: ORD and CHAR under an
alphabet given by literals (G-ordchar: GnuCOBOL uses the native order) and relation conditions
between two literals (G-alsolit: GnuCOBOL decides = and <> by the bytes, ignoring ALSO).
Reproducers: tools/difftest/coll_cases (`--run`).

usage: colltest.py --root C --out DIR [--n N] [--seed S] [--k K] [--native SHARE] [--keep]
       colltest.py --root C --out DIR --run PROG.cob...
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402

# printable characters a generated literal may hold (no quotes, which delimit literals)
POOL = [chr(b) for b in range(0x21, 0x7F) if chr(b) not in "'\""] + [" "]
FIGS = {"HIGH-VALUE": 0xFF, "LOW-VALUE": 0x00, "SPACE": 0x20, "QUOTE": 0x22, "ZERO": 0x30}
ITEMS = {"A1": 3, "A2": 5, "A3": 1, "A4": 4}
OPS = ["=", "<>", "<", ">", "<=", ">="]


class Alphabet:
    """A random ALPHABET clause given by literals: its source text and the characters it names
    (for the data), with the groups of characters that share a position."""

    def __init__(self, rng):
        self.used, self.groups, parts = set(), [], []
        numeric = rng.random() < 0.2
        for _ in range(rng.randint(2, 6)):
            r = rng.random()
            if r < 0.35:
                n = rng.randint(1, 1 if numeric else 4)
                cs = [b for b in self.free(rng, n)]
                if not cs:
                    continue
                if numeric:
                    parts.append(" ".join(str(b + 1) for b in cs))
                else:
                    parts.append("'" + "".join(chr(b) for b in cs) + "'")
                self.groups += [[b] for b in cs]
            elif r < 0.6:
                span = self.span(rng)
                if span is None:
                    continue
                a, b = span[0], span[-1]
                parts.append(f"{a + 1} THRU {b + 1}" if numeric else f"'{chr(a)}' THROUGH '{chr(b)}'")
                self.groups += [[x] for x in span]
            else:
                g = self.free(rng, rng.randint(2, 3), figs=not numeric)
                if len(g) < 2:
                    continue
                if numeric:
                    parts.append(" ALSO ".join(str(b + 1) for b in g))
                else:
                    parts.append(" ALSO ".join(self.lit(rng, b) for b in g))
                self.groups.append(g)
        if not parts:
            b = self.free(rng, 1)[0]
            parts.append(str(b + 1) if numeric else f"'{chr(b)}'")
            self.groups.append([b])
        self.text = " ".join(parts)
        self.tied = [g for g in self.groups if len(g) > 1]

    def lit(self, rng, b):
        names = [n for n, v in FIGS.items() if v == b]
        if names and (b not in range(0x21, 0x7F) or rng.random() < 0.5):
            return names[0]
        return f"'{chr(b)}'"

    def free(self, rng, n, figs=False):
        """Up to n unused characters (figurative ones too if figs)."""
        cand = [ord(c) for c in POOL if c != " "] + ([0x00, 0xFF, 0x20, 0x22] if figs else [])
        cand = [b for b in cand if b not in self.used]
        rng.shuffle(cand)
        out = cand[:n]
        self.used |= set(out)
        return out

    def span(self, rng):
        """An unused native range of 2 to 6 printable characters (without quotes), either way."""
        for _ in range(20):
            a = rng.randint(0x21, 0x7E)
            n = rng.randint(2, 6)
            d = rng.choice([1, -1])
            xs = [a + d * i for i in range(n)]
            if all(0x21 <= x <= 0x7E and chr(x) not in "'\"" and x not in self.used for x in xs):
                self.used |= set(xs)
                return xs
        return None


class Gen:
    def __init__(self, rng, native):
        self.rng = rng
        self.native = native
        self.alpha = None if native else Alphabet(rng)
        named = sorted(self.alpha.used) if self.alpha else []
        # data characters: the alphabet's (shared positions twice), some it leaves out, space
        extra = [ord(c) for c in rng.sample(POOL, 8)]
        tied = [b for g in (self.alpha.tied if self.alpha else []) for b in g]
        self.chars = [b for b in named + tied + extra + [0x20] if b not in (0x00, 0x22, 0xFF)] or [0x41]
        self.raw = [b for b in named + tied + extra + [0x20, 0x00, 0xFE, 0xFF] if b != 0x22]

    def text(self, n):
        return "".join(chr(self.rng.choice(self.chars)) for _ in range(n))

    def lit(self, n):
        return f"'{self.text(n)}'"

    def value(self, n):
        """A sending operand for an item of n characters: a literal, or a hexadecimal literal
        with X'00' / X'FE' / X'FF' bytes."""
        if self.rng.random() < 0.2:
            return "X'" + "".join(f"{self.rng.choice(self.raw):02X}" for _ in range(n)) + "'"
        return self.lit(self.rng.randint(1, n))

    def item(self):
        return self.rng.choice(list(ITEMS))

    def operand(self):
        """One side of a relation: an item, a reference-modified item or the group."""
        r = self.rng.random()
        if r < 0.65:
            return self.item()
        if r < 0.85:
            name = self.rng.choice(["A1", "A2", "A4"])
            s = self.rng.randint(1, ITEMS[name])
            return f"{name}({s}:{self.rng.randint(1, ITEMS[name] - s + 1)})"
        return "G1"

    def setup(self):
        out = []
        for name, n in ITEMS.items():
            out += E.wrap(f"MOVE {self.value(n)} TO {name}")
        out += E.wrap(f"MOVE {self.value(4)} TO G1")
        return out

    def yn(self, i, cond):
        return E.wrap(f"IF {cond}") + [f"              DISPLAY 'S{i:02d} Y|'", "           ELSE",
                                       f"              DISPLAY 'S{i:02d} N|'", "           END-IF"]

    def relation(self):
        rng = self.rng
        a = self.operand()
        r = rng.random()
        if r < 0.45:
            b = self.operand()
        elif r < 0.62:
            b = self.lit(rng.randint(1, 5))
        elif r < 0.7:
            b = self.hexlit(rng.randint(1, 3))
        elif r < 0.85:
            b = rng.choice(["HIGH-VALUE", "LOW-VALUE", "SPACE", "QUOTE", "ZERO", "HIGH-VALUES",
                            "LOW-VALUES"])
        else:
            a = "N1"
            b = rng.choice([self.item(), "'" + "".join(rng.choice("0123456789") for _ in range(3)) + "'"])
        if rng.random() < 0.5:
            a, b = b, a
        if a[0] in "'X" and b[0] in "'X" and not (a.startswith("X(") or b.startswith("X(")):
            b = self.item()
        c = f"{a} {rng.choice(OPS)} {b}"
        # NOT (...): cobc 3.2 aborts on `NOT ZERO = G1` (an abbreviated sign condition?)
        return f"NOT ({c})" if rng.random() < 0.15 else c

    def cond(self):
        r = self.rng.random()
        if r < 0.75:
            return self.relation()
        return f"({self.relation()}) {self.rng.choice(['AND', 'OR'])} ({self.relation()})"

    def hexlit(self, n):
        return "X'" + "".join(f"{self.rng.choice(self.raw):02X}" for _ in range(n)) + "'"

    def args(self, lo, hi):
        """Alphanumeric function arguments: items, literals and hexadecimal literals."""
        out = []
        for _ in range(self.rng.randint(lo, hi)):
            r = self.rng.random()
            out.append(self.item() if r < 0.55 else self.lit(self.rng.randint(1, 4)) if r < 0.85 else
                       self.hexlit(self.rng.randint(1, 2)))
        if all(a.startswith("'") or a.startswith("X'") for a in out):
            out[0] = self.item()
        return out

    def stmt(self, i):
        rng = self.rng
        r = rng.random()
        if self.native and r >= 0.85:
            return self.ordchar(i)
        if r < 0.36:
            return self.yn(i, self.cond())
        if r < 0.44:
            return E.wrap(f"MOVE {self.value(3)} TO V1") + self.yn(
                i, rng.choice(["V1-R", "V1-S", "V1-H", "V1-L", "NOT V1-R"]))
        if r < 0.52:
            a = self.item()
            lo, hi, v = self.lit(rng.randint(1, 3)), self.lit(rng.randint(1, 3)), self.lit(rng.randint(1, 3))
            return ([f"           EVALUATE {a}"] + E.wrap(f"   WHEN {lo} THRU {hi}") +
                    [f"                 DISPLAY 'S{i:02d} 1|'"] + E.wrap(f"   WHEN {v}") +
                    [f"                 DISPLAY 'S{i:02d} 2|'", "              WHEN OTHER",
                     f"                 DISPLAY 'S{i:02d} 3|'", "           END-EVALUATE"])
        if r < 0.58:
            op = rng.choice(OPS)
            return E.wrap(f"MOVE {self.lit(10)} TO T1") + E.wrap(f"MOVE {self.value(2)} TO A2") + [
                "           SET TX TO 1", "           MOVE 1 TO K2",
                "           SEARCH TE VARYING K2",
                f"              AT END DISPLAY 'S{i:02d} E|'"] + E.wrap(
                f"   WHEN TE(TX) {op} A2(1:2) DISPLAY 'S{i:02d} ' K2 '|'") + ["           END-SEARCH"]
        if r < 0.63:
            op = rng.choice(OPS)
            # K2 stays within 1 .. 6: both operands of OR are evaluated
            return E.wrap(f"MOVE {self.lit(6)} TO B6") + E.wrap(
                f"PERFORM VARYING K2 FROM 1 BY 1 UNTIL K2 > 5 OR B6(K2:1) {op} A3") + [
                "              CONTINUE", "           END-PERFORM", f"           DISPLAY 'S{i:02d} ' K2 '|'"]
        if r < 0.69:
            w = rng.choice(["HIGH-VALUE", "LOW-VALUE", "HIGH-VALUES", "LOW-VALUES"])
            a = self.item()
            return [f"           MOVE {w} TO {a}", f"           DISPLAY 'S{i:02d} ' {a} '|'"]
        if r < 0.745:
            f = rng.choice(["MAX", "MIN"])
            return E.wrap(f"MOVE FUNCTION {f}({' '.join(self.args(1, 4))}) TO B6") + [
                f"           DISPLAY 'S{i:02d} ' B6 '|'"]
        if r < 0.78:
            return self.tie(i)
        if r < 0.83:
            f = rng.choice(["MAX", "MIN"])
            return self.yn(i, f"FUNCTION {f}({' '.join(self.args(2, 3))}) {rng.choice(OPS)} {self.item()}")
        if r < 0.9:
            f = rng.choice(["ORD-MAX", "ORD-MIN"])
            return E.wrap(f"COMPUTE K2 = FUNCTION {f}({' '.join(self.args(1, 5))})") + [
                f"           DISPLAY 'S{i:02d} ' K2 '|'"]
        if r < 0.94:
            f = rng.choice(["ORD-MAX", "ORD-MIN"])
            nums = []
            for _ in range(rng.randint(1, 5)):
                x = rng.random()
                nums.append(rng.choice(["D1", "D2"]) if x < 0.4 else
                            str(rng.randint(-99, 99)) if x < 0.7 else f"{rng.randint(-9, 9)}.{rng.randint(0, 9)}")
            return E.wrap(f"MOVE {rng.randint(-999, 999) / 10} TO D1") + E.wrap(f"MOVE {rng.randint(0, 99)} TO D2") + \
                E.wrap(f"COMPUTE K2 = FUNCTION {f}({', '.join(nums)})") + [f"           DISPLAY 'S{i:02d} ' K2 '|'"]
        if not self.native or rng.random() < 0.3:
            g = rng.choice(self.alpha.tied) if self.alpha and self.alpha.tied else [rng.choice(self.chars)]
            c = rng.choice([b for b in g if b not in (0x00, 0x22, 0xFF)] or [0x41])
            s = "".join(chr(rng.choice(g + self.chars)) for _ in range(5)).replace("'", "A").replace('"', "A")
            s = "".join(ch if 0x20 <= ord(ch) < 0x7F else "A" for ch in s)
            return E.wrap(f"MOVE '{s}' TO A2") + ["           MOVE 0 TO K2"] + E.wrap(
                f"INSPECT A2 TALLYING K2 FOR ALL '{chr(c)}'") + [f"           DISPLAY 'S{i:02d} ' K2 '|'"]
        return self.ordchar(i)

    def tie(self, i):
        """MAX or MIN (DISPLAYed: its value has the selected argument's length) and ORD-MAX or
        ORD-MIN of an item and a literal that compare equal but differ: the literal is the item's
        text without its padding spaces, or with a character replaced by another of its position."""
        rng = self.rng
        s = self.text(rng.randint(1, 3)).rstrip() or "A"
        t = s
        tied = [[b for b in g if 0x20 < b < 0x7F and chr(b) not in "'\""] for g in
                (self.alpha.tied if self.alpha else [])]
        tied = [g for g in tied if len(g) >= 2]
        if tied and rng.random() < 0.6:
            g = rng.choice(tied)
            k = rng.randrange(len(s))
            a, b = rng.sample(g, 2)
            s, t = s[:k] + chr(a) + s[k + 1:], s[:k] + chr(b) + s[k + 1:]
        args = ["A2", f"'{t}'"] if rng.random() < 0.5 else [f"'{t}'", "A2"]
        f = rng.choice(["MAX", "MIN"])
        return E.wrap(f"MOVE '{s}' TO A2") + E.wrap(f"DISPLAY 'S{i:02d} ' FUNCTION {f}({' '.join(args)}) '|'") + \
            E.wrap(f"COMPUTE K2 = FUNCTION {rng.choice(['ORD-MAX', 'ORD-MIN'])}({' '.join(args)})") + [
                f"           DISPLAY 'S{i:02d} ' K2 '|'"]

    def ordchar(self, i):
        """ORD and CHAR (programs in native order only, see G-ordchar)."""
        rng = self.rng
        r = rng.random()
        if r < 0.3:
            a = rng.choice(["A3", f"A2({rng.randint(1, 5)}:1)", f"A1({rng.randint(1, 3)}:1)", self.lit(1)])
            return E.wrap(f"COMPUTE K3 = FUNCTION ORD({a})") + [f"           DISPLAY 'S{i:02d} ' K3 '|'"]
        if r < 0.45:
            return E.wrap(f"COMPUTE K3 = FUNCTION ORD({self.lit(1)}) + FUNCTION ORD(A3) - 1") + [
                f"           DISPLAY 'S{i:02d} ' K3 '|'"]
        if r < 0.6:
            return E.wrap(f"COMPUTE K3 = FUNCTION ORD(FUNCTION CHAR({rng.randint(1, 256)}))") + [
                f"           DISPLAY 'S{i:02d} ' K3 '|'"]
        if r < 0.75:
            return [f"           MOVE FUNCTION CHAR({rng.randint(34, 127)}) TO A3",
                    f"           DISPLAY 'S{i:02d} ' A3 '|'"]
        if r < 0.88:
            return [f"           MOVE {rng.randint(34, 127)} TO K3", "           MOVE FUNCTION CHAR(K3) TO A3",
                    f"           DISPLAY 'S{i:02d} ' A3 '|'"]
        return self.yn(i, f"FUNCTION CHAR({rng.randint(34, 127)}) {rng.choice(OPS)} A3")


def program(rng, k, native_share):
    native = rng.random() < native_share
    g = Gen(rng, native)
    # native order: no PROGRAM COLLATING SEQUENCE (NONE, maybe with an unused ALPHABET), or NATIVE,
    # STANDARD-1, STANDARD-2 (ASCII data)
    kind = rng.choice(["NONE", "NONE", "NATIVE", "STANDARD-1", "STANDARD-2"]) if native else "LITERAL"
    env = ["       ENVIRONMENT DIVISION.", "       CONFIGURATION SECTION."]
    clauses = []
    if kind != "NONE":
        env += ["       OBJECT-COMPUTER. X", "           PROGRAM COLLATING SEQUENCE IS SEQ1."]
        clauses.append(f"ALPHABET SEQ1 IS {g.alpha.text if kind == 'LITERAL' else kind}")
    if rng.random() < (0.5 if kind == "NONE" else 0.3):
        clauses.append(f"ALPHABET SEQ2 IS {rng.choice(['NATIVE', 'STANDARD-1', Alphabet(rng).text])}")
    if clauses:
        env.append("       SPECIAL-NAMES.")
        clauses[-1] += "."
        for c in clauses:
            env += E.wrap(c)
    elif kind == "NONE":
        env = []
    v88 = [f"           88 V1-R VALUE {g.lit(rng.randint(1, 3))} THRU {g.lit(rng.randint(1, 3))}.",
           f"           88 V1-S VALUE {g.lit(rng.randint(1, 3))} {g.lit(rng.randint(1, 3))}.",
           "           88 V1-H VALUE HIGH-VALUE.", "           88 V1-L VALUE LOW-VALUE."]
    data = ["       01  A1 PIC X(3).", "       01  A2 PIC X(5).", "       01  A3 PIC X.", "       01  A4 PIC X(4).",
            "       01  G1.", "           05 G1A PIC X(2).", "           05 G1B PIC X(2).",
            "       01  N1 PIC 9(3).", "       01  V1 PIC X(3)."] + v88 + [
            "       01  H2 PIC X(2) VALUE HIGH-VALUE.", "       01  L2 PIC X(2) VALUE LOW-VALUE.",
            "       01  T1.", "           05 TE PIC X(2) OCCURS 5 INDEXED BY TX.",
            "       01  B6 PIC X(6).", "       01  K2 PIC 99.", "       01  K3 PIC 999.",
            "       01  D1 PIC S9(3)V9.", "       01  D2 PIC 9(2)."]
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. COLLT.", *env, "       DATA DIVISION.",
             "       WORKING-STORAGE SECTION.", *data, "       PROCEDURE DIVISION.",
             "           DISPLAY 'H2 ' H2 ' L2 ' L2 '|'"]
    for i in range(k):
        lines += g.setup()
        lines += [f"           MOVE {rng.randint(0, 999)} TO N1"]
        lines += g.stmt(i)
    lines.append("           STOP RUN.")
    return "\n".join(E.check_lines(lines)) + "\n"


def show(s):
    """A DISPLAY line with bytes outside printable ASCII as <xx>."""
    return "".join(ch if 0x20 <= ord(ch) < 0x7F else f"<{ord(ch):02x}>" for ch in s)


def run_files(args):
    """--run: each program both ways, the lines side by side."""
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    worst = 0
    for path in args.run:
        with open(path, encoding="latin-1") as fh:
            src = fh.read()
        base = os.path.join(args.out, "run_" + os.path.splitext(os.path.basename(path))[0])
        status, detail = E.run(D, src, base, E.PLAIN_COBC, E.PLAIN_FE)
        print(f"== {path}: {status}")
        if status in ("ok", "mismatch"):
            g, m = detail
            for i in range(max(len(g), len(m))):
                a, b = (g[i] if i < len(g) else "<none>"), (m[i] if i < len(m) else "<none>")
                print(("   " if a == b else "!! ") + f"{show(a):<34} | {show(b)}")
        else:
            print(str(detail)[:2000])
        worst = max(worst, 0 if status == "ok" else 1)
    return worst


def main():
    ap = E.arg_parser(__doc__, 60, 20)
    ap.add_argument("--native", type=float, default=0.35, help="share of programs in native order")
    ap.add_argument("--run", nargs="+", metavar="PROG.cob")
    args = ap.parse_args()
    if args.run:
        sys.exit(run_files(args))
    args.keep = True    # the files of every program are kept
    E.main_loop(args, lambda rng, k: program(rng, k, args.native), E.PLAIN_COBC, E.PLAIN_FE)


if __name__ == "__main__":
    main()

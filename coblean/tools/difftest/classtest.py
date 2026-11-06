#!/usr/bin/env python3
"""Differential testing of SPECIAL-NAMES CLASS and class conditions with a class name.

Each random program declares two to four classes C1 .. C4 in SPECIAL-NAMES, each of one to four
phrases: alphanumeric literals of one to four characters (every character a member), THROUGH
ranges of one character each in either order (alphanumeric, hexadecimal, or numeric ordinal
positions: n is byte n - 1), hexadecimal literals, numeric ordinal positions, and the figurative
constants SPACE, ZERO, QUOTE, HIGH-VALUE and LOW-VALUE. A share of the programs declares PROGRAM
COLLATING SEQUENCE NATIVE or STANDARD-1 (the native order with ASCII data). Then K random steps,
each moving data into the items (characters of one class, other characters, X'00', X'7F', X'FF')
and testing, every outcome DISPLAYed, every DISPLAY ending with '|':
  * `id [IS] [NOT] Cn` on alphanumeric items of 1, 3 and 5 characters, an alphabetic item, an
    unsigned, an embedded-sign and a separate-leading-sign numeric DISPLAY item (the sign byte is a
    character of the item), a numeric-edited item, a group, its alphanumeric and numeric members,
    a table element with a literal and with a data-name subscript, and reference modifications
    (literal start and length, a data-name start, a literal start to the end of the item);
  * class conditions combined with AND, OR, NOT, NUMERIC / ALPHABETIC and relation conditions;
    EVALUATE TRUE ... WHEN with class conditions; PERFORM VARYING ... UNTIL a class condition on a
    table element (the index it stops at is DISPLAYed).
GnuCOBOL (-std=ibm) and the front end + cobolrun (--profile gnucobol, ASCII) must agree on every
line (ext_common.py). Nothing is left out: GnuCOBOL 3.2 follows IBM's rules for these (probe p1 of
the class-fix log, CLASS_PROGRESS.md). An ALPHABET of literals as the program collating sequence
is not generated: there the front end makes class conditions unsupported (unsup_cases).
The last line printed counts the Y and N outcomes in GnuCOBOL's output (both must occur).

usage: classtest.py --root C --out DIR [--n N] [--seed S] [--k K] [--keep]
       classtest.py --root C --out DIR --run PROG.cob...
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402

# printable characters a generated literal may hold (no quotes, which delimit literals)
POOL = [chr(b) for b in range(0x21, 0x7F) if chr(b) not in "'\""] + [" "]
FIGS = {"SPACE": [0x20], "ZERO": [0x30], "QUOTE": [0x22], "HIGH-VALUE": [0xFF], "LOW-VALUE": [0x00]}
PLURAL = {"SPACE": "SPACES", "ZERO": "ZEROS", "QUOTE": "QUOTES", "HIGH-VALUE": "HIGH-VALUES",
          "LOW-VALUE": "LOW-VALUES"}
# subjects of a class condition: name -> (kind, length) ('a' data written by MOVE of characters,
# 'n' by MOVE of numbers)
SUBJ = {"A1": ("a", 3), "A2": ("a", 5), "A3": ("a", 1), "B1": ("a", 4), "N1": ("n", 3), "N2": ("n", 3),
        "N3": ("n", 3), "E1": ("n", 3), "G1": ("a", 4), "G1A": ("a", 2), "G1B": ("a", 2), "T1": ("a", 8)}


class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.classes = [self.cls() for _ in range(rng.randint(2, 4))]

    def cls(self):
        """A CLASS clause body: (source text, set of byte values)."""
        rng, parts, members = self.rng, [], set()
        for _ in range(rng.randint(1, 4)):
            r = rng.random()
            if r < 0.3:
                s = "".join(rng.choice(POOL) for _ in range(rng.randint(1, 4)))
                parts.append(f"'{s}'")
                members |= {ord(c) for c in s}
            elif r < 0.5:
                a, b = rng.choice(POOL), rng.choice(POOL)
                parts.append(f"'{a}' {rng.choice(['THRU', 'THROUGH'])} '{b}'")
                members |= set(range(min(ord(a), ord(b)), max(ord(a), ord(b)) + 1))
            elif r < 0.6:
                a = rng.randint(1, 256)
                b = max(1, min(256, a + rng.randint(-30, 30)))
                parts.append(f"{a} THRU {b}")
                members |= set(range(min(a, b) - 1, max(a, b)))
            elif r < 0.7:
                a = rng.randint(1, 256)
                parts.append(str(a))
                members.add(a - 1)
            elif r < 0.8:
                bs = [rng.randint(0, 255) for _ in range(rng.randint(1, 3))]
                parts.append("X'" + "".join(f"{b:02X}" for b in bs) + "'")
                members |= set(bs)
            elif r < 0.88:
                a, b = rng.randint(0, 255), rng.randint(0, 255)
                parts.append(f"X'{a:02X}' THRU X'{b:02X}'")
                members |= set(range(min(a, b), max(a, b) + 1))
            else:
                f = rng.choice(list(FIGS))
                parts.append(f if rng.random() < 0.6 else PLURAL[f])
                members |= set(FIGS[f])
        return " ".join(parts), members

    def chars(self, n):
        """Data for n bytes: mostly the members of one class (so that Y happens), else anything."""
        rng = self.rng
        if rng.random() < 0.55:
            pool = sorted(rng.choice(self.classes)[1])
        else:
            pool = [ord(c) for c in rng.sample(POOL, 6)] + [0x00, 0x7F, 0xFF, 0x20]
        return [rng.choice(pool) for _ in range(n)]

    def value(self, n):
        """A sending literal for n bytes (hexadecimal if a byte is not printable or a quote)."""
        bs = self.chars(self.rng.randint(1, n))
        if all(0x20 <= b < 0x7F and b not in (0x22, 0x27) for b in bs):
            return "'" + "".join(map(chr, bs)) + "'"
        return "X'" + "".join(f"{b:02X}" for b in bs) + "'"

    def setup(self):
        rng = self.rng
        out = []
        for name in ("A1", "A2", "A3", "B1"):
            out += E.wrap(f"MOVE {self.value(SUBJ[name][1])} TO {name}")
        out += E.wrap(f"MOVE {rng.randint(0, 999)} TO N1")
        out += E.wrap(f"MOVE {rng.randint(-999, 999)} TO N2")
        out += E.wrap(f"MOVE {rng.randint(-999, 999)} TO N3")
        out += E.wrap(f"MOVE {rng.choice([0, rng.randint(0, 999)])} TO E1")
        out += E.wrap(f"MOVE {self.value(4)} TO G1")
        out += E.wrap(f"MOVE {self.value(8)} TO T1")
        out += [f"           MOVE {rng.randint(1, 4)} TO K1", f"           MOVE {rng.randint(1, 3)} TO K2"]
        return out

    def subject(self):
        rng = self.rng
        r = rng.random()
        if r < 0.6:
            return rng.choice(list(SUBJ))
        if r < 0.7:
            return f"TE({rng.randint(1, 4)})"
        if r < 0.78:
            return "TE(K1)"
        if r < 0.88:
            s = rng.randint(1, 5)
            return f"A2({s}:{rng.randint(1, 6 - s)})"
        if r < 0.94:
            return f"A2(K2:{rng.randint(1, 3)})"
        return f"A2({rng.randint(1, 5)}:)"

    def ccond(self):
        """`subject [IS] [NOT] Cn`."""
        rng = self.rng
        n = rng.randint(1, len(self.classes))
        return f"{self.subject()}{rng.choice(['', ' IS'])}{rng.choice(['', '', ' NOT'])} C{n}"

    def other(self):
        rng = self.rng
        r = rng.random()
        if r < 0.4:
            return f"{rng.choice(['A1', 'A2', 'G1A'])} {rng.choice(['NUMERIC', 'ALPHABETIC', 'NOT NUMERIC'])}"
        if r < 0.7:
            return f"A3 {rng.choice(['=', '<', '>', 'NOT ='])} '{rng.choice(POOL)}'"
        return f"N1 {rng.choice(['=', '<', '>'])} {rng.randint(0, 999)}"

    def cond(self):
        rng = self.rng
        r = rng.random()
        if r < 0.55:
            return self.ccond()
        if r < 0.85:
            a = self.ccond()
            b = self.ccond() if rng.random() < 0.6 else self.other()
            c = f"{a} {rng.choice(['AND', 'OR'])} {b}"
            return f"NOT ({c})" if rng.random() < 0.2 else c
        return f"({self.ccond()} OR {self.other()}) AND {self.ccond()}"

    def yn(self, i, cond):
        return E.wrap(f"IF {cond}") + [f"              DISPLAY 'S{i:02d} Y|'", "           ELSE",
                                       f"              DISPLAY 'S{i:02d} N|'", "           END-IF"]

    def stmt(self, i):
        rng = self.rng
        r = rng.random()
        if r < 0.75:
            return self.yn(i, self.cond())
        if r < 0.9:
            out = ["           EVALUATE TRUE"]
            for k in range(rng.randint(1, 3)):
                out += E.wrap(f"WHEN {self.ccond()}", indent=13)
                out.append(f"                DISPLAY 'S{i:02d} W{k + 1}|'")
            return out + ["             WHEN OTHER", f"                DISPLAY 'S{i:02d} W0|'",
                          "           END-EVALUATE"]
        # TE(4) is the last element: K1 stops at 4 at the latest, so TE(K1) is always in range
        n = rng.randint(1, len(self.classes))
        out = E.wrap(f"PERFORM VARYING K1 FROM 1 BY 1 UNTIL K1 > 3 OR TE(K1)"
                     f"{rng.choice(['', ' NOT'])} C{n}")
        return out + ["              CONTINUE", "           END-PERFORM",
                      f"           DISPLAY 'S{i:02d} K' K1 '|'"]


def program(rng, k):
    g = Gen(rng)
    env = ["       ENVIRONMENT DIVISION.", "       CONFIGURATION SECTION."]
    clauses = []
    if rng.random() < 0.25:
        env += ["       OBJECT-COMPUTER. X", "           PROGRAM COLLATING SEQUENCE IS SEQ1."]
        clauses.append(f"ALPHABET SEQ1 IS {rng.choice(['NATIVE', 'STANDARD-1'])}")
    clauses += [f"CLASS C{n + 1} {rng.choice(['IS ', ''])}{text}" for n, (text, _) in enumerate(g.classes)]
    clauses[-1] += "."
    env.append("       SPECIAL-NAMES.")
    for c in clauses:
        env += E.wrap(c)
    data = ["       01  A1 PIC X(3).", "       01  A2 PIC X(5).", "       01  A3 PIC X.",
            "       01  B1 PIC A(4).", "       01  N1 PIC 9(3).", "       01  N2 PIC S9(3).",
            "       01  N3 PIC S9(3) SIGN LEADING SEPARATE.", "       01  E1 PIC ZZ9.",
            "       01  G1.", "           05 G1A PIC X(2).", "           05 G1B PIC 9(2).",
            "       01  T1.", "           05 TE PIC X(2) OCCURS 4.", "       01  K1 PIC 9.",
            "       01  K2 PIC 9."]
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. CLASST.", *env, "       DATA DIVISION.",
             "       WORKING-STORAGE SECTION.", *data, "       PROCEDURE DIVISION."]
    for i in range(k):
        lines += g.setup()
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


def main_loop(args):
    """E.main_loop, plus the count of Y and N outcomes in GnuCOBOL's lines."""
    import random
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown, yn = {}, 0, {"Y": 0, "N": 0}
    for p in range(args.n):
        src = program(rng, args.k)
        base = os.path.join(args.out, f"p{args.seed}_{p:04d}")
        status, detail = E.run(D, src, base, E.PLAIN_COBC, E.PLAIN_FE)
        tally[status] = tally.get(status, 0) + 1
        with open(os.path.join(args.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": p, "status": status}) + "\n")
        if status in ("ok", "mismatch"):
            for ln in detail[0]:
                if ln.endswith(" Y|") or ln.endswith(" N|"):
                    yn[ln[-2]] += 1
        if status != "ok" and shown < args.show:
            shown += 1
            if status == "mismatch":
                print(f"program {p}: mismatch at line {E.first_diff(*detail)}")
            else:
                print(f"program {p}: {status}: {str(detail)[:600]}")
    print(json.dumps({"tally": tally}))
    print(json.dumps({"outcomes": yn}))


def main():
    ap = E.arg_parser(__doc__, 60, 20)
    ap.add_argument("--run", nargs="+", metavar="PROG.cob")
    args = ap.parse_args()
    if args.run:
        sys.exit(run_files(args))
    args.keep = True    # the files of every program are kept
    main_loop(args)


if __name__ == "__main__":
    main()

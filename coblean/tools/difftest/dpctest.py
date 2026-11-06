#!/usr/bin/env python3
"""Differential testing of DECIMAL-POINT IS COMMA, CURRENCY SIGN and BLANK WHEN ZERO on numeric
items.

Each random program is of one of four kinds: DECIMAL-POINT IS COMMA (40%), DECIMAL-POINT IS COMMA
with CURRENCY SIGN IS "c" (35%), CURRENCY SIGN alone (15%), neither (10%); c is one of the
upper-case letters IBM allows (W Y F H K M Q T; not L, which cobc 3.2 reads as its variable-length
PICTURE symbol even when it is the currency sign). It has eight numeric-edited items E1 .. E8
with random pictures, built in the standard roles and then written as the program reads them
(DECIMAL-POINT IS COMMA: "." and "," exchanged; CURRENCY SIGN: c for $), repetition factors
included: a fixed $, + or - on the left; an integer part of 1 to 6 digit positions (Z or * then 9,
all 9, or a floating $, + or - string then 9) with the insertion symbols , and B between
positions and 0 and / between two 9s; no point, a "." with 1 to 3 places (Z or * places when the
integer part is all Z or *; always places after a floating string with no 9, as cobc 3.2 rejects
`$,$`)
or a V; a +, -, CR or DB on the right when no other sign symbol is there; some with BLANK WHEN
ZERO (never with *). Also numeric items with VALUE clauses written with the decimal comma (N1
signed, N2 with a leading-comma literal such as ,125) and an unsigned 9(4) BLANK WHEN ZERO item
(numeric-edited by IBM's rule). K random steps, each DISPLAYing its result between [ ] and
ending with '|':
  * MOVE of a literal with decimal places (written with the program's decimal point, sometimes as
    ,5) to an edited item; MOVE of N1 (set by a literal just before); COMPUTE and ADD ... GIVING an
    edited item with such literals; MOVE ZERO / 0 (zero suppression, *, BLANK WHEN ZERO);
  * IF N1 = / < / > a literal with decimal places (Y or N);
  * MOVE of an integer to the BLANK WHEN ZERO numeric item.
Values always fit the receiver's integer positions and places: GnuCOBOL edits a literal before it
truncates it (README, "editing of literals before truncation"), so no truncation is generated.
Left out: the simple insertion symbols 0 and / inside or right after a Z, * or floating insertion
string, which IBM counts part of the string ("Any simple insertion symbols (B 0 / ,) within or to
the immediate right of the string ... are considered part of the string") and GnuCOBOL 3.2 writes
(G-ins0, also without the clauses: dpc_cases/g_ins0.cob); an insertion symbol right after the first
symbol of a floating $ string, where GnuCOBOL's COMPUTE / ADD ... GIVING (not its MOVE) drops the
leftmost digit (G-floatcs: $,$$$.9 = 851 gives "  $51.0"; dpc_cases/g_floatcs.cob); DISPLAY of a numeric literal with decimal
places (unsupported under DECIMAL-POINT IS COMMA: the model's form is unchecked), signed numeric
DISPLAY items (GnuCOBOL shows a separate sign),
de-editing MOVEs from edited items, BLANK WHEN ZERO on a numeric picture with V (GnuCOBOL makes the
item one byte longer, G-bwzv), CURRENCY SIGN ... PICTURE SYMBOL and several CURRENCY SIGN clauses (GnuCOBOL
does not implement them; unsupported in the front end).
GnuCOBOL (-std=ibm) and the front end + cobolrun (--profile gnucobol) must agree on every line.

usage: dpctest.py --root C --out DIR [--n N] [--seed S] [--k K] [--keep]
       dpctest.py --root C --out DIR --run PROG.cob...
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402
from classtest import run_files  # noqa: E402

# (not L: cobc 3.2 reads L in a PICTURE as its variable-length symbol even when it is the CURRENCY SIGN)
CURRENCIES = "WYFHKMQT"


class Pic:
    """A random numeric-edited picture in the standard roles: symbols, integer digit positions,
    places, whether it shows a sign, BLANK WHEN ZERO."""

    def __init__(self, rng):
        self.rng = rng
        syms = []
        left = rng.choice(["", "", "", "", "+", "-", "-", "$", "$", "$"])
        if left:
            syms.append(left)
        kind = rng.choice(["z", "star", "float", "nine"])
        if kind == "float" and left:
            kind = "z"
        n = rng.randint(1, 6)
        if kind == "float":
            f = rng.choice(["$", "+", "-"])
            k = rng.randint(1, n)
            body = [f] * (k + 1) + ["9"] * (n - k)
            self.sign = f in "+-"
        else:
            sup = {"z": "Z", "star": "*", "nine": "9"}[kind]
            k = rng.randint(0, n) if kind != "nine" else n
            body = [sup] * k + ["9"] * (n - k)
            self.sign = left in ("+", "-")
        # simple insertion symbols between positions (after the first; in a floating string too);
        # 0 and / only between two 9s (G-ins0: in or right after a Z, * or floating string GnuCOBOL
        # writes them, IBM counts them part of the string); none right after the first symbol of a
        # floating $ string (G-floatcs: an arithmetic statement storing into such a picture loses a
        # digit in GnuCOBOL)
        out = []
        for idx, s in enumerate(body):
            if idx and not (kind == "float" and body[0] == "$" and idx == 1) and rng.random() < 0.18:
                out.append(rng.choice([",", ",", ",", "B", "0", "/"] if body[idx - 1] == "9" else [",", ",", "B"]))
            out.append(s)
        syms += out
        self.ints = n
        self.places = 0
        r = rng.random()
        all_supp = kind in ("z", "star") and k == n
        if kind == "float" and k == n and r >= 0.6:
            # a floating string with no 9 at all: cobc 3.2 rejects `$,$` and `H,H` (it counts
            # adjacent floating symbols), so such pictures get places
            r = 0.0
        if r < 0.6:
            self.places = rng.randint(1, 3)
            syms.append(".")
            p = {"z": "Z", "star": "*"}[kind] if all_supp and rng.random() < 0.4 else "9"
            syms += [p] * self.places
        elif r < 0.7:
            self.places = rng.randint(1, 2)
            syms += ["V"] + ["9"] * self.places
        if not self.sign and left not in ("+", "-") and rng.random() < 0.4:
            syms.append(rng.choice(["+", "-", "CR", "DB"]))
            self.sign = True
        self.syms = syms
        # no BLANK WHEN ZERO on * (IBM), nor on a numeric picture with V (G-bwzv)
        self.bwz = kind != "star" and not (set(syms) <= {"9", "V"} and "V" in syms) and rng.random() < 0.15

    def text(self, dpc, cur):
        """The PICTURE string as the program writes it: runs of 3 or more as X(n) sometimes."""
        def w(s):
            if s == ".":
                return "," if dpc else "."
            if s == ",":
                return "." if dpc else ","
            if s == "$":
                return cur or "$"
            return s
        out, i = [], 0
        while i < len(self.syms):
            j = i
            while j < len(self.syms) and self.syms[j] == self.syms[i]:
                j += 1
            s, run = w(self.syms[i]), j - i
            if run >= 3 and len(s) == 1 and self.rng.random() < 0.3:
                out.append(f"{s}({run})")
            else:
                out.append(s * run)
            i = j
        return "".join(out)


def lit(v, s, dpc, rng, plus=True):
    """A numeric literal for the value v * 10^-s, written with the program's decimal point."""
    neg, m = v < 0, abs(v)
    ip, fp = str(m // 10 ** s), (str(m % 10 ** s).rjust(s, "0") if s else "")
    point = "," if dpc else "."
    if fp and ip == "0" and rng.random() < 0.3:
        body = point + fp
    else:
        body = ip + (point + fp if fp else "")
    return ("-" if neg else (rng.choice(["", "", "+"]) if plus else "")) + body


def two(rng, ints, places, room):
    """Two values (v, s), (a, t) whose sum has fewer than `room` integer digits."""
    while True:
        (v, s), (a, t) = value(rng, ints, places), value(rng, ints, places)
        S = max(s, t)
        if abs(v * 10 ** (S - s) + a * 10 ** (S - t)) < 10 ** (room + S):
            return (v, s), (a, t)


def value(rng, ints, places, signed=True):
    """(v, s): a value with at most `ints` integer digits and `places` places (s = places used)."""
    s = rng.randint(0, places)
    v = rng.randint(0, 10 ** (ints + s) - 1) if rng.random() < 0.85 else 0
    if signed and rng.random() < 0.35:
        v = -v
    return v, s


def program(rng, k):
    kind = rng.choices(["dpc", "both", "cur", "none"], [40, 35, 15, 10])[0]
    dpc = kind in ("dpc", "both")
    cur = rng.choice(CURRENCIES) if kind in ("both", "cur") else None
    pics = [Pic(rng) for _ in range(8)]
    env = []
    clauses = ([f"CURRENCY SIGN IS '{cur}'"] if cur else []) + (["DECIMAL-POINT IS COMMA"] if dpc else [])
    rng.shuffle(clauses)
    if clauses:
        env = ["       ENVIRONMENT DIVISION.", "       CONFIGURATION SECTION.", "       SPECIAL-NAMES."]
        clauses[-1] += "."
        for c in clauses:
            env += E.wrap(c)
    v1, s1 = value(rng, 5, 2)
    v2, s2 = rng.randint(0, 999), 3
    data = [f"       01  N1 PIC S9(5)V99 VALUE {lit(v1, s1, dpc, rng)}.",
            f"       01  N2 PIC 9(3)V9(3) VALUE {lit(v2, s2, dpc, rng, plus=False)}.",
            "       01  B1 PIC 9(4) BLANK WHEN ZERO."]
    for i, p in enumerate(pics):
        data += E.wrap(f"01  E{i + 1} PIC {p.text(dpc, cur)}{' BLANK WHEN ZERO' if p.bwz else ''}.", indent=7)
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. DPCT.", *env, "       DATA DIVISION.",
             "       WORKING-STORAGE SECTION.", *data, "       PROCEDURE DIVISION.",
             "           DISPLAY 'N2 ' N2 '|'"]
    for i in range(k):
        e = rng.randrange(8)
        p, name = pics[e], f"E{e + 1}"
        show = [f"           DISPLAY 'S{i:02d} [' {name} ']|'"]
        r = rng.random()
        if r < 0.35:
            v, s = value(rng, p.ints, p.places)
            lines += E.wrap(f"MOVE {lit(v, s, dpc, rng)} TO {name}") + show
        elif r < 0.5:
            v, s = value(rng, min(p.ints, 5), min(p.places, 2))
            lines += E.wrap(f"MOVE {lit(v, s, dpc, rng)} TO N1") + E.wrap(f"MOVE N1 TO {name}") + show
        elif r < 0.72:
            # COMPUTE / ADD ... GIVING N1 + a: places within the item's, the sum within its integer
            # positions (no size error)
            (v, s), (a, t) = two(rng, min(p.ints, 5), min(p.places, 2), p.ints)
            lines += E.wrap(f"MOVE {lit(v, s, dpc, rng)} TO N1")
            if r < 0.62:
                lines += E.wrap(f"COMPUTE {name} = N1 + {lit(a, t, dpc, rng)}") + show
            else:
                lines += E.wrap(f"ADD {lit(a, t, dpc, rng)} TO N1 GIVING {name}") + show
        elif r < 0.8:
            lines += [f"           MOVE {rng.choice(['ZERO', '0', 'ZEROS'])} TO {name}"] + show
        elif r < 0.9:
            a, t = value(rng, 5, 3)
            op = rng.choice(["=", "<", ">", "NOT ="])
            if rng.random() < 0.4:
                # an equal value written otherwise (more places, a sign) so that = holds
                v, s = value(rng, 5, 2)
                lines += E.wrap(f"MOVE {lit(v, s, dpc, rng)} TO N1")
                a, t = v * 10, s + 1
            lines += E.wrap(f"IF N1 {op} {lit(a, t, dpc, rng)}") + [
                f"              DISPLAY 'S{i:02d} Y|'", "           ELSE",
                f"              DISPLAY 'S{i:02d} N|'", "           END-IF"]
        else:
            lines += [f"           MOVE {rng.choice([0, rng.randint(0, 9999)])} TO B1",
                      f"           DISPLAY 'S{i:02d} [' B1 ']|'"]
    lines.append("           STOP RUN.")
    return "\n".join(E.check_lines(lines)) + "\n"


def main():
    ap = E.arg_parser(__doc__, 60, 20)
    ap.add_argument("--run", nargs="+", metavar="PROG.cob")
    args = ap.parse_args()
    if args.run:
        sys.exit(run_files(args))
    args.keep = True    # the files of every program are kept
    E.main_loop(args, program, E.PLAIN_COBC, E.PLAIN_FE)


if __name__ == "__main__":
    main()

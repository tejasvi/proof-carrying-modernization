#!/usr/bin/env python3
"""Differential testing of INITIALIZE: reference-modified identifiers and identifiers with a
REDEFINES clause, next to plain ones.

Each random program declares, with random sizes and pictures: level-01 alphanumeric,
alphabetic, numeric, numeric-edited and alphanumeric-edited items, each but the alphabetic one
redefined at level 01 (as numeric or as alphanumeric); a group G1 with alphanumeric, numeric,
signed, COMP-3, COMP, numeric-edited, alphanumeric-edited, FILLER and table members; a level-01
group G2 that REDEFINES G1, with a REDEFINES member and a table of groups inside; a group G3
whose members are redefined at level 05 (elementary and group redefinitions, two of the same
item, one alphanumeric-edited); a table of groups T1 with REDEFINES and COMP-3 members; the data
names I and L of the subscripts and positions. Each of K steps stores fresh random characters
into every record, runs one INITIALIZE and displays every record through alphanumeric views, so
that both sides show raw bytes (GnuCOBOL's DISPLAY of a numeric item shows a space digit as 0,
init_cases/refnum.cob). The identifiers are:
  * plain items: elementary items of every category, groups, table elements (literal and
    data-name subscripts);
  * items with a REDEFINES clause (IBM INITIALIZE rule 1a: "identifier-1 might itself have a
    REDEFINES clause"): elementary and group, level 01 and 05, a table element, an item inside
    a redefining group;
  * items subordinate to a redefining item;
  * reference-modified items (IBM: "an elementary data item" of category alphanumeric, so it
    receives SPACE): alphanumeric, alphabetic, numeric DISPLAY, numeric-edited,
    alphanumeric-edited and group items and table elements, literal or data-name positions,
    with and without a length;
  * two or three of these in one statement, overlapping ones included, with an INITIALIZE of
    I, L or W at the end in some (INITIALIZE A1 (I:L) I).
GnuCOBOL (-std=ibm) and the front end + cobolrun must produce the same DISPLAY lines
(ext_common.py). Exit status 0 only if every program agrees.

Left out of generation:
  a reference-modified COMP, COMP-3 or COMP-5 item (not IBM COBOL: reference modification needs
  usage DISPLAY; the model stops as unsupported, GnuCOBOL stores spaces into the bytes,
  init_cases/refcomp.cob);
  REPLACING, WITH FILLER, TO VALUE and DEFAULT (the front end makes them unsupported);
  a data name initialized before an identifier subscripted or reference-modified by it in the
  same statement (INITIALIZE I A1 (I:L) would use position 0).

usage: inittest.py --root C --out DIR [--n N] [--seed S] [--k K] [--forms F]
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402

CHARS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-*"
LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
EDIT = ["ZZZ9.99", "-ZZ9.99", "ZZ9.99-", "+999.99", "ZZ,ZZ9.99CR", "ZZZ9.99DB", "$$$,$$9.99",
        "***9.99", "ZZZZ9", "----9.99", "++++9", "99/99/99", "9B999", "ZZZ.ZZ", "$ZZ9.99"]
EDIT_SHORT = ["ZZ9", "Z9.99", "-Z9", "9B9", "ZZ.Z"]
AE4 = ["X/XX", "XX0X", "XBXX", "X0/X"]
FORMS = "all"


def ae_pic(rng, lo, hi):
    """Random alphanumeric-edited PICTURE of lo..hi positions: (text, length)."""
    t = rng.randint(lo, hi)
    m = rng.randint(1, min(3, t - 1))
    syms = [rng.choice("XXXXA9") for _ in range(t - m)]
    if not any(s in "XA" for s in syms):
        syms[0] = "X"
    for _ in range(m):
        syms.insert(rng.randint(0, len(syms)), rng.choice("B0/"))
    out, i = "", 0
    while i < len(syms):
        j = i
        while j < len(syms) and syms[j] == syms[i]:
            j += 1
        out += syms[i] * (j - i) if j - i <= 2 else f"{syms[i]}({j - i})"
        i = j
    return out, t


class Step:
    """Values of I and L one step needs (None: free)."""

    def __init__(self, rng):
        self.rng, self.i, self.l = rng, None, None

    def fix(self, var, lo, hi):
        cur = getattr(self, var)
        if cur is None:
            setattr(self, var, self.rng.randint(lo, hi))
            return True
        return lo <= cur <= hi


def subscript(st, n):
    if st.rng.random() < 0.5 and st.fix("i", 1, n):
        return " (I)"
    return f" ({st.rng.randint(1, n)})"


def refmod(st, n):
    rng = st.rng
    r = rng.random()
    s = rng.randint(1, n)
    if r < 0.4:
        return f" ({s}:{rng.randint(1, n - s + 1)})"
    if r < 0.55:
        return f" ({s}:)"
    if r < 0.8 and st.fix("i", 1, min(9, n)):
        if st.fix("l", 1, min(9, n - st.i + 1)):
            return " (I:L)"
        return f" (I:{rng.randint(1, n - st.i + 1)})"
    if r < 0.9 and st.fix("i", 1, min(9, n)):
        return " (I:)"
    if st.fix("l", 1, min(9, n - s + 1)):
        return f" ({s}:L)"
    return f" ({s}:{rng.randint(1, n - s + 1)})"


def program(rng, k):
    na, nb, n1 = rng.randint(6, 12), rng.randint(3, 8), rng.randint(3, 9)
    e1 = rng.choice(EDIT)
    ae1, nae = ae_pic(rng, 4, 10)
    k1, k2, k3, k4 = rng.randint(2, 5), rng.randint(2, 5), rng.randint(1, 4), rng.randint(1, 3)
    k5 = rng.randint(1, 5)
    g1d = rng.choice(EDIT_SHORT)
    g1f, ng1f = ae_pic(rng, 3, 6)
    lg1 = k1 + k2 + k3 + 1 + k5 // 2 + 1 + 2 + 2 + len(g1d) + 3 * k4 + ng1f
    m1, m2 = rng.randint(1, 4), rng.randint(2, 4)
    g2f, ng2f = ae_pic(rng, 3, 5)
    g3h = rng.choice(AE4)
    data = [f"       01  A1 PIC X({na}).", f"       01  NA1 REDEFINES A1 PIC 9({na}).",
            f"       01  AB PIC A({nb}).",
            f"       01  N1 PIC 9({n1}).", f"       01  N1X REDEFINES N1 PIC X({n1}).",
            f"       01  E1 PIC {e1}.", f"       01  E1X REDEFINES E1 PIC X({len(e1)}).",
            f"       01  AE1 PIC {ae1}.", f"       01  AE1X REDEFINES AE1 PIC X({nae}).",
            "       01  G1.", f"           05  G1A PIC X({k1}).", f"           05  G1B PIC 9({k2}).",
            f"           05  G1C PIC S9({k3})V9.", f"           05  G1P PIC 9({k5}) COMP-3.",
            "           05  G1Q PIC 9(4) COMP.", "           05  FILLER PIC X(2).",
            f"           05  G1D PIC {g1d}.", f"           05  G1E PIC X({k4}) OCCURS 3.",
            f"           05  G1F PIC {g1f}.",
            "       01  G2 REDEFINES G1.", f"           05  G2A PIC 9({m1}).",
            f"           05  G2B PIC X({m2}).", f"           05  G2C REDEFINES G2B PIC 9({m2}).",
            "           05  G2D OCCURS 2.", "               10  G2D1 PIC X.",
            "               10  G2D2 PIC 9."]
    lg2 = m1 + m2 + 4
    under = ["G2A", "G2B", "G2D", "G2D1", "G2D2", "G3B1", "G3B2", "G3F1", "G3F2"]
    # lengths of the items with usage DISPLAY (data-name-1 of a reference modification)
    lens = {"A1": na, "NA1": na, "AB": nb, "N1": n1, "N1X": n1, "E1": len(e1), "E1X": len(e1),
            "AE1": nae, "AE1X": nae, "G1": lg1, "G1A": k1, "G1B": k2, "G1C": k3 + 1,
            "G1D": len(g1d), "G1E": k4, "G1F": ng1f, "G2A": m1, "G2B": m2, "G2C": m2, "G2D": 2,
            "G2D1": 1, "G2D2": 1, "G3": 12, "G3A": 4, "G3B": 4, "G3B1": 2, "G3B2": 2, "G3H": 4,
            "G3C": 3, "G3D": 3, "G3E": 3, "G3E1": 1, "G3F": 3, "G3F1": 1, "G3F2": 2, "G3G": 2,
            "T1": 24, "T1E": 8, "T1A": 2, "T1B": 2, "T1C": 2, "T1D": 2, "W": 2}
    if lg1 - lg2 >= ng2f:
        data.append(f"           05  G2F PIC {g2f}.")
        lg2 += ng2f
        under.append("G2F")
        lens["G2F"] = ng2f
    if lg1 > lg2:
        data.append(f"           05  G2E PIC X({lg1 - lg2}).")
        under.append("G2E")
        lens["G2E"] = lg1 - lg2
        lg2 = lg1
    lens["G2"] = lg2
    data += ["       01  G3.", "           05  G3A PIC X(4).",
             "           05  G3B REDEFINES G3A.", "               10  G3B1 PIC 9(2).",
             "               10  G3B2 PIC X(2).", f"           05  G3H REDEFINES G3A PIC {g3h}.",
             "           05  G3C PIC 9(3).", "           05  G3D REDEFINES G3C PIC X(3).",
             "           05  G3E.", "               10  G3E1 PIC 9 OCCURS 3.",
             "           05  G3F REDEFINES G3E.", "               10  G3F1 PIC X.",
             "               10  G3F2 PIC 9(2).", "           05  G3G PIC S9(2).",
             "       01  T1.", "           05  T1E OCCURS 3.", "               10  T1A PIC X(2).",
             "               10  T1B PIC 9(2).", "               10  T1C REDEFINES T1B PIC X(2).",
             "               10  T1D PIC S9(2).", "               10  T1P PIC S9(3) COMP-3.",
             "       01  W.", "           05  I PIC 9.", "           05  L PIC 9."]
    # tables: item -> number of occurrences
    occurs = {"G1E": 3, "T1E": 3, "T1A": 3, "T1B": 3, "T1C": 3, "T1D": 3, "T1P": 3, "G2D": 2,
              "G2D1": 2, "G2D2": 2, "G3E1": 3}
    plain = ["A1", "AB", "N1", "E1", "AE1", "G1", "G1A", "G1B", "G1C", "G1P", "G1Q", "G1D", "G1E",
             "G1F", "G3", "G3A", "G3C", "G3E", "G3E1", "G3G", "T1", "T1E", "T1A", "T1B", "T1D",
             "T1P"]
    redef = ["NA1", "N1X", "E1X", "AE1X", "G2", "G2C", "G3B", "G3D", "G3F", "G3H", "T1C"]
    # data-name-1 of a reference modification: the DISPLAY items but W (not COMP-3, COMP)
    refm = sorted(n for n in lens if n != "W")

    def ident(st, pool):
        name = st.rng.choice(pool)
        return name + (subscript(st, occurs[name]) if name in occurs else "")

    def one(st):
        r = st.rng.random()
        form = FORMS if FORMS != "all" else \
            "plain" if r < 0.2 else "redef" if r < 0.5 else "under" if r < 0.65 else "refmod"
        if form != "refmod":
            return ident(st, {"plain": plain, "redef": redef, "under": under}[form])
        name = st.rng.choice(refm)
        sub = subscript(st, occurs[name]) if name in occurs else ""
        return name + sub + refmod(st, lens[name])

    lines = E.header("INITT", data)
    for i in range(k):
        st = Step(rng)
        ids = [one(st) for _ in range(rng.choice([1, 1, 1, 1, 1, 2, 3]))]
        if rng.random() < 0.15:
            last = {"all": ["I", "L", "W", "W (1:1)", "W (2:)"], "plain": ["I", "L", "W"],
                    "refmod": ["W (1:1)", "W (2:)"]}.get(FORMS)
            if last:
                ids.append(rng.choice(last))
        for name, n in (("A1", na), ("N1X", n1), ("E1X", len(e1)), ("AE1X", nae), ("G1", lg1),
                        ("G3", 12), ("T1", 24)):
            lines.append(f"           MOVE '{''.join(rng.choice(CHARS) for _ in range(n))}' TO {name}")
        lines.append(f"           MOVE '{''.join(rng.choice(LETTERS) for _ in range(nb))}' TO AB")
        iv = st.i if st.i is not None else rng.randint(1, 9)
        lv = st.l if st.l is not None else rng.randint(1, 9)
        lines.append(f"           MOVE '{iv}{lv}' TO W")
        lines += E.wrap("INITIALIZE " + " ".join(ids))
        lines.append(f"           DISPLAY 'A{i:02d} ' A1 '|' AB '|' N1X '|' E1X '|' AE1X '|'")
        lines.append(f"           DISPLAY 'B{i:02d} ' G1 '|' G3 '|' T1 '|' W '|'")
    lines.append("           STOP RUN.")
    return "\n".join(E.check_lines(lines)) + "\n"


def main():
    global FORMS
    ap = E.arg_parser(__doc__, 60, 20)
    ap.add_argument("--forms", default="all", choices=["all", "plain", "redef", "under", "refmod"],
                    help="identifiers of one kind only (plain, with REDEFINES, under a redefining "
                         "item, reference-modified); default: all, mixed")
    args = ap.parse_args()
    FORMS = args.forms
    E.main_loop(args, program, E.PLAIN_COBC, E.PLAIN_FE)
    with open(os.path.join(args.out, "results.jsonl")) as fh:
        ok = sum(json.loads(ln)["status"] == "ok" for ln in fh)
    return 0 if ok == args.n else 1


if __name__ == "__main__":
    sys.exit(main())

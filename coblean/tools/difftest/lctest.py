#!/usr/bin/env python3
"""Differential testing of PICTURE character-strings that begin with a comma (front-end defect E:
the lexer took a comma right after PIC / PICTURE [IS] for a separator, so PIC ,ZZ9 had 3 positions).

IBM Enterprise COBOL 6.4: the separator comma is a comma followed by a space (Separators, table 1:
",b"), and "PICTURE character-strings are delimited only by the separator space, separator comma,
separator semicolon, or separator period". So a ',' right after PIC / PICTURE [IS] that a non-space
follows begins the character-string. There it is a simple insertion character left of every digit
position, so not part of a zero-suppression or floating insertion string ("Any simple insertion
symbols (B 0 / ,) within or to the immediate right of the string ... are considered part of the
string"): it is written, PIC ,ZZ9 with 5 is ",  5"; under DECIMAL-POINT IS COMMA it is the decimal
point. A comma followed by a space (PIC , ZZ9) or by the end of the line stays a separator.

Each random program is of one of two kinds:
  * insertion programs (two thirds): six numeric-edited items E1 .. E6 whose pictures are ','
    followed by a body: 9s; a Z or * string, all of the integer part or followed by 9s; a
    floating $, + or - string, alone or followed by 9s; B or ',' between integer positions (not
    right after a floating string's first symbol); no point, or '.' or 'V' and 1 to 3 places (Z or
    * when the integer part is all Z or *, else 9); a trailing +, -, CR or DB (CR or DB after a
    floating $, none after a floating + or -); BLANK WHEN ZERO (not with *). Each item has a twin
    T (the body alone, a picture GnuCOBOL edits as IBM does; a quarter of the twins are written
    PIC , body: a separator comma, which stays a separator);
  * decimal-point programs (DECIMAL-POINT IS COMMA): six items whose pictures begin with the
    decimal point ',': 1 to 4 places 9, all Z or all *, B between places of 9, a trailing +, -, CR
    or DB (not with *), BLANK WHEN ZERO (not with *); no twins.
The clause is written PIC, PICTURE, PIC IS or PICTURE IS. Each of 20 steps moves a value (at most
the item's integer positions and places: no truncation; zero, ZERO, negative values) into an item
and its twin and displays both (E and T lines); some steps also move the item to the numeric item
N1 (de-editing, R line) and the value as the item holds it to N1V (V line); not for DB items
(G-deedit-db).

Checks per program (GnuCOBOL -std=ibm against the front end + cobolrun, --profile gnucobol):
  * every model line equals GnuCOBOL's, except E lines of insertion items whose only difference is
    the first character, ',' in the model and a space in GnuCOBOL's (G-editlc);
  * IBM mirror: the model's E line of an insertion item is GnuCOBOL's T line with ',' in front, or a
    space in front when that T line is all spaces (zero in an all-Z or all-floating item, BLANK WHEN
    ZERO), or '*' in front for zero in an all-* item (IBM: the whole item but the decimal point);
  * every model R line equals its V line.
Statuses: ok (every line equals GnuCOBOL's); ok-g (all checks hold, some lines are G-editlc);
mismatch; mirror (a mirror check fails); and the ext_common statuses.

G-editlc: GnuCOBOL 3.2 writes a ',' that has no digit position on its left as a space, also in a
picture with no zero suppression at all (PIC ,999 with 5: " 005", IBM ",005") and after a B
(PIC B,ZZ9 with 123: "  123", IBM " ,123"); IBM writes the ','. Reproducer:
tools/difftest/lc_cases/g_editlc.cob.

usage: lctest.py --root C --out DIR [--n N] [--seed S] [--k K] [--show K]
       lctest.py --root C --out DIR --run PROG.cob...
"""
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402
from classtest import run_files  # noqa: E402
from editpttest import parse, run_both  # noqa: E402

FLOAT = ("$", "+", "-")
KEYWORDS = ["PIC", "PIC", "PICTURE", "PIC IS", "PICTURE IS"]


def width(s):
    return 0 if s == "V" else (2 if s in ("CR", "DB") else 1)


def text_of(syms):
    out, i = "", 0
    while i < len(syms):
        j = i
        while j < len(syms) and syms[j] == syms[i]:
            j += 1
        r = j - i
        out += f"{syms[i]}({r})" if (r > 3 and syms[i] in ("9", "Z", "*", "$", "+", "-")) else syms[i] * r
        i = j
    return out


class Pic:
    """A random picture that begins with ',' (symbols), and what the tester needs: integer digit
    positions i, places f, sign shown, DB, all-* (zero gives '*'), the twin's symbols."""

    def __init__(self, rng, dpc):
        self.dpc = dpc
        (self.gen_dpc if dpc else self.gen_ins)(rng)
        self.syms = [","] + self.body
        self.width = sum(width(s) for s in self.syms)
        self.signed = any(s in ("+", "-", "CR", "DB") for s in self.syms)
        self.db = "DB" in self.syms
        self.kw = rng.choice(KEYWORDS)
        # the twin's clause: PIC, or PIC followed by a separator comma (comma + space)
        self.twin_kw = "PIC" if dpc else rng.choice(["PIC", "PIC", "PIC", "PIC ,"])

    def gen_ins(self, rng):
        i = rng.choice([1, 2, 2, 3, 3, 4])
        fr = rng.choice([0, 0, 1, 2, 2, 3])
        style = rng.choice(["9", "Z", "Z", "*", "*", "$", "$", "+", "-"])
        if style == "9":
            ints = ["9"] * i
        elif style in ("Z", "*"):
            k = rng.randint(1, i) if rng.random() < 0.5 else i
            ints = [style] * k + ["9"] * (i - k)
        else:
            k = rng.randint(1, i) if rng.random() < 0.4 else i
            ints = [style] * (k + 1) + ["9"] * (i - k)
        # B or ',' between integer positions: never first or last, never right after a floating
        # string's first symbol (cobc 3.2 rejects $,$ with no 9 and no places)
        for _ in range(rng.choice([0, 0, 0, 1, 1, 2])):
            lo = 2 if style in FLOAT else 1
            if len(ints) > lo:
                ints.insert(rng.randint(lo, len(ints) - 1), rng.choice(["B", ","]))
        self.allsupp = style in ("Z", "*") and "9" not in ints
        frac = []
        if fr:
            places = [style] * fr if (self.allsupp and rng.random() < 0.5) else ["9"] * fr
            frac = [rng.choice([".", ".", "V"])] + places
        if style in ("+", "-"):
            sign = None
        elif style == "$":
            sign = rng.choice([None, None, "CR", "DB"])
        else:
            sign = rng.choice([None, None, "+", "-", "CR", "DB"])
        self.body = ints + frac + ([sign] if sign else [])
        self.style = style
        nf = sum(1 for s in ints if s in FLOAT)
        self.i = sum(1 for s in ints if s in ("9", "Z", "*")) + (nf - 1 if nf else 0)
        self.f = fr
        self.allstar = self.allsupp and style == "*" and (not frac or frac[1] == "*")
        self.bwz = style != "*" and rng.random() < 0.15

    def gen_dpc(self, rng):
        fr = rng.choice([1, 2, 2, 3, 4])
        style = rng.choice(["9", "9", "9", "Z", "*", "B"])
        if style == "B":
            fr = max(fr, 2)
            places = ["9"] * fr
            places.insert(rng.randint(1, fr - 1), "B")
        else:
            places = [style] * fr
        sign = None if style == "*" else rng.choice([None, None, "+", "-", "CR", "DB"])
        self.body = places + ([sign] if sign else [])
        self.style = style
        self.i, self.f = 0, fr
        self.allsupp = style in ("Z", "*")
        self.allstar = style == "*"
        self.bwz = style != "*" and rng.random() < 0.15

    def text(self, syms=None):
        return text_of(self.syms if syms is None else syms)

    def clause(self, twin=False):
        kw = self.twin_kw if twin else self.kw
        return f"{kw} {self.text(self.body if twin else None)}" + (" BLANK WHEN ZERO" if self.bwz else "")


def lit(v, f, dpc=False):
    """Numeric literal of the integer v at scale f (decimal point ',' under DECIMAL-POINT IS COMMA)."""
    s = str(abs(v)).rjust(f + 1, "0")
    t = s if f == 0 else s[:-f] + ("," if dpc else ".") + s[-f:]
    return ("-" if v < 0 else "") + t


class Gen:
    def __init__(self, rng, k):
        self.rng, self.k = rng, k
        self.dpc = rng.random() < 1 / 3
        self.items = {f"E{j}": Pic(rng, self.dpc) for j in range(1, 7)}
        self.steps = []

    def data(self):
        d = []
        for nm, p in self.items.items():
            d += E.wrap(f"01  {nm} {p.clause()}.", indent=7)
            if not self.dpc:
                d += E.wrap(f"01  {nm}T {p.clause(twin=True)}.", indent=7)
        d += ["       01  N1 PIC S9(5)V9(4).", "       01  N1X REDEFINES N1 PIC X(9).",
              "       01  N1V PIC S9(5)V9(4).", "       01  N1VX REDEFINES N1V PIC X(9)."]
        return d

    def value(self, p):
        """(integer v at scale p.f, literal text): at most p.i integer digits and p.f places."""
        rng = self.rng
        r = rng.random()
        if r < 0.12 or (p.i + p.f) == 0:
            return 0, rng.choice(["0", "ZERO"] + ([lit(0, 1, self.dpc)] if p.f else []))
        if r < 0.45 and p.f:
            v = rng.randint(1, 10 ** p.f - 1)                                   # zero integer part
        elif r < 0.6:
            v = 10 ** (p.i + p.f) - 1                                           # the largest
        else:
            v = rng.randint(1, 10 ** (p.i + p.f) - 1)
        if rng.random() < 0.35:
            v = -v
        return v, lit(v, p.f, self.dpc)

    def step(self, n):
        rng = self.rng
        name = rng.choice(sorted(self.items))
        p = self.items[name]
        v, txt = self.value(p)
        out = [f"MOVE {txt} TO {name}", f"DISPLAY 'S{n:02d} E[' {name} ']'"]
        info = {"step": n, "item": name, "pic": p.text(), "kw": p.kw, "bwz": p.bwz, "value": txt,
                "dpc": self.dpc, "style": p.style, "zero": v == 0, "allstar": p.allstar,
                "allsupp": p.allsupp, "deedit": False}
        if not self.dpc:
            out += [f"MOVE {txt} TO {name}T", f"DISPLAY 'S{n:02d} T[' {name}T ']'"]
        if not p.db and rng.random() < 0.3:
            h = v if p.signed else abs(v)
            out += [f"MOVE {name} TO N1", f"DISPLAY 'S{n:02d} R ' N1X '|'",
                    f"MOVE {lit(h, p.f, self.dpc)} TO N1V", f"DISPLAY 'S{n:02d} V ' N1VX '|'"]
            info["deedit"] = True
        return out, info

    def header(self):
        out = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. LCTEST."]
        if self.dpc:
            out += ["       ENVIRONMENT DIVISION.", "       CONFIGURATION SECTION.", "       SPECIAL-NAMES.",
                    "           DECIMAL-POINT IS COMMA."]
        return out + ["       DATA DIVISION.", "       WORKING-STORAGE SECTION."] + self.data() + [
            "       PROCEDURE DIVISION."]

    def program(self):
        proc = []
        for n in range(self.k):
            lines, info = self.step(n)
            self.steps.append(info)
            for ln in lines:
                proc += E.wrap(ln)
        return "\n".join(E.check_lines(self.header() + proc + ["           STOP RUN."])) + "\n"


def g_editlc(g, m):
    """G-editlc: the E line differs only in its first character, ',' (model) and ' ' (GnuCOBOL)."""
    return len(g) == len(m) and len(m) > 2 and m[1] == "," and g[1] == " " and m[2:] == g[2:]


def mirror_of(t, st):
    """IBM's E line of an insertion item from GnuCOBOL's T line ('[content]')."""
    c = t[1:-1]
    if c.strip() == "":
        return "[ " + c + "]"
    if st["zero"] and st["allstar"]:
        return "[*" + c + "]"
    return "[," + c + "]"


def judge(g, m, signal, steps, tally):
    """Status of one program and a detail string (see the module docstring)."""
    if not signal.startswith("stop:"):
        return "lean-signal", signal
    if len(g) != len(m):
        return "mismatch", f"line counts {len(g)} vs {len(m)}"
    info = {s["step"]: s for s in steps}
    model, gnu, glines = {}, {}, 0
    for a, b in zip(g, m):
        n, tag, rest = parse(b)
        na, taga, resta = parse(a)
        st = info.get(n)
        if st is None or tag not in ("E", "T", "R", "V") or (na, taga) != (n, tag):
            return "mismatch", f"unexpected line: gnucobol {a!r} model {b!r}"
        model[(n, tag)], gnu[(n, tag)] = rest, resta
        tally[tag + "_lines"] = tally.get(tag + "_lines", 0) + 1
        if tag == "E" and rest[1:2] == ",":
            tally["comma_lines"] += 1
        if a == b:
            continue
        if tag == "E" and not st["dpc"] and g_editlc(resta, rest):
            glines += 1
            tally["g_lines"]["G-editlc"] = tally["g_lines"].get("G-editlc", 0) + 1
            continue
        return "mismatch", f"step {n} {tag}: gnucobol {a!r} model {b!r} ({st['pic']})"
    for st in steps:
        n = st["step"]
        if not st["dpc"]:
            exp = mirror_of(gnu[(n, "T")], st)
            if model[(n, "E")] != exp:
                return "mirror", f"step {n}: model E {model[(n, 'E')]!r} mirror {exp!r} ({st['pic']})"
        if st["deedit"] and model[(n, "R")] != model[(n, "V")]:
            return "mirror", f"step {n}: model R {model[(n, 'R')]!r} V {model[(n, 'V')]!r} ({st['pic']})"
    return ("ok-g" if glines else "ok"), ""


def coverage(gen, cov):
    cov["programs_dpc" if gen.dpc else "programs_insertion"] = cov.get("programs_dpc" if gen.dpc else
                                                                       "programs_insertion", 0) + 1
    for p in gen.items.values():
        feats = ["item", "dpc_item" if p.dpc else "insertion_item", "style_" + p.style, "kw_" + p.kw.replace(" ", "_")]
        if p.twin_kw != "PIC":
            feats.append("twin_sepcomma")
        feats += [f for f in ("CR", "DB", "B", "V", ".") if f in p.body]
        feats += [f"trailing_{s}" for s in ("+", "-") if p.body[-1] == s and p.style not in ("+", "-")]
        if "," in p.body:
            feats.append("inner_comma")
        feats += [f for f, t in (("BWZ", p.bwz), ("allsupp", p.allsupp), ("allstar", p.allstar)) if t]
        for f in feats:
            cov[f] = cov.get(f, 0) + 1
    for s in gen.steps:
        for f, t in (("step", True), ("deedit", s["deedit"]), ("zero_value", s["zero"]),
                     ("neg_value", s["value"].startswith("-"))):
            if t:
                cov[f] = cov.get(f, 0) + 1


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
    tally, shown = {"g_lines": {}, "comma_lines": 0}, 0
    statuses, cov = {}, {}
    for p in range(args.n):
        gen = Gen(rng, args.k)
        src = gen.program()
        base = os.path.join(args.out, f"p{args.seed}_{p:04d}")
        status, g, m, signal = run_both(D, src, base)
        detail = g
        if status == "ran":
            status, detail = judge(g, m, signal, gen.steps, tally)
        coverage(gen, cov)
        statuses[status] = statuses.get(status, 0) + 1
        with open(os.path.join(args.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": p, "status": status}) + "\n")
        if status not in ("ok", "ok-g"):
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
    # exit status 0 when every program passed (ok, ok-g), 1 otherwise
    sys.exit(0 if all(s in ("ok", "ok-g") for s in statuses) else 1)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Differential testing of numeric editing with simple insertion characters around the decimal
point and left of the string (M-editpoint: an insertion character right before the decimal point,
after a zero-suppression or floating insertion string with no 9, when the integer part is zero;
M-editlead: an insertion character before the first symbol of such a string).

IBM Enterprise COBOL 6.4 (PICTURE clause): "Any simple insertion symbols (B 0 / ,) within or to
the immediate right of the string of floating editing symbols are considered part of the string"
(zero suppression and replacement editing; floating insertion editing likewise); zero suppression
"stops at the leftmost character: That does not correspond to a suppression symbol, That contains
nonzero data, That is the decimal point"; a floating insertion character "is placed to the
immediate left of the first nonzero digit in the data, or of the decimal point, whichever is
farther to the left. The character positions to the left of the inserted character are filled
with spaces." So PIC $$,.99 with 0 is "  $.00" and PIC **,.99 with 0.86 is "***.86".

Each random program declares eight numeric-edited items E1 .. E8 with random pictures: an integer
part of 1 to 4 digit positions that is a Z or * suppression string or a floating $, + or - string,
mostly with no 9 and sometimes followed by 9s, or all 9s; the insertion characters B , 0 / inside
it, in a fifth of the pictures a B, 0 or / before its first symbol (left of the string, so not part
of it: written) and, in most pictures, one or two right before the decimal point; '.' or 'V'; 1 to
3 places (9s, or Z or * when the integer part is all Z or *), some with a 0 or / right after the
point or a B, 0 or / between places; a fixed $ or a leading or trailing
+, -, CR or DB where IBM allows them; BLANK WHEN ZERO (not with *). Each of its steps moves a value
into an item, mostly one with a zero integer part (0, ZERO, small fractions, negative ones), also
values with integer digits and the largest value, and displays the item (E line); some steps also
move the item to the numeric item N1 (de-editing, R line) and the value as the item holds it to
N1's twin N1T (T line).

IBM mirror: GnuCOBOL 3.2 keeps a 0 or / insertion character inside or right after a suppression or
floating string, where IBM replaces it (G-editins). An item with a 0 or / before its decimal point
(not counting one left of the string, which GnuCOBOL writes as IBM does) has a twin W with ',' in
those positions, which GnuCOBOL edits as IBM does; the twin gets the same values (W line). IBM's
editing of the item is the twin's, with the item's own 0 or / wherever the twin shows its ','
(whether a simple insertion character is replaced does not depend on which one it is). No ','
before the first symbol (GnuCOBOL writes such a ',' as a space, G-editlc; lctest.py tests it).

Checks per program (GnuCOBOL -std=ibm against the front end + cobolrun, --profile gnucobol):
  * every model line equals GnuCOBOL's, except the E lines of items with a twin and the R lines of
    steps whose item has a 0 insertion character (G-deedit-zero) or a DB sign and a negative value
    (G-deedit-db);
  * the model's E line of an item with a twin equals the mirror of the model's W line (which
    equals GnuCOBOL's);
  * every model R line equals its T line.
Statuses: ok (every line equals GnuCOBOL's); ok-g (all checks hold, some lines differ from
GnuCOBOL in a known class); mismatch; mirror (a mirror check fails); and the ext_common statuses.

Not generated, because GnuCOBOL or the model departs from IBM there (reproducers:
tools/difftest/editpt_cases):
  G-editptb     a B or ',' right after the decimal point (or V) when the integer part is a
                suppression or floating string and zero: GnuCOBOL writes '0' (PIC ZZ.B99 with 0.05:
                "  .005", IBM "  . 05"); 0 and / there agree;
  G-edittrunc, G-editsigncur, G-editfloatsign (deedittest.py): values have at most as many integer
                digits as the item has integer positions and at most its places; no leading sign
                before a fixed $; no fixed + or - after a floating $ string;
  a negative value that truncates to zero (the model has no negative zero).
A PICTURE never ends with ','.

usage: editpttest.py --root C --out DIR [--n N] [--seed S] [--k K] [--show K]
       editpttest.py --root C --out DIR --run PROG.cob...
"""
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402
from classtest import run_files  # noqa: E402

FLOAT = ("$", "+", "-")
INS = ["B", ",", ",", "0", "/"]


def width(s):
    return 0 if s == "V" else (2 if s in ("CR", "DB") else 1)


class Pic:
    """A random numeric-edited PICTURE (a list of symbols) and what the tester needs: integer digit
    positions i, places f, sign shown, DB, '0' insertion, the M-editpoint shape, the twin."""

    def __init__(self, rng):
        while True:
            self.gen(rng)
            if any(s not in ("9", "V") for s in self.syms):
                break
        self.width = sum(width(s) for s in self.syms)
        self.signed = any(s in ("+", "-", "CR", "DB") for s in self.syms)
        self.db = "DB" in self.syms
        self.zero_ins = "0" in self.syms
        # the IBM mirror (G-editins): every 0 or / before the decimal point but one left of the string
        # (GnuCOBOL writes that one, as IBM does), as (byte offset, char)
        mir = [k for k, s in enumerate(self.syms)
               if self.style != "9" and k < self.point_index and k != self.lead_at and s in ("0", "/")]
        self.mirror = []
        off = 0
        for k, s in enumerate(self.syms):
            if k in mir:
                self.mirror.append((off, s))
            off += width(s)
        self.twin = [("," if k in mir else s) for k, s in enumerate(self.syms)]

    def gen(self, rng):
        i = rng.choice([1, 2, 2, 3, 3, 4])
        fr = rng.choice([1, 2, 2, 3])
        style = rng.choice(["Z", "Z", "*", "*", "$", "$", "+", "-", "9"])
        if style == "9":
            ints = ["9"] * i
        else:
            k = rng.randint(1, i - 1) if (i > 1 and rng.random() < 0.25) else i
            ints = [style] * (k + (1 if style in FLOAT else 0)) + ["9"] * (i - k)
        # insertion characters inside the integer part, and in some pictures one before its first
        # symbol (left of the string: not part of it, written)
        for _ in range(rng.choice([0, 0, 1, 1, 2])):
            if len(ints) > 1:
                ints.insert(rng.randint(1, len(ints) - 1), rng.choice(INS))
        # (not ',': GnuCOBOL writes a ',' there as a space, G-editlc; lctest.py tests it)
        self.lead = style != "9" and rng.random() < 0.2
        if self.lead:
            ints.insert(0, rng.choice(["B", "0", "/"]))
        # and right before the decimal point: the M-editpoint shape when the integer part has no 9
        if rng.random() < 0.85:
            for _ in range(rng.choice([1, 1, 1, 2])):
                ints.append(rng.choice(INS))
        allsupp = style in ("Z", "*") and "9" not in ints
        if allsupp and rng.random() < 0.4:
            frac = [style] * fr
        else:
            frac = ["9"] * fr
            r = rng.random()
            if r < 0.2:
                frac.insert(0, rng.choice(["0", "/"]))        # right after the point (not B or ',': G-editptb)
            elif r < 0.35 and fr >= 2:
                frac.insert(rng.randint(1, fr - 1), rng.choice(["B", "0", "/"]))
        point = "." if rng.random() < 0.75 else "V"
        # one sign symbol at most (a floating + or - is the sign); no + / - after a floating $
        # (G-editfloatsign); a fixed $ never after a leading sign (G-editsigncur)
        if style in ("+", "-"):
            sign = None
        elif style == "$":
            sign = rng.choice([None, None, "CR", "DB"])
        else:
            sign = rng.choice([None, None, "L+", "L-", "T+", "T-", "CR", "DB"])
        cur = style in ("Z", "*", "9") and sign not in ("L+", "L-") and rng.random() < 0.3
        syms = []
        if sign in ("L+", "L-"):
            syms.append(sign[1])
        if cur:
            syms.append("$")
        self.point_index = len(syms) + len(ints)
        self.lead_at = len(syms) if self.lead else -1
        syms += ints + [point] + frac
        if sign in ("T+", "T-"):
            syms.append(sign[1])
        elif sign in ("CR", "DB"):
            syms.append(sign)
        self.syms, self.style, self.ints, self.allsupp = syms, style, ints, allsupp
        nf = sum(1 for s in ints if s in FLOAT)
        self.i = sum(1 for s in ints if s in ("9", "Z", "*")) + (nf - 1 if nf else 0)
        self.f = fr
        self.bwz = style != "*" and rng.random() < 0.15
        # the M-editpoint shape: a suppression or floating integer part with no 9, then an
        # insertion character right before the point
        self.trig = style != "9" and "9" not in ints and ints[-1] in ("B", ",", "0", "/")
        # visible: the old model's kept character differs from the replacement (B under Z is a
        # space either way)
        pre = []
        for s in reversed(ints):
            if s not in ("B", ",", "0", "/"):
                break
            pre.append(s)
        self.visible = self.trig and any(s != "B" or style != "Z" for s in pre)

    @staticmethod
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

    def text(self):
        return self.text_of(self.syms)

    def clause(self, twin=False):
        return f"PIC {self.text_of(self.twin if twin else self.syms)}" + (" BLANK WHEN ZERO" if self.bwz else "")


def lit(v, f):
    """Numeric literal of the integer v at scale f."""
    s = str(abs(v)).rjust(f + 1, "0")
    t = s if f == 0 else s[:-f] + "." + s[-f:]
    return ("-" if v < 0 else "") + t


class Gen:
    def __init__(self, rng, k):
        self.rng, self.k = rng, k
        self.items = {f"E{j}": Pic(rng) for j in range(1, 9)}
        self.steps = []

    def data(self):
        d = []
        for nm, p in self.items.items():
            d += E.wrap(f"01  {nm} {p.clause()}.", indent=7)
            if p.mirror:
                d += E.wrap(f"01  {nm}W {p.clause(twin=True)}.", indent=7)
        d += ["       01  N1 PIC S9(5)V9(4).", "       01  N1X REDEFINES N1 PIC X(9).",
              "       01  N1T PIC S9(5)V9(4).", "       01  N1TX REDEFINES N1T PIC X(9)."]
        return d

    def value(self, p):
        """A value for item p: (integer v at scale p.f, literal text); at most p.i integer digits
        and p.f places (G-edittrunc), so editing truncates nothing."""
        rng = self.rng
        r = rng.random()
        if r < 0.12:
            return 0, rng.choice(["0", "ZERO", "0.0"])
        if r < 0.55:
            v = rng.randint(1, 10 ** p.f - 1)                                   # zero integer part
        elif r < 0.7:
            v = rng.randint(1, 9) * 10 ** p.f + rng.randint(0, 10 ** p.f - 1)    # one integer digit
        elif r < 0.8:
            v = 10 ** (p.i + p.f) - 1                                           # the largest
        else:
            v = rng.randint(1, 10 ** (p.i + p.f) - 1)
        if rng.random() < 0.35:
            v = -v
        return v, lit(v, p.f)

    def step(self, n):
        rng = self.rng
        name = rng.choice(sorted(self.items))
        p = self.items[name]
        v, txt = self.value(p)
        out = [f"MOVE {txt} TO {name}", f"DISPLAY 'S{n:02d} E[' {name} ']'"]
        zint = abs(v) < 10 ** p.f
        info = {"step": n, "item": name, "pic": p.text(), "syms": p.syms, "bwz": p.bwz, "value": txt,
                "twin": bool(p.mirror), "mirror": p.mirror, "g": [], "deedit": False,
                "lead": p.lead,
                "trigger": p.trig and zint and not (v == 0 and (p.bwz or p.allsupp)),
                "visible": p.visible and zint and not (v == 0 and (p.bwz or p.allsupp))}
        if p.mirror:
            out += [f"MOVE {txt} TO {name}W", f"DISPLAY 'S{n:02d} W[' {name}W ']'"]
        if rng.random() < 0.3:
            h = v if p.signed else abs(v)
            out += [f"MOVE {name} TO N1", f"DISPLAY 'S{n:02d} R ' N1X '|'",
                    f"MOVE {lit(h, p.f)} TO N1T", f"DISPLAY 'S{n:02d} T ' N1TX '|'"]
            info["deedit"] = True
            if p.zero_ins:
                info["g"].append("G-deedit-zero")
            if p.db and v < 0:
                info["g"].append("G-deedit-db")
        return out, info

    def program(self):
        proc = []
        for n in range(self.k):
            lines, info = self.step(n)
            self.steps.append(info)
            for ln in lines:
                proc += E.wrap(ln)
        hdr = E.header("EDITPT", self.data())
        return "\n".join(E.check_lines(hdr + proc + ["           STOP RUN."])) + "\n"


def run_both(D, src, base):
    """GnuCOBOL and the model on one program: (status, gnucobol lines, model lines, model signal)."""
    d = os.path.dirname(base)
    with open(base + ".cob", "w", encoding="latin-1") as fh:
        fh.write(src)
    c = subprocess.run([D.COBC, "-x"] + E.PLAIN_COBC + ["-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return "cobc-error", c.stderr[-2000:], None, None
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    try:
        r = subprocess.run([base], capture_output=True, env=env, timeout=20, cwd=d)
    except subprocess.TimeoutExpired:
        return "gnucobol-timeout", None, None, None
    if r.returncode != 0:
        return "gnucobol-abend", (r.stdout[-500:] + r.stderr[-500:]).decode("latin-1"), None, None
    g = r.stdout.decode("latin-1").split("\n")
    if g and g[-1] == "":
        g.pop()
    fe = subprocess.run([sys.executable, "-I", D.COBOLFE, base + ".cob"] + E.PLAIN_FE +
                        ["--main", "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0:
        return "fe-error", fe.stderr[-2000:], None, None
    unsup = [ln for ln in fe.stderr.splitlines() if "unsupported" in ln]
    if unsup:
        return "fe-unsupported", "\n".join(unsup)[:2000], None, None
    try:
        lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True,
                            timeout=60, cwd=d)
    except subprocess.TimeoutExpired:
        return "lean-timeout", None, None, None
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-2000:], None, None
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    return "ran", g, m, res["signal"]


def parse(line):
    """'Snn X...' -> (nn, X, rest); E and W lines are 'Snn E[content]', R and T lines 'Snn R bytes|'."""
    if len(line) >= 5 and line[0] == "S" and line[1:3].isdigit() and line[3] == " ":
        return int(line[1:3]), line[4], line[5:]
    return None, None, line


def mirror_of(w, offs):
    """IBM's editing of an item from its twin's displayed line w ('[content]'): the item's own
    0 or / at each offset where the twin shows ','."""
    c = list(w[1:-1])
    for off, ch in offs:
        if off < len(c) and c[off] == ",":
            c[off] = ch
    return "[" + "".join(c) + "]"


def judge(g, m, signal, steps, tally):
    """Status of one program and a detail string (see the module docstring)."""
    if not signal.startswith("stop:"):
        return "lean-signal", signal
    if len(g) != len(m):
        return "mismatch", f"line counts {len(g)} vs {len(m)}"
    info = {s["step"]: s for s in steps}
    model, glines = {}, 0
    for a, b in zip(g, m):
        n, tag, rest = parse(b)
        st = info.get(n)
        if st is None or tag not in ("E", "W", "R", "T"):
            return "mismatch", f"unexpected model line {b!r}"
        model[(n, tag)] = rest
        tally[tag + "_lines"] = tally.get(tag + "_lines", 0) + 1
        if a == b:
            continue
        if tag == "E" and st["twin"]:
            glines += 1
            tally["g_lines"]["G-editins"] = tally["g_lines"].get("G-editins", 0) + 1
            continue
        if tag == "R" and st["g"]:
            glines += 1
            for c in st["g"]:
                tally["g_lines"][c] = tally["g_lines"].get(c, 0) + 1
            continue
        return "mismatch", f"step {n} {tag}: gnucobol {a!r} model {b!r}"
    for st in steps:
        n = st["step"]
        if st["twin"]:
            exp = mirror_of(model[(n, "W")], st["mirror"])
            if model[(n, "E")] != exp:
                return "mirror", f"step {n}: model E {model[(n, 'E')]!r} mirror {exp!r} ({st['pic']})"
        if st["deedit"] and model[(n, "R")] != model[(n, "T")]:
            return "mirror", f"step {n}: model R {model[(n, 'R')]!r} T {model[(n, 'T')]!r} ({st['pic']})"
    tally["trigger_lines"] += sum(1 for s in steps if s["trigger"])
    tally["visible_trigger_lines"] += sum(1 for s in steps if s["visible"])
    tally["lead_lines"] += sum(1 for s in steps if s["lead"])
    return ("ok-g" if glines else "ok"), ""


def coverage(steps, cov):
    for s in steps:
        sy = s["syms"]
        feats = [f for f in ("DB", "CR", "+", "-", "$", "Z", "*", "V", ".", "0", "B", "/", ",") if f in sy]
        if sum(1 for x in sy if x in FLOAT) >= 2:
            feats.append("floating")
        k = sy.index(".") if "." in sy else sy.index("V")
        if sy[k - 1] in ("B", ",", "0", "/"):
            feats.append("ins_before_point_" + sy[k - 1])
        if k + 1 < len(sy) and sy[k + 1] in ("0", "/"):
            feats.append("ins_after_point_" + sy[k + 1])
        feats += [f for f, t in (("BWZ", s["bwz"]), ("twin", s["twin"]), ("deedit", s["deedit"]), ("lead", s["lead"]),
                                 ("trigger", s["trigger"]), ("visible", s["visible"]),
                                 ("neg", s["value"].startswith("-")),
                                 ("zero", s["value"] == "ZERO" or s["value"].strip("-0.") == "")) if t]
        for feat in feats:
            cov[feat] = cov.get(feat, 0) + 1


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
    tally, shown = {"g_lines": {}, "trigger_lines": 0, "visible_trigger_lines": 0, "lead_lines": 0}, 0
    statuses, cov = {}, {}
    for p in range(args.n):
        gen = Gen(rng, args.k)
        src = gen.program()
        base = os.path.join(args.out, f"p{args.seed}_{p:04d}")
        status, g, m, signal = run_both(D, src, base)
        detail = g
        if status == "ran":
            status, detail = judge(g, m, signal, gen.steps, tally)
        coverage(gen.steps, cov)
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

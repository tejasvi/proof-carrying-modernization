#!/usr/bin/env python3
"""Differential testing of de-editing: MOVE from a numeric-edited item to numeric and numeric-edited
items.

IBM Enterprise COBOL 6.4 (MOVE, elementary move rules): "When the sending item is numeric-edited, the
compiler de-edits the sending data to establish the unedited value of the numeric-edited item (this
value can be signed). The unedited numeric value is used in the move to the receiving numeric or
numeric-edited data item." To the other receivers a numeric-edited item moves as alphanumeric.

Each random program declares three numeric-edited senders and a table of them (subscripted by a data
name), with random pictures: fixed or floating currency symbol, fixed or floating + or -, CR, DB, Z or
* suppression, B 0 / , insertion, the decimal point . or V, BLANK WHEN ZERO. Receivers: a signed and
an unsigned numeric DISPLAY item, a COMP-3 item (shown through a DISPLAY copy), two numeric-edited
items with random pictures, an alphanumeric item and a group. Each step:
  MOVE value TO sender        the sender's content is the editing of the value (E line)
  MOVE sender TO receivers    1-3 numeric / numeric-edited receivers (R line), sometimes with the
                              alphanumeric item or the group (A line)
  MOVE expected TO twins      items of the receivers' pictures get the value as the sender holds
                              it: truncated to its digit positions, negative only when its picture
                              shows a sign (T line): the IBM mirror of de-editing
Some steps move a reference-modified part of a sender (alphanumeric) into the alphanumeric item.
A program may end with an INVALID step: one character of the sender is replaced, through reference
modification, by 'X' (no editing writes an X), or the first position, when it is a suppression,
floating, currency, sign or insertion position, by '0' (a leading zero that editing would have
suppressed or replaced); then the sender is moved to N1. No value edits to such content, IBM does not
define its unedited value, and the model must stop with Fault.invalidData.

Checks per program (GnuCOBOL -std=ibm against the front end + cobolrun, --profile gnucobol):
  * every model line equals GnuCOBOL's, except the R lines of steps of a known class where GnuCOBOL
    departs from IBM (below);
  * on every step the model's R line equals its T line (de-editing = the mirror);
  * an INVALID step: the model's lines equal GnuCOBOL's up to the E line that shows the changed
    content, and the model then stops with invalidData.
Statuses: ok; ok-g (R lines of known classes differ from GnuCOBOL, all checks hold); ok-fault (the
expected invalidData stop, all checks hold); mismatch; mirror (a model R line differs from its T
line); bad-fault (an INVALID step that does not end as expected); and the ext_common statuses.

Invalid content (the model's choice where IBM is silent): the model de-edits exactly the contents
that editing can produce, so VALUE ZERO in PIC ZZ9.99 ("000000"), a leading zero in a Z position
("012.34") or a letter in a digit position fault with invalidData (GnuCOBOL skips every non-digit:
0, 12.34, the other digits).

Known GnuCOBOL 3.2 departures from IBM (the model follows IBM; R lines not compared, model R = T is):
  G-deedit-db    a DB sign is not recognized: "$ 45.60DB" de-edits to +45.60
                 (deedit_cases/g_deedit_db.cob);
  G-deedit-zero  a '0' insertion character counts as a digit: PIC 9(3)0 "1230" de-edits to 1230
                 (deedit_cases/g_deedit_zero.cob).
Not generated, because the EDITING (not the de-editing) of GnuCOBOL or of the model departs from IBM
there (found by this tester; every MOVE into such an item is affected, numeric senders too):
  G-edittrunc      GnuCOBOL places the zero suppression and floating insertion by the value before
                   high-order truncation: MOVE -1038 TO PIC ---- gives "-038" (IBM " -38"); values
                   have at most as many integer digits as the edited item has integer positions;
  G-editins        GnuCOBOL keeps a 0 or / insertion character inside or right after a suppression
                   or floating string where the suppression covers it: PIC $ZZ/,ZZZ with 8 gives
                   "$  /   8" (IBM "$      8"); 0 and / come only after the first 9;
  G-editsigncur    a leading + or - before a fixed $: GnuCOBOL writes "+" and a NUL byte for a
                   negative value (PIC +$Z99V99 with -828: "+\\x0082800", IBM "-$82800");
  G-editfloatsign  a floating $ string followed by a fixed + or -: PIC $(5)- with 6 gives "   $$6"
                   (IBM "   $6 ");
  M-editpoint      a B , 0 / insertion character right before the decimal point after a
                   suppression or floating string with no 9, with a zero integer part (PIC $$,.99
                   with 0: IBM and GnuCOBOL "  $.00", the character is part of the string): the model
                   kept it (" $,.00") until the fix of 2026-10-28, which editpttest.py tests; such
                   pictures are still not generated here;
  a negative value that truncates to zero in the sender or a signed receiver (the model has no
                   negative zero: it edits -0.001 into PIC -9.99 as "-0.00" where GnuCOBOL writes
                   " 0.00", and stores 0 where GnuCOBOL keeps a negative zero).
A PICTURE never ends with ',' (comma and space are a separator).
Reproducers: tools/difftest/deedit_cases (--run).

usage: deedittest.py --root C --out DIR [--n N] [--seed S] [--k K] [--invalid P] [--show K]
       deedittest.py --root C --out DIR --run PROG.cob...
"""
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402

FAULT = "fault:Cobol.Fault.invalidData"


class Pic:
    """A random numeric-edited PICTURE: symbols (9 Z * $ + - . V , B 0 / CR DB) and what the tester
    needs: digit positions n, fraction digits f, sign shown, DB, '0' insertion, width."""

    def __init__(self, rng):
        while True:
            self.gen(rng)
            # a comma followed by a space is a separator: no PICTURE ends with ','
            if self.edited() and self.syms[-1] != ",":
                break
        self.n = sum(1 for s in self.syms if s in "9Z*") + self.fdig
        self.f = self.frac
        self.width = sum(0 if s == "V" else (2 if s in ("CR", "DB") else 1) for s in self.syms)
        self.signed = any(s in ("+", "-", "CR", "DB") for s in self.syms)
        self.db = "DB" in self.syms
        self.zero_ins = "0" in self.syms

    def gen(self, rng):
        i = rng.choice([1, 1, 2, 3, 3, 4, 5])
        fr = rng.choice([0, 0, 1, 2, 2, 3])
        style = rng.choice(["9", "9", "Z", "Z", "*", "$", "+", "-"])
        # one sign symbol at most (a floating + or - is the sign); no leading sign before a floating $
        if style in "+-":
            sign = None
        elif style == "$":
            sign = rng.choice([None, None, "CR", "DB"])       # no + / - after it (G-editfloatsign)
        else:
            sign = rng.choice([None, None, "L+", "L-", "T+", "T-", "CR", "DB"])
        # a fixed currency symbol, never after a leading sign (G-editsigncur)
        cur = style not in "$+-" and sign not in ("L+", "L-") and rng.random() < 0.3
        ints = []
        self.fdig = 0           # floating positions that hold digits (after the first)
        if style in "$+-":
            k = rng.randint(1, i)                       # digit positions under the floating string
            ints = [style] * (k + 1) + ["9"] * (i - k)
            self.fdig = k
        elif style in "Z*":
            k = rng.randint(1, i)
            ints = [style] * k + ["9"] * (i - k)
        else:
            ints = ["9"] * i
        # simple insertion inside the integer part (never before a floating string's first symbol);
        # 0 and / only after the first 9 (inside or right after a suppression or floating string
        # GnuCOBOL keeps them where IBM replaces them: G-editins)
        for _ in range(rng.choice([0, 0, 0, 1, 1, 2])):
            ch = rng.choice(["B", ",", ",", "/", "0", "0"] if rng.random() < 0.5 else ["B", ",", "/"])
            lo = 2 if style in "$+-" else 1
            if ch in "0/" and style != "9":
                if "9" not in ints:
                    continue
                lo = ints.index("9") + 1
            # not right before the decimal point after a string with no 9 (M-editpoint)
            hi = len(ints) - (1 if style != "9" and "9" not in ints else 0)
            if hi < lo:
                continue
            ints.insert(rng.randint(lo, hi), ch)
        allsupp = style in "Z*" and all(s not in "9" for s in ints)
        frac = []
        if fr:
            frac = [style if allsupp and rng.random() < 0.5 else "9"] * fr
            if frac[0] != "9":
                frac = [style] * fr
            elif rng.random() < 0.15:
                frac.insert(rng.randint(1, fr), rng.choice(["B", "0", "/"]))
        point = [] if not fr else [rng.choice([".", ".", ".", "V"])]
        syms = []
        if sign in ("L+", "L-"):
            syms.append(sign[1])
        if cur:
            syms.append("$")
        syms += ints + point + frac
        if sign in ("T+", "T-"):
            syms.append(sign[1])
        elif sign in ("CR", "DB"):
            syms.append(sign)
        self.syms = syms
        self.frac = fr
        self.style = style
        self.bwz = style != "*" and rng.random() < 0.15

    def edited(self):
        return any(s not in ("9", "V") for s in self.syms)

    def text(self):
        out, i, s = "", 0, self.syms
        while i < len(s):
            j = i
            while j < len(s) and s[j] == s[i]:
                j += 1
            r = j - i
            out += s[i] * r if (r <= 3 or len(s[i]) == 2) else f"{s[i]}({r})"
            i = j
        return out

    def clause(self):
        return f"PIC {self.text()}" + (" BLANK WHEN ZERO" if self.bwz else "")


def trunc_mag(num, den, n, f):
    """|value| truncated to f decimals and to n digits, as an integer at scale f (value = num/den)."""
    return (abs(num) * 10 ** f // den) % 10 ** n


def lit(v, f):
    """Numeric literal of the integer v at scale f."""
    s = str(abs(v)).rjust(f + 1, "0")
    t = s if f == 0 else s[:-f] + "." + s[-f:]
    return ("-" if v < 0 else "") + t


class Num:
    """A numeric receiver: digits a+b, scale b, signed, usage."""

    def __init__(self, name, a, b, signed, packed=False):
        self.name, self.a, self.b, self.signed, self.packed = name, a, b, signed, packed

    def pic(self):
        return ("S" if self.signed else "") + (f"9({self.a})" if self.a else "") + (f"V9({self.b})" if self.b else "")


class Gen:
    def __init__(self, rng, k, p_invalid):
        self.rng, self.k = rng, k
        self.senders = {f"E{j}": Pic(rng) for j in (1, 2, 3)}
        self.tpic = Pic(rng)
        a1, b1 = rng.randint(1, 6), rng.randint(0, 4)
        a2, b2 = rng.randint(1, 6), rng.randint(0, 3)
        a3, b3 = rng.randint(1, 7), rng.randint(0, 3)
        self.nums = {"N1": Num("N1", a1, b1, True), "N2": Num("N2", a2, b2, False),
                     "P1": Num("P1", a3, b3, True, packed=True)}
        self.eds = {"R1": Pic(rng), "R2": Pic(rng)}
        self.awidth = rng.randint(3, 12)
        self.p_invalid = p_invalid
        self.steps = []

    def data(self):
        d = []
        for nm, p in self.senders.items():
            d += E.wrap(f"01  {nm} {p.clause()}.", indent=7)
        d += ["       01  TE.", *E.wrap(f"05  ET {self.tpic.clause()} OCCURS 3.", indent=11),
              "       01  I PIC 9 VALUE 1."]
        for nm, x in self.nums.items():
            for suf in ("", "T"):
                if x.packed:
                    d += [f"       01  {nm}{suf} PIC {x.pic()} COMP-3.",
                          f"       01  {nm}{suf}D PIC {x.pic()}.",
                          f"       01  {nm}{suf}X REDEFINES {nm}{suf}D PIC X({x.a + x.b})."]
                else:
                    d += [f"       01  {nm}{suf} PIC {x.pic()}.",
                          f"       01  {nm}{suf}X REDEFINES {nm}{suf} PIC X({x.a + x.b})."]
        for nm, p in self.eds.items():
            for suf in ("", "T"):
                d += E.wrap(f"01  {nm}{suf} {p.clause()}.", indent=7)
        d += [f"       01  A1 PIC X({self.awidth}).", "       01  G1.", "           05 G1A PIC X(3).",
              "           05 G1B PIC X(5)."]
        return d

    def value(self, p):
        """A random literal for sender picture p, as (numerator, denominator, text): at most as many
        integer digits as p has integer positions (G-edittrunc), up to one decimal place more."""
        rng = self.rng
        idig = rng.choice(range(0, p.n - p.f + 1))
        fdig = rng.choice(range(0, p.f + 2))
        if rng.random() < 0.1:
            return 0, 1, "0"
        iv = rng.randint(0, 10 ** idig - 1) if idig else 0
        fv = rng.randint(0, 10 ** fdig - 1) if fdig else 0
        num = iv * 10 ** fdig + fv
        if num == 0:
            return 0, 1, "0"
        neg = rng.random() < 0.4
        txt = str(iv) + ("." + str(fv).rjust(fdig, "0") if fdig else "")
        return (-num if neg else num), 10 ** fdig, ("-" if neg else "") + txt

    def held(self, p, num, den):
        """The value the sender holds after MOVE num/den TO it, as an integer at scale p.f, or None
        for a negative value that truncates to zero under a sign symbol (not generated)."""
        mag = trunc_mag(num, den, p.n, p.f)
        if num < 0 and mag == 0 and p.signed:
            return None
        return -mag if (num < 0 and p.signed) else mag

    def fits(self, r, v, f):
        """Receiver r (Num or Pic) can take the value v (scale f): no negative zero in a signed
        receiver, and no high-order truncation in an edited one (G-edittrunc)."""
        if isinstance(r, Num):
            ok = (abs(v) * 10 ** r.b // 10 ** f) % 10 ** (r.a + r.b) != 0
            return v >= 0 or ok or not r.signed
        if abs(v) // 10 ** f >= 10 ** (r.n - r.f):
            return False
        ok = (abs(v) * 10 ** r.f // 10 ** f) % 10 ** r.n != 0
        return v >= 0 or ok or not r.signed

    def disp(self, nm):
        """What a DISPLAY shows of receiver or twin nm: numeric items through their PIC X
        redefinition (the bytes), edited items themselves."""
        base = nm[:-1] if nm.endswith("T") else nm
        return f"{nm}X" if base in self.nums else nm

    def step(self, i, last):
        rng, out = self.rng, []
        s = rng.choice(["E1", "E2", "E3", "E1", "E2", "E3", "ET"])
        p = self.tpic if s == "ET" else self.senders[s]
        if s == "ET":
            out.append(f"MOVE {rng.randint(1, 3)} TO I")
            s = "ET (I)"
        while True:
            num, den, txt = self.value(p)
            v = self.held(p, num, den)
            if v is not None:
                break
        out += [f"MOVE {txt} TO {s}", f"DISPLAY 'S{i:02d} E[' {s} ']'"]
        info = {"step": i, "sender": s, "pic": p.text(), "syms": p.syms, "bwz": p.bwz, "value": txt,
                "held": lit(v, p.f), "g": [], "kind": "main"}
        if last and rng.random() < self.p_invalid:
            # INVALID: 'X' anywhere, or '0' in a first position that is not a digit 9 / a '0' insertion
            first = p.syms[0]
            if first not in ("9", "0", "V") and rng.random() < 0.4:
                pos, ch = 1, "0"
            else:
                pos, ch = rng.randint(1, p.width), "X"
            out += [f"MOVE '{ch}' TO {s} ({pos}:1)", f"DISPLAY 'S{i:02d} E[' {s} ']'",
                    f"MOVE {s} TO N1", f"DISPLAY 'S{i:02d} R ' N1X '|'"]
            info.update(kind="invalid", ch=ch, pos=pos)
            return out, info
        if rng.random() < 0.1:
            a = rng.randint(1, p.width)
            m = rng.randint(1, p.width - a + 1)
            out += [f"MOVE {s} ({a}:{m}) TO A1", f"DISPLAY 'S{i:02d} A ' A1 '|'"]
            info["kind"] = "refmod"
            return out, info
        pool = [n for n in ("N1", "N2", "P1") if self.fits(self.nums[n], v, p.f)] + \
               [n for n in ("R1", "R2") if self.fits(self.eds[n], v, p.f)]
        rcv = rng.sample(pool, min(len(pool), rng.choice([1, 1, 2, 3])))
        alt = rng.sample(["A1", "G1"], rng.choice([0, 0, 0, 1, 2]))
        order = rcv + alt
        rng.shuffle(order)
        if not rcv and not alt:
            alt = ["A1"]
            order = alt
        out += E.wrap(f"MOVE {s} TO {' '.join(order)}")
        for n in rcv:
            if n == "P1":
                out.append("MOVE P1 TO P1D")
        if rcv:
            out += E.wrap(f"DISPLAY 'S{i:02d} R ' " + " '|' ".join(self.disp(n) for n in rcv) + " '|'")
        if alt:
            out += E.wrap(f"DISPLAY 'S{i:02d} A ' " + " '|' ".join(alt) + " '|'")
        if rcv:
            out += E.wrap(f"MOVE {lit(v, p.f)} TO {' '.join(n + 'T' for n in rcv)}")
            for n in rcv:
                if n == "P1":
                    out.append("MOVE P1T TO P1TD")
            out += E.wrap(f"DISPLAY 'S{i:02d} T ' " + " '|' ".join(self.disp(n + "T") for n in rcv) + " '|'")
        if p.db and v < 0:
            info["g"].append("G-deedit-db")
        if p.zero_ins:
            info["g"].append("G-deedit-zero")
        info.update(rcv=rcv, alt=alt)
        return out, info

    def program(self):
        proc = []
        for i in range(self.k):
            lines, info = self.step(i, i == self.k - 1)
            self.steps.append(info)
            for ln in lines:
                proc += E.wrap(ln) if not ln.startswith(" ") else [ln]
        hdr = E.header("DEEDT", self.data())
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


def split(line):
    """'Snn X rest' -> (nn, X, rest); the E line is 'Snn E[...]'."""
    if len(line) >= 5 and line[0] == "S" and line[1:3].isdigit():
        tag = line[4] if line[4] != "E" else "E"
        return int(line[1:3]), tag, line[6:] if tag != "E" else line[4:]
    return None, None, line


def judge(g, m, signal, steps, tally):
    """Status of one program and a detail string (see the module docstring)."""
    info = {s["step"]: s for s in steps}
    last = steps[-1]
    invalid = last["kind"] == "invalid"
    if invalid:
        # the model stops after the E line that shows the changed content
        idx = [j for j, ln in enumerate(g) if ln.startswith(f"S{last['step']:02d} E[")]
        if len(idx) != 2:
            return "bad-fault", f"gnucobol E lines of the invalid step: {len(idx)}"
        cut = idx[1] + 1
        if signal != FAULT or len(m) != cut:
            return "bad-fault", f"signal {signal}, model lines {len(m)}, expected {cut}"
        g = g[:cut]
    elif not signal.startswith("stop:"):
        return "lean-signal", signal
    if len(g) != len(m):
        return "mismatch", f"line counts {len(g)} vs {len(m)}"
    rlines, tlines, glines = {}, {}, 0
    for a, b in zip(g, m):
        n, tag, rest = split(b)
        if tag == "R":
            rlines[n] = rest
        if tag == "T":
            tlines[n] = (split(a)[2], rest)
    for a, b in zip(g, m):
        if a == b:
            continue
        n, tag, rest = split(b)
        st = info.get(n)
        if tag == "R" and st is not None and st["g"] and n in tlines and tlines[n][0] == tlines[n][1]:
            glines += 1
            for c in st["g"]:
                tally["g_lines"][c] = tally["g_lines"].get(c, 0) + 1
            continue
        return "mismatch", f"gnucobol {a!r} model {b!r}"
    for n, r in rlines.items():
        if n in tlines and tlines[n][1] != r:
            return "mirror", f"step {n}: model R {r!r} T {tlines[n][1]!r}"
    tally["r_lines"] += len(rlines)
    if invalid:
        return "ok-fault", f"{last['ch']} at {last['pos']} of {last['pic']}"
    return ("ok-g" if glines else "ok"), ""


def coverage(steps, cov):
    for s in steps:
        cov["steps_" + s["kind"]] = cov.get("steps_" + s["kind"], 0) + 1
        sy = s["syms"]
        feats = [f for f in ("DB", "CR", "+", "-", "$", "Z", "*", "V", ".", "0", "B", "/", ",") if f in sy]
        if sum(1 for x in sy if x in ("$", "+", "-")) >= 2:
            feats.append("floating")
        feats += [f for f, t in (("BWZ", s["bwz"]), ("neg", s["held"].startswith("-")),
                                 ("zero", s["held"].strip("-0.") == ""),
                                 ("table", s["sender"].startswith("ET"))) if t]
        for feat in feats:
            cov["sender_" + feat] = cov.get("sender_" + feat, 0) + 1
        for r in s.get("rcv", []) + s.get("alt", []):
            cov["rcv_" + r] = cov.get("rcv_" + r, 0) + 1
        if s["kind"] == "invalid":
            cov["invalid_" + s["ch"]] = cov.get("invalid_" + s["ch"], 0) + 1


def run_files(args):
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    worst = 0
    for path in args.run:
        with open(path, encoding="latin-1") as fh:
            src = fh.read()
        base = os.path.join(args.out, "run_" + os.path.splitext(os.path.basename(path))[0])
        status, g, m, signal = run_both(D, src, base)
        print(f"== {path}: {status} {signal or ''}")
        if status == "ran":
            for i in range(max(len(g), len(m))):
                a, b = (g[i] if i < len(g) else "<none>"), (m[i] if i < len(m) else "<none>")
                print(("   " if a == b else "!! ") + f"{a:<40} | {b}")
            worst = max(worst, 0 if (g == m and signal.startswith("stop:")) else 1)
        else:
            print(str(g)[:2000])
            worst = 1
    return worst


def main():
    ap = E.arg_parser(__doc__, 60, 15)
    ap.add_argument("--invalid", type=float, default=0.3, help="share of programs ending with an INVALID step")
    ap.add_argument("--run", nargs="+", metavar="PROG.cob")
    args = ap.parse_args()
    if args.run:
        sys.exit(run_files(args))
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    open(os.path.join(args.out, "details.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown = {"g_lines": {}, "r_lines": 0}, 0
    statuses, cov = {}, {}
    for p in range(args.n):
        gen = Gen(rng, args.k, args.invalid)
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
        if status not in ("ok", "ok-g", "ok-fault"):
            with open(os.path.join(args.out, "details.jsonl"), "a") as fh:
                fh.write(json.dumps({"case": p, "status": status, "detail": str(detail)[:2000],
                                     "steps": gen.steps}) + "\n")
            if shown < args.show:
                shown += 1
                print(f"program {p}: {status}: {str(detail)[:600]}")
    with open(os.path.join(args.out, "coverage.json"), "w") as fh:
        json.dump({"statuses": statuses, "g_lines": tally["g_lines"], "r_lines": tally["r_lines"],
                   "coverage": cov}, fh, indent=1, sort_keys=True)
    print(json.dumps({"tally": statuses}))
    print(json.dumps({"g_lines": tally["g_lines"], "r_lines": tally["r_lines"]}, sort_keys=True))
    # exit status 0 when every program passed (ok, ok-g, ok-fault), 1 otherwise
    sys.exit(0 if all(s in ("ok", "ok-g", "ok-fault") for s in statuses) else 1)


if __name__ == "__main__":
    main()

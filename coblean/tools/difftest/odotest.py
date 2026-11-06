#!/usr/bin/env python3
"""Differential testing of OCCURS DEPENDING ON (variable-occurrence tables).

Each random program declares two tables `OCCURS integer-1 TO integer-2 DEPENDING ON`:
  TA, whose object NA (PIC 99 or PIC 9(3) COMP-3) is a record of its own: the record GA holds a
     header HA and TA, directly or through a group GA2; TA's elements are EA PIC X(w), with or
     without a second field FA PIC 99; integer-1 is 0, 1 or 2;
  TB, whose object NB (PIC 9) lies in its record GB before a header HB and TB (ASCENDING KEY KB,
     INDEXED BY IXB); integer-1 is 0 or 1;
and some programs a sequential file whose record FR (FN PIC 9, FH, FT OCCURS 1 TO 6 DEPENDING ON
FN) makes it variable-length. Each program runs K random steps, each starting with
DISPLAY 'S nn' and ending with a trace that shows NA and NB and the whole of GA and GB (their
objects set to integer-2 for the DISPLAY, then back), W1, W2, K and D:
  MOVE to NA and NB (values integer-1 .. integer-2);
  group MOVEs with GA, GA2 and GB as sender and as receiver (a receiver that contains its object,
  GB, gets its maximum length; GA and GA2 their current length), between them too;
  MOVE to and from elements, below and above the object's value (up to integer-2);
  numeric statements on FA elements; comparisons of the groups (with literals, W1, each other,
  reference-modified within the current length); INSPECT TALLYING / REPLACING of the groups;
  STRING the groups INTO W1, STRING / UNSTRING INTO GA (object outside), UNSTRING the groups;
  DISPLAY of the groups and of reference modifications; serial SEARCH of TA from a random
  start; SEARCH ALL of TB (its keys set in ascending order first); PERFORM VARYING I UNTIL I > NA
  over TA's elements; WRITE of FR with FN from 1 to 6 and READ ... INTO back.
GnuCOBOL (-std=ibm -fno-odoslide) and the front end + cobolrun must produce the same DISPLAY lines.

GnuCOBOL departs from IBM here (left out of generation; --unsafe generates the first two):
  G-odostring    STRING ... INTO a group that contains its object: GnuCOBOL fills the group's
                 current length, IBM its maximum length (maximum length rule: "STRING ... INTO").
  G-odounstring  UNSTRING ... INTO (or DELIMITER IN) such a group: the same.
  G-odoinit      INITIALIZE of a group containing such a table: GnuCOBOL initializes the
                 current occurrences; IBM: "you cannot use the INITIALIZE statement to
                 initialize ... a variable-length item" (the model: unsupported).
  G-odoslide     -std=ibm (odoslide: yes) computes every such group's length from its object,
                 even for a receiver that contains it (no maximum length rule), and a reference
                 modification without a length uses the maximum length; -fno-odoslide (used here)
                 follows IBM. odoslide only matters otherwise for variably located items, which
                 the model leaves unsupported.
With --mixed, one step sets an object outside integer-1 .. integer-2 and references its table
(IBM: "The behavior is undefined if the value of the object is outside of the range"): the model
must stop with a range fault at that reference, every line before it agreeing with GnuCOBOL (whose
run goes on with the value as it is), the last step marker shown being that step's.

usage: odotest.py [--n N] [--seed S] [--k K] [--out DIR] [--root TREE] [--show K] [--mixed] [--unsafe]
       odotest.py --run PROG.cob... [--out DIR] [--root TREE]   (tools/difftest/odo_cases)
  --root: the coblean tree whose front end and cobolrun are tested (default: this script's);
  COBOLFE=path/to/cobolfe.py overrides the front end.
"""
import argparse
import json
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
COBC_FLAGS = ["-std=ibm", "-fno-odoslide"]
LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"


def wrap(text, indent=11, width=72):
    """COBOL fixed-format lines (area B from column 12), splitting at blanks outside literals."""
    words, cur, out, inq = [], "", [], False
    for ch in text:
        if ch == "'":
            inq = not inq
        if ch == " " and not inq:
            words.append(cur)
            cur = ""
        else:
            cur += ch
    words.append(cur)
    line = " " * indent
    for w in words:
        if not w:
            continue
        if len(line) + 1 + len(w) > width:
            out.append(line)
            line = " " * (indent + 4) + w
        else:
            line = line + (" " if line.strip() else "") + w
    out.append(line)
    assert all(len(ln) <= width for ln in out), out
    return out


class Gen:
    def __init__(self, rng, mixed, unsafe):
        r = self.r = rng
        self.mixed, self.unsafe = mixed, unsafe
        self.loA = r.choice([0, 1, 1, 2])
        self.hiA = r.randint(self.loA + 2, 8)
        self.hA = r.randint(1, 4)
        self.wA = r.randint(1, 3)
        self.fA = r.random() < 0.5
        self.midA = r.random() < 0.5
        self.compA = r.random() < 0.3
        self.loB = r.choice([0, 1])
        self.hiB = r.randint(self.loB + 2, 9)
        self.hB = r.randint(1, 3)
        self.file = r.random() < 0.4
        self.na, self.nb = self.hiA, self.hiB
        self.fa_ok = [True] * (self.hiA + 1)
        self.ws = "".join(r.choice(LETTERS + "0123456789 ") for _ in range(24))
        self.mix_at = None
        self.mixed_done = False

    # ------------------------------------------------------------------ sizes
    def stride(self):
        return self.wA + (2 if self.fA else 0)

    def len_ga(self, n=None):
        return self.hA + (self.na if n is None else n) * self.stride()

    def len_ga2(self, n=None):
        return (self.na if n is None else n) * self.stride()

    def len_gb(self, n=None):
        return 1 + self.hB + (self.nb if n is None else n)

    def word(self, n, digits=False):
        alphabet = LETTERS + ("0123456789" if digits else "") + " "
        return "".join(self.r.choice(alphabet) for _ in range(n))

    # ------------------------------------------------------------------ program text
    def data(self):
        lv = (10, 15) if self.midA else (5, 10)
        na = f"01 NA PIC 9(3) COMP-3 VALUE {self.hiA}." if self.compA else f"01 NA PIC 99 VALUE {self.hiA}."
        lines = [na, "01 GA.", f"   05 HA PIC X({self.hA}) VALUE '{self.word(self.hA)}'."]
        if self.midA:
            lines.append("   05 GA2.")
        lines.append(f"   {lv[0]:02d} TA OCCURS {self.loA} TO {self.hiA} DEPENDING ON NA INDEXED BY IXA.")
        lines.append(f"      {lv[1]:02d} EA PIC X({self.wA}).")
        if self.fA:
            lines.append(f"      {lv[1]:02d} FA PIC 99.")
        lines += ["01 GB.", f"   05 NB PIC 9 VALUE {self.hiB}.",
                  f"   05 HB PIC X({self.hB}) VALUE '{self.word(self.hB)}'.",
                  f"   05 TB OCCURS {self.loB} TO {self.hiB} DEPENDING ON NB",
                  "         ASCENDING KEY IS KB INDEXED BY IXB.",
                  "      10 KB PIC X.",
                  "01 W1 PIC X(40) VALUE SPACES.", "01 W2 PIC X(40) VALUE SPACES.",
                  f"01 WS PIC X(24) VALUE '{self.ws}'.",
                  "01 K PIC 99 VALUE 0.", "01 I PIC 99 VALUE 0.", "01 SN PIC 99 VALUE 0.",
                  "01 D PIC 9(4) VALUE 0.", "01 FS1 PIC XX VALUE SPACES."]
        return ["       " + ln for ln in lines]

    def file_text(self):
        if not self.file:
            return [], []
        sel = ["       FILE-CONTROL.", "           SELECT OF1 ASSIGN TO 'ODOF1'",
               "               ORGANIZATION IS SEQUENTIAL FILE STATUS IS FS1."]
        fd = ["       FILE SECTION.", "       FD OF1.", "       01 FR.", "          05 FN PIC 9.",
              "          05 FH PIC XX.", "          05 FT OCCURS 1 TO 6 DEPENDING ON FN PIC X."]
        return sel, fd

    def init(self):
        out = []
        for k in range(1, self.hiA + 1):
            out.append(f"MOVE '{self.word(self.wA)}' TO EA({k})")
            if self.fA:
                out.append(f"MOVE {self.r.randint(0, 99)} TO FA({k})")
        out += self.keys()
        return out

    def keys(self):
        ks = sorted(self.r.sample("ABCDEFGHIJKLMNOPQRSTUVWXYZ", self.hiB))
        self.kb = ks
        return [f"MOVE '{c}' TO KB({k})" for k, c in enumerate(ks, 1)]

    def trace(self):
        return ["MOVE NA TO SN", f"MOVE {self.hiA} TO NA", "DISPLAY 'A ' SN ' [' GA ']'", "MOVE SN TO NA",
                "MOVE NB TO SN", f"MOVE {self.hiB} TO NB", "DISPLAY 'B ' SN ' [' GB ']'", "MOVE SN TO NB",
                "DISPLAY 'W [' W1 '] [' W2 '] ' K ' ' D"]

    # ------------------------------------------------------------------ steps
    def dirty(self):
        self.fa_ok = [False] * (self.hiA + 1)

    def fix_nb(self):
        """After a MOVE into GB (maximum length) left an arbitrary byte in NB."""
        self.nb = self.r.randint(self.loB, self.hiB)
        return [f"MOVE {self.nb} TO NB"]

    def st_setn(self):
        if self.r.random() < 0.5:
            self.na = self.r.randint(self.loA, self.hiA)
            return [f"MOVE {self.na} TO NA"]
        self.nb = self.r.randint(self.loB, self.hiB)
        return [f"MOVE {self.nb} TO NB"]

    def st_move_to_ga(self):
        src = self.r.choice([f"'{self.word(self.r.randint(1, 30), True)}'", "WS", "W1", "SPACES", "ALL '*'"])
        dst = "GA2" if self.midA and self.r.random() < 0.4 else "GA"
        self.dirty()
        return [f"MOVE {src} TO {dst}"]

    def st_move_from_ga(self):
        src = self.r.choice(["GA"] + (["GA2"] if self.midA else []) + ["GB"])
        return [f"MOVE {src} TO {self.r.choice(['W1', 'W2'])}"]

    def st_move_to_gb(self):
        if self.r.random() < 0.5:
            self.nb = self.r.randint(self.loB, self.hiB)
            lit = str(self.nb) + self.word(self.r.randint(0, 12))
            return [f"MOVE '{lit}' TO GB"]
        src = self.r.choice(["WS", "W1", "GA"] + (["GA2"] if self.midA else []))
        return [f"MOVE {src} TO GB"] + self.fix_nb()

    def st_move_gb_ga(self):
        self.dirty()
        return [f"MOVE GB TO {'GA2' if self.midA and self.r.random() < 0.4 else 'GA'}"]

    def st_elem_move(self):
        k = self.r.randint(1, self.hiA)
        if self.fA and self.r.random() < 0.4:
            self.fa_ok[k] = True
            return [f"MOVE {self.r.randint(0, 99)} TO FA({k})"]
        if self.r.random() < 0.3:
            return [f"MOVE '{self.r.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZ')}' TO KB({self.r.randint(1, self.hiB)})"]
        return [f"MOVE '{self.word(self.r.randint(1, self.wA + 1))}' TO EA({k})"]

    def st_elem_read(self):
        k = self.r.randint(1, self.hiA)
        c = self.r.random()
        if c < 0.3:
            return [f"MOVE EA({k}) TO W2"]
        if c < 0.6:
            return [f"DISPLAY 'E ' EA({k}) ' ' KB({self.r.randint(1, self.hiB)})"]
        return [f"IF EA({k}) = '{self.word(self.wA)}' DISPLAY 'Y' ELSE DISPLAY 'N' END-IF"]

    def st_elem_num(self):
        ks = [k for k in range(1, self.hiA + 1) if self.fa_ok[k]]
        if not self.fA or not ks:
            return None
        k = self.r.choice(ks)
        c = self.r.random()
        if c < 0.4:
            return [f"ADD FA({k}) TO D"]
        if c < 0.7:
            return [f"IF FA({k}) > {self.r.randint(0, 99)} DISPLAY 'G' ELSE DISPLAY 'L' END-IF"]
        self.fa_ok[k] = True
        return [f"ADD 1 TO FA({k}) ON SIZE ERROR DISPLAY 'SZ' END-ADD"]

    def refmod(self, name, length):
        if length < 1:
            return None
        s = self.r.randint(1, length)
        if self.r.random() < 0.3:
            return f"{name}({s}:)"
        return f"{name}({s}:{self.r.randint(1, length - s + 1)})"

    def st_cmp(self):
        a = self.r.choice(["GA", "GB"] + (["GA2"] if self.midA else []))
        b = self.r.choice([f"'{self.word(self.r.randint(1, 20), True)}'", "W1", "GA", "GB", "SPACES"])
        if self.r.random() < 0.3:
            rm = self.refmod("GA", self.len_ga())
            if rm is not None:
                a = rm
        return [f"IF {a} = {b} DISPLAY 'Y' ELSE DISPLAY 'N' END-IF"]

    def st_inspect(self):
        g = self.r.choice(["GA", "GB"] + (["GA2"] if self.midA else []))
        if self.r.random() < 0.6:
            return ["MOVE 0 TO K", f"INSPECT {g} TALLYING K FOR ALL '{self.r.choice(LETTERS + ' ')}'"]
        a, b = self.r.choice(LETTERS), self.r.choice(LETTERS)
        return [f"INSPECT {g} REPLACING ALL '{a}' BY '{b}'"]

    def st_string(self):
        c = self.r.random()
        if c < 0.5:
            srcs = " ".join(self.r.choice(["GA", "GB", "'*'", "WS"] + (["GA2"] if self.midA else []))
                            for _ in range(self.r.randint(1, 3)))
            return ["MOVE SPACES TO W1",
                    f"STRING {srcs} DELIMITED BY SIZE INTO W1 ON OVERFLOW DISPLAY 'OV' END-STRING"]
        if c < 0.8 or not self.unsafe:
            self.dirty()
            dst = "GA2" if self.midA and self.r.random() < 0.4 else "GA"
            return [f"STRING WS DELIMITED BY SIZE INTO {dst} ON OVERFLOW DISPLAY 'OV' END-STRING"]
        # G-odostring
        self.nb = None
        return ["STRING WS DELIMITED BY SIZE INTO GB END-STRING"] + self.fix_nb()

    def st_unstring(self):
        c = self.r.random()
        if c < 0.5:
            g = self.r.choice(["GA", "GB"] + (["GA2"] if self.midA else []))
            return ["MOVE SPACES TO W1 W2", f"UNSTRING {g} DELIMITED BY ' ' INTO W1 W2 END-UNSTRING"]
        if c < 0.8 or not self.unsafe:
            self.dirty()
            return ["UNSTRING WS DELIMITED BY ' ' INTO GA W2 END-UNSTRING"]
        # G-odounstring
        return ["UNSTRING WS DELIMITED BY ' ' INTO GB W2 END-UNSTRING"] + self.fix_nb()

    def st_display(self):
        g = self.r.choice(["GA", "GB"] + (["GA2"] if self.midA else []))
        rm = self.refmod("GB", self.len_gb()) if self.r.random() < 0.3 else None
        return [f"DISPLAY 'D [' {rm or g} ']'"]

    def st_search(self):
        start = self.r.randint(1, self.hiA)
        x = self.word(self.wA)
        return [f"SET IXA TO {start}",
                f"SEARCH TA AT END DISPLAY 'END' WHEN EA(IXA) = '{x}' DISPLAY 'F' "
                "WHEN EA(IXA) = SPACES DISPLAY 'S' END-SEARCH",
                "SET I TO IXA", "DISPLAY 'I ' I"]

    def st_search_all(self):
        out = self.keys()
        c = self.r.random()
        if c < 0.6 and self.nb > 0:
            x = self.kb[self.r.randint(0, self.nb - 1)]
        elif c < 0.8 and self.nb < self.hiB:
            x = self.kb[self.r.randint(self.nb, self.hiB - 1)]
        else:
            x = self.r.choice([ch for ch in "ABCDEFGHIJKLMNOPQRSTUVWXYZ" if ch not in self.kb])
        return out + [f"SEARCH ALL TB AT END DISPLAY 'END' WHEN KB(IXB) = '{x}' SET I TO IXB "
                      "DISPLAY 'F ' I END-SEARCH"]

    def st_loop(self):
        return ["PERFORM VARYING I FROM 1 BY 1 UNTIL I > NA DISPLAY 'L ' EA(I) END-PERFORM"]

    def st_refmod_write(self):
        rm = self.refmod("GA", self.len_ga())
        if rm is None:
            return None
        self.dirty()
        return [f"MOVE '{self.word(self.r.randint(1, 6))}' TO {rm}"]

    def st_file(self):
        if not self.file:
            return None
        out = ["OPEN OUTPUT OF1", "DISPLAY 'FO ' FS1"]
        m = self.r.randint(1, 3)
        for _ in range(m):
            v = self.r.randint(1, 6)
            out.append(f"MOVE {v} TO FN")
            out.append(f"MOVE '{self.word(2)}' TO FH")
            for k in range(1, self.r.randint(v, 6) + 1):
                out.append(f"MOVE '{self.r.choice(LETTERS)}' TO FT({k})")
            out += ["WRITE FR", "DISPLAY 'FW ' FS1"]
        out += ["CLOSE OF1", "OPEN INPUT OF1"]
        for _ in range(m + 1):
            out += ["MOVE SPACES TO W1", "READ OF1 INTO W1", "DISPLAY 'FR ' FS1 ' [' W1 ']'"]
        out += ["DISPLAY 'FN ' FN ' [' FR ']'", "CLOSE OF1"]
        return out

    def st_mix(self):
        """A step that sets an object outside its range, then references its table."""
        if self.r.random() < 0.5 or self.hiB == 9 and self.loB == 0:
            bad = self.hiA + 1 if self.loA == 0 or self.r.random() < 0.5 else self.loA - 1
            ref = self.r.choice(["DISPLAY 'X [' GA ']'", "MOVE GA TO W1", "MOVE EA(1) TO W2",
                                 "IF EA(1) = 'Q' DISPLAY 'Y' END-IF", "MOVE 'Q' TO EA(1)",
                                 "SET IXA TO 1 SEARCH TA WHEN EA(IXA) = 'Q' DISPLAY 'F' END-SEARCH"])
            return [f"MOVE {bad} TO NA", ref]
        bad = self.hiB + 1 if self.hiB < 9 else self.loB - 1
        ref = self.r.choice(["DISPLAY 'X [' GB ']'", "MOVE GB TO W1", "MOVE KB(1) TO W2",
                             "SEARCH ALL TB WHEN KB(IXB) = 'Q' DISPLAY 'F' END-SEARCH"])
        return [f"MOVE {bad} TO NB", ref]


STEPS = [("st_setn", 6), ("st_move_to_ga", 4), ("st_move_from_ga", 4), ("st_move_to_gb", 4),
         ("st_move_gb_ga", 2), ("st_elem_move", 5), ("st_elem_read", 4), ("st_elem_num", 3),
         ("st_cmp", 4), ("st_inspect", 3), ("st_string", 3), ("st_unstring", 3), ("st_display", 3),
         ("st_search", 3), ("st_search_all", 3), ("st_loop", 2), ("st_refmod_write", 2), ("st_file", 2)]


def program(rng, k, mixed, unsafe):
    g = Gen(rng, mixed, unsafe)
    mix_at = rng.randint(0, k - 1) if mixed else None
    names, weights = zip(*STEPS)
    used = {}
    body = g.init() + g.trace()
    for i in range(k):
        if i == mix_at:
            lines, name = g.st_mix(), "st_mix"
        else:
            while True:
                name = rng.choices(names, weights)[0]
                lines = getattr(g, name)()
                if lines is not None:
                    break
        used[name] = used.get(name, 0) + 1
        body += [f"DISPLAY 'S {i:02d}'"] + lines + g.trace()
    sel, fd = g.file_text()
    head = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. ODOT.", "       ENVIRONMENT DIVISION."]
    if sel:
        head += ["       INPUT-OUTPUT SECTION."] + sel
    head += ["       DATA DIVISION."] + fd + ["       WORKING-STORAGE SECTION."] + g.data()
    lines = head + ["       PROCEDURE DIVISION.", "       P0."]
    for s in body:
        lines += wrap(s)
    lines.append("           STOP RUN.")
    for ln in lines:
        assert len(ln) <= 72, ln
    return "\n".join(lines) + "\n", mix_at, used


def tools(root):
    cobolfe = os.environ.get("COBOLFE", os.path.join(root, "tools", "cobolfe", "cobolfe.py"))
    return (os.path.join(root, "scripts", "cobc.sh"), cobolfe, os.path.join(root, ".lake", "build", "bin", "cobolrun"),
            os.path.join(root, "third_party", "gnucobol", "usr", "lib", "x86_64-linux-gnu"))


def run(src, wd, name, root, flags=None, allow_unsup=False):
    """GnuCOBOL's DISPLAY lines and the model's (a last line `<model: SIGNAL>` when it does not
    stop normally), or an error (also when the front end reports an unsupported construct, unless
    allow_unsup)."""
    cobc, cobolfe, cobolrun, libdir = tools(root)
    os.makedirs(wd, exist_ok=True)
    base = os.path.join(wd, name)
    with open(base + ".cob", "w") as fh:
        fh.write(src)
    c = subprocess.run([cobc, "-x"] + (flags or COBC_FLAGS) + ["-o", base, base + ".cob"], capture_output=True,
                       text=True, timeout=120)
    if c.returncode != 0:
        return None, "cobc: " + c.stderr[-800:]
    try:
        r = subprocess.run([base], capture_output=True, env=dict(os.environ, LD_LIBRARY_PATH=libdir), cwd=wd,
                           timeout=20)
    except subprocess.TimeoutExpired:
        return None, "gnucobol timeout"
    g = r.stdout.decode("latin-1").splitlines()
    fe = subprocess.run([sys.executable, "-I", "-B", cobolfe, base + ".cob", "--profile", "gnucobol", "--main",
                         "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0:
        return None, "cobolfe: " + fe.stderr[-800:]
    if "unsupported" in fe.stderr and not allow_unsup:
        return None, "frontend-unsupported: " + fe.stderr[-800:]
    try:
        lr = subprocess.run([cobolrun, base + ".fe.json"], capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired:
        return None, "cobolrun timeout"
    if lr.returncode != 0:
        return None, "cobolrun: " + lr.stderr[-800:]
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop"):
        m.append("<model: " + res["signal"] + ">")
    if r.returncode != 0:
        g.append(f"<gnucobol: exit {r.returncode}>")
    return (g, m), None


def mixed_ok(g, m, mix_at):
    """The model agrees with GnuCOBOL up to its stop, stops with a range fault, and the last step
    marker it shows is the mixing step's."""
    if not m or m[-1] != "<model: fault:Cobol.Fault.range>":
        return False
    shown = m[:-1]
    if shown != g[:len(shown)]:
        return False
    marks = [ln for ln in shown if ln.startswith("S ") and ln[2:].isdigit()]
    return bool(marks) and int(marks[-1][2:]) == mix_at


def bump(tally, out, case, status):
    tally[status] = tally.get(status, 0) + 1
    with open(os.path.join(out, "results.jsonl"), "a") as fh:
        fh.write(json.dumps({"case": case, "status": status}) + "\n")


def run_cases(paths, out, root):
    """Hand cases (each says what to expect in its comment; a line `      * COBC: flags` replaces
    GnuCOBOL's flags): print GnuCOBOL's and the model's lines side by side where they differ."""
    st = []
    for p in paths:
        name = os.path.splitext(os.path.basename(p))[0]
        with open(p) as fh:
            src = fh.read()
        flags = next((ln.split(":", 1)[1].split() for ln in src.splitlines() if ln.startswith("      * COBC:")),
                     None)
        outs, err = run(src, os.path.join(out, name), name, root, flags, allow_unsup=True)
        if err:
            print(f"{name}: error {err[:600]}")
            st.append("error")
            continue
        g, m = outs
        if g == m:
            print(f"{name}: agree ({len(g)} lines)")
            st.append("agree")
            continue
        st.append("differ")
        print(f"{name}: differ")
        for i in range(max(len(g), len(m))):
            a = g[i] if i < len(g) else ""
            b = m[i] if i < len(m) else ""
            print(f"  {'  ' if a == b else '!='} gnucobol {a!r:44} model {b!r}")
    print(f"{len(st)} cases: {st.count('agree')} agree, {st.count('differ')} differ, {st.count('error')} errors")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=20)
    ap.add_argument("--out", default=os.path.join(HERE, "out_odo"))
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(HERE)))
    ap.add_argument("--show", type=int, default=3)
    ap.add_argument("--mixed", action="store_true")
    ap.add_argument("--unsafe", action="store_true", help="also generate G-odostring and G-odounstring")
    ap.add_argument("--run", nargs="+", metavar="PROG.cob")
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    os.makedirs(a.out, exist_ok=True)
    if a.run:
        return run_cases(a.run, a.out, root)
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, shown, steps = {"ok": 0}, 0, {}
    for p in range(a.n):
        src, mix_at, used = program(random.Random(rng.random()), a.k, a.mixed, a.unsafe)
        for s, c in used.items():
            steps[s[3:]] = steps.get(s[3:], 0) + c
        name = f"OD{a.seed:02d}{p:03d}"
        outs, err = run(src, os.path.join(a.out, name), name, root)
        if err:
            status = err.split(":")[0].replace(" ", "-")
            bump(tally, a.out, p, status)
            if shown < a.show:
                shown += 1
                print(f"program {p}: {err[:600]}")
            continue
        g, m = outs
        if mixed_ok(g, m, mix_at) if a.mixed else g == m:
            bump(tally, a.out, p, "ok")
            continue
        bump(tally, a.out, p, "mismatch")
        if shown < a.show:
            shown += 1
            i = next((j for j, (x, y) in enumerate(zip(g, m)) if x != y), min(len(g), len(m)))
            print(f"program {p}: first difference at line {i}: gnucobol {g[i:i + 2]!r} model {m[i:i + 2]!r}"
                  f" ({len(g)} vs {len(m)} lines)" + (f", mixing step {mix_at}" if a.mixed else ""))
    print(json.dumps({"tally": tally, "steps": dict(sorted(steps.items()))}))
    return 0 if tally["ok"] == a.n else 1


if __name__ == "__main__":
    sys.exit(main())

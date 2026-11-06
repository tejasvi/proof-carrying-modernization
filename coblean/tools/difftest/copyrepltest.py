#!/usr/bin/env python3
"""Differential testing of COPY ... REPLACING, COPY ... OF/IN and the REPLACE statement.

Each random program is made of 2 to 5 units; a unit writes copybooks (and maybe a library
directory), adds data entries and statements, and DISPLAYs what the replacements produced, every
DISPLAY ending with '|'. The units:
  * tag      copybook entries named :TAG:-A, (TAG)-B, S-:TAG: and M-(TAG)-N, replaced by COPY
             REPLACING ==:TAG:== and ==(TAG)== (the replacement glues to the text on either side)
             or by a REPLACE statement around the COPY;
  * partial  LEADING / TRAILING partial words in COPY REPLACING or REPLACE (also a whole word,
             pseudo-text in lower case);
  * literal  literal operands (also as pseudo-text), numeric literals, and operands that do not
             match (the other quotation mark, 07 for 7);
  * ident    qualified and subscripted identifiers as operands (W OF G BY W IN G2, T (2 1));
  * multi    pseudo-text of several words across lines, comment lines in the copybook and in the
             COPY statement, separator commas and semicolons between words;
  * picture  ==X(5)== BY ==X(7)==, a digit inside PIC X(5), a level number (lengths show in the
             DISPLAY);
  * replace  REPLACE statements in the PROCEDURE DIVISION: a match across a line break, :TAG: in a
             statement, a second REPLACE replacing the first, REPLACE OFF;
  * cascade  COPY REPLACING under a REPLACE statement (COPY first, then REPLACE on its result) and a
             REPLACE match on copied text;
  * nested   nested COPY: the outer REPLACING applies to the inner copybook, or the inner COPY has
             its own REPLACING;
  * library  COPY name OF / IN 'library' (a directory under the program's directory, with a
             copybook of the same name next to the program), COPY 'name' and SUPPRESS;
  * order    the first matching operand wins and replaced text is not compared again;
  * inline   a COPY statement inside a statement (ADD COPY K. TO N.), with or without REPLACING.
A tag copybook is copied a second time with another tag in half the programs that have one.
GnuCOBOL (-std=ibm, -I the program's directory) and the front end + cobolrun (--profile
gnucobol) must agree on every line (ext_common.py statuses). Left out, where GnuCOBOL 3.2 departs
from IBM (reproducers in tools/difftest/copyrepl_cases): a pseudo-text-1 that is only a separator
comma or semicolon (G-sepcomma: GnuCOBOL never matches it), separator commas inside parentheses
(G-parencomma: GnuCOBOL does not take them as spaces), operands that differ from the text only in
the case of a literal (G-litcase: GnuCOBOL matches 'abc' by 'ABC'), debugging lines in the matched
text (G-dline: GnuCOBOL drops them before matching), blanks at the ends of a pseudo-text-2 that
glues to the text around it (G-ptblank: GnuCOBOL keeps them, == PAY == does not form PAY-WEEK
from :TAG:-WEEK), blanks inside partial-word delimiters (G-pwblank: cobc rejects LEADING == QA ==,
IBM's own examples have them) and an empty partial-word-2 (cobc 3.2 aborts).

usage: copyrepltest.py --root C --out DIR [--n N] [--seed S] [--k K] [--keep]
       copyrepltest.py --root C --out DIR --run PROG.cob...   (copied into DIR with the .cpy files
                                                              and lib* directories next to it)
"""
import json
import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402

A, B = "       ", "           "      # area A (column 8) and area B (column 12)
C = "      *"                         # a comment line


def lit(rng, n=3):
    return "".join(rng.choice("ABCDEFGHJKLMNPRSTUVWXYZ0123456789") for _ in range(n))


def case(rng, word):
    """A word in upper or lower case (words match in either case; literals never change)."""
    return word.lower() if rng.random() < 0.3 else word


def pt(rng, text):
    """Pseudo-text ==text== with or without blanks inside the delimiters."""
    return f"== {text} ==" if rng.random() < 0.3 else f"=={text}=="


class Unit:
    """One unit of a program: its data lines, statements, copybooks and library copybooks."""

    def __init__(self, prog, u):
        self.prog, self.u = prog, u
        self.data, self.proc, self.books, self.libs = [], [], {}, {}

    def book(self, lines, lib=None):
        name = f"C{self.prog.tag}U{self.u}{chr(65 + len(self.books) + len(self.libs))}"
        (self.books if lib is None else self.libs.setdefault(lib, {}))[name] = lines
        return name

    def copy(self, rng, name, pairs, area=B, of=None):
        """COPY name [OF lib] [SUPPRESS] [REPLACING pairs] . as wrapped lines."""
        head = f"COPY '{name}'" if rng.random() < 0.15 else f"COPY {name}"
        if of:
            head += f" {rng.choice(['OF', 'IN'])} '{of}'"
        if rng.random() < 0.15:
            head += " SUPPRESS"
        if not pairs:
            return E.wrap(head + ".", len(area))
        out = E.wrap(head + " REPLACING", len(area))
        for k, (a, b) in enumerate(pairs):
            last = "." if k == len(pairs) - 1 else ""
            if rng.random() < 0.5:
                out += E.wrap(f"{a} BY {b}{last}", len(area) + 4)
            else:
                out += E.wrap(a, len(area) + 4) + E.wrap(f"BY {b}{last}", len(area) + 4)
        return out


def u_tag(rng, un):
    t = f"T{un.u}{lit(rng, 2)}"
    va, vc, nb = lit(rng, rng.randint(1, 4)), lit(rng, 2), rng.randint(0, 999)
    vs, vm = lit(rng, 2), lit(rng, 3)
    lines = [f"{A}01 :TAG:-G.", f"{B}05 :TAG:-A PIC X(4) VALUE '{va}'.",
             f"{B}05 (TAG)-B PIC 9(3) VALUE {nb}.", f"{B}05 :TAG:-C PIC X(2) VALUE '{vc}'.",
             f"{B}05 S-:TAG: PIC X(2) VALUE '{vs}'.", f"{B}05 M-(TAG)-N PIC X(3) VALUE '{vm}'."]
    name = un.book(lines)
    # no blanks inside pseudo-text-2: GnuCOBOL would keep them before -A, -B (G-ptblank)
    pairs = [(pt(rng, ":TAG:"), f"=={t}=="), (pt(rng, "(TAG)"), f"=={case(rng, t)}==")]
    rng.shuffle(pairs)
    if rng.random() < 0.5:
        un.data += un.copy(rng, name, pairs, A)
    else:
        un.data += [f"{A}REPLACE {pairs[0][0]} BY {pairs[0][1]}", f"{A}    {pairs[1][0]} BY {pairs[1][1]}."]
        un.data += un.copy(rng, name, [], A) + [f"{A}REPLACE OFF."]
    un.proc += [f"{B}DISPLAY {t}-A '|' {t}-B '|' {t}-C '|'.", f"{B}DISPLAY S-{t} '|' M-{t}-N '|'."]
    if rng.random() < 0.5:
        # the same copybook again with another tag (CardDemo copies CSSETATY so, five times)
        t2 = f"V{un.u}{lit(rng, 2)}"
        un.data += un.copy(rng, name, [(pt(rng, ":TAG:"), f"=={t2}=="), (pt(rng, "(TAG)"), f"=={t2}==")], A)
        un.proc += [f"{B}DISPLAY {t2}-B '|' S-{t2} '|' M-{t2}-N '|'."]


def u_inline(rng, un):
    n, d = f"I{un.u}{lit(rng, 2)}", rng.randint(1, 7)
    un.data += [f"{A}01 {n} PIC 9(2) VALUE {d}."]
    name = un.book([f"{B}    3"])
    # a COPY statement inside a statement (NIST SM101A: ADD COPY K1P01. TO WRK-DS-05V00.)
    pairs = [("==3==", f"=={rng.randint(4, 9)}==")] if rng.random() < 0.7 else []
    un.proc += [f"{B}ADD"] + un.copy(rng, name, pairs, B + "    ") + [f"{B}    TO {n}.", f"{B}DISPLAY {n} '|'."]


def u_partial(rng, un):
    p, s = f"QJ{un.u}", f"WK{un.u}"
    n1, n2 = f"ZN{un.u}{lit(rng, 1)}", f"ZT{un.u}{lit(rng, 1)}"
    vals = [lit(rng, 2) for _ in range(4)]
    lines = [f"{A}01 {p}-ALPHA PIC X(3) VALUE '{vals[0]}'.", f"{A}01 {p} PIC X(2) VALUE '{vals[1]}'.",
             f"{A}01 BETA-{s} PIC X(2) VALUE '{vals[2]}'.", f"{A}01 GAMMA{un.u} PIC X(2) VALUE '{vals[3]}'."]
    # no blanks inside partial-word delimiters (G-pwblank: cobc rejects them)
    pairs = [(f"LEADING =={case(rng, p)}==", f"=={n1}=="), (f"TRAILING =={case(rng, s)}==", f"=={n2}==")]
    rng.shuffle(pairs)
    if rng.random() < 0.6:
        un.data += un.copy(rng, un.book(lines), pairs, A)
    else:
        un.data += [f"{A}REPLACE {pairs[0][0]} BY {pairs[0][1]}", f"{A}    {pairs[1][0]} BY {pairs[1][1]}."]
        un.data += lines + [f"{A}REPLACE OFF."]
    un.proc += [f"{B}DISPLAY {n1}-ALPHA '|' {n1} '|' BETA-{n2} '|' GAMMA{un.u} '|'."]


def u_literal(rng, un):
    n = f"N{un.u}{lit(rng, 2)}"
    l1, l2, l3 = (f"L{un.u}{lit(rng, 2)}" for _ in range(3))
    m1, m3 = lit(rng, rng.randint(1, 5)), lit(rng, rng.randint(1, 5))
    k = rng.randint(1, 9)
    un.data += [f"{A}01 {n} PIC 9(2) VALUE 0."]
    lines = [f"{B}DISPLAY '{l1}' '{l2}' '|'.", f'{B}DISPLAY "{l3}" \'|\'.', f"{B}MOVE {k} TO {n}.",
             f"{B}DISPLAY {n} '|'.", f"{B}MOVE 0{k} TO {n}.", f"{B}DISPLAY {n} '|'."]
    pairs = [(f"'{l1}'", f"'{m1}'"), (pt(rng, f'"{l3}"'), pt(rng, f"'{m3}'")), (str(k), str((k + 4) % 9 + 1))]
    if rng.random() < 0.5:
        pairs.append((f'"{l2}"', "'NOMATCH'"))        # the other quotation mark: no match
    if rng.random() < 0.5:
        pairs.append((f"0{(k + 2) % 9 + 1}", "88"))   # not in the text
    rng.shuffle(pairs)
    un.proc += un.copy(rng, un.book(lines), pairs)


def u_ident(rng, un):
    g1, g2, w, r, t = (f"{c}{un.u}{lit(rng, 2)}" for c in "GHWRT")
    v = [lit(rng, 1) for _ in range(6)]
    un.data += [f"{A}01 {g1}.", f"{B}05 {w} PIC X VALUE '{v[0]}'.", f"{A}01 {g2}.",
                f"{B}05 {w} PIC X VALUE '{v[1]}'.", f"{A}01 {r} PIC X VALUE SPACE.",
                f"{A}01 {t}-T VALUE '{''.join(v[2:])}'.", f"{B}05 {t}-R OCCURS 2.", f"{B}   10 {t} PIC X OCCURS 2."]
    i, j = rng.randint(1, 2), rng.randint(1, 2)
    lines = [f"{B}MOVE {w} OF {g1} TO {r}.", f"{B}DISPLAY {r} '|'.", f"{B}MOVE {t} ({i} {j}) TO {r}.",
             f"{B}DISPLAY {r} '|'.", f"{B}MOVE {t} ({3 - i} {j}) TO {r}.", f"{B}DISPLAY {r} '|'."]
    pairs = []
    if rng.random() < 0.7:
        pairs.append((f"{case(rng, w)} OF {g1}", f"{w} {rng.choice(['OF', 'IN'])} {g2}"))
    if rng.random() < 0.7 or not pairs:
        sp = " " if rng.random() < 0.5 else ""
        pairs.append((f"{t} ({sp}{i} {j}{sp})", f"{t} ({3 - j} {3 - i})"))
    rng.shuffle(pairs)
    un.proc += un.copy(rng, un.book(lines), pairs)


def u_multi(rng, un):
    r1, r2 = f"R{un.u}{lit(rng, 2)}", f"S{un.u}{lit(rng, 2)}"
    p1, p2, q1, q2 = (lit(rng, 3) for _ in range(4))
    un.data += [f"{A}01 {r1} PIC X(3) VALUE SPACE.", f"{A}01 {r2} PIC X(3) VALUE SPACE."]
    sep = rng.choice([" ", ", ", "; "])
    lines = [f"{B}MOVE '{p1}' TO {r1}", f"{C}   A COMMENT LINE IN THE COPYBOOK", f"{B}MOVE '{p2}'",
             f"{B}     TO {r2}.", f"{B}DISPLAY {r1}{sep}{r2} '|'."]
    name = un.book(lines)
    k = rng.random()
    if k < 0.4:
        # pseudo-text across lines, with a comment line inside it
        un.proc += E.wrap(f"COPY {name} REPLACING", 11) + [
            f"{B}    =={case(rng, 'TO')} {r1}", f"{C}   A COMMENT LINE IN THE COPY STATEMENT",
            f"{B}    MOVE '{p2}'=="] + E.wrap(f"BY ==TO {r1} MOVE '{q2}'==.", 15)
    elif k < 0.7:
        un.proc += un.copy(rng, name, [(pt(rng, f"MOVE  '{p1}'  TO {r1}"), pt(rng, f"MOVE '{q1}' TO {r1}"))])
    else:
        un.proc += un.copy(rng, name, [(pt(rng, f"{r1} {r2}"), pt(rng, f"{r2}{sep}{r1}"))])


def u_picture(rng, un):
    v = f"V{un.u}{lit(rng, 2)}"
    s, d = lit(rng, rng.randint(1, 4)), rng.randint(0, 99)
    lines = [f"{A}01 {v}.", f"{B}05 {v}-A PIC X(5) VALUE '{s}'.", f"{B}05 {v}-B PIC 9(3) VALUE {d}."]
    choice = rng.choice([("==X(5)==", "==X(7)=="), ("==5==", "==6=="), ("==PIC 9(3)==", "==PIC 9(4)=="),
                         ("==05==", "==10=="), ("== 9(3) ==", "== 9(3)V9 ==")])
    un.data += un.copy(rng, un.book(lines), [choice], A)
    un.proc += [f"{B}DISPLAY {v}-A '|' {v}-B '|'."]


def u_replace(rng, un):
    k1, k2, k3, k4 = (f"K{un.u}{lit(rng, 2)}" for _ in range(4))
    s = f":S{un.u}:"
    un.proc += [f"{A}REPLACE ==DISPLAY '{k1}'== BY ==DISPLAY '{k2}'==", f"{A}        {pt(rng, s)} BY =='{k3}'==."]
    un.proc += [f"{B}DISPLAY '{k1}' '|'.", f"{B}DISPLAY", f"{B}    '{k1}' '|'.", f"{B}DISPLAY {s} '|'."]
    if rng.random() < 0.5:
        un.proc += [f"{A}REPLACE =='{k1}'== BY =='{k4}'==."]
        un.proc += [f"{B}DISPLAY '{k1}' '{k2}' '|'."]
    un.proc += [f"{A}REPLACE OFF.", f"{B}DISPLAY '{k1}' '|'."]


def u_cascade(rng, un):
    a1, b1, c1 = (f"{c}{un.u}{lit(rng, 2)}" for c in "ABC")
    un.data += [f"{A}01 {a1} PIC X(2) VALUE 'a{un.u}'.", f"{A}01 {b1} PIC X(2) VALUE 'b{un.u}'.",
                f"{A}01 {c1} PIC X(2) VALUE 'c{un.u}'."]
    d1, e1 = f"D{un.u}{lit(rng, 2)}", f"E{un.u}{lit(rng, 2)}"
    name = un.book([f"{B}DISPLAY {a1} '|'."])
    name2 = un.book([f"{B}DISPLAY '{d1}' '|'."])
    un.proc += [f"{A}REPLACE {pt(rng, b1)} BY {pt(rng, c1)}", f"{A}        =='{d1}'== BY =='{e1}'==."]
    un.proc += un.copy(rng, name, [(pt(rng, a1), pt(rng, b1))])
    un.proc += un.copy(rng, name2, [])
    un.proc += [f"{A}REPLACE OFF."]


def u_nested(rng, un):
    n1, n2, o2 = (f"N{un.u}{lit(rng, 2)}" for _ in range(3))
    inner = un.book([f"{B}DISPLAY '{n2}' '{n1}' '|'."])
    if rng.random() < 0.5:
        outer = un.book([f"{B}DISPLAY '{n1}' '|'.", f"{B}COPY {inner}."])
        un.proc += un.copy(rng, outer, [(pt(rng, f"'{n2}'"), pt(rng, f"'{o2}'"))])
    else:
        outer = un.book([f"{B}DISPLAY '{n1}' '|'."] + E.wrap(f"COPY {inner} REPLACING =='{n2}'== BY =='{o2}'==.", 11))
        un.proc += un.copy(rng, outer, [])


def u_library(rng, un):
    lib = f"lib{un.prog.tag.lower()}{un.u}"
    t1, t2 = f"P{un.u}{lit(rng, 2)}", f"Q{un.u}{lit(rng, 2)}"
    name = un.book([f"{B}DISPLAY '{t1}' '|'."])
    un.libs.setdefault(lib, {})[name] = [f"{B}DISPLAY '{t2}' '|'."]
    un.proc += un.copy(rng, name, [], of=lib if rng.random() < 0.5 else None)
    un.proc += un.copy(rng, name, [(pt(rng, f"'{t2}'"), pt(rng, f"'{t1}{t2}'"))] if rng.random() < 0.5 else [], of=lib)


def u_order(rng, un):
    a, b, c = (f"O{un.u}{lit(rng, 2)}" for _ in range(3))
    name = un.book([f"{B}DISPLAY '{a}' '{b}' '|'."])
    if rng.random() < 0.5:
        pairs = [(f"=='{a}'==", f"=='{c}'=="), (f"=='{a}' '{b}'==", "=='WHOLE'==")]
    else:
        pairs = [(f"=='{a}'==", f"=='{b}'=="), (f"=='{b}'==", f"=='{c}'==")]
    un.proc += un.copy(rng, name, pairs)


UNITS = [u_tag, u_partial, u_literal, u_ident, u_multi, u_picture, u_replace, u_cascade, u_nested,
         u_library, u_order, u_inline]


class Prog:
    def __init__(self, tag):
        self.tag = tag


def program(rng, k, tag):
    """(source text, {copybook name: lines}, {library: {name: lines}}, unit names)."""
    pr = Prog(tag)
    units, names = [], []
    for u in range(rng.randint(2, max(2, k))):
        un = Unit(pr, u)
        f = rng.choice(UNITS)
        f(rng, un)
        units.append(un)
        names.append(f.__name__[2:])
    data = [x for un in units for x in un.data]
    proc = [x for un in units for x in un.proc]
    src = E.check_lines(E.header(f"P{tag}", data) + proc + [f"{B}STOP RUN."])
    books = {n: E.check_lines(v) for un in units for n, v in un.books.items()}
    libs = {}
    for un in units:
        for lib, bs in un.libs.items():
            libs.setdefault(lib, {}).update({n: E.check_lines(v) for n, v in bs.items()})
    return "\n".join(src) + "\n", books, libs, names


def run(D, base, src, books, libs):
    """Write the program and its copybooks next to it, run both ways (ext_common.run with -I)."""
    d = os.path.dirname(base)
    for n, lines in books.items():
        with open(os.path.join(d, n + ".cpy"), "w", encoding="latin-1") as fh:
            fh.write("\n".join(lines) + "\n")
    for lib, bs in libs.items():
        os.makedirs(os.path.join(d, lib), exist_ok=True)
        for n, lines in bs.items():
            with open(os.path.join(d, lib, n + ".cpy"), "w", encoding="latin-1") as fh:
                fh.write("\n".join(lines) + "\n")
    with open(base + ".cob", "w", encoding="latin-1") as fh:
        fh.write(src)
    return run_file(D, base)


def gnucobol(D, base):
    """("ok", DISPLAY lines) or (status, detail) of GnuCOBOL on base.cob (copybooks next to it)."""
    d = os.path.dirname(base)
    c = subprocess.run([D.COBC, "-x"] + E.PLAIN_COBC + ["-I", d, "-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120, cwd=d)
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
    return "ok", g


def model(D, base):
    """("ok", DISPLAY lines) or (status, detail) of the front end + cobolrun on base.cob."""
    d = os.path.dirname(base)
    fe = subprocess.run([sys.executable, "-I", D.COBOLFE, base + ".cob"] + E.PLAIN_FE +
                        ["--main", "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0:
        return "fe-error", fe.stderr[-2000:]
    unsup = [ln for ln in fe.stderr.splitlines() if "unsupported" in ln]
    if unsup:
        return "fe-unsupported", "\n".join(unsup)[:2000]
    try:
        lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True, timeout=60, cwd=d)
    except subprocess.TimeoutExpired:
        return "lean-timeout", None
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-2000:]
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop:"):
        return "lean-signal", res["signal"]
    return "ok", m


def run_file(D, base):
    gs, g = gnucobol(D, base)
    if gs != "ok":
        return gs, g
    ms, m = model(D, base)
    if ms != "ok":
        return ms, m
    if g != m:
        return "mismatch", (g, m)
    return "ok", (g, m)


def run_cases(D, out, progs):
    """--run: copy each program, the .cpy files of its directory and its lib* directories into OUT
    and run it there: status, then the lines (= equal, ! different; model lines also when cobc
    rejects the program)."""
    import shutil
    for p in progs:
        src = os.path.dirname(os.path.abspath(p))
        for f in sorted(os.listdir(src)):
            q = os.path.join(src, f)
            if f.endswith(".cpy") or f == os.path.basename(p):
                shutil.copy(q, os.path.join(out, f))
            elif f.startswith("lib") and os.path.isdir(q) and not os.path.exists(os.path.join(out, f)):
                shutil.copytree(q, os.path.join(out, f))
        base = os.path.join(out, os.path.splitext(os.path.basename(p))[0])
        gs, g = gnucobol(D, base)
        ms, m = model(D, base)
        st = gs if gs != "ok" else ms if ms != "ok" else "ok" if g == m else "mismatch"
        print(f"{os.path.basename(p)}: {st}")
        if gs != "ok":
            print("  gnucobol: " + str(g)[:600].replace("\n", " | "))
            g = []
        if ms != "ok":
            print("  model: " + str(m)[:600].replace("\n", " | "))
            m = []
        for i in range(max(len(g), len(m))):
            gl = g[i] if i < len(g) else "<none>"
            ml = m[i] if i < len(m) else "<none>"
            print(f"  {'=' if gl == ml else '!'} gnucobol {gl!r} model {ml!r}")


def main():
    ap = E.arg_parser(__doc__, 60, 5)
    ap.add_argument("--run", nargs="*", default=None, help="run these programs (copybooks next to them)")
    a = ap.parse_args()
    D = E.difftest(a.root)
    os.makedirs(a.out, exist_ok=True)
    if a.run is not None:
        run_cases(D, a.out, a.run)
        return
    import random
    res = os.path.join(a.out, "results.jsonl")
    if os.path.exists(res):
        raise SystemExit(f"{res} exists")
    rng = random.Random(a.seed)
    tally, shown = {}, 0
    for p in range(a.n):
        tag = f"{a.seed}X{p:04d}"
        src, books, libs, names = program(rng, a.k, tag)
        base = os.path.join(a.out, f"p{a.seed}_{p:04d}")
        status, detail = run(D, base, src, books, libs)
        tally[status] = tally.get(status, 0) + 1
        with open(res, "a") as fh:
            fh.write(json.dumps({"case": p, "status": status, "units": names}) + "\n")
        if status != "ok":
            with open(base + ".detail", "w", encoding="latin-1") as fh:
                fh.write(f"{status}\n{detail}\n")
        if status != "ok" and shown < a.show:
            shown += 1
            if status == "mismatch":
                print(f"program {p}: mismatch at line {E.first_diff(*detail)}")
            else:
                print(f"program {p}: {status}: {str(detail)[:600]}")
    print(json.dumps({"tally": tally}))


if __name__ == "__main__":
    main()

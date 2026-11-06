#!/usr/bin/env python3
"""Differential testing of nested and batched programs, GLOBAL and EXTERNAL data, CALL forms.

Each random case is one source file: a main program, one to three programs it contains (some
COMMON, some containing a program of their own), and zero to two further separately compiled
programs after it (a batch, each ended by END PROGRAM; one may contain a program). The programs
use:
  - GLOBAL items of their containing programs (an alphanumeric item, a numeric item with a level-88
    condition name, a table with a GLOBAL index), and local items that hide a global name;
  - one EXTERNAL record described with different subordinate items in the main program, a
    contained program and a batch program (same length);
  - CALL literal and CALL identifier (the name in an item longer than the name) of every program a
    program may call by IBM's rules (its directly contained programs, COMMON programs contained in
    a program that contains it, the separately compiled programs), USING arguments BY REFERENCE and
    BY CONTENT (items and alphanumeric literals), ON EXCEPTION / ON OVERFLOW / NOT ON EXCEPTION
    phrases, called programs that end by EXIT PROGRAM, GOBACK or their last statement, the same
    item passed BY REFERENCE for two parameters (one storage in the called program);
  - INITIAL called programs (contained or separately compiled), and CANCEL by literal and by
    identifier of programs that are not active;
  - RETURN-CODE set by called programs and shown by their callers (through an edited item);
  - optionally a GLOBAL file of the main program with a USE GLOBAL declarative, whose at-end
    condition a contained program raises by a READ without AT END;
  - a paragraph of the same name in every program, performed locally.
A program calls only programs after it in a random order (no recursion); persistent counters show
that a called program keeps its storage between calls. Every program displays what it sees.

GnuCOBOL (-std=ibm, the C code compiled as C17: tools/nist/cobc_ref.sh explains why) runs the
program in a fresh directory; the front end (tools/cobolfe, --profile gnucobol) extracts it and
cobolrun runs it. Both must agree exactly on the DISPLAY lines, and the model must end with STOP RUN.

Generation stays inside what the model supports exactly: BY REFERENCE arguments are items of the
caller's own WORKING-STORAGE, distinct or the same item twice (overlapping arguments, arguments in
GLOBAL or EXTERNAL storage and passed-on LINKAGE items can make copy-in/copy-out differ from shared
storage, and the front end makes such CALLs unsupported); no program outside the unit; only the
main program has a declarative, and only it and its contained programs do I/O. Items are
initialized by VALUE, the EXTERNAL record by MOVEs at the start, since uninitialized storage differs
(GnuCOBOL: spaces and zeros; cobolrun: zero bytes). GnuCOBOL 3.2 defects are left out:
  G-declcall: once a USE GLOBAL declarative of the main program has run for an I/O statement of a
    contained program, later CALLs of programs that were called before fail: the ON EXCEPTION /
    ON OVERFLOW phrase runs, or GnuCOBOL crashes (SIGSEGV; its handler prints "libcob: " and
    hangs). The run should go on as without the declarative. The program that raises the
    condition is called last, and cases with the global file have no batch programs. Reproducer:
    tools/difftest/nested_cases/g_declcall.cob (--run).
  G-initialrc: after a CALL of an INITIAL separately compiled program GnuCOBOL sets the caller's
    RETURN-CODE to 0, not to the called program's value (IBM, RETURN-CODE: "the value of the
    RETURN-CODE special register is passed to the calling program"). RETURN-CODE is shown only
    after CALLs of other programs. Reproducer: nested_cases/g_initialrc.cob.
  G-cancelcommon: GnuCOBOL refuses ("attempt to CANCEL active program", run ends) a CANCEL of a
    COMMON program that has returned, issued by a program contained in its sibling. Only the main
    program and the programs one level down CANCEL. Reproducer: nested_cases/g_cancelcommon.cob.
  G-initialsib: a CALL of an INITIAL contained program also puts the programs contained in its
    sibling programs back in their initial state (IBM: the program and the programs it contains).
    INITIAL contained programs have no sibling with contained programs. Reproducer:
    nested_cases/g_initialsib.cob.
  G-initialnest: the second CALL of an INITIAL separately compiled program from a contained
    program stops GnuCOBOL with "attempt to CANCEL active program". INITIAL programs are called
    from separately compiled programs only. Reproducer: nested_cases/g_initialnest.cob.
  G-cancelinitial: a CANCEL of an INITIAL program that has returned, from a program other than
    the one that called it, stops GnuCOBOL with "attempt to CANCEL active program". INITIAL
    programs are not canceled (their CALLs start them in their initial state anyway). Reproducer:
    nested_cases/g_cancelinitial.cob.

usage: nestedtest.py [--n N] [--seed S] [--out DIR] [--root TREE] [--frontend DIR] [--show K]
       nestedtest.py --run PROG.cob... [--out DIR] [--root TREE]   (tools/difftest/nested_cases)
  --root: the coblean tree whose front end and cobolrun are tested (default: this script's)
  --frontend: the front end directory used instead of TREE/tools/cobolfe (planted errors)
"""
import argparse
import json
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
# parameter shapes: (PICTURE, length, alphanumeric?)
SHAPES = [("X(4)", 4, True), ("9(3)", 3, False), ("X(5)", 5, True), ("X(3)", 3, True)]


def wrap(text, indent=11):
    """Fixed-format lines within column 72, split at blanks outside literals."""
    words, cur, inq = [], "", False
    for ch in text:
        if ch in "'\"":
            inq = not inq
        if ch == " " and not inq:
            words.append(cur)
            cur = ""
        else:
            cur += ch
    words.append(cur)
    out, line = [], " " * indent
    for w in words:
        if not w:
            continue
        if len(line) + 1 + len(w) > 72:
            out.append(line)
            line = " " * (indent + 4) + w
        else:
            line = line + (" " if line.strip() else "") + w
    out.append(line)
    assert all(len(ln) <= 72 for ln in out), out
    return out


class Prog:
    def __init__(self, name, parent=None, batch=False):
        self.name, self.parent, self.batch = name, parent, batch
        self.children = []
        self.common = False
        self.rank = 0
        self.params = []          # shapes of the PROCEDURE DIVISION USING items
        self.globals = []         # (name, kind) of the GLOBAL items it declares
        self.hides = []           # global names it declares locally again
        self.ext = None           # its description of the EXTERNAL record: [(name, pic, len, alnum)]
        self.end = "EXIT PROGRAM"
        self.initial = False      # PROGRAM-ID ... INITIAL
        if parent is not None:
            parent.children.append(self)

    def ancestors(self):
        out, p = [], self.parent
        while p is not None:
            out.append(p)
            p = p.parent
        return out

    def outermost(self):
        return (self.ancestors() or [self])[-1]

    def within(self, q):
        return self is q or q in self.ancestors()


class Gen:
    def __init__(self, rng, name):
        self.rng, self.name = rng, name
        r = rng
        self.main = Prog(name + "M")
        progs = [self.main]
        for k in range(r.randint(1, 3)):
            c = Prog(f"{name}C{k}", self.main)
            c.common = r.random() < 0.5
            progs.append(c)
            if r.random() < 0.4:
                g = Prog(f"{name}C{k}N", c)
                g.common = r.random() < 0.3
                progs.append(g)
        # G-declcall (GnuCOBOL 3.2): once a USE GLOBAL declarative has run for an I/O statement of a
        # contained program, later CALLs of programs called before fail (ON EXCEPTION runs) or crash
        # GnuCOBOL: the program that raises it is called last, and there are no batch programs
        self.use_file = r.random() < 0.5
        for k in range(0 if self.use_file else r.randint(0, 2)):
            b = Prog(f"{name}B{k}", None, batch=True)
            progs.append(b)
            if r.random() < 0.3:
                progs.append(Prog(f"{name}B{k}N", b))
        self.reader = None
        if self.use_file:
            self.reader = Prog(f"{name}R", self.main)
            progs.append(self.reader)
        self.progs = progs
        order = progs[1:]
        r.shuffle(order)
        for i, p in enumerate(order):
            p.rank = i + 1
        if self.reader is not None:
            self.reader.rank = len(progs) + 1
        for p in progs[1:]:
            # shapes may repeat: the same item can then be passed twice BY REFERENCE
            p.params = [] if p is self.reader else r.choices(SHAPES, k=r.randint(0, 3))
            # (G-initialsib: GnuCOBOL resets the programs contained in the siblings of an INITIAL
            # contained program when it is called)
            p.initial = p is not self.reader and r.random() < 0.25 and \
                (p.parent is None or not any(s.children for s in p.parent.children if s is not p))
            p.end = r.choice(["EXIT PROGRAM", "GOBACK", ""])
        self.main.globals = [("GA", "x6"), ("GN", "n4"), ("GT", "t")]
        for p in progs[1:]:
            if p.children and r.random() < 0.7:
                p.globals = [(f"G{p.name[-2:]}", "x6")]
            if not p.batch and p.parent is self.main and r.random() < 0.4:
                p.hides = ["GA"]
        self.use_ext = r.random() < 0.8
        if self.use_ext:
            self.main.ext = [("EXA", "X(4)", 4, True), ("EXB", "9(3)", 3, False)]
            cands = [p for p in progs[1:] if p is not self.reader]
            for p in r.sample(cands, min(len(cands), r.randint(1, 3))):
                # alphanumeric parts over EXA and a numeric one over EXB only: a numeric field over
                # bytes another program moves letters into would hold invalid data
                p.ext = r.choice([[("EXN", "X(4)", 4, True), ("EXP", "9(3)", 3, False)],
                                  [("EXC", "X(2)", 2, True), ("EXD", "X(2)", 2, True), ("EXF", "9(3)", 3, False)],
                                  [("EXG", "X(1)", 1, True), ("EXH", "X(3)", 3, True), ("EXK", "9(3)", 3, False)]])
        self.counts = {"calls": 0, "call_identifier": 0, "by_content": 0, "exception_phrases": 0,
                       "cancels": 0, "duplicate_args": 0}

    # ------------------------------------------------------------------ scope
    def callable(self, p, q):
        """IBM: a CALL in p may name q (and no recursion: q comes later)."""
        if q.rank <= p.rank or p.within(q) or (q.initial and p.parent is not None):
            # (G-initialnest: GnuCOBOL fails the second CALL of an INITIAL program from a
            # contained program)
            return False
        if q.parent is p:
            return True
        if q.common and q.parent in p.ancestors():
            return True
        return q.batch and q is not p.outermost()

    def visible_globals(self, p):
        """(name, kind, owner) of the global names p sees, innermost declaration first."""
        seen, out = set(), []
        local = {n for n, _ in p.globals} | set(p.hides)
        for n, k in p.globals:
            out.append((n, k, p))
            seen.add(n)
        for a in p.ancestors():
            for n, k in a.globals:
                if n not in seen and n not in local:
                    out.append((n, k, a))
                    seen.add(n)
        return out

    # ------------------------------------------------------------------ rendering
    def data(self, p):
        r = self.rng
        lines = ["       WORKING-STORAGE SECTION."]
        for n, k in p.globals:
            if k == "x6":
                lines.append(f"       01 {n} GLOBAL PIC X(6) VALUE '{n}{r.randint(10, 99):02d}xx'.")
            elif k == "n4":
                lines.append(f"       01 {n} GLOBAL PIC 9(4) VALUE {r.choice([10, 20, 30])}.")
                lines.append(f"          88 {n}-TEN VALUE 10.")
            else:
                lines.append(f"       01 {n} GLOBAL.")
                lines.append(f"          05 {n}E PIC X(2) OCCURS 3 INDEXED BY {n}X.")
        for n in p.hides:
            lines.append(f"       01 {n} PIC X(6) VALUE 'LOC{p.name[-2:]}x'.")
        lines.append(f"       01 CNT PIC 9(3) VALUE {r.randint(0, 5)}.")
        for i, (pic, ln, alnum) in enumerate(SHAPES):
            v = f"'{(p.name[-2:] + 'abcde')[:ln]}'" if alnum else str(r.randint(100, 999))
            lines.append(f"       01 W{i} PIC {pic} VALUE {v}.")
        lines.append("       01 PN PIC X(12) VALUE SPACES.")
        lines.append("       01 FLAG PIC X(2) VALUE '--'.")
        lines.append("       01 RCED PIC -9(4).")
        if p.ext is not None:
            lines.append("       01 EXREC EXTERNAL.")
            for n, pic, _, _ in p.ext:
                lines.append(f"          05 {n} PIC {pic}.")
        if p.params:
            lines.append("       LINKAGE SECTION.")
            for i, (pic, _, _) in enumerate(p.params):
                lines.append(f"       01 P{i} PIC {pic}.")
        return lines

    def items_of(self, p):
        """(reference, alphanumeric?, writable value maker) of the items p can name, for MOVE/ADD/DISPLAY."""
        out = [("CNT", False)]
        out += [(f"W{i}", s[2]) for i, s in enumerate(SHAPES)]
        out += [(f"P{i}", s[2]) for i, s in enumerate(p.params)]
        for n, k, _ in self.visible_globals(p):
            if k == "x6":
                out.append((n, True))
            elif k == "n4":
                out.append((n, False))
        out += [(n, True) for n in p.hides]
        if p.ext is not None:
            out += [(n, a) for n, _, _, a in p.ext]
        return out

    def show(self, p, tag):
        items = self.items_of(p)
        pick = self.rng.sample(items, min(len(items), self.rng.randint(2, 5)))
        return [f"DISPLAY '{tag} ' " + " ' ' ".join(n for n, _ in pick)]

    def change(self, p):
        r = self.rng
        n, alnum = r.choice(self.items_of(p))
        if alnum:
            return [f"MOVE '{r.choice(['Q', 'RS', 'TUV', 'W1X2'])}' TO {n}"]
        return [f"ADD {r.randint(1, 9)} TO {n}"]

    def call(self, p, q):
        r = self.rng
        out = []
        args = []
        for i, (pic, ln, alnum) in enumerate(q.params):
            k = SHAPES.index((pic, ln, alnum))
            mode = r.choice(["REFERENCE", "CONTENT", "CONTENT-LIT"] if alnum else ["REFERENCE", "CONTENT"])
            if mode == "CONTENT-LIT":
                args.append(("CONTENT", "'" + "LIT".ljust(ln, "*")[:ln] + "'"))
            else:
                args.append((mode, f"W{k}"))
        if r.random() < 0.5:
            out.append(f"MOVE '{q.name}' TO PN")
            target = "PN"
        else:
            target = f"'{q.name}'"
        using = ""
        if args:
            parts, last = [], None
            for mode, a in args:
                if mode != last or r.random() < 0.3:
                    parts.append(f"BY {mode}")
                    last = mode
                parts.append(a)
            using = " USING " + " ".join(parts)
        exc = ""
        ph = r.random()
        if ph < 0.25:
            exc = " ON EXCEPTION MOVE 'EX' TO FLAG NOT ON EXCEPTION MOVE 'NE' TO FLAG"
        elif ph < 0.4:
            exc = " ON OVERFLOW MOVE 'OV' TO FLAG"
        elif ph < 0.55:
            exc = " NOT ON EXCEPTION MOVE 'NX' TO FLAG"
        out.append(f"CALL {target}{using}{exc} END-CALL")
        self.counts["calls"] += 1
        self.counts["call_identifier"] += target == "PN"
        self.counts["by_content"] += any(m == "CONTENT" for m, _ in args)
        self.counts["duplicate_args"] += any(args[i] == args[j] and args[i][0] == "REFERENCE"
                                              for j in range(len(args)) for i in range(j))
        self.counts["exception_phrases"] += bool(exc)
        if exc:
            out.append("DISPLAY 'FLAG ' FLAG")
            out.append("MOVE '--' TO FLAG")
        if q.batch and not q.initial:
            # (G-initialrc: GnuCOBOL gives 0 after a CALL of an INITIAL separately compiled program)
            out += ["MOVE RETURN-CODE TO RCED", f"DISPLAY 'RC {q.name} ' RCED"]
        return out

    def cancel(self, q):
        """CANCEL of a program called later in the order (never active here)."""
        self.counts["cancels"] += 1
        if self.rng.random() < 0.5:
            return [f"MOVE '{q.name}' TO PN", "CANCEL PN"]
        return [f"CANCEL '{q.name}'"]

    def body(self, p):
        r = self.rng
        st = self.show(p, p.name + " IN")
        st.append("ADD 1 TO CNT")
        if not p.batch and p.parent is not None and r.random() < 0.3:
            st.append(f"MOVE {r.randint(0, 9)} TO RETURN-CODE")
        vg = {n: k for n, k, _ in self.visible_globals(p)}
        if "GN" in vg and r.random() < 0.6:
            st.append("IF GN-TEN DISPLAY 'GN TEN' ELSE DISPLAY 'GN NOT TEN' END-IF")
        if "GT" in vg and r.random() < 0.6:
            st += [f"SET GTX TO {r.randint(1, 3)}", f"MOVE '{r.choice(['ab', 'cd', 'ef'])}' TO GTE(GTX)",
                   "DISPLAY 'GT ' GTE(1) GTE(2) GTE(3)"]
        callees = [q for q in self.progs if self.callable(p, q) and q is not self.reader]
        steps = r.randint(2, 6)
        for _ in range(steps):
            c = r.random()
            if callees and c < 0.45:
                st += self.call(p, r.choice(callees))
            elif c < 0.7:
                st += self.change(p)
            elif callees and c < 0.82 and (p.parent is None or p.parent is self.main):
                # (G-cancelcommon: GnuCOBOL refuses a CANCEL from a program two levels down)
                targets = [q for q in callees if not q.initial]
                st += self.cancel(r.choice(targets)) if targets else self.change(p)
            elif c < 0.92:
                st.append("PERFORM SUB-P")
            else:
                st += self.show(p, p.name)
        # every program it may call is called at least once from the main program's subtree
        if p is self.main:
            for q in callees:
                st += self.call(p, q)
            if self.reader is not None:
                st += self.call(p, self.reader)
        if p is self.reader:
            st += ["OPEN INPUT TF", "READ TF", "DISPLAY 'READ ' TR", "READ TF",
                   "DISPLAY 'AFTER EOF ' DCNT", "CLOSE TF"]
        if p.batch:
            # last, so that its callers see this value whatever its own CALLs did (G-initialrc)
            st.append(f"MOVE {r.randint(0, 9)} TO RETURN-CODE")
        st += self.show(p, p.name + " OUT")
        return st

    def render_prog(self, p, out):
        a = out.append
        a("       IDENTIFICATION DIVISION.")
        attr = (" IS COMMON" if p.common else "") + (" INITIAL" if p.initial else "")
        a(f"       PROGRAM-ID. {p.name}{attr}.")
        if p is self.main and self.use_file:
            a("       ENVIRONMENT DIVISION.")
            a("       INPUT-OUTPUT SECTION.")
            a("       FILE-CONTROL.")
            a(f"           SELECT TF ASSIGN TO '{self.name}TF.DAT'")
            a("               ORGANIZATION IS SEQUENTIAL.")
        a("       DATA DIVISION.")
        if p is self.main and self.use_file:
            a("       FILE SECTION.")
            a("       FD TF GLOBAL.")
            a("       01 TR PIC X(8).")
        out.extend(self.data(p))
        if p is self.main and self.use_file:
            out.append("       01 DCNT GLOBAL PIC 9(2) VALUE 0.")
        using = (" USING " + " ".join(f"P{i}" for i in range(len(p.params)))) if p.params else ""
        a(f"       PROCEDURE DIVISION{using}.")
        if p is self.main and self.use_file:
            a("       DECLARATIVES.")
            a("       D-IN SECTION.")
            a("           USE GLOBAL AFTER STANDARD ERROR PROCEDURE ON INPUT.")
            a("       D-IN-1.")
            a("           ADD 1 TO DCNT.")
            a("           DISPLAY 'DECL ' DCNT.")
            a("       END DECLARATIVES.")
            a("       MAIN-S SECTION.")
        a("       MAIN-P.")
        if p is self.main:
            if self.use_ext:
                for line in ["MOVE 'eext' TO EXA", "MOVE 123 TO EXB"]:
                    out.extend(wrap(line))
            if self.use_file:
                for line in ["OPEN OUTPUT TF", "MOVE 'RECORD01' TO TR", "WRITE TR", "CLOSE TF"]:
                    out.extend(wrap(line))
        for s in self.body(p):
            out.extend(wrap(s))
        if p is self.main:
            # (the run's exit status is RETURN-CODE)
            out.extend(wrap("MOVE 0 TO RETURN-CODE"))
            out.extend(wrap("STOP RUN."))
        else:
            out.extend(wrap((p.end + ".") if p.end else "CONTINUE."))
        a("       SUB-P.")
        out.extend(wrap(f"DISPLAY 'SUB {p.name} ' CNT."))
        for c in p.children:
            self.render_prog(c, out)
        a(f"       END PROGRAM {p.name}.")

    def render(self):
        out = []
        for p in self.progs:
            if p.parent is None:
                self.render_prog(p, out)
        return "\n".join(out) + "\n"


def run(cmd, timeout, **kw):
    try:
        return subprocess.run(cmd, capture_output=True, timeout=timeout, **kw)
    except subprocess.TimeoutExpired:
        return None


def cobc_env(root):
    """GnuCOBOL 3.2 of the tree, as tools/nist/cobc_ref.sh sets it up (C code compiled as C17: as
    C23, GCC 15 rejects GnuCOBOL's calls of nested programs)."""
    g = os.path.join(root, "third_party", "gnucobol", "usr")
    lib = os.path.join(g, "lib", "x86_64-linux-gnu")
    return dict(os.environ, PATH=os.path.join(g, "bin") + ":" + os.environ.get("PATH", ""),
                LD_LIBRARY_PATH=lib, COB_CONFIG_DIR=os.path.join(g, "share", "gnucobol", "config"),
                COB_COPY_DIR=os.path.join(g, "share", "gnucobol", "copy"),
                COB_CFLAGS=f"-std=c17 -I{g}/include -pipe -Wno-unused -fsigned-char -Wno-pointer-sign",
                COB_LDFLAGS=f"-L{lib}", COB_LIBS=f"-L{lib} -lcob -lm -lgmp",
                COB_SWITCH_1="ON", COB_SWITCH_2="OFF"), os.path.join(g, "bin", "cobc")


def compare(base, wd, root, src, frontend=None):
    """Status, details and GnuCOBOL's lines of program `src` (written to base.cob)."""
    cobolfe = os.path.join(frontend or os.path.join(root, "tools", "cobolfe"), "cobolfe.py")
    cobolrun = os.path.join(root, ".lake", "build", "bin", "cobolrun")
    env, cobc = cobc_env(root)
    with open(base + ".cob", "w") as fh:
        fh.write(src)
    c = run(["nice", "-n", "10", cobc, "-x", "-std=ibm", "-o", base, base + ".cob"], 180, env=env, text=True)
    if c is None or c.returncode != 0:
        return "cobc-error", (c.stderr[-800:] if c else "timeout"), None
    r = run([base], 20, env=env, cwd=wd)
    if r is None:
        return "gnucobol-timeout", None, None
    g = r.stdout.decode("latin-1").splitlines()
    if r.returncode != 0:
        return "gnucobol-abend", {"rc": r.returncode, "stderr": r.stderr.decode("latin-1")[-300:]}, g
    fe = run([sys.executable, "-I", "-B", cobolfe, base + ".cob", "--profile", "gnucobol", "--main",
              "-o", base + ".fe.json"], 120, text=True, env=env)
    if fe is None or fe.returncode != 0:
        return "frontend-error", (fe.stderr[-800:] if fe else "timeout"), g
    if "unsupported" in fe.stderr:
        return "frontend-unsupported", fe.stderr[-800:], g
    cmd = [cobolrun, base + ".fe.json", "--fuel", "1000000"]
    with open(base + ".cmd.json", "w") as fh:
        json.dump(cmd, fh)
    lr = run(cmd, 60, text=True)
    if lr is None:
        return "lean-timeout", None, g
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-800:], g
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if res["signal"] != "stop:Cobol.StopKind.run":
        return "lean-signal", {"signal": res["signal"], "lines": len(m), "gnucobol_lines": len(g)}, g
    if g != m:
        k = next((i for i, (a, b) in enumerate(zip(g, m)) if a != b), min(len(g), len(m)))
        return "mismatch", {"line": k, "gnucobol": g[k:k + 3], "lean": m[k:k + 3]}, g
    return "ok", None, g


def run_repro(path, out, root, frontend=None):
    """A hand-written case: prints the verdict and, where the two sides differ, both outputs from
    the first difference."""
    name = os.path.splitext(os.path.basename(path))[0]
    wd = os.path.join(out, name)
    os.makedirs(wd)
    with open(path) as fh:
        src = fh.read()
    status, info, g = compare(os.path.join(wd, name), wd, root, src, frontend)
    print(f"{name}: {status}" + (f" ({len(g)} lines)" if status == "ok" else ""))
    if status == "mismatch":
        with open(os.path.join(wd, name + ".cmd.json")) as fh:
            cmd = json.load(fh)
        res = json.loads(subprocess.run(cmd, capture_output=True, text=True, timeout=60).stdout)
        m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
        k = info["line"]
        print("  gnucobol from line %d: %s" % (k, " | ".join(g[k:])))
        print("  model    from line %d: %s" % (k, " | ".join(m[k:])))
    elif status != "ok":
        print("  " + json.dumps(info)[:1500])
    return status


def coverage(gen, cov):
    cov["programs"] += len(gen.progs)
    cov["contained"] += sum(1 for p in gen.progs if p.parent is not None)
    cov["common"] += sum(1 for p in gen.progs if p.common)
    cov["batch"] += sum(1 for p in gen.progs if p.batch)
    cov["external_descriptions"] += sum(1 for p in gen.progs if p.ext is not None)
    cov["global_file"] += 1 if gen.use_file else 0
    cov["hiding"] += sum(1 for p in gen.progs if p.hides)
    cov["initial"] += sum(1 for p in gen.progs if p.initial)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=os.path.join(HERE, "out_nested"))
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(HERE)))
    ap.add_argument("--frontend", default=None, help="the front end directory (default: ROOT/tools/cobolfe)")
    ap.add_argument("--show", type=int, default=3)
    ap.add_argument("--run", nargs="+", metavar="PROG.cob", help="run hand-written cases instead")
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    os.makedirs(a.out, exist_ok=True)
    if a.run:
        st = [run_repro(p, a.out, root, a.frontend) for p in a.run]
        print(f"{len(st)} cases, {st.count('ok')} agree")
        return 0 if st.count("ok") == len(st) else 1
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, shown = {}, 0
    cov = {"programs": 0, "contained": 0, "common": 0, "batch": 0, "external_descriptions": 0,
           "global_file": 0, "hiding": 0, "calls": 0, "call_identifier": 0, "by_content": 0,
           "exception_phrases": 0, "cancels": 0, "duplicate_args": 0, "initial": 0}
    for i in range(a.n):
        name = f"N{a.seed % 1000:03d}{i:02d}"
        gen = Gen(random.Random(rng.random()), name)
        wd = os.path.join(a.out, name)
        os.makedirs(wd, exist_ok=True)
        src = gen.render()
        status, info, g = compare(os.path.join(wd, name), wd, root, src, a.frontend)
        tally[status] = tally.get(status, 0) + 1
        coverage(gen, cov)
        for k, v in gen.counts.items():
            cov[k] += v
        with open(os.path.join(a.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": i, "status": status, "info": info}) + "\n")
        if status != "ok" and shown < a.show:
            shown += 1
            print(f"--- {name} {status}")
            print(json.dumps(info)[:1500])
    print(json.dumps({"coverage": cov}))
    print(json.dumps({"tally": tally}))
    return 0 if tally.get("ok", 0) == a.n else 1


if __name__ == "__main__":
    sys.exit(main())

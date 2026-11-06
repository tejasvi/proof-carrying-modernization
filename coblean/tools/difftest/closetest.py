#!/usr/bin/env python3
"""Differential testing of the CLOSE phrases REEL / UNIT [FOR REMOVAL | WITH NO REWIND], WITH NO REWIND and
WITH LOCK, and of OPEN INPUT ... REVERSED.

IBM (Language Reference 6.4, CLOSE statement, Tables 34, 35, 36 and 38): a disk file is a non-reel/unit
file, so REEL / UNIT (also with NO REWIND or FOR REMOVAL) closes no volume: the file stays open,
nothing else changes, and the status is 07; WITH NO REWIND closes the file with 07; WITH LOCK closes a
sequential or indexed file (00) and locks it: every later OPEN of it gets 38. On a file that is not
open every phrase gives 42. The statement is an I/O statement, so a sequential REWRITE right after a
REEL / UNIT phrase gets 43. OPEN statement: REVERSED does not apply to a direct-access device and IBM
does not say where the READs then start, so the model runs OPEN INPUT ... REVERSED only when the OPEN
fails (41, 38) or the file has at most one record (an absent OPTIONAL file: 05), as OPEN INPUT.

Each random program declares 1-3 files: sequential ones, most with a FILE STATUS item, some OPTIONAL,
and in some programs an indexed file (ACCESS RANDOM, with FILE STATUS). A setup program (GnuCOBOL) first
creates the files present when the program starts, with 0-4 records (every non-OPTIONAL file and some
OPTIONAL ones); the others are absent. The program then runs 12-28 random statements: OPEN in every
mode (no EXTEND for the indexed file), OPEN INPUT ... REVERSED (sequential files of 0 or 1 records,
absent OPTIONAL files, open or locked files), CLOSE, CLOSE with a REEL / UNIT phrase (every spelling:
REEL, UNIT, FOR REMOVAL, REMOVAL, WITH NO REWIND, NO REWIND), CLOSE WITH NO REWIND / NO REWIND, CLOSE WITH
LOCK / LOCK, READ (keyed for the indexed file), WRITE and REWRITE; after a successful READ in I-O mode a
CLOSE ... REEL / UNIT and a REWRITE (43) are weighted up, and so are OPENs of a locked file (38). An
epilogue closes every open file and reads every file back (a locked one: OPEN INPUT, 38). Every
statement is followed by a DISPLAY of a trace number, every FILE STATUS item and every record area.

A file without FILE STATUS gets only statements that succeed (07 is a success status: no abend; after
its LOCK it gets none). The tester mirrors IBM's statuses (`Sim`): every status it predicts for a file
with FILE STATUS must be the one GnuCOBOL's trace shows (else `mirror-mismatch`), and the model's
DISPLAY lines must equal GnuCOBOL's (else `mismatch`). Left out of generation: a CLOSE of a file closed
WITH LOCK (G-lockclose: GnuCOBOL gives 00 and lifts the lock of a sequential file and crashes on an
indexed file, IBM 42: close_cases/g_lockclose_seq.cob, g_lockclose_idx.cob), a REWRITE after a failed
OPEN (41) that follows a READ (G-open41, filetest.py), and a CLOSE ... REEL / UNIT or NO REWIND of an
OPTIONAL file that is not present (IBM gives no status for a file on no medium; the model reports it as
unsupported, GnuCOBOL closes the file with 00: close_cases/u_closereel_absent.cob), and OPEN INPUT ...
REVERSED of a file of two or more records (the model reports it as unsupported, GnuCOBOL ignores
REVERSED: close_cases/u_openrev_many.cob).

GnuCOBOL (-std=ibm) runs the setup and the program in a fresh directory; the front end
(tools/cobolfe, --profile gnucobol) extracts the program and cobolrun runs it with the setup's records
as --inputs and the absent OPTIONAL files as --absent.

usage: closetest.py [--n N] [--seed S] [--out DIR] [--root TREE] [--show K]
       closetest.py --run PROG.cob... [--out DIR] [--root TREE]   (tools/difftest/close_cases)
  --root: the coblean tree whose front end and cobolrun are tested (default: this script's)
"""
import argparse
import json
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REEL_FORMS = [("REEL", "reel"), ("UNIT", "reel"), ("REEL FOR REMOVAL", "removal"), ("UNIT REMOVAL", "removal"),
              ("REEL WITH NO REWIND", "norewind"), ("UNIT NO REWIND", "norewind")]
KEYS = ["K%02d" % i for i in range(1, 8)]


def wrap(text):
    """Fixed-format lines within column 72, split at blanks outside literals."""
    words, cur, inq = [], "", False
    for ch in text:
        if ch == '"':
            inq = not inq
        if ch == " " and not inq:
            words.append(cur)
            cur = ""
        else:
            cur += ch
    words.append(cur)
    out, line = [], " " * 11
    for w in words:
        if not w:
            continue
        if len(line) + 1 + len(w) > 72:
            out.append(line)
            line = " " * 15 + w
        else:
            line = line + (" " if line.strip() else "") + w
    out.append(line)
    assert all(len(ln) <= 72 for ln in out), out
    return out


class F:
    """A file and IBM's state of it (the mirror): sequential, or indexed (ACCESS RANDOM)."""
    def __init__(self, i, optional, fs, indexed=False):
        self.i, self.optional, self.fs, self.indexed = i, optional, fs, indexed
        self.name = f"F{i}"
        self.present = True       # exists when the program starts
        self.exists = True        # exists now (False: an absent OPTIONAL file)
        self.mode = None          # open mode or None
        self.recs = []            # records now (indexed: in key order)
        self.init = []            # records when the program starts (setup / --inputs)
        self.pos = 0              # next record to read (sequential)
        self.eof = False          # a READ reached the end (sequential)
        self.cur = None           # the record of the last successful READ (sequential REWRITE)
        self.tainted = False      # an OPEN of the open file followed a READ (G-open41)
        self.locked = False       # closed WITH LOCK

    def unavailable(self):
        """Opened INPUT while absent: an OPTIONAL file on no medium."""
        return self.mode is not None and not self.exists

    def keys(self):
        return [r[:3] for r in self.recs]


class Gen:
    def __init__(self, rng, name):
        self.rng, self.name = rng, name
        nf = rng.choice([1, 2, 2, 3])
        self.files = [F(i, rng.random() < 0.4, rng.random() < 0.8) for i in range(1, nf + 1)]
        if rng.random() < 0.35:
            # an indexed file (ACCESS RANDOM, FILE STATUS, not OPTIONAL) in place of the last one
            self.files[-1] = F(nf, False, True, indexed=True)
        for f in self.files:
            f.present = not f.optional or rng.random() < 0.5
            f.exists = f.present
            if f.present:
                n = rng.randint(0, 4)
                if f.indexed:
                    f.init = [k + "INIT%d" % f.i for k in sorted(rng.sample(KEYS, n))]
                else:
                    f.init = ["I%dR%dXXXX" % (f.i, j) for j in range(n)]
                f.recs = list(f.init)
        self.lines = []
        self.ntrace = 0
        self.expect = []          # (trace number, file, predicted status, kind of statement)
        self.cov = {}

    def count(self, key):
        self.cov[key] = self.cov.get(key, 0) + 1

    # ------------------------------------------------------------------ helpers
    def trace(self):
        self.ntrace += 1
        parts = [f'"S{self.ntrace:03d}"']
        for f in self.files:
            parts += ['" "', f"ST{f.i}" if f.fs else '"--"', '" "', f"R{f.i}"]
        self.lines += wrap("DISPLAY " + " ".join(parts))

    def predict(self, f, status, kind):
        if f.fs:
            self.expect.append((self.ntrace + 1, f, status, kind))

    # ------------------------------------------------------------------ statements (IBM's statuses)
    def stmt(self):
        rng = self.rng
        f = rng.choice(self.files)
        if f.locked:
            # a locked file: OPEN (38) mostly; READ (47), WRITE (48); never a CLOSE (G-lockclose)
            if not f.fs or rng.random() < 0.5:
                return False
            return getattr(self, "op_" + rng.choice(["open", "open", "openrev", "read", "write"]))(f)
        ops = ["open"] * 4 + ["openrev"] * 3 + ["close", "reel", "norewind", "lock"] if f.mode is None else \
            ["open", "openrev", "close", "reel", "reel", "reel", "norewind", "norewind", "lock"]
        ops += ["read", "read", "read", "write", "write", "rewrite"]
        if f.mode == "I-O":
            ops += ["read", "read", "rewrite"]
        if f.indexed:
            ops = [o for o in ops if o not in ("openrev", "reel", "norewind", "rewrite")]
        return getattr(self, "op_" + rng.choice(ops))(f)

    def op_open(self, f):
        m = self.rng.choice(["INPUT", "INPUT", "OUTPUT", "I-O", "I-O", "I-O"] + ([] if f.indexed else ["EXTEND"]))
        if f.locked:
            self.lines.append(f"           OPEN {m} {f.name}")
            self.predict(f, "38", "open")
            self.count(f"OPEN {m} of a locked file 38")
            return True
        if f.mode is not None:
            if not f.fs:
                return False
            self.lines.append(f"           OPEN {m} {f.name}")
            self.predict(f, "41", "open")
            if f.cur is not None:
                f.tainted = True
            f.cur = None
            return True
        self.lines.append(f"           OPEN {m} {f.name}")
        if not f.exists:
            # an absent OPTIONAL file: 05 (OUTPUT 00); INPUT leaves it absent, the other modes create it
            self.predict(f, "00" if m == "OUTPUT" else "05", "open")
            f.exists = m != "INPUT"
            f.recs = []
        else:
            self.predict(f, "00", "open")
            if m == "OUTPUT":
                f.recs = []
        f.mode, f.pos, f.eof, f.cur, f.tainted = m, 0, False, None, False
        return True

    def op_openrev(self, f):
        """OPEN INPUT f REVERSED where every reading of IBM gives one result: the OPEN fails (41, 38), or
        the file has at most one record (absent OPTIONAL: 05). A file of two or more records is left out
        (the model stops with unsupported: close_cases/u_openrev_many.cob)."""
        n = len(f.recs) if f.exists else 0
        if f.indexed or (not f.fs and (f.locked or f.mode is not None)) or (f.mode is None and not f.locked and n > 1):
            return False
        self.lines.append(f"           OPEN INPUT {f.name} REVERSED")
        if f.locked:
            st = "38"
        elif f.mode is not None:
            st = "41"
            if f.cur is not None:
                f.tainted = True
            f.cur = None
        else:
            st = "05" if not f.exists else "00"
            f.mode, f.pos, f.eof, f.cur, f.tainted = "INPUT", 0, False, None, False
        self.predict(f, st, "openrev")
        self.count(f"OPEN INPUT REVERSED {st}" + (f" ({n} records)" if st in ("00", "05") else "") + ("" if f.fs else " nofs"))
        return True

    def op_close(self, f):
        if f.mode is None and not f.fs:
            return False
        self.lines.append(f"           CLOSE {f.name}")
        self.predict(f, "42" if f.mode is None else "00", "close")
        f.mode, f.cur = None, None
        return True

    def op_reel(self, f):
        if f.unavailable() or (f.mode is None and not f.fs):
            return False
        text, form = self.rng.choice(REEL_FORMS)
        self.lines.append(f"           CLOSE {f.name} {text}")
        st = "42" if f.mode is None else "07"
        self.predict(f, st, "reel")
        self.count(f"{form} {f.mode or 'closed'} {st}" + ("" if f.fs else " nofs"))
        f.cur = None
        return True

    def op_norewind(self, f):
        if f.unavailable() or (f.mode is None and not f.fs):
            return False
        text = self.rng.choice(["WITH NO REWIND", "NO REWIND"])
        self.lines.append(f"           CLOSE {f.name} {text}")
        st = "42" if f.mode is None else "07"
        self.predict(f, st, "norewind")
        self.count(f"NO REWIND {f.mode or 'closed'} {st}" + ("" if f.fs else " nofs"))
        f.mode, f.cur = None, None
        return True

    def op_lock(self, f):
        if f.mode is None and not f.fs:
            return False
        text = self.rng.choice(["WITH LOCK", "LOCK"])
        self.lines.append(f"           CLOSE {f.name} {text}")
        st = "42" if f.mode is None else "00"
        self.predict(f, st, "lock")
        self.count(f"LOCK {'indexed ' if f.indexed else ''}{f.mode or 'closed'} {st}" + ("" if f.fs else " nofs"))
        if f.mode is not None:
            f.locked = True
        f.mode, f.cur = None, None
        return True

    def op_read(self, f):
        if f.indexed:
            return self.op_keyread(f)
        readable = f.mode in ("INPUT", "I-O")
        more = readable and not f.eof and f.pos < len(f.recs)
        if not f.fs and not more:
            return False
        f.tainted = False
        atend = not f.fs or self.rng.random() < 0.4
        n = self.ntrace + 1
        self.lines += wrap(f"READ {f.name}" + (f' AT END DISPLAY "E{n:03d}" END-READ' if atend else ""))
        if not readable:
            self.predict(f, "47", "read")
            f.cur = None
        elif f.eof:
            self.predict(f, "46", "read")
            f.cur = None
        elif f.pos < len(f.recs):
            self.predict(f, "00", "read")
            f.cur, f.pos = f.pos, f.pos + 1
            if f.mode == "I-O" and f.fs and self.rng.random() < 0.6:
                # a CLOSE ... REEL / UNIT between the READ and a REWRITE: 43
                self.count("READ, CLOSE ... REEL / UNIT, REWRITE (43)")
                self.trace()
                self.op_reel(f)
                self.trace()
                self.op_rewrite(f)
        else:
            self.predict(f, "10", "read")
            f.eof, f.cur = True, None
        return True

    def op_keyread(self, f):
        k = self.rng.choice(f.keys() if f.keys() and self.rng.random() < 0.6 else KEYS)
        n = self.ntrace + 1
        self.lines.append(f'           MOVE "{k}" TO K{f.i}')
        self.lines += wrap(f'READ {f.name} INVALID KEY DISPLAY "E{n:03d}" END-READ')
        self.predict(f, ("00" if k in f.keys() else "23") if f.mode in ("INPUT", "I-O") else "47", "read")
        return True

    def op_write(self, f):
        if f.indexed:
            n = self.ntrace + 1
            k = self.rng.choice(KEYS)
            self.lines.append(f'           MOVE "{k}W{n:03d}F" TO R{f.i}')
            self.lines += wrap(f'WRITE R{f.i} INVALID KEY DISPLAY "E{n:03d}" END-WRITE')
            if f.mode in ("OUTPUT", "I-O"):
                if k in f.keys():
                    self.predict(f, "22", "write")
                else:
                    self.predict(f, "00", "write")
                    f.recs = sorted(f.recs + [f"{k}W{n:03d}F"])
            else:
                self.predict(f, "48", "write")
            return True
        if f.mode not in ("OUTPUT", "EXTEND") and not f.fs:
            return False
        n = self.ntrace + 1
        rec = f"W{n:03d}F{f.i}XX"
        self.lines.append(f'           MOVE "{rec}" TO R{f.i}')
        self.lines.append(f"           WRITE R{f.i}")
        if f.mode in ("OUTPUT", "EXTEND"):
            self.predict(f, "00", "write")
            f.recs.append(rec)
        else:
            self.predict(f, "48", "write")
        f.cur = None
        return True

    def op_rewrite(self, f):
        if f.tainted or (f.mode != "I-O" and self.rng.random() < 0.7):
            return False
        ok = f.mode == "I-O" and f.cur is not None
        if not f.fs and not ok:
            return False
        n = self.ntrace + 1
        rec = f"R{n:03d}F{f.i}YY"
        self.lines.append(f'           MOVE "{rec}" TO R{f.i}')
        self.lines.append(f"           REWRITE R{f.i}")
        st = "49" if f.mode != "I-O" else "43" if f.cur is None else "00"
        self.predict(f, st, "rewrite")
        self.count(f"REWRITE {st}")
        if st == "00":
            f.recs[f.cur] = rec
        f.cur = None
        return True

    # ------------------------------------------------------------------ programs
    def head(self, name, optional):
        out = ["       IDENTIFICATION DIVISION.", f"       PROGRAM-ID. {name}.",
               "       ENVIRONMENT DIVISION.", "       INPUT-OUTPUT SECTION.", "       FILE-CONTROL."]
        for f in self.files:
            if not optional and not f.present:
                continue
            opt = "OPTIONAL " if optional and f.optional else ""
            out.append(f'           SELECT {opt}{f.name} ASSIGN TO "{self.name}-{f.i}.dat"')
            if f.indexed:
                acc = "RANDOM" if optional else "SEQUENTIAL"
                out.append(f"               ORGANIZATION IS INDEXED ACCESS MODE IS {acc}")
                out.append(f"               RECORD KEY IS K{f.i}")
            else:
                out.append("               ORGANIZATION IS SEQUENTIAL" + ("" if f.fs or not optional else "."))
            if f.fs or not optional:
                out.append(f"               FILE STATUS IS ST{f.i}.")
        out += ["       DATA DIVISION.", "       FILE SECTION."]
        for f in self.files:
            if not optional and not f.present:
                continue
            out.append(f"       FD {f.name}.")
            if f.indexed:
                out += [f"       01 R{f.i}.", f"          05 K{f.i} PIC X(3).", f"          05 V{f.i} PIC X(5)."]
            else:
                out.append(f"       01 R{f.i} PIC X(8).")
        out.append("       WORKING-STORAGE SECTION.")
        for f in self.files:
            if f.fs or not optional:
                if optional or f.present:
                    out.append(f'       01 ST{f.i} PIC XX VALUE "..".')
        return out

    def render_setup(self):
        """The program that creates the files present at the start (None: there are none)."""
        if not any(f.present for f in self.files):
            return None
        out = self.head(self.name + "S", False) + ["       PROCEDURE DIVISION.", "       M0."]
        for f in self.files:
            if not f.present:
                continue
            out.append(f"           OPEN OUTPUT {f.name}")
            for r in f.init:
                out.append(f'           MOVE "{r}" TO R{f.i}')
                out.append(f"           WRITE R{f.i}")
            out.append(f'           IF ST{f.i} NOT = "00" DISPLAY "SETUP " ST{f.i} END-IF')
            out.append(f"           CLOSE {f.name}")
        out.append("           STOP RUN.")
        return "\n".join(out) + "\n"

    def render(self):
        rng = self.rng
        out = self.head(self.name, True) + ["       PROCEDURE DIVISION.", "       M0."]
        for f in self.files:
            out.append(f'           MOVE "........" TO R{f.i}')
        self.lines = []
        self.trace()
        target = rng.randint(12, 28)
        tries = 0
        while self.ntrace <= target and tries < 500:
            tries += 1
            if self.stmt():
                self.trace()
        # epilogue: close every open file, then read each back (a locked file: OPEN INPUT 38 only)
        for f in self.files:
            if f.mode is not None:
                self.lines.append(f"           CLOSE {f.name}")
                self.predict(f, "00", "close")
                f.mode, f.cur = None, None
                self.trace()
        for f in self.files:
            if f.locked:
                if f.fs:
                    self.lines.append(f"           OPEN INPUT {f.name}")
                    self.predict(f, "38", "open")
                    self.trace()
                continue
            self.lines.append(f"           OPEN INPUT {f.name}")
            self.predict(f, "00" if f.exists else "05", "open")
            self.trace()
            f.mode, f.pos, f.eof = "INPUT", 0, False
            if f.indexed:
                for k in KEYS:
                    self.lines.append(f'           MOVE "{k}" TO K{f.i}')
                    self.lines.append(f"           READ {f.name}")
                    self.predict(f, "00" if k in f.keys() else "23", "read")
                    self.trace()
            else:
                for _ in range(len(f.recs) + (1 if f.fs else 0)):
                    self.op_read(f)
                    self.trace()
            self.lines.append(f"           CLOSE {f.name}")
            self.predict(f, "00", "close")
            f.mode = None
            self.trace()
        out += self.lines
        out.append("           STOP RUN.")
        return "\n".join(out) + "\n"

    def inputs(self):
        return [[f.i, [list(r.encode("ascii")) for r in f.init]] for f in self.files if f.present and f.init]

    def absent(self):
        return [f.i for f in self.files if not f.present]


def run(cmd, timeout, **kw):
    try:
        return subprocess.run(cmd, capture_output=True, timeout=timeout, **kw)
    except subprocess.TimeoutExpired:
        return None


def compare(base, wd, root, src, setup, inputs, absent):
    """Status, details, GnuCOBOL's lines and the model's lines (None without a cobolrun result) of
    program `src` (written to base.cob): GnuCOBOL in the fresh directory wd after the setup program
    (if any) vs front end + cobolrun with the records `inputs` and the absent files `absent`."""
    cobc = os.path.join(root, "scripts", "cobc.sh")
    cobolfe = os.path.join(root, "tools", "cobolfe", "cobolfe.py")
    cobolrun = os.path.join(root, ".lake", "build", "bin", "cobolrun")
    env = dict(os.environ, LD_LIBRARY_PATH=os.path.join(root, "third_party", "gnucobol", "usr", "lib",
                                                        "x86_64-linux-gnu"))
    with open(base + ".cob", "w") as fh:
        fh.write(src)
    if setup is not None:
        with open(base + "S.cob", "w") as fh:
            fh.write(setup)
        c = run([cobc, "-x", "-std=ibm", "-o", base + "S", base + "S.cob"], 120, text=True)
        if c is None or c.returncode != 0:
            return "cobc-error", "setup: " + (c.stderr[-800:] if c else "timeout"), None, None
        r = run([base + "S"], 20, env=env, cwd=wd)
        if r is None or r.returncode != 0 or r.stdout:
            return "setup-error", (r.stdout.decode("latin-1")[-300:] if r else "timeout"), None, None
    c = run([cobc, "-x", "-std=ibm", "-o", base, base + ".cob"], 120, text=True)
    if c is None or c.returncode != 0:
        return "cobc-error", (c.stderr[-800:] if c else "timeout"), None, None
    r = run([base], 20, env=env, cwd=wd)
    if r is None:
        return "gnucobol-timeout", None, None, None
    g = r.stdout.decode("latin-1").splitlines()
    if r.returncode != 0:
        return "gnucobol-abend", {"rc": r.returncode, "stderr": r.stderr.decode("latin-1")[-300:]}, g, None
    fe = run([sys.executable, "-I", "-B", cobolfe, base + ".cob", "--profile", "gnucobol", "--main",
              "-o", base + ".fe.json"], 120, text=True)
    if fe is None or fe.returncode != 0:
        return "frontend-error", (fe.stderr[-800:] if fe else "timeout"), g, None
    if "unsupported" in fe.stderr:
        return "frontend-unsupported", fe.stderr[-800:], g, None
    with open(base + ".inputs.json", "w") as fh:
        json.dump(inputs, fh)
    cmd = [cobolrun, base + ".fe.json", "--inputs", base + ".inputs.json"]
    if absent:
        cmd += ["--absent", ",".join(map(str, absent))]
    with open(base + ".cmd.json", "w") as fh:
        json.dump(cmd, fh)
    lr = run(cmd, 60, text=True)
    if lr is None:
        return "lean-timeout", None, g, None
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-800:], g, None
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop:"):
        return "lean-signal", {"signal": res["signal"], "lines": len(m), "gnucobol_lines": len(g)}, g, m
    if g != m:
        k = next((i for i, (a, b) in enumerate(zip(g, m)) if a != b), min(len(g), len(m)))
        return "mismatch", {"line": k, "gnucobol": g[k:k + 3], "lean": m[k:k + 3]}, g, m
    return "ok", None, g, m


def mirror(gen, g):
    """The predicted statuses against GnuCOBOL's trace lines: (checked, first disagreement or None)."""
    by_trace = {}
    for ln in g or []:
        w = ln.split()
        if w and len(w[0]) == 4 and w[0][0] == "S" and w[0][1:].isdigit():
            by_trace.setdefault(int(w[0][1:]), w)
    n = 0
    for t, f, st, kind in gen.expect:
        w = by_trace.get(t)
        got = w[2 * gen.files.index(f) + 1] if w is not None and len(w) > 2 * gen.files.index(f) + 1 else None
        n += 1
        if got != st:
            return n, {"trace": t, "file": f.name, "kind": kind, "predicted": st, "gnucobol": got}
    return n, None


def run_case(gen, wd, root):
    """One generated program."""
    os.makedirs(wd, exist_ok=True)
    src = gen.render()
    status, info, g, _ = compare(os.path.join(wd, gen.name), wd, root, src, gen.render_setup(), gen.inputs(),
                                 gen.absent())
    checked, bad = mirror(gen, g)
    if status == "ok" and bad is not None:
        status, info = "mirror-mismatch", bad
    return status, info, checked


def run_repro(path, out, root):
    """A hand case (no setup; its absent files on a line `      * ABSENT: 1,2`): prints `== PATH: status`
    and the two sides' DISPLAY lines side by side (`!! ` where they differ), as classtest.py --run does;
    for other statuses the details."""
    name = os.path.splitext(os.path.basename(path))[0]
    wd = os.path.join(out, name)
    os.makedirs(wd)
    with open(path) as fh:
        src = fh.read()
    absent = []
    for ln in src.splitlines():
        if ln.startswith("      * ABSENT:"):
            absent = [int(x) for x in ln.split(":", 1)[1].split(",") if x.strip()]
    status, info, g, m = compare(os.path.join(wd, name), wd, root, src, None, [], absent)
    print(f"== {path}: {status}")
    if status in ("ok", "mismatch"):
        for i in range(max(len(g), len(m))):
            a, b = (g[i] if i < len(g) else "<none>"), (m[i] if i < len(m) else "<none>")
            print(("   " if a == b else "!! ") + f"{a:<34} | {b}")
    else:
        print("  " + json.dumps(info)[:1500])
    return status


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=os.path.join(HERE, "out_close"))
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(HERE)))
    ap.add_argument("--show", type=int, default=3)
    ap.add_argument("--run", nargs="+", metavar="PROG.cob", help="run hand cases instead")
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    os.makedirs(a.out, exist_ok=True)
    if a.run:
        st = [run_repro(p, a.out, root) for p in a.run]
        print(f"{len(st)} cases, {st.count('ok')} agree")
        return 0
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, shown = {}, 0
    cov, checked = {}, 0
    for i in range(a.n):
        name = f"CT{a.seed:02d}{i:03d}"
        gen = Gen(random.Random(rng.random()), name)
        status, info, nchk = run_case(gen, os.path.join(a.out, name), root)
        tally[status] = tally.get(status, 0) + 1
        checked += nchk
        for k, v in gen.cov.items():
            cov[k] = cov.get(k, 0) + v
        with open(os.path.join(a.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": i, "status": status}) + "\n")
        if status != "ok" and shown < a.show:
            shown += 1
            print(f"--- {name} {status}")
            print(json.dumps(info)[:1500])
    with open(os.path.join(a.out, "coverage.json"), "w") as fh:
        json.dump({"counts": dict(sorted(cov.items())), "statuses_checked": checked}, fh, indent=1)
    print(json.dumps({"coverage": {"counts": dict(sorted(cov.items())), "statuses_checked": checked}}))
    print(json.dumps({"tally": tally}))
    return 0 if tally.get("ok", 0) == a.n else 1


if __name__ == "__main__":
    sys.exit(main())

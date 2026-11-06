#!/usr/bin/env python3
"""Differential testing of DECLARATIVES (USE AFTER STANDARD EXCEPTION/ERROR PROCEDURE).

Each random program declares 1-3 files (sequential, or indexed with RANDOM or DYNAMIC access,
some without FILE STATUS), 1-3 USE declaratives (on file names or on an open mode), creates the
files in a prologue, then runs 10-24 random I/O statements (OPEN, CLOSE, READ, READ NEXT, keyed
READ, WRITE, REWRITE, DELETE, START), some with AT END / INVALID KEY phrases. Many end with an
error or exception status (10, 22, 23, 41-49) on purpose. Every statement is followed by a
DISPLAY of a trace number, the FILE STATUS items and the count of USE procedures run; each USE
procedure displays its number and the same items. GnuCOBOL (-std=ibm) and the front end +
cobolrun must agree exactly: the DISPLAY lines (bytes, count), and how the run ends (normal end;
or an abend on an unhandled I/O error, with the same status).

Generation avoids the documented GnuCOBOL 3.2 file-status deviations of filetest.py (no ACCESS
SEQUENTIAL indexed files, no alternate keys, no REWRITE of a missing key, no REWRITE / DELETE
after a failed OPEN that follows a READ, no OPEN EXTEND of an indexed file). Named difference
classes found here, left out of generation:
  G-closedmode: an error on a file that is not open (status 42, 47, 48, 49) with only an
    open-mode USE: IBM applies a mode declarative to files open in that mode (none applies
    here); GnuCOBOL runs the declarative of the mode the file was last opened in.
  G-readfail (dyntest.py): a READ NEXT of an ACCESS DYNAMIC file after a keyed READ that found no
    record, before a START, a successful keyed READ or an OPEN: GnuCOBOL continues from where it
    was (or gives 10 or 46); IBM and the model: 46.

usage: decltest.py [--n N] [--seed S] [--out DIR] [--show K] [--keep] [--unsafe]
"""
import argparse
import json
import os
import random
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import difftest as D  # noqa: E402

KEYS = ["K%02d" % i for i in range(1, 10)]
MODES = ["INPUT", "OUTPUT", "I-O", "EXTEND"]


class F:
    def __init__(self, i, org, access, status):
        self.i, self.org, self.access, self.status = i, org, access, status
        self.name = f"F{i}"
        self.mode = None          # open mode or None
        self.keys = set()         # record keys present (indexed)
        self.nrec = 0             # records (sequential)
        self.read_ok = False      # last I/O on the file was a successful READ (sequential REWRITE)
        self.tainted = False      # a failed OPEN followed a READ (avoid REWRITE/DELETE: G-open41)
        self.ever_opened = None   # mode of the last OPEN (G-closedmode)
        self.eof = False
        self.readfail = False     # ACCESS DYNAMIC: a keyed READ found no record since the last
        #                           START / OPEN / successful keyed READ (G-readfail)


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


class Gen:
    def __init__(self, rng, name, unsafe):
        self.rng, self.name, self.unsafe = rng, name, unsafe
        nf = rng.choice([1, 2, 2, 3])
        self.files = []
        for i in range(1, nf + 1):
            org = "indexed" if rng.random() < 0.5 else "sequential"
            access = rng.choice(["random", "dynamic"]) if org == "indexed" else "sequential"
            self.files.append(F(i, org, access, rng.random() < 0.8))
        # USE declaratives: disjoint file lists or distinct modes
        self.uses = []
        names = [f.name for f in self.files]
        rng.shuffle(names)
        modes = MODES[:]
        rng.shuffle(modes)
        for _ in range(rng.choice([1, 1, 2, 3])):
            if names and (rng.random() < 0.6 or not modes):
                k = rng.choice([1, 1, 2])
                take, names = names[:k], names[k:]
                self.uses.append(("files", take))
            elif modes:
                self.uses.append(("mode", modes.pop()))
        self.lines = []
        self.ntrace = 0

    # ------------------------------------------------------------------ helpers
    def statuses(self):
        return " ".join(f'"{f.i}=" ST{f.i}' for f in self.files if f.status)

    def trace(self):
        self.ntrace += 1
        st = self.statuses()
        self.lines += wrap(f'DISPLAY "S{self.ntrace:02d} " UCNT{(" " + st) if st else ""}')

    def covered_mode_only(self, f):
        """f is covered by no USE naming it, only possibly by mode USEs."""
        return not any(kind == "files" and f.name in v for kind, v in self.uses)

    def has_mode_use(self):
        return any(kind == "mode" for kind, _ in self.uses)

    def would_hit_closedmode(self, f):
        # an error on a closed file covered only by an open-mode USE (G-closedmode)
        return (not self.unsafe and f.mode is None and self.covered_mode_only(f)
                and self.has_mode_use())

    def abend_risk(self, f):
        """An unhandled error on f would abend: no FILE STATUS and no applicable USE."""
        if f.status:
            return False
        if not self.covered_mode_only(f):
            return False
        return not any(kind == "mode" and v == (f.mode or "") for kind, v in self.uses)

    # ------------------------------------------------------------------ statements
    def stmt(self):
        rng = self.rng
        f = rng.choice(self.files)
        # reads and keyed operations weighted up, so that AT END (10), 46 and the invalid-key
        # statuses (22, 23) occur often, with and without their phrases
        if f.org == "indexed":
            ops = ["open", "close", "keyread", "keyread", "write", "write", "rewrite", "delete", "delete"]
            if f.access == "dynamic":
                ops += ["start", "readnext", "readnext", "readnext"]
        else:
            ops = ["open", "close", "read", "read", "read", "write", "rewrite"]
        op = rng.choice(ops)
        return getattr(self, "op_" + op)(f)

    def op_open(self, f):
        rng = self.rng
        modes = ["INPUT", "OUTPUT", "I-O"] + (["EXTEND"] if f.org == "sequential" else [])
        m = rng.choice(modes)
        if f.mode is not None:
            # 41: OPEN of an open file
            if f.read_ok:
                f.tainted = True
            if self.abend_risk(f) and rng.random() < 0.8:
                return False
            self.lines.append(f"           OPEN {m} {f.name}")
            return True
        self.lines.append(f"           OPEN {m} {f.name}")
        f.mode, f.ever_opened, f.read_ok = m, m, False
        if m == "OUTPUT":
            f.keys, f.nrec = set(), 0
        f.tainted = False
        f.eof = False
        f.readfail = False
        return True

    def op_close(self, f):
        if f.mode is None and (self.would_hit_closedmode(f) or (self.abend_risk(f) and self.rng.random() < 0.8)):
            return False
        self.lines.append(f"           CLOSE {f.name}")
        f.mode, f.read_ok = None, False
        return True

    def phrase(self, cond):
        """Optionally an AT END / INVALID KEY phrase and its NOT form (trace markers)."""
        rng = self.rng
        p = []
        if rng.random() < 0.35:
            p.append(f'{cond} DISPLAY "C{self.ntrace + 1:02d}"')
        if rng.random() < 0.25:
            p.append(f'NOT {cond} DISPLAY "N{self.ntrace + 1:02d}"')
        return p

    def op_read(self, f):
        if f.org == "indexed" and f.access == "random":
            return self.op_keyread(f)
        if f.access == "dynamic":
            return self.op_readnext(f)
        if f.mode not in ("INPUT", "I-O") and (self.would_hit_closedmode(f) or self.abend_risk(f)):
            return False
        ph = self.phrase("AT END")
        txt = f"READ {f.name}" + ((" " + " ".join(ph)) if ph else "") + (" END-READ" if ph else "")
        self.lines += wrap(txt)
        f.read_ok = f.mode in ("INPUT", "I-O")
        f.tainted = False
        return True

    def op_readnext(self, f):
        if f.mode not in ("INPUT", "I-O") and (self.would_hit_closedmode(f) or self.abend_risk(f)):
            return False
        if f.readfail and not self.unsafe:
            return False
        ph = self.phrase("AT END")
        txt = f"READ {f.name} NEXT" + ((" " + " ".join(ph)) if ph else "") + (" END-READ" if ph else "")
        self.lines += wrap(txt)
        f.tainted = False
        return True

    def op_keyread(self, f):
        if f.mode not in ("INPUT", "I-O") and (self.would_hit_closedmode(f) or self.abend_risk(f)):
            return False
        k = self.rng.choice(sorted(f.keys) if f.keys and self.rng.random() < 0.5 else KEYS)
        self.lines.append(f'           MOVE "{k}" TO K{f.i}')
        ph = self.phrase("INVALID KEY")
        txt = f"READ {f.name}" + ((" " + " ".join(ph)) if ph else "") + (" END-READ" if ph else "")
        self.lines += wrap(txt)
        f.tainted = False
        f.readfail = f.access == "dynamic" and k not in f.keys
        return True

    def op_write(self, f):
        rng = self.rng
        okmode = ("OUTPUT", "EXTEND") if f.org == "sequential" else ("OUTPUT", "I-O")
        if f.mode not in okmode and (self.would_hit_closedmode(f) or self.abend_risk(f)):
            return False
        if f.org == "indexed":
            k = rng.choice(KEYS)
            if f.mode == "OUTPUT" and f.access != "random" and False:
                pass
            self.lines.append(f'           MOVE "{k}" TO K{f.i}')
            self.lines.append(f'           MOVE "W{self.ntrace + 1:02d}XX" TO V{f.i}')
            ph = self.phrase("INVALID KEY")
            txt = f"WRITE R{f.i}" + ((" " + " ".join(ph)) if ph else "") + (" END-WRITE" if ph else "")
            self.lines += wrap(txt)
            if f.mode in okmode:
                f.keys.add(k)
        else:
            self.lines.append(f'           MOVE "W{self.ntrace + 1:02d}XXXXX" TO R{f.i}')
            self.lines.append(f"           WRITE R{f.i}")
        f.read_ok = False
        return True

    def op_rewrite(self, f):
        rng = self.rng
        if f.tainted:
            return False
        if f.mode != "I-O" and (self.would_hit_closedmode(f) or self.abend_risk(f)):
            return False
        if f.org == "indexed":
            if f.mode == "I-O":
                if not f.keys:
                    return False
                k = rng.choice(sorted(f.keys))     # never a missing key (G-rw21)
            else:
                k = rng.choice(KEYS)
            self.lines.append(f'           MOVE "{k}" TO K{f.i}')
            self.lines.append(f'           MOVE "R{self.ntrace + 1:02d}YY" TO V{f.i}')
            ph = self.phrase("INVALID KEY")
            txt = f"REWRITE R{f.i}" + ((" " + " ".join(ph)) if ph else "") + (" END-REWRITE" if ph else "")
            self.lines += wrap(txt)
        else:
            self.lines.append(f'           MOVE "R{self.ntrace + 1:02d}YYYYY" TO R{f.i}')
            self.lines.append(f"           REWRITE R{f.i}")
        f.read_ok = False
        return True

    def op_delete(self, f):
        rng = self.rng
        if f.tainted:
            return False
        if f.mode != "I-O" and (self.would_hit_closedmode(f) or self.abend_risk(f)):
            return False
        k = rng.choice(sorted(f.keys) if f.keys and rng.random() < 0.6 else KEYS)
        self.lines.append(f'           MOVE "{k}" TO K{f.i}')
        ph = self.phrase("INVALID KEY")
        txt = f"DELETE {f.name}" + ((" " + " ".join(ph)) if ph else "") + (" END-DELETE" if ph else "")
        self.lines += wrap(txt)
        if f.mode == "I-O":
            f.keys.discard(k)
        return True

    def op_start(self, f):
        rng = self.rng
        if f.mode not in ("INPUT", "I-O") and (self.would_hit_closedmode(f) or self.abend_risk(f)):
            return False
        k = rng.choice(KEYS)
        op = rng.choice(["=", ">", "NOT <"])
        self.lines.append(f'           MOVE "{k}" TO K{f.i}')
        ph = self.phrase("INVALID KEY")
        txt = f"START {f.name} KEY {op} K{f.i}" + ((" " + " ".join(ph)) if ph else "") + (" END-START" if ph else "")
        self.lines += wrap(txt)
        f.readfail = False
        return True

    # ------------------------------------------------------------------ program
    def render(self):
        rng = self.rng
        out = ["       IDENTIFICATION DIVISION.", f"       PROGRAM-ID. {self.name}.",
               "       ENVIRONMENT DIVISION.", "       INPUT-OUTPUT SECTION.", "       FILE-CONTROL."]
        for f in self.files:
            out.append(f'           SELECT {f.name} ASSIGN TO "{self.name}-{f.i}.dat"')
            if f.org == "indexed":
                out.append(f"               ORGANIZATION IS INDEXED ACCESS MODE IS {f.access.upper()}")
                out.append(f"               RECORD KEY IS K{f.i}")
            else:
                out.append("               ORGANIZATION IS SEQUENTIAL")
            if f.status:
                out.append(f"               FILE STATUS IS ST{f.i}")
            out[-1] += "."
        out += ["       DATA DIVISION.", "       FILE SECTION."]
        for f in self.files:
            out.append(f"       FD {f.name}.")
            if f.org == "indexed":
                out += [f"       01 R{f.i}.", f"          05 K{f.i} PIC X(3).", f"          05 V{f.i} PIC X(5)."]
            else:
                out.append(f"       01 R{f.i} PIC X(8).")
        out.append("       WORKING-STORAGE SECTION.")
        for f in self.files:
            if f.status:
                out.append(f'       01 ST{f.i} PIC XX VALUE "00".')
        out.append("       01 UCNT PIC 9(3) VALUE 0.")
        out += ["       PROCEDURE DIVISION.", "       DECLARATIVES."]
        for u, (kind, v) in enumerate(self.uses, 1):
            out.append(f"       U{u} SECTION.")
            target = " ".join(v) if kind == "files" else v
            word = rng.choice(["ERROR", "EXCEPTION"])
            out += wrap(f"USE AFTER STANDARD {word} PROCEDURE ON {target}.")
            out.append(f"       U{u}-P.")
            out.append("           ADD 1 TO UCNT.")
            st = self.statuses()
            out += wrap(f'DISPLAY "U{u} " UCNT{(" " + st) if st else ""}.')
        out += ["       END DECLARATIVES.", "       MAIN-CODE SECTION.", "       M0."]
        # prologue: create every file with a few records
        for f in self.files:
            out.append(f"           OPEN OUTPUT {f.name}")
            n = rng.randint(0, 4)
            if f.org == "indexed":
                ks = sorted(rng.sample(KEYS, n))
                for k in ks:
                    out.append(f'           MOVE "{k}" TO K{f.i}')
                    out.append(f'           MOVE "INIT0" TO V{f.i}')
                    out.append(f"           WRITE R{f.i}")
                f.keys = set(ks)
            else:
                for j in range(n):
                    out.append(f'           MOVE "INIT{j}XXX" TO R{f.i}')
                    out.append(f"           WRITE R{f.i}")
                f.nrec = n
            out.append(f"           CLOSE {f.name}")
        st = self.statuses()
        out += wrap(f'DISPLAY "P " UCNT{(" " + st) if st else ""}')
        self.lines = []
        target = rng.randint(10, 24)
        tries = 0
        while self.ntrace < target and tries < 400:
            tries += 1
            if self.stmt():
                self.trace()
        out += self.lines
        out.append("           STOP RUN.")
        return "\n".join(out) + "\n"


ABEND_RE = re.compile(r"status = (\d\d)")


def run_case(src, wd, name):
    os.makedirs(wd, exist_ok=True)
    base = os.path.join(wd, name)
    with open(base + ".cob", "w") as fh:
        fh.write(src)
    c = subprocess.run([D.COBC, "-x", "-std=ibm", "-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return "cobc-error", c.stderr[-800:]
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    try:
        r = subprocess.run([base], capture_output=True, env=env, timeout=20, cwd=wd)
    except subprocess.TimeoutExpired:
        return "gnucobol-timeout", None
    g = r.stdout.decode("latin-1").splitlines()
    gerr = r.stderr.decode("latin-1")
    fe = subprocess.run([sys.executable, "-I", D.COBOLFE, base + ".cob", "--profile", "gnucobol",
                         "--main", "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0:
        return "frontend-error", fe.stderr[-800:]
    if "unsupported" in fe.stderr:
        return "frontend-unsupported", fe.stderr[-800:]
    try:
        lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True, timeout=60)
    except subprocess.TimeoutExpired:
        return "lean-timeout", None
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-800:]
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    sig = res["signal"]
    gab = r.returncode != 0
    mab = sig.startswith("fault:Cobol.Fault.io")
    if not gab and not sig.startswith("stop:"):
        return "lean-signal", sig
    if g != m:
        k = next((i for i, (a, b) in enumerate(zip(g, m)) if a != b), min(len(g), len(m)))
        return "mismatch", {"line": k, "gnucobol": g[k:k + 3], "lean": m[k:k + 3], "signal": sig,
                            "gnucobol_rc": r.returncode}
    if gab != mab:
        return "end-mismatch", {"gnucobol_rc": r.returncode, "gnucobol_err": gerr[-300:], "signal": sig}
    if gab:
        gm = ABEND_RE.search(gerr)
        mm = re.search(r"io (\d+)", sig)
        if gm and mm and int(gm.group(1)) != int(mm.group(1)):
            return "abend-status-mismatch", {"gnucobol": gm.group(0), "signal": sig}
        return "ok-abend", None
    return "ok", None


def bump(tally, out, case, status):
    tally[status] = tally.get(status, 0) + 1
    with open(os.path.join(out, "results.jsonl"), "a") as fh:
        fh.write(json.dumps({"case": case, "status": status}) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "out_decl"))
    ap.add_argument("--show", type=int, default=3)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--unsafe", action="store_true", help="also generate the G-closedmode and G-readfail forms")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, shown = {}, 0
    for i in range(a.n):
        name = f"DT{a.seed:02d}{i:03d}"
        gen = Gen(random.Random(rng.random()), name, a.unsafe)
        src = gen.render()
        wd = os.path.join(a.out, name)
        status, info = run_case(src, wd, name)
        bump(tally, a.out, i, status)
        if status not in ("ok", "ok-abend") and shown < a.show:
            shown += 1
            print(f"--- {name} {status}")
            print(json.dumps(info)[:1500])
    print(json.dumps({"tally": tally}))
    bad = sum(v for k, v in tally.items() if k not in ("ok", "ok-abend"))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

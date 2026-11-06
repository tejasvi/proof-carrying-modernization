#!/usr/bin/env python3
"""Differential testing of SELECT OPTIONAL files: OPEN of an absent OPTIONAL file (status 05).

Each random program declares 1-3 files (sequential, or indexed with ACCESS RANDOM, DYNAMIC or
SEQUENTIAL), each with a FILE STATUS item; at least one is OPTIONAL. A setup program (GnuCOBOL)
first creates the files that are present when the program starts, with 0-4 records: every
non-OPTIONAL file and some OPTIONAL ones. The other OPTIONAL files (at least one) are absent.
The program then runs 10-24 random I/O statements: OPEN in each mode (EXTEND only for sequential
files and ACCESS SEQUENTIAL indexed files), CLOSE, READ, READ NEXT, keyed READ, START, WRITE,
REWRITE and DELETE, some with AT END / INVALID KEY phrases. OPENs of closed files are weighted
up, so that absent files are opened in each mode and files are opened again after a CLOSE. An
epilogue closes every file and reads it back: OPEN INPUT (00 if the file exists, 05 if it is
still absent), every record (sequentially, or by every key for ACCESS RANDOM), CLOSE. Every
statement is followed by a DISPLAY of a trace number, every FILE STATUS item and every record
area.

GnuCOBOL (-std=ibm) runs the setup and the program in a fresh directory; the front end
(tools/cobolfe, --profile gnucobol) extracts the program and cobolrun runs it with the setup's
records as --inputs and the absent OPTIONAL files as --absent. Both must agree exactly on the
DISPLAY lines and end normally.

Generation avoids the GnuCOBOL 3.2 file-status deviations of filetest.py: ACCESS SEQUENTIAL
WRITEs only in OUTPUT / EXTEND mode, with keys above every key in the file and every key written
since the OPEN (G-dup21, G-extend, G-lastkey); ACCESS SEQUENTIAL REWRITE keeps the key (G-rwkey);
no alternate keys (G-rwalt); random REWRITE only of keys in the file (G-rw21); no REWRITE /
DELETE after an OPEN of an open file that follows a READ (G-open41). The deviation classes found
here are left out of generation too (--unsafe generates them):
  G-optkey: the first READ of an absent OPTIONAL file opened INPUT is a keyed READ (ACCESS
    RANDOM, or DYNAMIC without NEXT). GnuCOBOL gives 10 and skips the INVALID KEY phrase, and
    a READ NEXT after it gives 46. IBM (file status 23: "a START or random READ statement was
    attempted on an optional input file that was unavailable"): 23 with INVALID KEY, then 46
    (G-readfail). Reproducer: tools/difftest/opt_cases/g_optkey.cob (--run).
  G-readfail (dyntest.py): a READ NEXT of an ACCESS DYNAMIC file after a keyed READ that found no
    record, before a START, a successful keyed READ or an OPEN. GnuCOBOL continues from where it
    was (or gives 10 or 46); IBM and the model: 46 (the file position indicator is undefined
    after an unsuccessful READ). In opt_cases/v_optional2.cob (--run), line D3 is such a READ
    NEXT (GnuCOBOL 10, the model 46); its other lines agree.

The summary also counts the OPENs of absent OPTIONAL files per file kind and open mode, as the
generator predicts them, and how many of the predicted 05s GnuCOBOL's trace shows.

usage: opttest.py [--n N] [--seed S] [--out DIR] [--root TREE] [--show K] [--unsafe]
       opttest.py --run PROG.cob... [--out DIR] [--root TREE]   (tools/difftest/opt_cases)
  --root: the coblean tree whose front end and cobolrun are tested (default: this script's)
"""
import argparse
import json
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
KEYS = ["K%02d" % i for i in range(1, 10)]


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
    def __init__(self, i, org, access, optional):
        self.i, self.org, self.access, self.optional = i, org, access, optional
        self.name = f"F{i}"
        self.present = True       # exists when the program starts
        self.exists = True        # exists now (False: an absent OPTIONAL file)
        self.mode = None          # open mode or None
        self.keys = set()         # record keys in the file (indexed)
        self.init = []            # records when the program starts (setup / --inputs)
        self.read_ok = False      # the last I/O on the file was a READ
        self.tainted = False      # an OPEN of the open file followed a READ (G-open41)
        self.last = None          # ACCESS SEQUENTIAL: the last key written since the OPEN
        self.seqread = False      # a sequential READ (or READ NEXT) since the OPEN (G-optkey)
        self.readfail = False     # ACCESS DYNAMIC: a keyed READ found no record since the last
        #                           START / OPEN / successful keyed READ (G-readfail)

    @property
    def kind(self):
        return "seq" if self.org == "sequential" else "idx-" + self.access

    def fill(self, rng, n):
        if self.org == "indexed":
            ks = sorted(rng.sample(KEYS, n))
            self.init = [k + "INIT0" for k in ks]
            self.keys = set(ks)
        else:
            self.init = ["INIT%dXXX" % j for j in range(n)]


class Gen:
    def __init__(self, rng, name, unsafe=False):
        self.rng, self.name, self.unsafe = rng, name, unsafe
        nf = rng.choice([1, 2, 2, 3])
        self.files = []
        for i in range(1, nf + 1):
            org = "indexed" if rng.random() < 0.5 else "sequential"
            access = rng.choice(["random", "dynamic", "sequential"]) if org == "indexed" else "sequential"
            self.files.append(F(i, org, access, rng.random() < 0.75))
        if not any(f.optional for f in self.files):
            rng.choice(self.files).optional = True
        for f in self.files:
            f.present = not f.optional or rng.random() < 0.35
        if all(f.present for f in self.files):
            rng.choice([f for f in self.files if f.optional]).present = False
        for f in self.files:
            f.exists = f.present
            if f.present:
                f.fill(rng, rng.randint(0, 4))
        self.lines = []
        self.ntrace = 0
        self.opens = []           # (trace number, file, mode, absent before the OPEN)

    # ------------------------------------------------------------------ helpers
    def trace(self):
        self.ntrace += 1
        parts = [f'"S{self.ntrace:03d}"']
        for f in self.files:
            parts += ['" "', f"ST{f.i}", '" "', f"R{f.i}"]
        self.lines += wrap("DISPLAY " + " ".join(parts))

    def phrase(self, cond):
        """Optionally an AT END / INVALID KEY phrase and its NOT form (trace markers)."""
        rng = self.rng
        p = []
        if rng.random() < 0.35:
            p.append(f'{cond} DISPLAY "C{self.ntrace + 1:03d}"')
        if rng.random() < 0.25:
            p.append(f'NOT {cond} DISPLAY "N{self.ntrace + 1:03d}"')
        return p

    def io(self, verb, cond, end):
        ph = self.phrase(cond) if cond else []
        self.lines += wrap(verb + ((" " + " ".join(ph) + " " + end) if ph else ""))

    # ------------------------------------------------------------------ statements
    def stmt(self):
        rng = self.rng
        f = rng.choice(self.files)
        # a closed file is mostly opened; an open one is used for about five statements, then
        # closed (and opened again later)
        ops = ["open"] * 4 + ["close"] if f.mode is None else ["open", "close", "close"]
        if f.org == "sequential":
            ops += ["read", "read", "read", "write", "write", "rewrite"]
        elif f.access == "random":
            ops += ["keyread", "keyread", "write", "write", "rewrite", "delete"]
        elif f.access == "dynamic":
            ops += ["keyread", "write", "write", "rewrite", "delete", "start", "readnext", "readnext"]
        else:
            ops += ["read", "read", "read", "write", "write", "rewrite", "delete"]
        return getattr(self, "op_" + rng.choice(ops))(f)

    def op_open(self, f):
        modes = ["INPUT", "OUTPUT", "I-O"]
        if f.org == "sequential" or f.access == "sequential":
            modes.append("EXTEND")
        m = self.rng.choice(modes)
        self.lines.append(f"           OPEN {m} {f.name}")
        if f.mode is not None:
            # 41: OPEN of an open file
            if f.read_ok:
                f.tainted = True
            return True
        absent = f.optional and not f.exists
        self.opens.append((self.ntrace + 1, f, m, absent))
        if absent:
            # status 05 (OUTPUT: 00); INPUT leaves the file absent, the other modes create it
            f.exists = m != "INPUT"
            f.keys = set()
        elif m == "OUTPUT":
            f.keys = set()
        f.mode, f.read_ok, f.tainted, f.last, f.seqread = m, False, False, None, False
        f.readfail = False
        return True

    def op_close(self, f):
        self.lines.append(f"           CLOSE {f.name}")
        f.mode, f.read_ok = None, False
        return True

    def op_read(self, f):
        self.io(f"READ {f.name}", "AT END", "END-READ")
        f.read_ok = f.mode in ("INPUT", "I-O")
        f.tainted = False
        f.seqread = True
        return True

    def op_readnext(self, f):
        if f.readfail and not self.unsafe:
            return False
        self.io(f"READ {f.name} NEXT", "AT END", "END-READ")
        f.read_ok = False
        f.tainted = False
        f.seqread = True
        return True

    def g_optkey(self, f):
        """A keyed READ now would be the first READ of an absent OPTIONAL file opened INPUT
        (G-optkey; a START does not count, it is not known to end that state in GnuCOBOL)."""
        return not self.unsafe and f.mode == "INPUT" and f.optional and not f.exists and not f.seqread

    def op_keyread(self, f):
        if self.g_optkey(f):
            return False
        k = self.rng.choice(sorted(f.keys) if f.keys and self.rng.random() < 0.5 else KEYS)
        self.lines.append(f'           MOVE "{k}" TO K{f.i}')
        self.io(f"READ {f.name}", "INVALID KEY", "END-READ")
        f.read_ok = False
        f.tainted = False
        f.readfail = f.access == "dynamic" and k not in f.keys
        return True

    def op_start(self, f):
        k = self.rng.choice(KEYS)
        op = self.rng.choice(["=", ">", "NOT <"])
        self.lines.append(f'           MOVE "{k}" TO K{f.i}')
        self.io(f"START {f.name} KEY {op} K{f.i}", "INVALID KEY", "END-START")
        f.read_ok = False
        f.readfail = False
        return True

    def op_write(self, f):
        rng = self.rng
        n = self.ntrace + 1
        if f.org == "sequential":
            self.lines.append(f'           MOVE "W{n:03d}XXXX" TO R{f.i}')
            self.lines.append(f"           WRITE R{f.i}")
        elif f.access == "sequential":
            # ascending keys above every key of the file, only where the WRITE is allowed
            if f.mode not in ("OUTPUT", "EXTEND"):
                return False
            top = max(list(f.keys) + ([f.last] if f.last else []), default="")
            cand = [k for k in KEYS if k > top]
            if not cand:
                return False
            k = rng.choice(cand[:3])
            self.lines.append(f'           MOVE "{k}" TO K{f.i}')
            self.lines.append(f'           MOVE "W{n:03d}X" TO V{f.i}')
            self.io(f"WRITE R{f.i}", "INVALID KEY", "END-WRITE")
            f.keys.add(k)
            f.last = k
        else:
            k = rng.choice(KEYS)
            self.lines.append(f'           MOVE "{k}" TO K{f.i}')
            self.lines.append(f'           MOVE "W{n:03d}X" TO V{f.i}')
            self.io(f"WRITE R{f.i}", "INVALID KEY", "END-WRITE")
            if f.mode in ("OUTPUT", "I-O"):
                f.keys.add(k)
        f.read_ok = False
        return True

    def op_rewrite(self, f):
        rng = self.rng
        n = self.ntrace + 1
        if f.tainted:
            return False
        if f.org == "sequential":
            self.lines.append(f'           MOVE "R{n:03d}YYYY" TO R{f.i}')
            self.lines.append(f"           REWRITE R{f.i}")
        elif f.access == "sequential":
            # the record of the last READ, its key unchanged
            self.lines.append(f'           MOVE "R{n:03d}Y" TO V{f.i}')
            self.io(f"REWRITE R{f.i}", "INVALID KEY", "END-REWRITE")
        else:
            if f.mode == "I-O":
                if not f.keys:
                    return False
                k = rng.choice(sorted(f.keys))
            else:
                k = rng.choice(KEYS)
            self.lines.append(f'           MOVE "{k}" TO K{f.i}')
            self.lines.append(f'           MOVE "R{n:03d}Y" TO V{f.i}')
            self.io(f"REWRITE R{f.i}", "INVALID KEY", "END-REWRITE")
        f.read_ok = False
        return True

    def op_delete(self, f):
        rng = self.rng
        if f.tainted:
            return False
        if f.access == "sequential":
            # the record of the last READ (its key is no longer tracked: later WRITEs stay above it)
            self.lines.append(f"           DELETE {f.name}")
        else:
            k = rng.choice(sorted(f.keys) if f.keys and rng.random() < 0.6 else KEYS)
            self.lines.append(f'           MOVE "{k}" TO K{f.i}')
            self.io(f"DELETE {f.name}", "INVALID KEY", "END-DELETE")
            if f.mode == "I-O":
                f.keys.discard(k)
        f.read_ok = False
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
            if f.org == "indexed":
                acc = f.access.upper() if optional else "SEQUENTIAL"
                out.append(f"               ORGANIZATION IS INDEXED ACCESS MODE IS {acc}")
                out.append(f"               RECORD KEY IS K{f.i}")
            else:
                out.append("               ORGANIZATION IS SEQUENTIAL")
            out.append(f"               FILE STATUS IS ST{f.i}.")
        out += ["       DATA DIVISION.", "       FILE SECTION."]
        for f in self.files:
            if not optional and not f.present:
                continue
            out.append(f"       FD {f.name}.")
            if f.org == "indexed":
                out += [f"       01 R{f.i}.", f"          05 K{f.i} PIC X(3).", f"          05 V{f.i} PIC X(5)."]
            else:
                out.append(f"       01 R{f.i} PIC X(8).")
        out.append("       WORKING-STORAGE SECTION.")
        for f in self.files:
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
        target = rng.randint(10, 24)
        tries = 0
        while self.ntrace <= target and tries < 400:
            tries += 1
            if self.stmt():
                self.trace()
        # epilogue: close every file, then read each back
        for f in self.files:
            self.lines.append(f"           CLOSE {f.name}")
            self.trace()
        for f in self.files:
            self.lines.append(f"           OPEN INPUT {f.name}")
            self.trace()
            f.mode, f.seqread = "INPUT", False
            if f.org == "indexed" and f.access == "random":
                # a file still absent: OPEN INPUT (05) and CLOSE only (G-optkey)
                for k in [] if self.g_optkey(f) else KEYS:
                    self.lines.append(f'           MOVE "{k}" TO K{f.i}')
                    self.lines.append(f"           READ {f.name}")
                    self.trace()
            else:
                nxt = " NEXT" if f.access == "dynamic" else ""
                self.lines.append(f'           PERFORM WITH TEST AFTER UNTIL ST{f.i} NOT = "00"')
                self.lines.append(f"           READ {f.name}{nxt}")
                self.trace()
                self.lines.append("           END-PERFORM")
            self.lines.append(f"           CLOSE {f.name}")
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
    """Status, details and GnuCOBOL's lines of program `src` (written to base.cob): GnuCOBOL in
    the fresh directory wd after the setup program (if any) vs front end + cobolrun with the
    records `inputs` and the absent files `absent`."""
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
            return "cobc-error", "setup: " + (c.stderr[-800:] if c else "timeout"), None
        r = run([base + "S"], 20, env=env, cwd=wd)
        if r is None or r.returncode != 0 or r.stdout:
            return "setup-error", (r.stdout.decode("latin-1")[-300:] if r else "timeout"), None
    c = run([cobc, "-x", "-std=ibm", "-o", base, base + ".cob"], 120, text=True)
    if c is None or c.returncode != 0:
        return "cobc-error", (c.stderr[-800:] if c else "timeout"), None
    r = run([base], 20, env=env, cwd=wd)
    if r is None:
        return "gnucobol-timeout", None, None
    g = r.stdout.decode("latin-1").splitlines()
    if r.returncode != 0:
        return "gnucobol-abend", {"rc": r.returncode, "stderr": r.stderr.decode("latin-1")[-300:]}, g
    fe = run([sys.executable, "-I", "-B", cobolfe, base + ".cob", "--profile", "gnucobol", "--main",
              "-o", base + ".fe.json"], 120, text=True)
    if fe is None or fe.returncode != 0:
        return "frontend-error", (fe.stderr[-800:] if fe else "timeout"), g
    if "unsupported" in fe.stderr:
        return "frontend-unsupported", fe.stderr[-800:], g
    with open(base + ".inputs.json", "w") as fh:
        json.dump(inputs, fh)
    cmd = [cobolrun, base + ".fe.json", "--inputs", base + ".inputs.json"]
    if absent:
        cmd += ["--absent", ",".join(map(str, absent))]
    with open(base + ".cmd.json", "w") as fh:
        json.dump(cmd, fh)
    lr = run(cmd, 60, text=True)
    if lr is None:
        return "lean-timeout", None, g
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-800:], g
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop:"):
        return "lean-signal", {"signal": res["signal"], "lines": len(m), "gnucobol_lines": len(g)}, g
    if g != m:
        k = next((i for i, (a, b) in enumerate(zip(g, m)) if a != b), min(len(g), len(m)))
        return "mismatch", {"line": k, "gnucobol": g[k:k + 3], "lean": m[k:k + 3]}, g
    return "ok", None, g


def run_case(gen, wd, root):
    """One generated program."""
    os.makedirs(wd, exist_ok=True)
    src = gen.render()
    return compare(os.path.join(wd, gen.name), wd, root, src, gen.render_setup(), gen.inputs(), gen.absent())


def run_repro(path, out, root):
    """A reproducer (no setup; its absent files on a line `      * ABSENT: 1,2`): prints the
    verdict and, where the two sides differ, both outputs from the first difference."""
    name = os.path.splitext(os.path.basename(path))[0]
    wd = os.path.join(out, name)
    os.makedirs(wd)
    with open(path) as fh:
        src = fh.read()
    absent = []
    for ln in src.splitlines():
        if ln.startswith("      * ABSENT:"):
            absent = [int(x) for x in ln.split(":", 1)[1].split(",") if x.strip()]
    status, info, g = compare(os.path.join(wd, name), wd, root, src, None, [], absent)
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


def coverage(gen, g, cov):
    """Count the OPENs of the random part by (kind, mode, absent); check the predicted 05s."""
    by_trace = {}
    for ln in g or []:
        w = ln.split()
        if w and len(w[0]) == 4 and w[0][0] == "S" and w[0][1:].isdigit():
            by_trace.setdefault(int(w[0][1:]), w)
    for t, f, m, absent in gen.opens:
        key = f"{'absent' if absent else 'present'} {f.kind} {m}"
        cov["opens"][key] = cov["opens"].get(key, 0) + 1
        if absent and m != "OUTPUT":
            cov["predicted05"] += 1
            w = by_trace.get(t)
            if w is not None and len(w) > 2 * f.i - 1 and w[2 * f.i - 1] == "05":
                cov["seen05"] += 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=os.path.join(HERE, "out_opt"))
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(HERE)))
    ap.add_argument("--show", type=int, default=3)
    ap.add_argument("--unsafe", action="store_true", help="also generate the G-optkey and G-readfail forms")
    ap.add_argument("--run", nargs="+", metavar="PROG.cob", help="run reproducers instead")
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
    cov = {"opens": {}, "predicted05": 0, "seen05": 0}
    for i in range(a.n):
        name = f"OT{a.seed:02d}{i:03d}"
        gen = Gen(random.Random(rng.random()), name, a.unsafe)
        status, info, g = run_case(gen, os.path.join(a.out, name), root)
        tally[status] = tally.get(status, 0) + 1
        coverage(gen, g, cov)
        with open(os.path.join(a.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": i, "status": status}) + "\n")
        if status != "ok" and shown < a.show:
            shown += 1
            print(f"--- {name} {status}")
            print(json.dumps(info)[:1500])
    cov["opens"] = dict(sorted(cov["opens"].items()))
    print(json.dumps({"coverage": cov}))
    print(json.dumps({"tally": tally}))
    return 0 if tally.get("ok", 0) == a.n else 1


if __name__ == "__main__":
    sys.exit(main())

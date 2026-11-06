#!/usr/bin/env python3
"""Differential testing of indexed files in ACCESS DYNAMIC around a failed keyed READ: READ NEXT
after it (IBM: 46), and the statements that set the file position indicator again.

Each random program declares two or three indexed files, each with a FILE STATUS item:
  F1  ACCESS DYNAMIC, RECORD KEY K1, and no alternate key, a unique alternate key A1 that the
      program never names (both: the model's record-key path, `FileDecl.keyRef` false), or an
      alternate key A2 WITH DUPLICATES (`keyRef` true: alttest.py's path);
  F2  ACCESS DYNAMIC, RECORD KEY K2, no alternate key;
  F3  (most programs) ACCESS SEQUENTIAL, RECORD KEY K3, no alternate key.
A setup program (GnuCOBOL) first creates the files with 0-7 records each, written in ascending
record-key order; the model gets them with --inputs. The program clears the record areas, opens
the files I-O and runs 15-35 random steps:
  F1, F2: START KEY = / > / >= / NOT < on the record key (value in the file or not), READ NEXT,
      keyed READ (READ f / READ f KEY IS K; record key in the file or not), WRITE (record key new
      or in use), REWRITE of a record key in the file, DELETE (record key in the file or not),
      CLOSE + OPEN I-O. After a failed keyed READ, READ NEXT is weighted up, also after a WRITE,
      REWRITE or DELETE, until a START, a successful keyed READ or an OPEN;
  F3: START (found or not), READ, REWRITE and DELETE of the record read (43 without one), WRITE
      (48: open I-O, ACCESS SEQUENTIAL);
with and without INVALID KEY / AT END phrases. After every step the program displays a trace line:
its number, every FILE STATUS and every record area. An epilogue closes the files, opens them
INPUT and reads each in record-key order (START NOT < LOW-VALUES, then one READ NEXT more than
there are records).

alttest.py's `Mirror` (IBM Enterprise COBOL 6.4's rules) predicts every status: a READ NEXT after a
failed keyed READ gets 46 ("The preceding READ statement was unsuccessful but did not cause an
at-end condition"; the file position indicator is undefined after an unsuccessful READ), and
so does one after a failed START or after the at-end condition. The model's status on every trace
line must equal the mirror's (status-mismatch otherwise). The model's DISPLAY lines must equal
GnuCOBOL's (mismatch otherwise), once every 02 that the mirror predicts is read as 00 (G-dup02,
alttest.py), except where GnuCOBOL departs from IBM:
  G-readfail  a READ NEXT after a failed keyed READ (before a START, a successful keyed READ or an
           OPEN): GnuCOBOL 3.2 continues from where it was (files without alternate keys), or
           repeats or skips records, or gives 46. On those trace lines the file's status and
           record area are compared with the mirror only (46; the area as before the READ:
           the model leaves the record area of a failed READ unchanged), not with GnuCOBOL, and
           the program then moves the mirror's area to the record and its status to the FILE
           STATUS item (both sides equal again). Such a READ NEXT has no AT END phrase (GnuCOBOL
           might run one).
Kept out of generation as in alttest.py: G-rw21 (REWRITE of a missing record key), G-rwalt (F3 has
no alternate key), G-open41 (no OPEN of an open file), WRITE in ACCESS SEQUENTIAL OUTPUT mode.
The summary counts the statements by kind, file path and mirror status, and GnuCOBOL's statuses
on the G-readfail lines.

Statuses: "ok", "mismatch", "status-mismatch", "area-mismatch" (model area on a G-readfail line
differs from the mirror's), "gnucobol-02", and alttest.py's run statuses (cobc-error,
setup-error, gnucobol-abend, gnucobol-timeout, frontend-error, frontend-unsupported,
lean-timeout, cobolrun-error, lean-signal).

usage: dyntest.py [--n N] [--seed S] [--out DIR] [--root TREE] [--show K]
  --root: the coblean tree whose front end and cobolrun are tested (default: this script's)
"""
import argparse
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import alttest as A  # noqa: E402

OPS = ["=", ">", ">=", "NOT <"]


class Gen:
    def __init__(self, rng, name):
        self.rng, self.name = rng, name
        f1 = rng.choice(["", "", "u", "u", "d"])
        self.specs = [A.Spec(1, "dynamic", "K", f1, 3), A.Spec(2, "dynamic", "L", "", 3)]
        if rng.random() < 0.7:
            self.specs.append(A.Spec(3, "sequential", "S", "", 4))
        self.path = {s.i: ("keyRef" if any(d for _, _, _, d in s.alts) else "basic") for s in self.specs}
        self.init = {}
        for s in self.specs:
            ks = sorted(rng.sample(s.kvals, rng.randint(0, 7)))
            us = rng.sample(A.UNIQV, len(ks))
            self.init[s.i] = [k + u + rng.choice(A.DUPV) + self.data(s) for k, u in zip(ks, us)]
        self.m = {s.i: A.Mirror(s, self.init[s.i]) for s in self.specs}
        self.area = {s.i: " " * s.reclen for s in self.specs}
        self.lines = []
        self.traces = []      # per trace line: (mirror statuses, {file index: predicted area} masked)
        self.cnt = {}
        self.n = 0

    def data(self, s):
        return "".join(self.rng.choice("pqrstvw") for _ in range(s.dlen))

    def count(self, what, s, m):
        k = f"{what} F{s.i}/{self.path[s.i]} {m.fs}"
        self.cnt[k] = self.cnt.get(k, 0) + 1

    # ---------------------------------------------------------------- program text
    def select(self, s):
        out = [f'           SELECT {s.name} ASSIGN TO "{self.name}{s.i}"',
               f"               ORGANIZATION IS INDEXED ACCESS MODE IS {s.access.upper()}",
               f"               RECORD KEY IS {s.kname}"]
        for f, _, _, dups in s.alts:
            out.append(f"               ALTERNATE RECORD KEY IS {f}" + (" WITH DUPLICATES" if dups else ""))
        out.append(f"               FILE STATUS IS FS{s.i}.")
        return out

    def fd(self, s):
        return [f"       FD {s.name}.", f"       01 REC{s.i}.", f"          05 {s.kname} PIC X(3).",
                f"          05 {s.uname} PIC X(2).", f"          05 {s.dname}.",
                f"             10 {s.pname} PIC X.", f"             10 {s.rname} PIC X.",
                f"          05 {s.data} PIC X({s.dlen})."]

    def header(self, name):
        out = ["       IDENTIFICATION DIVISION.", f"       PROGRAM-ID. {name}.",
               "       ENVIRONMENT DIVISION.", "       INPUT-OUTPUT SECTION.", "       FILE-CONTROL."]
        for s in self.specs:
            out += self.select(s)
        out += ["       DATA DIVISION.", "       FILE SECTION."]
        for s in self.specs:
            out += self.fd(s)
        out += ["       WORKING-STORAGE SECTION."]
        for s in self.specs:
            out.append(f'       01 FS{s.i} PIC XX VALUE "00".')
        out += ["       PROCEDURE DIVISION.", "       MAIN."]
        return out

    def render_setup(self):
        out = self.header(self.name + "S")
        for s in self.specs:
            out.append(f"           OPEN OUTPUT {s.name}")
            for r in self.init[s.i]:
                out.append(f'           MOVE "{r}" TO REC{s.i}')
                out.append(f"           WRITE REC{s.i}")
            out.append(f"           CLOSE {s.name}")
            out.append(f'           IF FS{s.i} NOT = "00" DISPLAY "SETUP {s.i} " FS{s.i} END-IF')
        out.append("           STOP RUN.")
        return "\n".join(out) + "\n"

    def trace(self, masked=None):
        self.n += 1
        fs = ' " " '.join(f"FS{s.i}" for s in self.specs)
        recs = ' "|" '.join(f"REC{s.i}" for s in self.specs)
        self.lines += A.wrap(f'DISPLAY "T{self.n:03d} " {fs} " " {recs} "|"')
        mask = {}
        if masked is not None:
            j = [s.i for s in self.specs].index(masked.i)
            mask[j] = self.area[masked.i]
        self.traces.append(([self.m[s.i].fs for s in self.specs], mask))

    def emit(self, text, phrase=None):
        """A statement, with its phrases (`phrase`: "INVALID KEY" / "AT END") half of the time."""
        if phrase is not None and self.rng.random() < 0.5:
            neg = "NOT " + phrase
            text += f' {phrase} DISPLAY "P{self.n + 1:03d} E" {neg} DISPLAY "P{self.n + 1:03d} N"'
            text += " END-" + text.split()[0]
        self.lines += A.wrap(text)

    def move_rec(self, s, r):
        self.lines.append(f'           MOVE "{r}" TO REC{s.i}')
        self.area[s.i] = r

    def move_key(self, s, k):
        self.lines.append(f'           MOVE "{k}" TO {s.kname}')
        self.area[s.i] = k + self.area[s.i][3:]

    def got(self, s, m):
        """After a READ: the record read is in the area (a failed READ leaves it)."""
        if m.fs in ("00", "02") and m.cur is not None:
            self.area[s.i] = m.recs[m.cur]

    # ---------------------------------------------------------------- statements
    def key(self, s, m, p_in):
        pool = sorted(m.recs) if m.recs and self.rng.random() < p_in else s.kvals
        return self.rng.choice(pool)

    def stmt_start(self, s, m):
        k = self.key(s, m, 0.6)
        op = self.rng.choice(OPS)
        self.move_key(s, k)
        self.emit(f"START {s.name} KEY IS {op} {s.kname}", "INVALID KEY")
        m.start(">=" if op == "NOT <" else op, 0, 3, k)
        self.count("START", s, m)
        self.trace()

    def stmt_read_next(self, s, m):
        if m.readfail:
            # G-readfail: no phrase; compared with the mirror only, then the record area and the
            # FILE STATUS item made equal on both sides (the mirror's values)
            self.lines.append(f"           READ {s.name} NEXT RECORD")
            m.read_next()
            self.count("READ-NEXT-after-failed-READ", s, m)
            self.got(s, m)
            self.trace(masked=s)
            self.move_rec(s, self.area[s.i])
            self.lines.append(f'           MOVE "{m.fs}" TO FS{s.i}')
            return
        if s.access == "sequential":
            self.emit(f"READ {s.name}" + (" NEXT RECORD" if self.rng.random() < 0.5 else ""), "AT END")
        else:
            self.emit(f"READ {s.name} NEXT RECORD", "AT END")
        what = "READ-NEXT" if not m.eof else "READ-NEXT-at-eof"
        m.read_next()
        self.count(what, s, m)
        self.got(s, m)
        self.trace()

    def stmt_read_key(self, s, m):
        k = self.key(s, m, 0.5)
        self.move_key(s, k)
        if self.rng.random() < 0.3:
            self.emit(f"READ {s.name}", "INVALID KEY")
        else:
            self.emit(f"READ {s.name} KEY IS {s.kname}", "INVALID KEY")
        m.read_key(0, k)
        self.count("READ-KEY", s, m)
        self.got(s, m)
        self.trace()

    def new_record(self, s, m, k, old=None):
        rng = self.rng
        uv = old[3:5] if old is not None and rng.random() < 0.5 else None
        if uv is None:
            used = sorted({r[3:5] for r in m.recs.values()})
            uv = rng.choice(used) if used and rng.random() < 0.2 else rng.choice(A.UNIQV)
        dv = old[5:7] if old is not None and rng.random() < 0.4 else rng.choice(A.DUPV)
        return k + uv + dv + self.data(s)

    def stmt_write(self, s, m):
        k = self.key(s, m, 0.2)
        self.move_rec(s, self.new_record(s, m, k))
        self.emit(f"WRITE REC{s.i}", "INVALID KEY" if s.access != "sequential" else None)
        m.write(self.area[s.i])
        self.count("WRITE", s, m)
        self.trace()

    def stmt_rewrite(self, s, m):
        if s.access == "sequential":
            if m.cur is None and self.rng.random() < 0.7:
                return
            k = m.cur if m.cur is not None else self.rng.choice(s.kvals)
            old = m.recs.get(k)
            r = self.new_record(s, m, k, old) if old is not None else k + "u1Ax" + self.data(s)
        else:
            if not m.recs:
                return
            k = self.rng.choice(sorted(m.recs))
            r = self.new_record(s, m, k, m.recs[k])
        self.move_rec(s, r)
        self.emit(f"REWRITE REC{s.i}", "INVALID KEY" if s.access != "sequential" else None)
        m.rewrite(r)
        self.count("REWRITE", s, m)
        self.trace()

    def stmt_delete(self, s, m):
        if s.access == "sequential":
            if m.cur is None and self.rng.random() < 0.7:
                return
            self.lines.append(f"           DELETE {s.name} RECORD")
            m.delete(None)
        else:
            k = self.key(s, m, 0.7)
            self.move_key(s, k)
            self.emit(f"DELETE {s.name} RECORD", "INVALID KEY")
            m.delete(k)
        self.count("DELETE", s, m)
        self.trace()

    def stmt_reopen(self, s, m):
        self.lines.append(f"           CLOSE {s.name}")
        m.close()
        self.lines.append(f"           OPEN I-O {s.name}")
        m.open("io")
        self.count("CLOSE+OPEN", s, m)
        self.trace()

    def step(self):
        rng = self.rng
        s = rng.choice(self.specs + self.specs[:2])
        m = self.m[s.i]
        x = rng.random()
        if s.access == "sequential":
            if x < 0.25:
                self.stmt_start(s, m)
            elif x < 0.65:
                self.stmt_read_next(s, m)
            elif x < 0.8:
                self.stmt_rewrite(s, m)
            elif x < 0.95:
                self.stmt_delete(s, m)
            else:
                self.stmt_write(s, m)
            return
        if m.readfail and x < 0.5:
            self.stmt_read_next(s, m)
            return
        if x < 0.18:
            self.stmt_start(s, m)
        elif x < 0.42:
            self.stmt_read_next(s, m)
        elif x < 0.66:
            self.stmt_read_key(s, m)
        elif x < 0.78:
            self.stmt_write(s, m)
        elif x < 0.86:
            self.stmt_rewrite(s, m)
        elif x < 0.95:
            self.stmt_delete(s, m)
        else:
            self.stmt_reopen(s, m)

    def epilogue(self):
        for s in self.specs:
            self.lines.append(f"           CLOSE {s.name}")
            self.m[s.i].close()
        for s in self.specs:
            self.lines.append(f"           OPEN INPUT {s.name}")
            self.m[s.i].open("input")
        self.trace()
        for s in self.specs:
            m = self.m[s.i]
            self.lines.append(f"           MOVE LOW-VALUES TO {s.kname}")
            self.area[s.i] = "\x00" * 3 + self.area[s.i][3:]
            self.lines.append(f"           START {s.name} KEY IS NOT < {s.kname}")
            m.start(">=", 0, 3, "\x00" * 3)
            self.trace()
            for _ in range(len(m.recs) + 1):
                self.lines.append(f"           READ {s.name} NEXT RECORD")
                m.read_next()
                self.got(s, m)
                self.trace()

    def render(self):
        out = self.header(self.name)
        for s in self.specs:
            self.lines.append(f"           MOVE SPACES TO REC{s.i}")
        for s in self.specs:
            self.lines.append(f"           OPEN I-O {s.name}")
            self.m[s.i].open("io")
        self.trace()
        for _ in range(self.rng.randint(15, 35)):
            self.step()
        self.epilogue()
        for s in self.specs:
            self.lines.append(f"           CLOSE {s.name}")
        out += self.lines
        out.append("           STOP RUN.")
        return "\n".join(out) + "\n"

    def inputs(self):
        return [[s.i, [list(r.encode("ascii")) for r in self.init[s.i]]] for s in self.specs if self.init[s.i]]


def columns(ln, specs):
    """(statuses, records) of a trace line."""
    nf = len(specs)
    st = [ln[5 + 3 * j:7 + 3 * j] for j in range(nf)]
    recs, p = [], 5 + 3 * nf
    for s in specs:
        recs.append(ln[p:p + s.reclen])
        p += s.reclen + 1
    return st, recs


def rebuild(ln, specs, st, recs):
    return ln[:5] + " ".join(st) + " " + "".join(r + "|" for r in recs)


def judge(g, m, gen):
    """Compare GnuCOBOL's lines g and the model's lines m of program gen: (status, info, readfail
    statuses GnuCOBOL gave)."""
    specs, traces = gen.specs, gen.traces
    gfail = []
    gn, mn = [], []
    for ln in g:
        t = A.TRACE.match(ln)
        if t is not None and any(ln[5 + 3 * j:7 + 3 * j] == "02" for j in range(len(specs))):
            return "gnucobol-02", ln, gfail
    for ln in m:
        t = A.TRACE.match(ln)
        if t is None:
            mn.append(ln)
            continue
        i = int(t.group(1))
        pred, mask = traces[i - 1]
        st, recs = columns(ln, specs)
        for j, p in enumerate(pred):
            if st[j] != p:
                return "status-mismatch", {"line": ln, "file": specs[j].i, "model": st[j], "mirror": p,
                                           "g_readfail_line": j in mask}, gfail
        for j, area in mask.items():
            if recs[j] != area:
                return "area-mismatch", {"line": ln, "file": specs[j].i, "model": recs[j], "mirror": area}, gfail
        st = ["00" if x == "02" else x for x in st]
        for j in mask:
            st[j], recs[j] = "##", "#" * specs[j].reclen
        mn.append(rebuild(ln, specs, st, recs))
    for ln in g:
        t = A.TRACE.match(ln)
        if t is None:
            gn.append(ln)
            continue
        i = int(t.group(1))
        if i > len(traces):
            gn.append(ln)
            continue
        _, mask = traces[i - 1]
        if not mask:
            gn.append(ln)
            continue
        st, recs = columns(ln, specs)
        for j in mask:
            gfail.append(st[j])
            st[j], recs[j] = "##", "#" * specs[j].reclen
        gn.append(rebuild(ln, specs, st, recs))
    if gn != mn:
        k = next((i for i, (a, b) in enumerate(zip(gn, mn)) if a != b), min(len(gn), len(mn)))
        return "mismatch", {"line": k, "gnucobol": g[k:k + 3], "lean": m[k:k + 3]}, gfail
    return "ok", {"lines": len(g)}, gfail


def compare(base, wd, root, gen):
    """Program gen (written to base.cob): GnuCOBOL in the fresh directory wd after the setup
    program vs front end + cobolrun with the setup's records (alttest.compare's runs), judged."""
    cobc = os.path.join(root, "scripts", "cobc.sh")
    cobolfe = os.path.join(root, "tools", "cobolfe", "cobolfe.py")
    cobolrun = os.path.join(root, ".lake", "build", "bin", "cobolrun")
    env = dict(os.environ, LD_LIBRARY_PATH=os.path.join(root, "third_party", "gnucobol", "usr", "lib",
                                                        "x86_64-linux-gnu"))
    with open(base + ".cob", "w") as fh:
        fh.write(gen.render())
    with open(base + "S.cob", "w") as fh:
        fh.write(gen.render_setup())
    c = A.run([cobc, "-x", "-std=ibm", "-o", base + "S", base + "S.cob"], 120, text=True)
    if c is None or c.returncode != 0:
        return "cobc-error", "setup: " + (c.stderr[-800:] if c else "timeout"), []
    r = A.run([base + "S"], 20, env=env, cwd=wd)
    if r is None or r.returncode != 0 or r.stdout:
        return "setup-error", (r.stdout.decode("latin-1")[-300:] if r else "timeout"), []
    c = A.run([cobc, "-x", "-std=ibm", "-o", base, base + ".cob"], 120, text=True)
    if c is None or c.returncode != 0:
        return "cobc-error", (c.stderr[-800:] if c else "timeout"), []
    r = A.run([base], 20, env=env, cwd=wd)
    if r is None:
        return "gnucobol-timeout", None, []
    g = r.stdout.decode("latin-1").splitlines()
    if r.returncode != 0:
        return "gnucobol-abend", {"rc": r.returncode, "stderr": r.stderr.decode("latin-1")[-300:]}, []
    fe = A.run([sys.executable, "-I", "-B", cobolfe, base + ".cob", "--profile", "gnucobol", "--main",
                "-o", base + ".fe.json"], 120, text=True)
    if fe is None or fe.returncode != 0:
        return "frontend-error", (fe.stderr[-800:] if fe else "timeout"), []
    if "unsupported" in fe.stderr:
        return "frontend-unsupported", fe.stderr[-800:], []
    with open(base + ".inputs.json", "w") as fh:
        json.dump(gen.inputs(), fh)
    lr = A.run([cobolrun, base + ".fe.json", "--inputs", base + ".inputs.json"], 60, text=True)
    if lr is None:
        return "lean-timeout", None, []
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-800:], []
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop:"):
        return "lean-signal", {"signal": res["signal"], "lines": len(m), "gnucobol_lines": len(g)}, []
    with open(base + ".gnucobol.txt", "w", encoding="latin-1") as fh:
        fh.write("".join(ln + "\n" for ln in g))
    with open(base + ".model.txt", "w", encoding="latin-1") as fh:
        fh.write("".join(ln + "\n" for ln in m))
    return judge(g, m, gen)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=os.path.join(HERE, "out_dyn"))
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(HERE)))
    ap.add_argument("--show", type=int, default=3)
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    os.makedirs(a.out, exist_ok=True)
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, shown = {}, 0
    cov = {"traces": 0, "files": {}, "stmts": {}, "gnucobol_on_readfail": {}}
    for i in range(a.n):
        name = f"DY{a.seed:02d}{i:03d}"
        gen = Gen(random.Random(rng.random()), name)
        wd = os.path.join(a.out, name)
        os.makedirs(wd, exist_ok=True)
        status, info, gfail = compare(os.path.join(wd, name), wd, root, gen)
        tally[status] = tally.get(status, 0) + 1
        cov["traces"] += len(gen.traces)
        for s in gen.specs:
            k = f"F{s.i}:{s.access}/{gen.path[s.i]}" + ("+alt" if s.alts else "")
            cov["files"][k] = cov["files"].get(k, 0) + 1
        for k, v in gen.cnt.items():
            cov["stmts"][k] = cov["stmts"].get(k, 0) + v
        for x in gfail:
            cov["gnucobol_on_readfail"][x] = cov["gnucobol_on_readfail"].get(x, 0) + 1
        with open(os.path.join(a.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": i, "status": status}) + "\n")
        if status != "ok":
            with open(os.path.join(a.out, "details.jsonl"), "a") as fh:
                fh.write(json.dumps({"case": i, "name": name, "status": status, "info": info}) + "\n")
        if status != "ok" and shown < a.show:
            shown += 1
            print(f"--- {name} {status}")
            print(json.dumps(info)[:1500])
    for k in ("files", "stmts", "gnucobol_on_readfail"):
        cov[k] = dict(sorted(cov[k].items()))
    print(json.dumps({"coverage": cov}))
    print(json.dumps({"tally": tally}))
    return 0 if tally.get("ok", 0) == a.n else 1


if __name__ == "__main__":
    sys.exit(main())

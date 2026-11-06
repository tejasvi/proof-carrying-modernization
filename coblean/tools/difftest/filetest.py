#!/usr/bin/env python3
"""Differential testing of file I/O: OPEN / READ / WRITE / REWRITE / DELETE / CLOSE.

Each random program declares 1-3 files: sequential, or indexed with ACCESS SEQUENTIAL or
RANDOM, a RECORD KEY and optionally an ALTERNATE RECORD KEY without duplicates; most files
have a FILE STATUS item.  The program creates its files itself (the first OPEN of a file is
OPEN OUTPUT) and runs a random sequence of I/O statements, misuse included (status 21, 22,
23, 41, 42, 43, 46, 47, 48, 49), with and without AT END / INVALID KEY / NOT AT END /
NOT INVALID KEY phrases.  After every statement the program stores, at a fixed position of
a trace buffer, the file status ('--' for a file without FILE STATUS), a marker of the
phrase that ran ('E' AT END / INVALID KEY, 'N' NOT AT END / NOT INVALID KEY) and, after a
READ, the record area (and the INTO item), and DISPLAYs that slot ('@nnn ' and the slot).
An epilogue closes every file and reads it back (sequentially, or by every record key and
alternate key value).  The working-storage record is dumped at the end, as in difftest.py.
The DISPLAY lines are compared line by line on both sides (`mismatch-trace`), also when the
program abends, where the final dump is lost (`abend-trace-mismatch`).

GnuCOBOL (`-std=ibm`) runs the program; the front end (tools/cobolfe) extracts the IR from
the same source and cobolrun runs it.  The dumps must agree (the dump epilogue is outside
the IR: execution faults there with storage final).  A statement that fails without an
applicable phrase on a file without FILE STATUS abends: both sides must then stop at the
same statement with the same status (`fault:...io N` / libcob's message).

`Sim` mirrors the model (Cobol/Sem/File.lean) to steer generation: files exist before they
are opened for input, statements on a file without FILE STATUS rarely fail unhandled.
`Sim(gnu=True)` mirrors the GnuCOBOL 3.2 (BDB) behaviour observed where it differs from the
model; the deviation classes are listed in KNOWN.  A statement where the two mirrors
disagree carries its class: classes in --exclude are not generated, and a mismatch is
reported under the class of the first disagreeing statement (`mismatch` alone = new).

usage: filetest.py [--n N] [--seed S] [--out DIR] [--keep] [--exclude CLASSES] [--show K]
       filetest.py --run PROG.cob...   (e.g. the reproducers in tools/difftest/filetest_cases)
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

ALNUM = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
KEYS = [b"K%02d" % i for i in range(1, 9)]   # record key values (ascending)
ALTS = [b"A%d" % i for i in range(1, 7)]     # alternate key values
SENT = b"FTRACE01"                           # first bytes of the dumped record R
MODEKW = {"input": "INPUT", "output": "OUTPUT", "io": "I-O", "extend": "EXTEND"}
UNKNOWN = -1                                 # a status the GnuCOBOL mirror cannot predict

# Known deviation classes: (who deviates from IBM Enterprise COBOL, description).
KNOWN = {
    # GnuCOBOL 3.2 deviations (excluded by default)
    "G-dup21": ("gnucobol", "ACCESS SEQUENTIAL WRITE in OUTPUT mode: a duplicate record key "
                            "(equal to the previous key) or alternate key gives 21 (IBM: 22)"),
    "G-extend": ("gnucobol", "OPEN EXTEND, ACCESS SEQUENTIAL: keys are checked only against keys "
                             "written since the OPEN, not the highest key in the file (IBM: 21)"),
    "G-lastkey": ("gnucobol", "a failed ACCESS SEQUENTIAL WRITE still becomes the previous key of "
                              "the ascending-key check: later WRITEs get 21 (IBM: previous record "
                              "written)"),
    "G-rwkey": ("gnucobol", "ACCESS SEQUENTIAL REWRITE with a changed record key rewrites by key "
                            "(00; or 22 and the READ record deleted) (IBM: 21, file unchanged)"),
    "G-rwalt": ("gnucobol", "ACCESS SEQUENTIAL REWRITE of an indexed file with an alternate key "
                            "fails with 22 (BDB0631 cursor error), record unchanged (IBM: 00)"),
    "G-rw21": ("gnucobol", "random REWRITE of a missing record key gives 21, or 22 if its "
                           "alternate key is in use (IBM: 23)"),
    "G-open41": ("gnucobol", "a failed OPEN (41) between a READ and a REWRITE / DELETE (sequential "
                             "access) does not cancel the READ: 00 (IBM: 43, the last I/O statement "
                             "was not a successful READ)"),
    # model and front-end classes: none known (OPEN WITH NO REWIND is unsupported in the front
    # end; CLOSE's phrases are tested by closetest.py; GnuCOBOL's behaviour: filetest_cases/)
}
GROUPS = {"gnucobol", "model", "frontend"}


def parse_exclude(spec):
    out = set()
    for w in filter(None, spec.split(",")):
        if w == "all":
            out |= set(KNOWN)
        elif w == "none":
            pass
        elif w in GROUPS:
            out |= {c for c, (k, _) in KNOWN.items() if k == w}
        elif w in KNOWN:
            out.add(w)
        else:
            raise SystemExit(f"unknown class {w}; known: {', '.join(sorted(KNOWN))}, "
                             f"{', '.join(sorted(GROUPS))}, all, none")
    return out


# ---------------------------------------------------------------- files and the model mirror
class FileSpec:
    def __init__(self, idx, org, access, alt, fs, prog):
        self.idx, self.org, self.access, self.alt, self.fs = idx, org, access, alt, fs
        self.name = f"XF{idx}"
        self.phys = f"{prog}_{idx}.dat"
        if org == "indexed":
            self.fields = [(self.name + "-K", 3)] + ([(self.name + "-A", 2)] if alt else []) + \
                [(self.name + "-D", 3)]
            self.key = (0, 3)
            self.altkey = (3, 2) if alt else None
        else:
            self.fields = [(self.name + "-D", 6)]
            self.key = self.altkey = None
        self.reclen = sum(n for _, n in self.fields)

    @property
    def indexed(self):
        return self.org == "indexed"

    @property
    def seqacc(self):
        return self.access == "sequential"

    def keydecl(self, k):
        return self.key if k == 0 else self.altkey

    def describe(self):
        d = self.org if not self.indexed else f"indexed/{self.access}" + ("+alt" if self.alt else "")
        return f"{self.name} {d}" + ("" if self.fs else " (no FILE STATUS)")


def find(recs, kd, v):
    off, ln = kd
    for i, r in enumerate(recs):
        if r[off:off + ln] == v:
            return i
    return None


def keyof(kd, r):
    return r[kd[0]:kd[0] + kd[1]]


class FSt:
    def __init__(self):
        self.mode = None       # None = closed
        self.recs = []         # file order / record-key order
        self.pos = 0           # next record of a sequential READ
        self.eof = False
        self.cur = None        # record of the last successful READ
        self.exists = False    # created by an OPEN OUTPUT
        self.read_done = False  # GnuCOBOL flag_read_done
        self.last_key = None   # GnuCOBOL: previous key of the ascending-key check
        self.ibm_read_ok = False  # IBM, model: the last I/O statement was a successful READ

    def clone(self):
        c = FSt()
        c.__dict__.update(self.__dict__)
        c.recs = list(self.recs)
        return c


class Outcome:
    def __init__(self, status, marker, abend, area, into):
        self.status, self.marker, self.abend, self.area, self.into = status, marker, abend, area, into


class Sim:
    """Mirror of `fileOpen` ... `fileDelete` and the phrase dispatch (`ioNext`) of the model;
    with `gnu=True`, of GnuCOBOL 3.2 where it differs.  After `apply`, `why` is the class of
    the GnuCOBOL path when its result differs from the model's on the same state."""

    def __init__(self, specs, gnu=False):
        self.specs = {s.idx: s for s in specs}
        self.gnu = gnu
        self.st = {s.idx: FSt() for s in specs}
        self.area = {s.idx: b" " * s.reclen for s in specs}
        self.into = {s.idx: b" " * s.reclen for s in specs}
        self.why = None

    def clone(self):
        c = Sim.__new__(Sim)
        c.specs, c.gnu = self.specs, self.gnu
        c.st = {k: v.clone() for k, v in self.st.items()}
        c.area, c.into = dict(self.area), dict(self.into)
        c.why = None
        return c

    def apply(self, t):
        self.why = None
        f, s = self.specs[t.f], self.st[t.f]
        if t.rec is not None:
            self.area[t.f] = t.rec
        if t.setkey is not None:
            off, ln = f.keydecl(t.setkey[0])
            a = self.area[t.f]
            self.area[t.f] = a[:off] + t.setkey[1] + a[off + ln:]
        if t.op == "open":
            code, cond = self.open(s, t.mode), False
        elif t.op == "close":
            code, cond = self.close(s), False
        elif t.op == "read":
            code = self.read(f, s, t.key)
            cond = code == 10 if t.key is None else code // 10 == 2
        elif t.op == "write":
            code = self.write(f, s, self.area[t.f])
            cond = f.indexed and code // 10 == 2
        elif t.op == "rewrite":
            code = self.rewrite(f, s, self.area[t.f])
            cond = f.indexed and code // 10 == 2
        else:
            code = self.delete(f, s)
            cond = code // 10 == 2
        if code == UNKNOWN:
            return Outcome(UNKNOWN, "?", False, None, None)
        if code < 10:
            if t.op == "read" and t.into:
                self.into[t.f] = self.area[t.f]
            return Outcome(code, "N" if t.noexc else " ", False, self.area[t.f], self.into[t.f])
        if cond and t.exc:
            return Outcome(code, "E", False, self.area[t.f], self.into[t.f])
        return Outcome(code, " ", not f.fs, self.area[t.f], self.into[t.f])

    def open(self, s, mode):
        if s.mode is not None:
            s.ibm_read_ok = False   # GnuCOBOL keeps the READ (G-open41)
            return 41
        s.mode, s.pos, s.eof, s.cur = mode, 0, False, None
        if mode == "output":
            s.recs, s.exists = [], True
        s.read_done, s.last_key, s.ibm_read_ok = False, None, False
        return 0

    def close(self, s):
        s.read_done = s.ibm_read_ok = False
        if s.mode is None:
            return 42
        s.mode, s.cur = None, None
        return 0

    def read(self, f, s, key):
        s.read_done = s.ibm_read_ok = False
        if s.mode not in ("input", "io"):
            return 47
        if key is None:
            if s.eof:
                return 46
            if s.pos >= len(s.recs):
                s.eof, s.cur = True, None
                return 10
            self.area[f.idx] = s.recs[s.pos]
            s.cur, s.pos = s.pos, s.pos + 1
        else:
            kd = f.keydecl(key)
            i = find(s.recs, kd, keyof(kd, self.area[f.idx]))
            if i is None:
                s.cur = None
                return 23
            self.area[f.idx] = s.recs[i]
            s.pos, s.eof, s.cur = i + 1, False, i
        s.read_done = s.ibm_read_ok = True
        return 0

    def altclash(self, f, recs, bs, skip):
        if f.altkey is None:
            return False
        v = keyof(f.altkey, bs)
        return any(i != skip and keyof(f.altkey, r) == v for i, r in enumerate(recs))

    def write(self, f, s, bs):
        s.read_done = s.ibm_read_ok = False
        if not f.indexed:
            if s.mode in ("output", "extend"):
                s.recs.append(bs)
                return 0
            return 48
        allowed = s.mode in ("output", "extend") if f.seqacc else s.mode in ("output", "io")
        if not allowed:
            return 48
        k = keyof(f.key, bs)
        dup = find(s.recs, f.key, k) is not None
        alt = self.altclash(f, s.recs, bs, None)
        mx = keyof(f.key, s.recs[-1]) if s.recs else None
        code = 21 if f.seqacc and mx is not None and k < mx else 22 if dup or alt else 0
        if self.gnu and f.seqacc:
            # GnuCOBOL: the key becomes the previous key before the write is attempted; in
            # OUTPUT mode a duplicate (record or alternate key) is reported as 21
            last = s.last_key
            if last is not None and k < last:
                g = 21
            else:
                s.last_key = k
                g = (21 if s.mode == "output" else 22) if dup or alt else 0
            if g != code:
                self.why = classify_seqwrite(code, g, k, last)
            code = g
        if code == 0:
            for i, r in enumerate(s.recs):
                if k < keyof(f.key, r):
                    s.recs.insert(i, bs)
                    break
            else:
                s.recs.append(bs)
        return code

    def replace(self, f, s, i, bs):
        if self.altclash(f, s.recs, bs, i):
            return 22
        s.recs[i], s.cur = bs, None
        return 0

    def rewrite(self, f, s, bs):
        done, ibm_ok = s.read_done, s.ibm_read_ok
        s.read_done = s.ibm_read_ok = False
        if s.mode != "io":
            return 49
        if f.indexed and not f.seqacc:
            i = find(s.recs, f.key, keyof(f.key, bs))
            if self.gnu and i is None:
                # GnuCOBOL: 22 if the alternate key is in use, else 21
                self.why = "G-rw21"
                return 22 if self.altclash(f, s.recs, bs, None) else 21
            return 23 if i is None else self.replace(f, s, i, bs)
        # sequential access: the record of the last READ, which must be the last I/O statement
        # executed for the file
        if not self.last_read(s, done, ibm_ok):
            return 43
        if self.gnu and f.alt:
            # GnuCOBOL (BDB): "BDB0631 Cursor position must be set before performing this
            # operation", status 22, record unchanged
            self.why = self.why or "G-rwalt"
            return 22
        if f.indexed and keyof(f.key, s.recs[s.cur]) != keyof(f.key, bs):
            if self.gnu:
                self.why = self.why or "G-rwkey"
                return UNKNOWN
            return 21
        return self.replace(f, s, s.cur, bs)

    def last_read(self, s, done, ibm_ok):
        """A sequential-access REWRITE / DELETE may proceed (else 43)."""
        if s.cur is None or not (done if self.gnu else ibm_ok):
            return False
        if self.gnu and not ibm_ok:
            self.why = "G-open41"
        return True

    def delete(self, f, s):
        done, ibm_ok = s.read_done, s.ibm_read_ok
        s.read_done = s.ibm_read_ok = False
        if s.mode != "io":
            return 49
        if not f.seqacc:
            i = find(s.recs, f.key, keyof(f.key, self.area[f.idx]))
            if i is None:
                return 23
        else:
            if not self.last_read(s, done, ibm_ok):
                return 43
            i = s.cur
        s.recs.pop(i)
        if i < s.pos:
            s.pos -= 1
        s.cur = None
        return 0


def classify_seqwrite(m, g, k, last):
    """Class of an ACCESS SEQUENTIAL WRITE where the model (`m`) and GnuCOBOL (`g`) differ."""
    if g == 21 and m in (0, 22):
        return "G-lastkey" if last is not None and k < last else "G-dup21"
    if m == 21 and g in (0, 22):
        return "G-extend"
    return "G-other"


# ---------------------------------------------------------------- statements
class Stmt:
    def __init__(self, f, op, mode=None, key=None, keyname=False, into=False, src=False, rec=None,
                 setkey=None, nxt=False, exc=False, noexc=False, epilogue=False):
        self.f, self.op, self.mode, self.key, self.keyname = f, op, mode, key, keyname
        self.into, self.src, self.rec, self.setkey, self.nxt = into, src, rec, setkey, nxt
        self.exc, self.noexc, self.epilogue = exc, noexc, epilogue
        self.pos = self.slot = 0
        self.expect = self.why = None
        self.verb = 0          # index of the verb line in the program's line list
        self.line = 0          # its line number in the source

    def invalid_key(self, f):
        return self.op in ("write", "rewrite", "delete") or (self.op == "read" and self.key is not None)

    def cobol(self, f):
        """Statement lines and the offset of the verb line."""
        p, n = self.pos, f.name
        out = []
        if self.setkey is not None:
            fld = n + ("-K" if self.setkey[0] == 0 else "-A")
            out.append(f"MOVE '{self.setkey[1].decode()}' TO {fld}")
        if self.rec is not None:
            out.append(f"MOVE '{self.rec.decode()}' TO {n}-{'W' if self.src else 'R'}")
        verb = len(out)
        if self.op == "open":
            out.append(f"OPEN {MODEKW[self.mode]} {n}")
        elif self.op == "close":
            out.append(f"CLOSE {n}")
        else:
            if self.op == "read":
                v = f"READ {n}" + (" NEXT RECORD" if self.nxt else "") + (f" INTO {n}-I" if self.into else "")
                if self.key == 1:
                    v += f" KEY IS {n}-A"
                elif self.key == 0 and self.keyname:
                    v += f" KEY IS {n}-K"
            elif self.op in ("write", "rewrite"):
                v = f"{self.op.upper()} {n}-R" + (f" FROM {n}-W" if self.src else "")
            else:
                v = f"DELETE {n} RECORD"
            out.append(v)
            ik = self.invalid_key(f)
            if self.exc:
                out.append(f"    {'INVALID KEY' if ik else 'AT END'} MOVE 'E' TO TRC({p + 2}:1)")
            if self.noexc:
                out.append(f"    {'NOT INVALID KEY' if ik else 'NOT AT END'} MOVE 'N' TO TRC({p + 2}:1)")
            out.append("END-" + self.op.upper())
        out.append(f"MOVE {n}-S TO TRC({p}:2)" if f.fs else f"MOVE '--' TO TRC({p}:2)")
        if self.op == "read":
            out.append(f"MOVE {n}-R TO TRC({p + 3}:{f.reclen})")
            if self.into:
                out.append(f"MOVE {n}-I TO TRC({p + 3 + f.reclen}:{f.reclen})")
        return out, verb


def observe(f, t, o):
    """What the trace shows of an outcome."""
    rd = t.op == "read"
    return (o.status if f.fs else None, o.marker, o.abend,
            o.area if rd else None, o.into if rd and t.into else None)


# ---------------------------------------------------------------- generator
class Gen:
    def __init__(self, rng, name, exclude):
        self.rng, self.name, self.exclude = rng, name, exclude
        nf = rng.choice([1, 2, 2, 3, 3])
        self.specs = []
        for i in range(1, nf + 1):
            org = "indexed" if rng.random() < 0.6 else "sequential"
            access = rng.choice(["sequential", "random"]) if org == "indexed" else "sequential"
            alt = org == "indexed" and rng.random() < 0.5
            self.specs.append(FileSpec(i, org, access, alt, rng.random() < 0.85, name))
        self.spec = {f.idx: f for f in self.specs}
        self.msim, self.gsim = Sim(self.specs), Sim(self.specs, gnu=True)
        self.stmts = []
        # a few programs may end with a statement that abends (no FILE STATUS, no phrase)
        self.abend_ok = rng.random() < 0.08
        self.abends = False

    def rand_bytes(self, n):
        return "".join(self.rng.choice(ALNUM) for _ in range(n)).encode()

    def pick_key(self, s, f, existing_p):
        """A record key value: one in the file with probability `existing_p`."""
        ks = [keyof(f.key, r) for r in s.recs]
        if ks and self.rng.random() < existing_p:
            return self.rng.choice(ks)
        return self.rng.choice(KEYS)

    def make_rec(self, f, s, op):
        rng = self.rng
        if not f.indexed:
            return self.rand_bytes(6)
        if op == "write" and f.seqacc and s.recs and rng.random() < 0.7:
            mx = keyof(f.key, s.recs[-1])
            higher = [k for k in KEYS if k > mx]
            k = rng.choice(higher) if higher else rng.choice(KEYS)
        elif op == "write":
            k = self.pick_key(s, f, 0.3)
        elif f.seqacc and s.cur is not None and rng.random() < 0.85:
            k = keyof(f.key, s.recs[s.cur])
        else:
            k = self.pick_key(s, f, 0.75)
        a = b""
        if f.alt:
            if op == "rewrite" and s.cur is not None and f.seqacc and rng.random() < 0.5:
                a = keyof(f.altkey, s.recs[s.cur])
            else:
                a = rng.choice(ALTS)
        return k + a + self.rand_bytes(3)

    def phrases(self, f, t):
        rng = self.rng
        if t.op in ("open", "close") or (t.op in ("write", "rewrite") and not f.indexed) or \
                (t.op == "delete" and f.seqacc):
            # no AT END / INVALID KEY phrase in these statements (IBM: DELETE in sequential
            # access mode must not have INVALID KEY)
            return
        if f.fs:
            t.exc, t.noexc = rng.choices([(False, False), (True, False), (False, True), (True, True)],
                                         [3, 3, 1.5, 3])[0]
        else:
            t.exc, t.noexc = rng.random() < 0.85, rng.random() < 0.4

    def propose(self, f):
        rng = self.rng
        s = self.msim.st[f.idx]
        dl = 1 if f.indexed else 0
        w = {None: {"open": 8, "read": 1, "write": 1, "rewrite": 0.5, "delete": 0.5 * dl, "close": 1},
             "input": {"read": 8, "close": 2, "open": 1, "write": 1, "rewrite": 0.5, "delete": 0.5 * dl},
             "output": {"write": 8, "close": 2, "open": 1, "read": 1, "rewrite": 0.5, "delete": 0.5 * dl},
             "extend": {"write": 7, "close": 2, "open": 1, "read": 1, "rewrite": 0.5, "delete": 0.5 * dl},
             "io": {"read": 6, "rewrite": 4, "delete": 3 * dl, "write": 1.5, "close": 1, "open": 0.5}}[s.mode]
        op = rng.choices(list(w), list(w.values()))[0]
        if op == "open":
            if not s.exists:
                mode = "output"   # the program creates the file (cobolrun has no OPEN errors)
            else:
                mode = rng.choices(["input", "io", "extend", "output"], [3, 4, 2, 1])[0]
            t = Stmt(f.idx, "open", mode=mode)
        elif op == "close":
            t = Stmt(f.idx, "close")
        elif op == "read":
            if f.indexed and not f.seqacc:
                key = 1 if f.alt and rng.random() < 0.3 else 0
                if key == 0:
                    v = self.pick_key(s, f, 0.6)
                else:
                    alts = [keyof(f.altkey, r) for r in s.recs]
                    v = rng.choice(alts) if alts and rng.random() < 0.6 else rng.choice(ALTS)
                t = Stmt(f.idx, "read", key=key, keyname=rng.random() < 0.5, setkey=(key, v),
                         into=rng.random() < 0.25)
            else:
                t = Stmt(f.idx, "read", nxt=rng.random() < 0.3, into=rng.random() < 0.25)
        elif op in ("write", "rewrite"):
            t = Stmt(f.idx, op, rec=self.make_rec(f, s, op), src=rng.random() < 0.3)
        else:
            if not f.seqacc:
                t = Stmt(f.idx, "delete", setkey=(0, self.pick_key(s, f, 0.7)))
            else:
                t = Stmt(f.idx, "delete")
        self.phrases(f, t)
        return t

    def add(self, t, force=False):
        """Run `t` on both mirrors; keep it unless it is excluded or abends unplanned."""
        f = self.spec[t.f]
        m, g = self.msim.clone(), self.gsim.clone()
        mo, go = m.apply(t), g.apply(t)
        why = None
        if observe(f, t, mo) != observe(f, t, go):
            why = g.why or "G-other"
        if not force:
            if why in self.exclude:
                return False
            if mo.abend and not self.abend_ok:
                return False
        self.msim, self.gsim = m, g
        t.expect, t.why = (mo, go), why
        self.stmts.append(t)
        if mo.abend:
            self.abends = True
        return True

    def build(self):
        rng = self.rng
        for _ in range(rng.randint(10, 32)):
            for _ in range(30):
                if self.add(self.propose(rng.choice(self.specs))):
                    break
            if self.abends:
                return
        # epilogue: close every created file and read it back
        for f in self.specs:
            s = self.msim.st[f.idx]
            if not s.exists:
                continue
            if s.mode is not None:
                self.add(Stmt(f.idx, "close", epilogue=True), force=True)
            self.add(Stmt(f.idx, "open", mode="input", epilogue=True), force=True)
            if f.seqacc:
                for _ in range(len(self.msim.st[f.idx].recs) + 1):
                    self.add(Stmt(f.idx, "read", exc=True, epilogue=True), force=True)
            else:
                for k in KEYS:
                    self.add(Stmt(f.idx, "read", key=0, setkey=(0, k), exc=True, epilogue=True), force=True)
                for a in (ALTS if f.alt else []):
                    self.add(Stmt(f.idx, "read", key=1, setkey=(1, a), exc=True, epilogue=True), force=True)
            self.add(Stmt(f.idx, "close", epilogue=True), force=True)

    def render(self):
        pos = 1
        for t in self.stmts:
            f = self.spec[t.f]
            t.pos = pos
            t.slot = 3 + (f.reclen if t.op == "read" else 0) + (f.reclen if t.op == "read" and t.into else 0)
            pos += t.slot
        tlen = max(pos - 1, 1)
        L = ["IDENTIFICATION DIVISION.", f"PROGRAM-ID. {self.name}.", "ENVIRONMENT DIVISION.",
             "INPUT-OUTPUT SECTION.", "FILE-CONTROL."]
        for f in self.specs:
            sel = [f"    SELECT {f.name} ASSIGN TO '{f.phys}'",
                   f"        ORGANIZATION IS {'INDEXED' if f.indexed else 'SEQUENTIAL'}",
                   f"        ACCESS MODE IS {f.access.upper()}"]
            if f.indexed:
                sel.append(f"        RECORD KEY IS {f.name}-K")
            if f.alt:
                sel.append(f"        ALTERNATE RECORD KEY IS {f.name}-A")
            if f.fs:
                sel.append(f"        FILE STATUS IS {f.name}-S")
            sel[-1] += "."
            L += sel
        L += ["DATA DIVISION.", "FILE SECTION."]
        for f in self.specs:
            L += [f"FD  {f.name}.", f"01  {f.name}-R."] + [f"    05  {n} PIC X({k})." for n, k in f.fields]
        total = 8 + tlen + sum((2 if f.fs else 0) + 2 * f.reclen for f in self.specs)
        L += ["WORKING-STORAGE SECTION.", "01  R.", f"    05  SENT PIC X(8) VALUE '{SENT.decode()}'.",
              f"    05  TRC PIC X({tlen}) VALUE SPACES."]
        for f in self.specs:
            if f.fs:
                L.append(f"    05  {f.name}-S PIC XX VALUE SPACES.")
            L += [f"    05  {f.name}-I PIC X({f.reclen}) VALUE SPACES.",
                  f"    05  {f.name}-W PIC X({f.reclen}) VALUE SPACES."]
        L += ["01  RX REDEFINES R.", f"    05  BYTE PIC X OCCURS {total}.", "01  IDX PIC 9(4) COMP.",
              "PROCEDURE DIVISION.", "MAIN-PARA."]
        # the record areas start defined (the model's storage starts as zeros)
        L += [f"    MOVE SPACES TO {f.name}-R" for f in self.specs]
        for j, t in enumerate(self.stmts):
            lines, v = t.cobol(self.spec[t.f])
            t.verb = len(L) + v
            L += ["    " + ln for ln in lines]
            # the statement's trace slot, also shown at once: compared line by line, so the
            # statements before an abend are compared too (the final dump is lost there)
            L.append(f"    DISPLAY '@{j:03d} ' TRC({t.pos}:{t.slot})")
        L += [f"    PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > {total}",
              "       DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING",
              "    END-PERFORM", "    DISPLAY ' '", "    STOP RUN."]
        out, lineno = [], 1
        starts = []
        for ln in L:
            starts.append(lineno)
            w = D.wrap_fixed(ln)
            out.append(w)
            lineno += w.count("\n") + 1
        for t in self.stmts:
            t.line = starts[t.verb]
        return "\n".join(out) + "\n", total


# ---------------------------------------------------------------- running and comparing
ERR_RE = re.compile(r"libcob: (\S+):(\d+): error: .*\(status = (\d+)\) for file (\S+)")


def slot_view(f, t, bs):
    """Readable contents of statement `t`'s slot."""
    v = {"status": bytes(bs[0:2]).decode(errors="replace"), "marker": chr(bs[2])}
    if t.op == "read":
        v["area"] = bytes(bs[3:3 + f.reclen]).decode(errors="replace")
        if t.into:
            v["into"] = bytes(bs[3 + f.reclen:3 + 2 * f.reclen]).decode(errors="replace")
    return v


def predicted_view(f, t, o):
    """Slot contents predicted by a mirror outcome (None if unpredictable)."""
    if o.status == UNKNOWN:
        return None
    v = {"status": f"{o.status:02d}" if f.fs else "--", "marker": o.marker}
    if t.op == "read":
        v["area"] = o.area.decode()
        if t.into:
            v["into"] = o.into.decode()
    return v


def first_tag(gen, upto):
    """Class of the first statement (index <= upto) where the mirrors disagree."""
    for t in gen.stmts[:upto + 1]:
        if t.why:
            return t.why
    return None


def history(gen, j):
    """Statements on the file of statement j, up to j: source line, statement, status and
    phrase marker of the model mirror and of the GnuCOBOL mirror."""
    fj = gen.stmts[j].f
    out = []
    for i, t in enumerate(gen.stmts[:j + 1]):
        if t.f != fj:
            continue
        lines, _ = t.cobol(gen.spec[t.f])
        text = " / ".join(x.strip() for x in lines
                          if not (x.startswith("MOVE") and " TO TRC(" in x) and not x.startswith("END-"))
        mo, go = t.expect
        out.append(f"#{i} L{t.line}: {text}  [model {mo.status:02d}{mo.marker.strip()}"
                   f" gnu {go.status:02d}{go.marker.strip()}]")
    return out


def detail(gen, j, gslot=None, lslot=None, extra=None):
    t = gen.stmts[j]
    f = gen.spec[t.f]
    d = {"files": [x.describe() for x in gen.specs], "statement": j, "line": t.line,
         "cobol": [x.strip() for x in t.cobol(f)[0]]}
    if gslot is not None:
        d["gnucobol"] = gslot
        d["lean"] = lslot
    mo, go = t.expect
    d["mirror"] = {"model": f"{mo.status:02d}{mo.marker.strip()}", "gnucobol": f"{go.status:02d}{go.marker.strip()}"}
    d["file history"] = history(gen, j)
    if extra:
        d.update(extra)
    return d


def data_files(outdir, name):
    """Every data file a program `name` can create (BDB keeps an alternate key in NAME.1)."""
    return [os.path.join(outdir, f"{name}_{i}.dat{e}") for i in (1, 2, 3) for e in ("", ".1")]


def cleanup(outdir, name, keep):
    if keep:
        return
    base = os.path.join(outdir, name)
    for p in [base + e for e in ("", ".cob", ".fe.json", ".c", ".c.h", ".c.l.h")] + \
            data_files(outdir, name):
        if os.path.exists(p):
            os.remove(p)


def run_one(idx, rng, outdir, keep, exclude):
    name = f"F{idx:05d}"
    gen = Gen(rng, name, exclude)
    gen.build()
    cobol, total = gen.render()
    base = os.path.join(outdir, name)
    with open(base + ".cob", "w") as fh:
        fh.write(cobol)
    for p in data_files(outdir, name):
        if os.path.exists(p):
            os.remove(p)
    res = compare(gen, base, outdir, total)
    if res[0] in ("ok", "ok-abend"):
        cleanup(outdir, name, keep)
    return res


def compare(gen, base, outdir, total):
    c = subprocess.run([D.COBC, "-x", "-std=ibm", "-fsource-location", "-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return ("cobc-error", c.stderr[:2000])
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    try:
        r = subprocess.run([base], capture_output=True, text=True, env=env, timeout=20, cwd=outdir)
    except subprocess.TimeoutExpired:
        return ("gnucobol-timeout", None)
    fe = subprocess.run([sys.executable, "-I", D.COBOLFE, base + ".cob", "--profile", "gnucobol",
                         "--main", "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0:
        return ("frontend-error", fe.stderr[:2000])
    unsup = [ln for ln in fe.stderr.splitlines() if "unsupported" in ln]
    if any("DISPLAY" not in ln for ln in unsup):
        return ("frontend-unsupported", "\n".join(unsup)[:2000])
    lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True, timeout=60)
    if lr.returncode != 0:
        return ("cobolrun-error", lr.stderr[:2000])
    res = json.loads(lr.stdout)
    sig, mem = res["signal"], res["mem"]
    try:
        off = bytes(mem).index(SENT)
    except ValueError:
        return ("lean-layout", "sentinel not found in storage")
    lb = mem[off:off + total]
    lean_io = re.match(r"fault:Cobol\.Fault\.io (\d+)", sig)
    lean_done = "unsupported" in sig and "DISPLAY" in sig
    # the trace lines ('@nnn ' and the statement's slot), one per completed statement
    g_lines = r.stdout.splitlines()
    g_trace = [ln for ln in g_lines if ln.startswith("@")]
    g_dump = " ".join(ln for ln in g_lines if not ln.startswith("@"))
    l_trace = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]

    def trace_diff():
        """None when both sides show the same trace lines, else the first difference."""
        if g_trace == l_trace:
            return None
        n = min(len(g_trace), len(l_trace))
        k = next((i for i in range(n) if g_trace[i] != l_trace[i]), n)
        return {"trace line": k, "gnucobol": g_trace[k] if k < len(g_trace) else None,
                "lean": l_trace[k] if k < len(l_trace) else None,
                "lines": [len(g_trace), len(l_trace)]}

    def stmt_at(i):
        """Statement whose trace slot holds R byte i."""
        for j, t in enumerate(gen.stmts):
            if 8 + t.pos - 1 <= i < 8 + t.pos - 1 + t.slot:
                return j
        return None

    def lean_stop():
        """First statement whose slot was not written: where the IR run faulted."""
        for j, t in enumerate(gen.stmts):
            if lb[8 + t.pos - 1] == 0x20:
                return j
        return None

    def tagged(kind, j):
        tag = first_tag(gen, j if j is not None else len(gen.stmts) - 1)
        return f"{kind}:{tag}" if tag else kind

    if r.returncode == 0:
        try:
            g = [int(x) - 1 for x in g_dump.split()]
        except ValueError:
            return ("gnucobol-output", r.stdout[:500])
        if len(g) != total:
            return ("gnucobol-output", r.stdout[:500])
        if lean_io:
            j = lean_stop()
            return (tagged("lean-abend", j), detail(gen, j, extra={"lean signal": sig}) if j is not None else sig)
        if not lean_done:
            return ("lean-signal", sig)
        if g == lb:
            td = trace_diff()
            if td is not None:
                return (tagged("mismatch-trace", None), td)
            tag = first_tag(gen, len(gen.stmts) - 1)
            return ("ok", None) if not tag else (f"ok-predicted:{tag}", None)
        i = next(k for k in range(total) if g[k] != lb[k])
        j = stmt_at(i)
        if j is None:
            return (tagged("mismatch-tail", None), {"byte": i, "gnucobol": g[i:i + 12], "lean": lb[i:i + 12]})
        t = gen.stmts[j]
        f = gen.spec[t.f]
        a = 8 + t.pos - 1
        gv, lv = slot_view(f, t, g[a:a + t.slot]), slot_view(f, t, lb[a:a + t.slot])
        kind = tagged("mismatch", j)
        if t.why:
            # the class is confirmed when both sides show what the two mirrors predict
            mo, go = t.expect
            pg, pm = predicted_view(f, t, go), predicted_view(f, t, mo)
            if pm != lv or (pg is not None and pg != gv):
                kind += "/unconfirmed"
        return (kind, detail(gen, j, gv, lv))
    m = ERR_RE.search(r.stderr)
    if not m:
        return (tagged("gnucobol-abend", None), (r.stdout[-300:] + r.stderr[-700:]))
    gline, gcode, gfile = int(m.group(2)), int(m.group(3)), m.group(4)
    jg = next((j for j, t in enumerate(gen.stmts) if t.line == gline), None)
    if jg is None:
        return (tagged("gnucobol-abend", None), r.stderr[-700:])
    if not lean_io:
        return (tagged("gnucobol-abend-only", jg),
                detail(gen, jg, extra={"gnucobol": m.group(0), "lean signal": sig}))
    jl = lean_stop()
    if jl == jg and int(lean_io.group(1)) == gcode and gfile == gen.spec[gen.stmts[jg].f].name:
        # same statement, same status: the statements before it must have shown the same
        td = trace_diff()
        if td is not None:
            return (tagged("abend-trace-mismatch", jg), td)
        return ("ok-abend", None)
    return (tagged("abend-mismatch", min(x for x in (jl, jg) if x is not None)),
            detail(gen, jg, extra={"gnucobol": m.group(0), "lean signal": sig, "lean stop": jl}))


def run_program(path, outdir, keep):
    """`--run`: run a COBOL program (e.g. tools/difftest/filetest_cases/*.cob) with GnuCOBOL and
    through the front end + cobolrun, in `outdir`; print both DISPLAY outputs side by side."""
    with open(path, encoding="latin-1") as fh:
        src = fh.read()
    name = "run_" + os.path.splitext(os.path.basename(path))[0]
    base = os.path.join(outdir, name)
    data = []
    for a in re.findall(r"ASSIGN\s+TO\s+'([^']+)'", src, re.I):
        if os.path.basename(a) != a:
            raise SystemExit(f"{path}: ASSIGN TO '{a}' must be a plain file name")
        data += [os.path.join(outdir, a + e) for e in ("", ".1")]
    for p in data:
        if os.path.exists(p):
            os.remove(p)
    c = subprocess.run([D.COBC, "-x", "-std=ibm", "-fsource-location", "-o", base, path],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        print(c.stderr)
        return 1
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    r = subprocess.run([base], capture_output=True, text=True, env=env, timeout=20, cwd=outdir)
    fe = subprocess.run([sys.executable, "-I", D.COBOLFE, path, "--profile", "gnucobol", "--main",
                         "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0:
        print(fe.stderr)
        return 1
    lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True, timeout=60)
    if lr.returncode != 0:
        print(lr.stderr)
        return 1
    res = json.loads(lr.stdout)
    g = r.stdout.splitlines()
    m = [bytes(e["display"]).decode(errors="replace") for e in res["out"] if "display" in e]
    print(f"== {path}")
    print(f"   {'GnuCOBOL (rc ' + str(r.returncode) + ')':<40} | model via front end ({res['signal']})")
    for i in range(max(len(g), len(m))):
        a, b = (g[i] if i < len(g) else ""), (m[i] if i < len(m) else "")
        print(("   " if a == b else "!! ") + f"{a:<40} | {b}")
    for ln in r.stderr.splitlines():
        if "error" in ln or "BDB" in ln:
            print("   gnucobol stderr: " + ln)
    if not keep:
        for p in data + [base, base + ".fe.json"]:
            if os.path.exists(p):
                os.remove(p)
    return 0


def bump(tally, out, case, status):
    """Count one case and append it to OUT/results.jsonl (one JSON object per case)."""
    tally[status] = tally.get(status, 0) + 1
    with open(os.path.join(out, "results.jsonl"), "a") as fh:
        fh.write(json.dumps({"case": case, "status": status}) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=50)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=os.path.join(D.ROOT, "tools", "difftest", "out_file"))
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--exclude", default="gnucobol",
                    help="deviation classes not generated: comma list of class names, groups "
                         "(gnucobol, model, frontend), all or none (default: gnucobol)")
    ap.add_argument("--show", type=int, default=15, help="failures shown in detail")
    ap.add_argument("--run", nargs="+", metavar="PROG.cob",
                    help="run these COBOL programs on both sides instead (DISPLAY output side by side)")
    args = ap.parse_args()
    exclude = parse_exclude(args.exclude)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    if args.run:
        return max(run_program(p, args.out, args.keep) for p in args.run)
    rng = random.Random(args.seed)
    tally, fails = {}, []
    for i in range(args.n):
        st, det = run_one(i, random.Random(rng.random()), args.out, args.keep, exclude)
        bump(tally, args.out, i, st)
        if st not in ("ok", "ok-abend"):
            fails.append((i, st, det))
    print(json.dumps({"tally": dict(sorted(tally.items())), "exclude": sorted(exclude)}))
    for i, st, det in fails[:args.show]:
        print(f"--- F{i:05d} {st}")
        print(json.dumps(det, indent=1)[:3000] if not isinstance(det, str) else det[:2000])
    unexplained = [x for x in fails if ":" not in x[1]]
    return 0 if not unexplained else 1


if __name__ == "__main__":
    sys.exit(main())

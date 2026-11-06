#!/usr/bin/env python3
"""Differential testing of alternate record keys and SAME RECORD AREA: START by an alternate key
(or a leading part of one), READ NEXT in an alternate key's order, keyed READ by an alternate key,
alternate keys WITH DUPLICATES (the order of placement, status 02), WRITE / REWRITE / DELETE under
an alternate key of reference.

Each random program declares two or three indexed files, each with a FILE STATUS item:
  F1  ACCESS DYNAMIC, RECORD KEY K1, ALTERNATE RECORD KEY A1 (unique) and / or A2 WITH DUPLICATES
      (A2 = A2P A2R, so that START can name its leading part A2P);
  F2  ACCESS SEQUENTIAL, RECORD KEY K2 and ALTERNATE RECORD KEY B2 WITH DUPLICATES (B2P B2R), or a
      unique B1 (then no REWRITE: G-rwalt), or no alternate key;
  F3  (most programs) ACCESS RANDOM, RECORD KEY K3, ALTERNATE RECORD KEY C2 WITH DUPLICATES and /
      or a unique C1.
Some programs name F2 and F3 in SAME RECORD AREA (records of 10 and 11 bytes). A setup program
(GnuCOBOL) first creates the files with 0-7 records each, written in ascending record-key order;
the model gets them with --inputs (records in the file before the run come first among
duplicates, in record-key order, as GnuCOBOL's are after that setup). The program then opens the
files I-O and runs 15-35 random I/O statements:
  F1: START KEY = / > / >= / NOT < on K1, A1, A2 or A2P (value in the file or not), READ NEXT,
      READ KEY IS K1 / A1 / A2 (and READ without KEY), WRITE (record key new or in use; A1 maybe in
      use; A2 often a duplicate), REWRITE of a record key in the file (A1, A2, data changed or
      kept), DELETE (record key in the file or not);
  F2: START on K2, B2, B2P or B1, READ NEXT, REWRITE of the record read (record key kept, B2 and
      data changed or kept), DELETE of the record read, WRITE (48: open I-O, ACCESS SEQUENTIAL);
  F3: READ KEY IS K3 / C1 / C2, WRITE, REWRITE of a record key in the file, DELETE;
with and without INVALID KEY / AT END phrases (the phrase that ran is displayed). After every
statement the program displays a trace line: its number, every FILE STATUS and every record
area. An epilogue closes the files, opens them INPUT and reads F1 and F2 in the order of each of
their keys (START NOT < LOW-VALUES, then as many READ NEXT as there are records, and one more),
and F3 by every record key and every value of its alternate keys; this shows the final order of
the duplicates.

GnuCOBOL (-std=ibm) runs the setup and the program in a fresh directory; the front end
(tools/cobolfe, --profile gnucobol) extracts the program and cobolrun runs it with the setup's
records as --inputs. `Mirror` predicts every file status from IBM's rules (Enterprise COBOL 6.4:
the key of reference, the file position indicator as a place in the key's order, duplicates in
the order they were placed, status 02 for a READ whose next record in the key of reference has the
same value of the key and for a WRITE / REWRITE that created a duplicate value). A program passes
("ok") when the model's DISPLAY lines equal GnuCOBOL's, once every status 02 that the mirror
predicts is read as 00 (GnuCOBOL never gives 02: G-dup02), and the model's status on every trace
line equals the mirror's (02 included). Other statuses: "mismatch" (lines differ), "status-mismatch"
(the model's status differs from the mirror's), "gnucobol-02", "lean-signal", "frontend-error",
"frontend-unsupported", "cobc-error", "setup-error", "gnucobol-abend", "gnucobol-timeout",
"lean-timeout", "cobolrun-error".

GnuCOBOL 3.2 deviations from IBM, kept out of generation or read as above:
  G-dup02  GnuCOBOL (BDB) never gives status 02 (probe1 p1, p2): a WRITE / REWRITE that creates a
           duplicate alternate key value, and a READ followed by a record with the same value of
           the key of reference, give 00.
  G-rwalt  ACCESS SEQUENTIAL REWRITE of a file with a unique alternate key fails with 22
           (BDB0631) and drops the record's alternate-index entry (probe1 p4; filetest.py): F2
           with a unique alternate key gets no REWRITE.
  G-rw21   REWRITE of a record key not in the file gives 21 (IBM 23): REWRITE only of record keys
           in the file (ACCESS DYNAMIC / RANDOM).
  G-readfail  READ NEXT after a failed keyed READ: GnuCOBOL continues from where it was, or repeats
           records, or skips one, or gives 46 (probe1 p6); IBM: 46 ("The preceding READ statement was
           unsuccessful but did not cause an at-end condition"), as the model: no READ NEXT of F1
           after a failed keyed READ until a START, a successful keyed READ or an OPEN.
A READ NEXT after a failed START is generated (46 on both sides). Kept out as well: a WRITE in
ACCESS SEQUENTIAL OUTPUT mode (filetest.py's G-dup21 / G-extend / G-lastkey: the setup writes in
ascending order) and a failed OPEN (G-open41).

Hand cases (tools/difftest/alt_cases, --run; GnuCOBOL vs model, a status 02 that ends a model line
read as 00): v_altkey1.cob (dynamic access, a unique and a duplicates alternate key: WRITE, START =,
>, NOT < on both and on a leading part, READ KEY IS the duplicates key, READ by the record key,
WRITE / DELETE / REWRITE while reading by the alternate key, a failed START), v_altkey2.cob (failed
START and keyed READ followed by READ NEXT, START > among duplicates, REWRITE keeping and changing a
duplicates key, DELETE + WRITE of one record key, CLOSE + OPEN, and an ACCESS SEQUENTIAL file read by
its duplicates key with REWRITE and DELETE of the record read), v_altkey_seq.cob (ACCESS SEQUENTIAL:
REWRITE that moves the record read within the duplicates, START by the record key), v_same_record.cob
(SAME RECORD AREA shares the area, SAME AREA does not: indexed and sequential files) agree; the
reproducers g_rwalt_alt.cob (G-rwalt) and g_readfail.cob (G-readfail) differ as documented.

usage: alttest.py [--n N] [--seed S] [--out DIR] [--root TREE] [--show K]
       alttest.py --run PROG.cob... [--out DIR] [--root TREE]
  --root: the coblean tree whose front end and cobolrun are tested (default: this script's)
"""
import argparse
import json
import os
import random
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OPS = ["=", ">", ">=", "NOT <"]
DUPV = ["Ax", "Ay", "Bx", "Cx"]           # values of a duplicates key (leading parts A, B, C)
UNIQV = ["u%d" % i for i in range(1, 9)]  # values of a unique alternate key


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


class Spec:
    """A file: name, access, record layout (fields in order) and keys."""

    def __init__(self, i, access, kpref, alts, dlen):
        self.i, self.access = i, access
        self.name = f"F{i}"
        n = {1: "A", 2: "B", 3: "C"}[i]
        self.kname, self.uname, self.dname = f"K{i}", f"{n}1", f"{n}2"
        self.pname, self.rname, self.data = f"{n}2P", f"{n}2R", f"D{i}"
        self.kvals = [f"{kpref}{j:02d}" for j in range(1, 10)]
        self.dlen = dlen
        # alternate keys in declaration order: (field name, offset, length, dups)
        self.alts = []
        if "u" in alts:
            self.alts.append((self.uname, 3, 2, False))
        if "d" in alts:
            self.alts.append((self.dname, 5, 2, True))
        self.reclen = 7 + dlen

    def alt(self, field):
        for j, a in enumerate(self.alts):
            if a[0] == field:
                return j, a
        return None


class Mirror:
    """IBM's rules for one indexed file, as far as the generated statements use them."""

    def __init__(self, spec, recs):
        self.s = spec
        self.recs = {r[:3]: r for r in recs}     # record key -> record (strings)
        self.stamps = {}                          # (alternate key index, record key) -> placement
        self.nstamp = 0
        self.mode = None
        self.kor = 0                              # 0 = record key, j + 1 = alternate key j
        self.bound = None                         # file position indicator: (place, incl) or None
        self.eof = False
        self.cur = None                           # record key of the last successful READ
        self.fs = "00"                            # the FILE STATUS item (its VALUE)
        self.readfail = False                     # a keyed READ failed since the last START / OPEN /
        #                                           successful keyed READ (G-readfail)

    # places in a key's order
    def val(self, j, r):
        _, off, ln, _ = self.s.alts[j]
        return r[off:off + ln]

    def place(self, kor, r):
        if kor == 0:
            return (r[:3],)
        j = kor - 1
        dups = self.s.alts[j][3]
        st = self.stamps.get((j, r[:3])) if dups else None
        return (self.val(j, r), (0,) if st is None else (1, st), r[:3])

    def ordered(self, kor):
        return sorted(self.recs.values(), key=lambda r: self.place(kor, r))

    def dupnext(self, kor, r):
        """02: the next record in the key of reference has the same value of the key."""
        if kor == 0 or not self.s.alts[kor - 1][3]:
            return "00"
        p = self.place(kor, r)
        same = any(self.val(kor - 1, x) == self.val(kor - 1, r) and self.place(kor, x) > p
                   for x in self.recs.values())
        return "02" if same else "00"

    def set(self, code):
        self.fs = code
        return code

    # statements
    def open(self, mode):
        self.mode, self.kor, self.eof, self.cur, self.readfail = mode, 0, False, None, False
        if mode == "output":
            self.recs, self.stamps = {}, {}
        ks = sorted(self.recs)
        self.bound = ((ks[0],), True) if ks else None
        return self.set("00")

    def close(self):
        self.mode, self.cur = None, None
        return self.set("00")

    def start(self, op, kor, ln, v):
        self.cur, self.readfail = None, False
        if self.mode not in ("input", "io"):
            return self.set("47")
        for r in self.ordered(kor):
            k = r[:3] if kor == 0 else self.val(kor - 1, r)
            k = k[:ln]
            ok = k == v if op == "=" else (k > v if op == ">" else k >= v)
            if ok:
                self.kor, self.bound, self.eof = kor, (self.place(kor, r), True), False
                return self.set("00")
        self.kor, self.eof = kor, True
        return self.set("23")

    def read_next(self):
        if self.mode not in ("input", "io"):
            self.cur = None
            return self.set("47")
        if self.eof:
            self.cur = None
            return self.set("46")
        for r in self.ordered(self.kor):
            p = self.place(self.kor, r)
            if self.bound is None or (p >= self.bound[0] if self.bound[1] else p > self.bound[0]):
                self.bound, self.cur = (p, False), r[:3]
                return self.set(self.dupnext(self.kor, r))
        self.eof, self.cur = True, None
        return self.set("10")

    def read_key(self, kor, v):
        self.cur = None
        if self.mode not in ("input", "io"):
            return self.set("47")
        for r in self.ordered(kor):
            if (r[:3] if kor == 0 else self.val(kor - 1, r)) == v:
                self.kor, self.bound, self.eof, self.cur = kor, (self.place(kor, r), False), False, r[:3]
                self.readfail = False
                return self.set(self.dupnext(kor, r))
        # a failed keyed READ: the key of reference is set, READ NEXT gives 46
        self.kor, self.eof, self.readfail = kor, True, True
        return self.set("23")

    def made_dup(self, r, skip, changed):
        for j, (_, _, _, dups) in enumerate(self.s.alts):
            if dups and changed(j) and any(k != skip and self.val(j, x) == self.val(j, r)
                                           for k, x in self.recs.items()):
                return True
        return False

    def unique_clash(self, r, skip):
        return any(not dups and any(k != skip and self.val(j, x) == self.val(j, r) for k, x in self.recs.items())
                   for j, (_, _, _, dups) in enumerate(self.s.alts))

    def stamp(self, r, changed):
        for j, (_, _, _, dups) in enumerate(self.s.alts):
            if dups and changed(j):
                self.stamps[(j, r[:3])] = self.nstamp
        self.nstamp += 1

    def write(self, r):
        self.cur = None
        ok = ("output", "extend") if self.s.access == "sequential" else ("output", "io")
        if self.mode not in ok:
            return self.set("48")
        if r[:3] in self.recs or self.unique_clash(r, None):
            return self.set("22")
        code = "02" if self.made_dup(r, None, lambda j: True) else "00"
        self.recs[r[:3]] = r
        self.stamp(r, lambda j: True)
        return self.set(code)

    def rewrite(self, r):
        cur, self.cur = self.cur, None
        if self.mode != "io":
            return self.set("49")
        if self.s.access == "sequential":
            if cur is None:
                return self.set("43")
            assert cur == r[:3]
        elif r[:3] not in self.recs:
            return self.set("23")
        old = self.recs[r[:3]]
        if self.unique_clash(r, r[:3]):
            return self.set("22")
        changed = lambda j: self.val(j, old) != self.val(j, r)  # noqa: E731
        code = "02" if self.made_dup(r, r[:3], changed) else "00"
        self.recs[r[:3]] = r
        self.stamp(r, changed)
        return self.set(code)

    def delete(self, k):
        cur, self.cur = self.cur, None
        if self.mode != "io":
            return self.set("49")
        if self.s.access == "sequential":
            if cur is None:
                return self.set("43")
            k = cur
        elif k not in self.recs:
            return self.set("23")
        del self.recs[k]
        self.stamps = {jk: n for jk, n in self.stamps.items() if jk[1] != k}
        return self.set("00")


class Gen:
    def __init__(self, rng, name):
        self.rng, self.name = rng, name
        r = rng.random
        f1 = rng.choice(["ud", "ud", "d", "u"])
        f2 = rng.choice(["d", "d", "u", ""])
        f3 = rng.choice(["ud", "d", "u", None]) if r() < 0.85 else None
        self.specs = [Spec(1, "dynamic", "K", f1, 3), Spec(2, "sequential", "S", f2, 3)]
        if f3 is not None:
            self.specs.append(Spec(3, "random", "R", f3, 4))
        self.same = len(self.specs) == 3 and r() < 0.4
        self.init = {}
        for s in self.specs:
            ks = sorted(rng.sample(s.kvals, rng.randint(0, 7)))
            us = rng.sample(UNIQV, len(ks))
            self.init[s.i] = [k + u + rng.choice(DUPV) + self.data(s) for k, u in zip(ks, us)]
        self.m = {s.i: Mirror(s, self.init[s.i]) for s in self.specs}
        self.lines = []
        self.traces = []      # per trace line: the statuses the mirror predicts (one per file)
        self.cnt = {}         # "statement key status" -> count (random part)
        self.n = 0

    def count(self, what, m):
        k = f"{what} {m.fs}"
        self.cnt[k] = self.cnt.get(k, 0) + 1

    @staticmethod
    def kind(s, kor):
        """The key of reference `kor` of file `s`: prime, unique or dups."""
        return "prime" if kor == 0 else ("dups" if s.alts[kor - 1][3] else "unique")

    def data(self, s):
        return "".join(self.rng.choice("pqrstvw") for _ in range(s.dlen))

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

    def header(self, name, same):
        out = ["       IDENTIFICATION DIVISION.", f"       PROGRAM-ID. {name}.",
               "       ENVIRONMENT DIVISION.", "       INPUT-OUTPUT SECTION.", "       FILE-CONTROL."]
        for s in self.specs:
            out += self.select(s)
        if same:
            out += ["       I-O-CONTROL.", "           SAME RECORD AREA FOR F2 F3."]
        out += ["       DATA DIVISION.", "       FILE SECTION."]
        for s in self.specs:
            out += self.fd(s)
        out += ["       WORKING-STORAGE SECTION."]
        for s in self.specs:
            out.append(f'       01 FS{s.i} PIC XX VALUE "00".')
        out += ["       PROCEDURE DIVISION.", "       MAIN."]
        return out

    def render_setup(self):
        out = self.header(self.name + "S", False)
        for s in self.specs:
            out.append(f"           OPEN OUTPUT {s.name}")
            for r in self.init[s.i]:
                out.append(f'           MOVE "{r}" TO REC{s.i}')
                out.append(f"           WRITE REC{s.i}")
            out.append(f"           CLOSE {s.name}")
            out.append(f'           IF FS{s.i} NOT = "00" DISPLAY "SETUP {s.i} " FS{s.i} END-IF')
        out.append("           STOP RUN.")
        return "\n".join(out) + "\n"

    def trace(self):
        self.n += 1
        fs = ' " " '.join(f"FS{s.i}" for s in self.specs)
        recs = ' "|" '.join(f"REC{s.i}" for s in self.specs)
        self.lines += wrap(f'DISPLAY "T{self.n:03d} " {fs} " " {recs} "|"')
        self.traces.append([self.m[s.i].fs for s in self.specs])

    def emit(self, text, phrase=None):
        """A statement, with its phrases (`phrase`: "INVALID KEY" / "AT END") half of the time."""
        if phrase is not None and self.rng.random() < 0.5:
            neg = "NOT " + phrase
            text += f' {phrase} DISPLAY "P{self.n + 1:03d} E" {neg} DISPLAY "P{self.n + 1:03d} N"'
            text += " END-" + text.split()[0]
        self.lines += wrap(text)

    # ---------------------------------------------------------------- statements
    def key_value(self, s, m, field):
        rng = self.rng
        if field == s.kname:
            pool = sorted(m.recs) if m.recs and rng.random() < 0.7 else s.kvals
            return rng.choice(pool), 0, 3
        if field == s.pname:
            j, _ = s.alt(s.dname)
            vals = sorted({m.val(j, r)[:1] for r in m.recs.values()})
            return rng.choice(vals if vals and rng.random() < 0.7 else ["A", "B", "C", "D"]), j + 1, 1
        j, (_, _, ln, dups) = s.alt(field)
        vals = sorted({m.val(j, r) for r in m.recs.values()})
        pool = DUPV + ["Dx"] if dups else UNIQV + ["u9"]
        return rng.choice(vals if vals and rng.random() < 0.8 else pool), j + 1, ln

    def stmt_start(self, s, m):
        fields = [s.kname] + [a[0] for a in s.alts] + ([s.pname] if s.alt(s.dname) else [])
        field = self.rng.choice(fields)
        v, kor, ln = self.key_value(s, m, field)
        op = self.rng.choice(OPS)
        self.lines.append(f'           MOVE "{v}" TO {field}')
        self.emit(f"START {s.name} KEY IS {op} {field}", "INVALID KEY")
        m.start(">=" if op == "NOT <" else op, kor, ln, v)
        self.count(f"START {self.kind(s, kor)}{'-part' if field == s.pname else ''}", m)

    def stmt_read_next(self, s, m):
        self.emit(f"READ {s.name} NEXT RECORD", "AT END")
        k = self.kind(s, m.kor)
        m.read_next()
        self.count(f"READ-NEXT {k}", m)

    def stmt_read_key(self, s, m):
        fields = [s.kname] + [a[0] for a in s.alts]
        field = self.rng.choice(fields)
        v, kor, _ = self.key_value(s, m, field)
        self.lines.append(f'           MOVE "{v}" TO {field}')
        if field == s.kname and self.rng.random() < 0.3:
            self.emit(f"READ {s.name}", "INVALID KEY")
        else:
            self.emit(f"READ {s.name} KEY IS {field}", "INVALID KEY")
        m.read_key(kor, v)
        self.count(f"READ-KEY {self.kind(s, kor)}", m)

    def new_record(self, s, m, k, old=None):
        rng = self.rng
        uv = old[3:5] if old is not None and rng.random() < 0.5 else None
        if uv is None:
            used = sorted({r[3:5] for r in m.recs.values()})
            uv = rng.choice(used) if used and rng.random() < 0.2 else rng.choice(UNIQV)
        dv = old[5:7] if old is not None and rng.random() < 0.4 else rng.choice(DUPV)
        return k + uv + dv + self.data(s)

    def stmt_write(self, s, m):
        k = self.rng.choice(sorted(m.recs)) if m.recs and self.rng.random() < 0.2 else self.rng.choice(s.kvals)
        r = self.new_record(s, m, k)
        self.lines.append(f'           MOVE "{r}" TO REC{s.i}')
        self.emit(f"WRITE REC{s.i}", "INVALID KEY" if s.access != "sequential" else None)
        m.write(r)
        self.count("WRITE", m)

    def stmt_rewrite(self, s, m):
        if s.access == "sequential":
            if m.cur is None and self.rng.random() < 0.7:
                return False
            k = m.cur if m.cur is not None else self.rng.choice(s.kvals)
            old = m.recs.get(k)
            r = self.new_record(s, m, k, old) if old is not None else k + "u1Ax" + self.data(s)
            if m.cur is None:
                # 43: no record read; the model and GnuCOBOL check that before the record key
                pass
        else:
            if not m.recs:
                return False
            k = self.rng.choice(sorted(m.recs))
            r = self.new_record(s, m, k, m.recs[k])
        self.lines.append(f'           MOVE "{r}" TO REC{s.i}')
        self.emit(f"REWRITE REC{s.i}", "INVALID KEY" if s.access != "sequential" else None)
        m.rewrite(r)
        self.count(f"REWRITE {s.access}", m)
        return True

    def stmt_delete(self, s, m):
        if s.access == "sequential":
            if m.cur is None and self.rng.random() < 0.7:
                return False
            self.lines.append(f"           DELETE {s.name} RECORD")
            m.delete(None)
            self.count(f"DELETE {s.access}", m)
            return True
        k = self.rng.choice(sorted(m.recs)) if m.recs and self.rng.random() < 0.8 else self.rng.choice(s.kvals)
        self.lines.append(f'           MOVE "{k}" TO {s.kname}')
        self.emit(f"DELETE {s.name} RECORD", "INVALID KEY")
        m.delete(k)
        self.count(f"DELETE {s.access}", m)
        return True

    def step(self):
        rng = self.rng
        s = rng.choice(self.specs + [self.specs[0]])
        m = self.m[s.i]
        x = rng.random()
        if s.access == "random":
            done = (self.stmt_read_key(s, m) or True) if x < 0.4 else \
                (self.stmt_write(s, m) or True) if x < 0.65 else \
                self.stmt_rewrite(s, m) if x < 0.85 else self.stmt_delete(s, m)
        elif s.access == "sequential":
            if x < 0.25:
                self.stmt_start(s, m)
                done = True
            elif x < 0.6:
                self.stmt_read_next(s, m)
                done = True
            elif x < 0.8:
                # no REWRITE of a file with a unique alternate key (G-rwalt)
                done = all(d for _, _, _, d in s.alts) and self.stmt_rewrite(s, m)
            elif x < 0.95:
                done = self.stmt_delete(s, m)
            else:
                self.stmt_write(s, m)
                done = True
        else:
            if x < 0.2 or (x < 0.45 and m.readfail):
                self.stmt_start(s, m)
            elif x < 0.45:
                self.stmt_read_next(s, m)
            elif x < 0.6:
                self.stmt_read_key(s, m)
            elif x < 0.75:
                self.stmt_write(s, m)
            elif x < 0.88:
                self.stmt_rewrite(s, m)
            else:
                self.stmt_delete(s, m)
            done = True
        if done:
            self.trace()

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
            if s.access == "random":
                for k in sorted(m.recs):
                    self.lines.append(f'           MOVE "{k}" TO {s.kname}')
                    self.lines.append(f"           READ {s.name}")
                    m.read_key(0, k)
                    self.trace()
                for j, (f, _, _, _) in enumerate(s.alts):
                    for v in sorted({m.val(j, r) for r in m.recs.values()}):
                        self.lines.append(f'           MOVE "{v}" TO {f}')
                        self.lines.append(f"           READ {s.name} KEY IS {f}")
                        m.read_key(j + 1, v)
                        self.trace()
                continue
            for kor, f in enumerate([s.kname] + [a[0] for a in s.alts]):
                self.lines.append(f"           MOVE LOW-VALUES TO {f}")
                self.lines.append(f"           START {s.name} KEY IS NOT < {f}")
                ln = 3 if kor == 0 else s.alts[kor - 1][2]
                m.start(">=", kor, ln, "\x00" * ln)
                self.trace()
                for _ in range(len(m.recs) + 1):
                    self.lines.append(f"           READ {s.name} NEXT RECORD")
                    m.read_next()
                    self.trace()

    def render(self):
        out = self.header(self.name, self.same)
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


TRACE = re.compile(r"^T(\d{3}) ")


def normalize(m, traces):
    """The model's lines with the predicted 02s read as 00: (lines, problem or None)."""
    out = []
    for ln in m:
        t = TRACE.match(ln)
        if t is None or traces is None:
            out.append(ln)
            continue
        pred = traces[int(t.group(1)) - 1]
        chars = list(ln)
        for j, p in enumerate(pred):
            pos = 5 + 3 * j
            got = ln[pos:pos + 2]
            if got != p:
                return None, {"line": ln, "file": j + 1, "model": got, "mirror": p}
            if got == "02":
                chars[pos + 1] = "0"
        out.append("".join(chars))
    return out, None


def run(cmd, timeout, **kw):
    try:
        return subprocess.run(cmd, capture_output=True, timeout=timeout, **kw)
    except subprocess.TimeoutExpired:
        return None


def compare(base, wd, root, src, setup, inputs, traces):
    """Status, details and GnuCOBOL's lines of program `src` (written to base.cob): GnuCOBOL in the
    fresh directory wd after the setup program (if any) vs front end + cobolrun with the records
    `inputs`; `traces`: the mirror's statuses per trace line (None: only read every 02 as 00)."""
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
    nf = len(traces[0]) if traces else 0
    for ln in g:
        t = TRACE.match(ln)
        if t is not None and "02" in [ln[5 + 3 * j:7 + 3 * j] for j in range(nf)]:
            return "gnucobol-02", ln, g
    if traces is None:
        # a hand case: a status 02 ends a line (alt_cases/)
        mn = [ln[:-3] + " 00" if ln.endswith(" 02") else ln for ln in m]
    else:
        mn, bad = normalize(m, traces)
        if bad is not None:
            return "status-mismatch", bad, g
    if g != mn:
        k = next((i for i, (a, b) in enumerate(zip(g, mn)) if a != b), min(len(g), len(mn)))
        return "mismatch", {"line": k, "gnucobol": g[k:k + 3], "lean": m[k:k + 3]}, g
    return "ok", {"lines": len(g)}, g


def run_repro(path, out, root):
    """A hand case (no setup, no mirror; tools/difftest/alt_cases): GnuCOBOL vs model with a status
    02 that ends a model line read as 00; prints the verdict and, where they differ, the first
    difference."""
    name = os.path.splitext(os.path.basename(path))[0]
    wd = os.path.join(out, name)
    os.makedirs(wd)
    with open(path) as fh:
        src = fh.read()
    status, info, g = compare(os.path.join(wd, name), wd, root, src, None, [], None)
    print(f"{name}: {status}" + (f" ({info})" if status == "ok" else ""))
    if status != "ok":
        print("  " + json.dumps(info)[:1500])
    return status


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=os.path.join(HERE, "out_alt"))
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(HERE)))
    ap.add_argument("--show", type=int, default=3)
    ap.add_argument("--run", nargs="+", metavar="PROG.cob", help="run hand cases instead")
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    os.makedirs(a.out, exist_ok=True)
    if a.run:
        st = [run_repro(p, a.out, root) for p in a.run]
        print(f"{len(st)} cases, {st.count('ok')} agree")
        return 0 if st.count("ok") == len(st) else 1
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, shown = {}, 0
    cov = {"traces": 0, "same": 0, "files": {}, "stmts": {}}
    for i in range(a.n):
        name = f"AK{a.seed:02d}{i:03d}"
        gen = Gen(random.Random(rng.random()), name)
        src = gen.render()
        wd = os.path.join(a.out, name)
        os.makedirs(wd, exist_ok=True)
        status, info, g = compare(os.path.join(wd, name), wd, root, src, gen.render_setup(), gen.inputs(),
                                  gen.traces)
        tally[status] = tally.get(status, 0) + 1
        cov["traces"] += len(gen.traces)
        cov["same"] += gen.same
        for s in gen.specs:
            k = f"F{s.i}:" + "".join("d" if d else "u" for _, _, _, d in s.alts)
            cov["files"][k] = cov["files"].get(k, 0) + 1
        for k, v in gen.cnt.items():
            cov["stmts"][k] = cov["stmts"].get(k, 0) + v
        with open(os.path.join(a.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": i, "status": status}) + "\n")
        if status != "ok" and shown < a.show:
            shown += 1
            print(f"--- {name} {status}")
            print(json.dumps(info)[:1500])
    cov["files"] = dict(sorted(cov["files"].items()))
    cov["stmts"] = dict(sorted(cov["stmts"].items()))
    print(json.dumps({"coverage": cov}))
    print(json.dumps({"tally": tally}))
    return 0 if tally.get("ok", 0) == a.n else 1


if __name__ == "__main__":
    sys.exit(main())

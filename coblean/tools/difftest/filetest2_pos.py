#!/usr/bin/env python3
"""Differential testing of indexed files: ACCESS DYNAMIC and the reading position (copy of the
PREREG_M extended suite's filetest2.py with the M-pos steering off: class M-pos is generated).

Each random program creates two indexed files: F1 with ACCESS DYNAMIC (record key RKEY, keys
K01..K12, written in random order) and F2 with ACCESS SEQUENTIAL (keys S01..S12, written in
ascending order). Both are then opened I-O and the program runs K random statements:
  F1: START KEY = / > / >= / NOT < (key present or absent), READ NEXT, READ by key, DELETE by
      key, REWRITE by key, WRITE (new or duplicate key);
  F2: READ (next), DELETE and REWRITE of the record read (or with none read);
with and without AT END / INVALID KEY / NOT AT END / NOT INVALID KEY phrases. After every
statement the program displays the file status; a record read is displayed in the NOT AT END /
NOT INVALID KEY phrase. An epilogue reads both files back in key order. Records are inserted
and deleted before, at and after the reading position, so READ NEXT after DELETE, WRITE,
REWRITE, START and keyed READ is compared.

The generator tracks the keys of F1 and its reading position (as the model keeps it) only to
steer: no READ NEXT while the position is undefined (after a failed START or keyed READ, until
a START or keyed READ succeeds), and no WRITE of class M-pos.

Not generated (a model deviation from IBM and GnuCOBOL, class M-pos): a WRITE of a new key that
sorts exactly at the model's reading position when IBM would not read it next. The model keeps
the position as an index (Cobol/Sem/File.lean, fileWrite: a record inserted before the position
moves it, one inserted at it does not), so it reads the new record next; IBM keeps a key. Three
forms: after a START, any such key (dev run file1, program 23: START KEY >= K05 on K01 K06 K08,
WRITE K04, READ NEXT: GnuCOBOL K06, model K04); after a READ whose record was then deleted, a
key at or below the key read (dev run file2, program 2: READ K02, DELETE K02, WRITE K02, READ
NEXT: GnuCOBOL K05, model K02); after OPEN, before any READ or START, a key below every key
(dev run file3, program 12: OPEN I-O on K04 K05 K08 K09, WRITE K02, READ NEXT: GnuCOBOL K04,
model K02; IBM's choice for this form is not established here, so it is left out as well).

Displayed differently (GnuCOBOL 3.2 deviations from IBM, classes of filetest.py's KNOWN):
  G-rw21  REWRITE of a missing record key: GnuCOBOL 21, IBM 23 (probes/file1.cob, also in
          ACCESS DYNAMIC). After a REWRITE of F1 only the status class FS1(1:1) is displayed,
          so the second digit of that status is not compared.
  G-rwkey ACCESS SEQUENTIAL REWRITE with a changed record key: not generated (F2's REWRITE
          changes only the data part).
  G-dup21, G-extend, G-lastkey (ACCESS SEQUENTIAL WRITE): not generated (F2 is written once, in
          ascending order, in OUTPUT mode); G-rwalt: no alternate keys; G-open41: no failed OPEN.
GnuCOBOL (-std=ibm) and the front end + cobolrun must agree on every line (ext_common.py).

usage: filetest2.py --root C --out DIR [--n N] [--seed S] [--k K]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402

K1 = [f"K{i:02d}" for i in range(1, 13)]
K2 = [f"S{i:02d}" for i in range(1, 13)]


def lit(s):
    return "'" + s + "'"


def data4(rng):
    return "".join(rng.choice("ABCDWXYZ") for _ in range(4))


class Pos:
    """F1's keys and reading position as the model keeps them: `idx`, an index into the records
    in key order (Cobol/Sem/File.lean). IBM's position is a key instead: after a READ, the next
    record is the first with a key above the one read; after a START, the record START chose.
    `basis` is that key (and whether a record with it counts), `from_start` whether it comes
    from a START. `valid` is False while the position is undefined (after a failed START or
    keyed READ)."""

    def __init__(self, keys):
        self.keys = sorted(keys)
        self.idx, self.valid, self.from_start = 0, True, True   # OPEN chose the first record
        self.basis = ("", True)

    def start(self, op, key):
        ks = self.keys
        if op == "=":
            hits = [j for j, k in enumerate(ks) if k == key]
        elif op == ">":
            hits = [j for j, k in enumerate(ks) if k > key]
        else:
            hits = [j for j, k in enumerate(ks) if k >= key]
        if hits:
            self.idx, self.valid, self.from_start = hits[0], True, True
            self.basis = (key, op != ">")
        else:
            self.valid, self.from_start = False, False

    def read_next(self):
        if self.idx < len(self.keys):
            self.basis = (self.keys[self.idx], False)
            self.idx += 1
        self.from_start = False

    def read_key(self, key):
        if key in self.keys:
            self.idx, self.valid = self.keys.index(key) + 1, True
            self.basis = (key, False)
        else:
            self.valid = False
        self.from_start = False

    def delete(self, key):
        if key in self.keys:
            j = self.keys.index(key)
            if j < self.idx:
                self.idx -= 1
            self.keys.remove(key)

    def write_diverges(self, key):
        """True for class M-pos: a new key that sorts exactly at the model's position (so the
        model reads it next) where IBM would not read it next: after a START (any such key), or
        after a READ when the key is not above the key read (the record read was deleted and a
        key at or below it inserted)."""
        return False   # filetest2_pos: class M-pos generated too (the steering of filetest2.py is off)
        if key in self.keys or not self.valid:
            return False
        if sum(1 for k in self.keys if k < key) != self.idx:
            return False
        if self.from_start:
            return True
        b, incl = self.basis
        return key < b or (key == b and not incl)

    def write(self, key):
        if key not in self.keys:
            j = sum(1 for k in self.keys if k < key)
            if j < self.idx:
                self.idx += 1
            self.keys.insert(j, key)


def f1_stmt(rng, i, pos):
    out = []
    kind = rng.random()
    key = rng.choice(K1)
    if kind < 0.16:   # START
        op = rng.choice(["=", ">", ">=", "NOT <"])
        out.append(f"           MOVE {lit(key)} TO RKEY")
        text = f"START F1 KEY IS {op} RKEY"
        if rng.random() < 0.5:
            text += f" INVALID KEY DISPLAY 'F{i:02d} E|' NOT INVALID KEY DISPLAY 'F{i:02d} N|' END-START"
        out += E.wrap(text)
        out.append(f"           DISPLAY 'F{i:02d} ' FS1 '|'")
        pos.start(">=" if op == "NOT <" else op, key)
    elif kind < 0.40 and pos.valid:   # READ NEXT (only from a defined position)
        if rng.random() < 0.6:
            out += E.wrap(f"READ F1 NEXT RECORD AT END DISPLAY 'F{i:02d} E|' "
                          f"NOT AT END DISPLAY 'F{i:02d} R ' REC '|' END-READ")
        else:
            out.append("           READ F1 NEXT RECORD")
        out.append(f"           DISPLAY 'F{i:02d} ' FS1 '|'")
        pos.read_next()
    elif kind < 0.55:   # READ by key
        out.append(f"           MOVE {lit(key)} TO RKEY")
        out += E.wrap(f"READ F1 INVALID KEY DISPLAY 'F{i:02d} E|' "
                      f"NOT INVALID KEY DISPLAY 'F{i:02d} R ' REC '|' END-READ")
        out.append(f"           DISPLAY 'F{i:02d} ' FS1 '|'")
        pos.read_key(key)
    elif kind < 0.72:   # DELETE by key
        out.append(f"           MOVE {lit(key)} TO RKEY")
        if rng.random() < 0.5:
            out += E.wrap(f"DELETE F1 RECORD INVALID KEY DISPLAY 'F{i:02d} E|' "
                          f"NOT INVALID KEY DISPLAY 'F{i:02d} N|' END-DELETE")
        else:
            out.append("           DELETE F1 RECORD")
        out.append(f"           DISPLAY 'F{i:02d} ' FS1 '|'")
        pos.delete(key)
    elif kind < 0.86:   # REWRITE by key (status class only: G-rw21)
        out.append(f"           MOVE {lit(key)} TO RKEY")
        out.append(f"           MOVE {lit(data4(rng))} TO RDATA")
        if rng.random() < 0.5:
            out += E.wrap(f"REWRITE REC INVALID KEY DISPLAY 'F{i:02d} E|' "
                          f"NOT INVALID KEY DISPLAY 'F{i:02d} N|' END-REWRITE")
        else:
            out.append("           REWRITE REC")
        out.append(f"           DISPLAY 'F{i:02d} ' FS1(1:1) '|'")
    else:   # WRITE by key (class M-pos left out)
        for _ in range(20):
            if not pos.write_diverges(key):
                break
            key = rng.choice(K1)
        else:
            return out
        out.append(f"           MOVE {lit(key)} TO RKEY")
        out.append(f"           MOVE {lit(data4(rng))} TO RDATA")
        if rng.random() < 0.5:
            out += E.wrap(f"WRITE REC INVALID KEY DISPLAY 'F{i:02d} E|' "
                          f"NOT INVALID KEY DISPLAY 'F{i:02d} N|' END-WRITE")
        else:
            out.append("           WRITE REC")
        out.append(f"           DISPLAY 'F{i:02d} ' FS1 '|'")
        pos.write(key)
    return out


def f2_stmt(rng, i):
    out = []
    kind = rng.random()
    if kind < 0.5:
        if rng.random() < 0.6:
            out += E.wrap(f"READ F2 AT END DISPLAY 'G{i:02d} E|' "
                          f"NOT AT END DISPLAY 'G{i:02d} R ' SREC '|' END-READ")
        else:
            out.append("           READ F2")
        out.append(f"           DISPLAY 'G{i:02d} ' FS2 '|'")
    elif kind < 0.75:
        out.append("           DELETE F2 RECORD")
        out.append(f"           DISPLAY 'G{i:02d} ' FS2 '|'")
    else:
        out.append(f"           MOVE {lit(data4(rng))} TO SDATA")
        out.append("           REWRITE SREC")
        out.append(f"           DISPLAY 'G{i:02d} ' FS2 '|'")
    return out


def program(rng, k):
    sel = ["           SELECT F1 ASSIGN TO 'FT2A'", "               ORGANIZATION IS INDEXED",
           "               ACCESS MODE IS DYNAMIC", "               RECORD KEY IS RKEY",
           "               FILE STATUS IS FS1.",
           "           SELECT F2 ASSIGN TO 'FT2B'", "               ORGANIZATION IS INDEXED",
           "               ACCESS MODE IS SEQUENTIAL", "               RECORD KEY IS SKEY",
           "               FILE STATUS IS FS2."]
    fd = ["       FD  F1.", "       01  REC.", "           05  RKEY PIC X(3).",
          "           05  RDATA PIC X(4).",
          "       FD  F2.", "       01  SREC.", "           05  SKEY PIC X(3).",
          "           05  SDATA PIC X(4)."]
    data = ["       01  FS1 PIC XX.", "       01  FS2 PIC XX."]
    lines = E.header("FILET2", data, files_section=fd, select_lines=sel)
    keys = set(rng.sample(K1, rng.randint(3, 9)))
    order = list(keys)
    rng.shuffle(order)
    lines.append("           OPEN OUTPUT F1")
    for key in order:
        lines.append(f"           MOVE {lit(key)} TO RKEY")
        lines.append(f"           MOVE {lit(data4(rng))} TO RDATA")
        lines.append("           WRITE REC")
    lines.append("           DISPLAY 'C1 ' FS1 '|'")
    lines.append("           CLOSE F1")
    lines.append("           OPEN OUTPUT F2")
    for key in sorted(rng.sample(K2, rng.randint(3, 9))):
        lines.append(f"           MOVE {lit(key)} TO SKEY")
        lines.append(f"           MOVE {lit(data4(rng))} TO SDATA")
        lines.append("           WRITE SREC")
    lines.append("           DISPLAY 'C2 ' FS2 '|'")
    lines.append("           CLOSE F2")
    lines.append("           OPEN I-O F1")
    lines.append("           OPEN I-O F2")
    lines.append("           DISPLAY 'O ' FS1 ' ' FS2 '|'")
    pos = Pos(keys)
    for i in range(k):
        lines += f1_stmt(rng, i, pos) if rng.random() < 0.7 else f2_stmt(rng, i)
    lines += ["           CLOSE F1", "           CLOSE F2",
              "           OPEN INPUT F1", "           OPEN INPUT F2",
              "           DISPLAY 'Z ' FS1 ' ' FS2 '|'",
              "           PERFORM UNTIL FS1 NOT = '00'",
              "               READ F1 NEXT RECORD",
              "                   NOT AT END DISPLAY 'Z1 ' REC '|'",
              "               END-READ",
              "           END-PERFORM",
              "           PERFORM UNTIL FS2 NOT = '00'",
              "               READ F2",
              "                   NOT AT END DISPLAY 'Z2 ' SREC '|'",
              "               END-READ",
              "           END-PERFORM",
              "           DISPLAY 'Z ' FS1 ' ' FS2 '|'",
              "           CLOSE F1", "           CLOSE F2", "           STOP RUN."]
    return "\n".join(E.check_lines(lines)) + "\n"


def main():
    args = E.arg_parser(__doc__, 100, 30).parse_args()
    E.main_loop(args, program, E.PLAIN_COBC, E.PLAIN_FE, files=("FT2A", "FT2B"))


if __name__ == "__main__":
    main()

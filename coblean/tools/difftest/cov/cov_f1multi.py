#!/usr/bin/env python3
"""Differential testing of several sequential files read interleaved (the front end's
OPEN/READ statements, Cobol/Sem/File.lean), next to cov_f1inp.py, which covers the semantics'
input-stream READ of hand-built IRs (Cobol/Sem/Exec.lean `.read`, PREREG_M set 2 survivor #5).

Each random program declares 2 or 3 sequential files FA, FB, FC (fixed 3-byte records, FILE
STATUS SA, SB, SC), writes 0 to 4 records to each (OPEN OUTPUT, WRITE, CLOSE), opens them all
for INPUT and runs 6 to 16 READs in a random interleaving: READ ... AT END / NOT AT END with a
DISPLAY in each phrase, READ ... INTO a working item, and READs past the end (status 10, then
46, where neither phrase runs). The file status is displayed after every READ. Some programs
CLOSE and re-OPEN one file midway, which restarts it.

usage: cov_f1multi.py --root C --out DIR [--n N] [--seed S] [--k K]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cov_common as E  # noqa: E402

CH = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
NAMES = ["A", "B", "C"]


def program(rng, k):
    nf = rng.choice([2, 3])
    fs = NAMES[:nf]
    L = []

    def st(s):
        L.append("           " + s)

    st("OPEN OUTPUT " + " ".join("F" + f for f in fs))
    for f in fs:
        for _ in range(rng.randint(0, 4)):
            st(f"MOVE '{''.join(rng.choice(CH) for _ in range(3))}' TO R{f}")
            st(f"WRITE R{f}")
    st("CLOSE " + " ".join("F" + f for f in fs))
    st("OPEN INPUT " + " ".join("F" + f for f in fs))
    reopened = False
    for i in range(rng.randint(6, max(7, k))):
        f = rng.choice(fs)
        r = rng.random()
        if r < 0.08 and not reopened:
            st(f"CLOSE F{f}")
            st(f"OPEN INPUT F{f}")
            st(f"DISPLAY 'O{i:02d} {f} ' S{f} '|'")
            reopened = True
            continue
        st("MOVE '***' TO W")
        if r < 0.6:
            st(f"READ F{f}")
            st(f"  AT END DISPLAY 'E{i:02d} {f} ' S{f} '|'")
            st(f"  NOT AT END DISPLAY 'N{i:02d} {f} ' R{f} ' ' S{f} '|'")
            st("END-READ")
        elif r < 0.85:
            st(f"READ F{f} INTO W")
            st(f"  AT END DISPLAY 'E{i:02d} {f} ' S{f} '|'")
            st("END-READ")
            st(f"DISPLAY 'I{i:02d} {f} ' W ' ' S{f} '|'")
        else:
            st(f"READ F{f}")
        st(f"DISPLAY 'S{i:02d} {f} ' S{f} '|'")
    st("CLOSE " + " ".join("F" + f for f in fs))
    head = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. COVF1.",
            "       ENVIRONMENT DIVISION.", "       INPUT-OUTPUT SECTION.", "       FILE-CONTROL."]
    for f in fs:
        head += [f"           SELECT F{f} ASSIGN TO \"f{f.lower()}.dat\"",
                 f"               ORGANIZATION IS SEQUENTIAL FILE STATUS IS S{f}."]
    head += ["       DATA DIVISION.", "       FILE SECTION."]
    for f in fs:
        head += [f"       FD  F{f}.", f"       01  R{f} PIC X(3)."]
    head += ["       WORKING-STORAGE SECTION.", "       01  W PIC X(3) VALUE '***'."]
    for f in fs:
        head.append(f"       01  S{f} PIC XX VALUE SPACES.")
    head.append("       PROCEDURE DIVISION.")
    return "\n".join(head + L + ["           STOP RUN."]) + "\n"


def main():
    ap = E.arg_parser(__doc__, 60, 14)
    args = ap.parse_args()
    E.main_loop(args, program, E.PLAIN_COBC, E.PLAIN_FE, files=["fa.dat", "fb.dat", "fc.dat"])


if __name__ == "__main__":
    main()

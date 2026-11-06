#!/usr/bin/env python3
"""Differential testing of variable-length records (RECORD IS VARYING IN SIZE FROM a TO b
DEPENDING ON item), where PREREG_M set 2 survivors #7 (Cobol/Sem/File.lean recLenOk: a record of
exactly the maximum length) and #9 (REWRITE of a sequential record with a changed length) sit.

Each random program uses a sequential file VS (FROM a TO b, 1 <= a, b - a from 2 to 8, record
area PIC X(b), DEPENDING ON LS) and an indexed file VI (ACCESS DYNAMIC, RECORD KEY VI-KEY PIC
XX at the start, FROM c TO d with c >= 2, DEPENDING ON LI), each with FILE STATUS:
  1. OPEN OUTPUT VS and WRITE records of length a, b, a length between, or a - 1 (status 44);
  2. OPEN I-O VS: READs (the record area filled with '*' first; 00, then 10 and 46 past the
     end), and REWRITEs: a changed length within a..b after a READ (44), the unchanged length of
     a record of the maximum length b (00), or any length within a..b without a current record
     (43);
  3. OPEN INPUT VS and READ every record;
  4. OPEN OUTPUT VI and WRITE records with random keys (an existing key: 22) and lengths c, d,
     between, or c - 1 (44, never together with an existing key);
  5. OPEN I-O VI: keyed READs (existing keys: 00; missing: 23), REWRITEs of existing keys with
     any length from c - 1 to d (indexed records may change length; c - 1: 44), DELETEs of
     existing or missing keys;
  6. OPEN INPUT VI and READ NEXT through the file (then 10 and 46).
The generator keeps a model of the files to choose the cases above. After each statement the
file status is displayed, and after each READ the length item and the whole record area (both
systems leave the bytes after a shorter record unchanged).

Not generated, GnuCOBOL 3.2 deviations from the standard and IBM (coblean follows the standard):
  * G-varmax: a WRITE whose DEPENDING ON value exceeds the maximum b: GnuCOBOL writes the record
    cut to b bytes with status 00, instead of 44 (probes/p3vary.cob);
  * G-rwshort: a sequential REWRITE with an unchanged length below the maximum b: GnuCOBOL gives
    44 and leaves the record, instead of 00 (probes/p3cvary.cob); at length b it gives 00;
  * G-rw21: an indexed REWRITE (dynamic access) of a key not in the file: GnuCOBOL 21 instead of
    23;
  * G-vary39: a new variable-length sequential file whose only WRITE was rejected (44): GnuCOBOL
    then refuses OPEN I-O of it with status 39 (READ 47, REWRITE 49, CLOSE 42), where coblean
    opens the empty file (00); without the rejected WRITE GnuCOBOL opens it too
    (probes/p3evary.cob, p3dempty.cob). The first WRITE of each program is therefore valid;
    the status of every OPEN is displayed;
  * two errors at once (no current record and a length outside a..b; an existing key and a
    length outside c..d): the order of the checks is not fixed by the standard, and GnuCOBOL and
    coblean differ (43 / 44).

usage: cov_f2vary.py --root C --out DIR [--n N] [--seed S] [--k K]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cov_common as E  # noqa: E402

CH = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"


def rtext(rng, n):
    return "".join(rng.choice(CH) for _ in range(n))


def program(rng, k):
    a = rng.randint(1, 4)
    b = a + rng.randint(2, 8)
    c = rng.randint(2, 4)
    d = c + rng.randint(2, 8)
    L = []
    n = 0

    def st(s):
        L.append("           " + s)

    def tag():
        nonlocal n
        n += 1
        return f"{n:03d}"

    def wlen(lo, hi):
        r = rng.random()
        if r < 0.25:
            return lo
        if r < 0.55:
            return hi
        if r < 0.85:
            return rng.randint(lo, hi)
        return lo - 1 if lo > 1 else lo

    # 1. sequential writes (the first one valid: see G-vary39)
    recs = []
    st("OPEN OUTPUT VS")
    st(f"DISPLAY 'O{tag()} ' SV '|'")
    for j in range(rng.randint(1, max(2, k // 3))):
        ln = wlen(a, b) if j else rng.choice([a, b, rng.randint(a, b)])
        st(f"MOVE '{rtext(rng, b)}' TO VS-REC")
        st(f"MOVE {ln} TO LS")
        st("WRITE VS-REC")
        st(f"DISPLAY 'W{tag()} ' SV '|'")
        if a <= ln <= b:
            recs.append(ln)
    st("CLOSE VS")
    # 2. I-O: reads and rewrites
    st("OPEN I-O VS")
    st(f"DISPLAY 'O{tag()} ' SV '|'")
    pos, cur, eof = 0, None, False
    for _ in range(rng.randint(2, k)):
        r = rng.random()
        options = []
        if cur is not None:
            others = [x for x in range(a, b + 1) if x != recs[cur]]
            if others:
                options.append(("changed", rng.choice(others)))
            if recs[cur] == b:
                options.append(("same", b))
        else:
            options.append(("nocur", rng.randint(a, b)))
        if r < 0.5 or not options:
            st("MOVE ALL '*' TO VS-REC")
            st("READ VS")
            st(f"DISPLAY 'R{tag()} ' SV ' ' LS ' ' VS-REC '|'")
            if eof:
                cur = None
            elif pos < len(recs):
                cur, pos = pos, pos + 1
            else:
                eof, cur = True, None
        else:
            kind, ln = rng.choice(options)
            st(f"MOVE '{rtext(rng, b)}' TO VS-REC")
            st(f"MOVE {ln} TO LS")
            st("REWRITE VS-REC")
            st(f"DISPLAY 'U{tag()} ' SV '|'")
            cur = None
    st("CLOSE VS")
    # 3. read back
    st("OPEN INPUT VS")
    st(f"DISPLAY 'O{tag()} ' SV '|'")
    for _ in range(len(recs) + 2):
        st("MOVE ALL '*' TO VS-REC")
        st("READ VS")
        st(f"DISPLAY 'X{tag()} ' SV ' ' LS ' ' VS-REC '|'")
    st("CLOSE VS")
    # 4. indexed writes
    keys = set()
    st("OPEN OUTPUT VI")
    st(f"DISPLAY 'O{tag()} ' SI '|'")
    for _ in range(rng.randint(1, max(2, k // 3))):
        key = f"K{rng.randint(0, 9)}"
        ln = wlen(c, d)
        if key in keys and not (c <= ln <= d):
            ln = d
        st(f"MOVE '{key}{rtext(rng, d - 2)}' TO VI-REC")
        st(f"MOVE {ln} TO LI")
        st("WRITE VI-REC")
        st(f"DISPLAY 'I{tag()} ' SI '|'")
        if c <= ln <= d:
            keys.add(key)
    st("CLOSE VI")
    # 5. indexed I-O
    st("OPEN I-O VI")
    st(f"DISPLAY 'O{tag()} ' SI '|'")
    for _ in range(rng.randint(2, k)):
        r = rng.random()
        if r < 0.4 or not keys:
            key = rng.choice(sorted(keys)) if keys and rng.random() < 0.75 else f"K{rng.randint(0, 9)}"
            st("MOVE ALL '*' TO VI-REC")
            st(f"MOVE '{key}' TO VI-KEY")
            st("READ VI KEY IS VI-KEY")
            st(f"DISPLAY 'J{tag()} ' SI ' ' LI ' ' VI-REC '|'")
        elif r < 0.85:
            key = rng.choice(sorted(keys))
            st(f"MOVE '{key}{rtext(rng, d - 2)}' TO VI-REC")
            st(f"MOVE {rng.randint(c - 1, d)} TO LI")
            st("REWRITE VI-REC")
            st(f"DISPLAY 'V{tag()} ' SI '|'")
        else:
            key = rng.choice(sorted(keys)) if rng.random() < 0.7 else f"K{rng.randint(0, 9)}"
            st(f"MOVE '{key}' TO VI-KEY")
            st("DELETE VI RECORD")
            st(f"DISPLAY 'D{tag()} ' SI '|'")
            keys.discard(key)
    st("CLOSE VI")
    # 6. indexed read back in key order
    st("OPEN INPUT VI")
    st(f"DISPLAY 'O{tag()} ' SI '|'")
    for _ in range(len(keys) + 2):
        st("MOVE ALL '*' TO VI-REC")
        st("READ VI NEXT RECORD")
        st(f"DISPLAY 'Y{tag()} ' SI ' ' LI ' ' VI-REC '|'")
    st("CLOSE VI")
    head = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. COVF2.",
            "       ENVIRONMENT DIVISION.", "       INPUT-OUTPUT SECTION.", "       FILE-CONTROL.",
            "           SELECT VS ASSIGN TO \"vs.dat\"",
            "               ORGANIZATION IS SEQUENTIAL FILE STATUS IS SV.",
            "           SELECT VI ASSIGN TO \"vi.dat\"",
            "               ORGANIZATION IS INDEXED ACCESS MODE IS DYNAMIC",
            "               RECORD KEY IS VI-KEY FILE STATUS IS SI.",
            "       DATA DIVISION.", "       FILE SECTION.",
            f"       FD  VS RECORD IS VARYING IN SIZE FROM {a} TO {b}",
            "           DEPENDING ON LS.",
            f"       01  VS-REC PIC X({b}).",
            f"       FD  VI RECORD IS VARYING IN SIZE FROM {c} TO {d}",
            "           DEPENDING ON LI.",
            "       01  VI-REC.",
            "           05  VI-KEY PIC XX.",
            f"           05  VI-DATA PIC X({d - 2}).",
            "       WORKING-STORAGE SECTION.",
            "       01  LS PIC 99 VALUE 0.", "       01  LI PIC 99 VALUE 0.",
            "       01  SV PIC XX VALUE SPACES.", "       01  SI PIC XX VALUE SPACES.",
            "       PROCEDURE DIVISION."]
    return "\n".join(head + L + ["           STOP RUN."]) + "\n"


def main():
    ap = E.arg_parser(__doc__, 60, 10)
    args = ap.parse_args()
    E.main_loop(args, program, E.PLAIN_COBC, E.PLAIN_FE, files=["vs.dat", "vi.dat"])


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Differential testing of UNSTRING.

Each random program runs K random UNSTRING statements on a 14-character item over the
alphabet 'AB,; ' with 1-2 delimiters (1-2 characters, ALL or not), 1-3 alphanumeric receivers
of 2-6 characters with optional DELIMITER IN / COUNT IN, an optional POINTER (1 to 16, so
out-of-range values occur) and TALLYING IN, and ON OVERFLOW / NOT ON OVERFLOW phrases; it
displays every receiver, delimiter, count, the pointer, the tally and which phrase ran. The
counts and the tally start from non-zero values, so that a tally that is stored instead of
added, or a count set for a receiver not acted upon, shows. GnuCOBOL (-std=ibm) and the front
end + cobolrun must agree.

usage: unstringtest.py [--n N] [--seed S] [--k K] [--out DIR] [--show K]
"""
import argparse
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import difftest as D  # noqa: E402
from inspecttest import lit, wrap, run  # noqa: E402

ALPHA = "AB,; "


def rnd_delim(rng):
    n = rng.choice([1, 1, 1, 2])
    if n == 1 and rng.random() < 0.15:
        return "SPACE"
    return lit("".join(rng.choice(",; A") for _ in range(n)))


def rnd_stmt(rng):
    """(setup lines, UNSTRING text, display lines)"""
    item = "".join(rng.choice(ALPHA) for _ in range(14))
    setup = [f"MOVE {lit(item)} TO S", "MOVE ALL '*' TO R1 R2 R3", "MOVE '**' TO D1 D2 D3",
             "MOVE 0 TO C1 C2 C3 T", "MOVE ' ' TO F"]
    parts = ["UNSTRING S"]
    if rng.random() < 0.85:
        ds = []
        for _ in range(rng.choice([1, 1, 2])):
            ds.append(("ALL " if rng.random() < 0.3 else "") + rnd_delim(rng))
        parts.append("DELIMITED BY " + " OR ".join(ds))
    parts.append("INTO")
    nr = rng.choice([1, 2, 3])
    for i in range(1, nr + 1):
        parts.append(f"R{i}")
        if rng.random() < 0.4:
            parts.append(f"DELIMITER IN D{i}")
        if rng.random() < 0.4:
            parts.append(f"COUNT IN C{i}")
    if rng.random() < 0.4:
        p = rng.choice([1, 1, 2, 3, 5, 8, 14, 15, 16])
        setup.append(f"MOVE {p} TO P")
        parts.append("WITH POINTER P")
    else:
        setup.append("MOVE 0 TO P")
    if rng.random() < 0.4:
        parts.append("TALLYING IN T")
    if rng.random() < 0.6:
        parts.append("ON OVERFLOW MOVE 'O' TO F")
    if rng.random() < 0.4:
        parts.append("NOT ON OVERFLOW MOVE 'N' TO F")
    parts.append("END-UNSTRING")
    return setup, " ".join(parts)


def program(rng, k):
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. UNSTT.",
             "       DATA DIVISION.", "       WORKING-STORAGE SECTION.",
             "       01  S PIC X(14).", "       01  R1 PIC X(4).", "       01  R2 PIC X(6).",
             "       01  R3 PIC X(2).", "       01  D1 PIC X(2).", "       01  D2 PIC X(2).",
             "       01  D3 PIC X(2).", "       01  C1 PIC 9(2).", "       01  C2 PIC 9(2).",
             "       01  C3 PIC 9(2).", "       01  P PIC 9(2).", "       01  T PIC 9(2).",
             "       01  F PIC X.", "       PROCEDURE DIVISION."]
    stmts = []
    for i in range(k):
        setup, u = rnd_stmt(rng)
        # non-zero counts and tally, fixed per statement number (the random stream is unchanged):
        # TALLYING adds to T, and COUNT IN is stored only for the receivers acted upon
        setup = [x for x in setup if x != "MOVE 0 TO C1 C2 C3 T"] + [
            f"MOVE {(i * 7) % 60 + 10} TO C1", f"MOVE {(i * 11) % 60 + 10} TO C2",
            f"MOVE {(i * 13) % 60 + 10} TO C3", f"MOVE {(i * 17) % 50 + 5} TO T"]
        stmts.append((setup[0], u))
        lines += ["           " + x for x in setup]
        lines += wrap(u)
        # wrapped: on one line, P, T and F fell past column 72 and were never displayed
        lines += wrap(f"DISPLAY 'U{i:02d} ' R1 '|' R2 '|' R3 '|' D1 D2 D3 '|' C1 C2 C3 '|' P '|' T '|' F")
    lines.append("           STOP RUN.")
    return "\n".join(lines) + "\n", stmts


def bump(tally, out, case, status):
    """Count one case and append it to OUT/results.jsonl (one JSON object per case)."""
    tally[status] = tally.get(status, 0) + 1
    with open(os.path.join(out, "results.jsonl"), "a") as fh:
        fh.write(json.dumps({"case": case, "status": status}) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=25)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                  "out_unstring"))
    ap.add_argument("--show", type=int, default=3)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown = {"ok": 0}, 0
    for p in range(args.n):
        src, stmts = program(rng, args.k)
        base = os.path.join(args.out, f"unst_{args.seed}_{p}")
        outs, err = run(src, base)
        if err:
            bump(tally, args.out, p, "error")
            print(f"program {p}: {err}")
            continue
        g, m = outs
        bad = [(i, a, b) for i, (a, b) in enumerate(zip(g, m)) if a.rstrip() != b.rstrip()]
        if len(g) != len(m):
            bad.append((min(len(g), len(m)), "<length>", "<length>"))
        if not bad:
            bump(tally, args.out, p, "ok")
            for e in (".cob", "", ".fe.json"):
                if os.path.exists(base + e):
                    os.remove(base + e)
            continue
        bump(tally, args.out, p, "mismatch")
        if shown < args.show:
            shown += 1
            for i, a, b in bad[:3]:
                st = stmts[i] if i < len(stmts) else ("", "")
                print(f"program {p} stmt {i}: {st[0]}  {st[1]}")
                print(f"   gnucobol: {a!r}")
                print(f"   model   : {b!r}")
    print(json.dumps({"tally": tally}))


if __name__ == "__main__":
    main()

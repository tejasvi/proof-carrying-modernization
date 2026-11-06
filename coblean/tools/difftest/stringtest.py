#!/usr/bin/env python3
"""Differential testing of STRING.

Each random program runs K random STRING statements: 1-3 groups of 1-2 sources (literals over
the alphabet 'AB,; ', alphanumeric items S1 X(6) and S2 X(4), the unsigned numeric item N1
9(3)), each group DELIMITED BY SIZE, a 1-2 character literal, SPACE or the item D1 X(1); INTO
R X(8) (preset to '********'); an optional POINTER (0 to 10, so out-of-range values occur); ON
OVERFLOW / NOT ON OVERFLOW phrases.  It displays R, the pointer and which phrase ran.
GnuCOBOL (-std=ibm) and the front end + cobolrun must agree.

usage: stringtest.py [--n N] [--seed S] [--k K] [--out DIR] [--show K]
"""
import argparse
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from inspecttest import lit, wrap, run  # noqa: E402

ALPHA = "AB,; "


def rnd_src(rng):
    r = rng.random()
    if r < 0.45:
        return lit("".join(rng.choice(ALPHA) for _ in range(rng.randint(1, 5))))
    return rng.choice(["S1", "S2", "N1"])


def rnd_delim(rng):
    r = rng.random()
    if r < 0.35:
        return "SIZE"
    if r < 0.5:
        return "SPACE"
    if r < 0.6:
        return "D1"
    return lit("".join(rng.choice(",; A") for _ in range(rng.choice([1, 1, 2]))))


def rnd_stmt(rng):
    s1 = "".join(rng.choice(ALPHA) for _ in range(6))
    s2 = "".join(rng.choice(ALPHA) for _ in range(4))
    setup = [f"MOVE {lit(s1)} TO S1", f"MOVE {lit(s2)} TO S2",
             f"MOVE {rng.randint(0, 999)} TO N1", f"MOVE {lit(rng.choice(',; A'))} TO D1",
             "MOVE ALL '*' TO R", "MOVE ' ' TO F"]
    parts = ["STRING"]
    for _ in range(rng.choice([1, 2, 3])):
        for _ in range(rng.choice([1, 1, 2])):
            parts.append(rnd_src(rng))
        parts.append("DELIMITED BY " + rnd_delim(rng))
    parts.append("INTO R")
    if rng.random() < 0.5:
        setup.append(f"MOVE {rng.choice([0, 1, 1, 2, 3, 5, 8, 9, 10])} TO P")
        parts.append("WITH POINTER P")
    else:
        setup.append("MOVE 0 TO P")
    if rng.random() < 0.6:
        parts.append("ON OVERFLOW MOVE 'O' TO F")
    if rng.random() < 0.4:
        parts.append("NOT ON OVERFLOW MOVE 'N' TO F")
    parts.append("END-STRING")
    return setup, " ".join(parts)


def program(rng, k):
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. STRT.",
             "       DATA DIVISION.", "       WORKING-STORAGE SECTION.",
             "       01  S1 PIC X(6).", "       01  S2 PIC X(4).", "       01  N1 PIC 9(3).",
             "       01  D1 PIC X(1).", "       01  R PIC X(8).", "       01  P PIC 9(2).",
             "       01  F PIC X.", "       PROCEDURE DIVISION."]
    stmts = []
    for i in range(k):
        setup, u = rnd_stmt(rng)
        stmts.append((" ".join(setup[:4]), u))
        lines += ["           " + x for x in setup]
        lines += wrap(u)
        lines.append(f"           DISPLAY 'S{i:02d} ' R '|' P '|' F")
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
                                                  "out_string"))
    ap.add_argument("--show", type=int, default=3)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown = {"ok": 0}, 0
    for p in range(args.n):
        src, stmts = program(rng, args.k)
        base = os.path.join(args.out, f"str_{args.seed}_{p}")
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

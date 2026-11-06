#!/usr/bin/env python3
"""Differential testing of PERFORM VARYING ... AFTER ... (2 and 3 levels).

Each random program runs K PERFORM statements with VARYING and one or two AFTER phrases, inline
or out of line (a paragraph), WITH TEST BEFORE or AFTER. FROM operands are literals, data items
or an outer loop's variable; BY operands are non-zero literals, a non-zero data item or (for an
outer level) the next inner level's variable while that one only takes positive values; UNTIL
conditions test the level's own variable and sometimes another level's. Every condition also
ends the loop once the body has run more than 40 times. The body (and the paragraph) displays
the three variables and a counter; after each PERFORM their final values are displayed.
GnuCOBOL (-std=ibm) and the front end + cobolrun must produce the same DISPLAY lines.

Left out of generation (GnuCOBOL departs from IBM's documented rule):
  G-after3  with TEST BEFORE and three levels GnuCOBOL sets the third variable only after
            condition-1 is false (its code initializes level k + 2 inside level k + 1's loop), so
            a condition-1 reading it, and its value at the end, differ from IBM ("identifier-5 and
            identifier-8 contain the current values of identifier-6 and identifier-9"). Here a
            condition never reads a variable two levels deeper, and V3 is not displayed after such
            a PERFORM.

usage: aftertest.py [--n N] [--seed S] [--k K] [--out DIR] [--show K]
"""
import argparse
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from inspecttest import run  # noqa: E402

GUARD = "CNT > 40"


def lit(n):
    return str(n) if n >= 0 else f"-{-n}"


def rnd_level(rng, k, levels):
    """(var, from, by, cond, by_sign, positive) for level k (0-based) given the outer levels."""
    v = f"V{k + 1}"
    r = rng.random()
    if k > 0 and r < 0.35:
        frm = rng.choice([x[0] for x in levels])          # an outer variable
        pos_from = all(x[5] for x in levels if x[0] == frm)
    elif r < 0.55:
        frm = rng.choice(["W1", "W2"])
        pos_from = False
    else:
        n = rng.randint(-2, 4)
        frm, pos_from = lit(n), n > 0
    by_sign = rng.choice([1, 1, 1, -1])
    if rng.random() < 0.2:
        by = "W3" if by_sign > 0 else "W4"                 # W3 > 0, W4 < 0
    else:
        by = lit(by_sign * rng.choice([1, 1, 2, 3]))
    lim = rng.randint(-1, 4)
    if by_sign > 0:
        c = f"{v} {rng.choice(['>', '>', 'NOT <'])} {lit(lim)}"
    else:
        c = f"{v} < {lit(lim - 3)}"
    return v, frm, by, c, by_sign, pos_from and by_sign > 0


def rnd_perform(rng, i, para):
    n = rng.choice([2, 2, 3])
    levels = []
    for k in range(n):
        levels.append(list(rnd_level(rng, k, levels)))
    # an outer level augmented by the next inner variable: only while that one stays positive
    for k in range(n - 1):
        nxt = levels[k + 1]
        if levels[k][4] > 0 and nxt[5] and rng.random() < 0.25:
            levels[k][2] = nxt[0]
    test = rng.choice(["", "", "WITH TEST BEFORE ", "WITH TEST AFTER ", "WITH TEST AFTER "])
    before = test != "WITH TEST AFTER "
    conds = []
    for k, (v, frm, by, c, _, _) in enumerate(levels):
        extra = ""
        if rng.random() < 0.3:
            # G-after3: with TEST BEFORE, a condition does not read a variable two levels deeper
            other = rng.choice([x[0] for x in levels[:k + 2] if before] or [x[0] for x in levels])
            extra = f" OR {other} = {lit(rng.randint(0, 3))}"
        conds.append(f"({c}{extra} OR {GUARD})")
    head = f"VARYING {levels[0][0]} FROM {levels[0][1]} BY {levels[0][2]} UNTIL {conds[0]}"
    for k in range(1, n):
        head += f" AFTER {levels[k][0]} FROM {levels[k][1]} BY {levels[k][2]} UNTIL {conds[k]}"
    setup = [f"MOVE 0 TO CNT", f"MOVE {lit(rng.randint(-3, 3))} TO V1 V2 V3",
             f"MOVE {lit(rng.randint(-1, 3))} TO W1", f"MOVE {lit(rng.randint(0, 2))} TO W2",
             f"MOVE {rng.randint(1, 2)} TO W3", f"MOVE -{rng.randint(1, 2)} TO W4",
             f"DISPLAY 'T{i:02d}'"]
    body = ["ADD 1 TO CNT", "MOVE V1 TO E1", "MOVE V2 TO E2", "MOVE V3 TO E3",
            "DISPLAY 'B ' E1 ' ' E2 ' ' E3 ' ' CNT"]
    if rng.random() < 0.15:
        body = ["PERFORM 1 TIMES", "IF CNT > 2 EXIT PERFORM END-IF", "MOVE 1 TO W1",
                "END-PERFORM"] + body
    if para:
        stmt = [f"PERFORM PB {test}{head}"]
    else:
        stmt = [f"PERFORM {test}{head}"] + body + ["END-PERFORM"]
    if before and n == 3:      # G-after3: V3's final value is not compared
        fin = ["MOVE V1 TO E1", "MOVE V2 TO E2", "DISPLAY 'E ' E1 ' ' E2 ' ' CNT"]
    else:
        fin = ["MOVE V1 TO E1", "MOVE V2 TO E2", "MOVE V3 TO E3", "DISPLAY 'E ' E1 ' ' E2 ' ' E3 ' ' CNT"]
    return setup + stmt + fin


def wrap(text, indent=11, width=72):
    """COBOL fixed-format lines (area B from column 12), splitting at blanks outside literals."""
    words, cur, inq = [], "", False
    for ch in text:
        if ch == "'":
            inq = not inq
        if ch == " " and not inq:
            words.append(cur)
            cur = ""
        else:
            cur += ch
    words.append(cur)
    out, line = [], " " * indent
    for w in words:
        if not w:
            continue
        if len(line) + 1 + len(w) > width:
            out.append(line)
            line = " " * (indent + 4) + w
        else:
            line = line + (" " if line.strip() else "") + w
    out.append(line)
    return out


def program(rng, k):
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. AFTT.",
             "       DATA DIVISION.", "       WORKING-STORAGE SECTION.",
             "       01  V1 PIC S9(3) VALUE 0.", "       01  V2 PIC S9(3) VALUE 0.",
             "       01  V3 PIC S9(3) VALUE 0.", "       01  W1 PIC S9(3) VALUE 0.",
             "       01  W2 PIC S9(3) VALUE 0.", "       01  W3 PIC S9(3) VALUE 1.",
             "       01  W4 PIC S9(3) VALUE -1.", "       01  CNT PIC 9(4) VALUE 0.",
             "       01  E1 PIC -999.", "       01  E2 PIC -999.", "       01  E3 PIC -999.",
             "       PROCEDURE DIVISION.", "       P0."]
    for i in range(k):
        for s in rnd_perform(rng, i, rng.random() < 0.4):
            lines += wrap(s)
    lines += ["           STOP RUN.", "       PB.", "           ADD 1 TO CNT.",
              "           MOVE V1 TO E1. MOVE V2 TO E2. MOVE V3 TO E3.",
              "           DISPLAY 'B ' E1 ' ' E2 ' ' E3 ' ' CNT."]
    for l in lines:
        assert len(l) <= 72, l
    return "\n".join(lines) + "\n"


def bump(tally, out, case, status):
    tally[status] = tally.get(status, 0) + 1
    with open(os.path.join(out, "results.jsonl"), "a") as fh:
        fh.write(json.dumps({"case": case, "status": status}) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=6)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "out_after"))
    ap.add_argument("--show", type=int, default=3)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown = {"ok": 0}, 0
    for p in range(args.n):
        src = program(rng, args.k)
        base = os.path.join(args.out, f"aft_{args.seed}_{p}")
        outs, err = run(src, base)
        if err:
            bump(tally, args.out, p, "error")
            print(f"program {p}: {err[:300]}")
            continue
        g, m = outs
        if g == m:
            bump(tally, args.out, p, "ok")
            for e in (".cob", "", ".fe.json"):
                if os.path.exists(base + e):
                    os.remove(base + e)
            continue
        bump(tally, args.out, p, "mismatch")
        if shown < args.show:
            shown += 1
            i = next((j for j, (a, b) in enumerate(zip(g, m)) if a != b), min(len(g), len(m)))
            print(f"program {p}: first difference at line {i}: gnucobol {g[i:i + 1]} model {m[i:i + 1]}"
                  f" ({len(g)} vs {len(m)} lines)")
    print(json.dumps({"tally": tally}))
    return 0 if tally["ok"] == args.n else 1


sys.exit(main())

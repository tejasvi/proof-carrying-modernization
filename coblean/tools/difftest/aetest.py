#!/usr/bin/env python3
"""Differential testing of alphanumeric-edited items (PICTURE with A, X, 9 and B, 0, / insertion).

Each random program declares alphanumeric-edited items (one of them in a table, one inside a
group) and runs K MOVE statements into them from alphanumeric items shorter and longer than the
data positions, literals, unsigned and signed integer DISPLAY items, figurative constants (SPACE,
ZERO, HIGH-VALUE, LOW-VALUE, QUOTE, with and without ALL), group items, other alphanumeric-edited
items, reference-modified items, a table element subscripted by a data name and the functions
REVERSE and LOWER-CASE of an alphanumeric item; some MOVEs have several receivers mixing
alphanumeric and alphanumeric-edited items, some receivers are reference-modified (no editing).
Some steps are an INITIALIZE of an item, of the group, of a table element or of two identifiers
(one of them the subscript of the other) instead. After each step the receivers are displayed,
and alphanumeric-edited items are compared with literals.
GnuCOBOL (-std=ibm) and the front end + cobolrun must produce the same DISPLAY lines.

Left out of generation:
  MOVE ALL nonfigurative-literal into an alphanumeric-edited item (GnuCOBOL fills the whole item
  without editing; the standard repeats the literal to the item's size and edits it; the front end
  makes it unsupported);
  MOVE from a function or from an item with a data-name subscript to several receivers, one
  alphanumeric-edited (unsupported);
  MOVE of an alphanumeric-edited item into itself (overlapping fields; the model stops with
  an overlap).

usage: aetest.py [--n N] [--seed S] [--k K] [--out DIR] [--show K]
"""
import argparse
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from inspecttest import run, wrap  # noqa: E402

ALPHA = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 -*"


def rnd_ae_pic(rng):
    n = rng.randint(3, 12)
    syms = [rng.choice("XXXXA9") for _ in range(n)]
    for _ in range(rng.randint(1, 3)):
        syms.insert(rng.randint(0, len(syms)), rng.choice("B0/"))
    if not any(s in "XA" for s in syms):
        syms[0] = "X"
    pat = "".join(syms)
    # repetition factors for runs
    out, i = "", 0
    while i < len(pat):
        j = i
        while j < len(pat) and pat[j] == pat[i]:
            j += 1
        out += pat[i] if j - i == 1 else (pat[i] * 2 if j - i == 2 else f"{pat[i]}({j - i})")
        i = j
    return out, len(syms)


def rnd_text(rng, n):
    return "".join(rng.choice(ALPHA) for _ in range(n))


def program(rng, k):
    aes = [rnd_ae_pic(rng) for _ in range(3)]
    tab_pic, tab_len = rnd_ae_pic(rng)
    grp_pic, grp_len = rnd_ae_pic(rng)
    s_lens = [rng.randint(1, 4), rng.randint(5, 9), rng.randint(10, 16)]
    data = ["       01  AE{} PIC {}.".format(i + 1, p) for i, (p, _) in enumerate(aes)]
    data += [f"       01  S{i + 1} PIC X({n}) VALUE '{rnd_text(rng, n)}'." for i, n in enumerate(s_lens)]
    data += [f"       01  N1 PIC 9(5) VALUE {rng.randint(0, 99999)}.",
             f"       01  N2 PIC S9(4) VALUE -{rng.randint(0, 9999)}.",
             f"       01  N3 PIC 9(2) VALUE {rng.randint(0, 99)}.",
             "       01  T1 OCCURS 3.", f"           05  ATB PIC {tab_pic}.",
             "       01  G1.", f"           05  AG PIC {grp_pic}.",
             f"           05  GN PIC X(3) VALUE '{rnd_text(rng, 3)}'.",
             "       01  G2.", f"           05  G2A PIC X(4) VALUE '{rnd_text(rng, 4)}'.",
             f"           05  G2B PIC 9(3) VALUE {rng.randint(0, 999)}.",
             "       01  I PIC 9 VALUE 1."]
    srcs = ["S1", "S2", "S3", "N1", "N2", "N3", "G2", "SPACES", "ZEROS", "HIGH-VALUES",
            "LOW-VALUES", "QUOTES", "ALL SPACES", "ALL ZEROS", "AE1", "AE2", "S3 (2:5)",
            "G2 (2:4)", "ATB (2)", "AG", "ATB (I)", "FUNCTION REVERSE (S2)",
            "FUNCTION LOWER-CASE (S3)"]
    rcvs = ["AE1", "AE2", "AE3", "ATB (I)", "AG", "S2", "AE2 (2:3)", "G1"]
    proc = []
    for i in range(k):
        s = rng.choice(srcs + [f"'{rnd_text(rng, rng.randint(1, 14))}'"] * 3 + [str(rng.randint(0, 99999))])
        rs = rng.sample(rcvs, rng.choice([1, 1, 1, 2, 3]))
        if s.split(" ")[0] in [r.split(" ")[0] for r in rs]:
            rs = [r for r in rs if r.split(" ")[0] != s.split(" ")[0]] or ["AE3"]
            if s.split(" ")[0] == "AE3":
                rs = ["AE1"]
        if rs == ["G1"] and s.startswith("AG"):
            rs = ["AE1"]
        if ("G1" in rs or "AG" in rs) and s.startswith("AG"):
            rs = [r for r in rs if r not in ("G1", "AG")] or ["AE1"]
        if s == "ATB (I)" or s.startswith("FUNCTION"):
            rs = rs[:1]
        proc.append(f"MOVE {rng.randint(1, 3)} TO I")
        if rng.random() < 0.15:
            tg, rs = rng.choice([("AE1", ["AE1"]), ("AE2", ["AE2"]), ("AE3", ["AE3"]), ("G1", ["G1"]),
                                 ("T1 (I)", ["T1 (I)"]), ("AE1 AE2", ["AE1", "AE2"]),
                                 ("G1 AE3", ["G1", "AE3"]),
                                 ("T1 (I) I", ["ATB (1)", "ATB (2)", "ATB (3)", "I"])])
            proc.append(f"INITIALIZE {tg}")
        else:
            proc.append(f"MOVE {s} TO {' '.join(rs)}")
        shown = []
        for r in rs:
            shown += [f"'[' {r} ']'"]
        proc.append(f"DISPLAY 'M{i:02d} ' {' '.join(shown)}")
        if rng.random() < 0.3:
            e, n = rng.choice([("AE1", aes[0][1]), ("AE2", aes[1][1]), ("AE3", aes[2][1])])
            proc.append(f"IF {e} = '{rnd_text(rng, n)}' OR {e} > '{rnd_text(rng, n)}' "
                        f"DISPLAY 'C{i:02d} Y' ELSE DISPLAY 'C{i:02d} N' END-IF")
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. AET.", "       DATA DIVISION.",
             "       WORKING-STORAGE SECTION."] + data + ["       PROCEDURE DIVISION.", "       P0."]
    for s in proc:
        lines += wrap(s)
    lines.append("           STOP RUN.")
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
    ap.add_argument("--k", type=int, default=25)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "out_ae"))
    ap.add_argument("--show", type=int, default=3)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown = {"ok": 0}, 0
    for p in range(args.n):
        src = program(rng, args.k)
        base = os.path.join(args.out, f"ae_{args.seed}_{p}")
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
            print(f"program {p}: first difference at line {i}: gnucobol {g[i:i + 1]!r} model {m[i:i + 1]!r}"
                  f" ({len(g)} vs {len(m)} lines)")
    print(json.dumps({"tally": tally}))
    return 0 if tally["ok"] == args.n else 1


sys.exit(main())

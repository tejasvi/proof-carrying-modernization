#!/usr/bin/env python3
"""Differential testing of INSPECT on signed numeric DISPLAY items.

Each random program runs K random INSPECT statements on one of five signed numeric DISPLAY items
(PIC S9(7) with a trailing or leading embedded sign, with a trailing or leading separate sign, and
PIC S9(5)V99), after a MOVE of a random signed value: TALLYING (ALL, CHARACTERS, LEADING, one or two
counters, BEFORE / AFTER INITIAL, the sign characters as patterns), REPLACING (ALL, LEADING, FIRST,
CHARACTERS) and CONVERTING, with digit patterns and replacements.  The counters start at non-zero
values (TALLYING adds).  After each statement it displays both counters and the item's bytes (a
REDEFINES as PIC X), never the numeric item itself (DISPLAY formats signed items differently in
GnuCOBOL).  GnuCOBOL (-std=ibm) and the front end + cobolrun must print the same lines, compared
exactly.  Not generated (named): negative zero; replacement characters other than digits (a non-digit
in the byte that carries an embedded sign is unsupported in the model); G-convempty: CONVERTING with
an empty region (BEFORE INITIAL at the first examined byte, AFTER INITIAL absent or at the last byte)
on an item with an embedded sign, where GnuCOBOL 3.2 drops the sign although nothing is converted.

usage: inspecttest_signed.py [--n N] [--seed S] [--k K] [--out DIR] [--tree ROOT] [--show K]
  --tree  the coblean tree whose GnuCOBOL wrapper, front end and cobolrun are used (default: this one)
"""
import argparse
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import difftest as D  # noqa: E402
from inspecttest import lit, wrap  # noqa: E402

# (name, picture clause, bytes, integer digits, decimals)
ITEMS = [("N1", "PIC S9(7)", 7, 7, 0), ("N2", "PIC S9(7) SIGN LEADING", 7, 7, 0),
         ("N3", "PIC S9(7) SIGN TRAILING SEPARATE", 8, 7, 0),
         ("N4", "PIC S9(7) SIGN LEADING SEPARATE", 8, 7, 0), ("N5", "PIC S9(5)V99", 7, 5, 2)]


def rnd_value(rng, idig, dec):
    alpha = rng.choice(["0125", "15", "0123456789", "5", "05"])
    ds = "".join(rng.choice(alpha) for _ in range(idig + dec))
    neg = rng.random() < 0.6 and ds.strip("0") != ""
    body = ds[:idig] + ("." + ds[idig:] if dec else "")
    return ("-" if neg else "+") + body


def rnd_digit(rng):
    return rng.choice("0125" if rng.random() < 0.7 else "0123456789")


def rnd_delim(rng):
    r = rng.random()
    if r < 0.6:
        return ""
    d = rnd_digit(rng)
    return f" {'BEFORE' if r < 0.8 else 'AFTER'} INITIAL {lit(d)}"


def rnd_stmt(rng):
    r = rng.random()
    if r < 0.14:
        return f"TALLYING C1 FOR ALL {lit(rnd_digit(rng))}{rnd_delim(rng)}"
    if r < 0.24:
        return f"TALLYING C1 FOR CHARACTERS{rnd_delim(rng)}"
    if r < 0.30:
        return f"TALLYING C1 FOR LEADING {lit(rnd_digit(rng))}"
    if r < 0.36:
        return f"TALLYING C1 FOR ALL {lit(rng.choice('-+'))} C2 FOR ALL {lit(rnd_digit(rng))}"
    if r < 0.44:
        return f"TALLYING C1 FOR ALL {lit(rnd_digit(rng))} C2 FOR ALL {lit(rnd_digit(rng))}"
    if r < 0.56:
        n = rng.choice([1, 1, 2])
        p = "".join(rnd_digit(rng) for _ in range(n))
        q = "".join(rnd_digit(rng) for _ in range(n))
        return f"REPLACING ALL {lit(p)} BY {lit(q)}{rnd_delim(rng)}"
    if r < 0.62:
        return f"REPLACING LEADING {lit(rnd_digit(rng))} BY {lit(rnd_digit(rng))}"
    if r < 0.68:
        return f"REPLACING FIRST {lit(rnd_digit(rng))} BY {lit(rnd_digit(rng))}{rnd_delim(rng)}"
    if r < 0.76:
        return f"REPLACING CHARACTERS BY {lit(rnd_digit(rng))}{rnd_delim(rng)}"
    if r < 0.86:
        return (f"TALLYING C1 FOR ALL {lit(rnd_digit(rng))} "
                f"REPLACING ALL {lit(rnd_digit(rng))} BY {lit(rnd_digit(rng))}")
    n = rng.choice([1, 2, 3])
    src = "".join(rng.sample("0123456789", n))
    dst = "".join(rng.choice("0123456789") for _ in range(n))
    return f"CONVERTING {lit(src)} TO {lit(dst)}{rnd_delim(rng)}"


def convempty(v, c):
    """G-convempty: CONVERTING whose region in the examined digits of value `v` is empty."""
    if not c.startswith("CONVERTING"):
        return False
    digits = v[1:].replace(".", "")
    for kw in ("BEFORE", "AFTER"):
        tag = f" {kw} INITIAL '"
        if tag in c:
            d = c.split(tag, 1)[1][0]
            j = digits.find(d)
            return j == 0 if kw == "BEFORE" else (j < 0 or j + 1 >= len(digits))
    return False


def program(rng, k):
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. INSPS.",
             "       DATA DIVISION.", "       WORKING-STORAGE SECTION."]
    for name, pic, nb, _, _ in ITEMS:
        lines.append(f"       01  {name} {pic}.")
        lines.append(f"       01  {name}X REDEFINES {name} PIC X({nb}).")
    lines += ["       01  C1 PIC 9(4).", "       01  C2 PIC 9(4).", "       PROCEDURE DIVISION."]
    stmts = []
    for i in range(k):
        name, pic, _, idig, dec = rng.choice(ITEMS)
        v = rnd_value(rng, idig, dec)
        c = rnd_stmt(rng)
        while "SEPARATE" not in pic and convempty(v, c):
            c = rnd_stmt(rng)
        stmts.append((name, v, c))
        lines.append(f"           MOVE {v} TO {name}")
        # non-zero counters (TALLYING adds to them); at most 1002 + 8 fits PIC 9(4)
        lines.append(f"           MOVE {(i * 37) % 1000 + 1} TO C1")
        lines.append(f"           MOVE {(i * 53) % 1000 + 2} TO C2")
        lines += wrap(f"INSPECT {name} {c}")
        lines.append(f"           DISPLAY 'I{i:02d} ' C1 ' ' C2 ' ' {name}X")
    lines.append("           STOP RUN.")
    for ln in lines:
        assert len(ln) <= 72, ln
    return "\n".join(lines) + "\n", stmts


def run(src, base, tree):
    cobc = os.path.join(tree, "scripts", "cobc.sh")
    libdir = os.path.join(tree, "third_party", "gnucobol", "usr", "lib", "x86_64-linux-gnu")
    cobolfe = os.path.join(tree, "tools", "cobolfe", "cobolfe.py")
    cobolrun = os.path.join(tree, ".lake", "build", "bin", "cobolrun")
    with open(base + ".cob", "w") as fh:
        fh.write(src)
    c = subprocess.run([cobc, "-x", "-std=ibm", "-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return None, "cobc: " + c.stderr
    env = dict(os.environ, LD_LIBRARY_PATH=libdir)
    r = subprocess.run([base], capture_output=True, env=env, timeout=20)
    if r.returncode != 0:
        return None, f"gnucobol rc {r.returncode}: " + r.stderr.decode("latin-1")[-300:]
    gout = r.stdout.decode("latin-1")
    fe = subprocess.run([sys.executable, "-I", "-B", cobolfe, base + ".cob", "--profile", "gnucobol",
                         "--main", "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0 or "unsupported" in fe.stderr:
        return None, "cobolfe: " + fe.stderr
    lr = subprocess.run([cobolrun, base + ".fe.json"], capture_output=True, text=True, timeout=60)
    if lr.returncode != 0:
        return None, "cobolrun: " + lr.stderr
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop"):
        m.append("<model: " + res["signal"] + ">")
    return (gout.split("\n")[:-1] if gout.endswith("\n") else gout.split("\n"), m), None


def bump(tally, out, case, status):
    tally[status] = tally.get(status, 0) + 1
    with open(os.path.join(out, "results.jsonl"), "a") as fh:
        fh.write(json.dumps({"case": case, "status": status}) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=25)
    ap.add_argument("--out", required=True)
    ap.add_argument("--tree", default=D.ROOT)
    ap.add_argument("--show", type=int, default=3)
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown = {"ok": 0}, 0
    for p in range(args.n):
        src, stmts = program(rng, args.k)
        base = os.path.join(args.out, f"insps_{args.seed}_{p}")
        outs, err = run(src, base, args.tree)
        if err:
            bump(tally, args.out, p, "error")
            print(f"program {p}: {err[:300]}")
            continue
        g, m = outs
        bad = [(i, a, b) for i, (a, b) in enumerate(zip(g, m)) if a != b]
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
            i, a, b = bad[0]
            st = stmts[i] if i < len(stmts) else None
            print(f"program {p} statement {i}: {st}\n  gnucobol: {a!r}\n  model   : {b!r}")
    print(json.dumps({"tally": tally}))
    return 0 if set(tally) <= {"ok"} else 1


sys.exit(main())

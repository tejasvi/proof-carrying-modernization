#!/usr/bin/env python3
"""Differential test of the Lean transcriptions of the Java and Rust rewrites against the
real code: the equivalence theorems are about `AcctIntJava.accrue` / `AcctIntRust.accrue`;
this checks, on random valid records, that those Lean functions compute what `AcctInt.java`
(JDK `BigDecimal`) and `acctint.rs` (rustc, debug build: overflow panics) compute.

usage: targettest.py [--n N] [--seed S]
"""
import argparse
import json
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(HERE, "out")
TC = os.path.expanduser("~/.elan/toolchains/leanprover--lean4---v4.35.0")


def build():
    os.makedirs(OUT, exist_ok=True)
    subprocess.run(["javac", "-d", OUT, os.path.join(ROOT, "examples", "acctint", "AcctInt.java"),
                    os.path.join(HERE, "AcctIntDriver.java")], check=True)
    subprocess.run(["rustc", "-O", "-C", "debug-assertions=on", "-C", "overflow-checks=on",
                    "-o", os.path.join(OUT, "rust_driver"), os.path.join(HERE, "rust_driver.rs")],
                   check=True, capture_output=True)


def run(cmd, inp, env=None):
    return subprocess.run(cmd, input=inp, capture_output=True, text=True, check=True, env=env).stdout.split("\n")


def main():
    global OUT
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=500)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=OUT, help="working directory (default: out/ next to this script)")
    args = ap.parse_args()
    OUT = args.out
    build()
    open(os.path.join(OUT, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    lines = []
    for _ in range(args.n):
        t = rng.choice("SCSCX")
        bal = "null" if rng.random() < 0.1 else str(rng.choice(
            [rng.randint(-10 ** 13 + 1, 10 ** 13 - 1), rng.randint(-10 ** 6, 10 ** 6)]))
        rate = rng.randint(-99999, 99999)
        days = rng.choice([0, rng.randint(1, 999)])
        lines.append(f"{t} {bal} {rate} {days}")
    inp = "\n".join(lines) + "\n"
    java = run(["java", "-cp", OUT, "AcctIntDriver"], inp)
    rust = run([os.path.join(OUT, "rust_driver")], inp)
    env = dict(os.environ, LEAN_PATH=os.path.join(ROOT, ".lake", "build", "lib", "lean") + ":" +
               os.path.join(TC, "lib", "lean"))
    lean_j = run([os.path.join(TC, "bin", "lean"), "--run", os.path.join(HERE, "LeanModels.lean"), "java"], inp, env)
    lean_r = run([os.path.join(TC, "bin", "lean"), "--run", os.path.join(HERE, "LeanModels.lean"), "rust"], inp, env)
    bad = 0
    for i, l in enumerate(lines):
        b0 = bad
        if not (java[i] == lean_j[i] and rust[i] == lean_r[i] and java[i] == rust[i]):
            bad += 1
            if bad <= 10:
                print("MISMATCH", l, "| java", java[i], "| lean-java", lean_j[i], "| rust", rust[i],
                      "| lean-rust", lean_r[i])
        with open(os.path.join(OUT, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": i, "status": "mismatch" if bad > b0 else "ok"}) + "\n")
    print({"cases": args.n, "mismatches": bad})
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

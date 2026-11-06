#!/usr/bin/env python3
"""Check the IR of RECSUM against the COBOL source with GnuCOBOL, including file I/O.

For random input files (0 to 30 records: id bytes, packed amount), RECSUM.cob runs under
GnuCOBOL reading `INFILE` (fixed 8-byte records) and writing `OUTFILE` (fixed 10-byte
records); the GnuCOBOL-profile IR (`recsum.gnucobol.ir.json`) runs under `cobolrun` with the
same records as file 1.  The output records must agree.

usage: validate.py [--n N] [--seed S]
"""
import argparse
import json
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
COBC = os.path.join(ROOT, "scripts", "cobc.sh")
COBOLRUN = os.path.join(ROOT, ".lake", "build", "bin", "cobolrun")
LIBDIR = os.path.join(ROOT, "third_party", "gnucobol", "usr", "lib", "x86_64-linux-gnu")
OUT = os.path.join(HERE, "out")


def packed(v, digits):
    nd = digits // 2 * 2 + 1
    s = str(abs(v)).rjust(nd, "0")
    nib = [int(c) for c in s] + [0xD if v < 0 else 0xC]
    return [nib[i] * 16 + nib[i + 1] for i in range(0, len(nib), 2)]


def main():
    global OUT
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=30)
    ap.add_argument("--ir", help="IR to check (default: the hand-written GnuCOBOL-profile IR)")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=OUT, help="working directory (default: out/ next to this script)")
    args = ap.parse_args()
    OUT = args.out
    os.makedirs(OUT, exist_ok=True)
    open(os.path.join(OUT, "results.jsonl"), "w").close()
    src = open(os.path.join(HERE, "RECSUM.cob")).read()
    src = src.replace("           SELECT IN-FILE ASSIGN TO INFILE\n               ORGANIZATION IS SEQUENTIAL.",
                      "           SELECT IN-FILE ASSIGN TO INFILE\n               ORGANIZATION IS RECORD SEQUENTIAL.")
    src = src.replace("           SELECT OUT-FILE ASSIGN TO OUTFILE\n               ORGANIZATION IS SEQUENTIAL.",
                      "           SELECT OUT-FILE ASSIGN TO OUTFILE\n               ORGANIZATION IS RECORD SEQUENTIAL.")
    prog = os.path.join(OUT, "recsum")
    open(prog + ".cob", "w").write(src)
    c = subprocess.run([COBC, "-x", "-std=ibm", "-fbinary-truncate", "-fno-arithmetic-osvs", "-o", prog,
                        prog + ".cob"], capture_output=True, text=True)
    if c.returncode:
        print(c.stderr[:3000]); return 1
    rng = random.Random(args.seed)
    ir = args.ir or os.path.join(HERE, "recsum.gnucobol.ir.json")
    bad = 0
    for i in range(args.n):
        b0 = bad
        k = rng.choice([0, 1, 2, rng.randint(3, 30)])
        recs = [[rng.randint(0x41, 0x5A) for _ in range(4)] + packed(rng.randint(-9999999, 9999999), 7)
                for _ in range(k)]
        inf, outf = os.path.join(OUT, f"in{i}.dat"), os.path.join(OUT, f"out{i}.dat")
        open(inf, "wb").write(bytes(sum(recs, [])))
        if os.path.exists(outf):
            os.remove(outf)
        r = subprocess.run([prog], capture_output=True, text=True,
                           env=dict(os.environ, LD_LIBRARY_PATH=LIBDIR, COB_FILE_PATH="",
                                    DD_INFILE=inf, DD_OUTFILE=outf))
        g = open(outf, "rb").read() if os.path.exists(outf) else b""
        grecs = [list(g[j:j + 10]) for j in range(0, len(g), 10)]
        inputs = os.path.join(OUT, f"in{i}.json")
        json.dump([[1, recs]], open(inputs, "w"))
        l = json.loads(subprocess.run([COBOLRUN, ir, "--inputs", inputs], capture_output=True, text=True).stdout)
        lrecs = [e["write"]["rec"] for e in l["out"]]
        if grecs != lrecs or not l["signal"].startswith("stop") or r.returncode:
            bad += 1
            print("MISMATCH", k, "records\n gnucobol", grecs[:3], r.stderr[:200], "\n lean    ", lrecs[:3], l["signal"])
        with open(os.path.join(OUT, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": i, "status": "mismatch" if bad > b0 else "ok"}) + "\n")
    print(json.dumps({"cases": args.n, "mismatches": bad}))
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

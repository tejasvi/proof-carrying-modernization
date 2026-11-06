#!/usr/bin/env python3
"""Check the IR of BINCNT against the COBOL source with GnuCOBOL.

For random record contents (including counter and total overflow), a driver variant of
BINCNT.cob (the record is set byte by byte through a REDEFINES, `PERFORM 0000-MAIN`, then the
record is dumped) runs under GnuCOBOL; the GnuCOBOL-profile IR (`bincnt.gnucobol.ir.json`,
little-endian COMP-5 as GnuCOBOL stores it on x86) runs under `cobolrun` from the same bytes.
The 8 record bytes must agree.

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


def driver(bs):
    src = open(os.path.join(HERE, "BINCNT.cob")).read()
    src = src.replace("       01  WS-REC.", "       01  WS-REC.")
    src = src.replace("       PROCEDURE DIVISION.",
                      "       01  WS-BYTES REDEFINES WS-REC.\n           05 WS-B PIC X OCCURS 8.\n"
                      "       01  BX PIC 9(4) COMP.\n       PROCEDURE DIVISION.\n       DRIVER.\n" +
                      "".join(f"           MOVE FUNCTION CHAR({b + 1}) TO WS-B({i + 1})\n"
                              for i, b in enumerate(bs)) +
                      "           PERFORM 0000-MAIN\n"
                      "           PERFORM VARYING BX FROM 1 BY 1 UNTIL BX > 8\n"
                      "              DISPLAY FUNCTION ORD(WS-B(BX)) ' ' WITH NO ADVANCING\n"
                      "           END-PERFORM\n           DISPLAY ' '\n           STOP RUN.")
    return src.replace("           GOBACK.", "           EXIT.")


def main():
    global OUT
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=100)
    ap.add_argument("--ir", help="IR to check (default: the hand-written GnuCOBOL-profile IR)")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=OUT, help="working directory (default: out/ next to this script)")
    args = ap.parse_args()
    OUT = args.out
    os.makedirs(OUT, exist_ok=True)
    open(os.path.join(OUT, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    ir = args.ir or os.path.join(HERE, "bincnt.gnucobol.ir.json")
    bad = 0
    for i in range(args.n):
        b0 = bad
        cnt = rng.choice([32767, -32768, -1, 0, rng.randint(-32768, 32767)])
        tot = rng.choice([2 ** 31 - 1, -2 ** 31, 2 ** 31 - 3, rng.randint(-2 ** 31, 2 ** 31 - 1)])
        bs = list(cnt.to_bytes(2, "little", signed=True)) + list(tot.to_bytes(4, "little", signed=True)) \
            + [rng.randint(0, 255), rng.randint(0, 255)]
        base = os.path.join(OUT, f"b{i}")
        open(base + ".cob", "w").write(driver(bs))
        c = subprocess.run([COBC, "-x", "-std=ibm", "-fno-arithmetic-osvs", "-o", base, base + ".cob"],
                           capture_output=True, text=True)
        if c.returncode:
            print(c.stderr[:2000]); return 1
        g = subprocess.run([base], capture_output=True, text=True,
                           env=dict(os.environ, LD_LIBRARY_PATH=LIBDIR)).stdout
        gb = [int(x) - 1 for x in g.split()]
        hexs = "".join(f"{b:02X}" for b in bs)
        l = json.loads(subprocess.run([COBOLRUN, ir, "--mem", hexs], capture_output=True, text=True).stdout)
        if gb != l["mem"][:8] or not l["signal"].startswith("stop"):
            bad += 1
            print("MISMATCH", bs, "\n gnucobol", gb, "\n lean    ", l["mem"][:8], l["signal"])
        with open(os.path.join(OUT, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": i, "status": "mismatch" if bad > b0 else "ok"}) + "\n")
    print(json.dumps({"cases": args.n, "mismatches": bad}))
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

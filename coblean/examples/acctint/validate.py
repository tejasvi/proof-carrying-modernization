#!/usr/bin/env python3
"""Check the hand-written IR of ACCTINT against the COBOL source with GnuCOBOL.

For random account records, a driver variant of ACCTINT.cob (the record is set up by MOVEs,
then `PERFORM 1000-CALC THRU 1000-EXIT`, then the storage is dumped) runs under GnuCOBOL;
the IR (`acctint.gnucobol.ir.json`, ASCII profile) runs under `cobolrun` from the same
initial bytes.  The 33 storage bytes must agree.

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


def packed(v, digits, signed=True):
    nd = digits // 2 * 2 + 1
    s = str(abs(v)).rjust(nd, "0")
    nib = [int(c) for c in s] + [(0xD if v < 0 else 0xC) if signed else 0xF]
    return [nib[i] * 16 + nib[i + 1] for i in range(0, len(nib), 2)]


def lit(v, scale):
    sign = "-" if v < 0 else ""
    a = str(abs(v)).rjust(scale + 1, "0")
    return f"{sign}{a[:-scale]}.{a[-scale:]}" if scale else f"{sign}{a}"


def driver(case):
    src = open(os.path.join(HERE, "ACCTINT.cob")).read()
    cpy = open(os.path.join(HERE, "ACCTREC.cpy")).read()
    src = src.replace("       COPY ACCTREC.\n", cpy)
    setup = ["           MOVE SPACES TO ACCT-ID",
             f"           MOVE '{case['type']}' TO ACCT-TYPE"]
    if case["balance"] is None:
        setup.append("           MOVE LOW-VALUES TO ACCT-BAL-RAW")
    else:
        setup.append(f"           MOVE {lit(case['balance'], 2)} TO ACCT-BALANCE")
    setup += [f"           MOVE {lit(case['rate'], 5)} TO ACCT-RATE",
              f"           MOVE {case['days']} TO ACCT-DAYS",
              "           PERFORM 1000-CALC THRU 1000-EXIT",
              "           PERFORM VARYING DX FROM 1 BY 1 UNTIL DX > 33",
              "              DISPLAY FUNCTION ORD(DBYTE(DX)) ' ' WITH NO ADVANCING",
              "           END-PERFORM",
              "           DISPLAY ' '",
              "           STOP RUN.",
              "       DUMMY-PARA.",
              "           CONTINUE."]
    src = src.replace("           PERFORM 1000-CALC THRU 1000-EXIT.\n           GOBACK.\n", "\n".join(setup) + "\n")
    # a REDEFINES of all storage for the dump: put both records under one group
    src = src.replace("       COPY ACCTREC.", "")
    src = src.replace("       01  ACCT-REC.", "       01  ALLSTORE.\n       02  ACCT-REC.")
    src = src.replace("       01  WS-WORK.", "       02  WS-WORK.")
    src = src.replace("       PROCEDURE DIVISION.",
                      "       01  DUMPV REDEFINES ALLSTORE.\n           05 DBYTE PIC X OCCURS 33.\n"
                      "       01  DX PIC 9(4) COMP.\n       PROCEDURE DIVISION.")
    return src


def initial_bytes(case):
    bs = [0x20] * 8 + [ord(case["type"])]
    bs += [0] * 7 if case["balance"] is None else packed(case["balance"], 13)
    bs += packed(case["rate"], 5)
    bs += [case["days"] // 256, case["days"] % 256]
    bs += [0] * 12   # WS-WORK: set by its VALUE clauses
    return bs


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
    ir = args.ir or os.path.join(HERE, "acctint.gnucobol.ir.json")
    bad = 0
    for i in range(args.n):
        b0 = bad
        bal = None if rng.random() < 0.1 else rng.choice(
            [rng.randint(-10 ** 13 + 1, 10 ** 13 - 1), rng.randint(-10 ** 6, 10 ** 6)])
        case = {"type": rng.choice("SCSX"), "balance": bal,
                "rate": rng.randint(-99999, 99999), "days": rng.choice([0, rng.randint(1, 999)])}
        base = os.path.join(OUT, f"v{i}")
        open(base + ".cob", "w").write(driver(case))
        c = subprocess.run([COBC, "-x", "-std=ibm", "-fbinary-truncate", "-fno-arithmetic-osvs",
                            "-o", base, base + ".cob"], capture_output=True, text=True)
        if c.returncode:
            print(c.stderr[:2000]); return 1
        g = subprocess.run([base], capture_output=True, text=True,
                           env=dict(os.environ, LD_LIBRARY_PATH=LIBDIR)).stdout
        gb = [int(x) - 1 for x in g.split()]
        hexs = "".join(f"{b:02X}" for b in initial_bytes(case))
        l = json.loads(subprocess.run([COBOLRUN, ir, "--mem", hexs], capture_output=True, text=True).stdout)
        if gb != l["mem"][:33] or not l["signal"].startswith("stop"):
            bad += 1
            print("MISMATCH", case, "\n gnucobol", gb, "\n lean    ", l["mem"][:33], l["signal"])
        with open(os.path.join(OUT, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": i, "status": "mismatch" if bad > b0 else "ok"}) + "\n")
    print(json.dumps({"cases": args.n, "mismatches": bad}))
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())

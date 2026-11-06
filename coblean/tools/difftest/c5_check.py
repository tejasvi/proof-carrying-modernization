#!/usr/bin/env python3
"""Hand-written cases for record areas of FDs with several record descriptions (C5): GnuCOBOL
(-std=ibm) against the front end + cobolrun, every DISPLAY line compared exactly.

usage: python3 -I -B c5_check.py --root C --out DIR
Runs every c5_cases/*.cob in a directory of its own under DIR (new), so GnuCOBOL's data files
are never reused or removed. Status per program as in ext_common.run, also in DIR/results.jsonl
({"case": i, "status": s}, programs in name order); prints the tally; exits 0 when all are ok.
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    D = E.difftest(a.root)
    here = os.path.join(os.path.dirname(os.path.abspath(__file__)), "c5_cases")
    os.makedirs(a.out)
    tally = {}
    res = open(os.path.join(a.out, "results.jsonl"), "w")
    for case, f in enumerate(sorted(x for x in os.listdir(here) if x.endswith(".cob"))):
        src = open(os.path.join(here, f), encoding="latin-1").read()
        if any(len(ln) > 72 for ln in src.split("\n")):
            st, det = "gen-col72", None
        else:
            wd = os.path.join(a.out, f[:-4])
            os.makedirs(wd)
            st, det = E.run(D, src, os.path.join(wd, "prog"), E.PLAIN_COBC, E.PLAIN_FE)
        tally[st] = tally.get(st, 0) + 1
        res.write(json.dumps({"case": case, "status": st}) + "\n")
        if st in ("ok", "mismatch"):
            g, m = det
            print(f"{f} {st}\n   gnucobol: {' '.join(g)}" + ("" if st == "ok" else f"\n   model   : {' '.join(m)}"))
        else:
            print(f"{f} {st}: {str(det)[:400]}")
    res.close()
    print(json.dumps({"tally": dict(sorted(tally.items()))}))
    return 0 if set(tally) == {"ok"} else 1


sys.exit(main())

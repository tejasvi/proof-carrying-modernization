#!/usr/bin/env python3
"""Documenting test of the known coblean defect M-pos (Cobol/Sem/File.lean: the dynamic read
position of an indexed file is kept as a record index). After a START, or after a READ whose
record is then DELETEd, a WRITE of a key that lands at that index makes READ NEXT return the
new record; GnuCOBOL (and the standard: the next record by key from the position indicator)
returns the record the position names.

Runs the hand-written programs in f6/ with GnuCOBOL and with the front end + cobolrun and
compares each line exactly. f6/expected.json lists the lines that differ today, with both
outputs. Status per program: "known-mismatch" (exactly the listed lines differ, exactly as
listed), "ok" (every line agrees: the defect is gone, update expected.json), or "mismatch"
(anything else, including a listed line that differs differently).

usage: cov_f6mpos.py --root C --out DIR
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cov_common as E  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    D = E.difftest(args.root)
    here = os.path.join(os.path.dirname(os.path.abspath(__file__)), "f6")
    exp = json.load(open(os.path.join(here, "expected.json")))
    os.makedirs(args.out, exist_ok=True)
    tally = {}
    with open(os.path.join(args.out, "results.jsonl"), "w") as res:
        for f in sorted(x for x in os.listdir(here) if x.endswith(".cob")):
            wd = os.path.join(args.out, f[:-4])
            os.makedirs(wd, exist_ok=True)
            src = open(os.path.join(here, f), encoding="latin-1").read()
            st, det = E.run(D, src, os.path.join(wd, "prog"), E.PLAIN_COBC, E.PLAIN_FE,
                            files=["kf.dat", "kf2.dat"])
            diffs = {}
            if st in ("ok", "mismatch"):
                g, m = det
                if len(g) == len(m):
                    diffs = {str(i): [a, b] for i, (a, b) in enumerate(zip(g, m)) if a != b}
                    st = "ok" if not diffs else ("known-mismatch" if diffs == exp.get(f, {}) else "mismatch")
            tally[st] = tally.get(st, 0) + 1
            res.write(json.dumps({"case": f, "status": st, "diffs": diffs}) + "\n")
            print(f, st, json.dumps(diffs))
    print(json.dumps({"tally": dict(sorted(tally.items()))}))


if __name__ == "__main__":
    main()

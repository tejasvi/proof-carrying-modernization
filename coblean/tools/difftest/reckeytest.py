#!/usr/bin/env python3
"""Differential testing of the spellings of the RECORD KEY and ALTERNATE RECORD KEY clauses.

IBM Enterprise COBOL 6.4 (FILE-CONTROL paragraph, format 2) writes the clauses
`RECORD [KEY] [IS] data-name-2` and `ALTERNATE [RECORD] [KEY] [IS] data-name-3`: the bracketed
words are optional. The programs are filetest.py's random file programs (files created by the
program, OPEN / READ / WRITE / REWRITE / DELETE / CLOSE, keyed READs of every record key and
alternate key value in the epilogue), with each indexed file's record key clause written in one
of the four spellings `RECORD KEY IS k`, `RECORD KEY k`, `RECORD IS k`, `RECORD k`, its alternate
key clause in one of six (`ALTERNATE RECORD KEY IS a` ... `ALTERNATE KEY IS a`, `ALTERNATE a`),
and some sequential files declaring `RECORD DELIMITER STANDARD-1` (which is not a key clause).
GnuCOBOL (-std=ibm) and the front end + cobolrun must agree as in filetest.py (trace lines and
the final dump). Exit status 0 only when every program is ok or ok-abend.

Control: the front end of coblean-20261027T0518Z (COBOLFE=<copy>/cobolfe.py) has no key for
`RECORD IS k` and `RECORD k` (its keyed READ crashed in key_item) and rejects an ALTERNATE clause
without KEY.
Planted fault (reckeytest_m1.diff, next to this file): a clause without KEY names the file's
first ALTERNATE RECORD KEY item, when it has one, as the record key. Recipe:
  cp -a tools/cobolfe M && patch M/parser.py < tools/difftest/reckeytest_m1.diff
  COBOLFE=M/cobolfe.py python3 -I -B tools/difftest/reckeytest.py --n 60 --seed 1
must report mismatches (files with an alternate key and a spelling without KEY).

usage: reckeytest.py [--n N] [--seed S] [--out DIR] [--keep] [--show K]
"""
import argparse
import json
import os
import random
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import difftest as D  # noqa: E402
import filetest as F  # noqa: E402

SPELLINGS = ["RECORD KEY IS {k}", "RECORD KEY {k}", "RECORD IS {k}", "RECORD {k}"]
ALT_SPELLINGS = ["ALTERNATE RECORD KEY IS {k}", "ALTERNATE RECORD KEY {k}", "ALTERNATE RECORD IS {k}",
                 "ALTERNATE RECORD {k}", "ALTERNATE KEY IS {k}", "ALTERNATE {k}"]


def respell(cobol, rng, counts):
    """The program with each RECORD KEY clause respelled and RECORD DELIMITER on some sequential
    files; the same number of lines (the statements' source lines are compared on abends)."""
    out = []
    for ln in cobol.split("\n"):
        m = re.match(r"^( +)RECORD KEY IS (XF\d-K)(\.?)$", ln)
        a = re.match(r"^( +)ALTERNATE RECORD KEY IS (XF\d-A)(\.?)$", ln)
        if m:
            s = rng.randrange(len(SPELLINGS))
            counts[SPELLINGS[s]] = counts.get(SPELLINGS[s], 0) + 1
            ln = m.group(1) + SPELLINGS[s].format(k=m.group(2)) + m.group(3)
        elif a:
            s = rng.randrange(len(ALT_SPELLINGS))
            counts[ALT_SPELLINGS[s]] = counts.get(ALT_SPELLINGS[s], 0) + 1
            ln = a.group(1) + ALT_SPELLINGS[s].format(k=a.group(2)) + a.group(3)
        elif re.match(r"^ +ORGANIZATION IS SEQUENTIAL$", ln) and rng.random() < 0.3:
            counts["RECORD DELIMITER"] = counts.get("RECORD DELIMITER", 0) + 1
            ln += " RECORD DELIMITER STANDARD-1"
        if len(ln) > 72:
            raise ValueError("line too long: " + ln)
        out.append(ln)
    return "\n".join(out)


def run_one(idx, rng, outdir, keep, counts):
    name = f"F{idx:05d}"
    rs = random.Random(rng.random())
    gen = F.Gen(rng, name, F.parse_exclude("gnucobol"))
    gen.build()
    cobol, total = gen.render()
    cobol = respell(cobol, rs, counts)
    base = os.path.join(outdir, name)
    with open(base + ".cob", "w") as fh:
        fh.write(cobol)
    for p in F.data_files(outdir, name):
        if os.path.exists(p):
            os.remove(p)
    res = F.compare(gen, base, outdir, total)
    if res[0] in ("ok", "ok-abend"):
        F.cleanup(outdir, name, keep)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=os.path.join(D.ROOT, "tools", "difftest", "out_reckey"))
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--show", type=int, default=10, help="failures shown in detail")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, fails, counts = {}, [], {}
    for i in range(a.n):
        st, det = run_one(i, random.Random(rng.random()), a.out, a.keep, counts)
        F.bump(tally, a.out, i, st)
        if st not in ("ok", "ok-abend"):
            fails.append((i, st, det))
    print(json.dumps({"tally": dict(sorted(tally.items())), "clauses": dict(sorted(counts.items()))}))
    for i, st, det in fails[:a.show]:
        print(f"--- F{i:05d} {st}")
        print(json.dumps(det, indent=1)[:3000] if not isinstance(det, str) else det[:2000])
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())

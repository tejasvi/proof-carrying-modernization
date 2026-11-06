#!/usr/bin/env python3
"""Differential testing of the semantics' input-stream READ (Cobol/Sem/Exec.lean `.read`, the
statement form of hand-built IRs such as examples/recsum, with the input files given to
cobolrun by --inputs) on several files read interleaved: PREREG_M set 2 survivor #5
(Exec.lean:357, the update of the other files' remaining input records).

Each random program has 2 or 3 input files F1, F2, F3 (sequential, fixed 3-byte records) with
0 to 4 records each, and reads them in a random interleaving of up to K READs, each READ ... AT
END DISPLAY ... NOT AT END DISPLAY the record; no file is read again after its end of file (a
READ after AT END is an error in COBOL; the input-stream READ has no status for it). GnuCOBOL
runs the COBOL source on the data files; the model runs a hand-built IR of the same program
(tools/irjson.py; OPEN and CLOSE are not statements of that IR) with the same records as
cobolrun --inputs. The DISPLAY lines must agree exactly, and both runs must end normally.

usage: cov_f1inp.py --root C --out DIR [--n N] [--seed S] [--k K]
"""
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cov_common as E  # noqa: E402

CH = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"


def generate(rng, k):
    nf = rng.choice([2, 3])
    recs = {f: ["".join(rng.choice(CH) for _ in range(3)) for _ in range(rng.randint(0, 4))]
            for f in range(1, nf + 1)}
    left = {f: len(recs[f]) + 1 for f in recs}       # reads allowed, the end-of-file one included
    reads = []
    while len(reads) < k and any(left.values()):
        f = rng.choice([g for g in left if left[g]])
        reads.append(f)
        left[f] -= 1
    return recs, reads


def cobol(recs, reads):
    fs = sorted(recs)
    L = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. COVF1B.",
         "       ENVIRONMENT DIVISION.", "       INPUT-OUTPUT SECTION.", "       FILE-CONTROL."]
    for f in fs:
        L += [f"           SELECT F{f} ASSIGN TO \"f{f}.dat\"",
              "               ORGANIZATION IS SEQUENTIAL."]
    L += ["       DATA DIVISION.", "       FILE SECTION."]
    for f in fs:
        L += [f"       FD  F{f}.", f"       01  R{f} PIC X(3)."]
    L += ["       PROCEDURE DIVISION.",
          "           OPEN INPUT " + " ".join(f"F{f}" for f in fs)]
    for i, f in enumerate(reads):
        L += [f"           READ F{f}",
              f"             AT END DISPLAY 'E{i:02d} {f}|'",
              f"             NOT AT END DISPLAY 'N{i:02d} {f} ' R{f} '|'",
              "           END-READ"]
    L += ["           CLOSE " + " ".join(f"F{f}" for f in fs), "           STOP RUN."]
    return "\n".join(L) + "\n"


def ir(J, recs, reads):
    fs = sorted(recs)
    data = [J.item(f, 1, f"R{f}", J.pic_x(3)) for f in fs]
    sentences = []
    for i, f in enumerate(reads):
        sentences.append([J.read(f, J.ref(f),
                                 at_end=[{"display": {"ops": [J.o_str(f"E{i:02d} {f}|")]}}],
                                 not_at_end=[{"display": {"ops": [J.o_str(f"N{i:02d} {f} "),
                                                                  J.o_ref(f), J.o_str("|")]}}])])
    sentences.append([J.STOP_RUN])
    return J.program("COVF1B", data, [J.para("MAIN", *sentences)], config=J.GNUCOBOL)


def run_one(D, J, recs, reads, wd):
    src = cobol(recs, reads)
    bad = E.col72(src)
    if bad:
        return "gen-col72", bad
    base = os.path.join(wd, "prog")
    open(base + ".cob", "w").write(src)
    json.dump(ir(J, recs, reads), open(base + ".ir.json", "w"))
    inputs = [[f, [list(r.encode()) for r in recs[f]]] for f in sorted(recs)]
    json.dump(inputs, open(base + ".inputs.json", "w"))
    for f in recs:
        open(os.path.join(wd, f"f{f}.dat"), "wb").write("".join(recs[f]).encode())
    c = subprocess.run([D.COBC, "-x"] + E.PLAIN_COBC + ["-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return "cobc-error", c.stderr[-2000:]
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    r = subprocess.run([base], capture_output=True, env=env, timeout=20, cwd=wd,
                       stdin=subprocess.DEVNULL)
    g = r.stdout.decode("latin-1").split("\n")
    if g and g[-1] == "":
        g.pop()
    if r.returncode != 0:
        return "gnucobol-abend", {"rc": r.returncode, "err": r.stderr.decode("latin-1")[-600:]}
    lr = subprocess.run([D.COBOLRUN, base + ".ir.json", "--inputs", base + ".inputs.json"],
                        capture_output=True, text=True, timeout=60, cwd=wd)
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-2000:]
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop:"):
        return "lean-signal", {"signal": res["signal"], "model": m[-3:]}
    if g != m:
        return "mismatch", (g, m)
    return "ok", (g, m)


def main():
    ap = E.arg_parser(__doc__, 60, 12)
    args = ap.parse_args()
    D = E.difftest(args.root)
    sys.path.insert(0, os.path.join(os.path.abspath(args.root), "tools"))
    import irjson as J  # noqa: E402
    os.makedirs(args.out, exist_ok=True)
    rng = random.Random(args.seed)
    tally = {}
    with open(os.path.join(args.out, "results.jsonl"), "w") as res, \
            open(os.path.join(args.out, "details.jsonl"), "w") as det:
        for p in range(args.n):
            recs, reads = generate(rng, args.k)
            wd = os.path.join(args.out, f"p{args.seed}_{p:04d}")
            os.makedirs(wd, exist_ok=True)
            st, detail = run_one(D, J, recs, reads, wd)
            tally[st] = tally.get(st, 0) + 1
            res.write(json.dumps({"case": p, "status": st}) + "\n")
            if st != "ok":
                det.write(json.dumps({"case": p, "status": st,
                                      "first_diff": E.first_diff(*detail) if st == "mismatch" else None,
                                      "detail": None if st == "mismatch" else detail}) + "\n")
    print(json.dumps({"tally": dict(sorted(tally.items()))}))


if __name__ == "__main__":
    main()

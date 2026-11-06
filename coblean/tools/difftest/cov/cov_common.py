"""Shared part of the coverage testers (declared later validation work, 2026-10-26).

Each tester runs COBOL programs with GnuCOBOL (the reference) and with coblean's front end +
cobolrun (the model) and compares the outputs exactly: the same number of DISPLAY lines, each
line byte for byte (Latin-1, split at line feeds only, nothing stripped), GnuCOBOL ending with
exit status 0 and the model with a `stop` signal. Every DISPLAY of a program ends with '|', so
trailing spaces are inside the compared text. Every program line is checked to stay within
column 72 (status "gen-col72" otherwise: a generator defect, never a pass).

The work copy ROOT supplies GnuCOBOL (scripts/cobc.sh, third_party), the front end
(tools/cobolfe/cobolfe.py, or --fe PATH) and cobolrun (.lake/build/bin/cobolrun), through the
copy's tools/difftest/difftest.py.

Statuses: "ok" (the only pass), "mismatch", "lean-signal" (the model stopped with a fault or an
unsupported statement), "fe-unsupported" (the front end turned a construct into `unsupported`),
"fe-error", "cobc-error", "gnucobol-abend", "gnucobol-timeout", "lean-timeout", "cobolrun-error",
"gen-col72".
"""
import argparse
import json
import os
import random
import subprocess
import sys

ARITH_COBC = ["-std=ibm", "-fbinary-truncate", "-fno-arithmetic-osvs"]
ARITH_FE = ["--profile", "gnucobol", "--trunc", "std", "--div-scale", "30"]
PLAIN_COBC = ["-std=ibm"]
PLAIN_FE = ["--profile", "gnucobol"]


def difftest(root):
    sys.path.insert(0, os.path.join(os.path.abspath(root), "tools", "difftest"))
    import difftest as D  # noqa: E402
    if os.path.abspath(D.ROOT) != os.path.abspath(root):
        raise SystemExit(f"difftest.py of {D.ROOT}, not of {root}")
    return D


def col72(src):
    """Line numbers (1-based) of non-comment fixed-format lines longer than 72 columns."""
    bad = []
    for i, ln in enumerate(src.split("\n"), 1):
        if len(ln) > 6 and ln[6] in "*/":
            continue
        if len(ln) > 72:
            bad.append(i)
    return bad


def clean(d, files):
    for f in files:
        p = os.path.join(d, f)
        if os.path.exists(p):
            os.remove(p)


def run(D, src, base, cobc_flags, fe_flags, files=(), fe=None, timeout=20):
    """Run one program both ways. Returns (status, detail); detail is (gnucobol lines, model
    lines) for "ok" and "mismatch". FILES: data files in BASE's directory, removed before each
    system's run (the model's files are in memory)."""
    bad = col72(src)
    if bad:
        return "gen-col72", bad
    d = os.path.dirname(base)
    with open(base + ".cob", "w", encoding="latin-1") as fh:
        fh.write(src)
    c = subprocess.run([D.COBC, "-x"] + cobc_flags + ["-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return "cobc-error", c.stderr[-2000:]
    clean(d, files)
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    try:
        r = subprocess.run([base], capture_output=True, env=env, timeout=timeout, cwd=d,
                           stdin=subprocess.DEVNULL)
    except subprocess.TimeoutExpired:
        return "gnucobol-timeout", None
    g = r.stdout.decode("latin-1").split("\n")
    if g and g[-1] == "":
        g.pop()
    if r.returncode != 0:
        return "gnucobol-abend", {"rc": r.returncode, "out": g[-5:],
                                  "err": r.stderr.decode("latin-1")[-600:]}
    fe_path = fe or D.COBOLFE
    f = subprocess.run([sys.executable, "-I", fe_path, base + ".cob"] + fe_flags +
                       ["--main", "-o", base + ".fe.json"], capture_output=True, text=True,
                       timeout=120)
    if f.returncode != 0:
        return "fe-error", f.stderr[-2000:]
    unsup = [ln for ln in f.stderr.splitlines() if "unsupported" in ln]
    if unsup:
        return "fe-unsupported", "\n".join(unsup)[:2000]
    try:
        lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True,
                            timeout=60, cwd=d)
    except subprocess.TimeoutExpired:
        return "lean-timeout", None
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-2000:]
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop:"):
        return "lean-signal", {"signal": res["signal"], "model": m[-3:]}
    if g != m:
        return "mismatch", (g, m)
    return "ok", (g, m)


def first_diff(g, m):
    for i in range(max(len(g), len(m))):
        a = g[i] if i < len(g) else "<none>"
        b = m[i] if i < len(m) else "<none>"
        if a != b:
            return i, a, b
    return None


def main_loop(args, program, cobc_flags, fe_flags, files=(), runner=None):
    """Generate args.n programs with program(rng, k) -> source text; run; record statuses in
    OUT/results.jsonl and details of non-ok programs in OUT/details.jsonl."""
    D = difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    open(os.path.join(args.out, "details.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally = {}
    for p in range(args.n):
        src = program(rng, args.k)
        wd = os.path.join(args.out, f"p{args.seed}_{p:04d}")
        os.makedirs(wd, exist_ok=True)
        base = os.path.join(wd, "prog")
        if runner:
            status, detail = runner(D, src, base, args)
        else:
            status, detail = run(D, src, base, cobc_flags, fe_flags, files, fe=args.fe)
        tally[status] = tally.get(status, 0) + 1
        with open(os.path.join(args.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": p, "status": status}) + "\n")
        if status != "ok":
            info = {"case": p, "status": status}
            if status == "mismatch":
                info["first_diff"] = first_diff(*detail)
            else:
                info["detail"] = detail
            with open(os.path.join(args.out, "details.jsonl"), "a") as fh:
                fh.write(json.dumps(info) + "\n")
    print(json.dumps({"tally": dict(sorted(tally.items()))}))


def arg_parser(doc, n, k):
    ap = argparse.ArgumentParser(description=doc)
    ap.add_argument("--root", required=True, help="the work copy (tree + cobolrun)")
    ap.add_argument("--n", type=int, default=n)
    ap.add_argument("--k", type=int, default=k)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", required=True)
    ap.add_argument("--fe", default=None, help="front end cobolfe.py to use (default: the root's)")
    return ap


def wrap(text, indent=11, width=72):
    """Fixed-format lines from column 12, split at blanks outside literals ('...')."""
    words, cur, inq = [], "", False
    for ch in text:
        if ch == "'":
            inq = not inq
        if ch == " " and not inq:
            words.append(cur)
            cur = ""
        else:
            cur += ch
    words.append(cur)
    out, line = [], " " * indent
    for w in words:
        if not w:
            continue
        if len(line) + 1 + len(w) > width:
            out.append(line)
            line = " " * (indent + 4) + w
        else:
            line = line + (" " if line.strip() else "") + w
    out.append(line)
    return out

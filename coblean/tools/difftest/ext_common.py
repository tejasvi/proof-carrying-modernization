"""Shared part of the extended differential suite (PREREG_M_v1 set 2, coblean semantics).

Every tester of the suite generates random COBOL programs from a seed, runs each program with
GnuCOBOL (the reference) and with coblean's front end + cobolrun (the model), and compares
the two outputs exactly: the same number of DISPLAY lines, each line byte for byte (decoded
as Latin-1, nothing stripped), GnuCOBOL ending with exit status 0 and the model with a `stop`
signal. Every DISPLAY of a generated program ends with the literal '|', so trailing spaces of
an item are inside the compared text.

The work copy ROOT (the tester's --root, the harness's $C) supplies GnuCOBOL (scripts/cobc.sh
and third_party), the front end (tools/cobolfe/cobolfe.py) and cobolrun
(.lake/build/bin/cobolrun), through the copy's tools/difftest/difftest.py.

One status per program in OUT/results.jsonl ({"case": i, "status": s}). Pass: "ok" only.
Other statuses: "mismatch" (some line or the line count differs), "lean-signal" (the model
stopped with a fault or an unsupported statement), "lean-timeout", "cobolrun-error",
"fe-error", "fe-unsupported" (the front end turned a statement into `unsupported`),
"cobc-error", "gnucobol-abend", "gnucobol-timeout".
"""
import json
import os
import subprocess
import sys

# GnuCOBOL flags and front-end options of difftest.py for TRUNC(STD) (the arithmetic rows of the
# validation table); the non-arithmetic testers of the table use -std=ibm and the front end's
# defaults, as inspecttest.py does.
ARITH_COBC = ["-std=ibm", "-fbinary-truncate", "-fno-arithmetic-osvs"]
ARITH_FE = ["--profile", "gnucobol", "--trunc", "std", "--div-scale", "30"]
PLAIN_COBC = ["-std=ibm"]
PLAIN_FE = ["--profile", "gnucobol"]


def difftest(root):
    """The work copy's difftest module (paths of cobc.sh, cobolrun, the front end)."""
    sys.path.insert(0, os.path.join(os.path.abspath(root), "tools", "difftest"))
    import difftest as D  # noqa: E402
    if os.path.abspath(D.ROOT) != os.path.abspath(root):
        raise SystemExit(f"difftest.py of {D.ROOT}, not of {root}")
    return D


def run(D, src, base, cobc_flags, fe_flags, files=()):
    """Run one program both ways. Returns (status, detail); detail is the pair of line lists
    for "ok" and "mismatch". FILES: data files (in BASE's directory) removed before each run."""
    d = os.path.dirname(base)
    with open(base + ".cob", "w", encoding="latin-1") as fh:
        fh.write(src)
    c = subprocess.run([D.COBC, "-x"] + cobc_flags + ["-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return "cobc-error", c.stderr[-2000:]
    for f in files:
        for e in ("", ".1"):
            p = os.path.join(d, f + e)
            if os.path.exists(p):
                os.remove(p)
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    try:
        r = subprocess.run([base], capture_output=True, env=env, timeout=20, cwd=d)
    except subprocess.TimeoutExpired:
        return "gnucobol-timeout", None
    if r.returncode != 0:
        return "gnucobol-abend", (r.stdout[-500:] + r.stderr[-500:]).decode("latin-1")
    g = r.stdout.decode("latin-1").split("\n")
    if g and g[-1] == "":
        g.pop()
    fe = subprocess.run([sys.executable, "-I", D.COBOLFE, base + ".cob"] + fe_flags +
                        ["--main", "-o", base + ".fe.json"], capture_output=True, text=True,
                        timeout=120)
    if fe.returncode != 0:
        return "fe-error", fe.stderr[-2000:]
    unsup = [ln for ln in fe.stderr.splitlines() if "unsupported" in ln]
    if unsup:
        return "fe-unsupported", "\n".join(unsup)[:2000]
    for f in files:
        for e in ("", ".1"):
            p = os.path.join(d, f + e)
            if os.path.exists(p):
                os.remove(p)
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
        return "lean-signal", res["signal"]
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


def main_loop(args, program, cobc_flags, fe_flags, files=()):
    """Generate args.n programs with `program(rng, k)` -> source text, run, record statuses."""
    import random
    D = difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown = {}, 0
    for p in range(args.n):
        src = program(rng, args.k)
        base = os.path.join(args.out, f"p{args.seed}_{p:04d}")
        status, detail = run(D, src, base, cobc_flags, fe_flags, files)
        tally[status] = tally.get(status, 0) + 1
        with open(os.path.join(args.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": p, "status": status}) + "\n")
        if status == "ok" and not args.keep:
            for e in (".cob", "", ".fe.json"):
                if os.path.exists(base + e):
                    os.remove(base + e)
        elif status != "ok" and shown < args.show:
            shown += 1
            if status == "mismatch":
                print(f"program {p}: mismatch at line {first_diff(*detail)}")
            else:
                print(f"program {p}: {status}: {str(detail)[:600]}")
    print(json.dumps({"tally": tally}))


def arg_parser(doc, n, k):
    import argparse
    ap = argparse.ArgumentParser(description=doc)
    ap.add_argument("--root", required=True, help="the work copy (pin + cobolrun)")
    ap.add_argument("--n", type=int, default=n, help="programs")
    ap.add_argument("--k", type=int, default=k, help="statements per program")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", required=True)
    ap.add_argument("--show", type=int, default=3)
    ap.add_argument("--keep", action="store_true", help="keep the files of passing programs")
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
        if len(w) > width - indent - 4:
            raise ValueError(f"word too long for a line: {w}")
        if len(line) + 1 + len(w) > width:
            out.append(line)
            line = " " * (indent + 4) + w
        else:
            line = line + (" " if line.strip() else "") + w
    out.append(line)
    return out


def header(name, data_lines, files_section=None, select_lines=None):
    """Program text up to PROCEDURE DIVISION."""
    out = ["       IDENTIFICATION DIVISION.", f"       PROGRAM-ID. {name}."]
    if select_lines:
        out += ["       ENVIRONMENT DIVISION.", "       INPUT-OUTPUT SECTION.", "       FILE-CONTROL."]
        out += select_lines
    out += ["       DATA DIVISION."]
    if files_section:
        out += ["       FILE SECTION."] + files_section
    out += ["       WORKING-STORAGE SECTION."] + data_lines + ["       PROCEDURE DIVISION."]
    return out


def check_lines(lines):
    for ln in lines:
        if len(ln) > 72:
            raise ValueError(f"line past column 72: {ln}")
    return lines

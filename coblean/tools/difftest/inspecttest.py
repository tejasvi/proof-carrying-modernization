#!/usr/bin/env python3
"""Differential testing of INSPECT: TALLYING, REPLACING, TALLYING ... REPLACING, CONVERTING.

Each random program runs K random INSPECT statements on a 12-character item over a small
alphabet (so that patterns occur often), each with 1-3 phrases of the kinds CHARACTERS / ALL /
LEADING / FIRST, patterns of 1-2 characters (or a figurative constant), and optional
BEFORE / AFTER INITIAL delimiters; TALLYING uses up to two counters, which start from non-zero
values (fixed per statement number, so the random stream is unchanged) so that a count that is
stored instead of added shows.  After each statement the program displays the counters and the
item.  GnuCOBOL (-std=ibm) runs the program; the front end (tools/cobolfe) extracts the IR and
cobolrun runs it; the outputs must agree.

A mismatch is classified when it matches a known GnuCOBOL deviation (see KNOWN); classes in
--exclude are not generated.

usage: inspecttest.py [--n N] [--seed S] [--k K] [--out DIR] [--show K] [--exclude CLASSES]
"""
import argparse
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import difftest as D  # noqa: E402

ALPHA = "AB X"
REPL = "abxyz"

# Known deviations: class -> (who deviates from IBM, description).  All three come from
# GnuCOBOL applying the phrases one at a time over the whole item instead of the standard
# comparison cycle (at each position, the first phrase that matches there).
KNOWN = {
    "G-lead": ("gnucobol", "LEADING followed by another phrase: positions of the leading run are "
                           "counted again by later phrases (LEADING 'A' then CHARACTERS on "
                           "'AAB…' (20 chars): 2 + 19)"),
    "G-order": ("gnucobol", "a later phrase whose pattern starts before an earlier phrase's match: "
                            "the earlier phrase wins (ALL 'A' BY 'y', ALL ' A' BY 'bx' on 'BABAX "
                            "AXBBXA': GnuCOBOL 'ByByX yXBB…', IBM 'ByByXbxXBB…')"),
    "G-chars2": ("gnucobol", "two CHARACTERS phrases: the second (never applicable) changes the "
                             "result"),
}


def lit(s):
    return "'" + s + "'"


def rnd_item(rng):
    return "".join(rng.choice(ALPHA) for _ in range(12))


def rnd_pat(rng, n=None):
    if n is None:
        n = rng.choice([1, 1, 1, 2])
    if n == 1 and rng.random() < 0.15:
        return "SPACE", 1
    return lit("".join(rng.choice("AB X") for _ in range(n))), n


def rnd_rep(rng, n):
    if n == 1 and rng.random() < 0.15:
        return rng.choice(["ZERO", "SPACE"])
    return lit("".join(rng.choice(REPL) for _ in range(n)))


def rnd_bounds(rng):
    out = []
    if rng.random() < 0.3:
        out.append("BEFORE INITIAL " + rnd_pat(rng)[0])
    if rng.random() < 0.3:
        out.append("AFTER INITIAL " + rnd_pat(rng)[0])
    rng.shuffle(out)
    return " ".join(out)


SAFE = {"multi1": True}   # multi-phrase statements: single-character patterns, no LEADING


def tally_clause(rng):
    """TALLYING clause text and the set of phrase kinds used (in order)."""
    parts, kinds = [], []
    ctrs = rng.sample(["C1", "C2"], rng.choice([1, 1, 2]))
    for ctr in ctrs:
        phrases = []
        # one phrase per counter: GnuCOBOL 3.2 rejects e.g. `FOR CHARACTERS LEADING 'A'`
        for _ in range(1):
            multi = len(ctrs) > 1 and SAFE["multi1"]
            k = rng.choice(["CHARACTERS", "ALL"] if multi else ["CHARACTERS", "ALL", "LEADING"])
            if multi and k == "CHARACTERS" and "CHARACTERS" in kinds:
                k = "ALL"
            kinds.append(k)
            if k == "CHARACTERS":
                phrases.append(("CHARACTERS " + rnd_bounds(rng)).strip())
            else:
                p, _ = rnd_pat(rng, 1 if multi else None)
                phrases.append((k + " " + p + " " + rnd_bounds(rng)).strip())
        parts.append(ctr + " FOR " + " ".join(phrases))
    return "TALLYING " + " ".join(parts), kinds


def replace_clause(rng):
    phrases, kinds = [], []
    nph = rng.choice([1, 1, 2, 3])
    for _ in range(nph):
        multi = nph > 1 and SAFE["multi1"]
        k = rng.choice(["CHARACTERS", "ALL", "FIRST"] if multi else ["CHARACTERS", "ALL", "LEADING", "FIRST"])
        if multi and k == "CHARACTERS" and "CHARACTERS" in kinds:
            k = "ALL"
        kinds.append(k)
        if k == "CHARACTERS":
            phrases.append(("CHARACTERS BY " + rnd_rep(rng, 1) + " " + rnd_bounds(rng)).strip())
        else:
            p, n = rnd_pat(rng, 1 if multi else None)
            phrases.append((k + " " + p + " BY " + rnd_rep(rng, n) + " " + rnd_bounds(rng)).strip())
    return "REPLACING " + " ".join(phrases), kinds


def convert_clause(rng):
    n = rng.choice([1, 2, 3])
    src = "".join(rng.sample("AB X", n))
    dst = "".join(rng.choice(REPL) for _ in range(n))
    return ("CONVERTING " + lit(src) + " TO " + lit(dst) + " " + rnd_bounds(rng)).strip(), []


def rnd_stmt(rng):
    r = rng.random()
    if r < 0.35:
        c, kinds = tally_clause(rng)
    elif r < 0.7:
        c, kinds = replace_clause(rng)
    elif r < 0.85:
        t, k1 = tally_clause(rng)
        rp, k2 = replace_clause(rng)
        c, kinds = t + " " + rp, k1 + k2
    else:
        c, kinds = convert_clause(rng)
    return c, kinds


def value(op):
    """Characters of a pattern / delimiter operand of the generator."""
    return " " if op == "SPACE" else op.strip("'")


def ambiguous(item, clause):
    """Some phrase has both delimiters and the first BEFORE occurrence lies before the end of
    the AFTER delimiter (the model reports such statements as unsupported)."""
    toks, cur, inq = [], "", False
    for ch in clause:
        if ch == "'":
            inq = not inq
            cur += ch
        elif ch == " " and not inq:
            toks.append(cur)
            cur = ""
        else:
            cur += ch
    toks.append(cur)
    toks = [t for t in toks if t]
    # each phrase's delimiters: scan for BEFORE/AFTER INITIAL x, phrases separated by kinds
    phrases, cur = [], {}
    for i, t in enumerate(toks):
        if t in ("CHARACTERS", "ALL", "LEADING", "FIRST", "CONVERTING") or (
                i + 1 < len(toks) and toks[i + 1] == "FOR"):
            phrases.append(cur)
            cur = {}
        if t in ("BEFORE", "AFTER") and i + 2 < len(toks):
            cur[t] = value(toks[i + 2])
        if t not in ("BEFORE", "AFTER", "INITIAL", "BY", "TO", "FOR", "TALLYING", "REPLACING") \
                and not t.startswith("'") and t != "SPACE" and t not in ("ZERO",) and i > 0 \
                and toks[i - 1] not in ("INITIAL",) and t in ("ALL", "LEADING", "FIRST"):
            pass
    phrases.append(cur)
    for p in phrases:
        if "BEFORE" in p and "AFTER" in p:
            a, b = p["AFTER"], p["BEFORE"]
            ia = item.find(a)
            ib = item.find(b)
            if ia >= 0 and ib >= 0 and ib < ia + len(a):
                return True
    return False


def classify(stmt_kinds_tally):
    """Known-deviation class of a statement from the phrase kinds of its TALLYING clause."""
    k = stmt_kinds_tally
    if "LEADING" in k and k.index("LEADING") < len(k) - 1:
        return "G-lead"
    return None


def wrap(text, indent=11, width=72):
    """COBOL fixed-format lines (area B from column 12), splitting at blanks outside literals."""
    words, cur, out, inq = [], "", [], False
    for ch in text:
        if ch == "'":
            inq = not inq
        if ch == " " and not inq:
            words.append(cur)
            cur = ""
        else:
            cur += ch
    words.append(cur)
    line = " " * indent
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


def program(rng, k, exclude):
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. INSPT.",
             "       DATA DIVISION.", "       WORKING-STORAGE SECTION.",
             "       01  S PIC X(12).", "       01  C1 PIC 9(4).", "       01  C2 PIC 9(4).",
             "       PROCEDURE DIVISION."]
    stmts = []
    while len(stmts) < k:
        item = rnd_item(rng)
        c, kinds = rnd_stmt(rng)
        tk = []
        if c.startswith("TALLYING"):
            # phrase kinds of the TALLYING clause only
            tk = [x for x in kinds[:len(kinds)] if x in ("CHARACTERS", "ALL", "LEADING")]
            if "REPLACING" in c:
                nrep = c.split("REPLACING", 1)[1].count(" BY ")
                tk = kinds[:len(kinds) - nrep]
        cls = classify(tk)
        if cls in exclude or ambiguous(item, c):
            continue
        stmts.append((item, c, cls))
    for i, (item, c, _) in enumerate(stmts):
        lines.append(f"           MOVE {lit(item)} TO S")
        # non-zero counters (TALLYING adds to them); at most 1002 + 24 fits PIC 9(4)
        lines.append(f"           MOVE {(i * 37) % 1000 + 1} TO C1")
        lines.append(f"           MOVE {(i * 53) % 1000 + 2} TO C2")
        lines += wrap("INSPECT S " + c)
        lines.append(f"           DISPLAY 'S{i:02d} ' C1 ' ' C2 ' ' S")
    lines.append("           STOP RUN.")
    return "\n".join(lines) + "\n", stmts


def run(src, base):
    with open(base + ".cob", "w") as fh:
        fh.write(src)
    c = subprocess.run([D.COBC, "-x", "-std=ibm", "-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return None, "cobc: " + c.stderr
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    r = subprocess.run([base], capture_output=True, env=env, timeout=20)
    gout = r.stdout.decode("latin-1")
    fe = subprocess.run([sys.executable, "-I", D.COBOLFE, base + ".cob", "--profile", "gnucobol",
                         "--main", "-o", base + ".fe.json"], capture_output=True, text=True,
                        timeout=120)
    if fe.returncode != 0:
        return None, "cobolfe: " + fe.stderr
    lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True,
                        timeout=60)
    if lr.returncode != 0:
        return None, "cobolrun: " + lr.stderr
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop"):
        m.append("<model: " + res["signal"] + ">")
    return (gout.splitlines(), m), None


def bump(tally, out, case, status):
    """Count one case and append it to OUT/results.jsonl (one JSON object per case)."""
    tally[status] = tally.get(status, 0) + 1
    with open(os.path.join(out, "results.jsonl"), "a") as fh:
        fh.write(json.dumps({"case": case, "status": status}) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=25)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                  "out_inspect"))
    ap.add_argument("--show", type=int, default=3)
    ap.add_argument("--exclude", default="G-lead")
    ap.add_argument("--unsafe", action="store_true",
                    help="also multi-phrase statements outside the subset where GnuCOBOL's "
                         "phrase-by-phrase processing equals the standard comparison cycle")
    args = ap.parse_args()
    SAFE["multi1"] = not args.unsafe
    exclude = set(x for x in args.exclude.split(",") if x)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally = {"ok": 0}
    shown = 0
    for p in range(args.n):
        src, stmts = program(rng, args.k, exclude)
        base = os.path.join(args.out, f"insp_{args.seed}_{p}")
        outs, err = run(src, base)
        if err:
            bump(tally, args.out, p, "error")
            print(f"program {p}: {err}")
            continue
        g, m = outs
        bad = [(i, a, b) for i, (a, b) in enumerate(zip(g, m)) if a.rstrip() != b.rstrip()]
        if len(g) != len(m):
            bad.append((min(len(g), len(m)), "<length>", "<length>"))
        if not bad:
            bump(tally, args.out, p, "ok")
            for e in (".cob", "", ".fe.json"):
                if os.path.exists(base + e):
                    os.remove(base + e)
            continue
        cls = stmts[bad[0][0]][2] if bad[0][0] < len(stmts) else None
        key = cls or "mismatch"
        bump(tally, args.out, p, key)
        if shown < args.show:
            shown += 1
            for i, a, b in bad[:3]:
                st = stmts[i] if i < len(stmts) else ("", "", None)
                print(f"program {p} stmt {i} [{st[2] or 'new'}]: item {st[0]!r} INSPECT S {st[1]}")
                print(f"   gnucobol: {a!r}")
                print(f"   model   : {b!r}")
    print(json.dumps({"tally": tally, "exclude": sorted(exclude)}))


if __name__ == "__main__":
    main()

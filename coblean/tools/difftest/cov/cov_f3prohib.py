#!/usr/bin/env python3
"""ROUNDED MODE IS PROHIBITED checked against an exact-rational oracle (not GnuCOBOL: GnuCOBOL 3.2
raises the size error condition on every PROHIBITED statement, exact results included; see
cov_f3round.py). PREREG_M set 2 survivor #11 (Cobol/Sem/Arith.lean quotExact, the exactness test
of a quotient whose receiver has fewer decimals than dividend minus divisor) sits here.

Rule checked (COBOL 2014 ROUNDED MODE PROHIBITED, with ON SIZE ERROR): if the exact result of
the operation is not representable in the receiver (it needs more decimal places than the
receiver has, or more integer digits) or a divisor is zero, the size error condition holds:
the receiver keeps its value and ON SIZE ERROR runs; otherwise the result is stored and NOT
ON SIZE ERROR runs.

Each random program runs K statements on operands A0 (S9(4)), A1 (S9(3)V9), A2 (S9(3)V99),
A3 (S9(2)V999) and receivers R0 (S9(5)), R1 (S9(4)V9), R2 (S9(3)V99): COMPUTE r = x op y (op +,
-, *, /), DIVIDE x BY y GIVING r, DIVIDE y INTO r, MULTIPLY x BY y GIVING r, ADD x TO r,
SUBTRACT x FROM r, all ROUNDED MODE IS PROHIBITED with ON SIZE ERROR and NOT ON SIZE ERROR.
Quotients are made exact about half the time (x = y * q), including dividends with more
decimals than the receiver. Only the model runs (front end + cobolrun, TRUNC(STD) options); its
DISPLAY lines must equal the oracle's exactly.

usage: cov_f3prohib.py --root C --out DIR [--n N] [--seed S] [--k K]
"""
import json
import os
import random
import subprocess
import sys
from fractions import Fraction as Q

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cov_common as E  # noqa: E402

OPS = {"A0": (4, 0), "A1": (3, 1), "A2": (3, 2), "A3": (2, 3)}
RCV = {"R0": (5, 0), "R1": (4, 1), "R2": (3, 2)}


def fits(v, digits, scale):
    return (v * 10 ** scale).denominator == 1 and abs(v) < Q(10) ** (digits - scale) / 1


def text(v, scale):
    s = "-" if v < 0 else ""
    a = abs(v)
    i = int(a)
    if scale == 0:
        return f"{s}{i}"
    f = int((a - i) * 10 ** scale)
    return f"{s}{i}.{f:0{scale}d}"


def rnd(rng, item):
    ip, sc = OPS[item] if item in OPS else RCV[item]
    while True:
        v = Q(rng.randint(-(10 ** (ip + sc)) + 1, 10 ** (ip + sc) - 1), 10 ** sc)
        if rng.random() < 0.5:                       # small values make exact results likelier
            v = Q(rng.randint(-99, 99), 10 ** rng.randint(0, sc))
        if fits(v, ip + sc, sc):
            return v


def edited(v):
    """PIC -9(5).9(4) of v."""
    a = abs(v)
    i = int(a)
    f = int((a - i) * 10000)
    return ("-" if v < 0 else " ") + f"{i:05d}.{f:04d}"


# dividend, divisor, receiver with fewer receiver decimals than dividend minus divisor decimals
LOWSCALE = [("A2", "A0", "R0"), ("A2", "A0", "R1"), ("A3", "A0", "R0"), ("A3", "A0", "R1"),
            ("A3", "A0", "R2"), ("A3", "A1", "R0"), ("A3", "A1", "R1"), ("A2", "A1", "R0")]


def statement(rng, i, state):
    form = rng.choice(["c+", "c-", "c*", "c/", "div", "into", "mul", "add", "sub"])
    low = form in ("c/", "div") and rng.random() < 0.5
    if low:
        x, y, rv = rng.choice(LOWSCALE)
    else:
        x = rng.choice(list(OPS))
        y = rng.choice([o for o in OPS if o != x])
        rv = rng.choice(list(RCV))
    rd, rs = RCV[rv]
    xd, xs = OPS[x]
    xv, yv = rnd(rng, x), rnd(rng, y)
    if form in ("c/", "div") and rng.random() < 0.6:
        # an exact quotient: x = y * q, when it fits x; for the low-scale cases q has at most
        # the receiver's decimals, so the quotient is representable unless it is too large
        for _ in range(40):
            if low:
                q = Q(rng.randint(-99, 99), 10 ** rng.randint(0, rs))
            else:
                q = Q(rng.randint(-99, 99), rng.choice([1, 1, 2, 4, 5, 10, 20, 25, 100]))
            if yv != 0 and fits(yv * q, xd + xs, xs):
                xv = yv * q
                break
    rstart = rnd(rng, rv)
    lines = [f"MOVE {text(xv, OPS[x][1])} TO {x}", f"MOVE {text(yv, OPS[y][1])} TO {y}",
             f"MOVE {text(rstart, rs)} TO {rv}", "MOVE ' ' TO F"]
    m = "ROUNDED MODE IS PROHIBITED"
    if form[0] == "c":
        op = form[1]
        s = f"COMPUTE {rv} {m} = {x} {op} {y}"
        end = "END-COMPUTE"
        res = {"+": lambda: xv + yv, "-": lambda: xv - yv, "*": lambda: xv * yv,
               "/": lambda: None if yv == 0 else xv / yv}[op]()
    elif form == "div":
        s, end = f"DIVIDE {x} BY {y} GIVING {rv} {m}", "END-DIVIDE"
        res = None if yv == 0 else xv / yv
    elif form == "into":
        s, end = f"DIVIDE {y} INTO {rv} {m}", "END-DIVIDE"
        res = None if yv == 0 else rstart / yv
    elif form == "mul":
        s, end = f"MULTIPLY {x} BY {y} GIVING {rv} {m}", "END-MULTIPLY"
        res = xv * yv
    elif form == "add":
        s, end = f"ADD {x} TO {rv} {m}", "END-ADD"
        res = rstart + xv
    else:
        s, end = f"SUBTRACT {x} FROM {rv} {m}", "END-SUBTRACT"
        res = rstart - xv
    s += f" ON SIZE ERROR MOVE 'E' TO F NOT ON SIZE ERROR MOVE 'K' TO F {end}"
    if res is not None and fits(res, rd + rs, rs):
        rnew, flag = res, "K"
    else:
        rnew, flag = rstart, "E"
    out = ["           " + l for l in lines] + E.wrap(s)
    out += [f"           MOVE {rv} TO E", f"           DISPLAY 'P{i:02d} ' E ' ' F '|'"]
    state.append(f"P{i:02d} {edited(rnew)} {flag}|")
    return out


def program(rng, k):
    exp = []
    L = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. COVF3P.",
         "       DATA DIVISION.", "       WORKING-STORAGE SECTION."]
    for nm, (ip, sc) in list(OPS.items()) + list(RCV.items()):
        pic = f"S9({ip})" + (f"V9({sc})" if sc else "")
        L.append(f"       01  {nm} PIC {pic} VALUE 0.")
    L += ["       01  E PIC -9(5).9(4).", "       01  F PIC X VALUE ' '.", "       PROCEDURE DIVISION."]
    for i in range(k):
        L += statement(rng, i, exp)
    L.append("           STOP RUN.")
    return "\n".join(L) + "\n", exp


def run_model(D, src, base, fe=None):
    bad = E.col72(src)
    if bad:
        return "gen-col72", bad
    open(base + ".cob", "w").write(src)
    f = subprocess.run([sys.executable, "-I", fe or D.COBOLFE, base + ".cob"] + E.ARITH_FE +
                       ["--main", "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if f.returncode != 0:
        return "fe-error", f.stderr[-2000:]
    if any("unsupported" in ln for ln in f.stderr.splitlines()):
        return "fe-unsupported", f.stderr[-2000:]
    lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True, timeout=60)
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-2000:]
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop:"):
        return "lean-signal", {"signal": res["signal"], "model": m[-3:]}
    return "ran", m


def main():
    ap = E.arg_parser(__doc__, 60, 15)
    args = ap.parse_args()
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    rng = random.Random(args.seed)
    tally = {}
    with open(os.path.join(args.out, "results.jsonl"), "w") as res, \
            open(os.path.join(args.out, "details.jsonl"), "w") as det:
        for p in range(args.n):
            src, exp = program(rng, args.k)
            wd = os.path.join(args.out, f"p{args.seed}_{p:04d}")
            os.makedirs(wd, exist_ok=True)
            st, m = run_model(D, src, os.path.join(wd, "prog"), args.fe)
            if st == "ran":
                st = "ok" if m == exp else "mismatch"
            tally[st] = tally.get(st, 0) + 1
            res.write(json.dumps({"case": p, "status": st}) + "\n")
            if st != "ok":
                det.write(json.dumps({"case": p, "status": st,
                                      "first_diff": E.first_diff(exp, m) if st == "mismatch" else None,
                                      "detail": None if st == "mismatch" else m}) + "\n")
    print(json.dumps({"tally": dict(sorted(tally.items()))}))


if __name__ == "__main__":
    main()

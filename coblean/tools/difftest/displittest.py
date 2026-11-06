#!/usr/bin/env python3
"""Differential testing of DISPLAY with numeric literal operands.

IBM Enterprise COBOL 6.4: DISPLAY "literal-1 Can be any literal"; "The size of the sending field is the
total byte count of all operands listed." Numeric literals: "If a decimal point is included, it is
treated as an assumed decimal point (that is, as not taking up a character position in the literal)";
"The size of a numeric literal is equal to the number of digits specified by the user." So an unsigned
numeric literal is displayed as its digits, as written, without the decimal point (1.5 as 15, 0.05 as
005, .5 as 5, 100.00 as 10000), as GnuCOBOL 3.2 does. IBM gives no form for the sign of a signed
literal: the front end makes a DISPLAY of a signed numeric literal unsupported ("DISPLAY of a signed
numeric literal").

Each random program has a few alphanumeric and unsigned numeric DISPLAY items with VALUEs; each of its
steps DISPLAYs one to four operands among alphanumeric literals, unsigned numeric literals (integers and
decimals, with leading and trailing zeros, a leading point, up to 18 digits), the items, ZERO and SPACE,
every line starting with its step label and ending with '|'. A quarter of the programs also have one
DISPLAY of a signed numeric literal (+ or -, integer or decimal): the front end must report that
statement as unsupported (status ok-unsup); the other programs must agree with GnuCOBOL -std=ibm on
every line (status ok).
Statuses: ok, ok-unsup, unsup-missing (a signed literal not reported), and the ext_common statuses.

usage: displittest.py --root C --out DIR [--n N] [--seed S] [--k K] [--show K]
       displittest.py --root C --out DIR --run PROG.cob...
"""
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402
from classtest import run_files  # noqa: E402

MSG = "DISPLAY of a signed numeric literal"


def numlit(rng):
    """An unsigned numeric literal as written: (text, has a decimal point)."""
    i = rng.choice([0, 1, 1, 2, 3, 5, 8])
    f = rng.choice([0, 0, 1, 2, 2, 3, 5])
    if i + f == 0 or i + f > 18:
        i = max(1, min(i, 18 - f))
    ip = "".join(rng.choice("0123456789") for _ in range(i))
    if ip and rng.random() < 0.25:
        ip = "0" + ip[1:]                          # a leading zero
    fp = "".join(rng.choice("0123456789") for _ in range(f))
    if fp and rng.random() < 0.25:
        fp = fp[:-1] + "0"                         # a trailing zero
    if not f:
        return (ip or "0"), False
    if not ip or (rng.random() < 0.15 and ip == "0"):
        return "." + fp, True                      # a leading point
    return ip + "." + fp, True


class Gen:
    def __init__(self, rng, k):
        self.rng, self.k = rng, k
        self.items = {f"X{j}": rng.randint(1, 8) for j in (1, 2)}
        self.nums = {f"N{j}": rng.randint(1, 6) for j in (1, 2)}
        self.signed = rng.random() < 0.25
        self.tally = {"num_ops": 0, "dec_ops": 0, "int_ops": 0, "signed_ops": 0}

    def data(self):
        rng, d = self.rng, []
        for nm, n in self.items.items():
            d.append(f'       01  {nm} PIC X({n}) VALUE "{"".join(rng.choice("ABCXYZ 12") for _ in range(n))}".')
        for nm, n in self.nums.items():
            d.append(f"       01  {nm} PIC 9({n}) VALUE {rng.randint(0, 10 ** n - 1)}.")
        return d

    def operand(self):
        rng = self.rng
        r = rng.random()
        if r < 0.55:
            t, dec = numlit(rng)
            self.tally["num_ops"] += 1
            self.tally["dec_ops" if dec else "int_ops"] += 1
            return t
        if r < 0.7:
            return f"'{rng.choice(['A', 'XY', ' ', '=', 'Q R'])}'"
        if r < 0.85:
            return rng.choice(sorted(self.items) + sorted(self.nums))
        return rng.choice(["ZERO", "SPACE"])

    def program(self):
        rng, proc = self.rng, []
        sig_at = rng.randrange(self.k) if self.signed else -1
        for n in range(self.k):
            ops = [self.operand() for _ in range(rng.choice([1, 1, 2, 3, 4]))]
            if n == sig_at:
                t, _ = numlit(rng)
                ops.insert(rng.randrange(len(ops) + 1), rng.choice("+-") + t)
                self.tally["signed_ops"] += 1
            proc += E.wrap(f"DISPLAY 'S{n:02d} [' " + " ".join(ops) + " '|'")
        hdr = E.header("DISPLIT", self.data())
        return "\n".join(E.check_lines(hdr + proc + ["           STOP RUN."])) + "\n"


def main():
    ap = E.arg_parser(__doc__, 60, 15)
    ap.add_argument("--run", nargs="+", metavar="PROG.cob")
    args = ap.parse_args()
    if args.run:
        sys.exit(run_files(args))
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    statuses, cov, shown = {}, {}, 0
    for p in range(args.n):
        gen = Gen(rng, args.k)
        src = gen.program()
        base = os.path.join(args.out, f"p{args.seed}_{p:04d}")
        status, detail = E.run(D, src, base, E.PLAIN_COBC, E.PLAIN_FE)
        if gen.signed:
            status = "ok-unsup" if status == "fe-unsupported" and MSG in str(detail) else \
                ("unsup-missing" if status in ("ok", "mismatch") else status)
        for k, v in gen.tally.items():
            cov[k] = cov.get(k, 0) + v
        statuses[status] = statuses.get(status, 0) + 1
        with open(os.path.join(args.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": p, "status": status}) + "\n")
        if status not in ("ok", "ok-unsup") and shown < args.show:
            shown += 1
            if status == "mismatch":
                print(f"program {p}: mismatch at line {E.first_diff(*detail)}")
            else:
                print(f"program {p}: {status}: {str(detail)[:600]}")
    with open(os.path.join(args.out, "coverage.json"), "w") as fh:
        json.dump({"statuses": statuses, "coverage": cov}, fh, indent=1, sort_keys=True)
    print(json.dumps({"tally": statuses}))
    print(json.dumps(cov, sort_keys=True))
    # exit status 0 when every program passed (ok, ok-unsup), 1 otherwise
    sys.exit(0 if all(s in ("ok", "ok-unsup") for s in statuses) else 1)


if __name__ == "__main__":
    main()

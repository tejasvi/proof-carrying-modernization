#!/usr/bin/env python3
"""Differential testing of MOVE into JUSTIFIED RIGHT items, group senders above all.

IBM Enterprise COBOL 6.4: "A group move is treated as though it were an alphanumeric-to-alphanumeric
elementary move, except that there is no conversion of data from one form of internal representation
to another" (Group moves); an alphanumeric receiver gets "Alignment and any necessary space filling or
truncation ... as described under Alignment rules" (Elementary move rules), where "If the JUSTIFIED
clause is specified for this receiving item, the above rule is modified as described in JUSTIFIED
clause"; JUSTIFIED clause: "the data is aligned at the rightmost character position in the receiving
item ... If the sending item is larger than the receiving item, the leftmost character positions are
truncated." So a group moved to a JUSTIFIED RIGHT item is right-justified (NIST NC107A JUST-TEST-04).
A group receiver is filled from the left whatever JUSTIFIED items it contains.

Each random program has three groups G1 .. G3 of one to three alphanumeric or unsigned numeric DISPLAY
members (1 to 14 bytes in all, with VALUEs), JUSTIFIED RIGHT receivers J1 .. J4 (PIC X(n), 1 to 12)
and JA (PIC A(n)), a table T1 of three JUSTIFIED elements TJ, a group H1 holding a JUSTIFIED member HJ
and an alphanumeric member HX, and an alphanumeric item X1 without JUSTIFIED. Each of its steps either
moves literals into group members, or moves a group to one to three receivers (J1 .. J4, JA, TJ with a
literal or a data-name subscript, HJ, H1, X1), or moves another sender to a JUSTIFIED receiver (a
reference modification of a group, a group member, an alphanumeric literal, SPACE, ZERO, QUOTE,
ALL literal); every receiver is displayed after each MOVE (T1 and H1 whole). GnuCOBOL 3.2 -std=ibm
(which right-justifies a group sender as IBM does) and the front end + cobolrun (--profile gnucobol)
must agree on every line.
Statuses: ok, mismatch and the other ext_common statuses.

usage: justtest.py --root C --out DIR [--n N] [--seed S] [--k K] [--show K]
       justtest.py --root C --out DIR --run PROG.cob...
"""
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402
from classtest import run_files  # noqa: E402

LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


def alit(rng, n):
    """An alphanumeric literal of n characters (letters, digits, some spaces)."""
    return "".join(rng.choice(LETTERS + "0123456789  ") for _ in range(n))


class Gen:
    def __init__(self, rng, k):
        self.rng, self.k = rng, k
        self.groups = {}
        for g in ("G1", "G2", "G3"):
            mem, total = [], 0
            for m in range(rng.choice([1, 2, 2, 3])):
                n = rng.randint(1, 6)
                if total + n > 14:
                    break
                kind = rng.choice(["X", "X", "9"])
                mem.append((f"{g}M{m + 1}", kind, n))
                total += n
            self.groups[g] = mem
        self.j = {f"J{i}": rng.randint(1, 12) for i in range(1, 5)}
        self.ja = rng.randint(1, 8)
        self.tj = rng.randint(1, 8)
        self.hj, self.hx = rng.randint(1, 8), rng.randint(1, 4)
        self.x1 = rng.randint(1, 12)
        self.tally = {}

    def glen(self, g):
        return sum(n for _, _, n in self.groups[g])

    def data(self):
        d = []
        rng = self.rng
        for g, mem in self.groups.items():
            d.append(f"       01  {g}.")
            for nm, kind, n in mem:
                v = f'"{alit(rng, n)}"' if kind == "X" else str(rng.randint(0, 10 ** n - 1))
                d.append(f"           05  {nm} PIC {kind}({n}) VALUE {v}.")
        for nm, n in self.j.items():
            d.append(f"       01  {nm} PIC X({n}) JUSTIFIED RIGHT.")
        d += [f"       01  JA PIC A({self.ja}) JUST.",
              "       01  T1 VALUE SPACES.", f"           05  TJ PIC X({self.tj}) JUST OCCURS 3.",
              "       01  H1 VALUE SPACES.", f"           05  HJ PIC X({self.hj}) JUSTIFIED RIGHT.",
              f"           05  HX PIC X({self.hx}).", f"       01  X1 PIC X({self.x1}).",
              "       01  I1 PIC 9 VALUE 1."]
        return d

    def bump(self, k):
        self.tally[k] = self.tally.get(k, 0) + 1

    def show(self, n, r):
        """DISPLAY of receiver r (T1 and H1 whole)."""
        if r.startswith("TJ"):
            return f"DISPLAY 'S{n:02d} T1[' T1 ']'"
        if r == "HJ":
            return f"DISPLAY 'S{n:02d} H1[' H1 ']'"
        return f"DISPLAY 'S{n:02d} {r}[' {r} ']'"

    def step(self, n):
        rng, out = self.rng, []
        r = rng.random()
        if r < 0.25:
            g = rng.choice(sorted(self.groups))
            for nm, kind, k in self.groups[g]:
                if rng.random() < 0.7:
                    v = f'"{alit(rng, rng.randint(1, k))}"' if kind == "X" else str(rng.randint(0, 10 ** k - 1))
                    out.append(f"MOVE {v} TO {nm}")
            out.append(f"DISPLAY 'S{n:02d} {g}[' {g} ']'")
            return out
        if r < 0.75:
            g = rng.choice(sorted(self.groups))
            pool = sorted(self.j) + ["JA", "TJ (2)", "TJ (I1)", "HJ", "H1", "X1"]
            rcv = rng.sample(pool, rng.choice([1, 1, 2, 3]))
            if any(x.startswith("TJ") for x in rcv):
                out.append(f"MOVE {rng.randint(1, 3)} TO I1")
            out += E.wrap(f"MOVE {g} TO {' '.join(rcv)}")
            for x in rcv:
                out.append(self.show(n, x))
                ln = {"JA": self.ja, "HJ": self.hj, "H1": self.hj + self.hx, "X1": self.x1}.get(
                    x, self.tj if x.startswith("TJ") else self.j.get(x))
                kind = "group>" + ("group" if x == "H1" else "alnum" if x == "X1" else "just")
                rel = "shorter" if self.glen(g) < ln else "longer" if self.glen(g) > ln else "equal"
                self.bump(f"{kind}:{rel}")
            return out
        dst = rng.choice(sorted(self.j) + ["JA", "TJ (I1)", "HJ"])
        dlen = {"JA": self.ja, "HJ": self.hj}.get(dst, self.tj if dst.startswith("TJ") else self.j.get(dst))
        g = rng.choice(sorted(self.groups))
        c = rng.choice(["refmod", "member", "lit", "fig"])
        # into the alphabetic JA only alphanumeric senders of letters and spaces (IBM: no numeric sender);
        # no numeric member longer than its JUSTIFIED receiver (GnuCOBOL departs: README)
        mem = [m for m in self.groups[g] if m[1] == "X" or (dst != "JA" and m[2] <= dlen)]
        if c == "member" and not mem:
            c = "refmod"
        if c == "refmod":
            L = self.glen(g)
            a = rng.randint(1, L)
            src = f"{g} ({a}:{rng.randint(1, L - a + 1)})"
        elif c == "member":
            src = rng.choice(mem)[0]
        elif c == "lit":
            n = rng.randint(1, 14)
            src = f'"{"".join(rng.choice(LETTERS + " ") for _ in range(n)) if dst == "JA" else alit(rng, n)}"'
        else:
            src = rng.choice(["SPACES", "QUOTE", 'ALL "AB"', 'ALL "Q"'] + ([] if dst == "JA" else ["ZERO"]))
        if dst.startswith("TJ"):
            out.append(f"MOVE {rng.randint(1, 3)} TO I1")
        out += E.wrap(f"MOVE {src} TO {dst}")
        out.append(self.show(n, dst))
        self.bump(f"{c}>just")
        return out

    def program(self):
        proc = []
        for n in range(self.k):
            for ln in self.step(n):
                proc += E.wrap(ln) if not ln.startswith(" ") else [ln]
        hdr = E.header("JUSTT", self.data())
        return "\n".join(E.check_lines(hdr + proc + ["           STOP RUN."])) + "\n"


def main():
    ap = E.arg_parser(__doc__, 60, 20)
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
        statuses[status] = statuses.get(status, 0) + 1
        for k, v in gen.tally.items():
            cov[k] = cov.get(k, 0) + v
        with open(os.path.join(args.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": p, "status": status}) + "\n")
        if status != "ok" and shown < args.show:
            shown += 1
            if status == "mismatch":
                print(f"program {p}: mismatch at line {E.first_diff(*detail)}")
            else:
                print(f"program {p}: {status}: {str(detail)[:600]}")
    with open(os.path.join(args.out, "coverage.json"), "w") as fh:
        json.dump({"statuses": statuses, "coverage": cov}, fh, indent=1, sort_keys=True)
    print(json.dumps({"tally": statuses}))
    print(json.dumps(cov, sort_keys=True))
    # exit status 0 when every program passed, 1 otherwise
    sys.exit(0 if all(s == "ok" for s in statuses) else 1)


if __name__ == "__main__":
    main()

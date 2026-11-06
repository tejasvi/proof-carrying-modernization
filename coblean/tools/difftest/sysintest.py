#!/usr/bin/env python3
"""Differential testing of ACCEPT from the system input device (IBM ACCEPT format 1, SYSIN).

IBM Enterprise COBOL 6.4 (ACCEPT statement, Data transfer, "System input device"): "The system input
device is read until the receiving area is filled or EOF is encountered. If the length of the
receiving area is not an even multiple of the system input device record length, the final record
will be truncated as required. If EOF is encountered after data has been moved and before the
receiving area has been filled, the receiving area is padded with spaces of the appropriate
representation for the receiving area. If EOF is encountered before any data has been moved to the
receiving area, padding will not take place and the contents of the receiving area are unchanged.
Each input record is concatenated with the previous input record." and "There is no editing or error
checking of the incoming data." The model: Stmt.accept, Sem.sysinRead (Cobol/Sem/Exec.lean); the
records come from cobolrun --sysin.

Each random program declares receivers of every kind IBM allows (identifier-1: "An alphanumeric group
item" or "An elementary data item of usage DISPLAY"): X1, X2 alphanumeric, A1 alphabetic, N1 unsigned
numeric DISPLAY, G1 a group of an alphanumeric, a numeric and an alphanumeric item, the table T1 of
four TE elements (subscripted by the data name IX or a literal), a reference-modified X1, J1
JUSTIFIED RIGHT, E1 numeric-edited (ZZ9.99), AE1 alphanumeric-edited (XXBXX), and the COBSWAIT shape:
PV PIC X(8) moved to MT PIC 9(8) COMP (shown through MTD PIC 9(8)). SPECIAL-NAMES gives SYSIN the
mnemonic name IN-DEV and SYSIPT the name CARDS. Each step: the receiver is filled with a marker (MOVE
ALL '*' / 'Z' / '7' / '.'), then ACCEPT it, with no FROM, FROM SYSIN, FROM SYSIPT, FROM IN-DEV or FROM
CARDS, then DISPLAY 'Snn KK[' item ']|'. The deck (the input stream): fixed-length records of LRECL 80
or a random LRECL (the model's records are the lines padded with spaces to LRECL; GnuCOBOL reads the
lines) or variable-length records (each line its own length). A program may end with a tail:
  EOF      the deck ends before the last one or two steps: IBM leaves the area unchanged;
  LONG     the last step's receiver X2 is longer than its record: IBM reads the next records too;
  INVALID  the last step is the COBSWAIT shape with a non-digit among the 8 characters: the MOVE to
           the COMP item faults with invalidData (Cobol/Sem/Data.lean alnumAsInt; IBM, MOVE: "the data
           is moved as if the sending item were described as an unsigned integer", and its NUMCHECK
           option flags such a sender as invalid data).
Checks per program (GnuCOBOL -std=ibm with the deck as standard input, against the front end +
cobolrun --sysin, --profile gnucobol):
  * every model line equals the IBM mirror computed here (the rule above, on the records);
  * every model line equals GnuCOBOL's, except the lines of steps of a known class where GnuCOBOL
    departs from IBM (below);
  * an INVALID tail: the model's lines equal GnuCOBOL's up to the step's PV line, then the model stops
    with invalidData.
Statuses: ok; ok-g (lines of known classes differ from GnuCOBOL, all checks hold); ok-fault (the
expected invalidData stop, all checks hold); mismatch; mirror (a model line differs from the IBM
mirror); bad-fault; and the ext_common statuses.

GnuCOBOL 3.2 departures from IBM (one standard input line per ACCEPT; the model follows IBM, the
lines are checked against the mirror only; reproducers in tools/difftest/sysin_cases):
  G-sysin-eof   at the end of the input GnuCOBOL moves a space into the receiver (spaces, zeros);
                IBM leaves it unchanged (g_sysin_eof.cob);
  G-sysin-long  a receiver longer than the record: GnuCOBOL pads the one line; IBM reads further
                records to fill it (g_sysin_long.cob);
  G-sysin-num   a numeric receiver gets a MOVE of the line in GnuCOBOL ("12AB" into 9(6) gives 000012),
                IBM transfers the characters (g_sysin_num.cob);
  G-sysin-edit  an edited receiver is edited by GnuCOBOL ("1.5" into ZZ9.99 gives "  1.50", "ABCDE"
                into XXBXX "AB CD"), IBM transfers the characters (g_sysin_edit.cob);
  G-sysin-just  a JUSTIFIED RIGHT receiver is right-justified by GnuCOBOL; IBM fills the area from
                the left with the record data (g_sysin_just.cob).
Not generated: a system input device that is missing (Env.sysin = none: the model faults with
unsupported "ACCEPT: no system input device"; GnuCOBOL always has a standard input), checked by
n_nodevice.cob with --run.

usage: sysintest.py --root C --out DIR [--n N] [--seed S] [--k K] [--show K]
       sysintest.py --root C --out DIR --run PROG.cob...   (each with PROG.deck: a first line
       "LRECL n" (0: variable-length records) or "NO-DEVICE", then the records, one per line)
"""
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ext_common as E  # noqa: E402

FAULT = "fault:Cobol.Fault.invalidData"
CHARS = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789 +-.,$/*()=:;'\"<>&%#@!?"
DIGITS = "0123456789"
FORMS = ["", " FROM SYSIN", " FROM SYSIPT", " FROM IN-DEV", " FROM CARDS"]


def ibm_accept(recs, pos, n):
    """IBM's rule (the mirror): (new contents or None = unchanged, records read)."""
    acc, k = b"", 0
    while len(acc) < n and pos + k < len(recs):
        acc += recs[pos + k]
        k += 1
    if len(acc) >= n:
        return acc[:n], k
    if not acc:
        return None, k
    return acc + b" " * (n - len(acc)), k


class Gen:
    def __init__(self, rng, k):
        self.rng = rng
        self.k = rng.randint(2, k)
        r = rng.random()
        self.lrecl = 80 if r < 0.6 else (rng.randint(8, 100) if r < 0.85 else 0)
        self.size = {"X1": rng.randint(1, 40), "X2": rng.randint(1, 90), "A1": rng.randint(1, 20),
                     "J1": rng.randint(2, 20), "N1": rng.randint(1, 12), "G1A": rng.randint(1, 6),
                     "G1N": rng.randint(1, 5), "G1B": rng.randint(1, 6), "TE": rng.randint(1, 8),
                     "E1": 6, "AE1": 5, "PV": 8}
        self.size["G1"] = self.size["G1A"] + self.size["G1N"] + self.size["G1B"]
        self.size["T1"] = 4 * self.size["TE"]
        if self.lrecl:
            # every receiver of a step that reads one record fits a record
            for key in ("X1", "X2", "A1", "J1", "N1", "TE", "PV", "E1", "AE1"):
                self.size[key] = min(self.size[key], self.lrecl)
            while self.size["G1"] > self.lrecl:
                big = max(("G1A", "G1N", "G1B"), key=lambda x: self.size[x])
                self.size[big] -= 1
                self.size["G1"] -= 1
            self.size["T1"] = 4 * self.size["TE"]
        self.lines, self.steps = [], []

    def data(self):
        s = self.size
        return [f"       01 X1 PIC X({s['X1']}).", f"       01 X2 PIC X({s['X2']}).",
                f"       01 A1 PIC A({s['A1']}).", f"       01 J1 PIC X({s['J1']}) JUSTIFIED RIGHT.",
                f"       01 N1 PIC 9({s['N1']}).", "       01 G1.",
                f"          05 G1A PIC X({s['G1A']}).", f"          05 G1N PIC 9({s['G1N']}).",
                f"          05 G1B PIC X({s['G1B']}).", "       01 T1.",
                f"          05 TE PIC X({s['TE']}) OCCURS 4.", "       01 IX PIC 9 VALUE 1.",
                "       01 E1 PIC ZZ9.99.", "       01 AE1 PIC XXBXX.", "       01 PV PIC X(8).",
                "       01 MT PIC 9(8) COMP.", "       01 MTD PIC 9(8)."]

    def text(self, n, digits=0, at_least=0):
        """A record's text: `digits` leading digits, at least `at_least` characters in all."""
        rng = self.rng
        cap = self.lrecl if self.lrecl else 100
        m = rng.randint(max(digits, at_least), max(digits, at_least, min(cap, n + rng.choice([0, 0, 5, 20]))))
        if self.lrecl:
            m = min(m, self.lrecl)
        t = "".join(rng.choice(DIGITS) for _ in range(digits)) + \
            "".join(rng.choice(CHARS) for _ in range(m - digits))
        return t

    def program(self):
        rng = self.rng
        tail = rng.choice([None, None, "EOF", "LONG", "INVALID"])
        nsteps = self.k
        # EOF: the deck ends before step eof_from; LONG: X2 is longer than its record and only the last
        # step uses it (IBM reads further records, so GnuCOBOL's and IBM's positions part there)
        eof_from = nsteps - rng.choice([1, 1, 2]) if tail == "EOF" else nsteps
        kinds = ["X1", "X1", "X2", "A1", "N1", "N1", "G1", "TE", "TE", "R1", "PV", "PV", "J1", "E1", "AE1"]
        if tail == "LONG":
            kinds = [x for x in kinds if x != "X2"]
            if self.lrecl:
                self.size["X2"] = self.lrecl + rng.randint(1, 30)
            else:
                self.size["X2"] = rng.randint(2, 90)
        proc = []
        for i in range(nsteps):
            last = i == nsteps - 1
            eof = i >= eof_from
            st = {"step": i, "g": []}
            if tail == "LONG" and last:
                kind = "X2"
            elif tail == "INVALID" and last:
                kind = "PV"
            elif eof:
                # the steps after the end of the deck: receivers with a visible marker
                kind = rng.choice(["X1", "X2", "A1", "N1", "G1", "TE", "R1", "J1"])
            else:
                kind = rng.choice(kinds)
            form = rng.choice(FORMS)
            st.update(kind=kind, form=form, eof=eof)
            item = {"R1": "X1", "TE": "T1"}.get(kind, kind)
            n = self.size["X1"] if kind == "R1" else self.size[kind]
            # the marker
            mark = {"A1": "Z", "N1": "7", "TE": "."}.get(kind, "*")
            if kind in ("E1", "AE1"):
                preset = None
            else:
                proc.append(f"MOVE ALL '{mark}' TO {item}")
                preset = mark.encode() * self.size[item]
            target = kind
            if kind == "TE":
                sub = rng.randint(1, 4)
                if rng.random() < 0.5:
                    proc.append(f"MOVE {sub} TO IX")
                    target = "TE (IX)"
                else:
                    target = f"TE ({sub})"
                st["sub"] = sub
            elif kind == "R1":
                p = rng.randint(1, n)
                q = rng.randint(1, n - p + 1)
                target = f"X1 ({p}:{q})"
                st["refmod"] = (p, q)
                n = q
            st["n"] = n
            proc.append(f"ACCEPT {target}{form}")
            # the record this step reads
            if not eof:
                if kind == "N1":
                    bad = rng.random() < 0.15
                    t = self.text(n, digits=0 if bad else n, at_least=n)
                    if bad:
                        t = t[:max(0, n - 1)] + rng.choice("ABC -.+") + t[n:]
                        st["g"].append("G-sysin-num")
                elif kind == "PV":
                    if tail == "INVALID" and last:
                        t = list(self.text(8, digits=8, at_least=8))
                        t[rng.randint(0, 7)] = rng.choice("ABC -.+*/")
                        t = "".join(t)
                    else:
                        t = self.text(8, digits=8, at_least=8)
                elif kind == "X2" and tail == "LONG" and last:
                    # a record shorter than the receiver (fixed: X2 is longer than LRECL), then more
                    t = self.text(1, at_least=0)
                    if not self.lrecl:
                        t = t[:n - 1]
                    st["g"].append("G-sysin-long")
                else:
                    t = self.text(n, at_least=0 if self.lrecl else n)
                self.lines.append(t)
                st["line"] = t
            if kind == "J1":
                st["g"].append("G-sysin-just")
            if kind in ("E1", "AE1"):
                st["g"].append("G-sysin-edit")
            if eof:
                st["g"].append("G-sysin-eof")
            st["preset"] = preset
            disp = item
            proc.append(f"DISPLAY 'S{i:02d} {disp}[' {disp} ']|'")
            if kind == "PV":
                proc += ["MOVE PV TO MT", "MOVE MT TO MTD", f"DISPLAY 'S{i:02d} MT[' MTD ']|'"]
            self.steps.append(st)
        if tail == "LONG":
            # more records after the long step's record, read by IBM's rule
            for _ in range(rng.randint(0, 3)):
                self.lines.append(self.text(rng.randint(1, 30)))
        self.tail = tail
        hdr = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. SYSIT.",
               "       ENVIRONMENT DIVISION.", "       CONFIGURATION SECTION.", "       SPECIAL-NAMES.",
               "           SYSIN IS IN-DEV", "           SYSIPT IS CARDS.", "       DATA DIVISION.",
               "       WORKING-STORAGE SECTION."] + self.data() + ["       PROCEDURE DIVISION."]
        body = []
        for ln in proc:
            body += E.wrap(ln)
        return "\n".join(E.check_lines(hdr + body + ["           STOP RUN."])) + "\n"

    def records(self):
        """The model's records (bytes): fixed-length LRECL (lines padded) or variable."""
        return [(ln.ljust(self.lrecl) if self.lrecl else ln).encode("latin-1") for ln in self.lines]

    def mirror(self):
        """The model lines IBM's rule gives, step by step (a list of (step, tag, text))."""
        recs, pos, out = self.records(), 0, []
        for st in self.steps:
            kind, n = st["kind"], st["n"]
            item = {"R1": "X1", "TE": "T1"}.get(kind, kind)
            cur = st["preset"]
            got, k = ibm_accept(recs, pos, n)
            pos += k
            if cur is None:
                cur = got if got is not None else b"?" * n
            elif got is not None:
                if kind == "TE":
                    w = self.size["TE"]
                    a = (st["sub"] - 1) * w
                    cur = cur[:a] + got + cur[a + w:]
                elif kind == "R1":
                    p, q = st["refmod"]
                    cur = cur[:p - 1] + got + cur[p - 1 + q:]
                else:
                    cur = got
            out.append((st["step"], item, cur.decode("latin-1")))
            if kind == "PV":
                if cur.isdigit() and len(cur) == 8:
                    out.append((st["step"], "MT", cur.decode("latin-1")))
                else:
                    out.append((st["step"], "MT", None))   # invalidData at the MOVE
        return out


def run_both(D, src, lines, records, base, device=True):
    """GnuCOBOL (standard input = the lines) and the model (--sysin = the records) on one program:
    (status, gnucobol lines, model lines, model signal)."""
    d = os.path.dirname(base)
    with open(base + ".cob", "w", encoding="latin-1") as fh:
        fh.write(src)
    deck = "".join(ln + "\n" for ln in lines).encode("latin-1")
    with open(base + ".stdin", "wb") as fh:
        fh.write(deck)
    with open(base + ".sysin.json", "w") as fh:
        json.dump([list(r) for r in records], fh)
    c = subprocess.run([D.COBC, "-x"] + E.PLAIN_COBC + ["-o", base, base + ".cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return "cobc-error", c.stderr[-2000:], None, None
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    try:
        r = subprocess.run([base], input=deck, capture_output=True, env=env, timeout=20, cwd=d)
    except subprocess.TimeoutExpired:
        return "gnucobol-timeout", None, None, None
    if r.returncode != 0:
        return "gnucobol-abend", (r.stdout[-500:] + r.stderr[-500:]).decode("latin-1"), None, None
    g = r.stdout.decode("latin-1").split("\n")
    if g and g[-1] == "":
        g.pop()
    fe = subprocess.run([sys.executable, "-I", D.COBOLFE, base + ".cob"] + E.PLAIN_FE +
                        ["--main", "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0:
        return "fe-error", fe.stderr[-2000:], None, None
    unsup = [ln for ln in fe.stderr.splitlines() if "unsupported" in ln]
    if unsup:
        return "fe-unsupported", "\n".join(unsup)[:2000], None, None
    cmd = [D.COBOLRUN, base + ".fe.json"] + (["--sysin", base + ".sysin.json"] if device else [])
    try:
        lr = subprocess.run(cmd, capture_output=True, text=True, timeout=60, cwd=d)
    except subprocess.TimeoutExpired:
        return "lean-timeout", None, None, None
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[-2000:], None, None
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    return "ran", g, m, res["signal"]


def judge(gen, g, m, signal, tally):
    """Status of one program and a detail string (see the module docstring)."""
    exp = gen.mirror()
    steps = {s["step"]: s for s in gen.steps}
    invalid = gen.tail == "INVALID"
    want = []
    for step, tag, text in exp:
        if text is None:
            break
        want.append((step, tag, f"S{step:02d} {tag}[{text}]|"))
    if invalid:
        if exp[-1][2] is not None:
            # the 8 characters happen to be digits after all (cannot happen: one is replaced)
            return "bad-fault", "invalid step without a non-digit"
        if signal != FAULT or len(m) != len(want):
            return "bad-fault", f"signal {signal}, model lines {len(m)}, expected {len(want)}"
        g = g[:len(want)]
    elif not signal.startswith("stop:"):
        return "lean-signal", signal
    if len(m) != len(want):
        return "mirror", f"model lines {len(m)}, mirror lines {len(want)}"
    for line, (step, tag, w) in zip(m, want):
        if line != w:
            return "mirror", f"step {step}: model {line!r} mirror {w!r}"
    if len(g) != len(m):
        return "mismatch", f"line counts {len(g)} vs {len(m)}"
    glines = 0
    for a, b, (step, tag, w) in zip(g, m, want):
        if a == b:
            continue
        st = steps[step]
        if st["g"]:
            glines += 1
            for c in st["g"]:
                tally["g_lines"][c] = tally["g_lines"].get(c, 0) + 1
            continue
        return "mismatch", f"gnucobol {a!r} model {b!r}"
    tally["lines"] += len(m)
    if invalid:
        return "ok-fault", f"PV {exp[-2][2]!r}"
    return ("ok-g" if glines else "ok"), ""


def coverage(gen, cov):
    cov["lrecl_" + ("var" if gen.lrecl == 0 else ("80" if gen.lrecl == 80 else "other"))] = \
        cov.get("lrecl_" + ("var" if gen.lrecl == 0 else ("80" if gen.lrecl == 80 else "other")), 0) + 1
    cov["tail_" + str(gen.tail)] = cov.get("tail_" + str(gen.tail), 0) + 1
    for s in gen.steps:
        cov["kind_" + s["kind"]] = cov.get("kind_" + s["kind"], 0) + 1
        f = s["form"].strip() or "no FROM"
        cov["form_" + f] = cov.get("form_" + f, 0) + 1
        for c in s["g"]:
            cov["steps_" + c] = cov.get("steps_" + c, 0) + 1


def run_files(args):
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    worst = 0
    for path in args.run:
        with open(path, encoding="latin-1") as fh:
            src = fh.read()
        deck = open(os.path.splitext(path)[0] + ".deck", encoding="latin-1").read().split("\n")
        if deck and deck[-1] == "":
            deck.pop()
        head, lines = deck[0].split(), deck[1:]
        device = head[0] != "NO-DEVICE"
        lrecl = int(head[1]) if device else 0
        records = [(ln.ljust(lrecl) if lrecl else ln).encode("latin-1") for ln in lines]
        base = os.path.join(args.out, "run_" + os.path.splitext(os.path.basename(path))[0])
        status, g, m, signal = run_both(D, src, lines, records, base, device)
        print(f"== {path}: {status} {signal or ''}")
        if status == "ran":
            for i in range(max(len(g), len(m))):
                a, b = (g[i] if i < len(g) else "<none>"), (m[i] if i < len(m) else "<none>")
                print(("   " if a == b else "!! ") + f"{a:<44} | {b}")
            worst = max(worst, 0 if (g == m and signal.startswith("stop:")) else 1)
        else:
            print(str(g)[:2000])
            worst = 1
    return worst


def main():
    ap = E.arg_parser(__doc__, 60, 8)
    ap.add_argument("--run", nargs="+", metavar="PROG.cob")
    args = ap.parse_args()
    if args.run:
        sys.exit(run_files(args))
    D = E.difftest(args.root)
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    open(os.path.join(args.out, "details.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown = {"g_lines": {}, "lines": 0}, 0
    statuses, cov = {}, {}
    for p in range(args.n):
        gen = Gen(rng, args.k)
        src = gen.program()
        base = os.path.join(args.out, f"p{args.seed}_{p:04d}")
        status, g, m, signal = run_both(D, src, gen.lines, gen.records(), base)
        detail = g
        if status == "ran":
            status, detail = judge(gen, g, m, signal, tally)
        coverage(gen, cov)
        statuses[status] = statuses.get(status, 0) + 1
        with open(os.path.join(args.out, "results.jsonl"), "a") as fh:
            fh.write(json.dumps({"case": p, "status": status}) + "\n")
        if status not in ("ok", "ok-g", "ok-fault"):
            with open(os.path.join(args.out, "details.jsonl"), "a") as fh:
                fh.write(json.dumps({"case": p, "status": status, "detail": str(detail)[:2000],
                                     "steps": gen.steps, "lrecl": gen.lrecl}, default=str) + "\n")
            if shown < args.show:
                shown += 1
                print(f"program {p}: {status}: {str(detail)[:600]}")
    with open(os.path.join(args.out, "coverage.json"), "w") as fh:
        json.dump({"statuses": statuses, "g_lines": tally["g_lines"], "lines": tally["lines"],
                   "coverage": cov}, fh, indent=1, sort_keys=True)
    print(json.dumps({"tally": statuses}))
    print(json.dumps({"g_lines": tally["g_lines"], "lines": tally["lines"]}, sort_keys=True))
    # exit status 0 when every program passed (ok, ok-g, ok-fault), 1 otherwise
    sys.exit(0 if all(s in ("ok", "ok-g", "ok-fault") for s in statuses) else 1)


if __name__ == "__main__":
    main()

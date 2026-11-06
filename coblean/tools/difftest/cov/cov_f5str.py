#!/usr/bin/env python3
"""Differential testing of STRING with every delimiter BY SIZE and no POINTER: the front end's
statically laid-out path (tools/cobolfe parser.py st_STRING / string_source), where front-end
mutants of PREREG_M part FE set 2 (orders 1 and 18) survived.

Each random program runs K STRING statements into alphanumeric receivers R4, R7, R12, R16
(PIC X(n)) that first get random contents (ALL '#', SPACES or a random literal), so the
positions STRING does not reach stay visible (STRING does not pad). Sources, 1 to 6 per
statement, grouped 1 to 3 per DELIMITED [BY] SIZE phrase: alphanumeric literals, unsigned
integer numeric literals (leading zeros kept), figurative constants (SPACE(S), ZERO(S)/ZEROES,
QUOTE(S), HIGH-VALUE(S), LOW-VALUE(S)), the sending items S1, S3, S5, S8 (random contents set
before each statement), and their reference modifications with literal start and length.
Total source lengths range from short of the receiver to past it (overflow). ON OVERFLOW /
NOT ON OVERFLOW phrases are present in random combinations; the phrase that ran (O, N or
blank) and the receiver are displayed after each statement.

usage: cov_f5str.py --root C --out DIR [--n N] [--seed S] [--k K] [--fe FE]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cov_common as E  # noqa: E402

ITEMS = {"S1": 1, "S3": 3, "S5": 5, "S8": 8}
RCVS = {"R4": 4, "R7": 7, "R12": 12, "R16": 16}
CH = "ABCxyz019 -.#"
FIGS = ["SPACE", "SPACES", "ZERO", "ZEROS", "ZEROES", "QUOTE", "QUOTES", "HIGH-VALUE",
        "HIGH-VALUES", "LOW-VALUE", "LOW-VALUES"]


def lit(s):
    return "'" + s + "'"


def rtext(rng, n):
    return "".join(rng.choice(CH) for _ in range(n))


def source(rng):
    """(source text, its length)"""
    r = rng.random()
    if r < 0.22:
        n = rng.randint(1, 5)
        return lit(rtext(rng, n)), n
    if r < 0.4:
        v = rng.randint(0, 9999)
        s = str(v).zfill(rng.choice([1, 1, 2, 3, 4]))
        return s, len(s)
    if r < 0.55:
        return rng.choice(FIGS), 1
    nm = rng.choice(list(ITEMS))
    n = ITEMS[nm]
    if r < 0.8:
        return nm, n
    st = rng.randint(1, n)
    ln = rng.randint(1, n - st + 1)
    return f"{nm}({st}:{ln})", ln


def statement(rng, i):
    rv = rng.choice(list(RCVS))
    n = RCVS[rv]
    lines = []
    init = rng.random()
    if init < 0.4:
        lines.append(f"MOVE ALL '#' TO {rv}")
    elif init < 0.6:
        lines.append(f"MOVE SPACES TO {rv}")
    else:
        lines.append(f"MOVE {lit(rtext(rng, n))} TO {rv}")
    for nm, ln in ITEMS.items():
        lines.append(f"MOVE {lit(rtext(rng, ln))} TO {nm}")
    lines.append("MOVE ' ' TO F")
    # aim for totals around the receiver length: often under, sometimes exact, sometimes over
    parts, total = [], 0
    nsrc = rng.randint(1, 6)
    for _ in range(nsrc):
        s, ln = source(rng)
        parts.append(s)
        total += ln
    text = "STRING"
    j = 0
    while j < len(parts):
        g = rng.randint(1, 3)
        text += " " + " ".join(parts[j:j + g]) + rng.choice([" DELIMITED BY SIZE", " DELIMITED SIZE"])
        j += g
    text += f" INTO {rv}"
    ph = rng.random()
    if ph < 0.35:
        text += " ON OVERFLOW MOVE 'O' TO F NOT ON OVERFLOW MOVE 'N' TO F"
    elif ph < 0.55:
        text += " ON OVERFLOW MOVE 'O' TO F"
    elif ph < 0.75:
        text += " NOT ON OVERFLOW MOVE 'N' TO F"
    text += " END-STRING"
    out = ["           " + x for x in lines]
    out += E.wrap(text)
    out.append(f"           DISPLAY 'T{i:02d} ' {rv} ' ' F '|'")
    return out


def program(rng, k):
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. COVF5.",
             "       DATA DIVISION.", "       WORKING-STORAGE SECTION."]
    for nm, n in list(ITEMS.items()) + list(RCVS.items()):
        lines.append(f"       01  {nm} PIC X({n}) VALUE SPACES.")
    lines.append("       01  F PIC X VALUE ' '.")
    lines.append("       PROCEDURE DIVISION.")
    for i in range(k):
        lines += statement(rng, i)
    lines.append("           STOP RUN.")
    return "\n".join(lines) + "\n"


def main():
    ap = E.arg_parser(__doc__, 60, 12)
    args = ap.parse_args()
    E.main_loop(args, program, E.PLAIN_COBC, E.PLAIN_FE)


if __name__ == "__main__":
    main()

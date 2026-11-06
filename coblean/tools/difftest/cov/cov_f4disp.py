#!/usr/bin/env python3
"""Differential testing of DISPLAY of numbers: numeric literals with and without decimal places
(the semantics' `.num` operand, Cobol/Sem/Exec.lean displayBytes, where PREREG_M set 2 survivor
#26 sits: the decimal point character), and numeric data items.

--part lit: each random program DISPLAYs K unsigned numeric literals: 1 to 5 integer digits
  (leading zeros kept) and 0 to 4 decimal places, between two alphanumeric literals. GnuCOBOL runs
  with -std=ibm (pretty-display: no), which drops the decimal point (12.34 shows as 1234), as IBM's
  rules for numeric literals give (the point is an assumed one, not a character position; the
  size is the number of digits). Not generated: a literal written with a sign, for which IBM gives
  no form (the front end makes such a DISPLAY unsupported; displittest.py).
--part items: each random program MOVEs random values to numeric items and DISPLAYs them,
  under -std=ibm: unsigned COMP-3 (PACKED-DECIMAL) items, unsigned DISPLAY items and signed
  DISPLAY items with SIGN LEADING SEPARATE or SIGN TRAILING SEPARATE, with 0 to 3 decimal
  places. Not generated, GnuCOBOL/IBM display-format deviations (probes/p2disp.cob): signed
  COMP-3, any COMP/BINARY or COMP-5 item, and signed DISPLAY items with an embedded sign.
  coblean shows these as IBM does (the digits of the PICTURE as zoned decimal, the sign as an
  overpunch on the last digit); GnuCOBOL -std=ibm shows binary items with all the digits of
  their storage size, and signed items with a separate leading or trailing sign. Nor MOVE -0
  (GnuCOBOL keeps a negative zero, coblean stores zero as positive: the known negative-zero class).

usage: cov_f4disp.py --root C --out DIR --part lit|items [--n N] [--seed S] [--k K]
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cov_common as E  # noqa: E402


def literal(rng):
    ip = rng.randint(1, 5)
    i = "".join(rng.choice("0123456789") for _ in range(ip))
    if rng.random() < 0.5:
        i = i.lstrip("0") or "0"
    dp = rng.choice([0, 1, 1, 2, 2, 3, 4])
    f = "".join(rng.choice("0123456789") for _ in range(dp))
    return i + ("." + f if dp else "")


def program_lit(rng, k):
    L = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. COVF4L.", "       PROCEDURE DIVISION."]
    for i in range(k):
        L.append(f"           DISPLAY 'L{i:02d} ' {literal(rng)} '|'")
    L.append("           STOP RUN.")
    return "\n".join(L) + "\n"


ITEMS = []
for _usage, _sign in [("COMP-3", ""), ("", ""), ("", "SIGN LEADING SEPARATE"),
                      ("", "SIGN TRAILING SEPARATE")]:
    for _ip in (1, 3, 5):
        for _sc in (0, 1, 2, 3):
            ITEMS.append((_usage, _sign, _ip, _sc))


def pic(ip, sc, signed):
    return ("S" if signed else "") + f"9({ip})" + (f"V9({sc})" if sc else "")


def value(rng, ip, sc, signed):
    i = rng.randint(0, 10 ** ip - 1) if rng.random() < 0.7 else rng.randint(0, 9)
    f = rng.randint(0, 10 ** sc - 1) if sc else 0
    s = "-" if signed and rng.random() < 0.5 and (i or f) else ""   # no negative zero
    return s + str(i) + (f".{f:0{sc}d}" if sc else "")


def program_items(rng, k):
    chosen = [rng.choice(ITEMS) for _ in range(6)]
    L = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. COVF4I.",
         "       DATA DIVISION.", "       WORKING-STORAGE SECTION."]
    for j, (usage, sign, ip, sc) in enumerate(chosen):
        decl = f"       01  N{j} PIC {pic(ip, sc, bool(sign))}"
        if sign:
            L.append(decl)
            L.append(f"           {sign}" + (f" {usage}" if usage else "") + " VALUE 0.")
        else:
            L.append(decl + (f" {usage}" if usage else "") + " VALUE 0.")
    L.append("       PROCEDURE DIVISION.")
    for i in range(k):
        j = rng.randrange(len(chosen))
        usage, sign, ip, sc = chosen[j]
        L.append(f"           MOVE {value(rng, ip, sc, bool(sign))} TO N{j}")
        L.append(f"           DISPLAY 'D{i:02d} ' N{j} '|'")
    L.append("           STOP RUN.")
    return "\n".join(L) + "\n"


def main():
    ap = E.arg_parser(__doc__, 60, 20)
    ap.add_argument("--part", choices=["lit", "items"], required=True)
    args = ap.parse_args()
    if args.part == "lit":
        E.main_loop(args, program_lit, E.PLAIN_COBC, E.PLAIN_FE)
    else:
        E.main_loop(args, program_items, E.PLAIN_COBC, E.PLAIN_FE)


if __name__ == "__main__":
    main()

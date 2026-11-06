#!/usr/bin/env python3
"""Differential testing of INITIALIZE ... REPLACING, and its consistency with plain INITIALIZE.

IBM Enterprise COBOL 6.4, INITIALIZE statement rules: rule 1 selects the receivers (items that
are not MOVE receivers, FILLER items without WITH FILLER, and items inside identifier-1 that have
a REDEFINES clause or lie under one are excluded; identifier-1's own REDEFINES does not exclude
it; every table occurrence is a receiver); with REPLACING only the items of a category named in
the phrase are receivers, each sent that category's literal or identifier; without REPLACING
(and VALUE) every receiver gets SPACE (alphabetic, alphanumeric, alphanumeric-edited) or ZERO
(numeric, numeric-edited) (rule 2).

Each random program has one record R: a sentinel, a data area D (a group with a FILLER item, a
REDEFINES child, a table and a nested group; a group redefined by another; an elementary item;
items of every category: alphabetic, alphanumeric, alphanumeric-edited, numeric DISPLAY / COMP /
COMP-3, numeric-edited) and one history slot per step. Each step fills D with '#', runs one
INITIALIZE and copies D into its slot:
  - INITIALIZE of one or two identifiers (groups, an elementary item, a table element, the
    redefining group) REPLACING 1-5 categories in random order BY literals, figurative constants
    or items outside R;
  - plain INITIALIZE of one or two identifiers (never the redefining group, a root with REDEFINES,
    which the resolver before init-fix skips);
  - a consistency pair: INITIALIZE X, its copy in the slot, D filled again, then INITIALIZE X
    REPLACING ALPHABETIC BY SPACES ALPHANUMERIC BY SPACES ALPHANUMERIC-EDITED BY SPACES NUMERIC BY
    ZERO NUMERIC-EDITED BY ZERO (the same by IBM's rules 1c and 2) and a DISPLAY of whether D
    equals the slot.
At the end GnuCOBOL (-std=ibm -fbinary-truncate, i.e. TRUNC(STD)) dumps R; the front end +
cobolrun runs until that dump (outside the IR), and R's bytes in its storage must equal
GnuCOBOL's, the DISPLAY lines must agree and every consistency pair must show SAME. Exit status 0
only when every program passes.

Left out of generation:
  G-fillersep  GnuCOBOL 3.2 initializes a FILLER item with SIGN ... SEPARATE (plain INITIALIZE and
               REPLACING alike; other FILLER items are skipped), IBM's rule 1a excludes every
               FILLER item (initrepl_cases/fil2.cob); no FILLER item here has a separate sign;
  a negative value that becomes zero in the receiver (MOVE -0.5 to S9(3)): GnuCOBOL keeps the
               minus sign, the model does not model negative zero (README);
  index data items (G-initindex: GnuCOBOL 3.2 sets them, IBM's rule 1a excludes them; the
               expected-output case initrepl_cases/irindex1.cob needs USAGE INDEX in the front end).

Control: the front end of coblean-20261027T0518Z makes the REPLACING steps unsupported.
Planted faults (recipes, on a copy M of tools/cobolfe; each must give failures):
  M1 a REDEFINES item inside the identifier is a receiver too:
     sed -i 's/if e is not root and e.redefines is not None or e.usage/if e.usage/' M/parser.py
  M2 an alphabetic item counts as alphanumeric:
     sed -i 's/return "ALPHABETIC" if set/return "ALPHANUMERIC" if set/' M/parser.py
then COBOLFE=M/cobolfe.py python3 -I -B tools/difftest/initrepltest.py --n 60 --seed 1.

usage: initrepltest.py [--n N] [--seed S] [--k K] [--out DIR] [--show K]
"""
import argparse
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import difftest as D  # noqa: E402
from inspecttest import bump  # noqa: E402

SENT = "IRTRACE1"
CATS = ["ALPHABETIC", "ALPHANUMERIC", "ALPHANUMERIC-EDITED", "NUMERIC", "NUMERIC-EDITED"]
# (PICTURE and USAGE, size, category)
ELEMS = {
    "A": [("PIC A(1)", 1), ("PIC A(4)", 4), ("PIC A(6)", 6)],
    "X": [("PIC X(1)", 1), ("PIC X(3)", 3), ("PIC X(7)", 7)],
    "AN": [("PIC XX99", 4), ("PIC A9X", 3), ("PIC 9X9", 3)],
    "AE": [("PIC XXBXX", 5), ("PIC X0X", 3), ("PIC XX/XX/XX", 8), ("PIC AAB9", 4), ("PIC 0XX", 3)],
    "N": [("PIC 9(4)", 4), ("PIC S9(3)V9", 4), ("PIC 99V99", 4), ("PIC S9(3) SIGN LEADING SEPARATE", 4),
          ("PIC S9(4) COMP", 2), ("PIC 9(8) COMP", 4), ("PIC S9(5) COMP-3", 3), ("PIC 9(4)V9 COMP-3", 3)],
    "NE": [("PIC ZZ9.99", 6), ("PIC $(3)9.99", 7), ("PIC -(3)9", 4), ("PIC **9.9", 5), ("PIC 9(3)CR", 5),
           ("PIC Z,ZZ9", 5), ("PIC +9(3)", 4)],
}
CAT_OF = {"A": "ALPHABETIC", "X": "ALPHANUMERIC", "AN": "ALPHANUMERIC", "AE": "ALPHANUMERIC-EDITED",
          "N": "NUMERIC", "NE": "NUMERIC-EDITED"}
OPERANDS = {
    "ALPHABETIC": ["'ABCDEFG'", "'XY'", "SPACES", "BA", "'Q R'"],
    "ALPHANUMERIC": ["'K9-L'", "'1234567890'", "SPACES", "ZEROS", "HIGH-VALUES", "LOW-VALUES", "QUOTES",
                     "BX", "BI", "ALL 'AB'"],
    "ALPHANUMERIC-EDITED": ["'ABCDEFGH'", "'12'", "SPACES", "ZEROS", "HIGH-VALUES", "BX", "BI"],
    "NUMERIC": ["5", "-17", "123.45", "ZERO", "BN", "BI", "98765"],
    "NUMERIC-EDITED": ["5", "-17", "123.45", "ZERO", "BN", "BI", "0"],
}
PLAIN = {"ALPHABETIC": "SPACES", "ALPHANUMERIC": "SPACES", "ALPHANUMERIC-EDITED": "SPACES",
         "NUMERIC": "ZERO", "NUMERIC-EDITED": "ZERO"}


def elem(rng, maxsize=None, filler=False):
    while True:
        k = rng.choice(sorted(ELEMS))
        pic, size = rng.choice(ELEMS[k])
        if filler and "SEPARATE" in pic:
            continue                    # G-fillersep
        if maxsize is None or size <= maxsize:
            return pic, size


def data_area(rng):
    """The lines of D (level 10 and below), its size and the INITIALIZE candidates:
    (identifier, may be plain-initialized)."""
    L, cands = [], []
    g1 = 0
    L.append("        10 G1.")
    p, s = elem(rng)
    L.append(f"           15 G1A {p}."); g1 += s
    p, s = elem(rng, filler=True)
    L.append(f"           15 {'FILLER' if rng.random() < 0.7 else 'G1B'} {p}."); g1 += s
    p, s = elem(rng)
    L.append(f"           15 G1C {p}."); g1 += s
    if rng.random() < 0.6:
        L.append(f"           15 G1R REDEFINES G1C PIC X({s}).")
    if rng.random() < 0.7:
        m = rng.randint(2, 3)
        L.append(f"           15 T1 OCCURS {m}.")
        pa, sa = elem(rng)
        pb, sb = elem(rng)
        L += [f"              20 T1A {pa}.", f"              20 T1B {pb}."]
        g1 += m * (sa + sb)
        cands += [(f"T1 ({rng.randint(1, m)})", True), (f"T1A ({rng.randint(1, m)})", True)]
    if rng.random() < 0.6:
        L.append("           15 GS.")
        for nm in ("GSA", "FILLER", "GSC"):
            p, s = elem(rng, filler=nm == "FILLER")
            L.append(f"              20 {nm} {p}."); g1 += s
        cands.append(("GS", True))
    L.append("        10 G2.")
    g2 = 0
    for nm in ("G2A", "G2B"):
        p, s = elem(rng)
        L.append(f"           15 {nm} {p}."); g2 += s
    L.append("        10 G2R REDEFINES G2.")
    p, s = elem(rng, g2)
    L.append(f"           15 G2RA {p}.")
    if s < g2:
        L.append(f"           15 G2RB PIC X({g2 - s}).")
    p, s = elem(rng)
    L.append(f"        10 E1 {p}.")
    cands += [("G1", True), ("G2", True), ("E1", True), ("D", True), ("G1A", True), ("G2R", False)]
    return L, g1 + g2 + s, cands


def program(rng, k, counts):
    dl, dsize, cands = data_area(rng)
    total = 8 + dsize * (k + 1)
    proc = []
    for j in range(k):
        proc.append("MOVE ALL '#' TO D")
        r = rng.random()
        if r < 0.55:
            ids = [c for c, _ in rng.sample(cands, rng.choice([1, 1, 2]))]
            cats = rng.sample(CATS, rng.randint(1, 5))
            for c in cats:
                counts[c] = counts.get(c, 0) + 1
            phr = " ".join(f"{c}{' DATA' if rng.random() < 0.3 else ''} BY {rng.choice(OPERANDS[c])}"
                           for c in cats)
            proc.append(f"INITIALIZE {' '.join(ids)} REPLACING {phr}")
            proc.append(f"MOVE D TO HS ({j + 1})")
        elif r < 0.75:
            ids = [c for c, _ in rng.sample([x for x in cands if x[1]], rng.choice([1, 1, 2]))]
            proc.append(f"INITIALIZE {' '.join(ids)}")
            proc.append(f"MOVE D TO HS ({j + 1})")
        else:
            x = rng.choice([c for c, ok in cands if ok])
            cats = rng.sample(CATS, 5)
            phr = " ".join(f"{c} BY {PLAIN[c]}" for c in cats)
            counts["consistency pairs"] = counts.get("consistency pairs", 0) + 1
            proc += [f"INITIALIZE {x}", f"MOVE D TO HS ({j + 1})", "MOVE ALL '#' TO D",
                     f"INITIALIZE {x} REPLACING {phr}",
                     f"IF D = HS ({j + 1}) DISPLAY 'C{j + 1} SAME' ELSE DISPLAY 'C{j + 1} DIFF' END-IF"]
    L = ["IDENTIFICATION DIVISION.", "PROGRAM-ID. IRT.", "DATA DIVISION.", "WORKING-STORAGE SECTION.",
         "01  R.", f"    05 SENT PIC X(8) VALUE '{SENT}'.", "    05 D."] + dl + \
        [f"    05 HS OCCURS {k} PIC X({dsize}).", "01  RX REDEFINES R.", f"    05 BYTE PIC X OCCURS {total}.",
         "01  BA PIC A(4) VALUE 'QRST'.", "01  BX PIC X(5) VALUE 'X1Y2Z'.", "01  BI PIC 9(3) VALUE 417.",
         "01  BN PIC S9(3)V99 VALUE -12.34.", "01  IDX PIC 9(5) COMP.", "PROCEDURE DIVISION.", "MAIN-PARA.",
         "    MOVE ALL '#' TO HS (1)"]
    L += [f"    MOVE HS (1) TO HS ({i})" for i in range(2, k + 1)]
    L += ["    " + s for s in proc]
    L += [f"    PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > {total}",
          "       DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING", "    END-PERFORM", "    DISPLAY ' '",
          "    STOP RUN."]
    return "\n".join(D.wrap_fixed(x) for x in L) + "\n", total


def run(src, base, total):
    with open(base + ".cob", "w") as fh:
        fh.write(src)
    # TRUNC(STD), as the front end's default (-std=ibm alone truncates binary items like TRUNC(BIN))
    c = subprocess.run([D.COBC, "-x"] + D.COBC_FLAGS["std"] + ["-o", base, base + ".cob"], capture_output=True,
                       text=True, timeout=120)
    if c.returncode != 0:
        return "cobc-error", c.stderr[:1500]
    r = subprocess.run([base], capture_output=True, env=dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR), timeout=20)
    g = r.stdout.decode("latin-1").splitlines()
    try:
        gdump = [int(x) - 1 for x in g[-1].split()]
    except (ValueError, IndexError):
        return "gnucobol-output", r.stdout[-500:]
    glines = g[:-1]
    if len(gdump) != total:
        return "gnucobol-output", f"{len(gdump)} bytes dumped, {total} expected"
    fe = subprocess.run([sys.executable, "-I", D.COBOLFE, base + ".cob", "--profile", "gnucobol", "--main",
                         "-o", base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if fe.returncode != 0:
        return "frontend-error", fe.stderr[:1500]
    unsup = [ln for ln in fe.stderr.splitlines() if "unsupported" in ln and "DISPLAY (line" not in ln]
    if unsup:
        return "frontend-unsupported", "\n".join(unsup)[:1500]
    lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True, timeout=60)
    if lr.returncode != 0:
        return "cobolrun-error", lr.stderr[:1500]
    res = json.loads(lr.stdout)
    if not ("unsupported" in res["signal"] and "DISPLAY" in res["signal"]):
        return "model-signal", res["signal"]
    mlines = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if mlines != glines:
        return "mismatch-display", {"gnucobol": glines, "model": mlines}
    mem = bytes(res["mem"])
    off = mem.find(SENT.encode())
    if off < 0:
        return "model-layout", "sentinel not found"
    mb = list(mem[off:off + total])
    if mb != gdump:
        i = next(x for x in range(total) if mb[x] != gdump[x])
        return "mismatch-storage", {"byte": i, "gnucobol": gdump[i:i + 12], "model": mb[i:i + 12]}
    if any(ln.endswith("DIFF") for ln in mlines):
        return "inconsistent", mlines
    return "ok", None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=8)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "out_initrepl"))
    ap.add_argument("--show", type=int, default=3)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, counts, shown = {}, {}, 0
    for p in range(a.n):
        src, total = program(random.Random(rng.random()), a.k, counts)
        base = os.path.join(a.out, f"irt_{a.seed}_{p}")
        st, det = run(src, base, total)
        bump(tally, a.out, p, st)
        if st != "ok" and shown < a.show:
            shown += 1
            print(f"program {p}: {st}: {json.dumps(det)[:1500] if not isinstance(det, str) else det[:1500]}")
        if st == "ok":
            for e in ("", ".cob", ".fe.json"):
                if os.path.exists(base + e):
                    os.remove(base + e)
    print(json.dumps({"tally": dict(sorted(tally.items())), "phrases": dict(sorted(counts.items()))}))
    return 0 if set(tally) == {"ok"} else 1


if __name__ == "__main__":
    sys.exit(main())

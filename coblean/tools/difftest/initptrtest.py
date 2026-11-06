#!/usr/bin/env python3
"""Differential testing of INITIALIZE on groups with POINTER items.

IBM Enterprise COBOL 6.4, INITIALIZE rule 1a: items that are not valid MOVE receivers, such as
pointers, are not initialized. The resolver cannot tell a pointer from a 9-digit COMP-5 item, so
the front end lowers a plain INITIALIZE of an identifier with a pointer among its rule-1
candidates to the MOVEs of REPLACING every category BY SPACE or ZERO (rules 1c and 2), which skip
the pointers. GnuCOBOL's pointers have 8 bytes and the model's 4, so the pointer program P is not
compared with GnuCOBOL directly: its twin T has a FILLER PIC X(4) in place of each pointer (the
same layout; FILLER items are not initialized either), which goes through the resolver's plain
INITIALIZE and GnuCOBOL.

Each random program has initrepltest.py's record R (sentinel, data area D, one history slot per
step) with pointers in D: next to other items in a group, in a table, in a nested group, and
under a REDEFINES child (no candidate there). Each step fills D with '#' (the pointers' bytes
too), runs a plain INITIALIZE of one or two identifiers, an INITIALIZE ... REPLACING of 1 to 5
categories, or a pair (plain INITIALIZE X and INITIALIZE X REPLACING every category BY SPACES or
ZERO, then a DISPLAY of whether they left the same bytes), and copies D into its slot. Checks: R
of model(T) equals GnuCOBOL's dump of T (-std=ibm -fbinary-truncate), R of model(P) equals R of
model(T), the DISPLAY lines of the three agree, and every pair shows SAME. Exit status 0 only
when every program passes.

Control: the front end of coblean_fesmall (before this change) zeroes the pointers in a plain
INITIALIZE. Planted faults (recipes, on a copy M of tools/cobolfe; each must give failures):
  M1 the lowered MOVEs include the pointers (MOVE ZERO into them):
     sed 's/for e, occs in self.init_receivers(d.entry):/for e, occs in self.init_receivers(d.entry, pointers=True):/' tools/cobolfe/parser.py > M/parser.py
  M2 alphanumeric-edited items in the lowered MOVEs are not edited:
     sed 's/                if e.ae is not None:$/                if False:/' tools/cobolfe/parser.py > M/parser.py
then COBOLFE=M/cobolfe.py python3 -I -B tools/difftest/initptrtest.py --n 60 --seed 1.

usage: initptrtest.py [--n N] [--seed S] [--k K] [--out DIR] [--show K]
"""
import argparse
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import difftest as D  # noqa: E402
import initrepltest as IR  # noqa: E402
from inspecttest import bump  # noqa: E402

PTR = "@PTR@"   # a pointer slot: `NAME POINTER` in P, `FILLER PIC X(4)` in T


def data_area(rng):
    """D's lines (with pointer slots), its size, and the INITIALIZE candidates."""
    L, cands, size = [], [], 0

    def item(level, name, pic, s):
        nonlocal size
        L.append(f"{' ' * (8 + 3 * (level - 10) // 5)}{level} {name} {pic}.")
        size += s

    L.append("        10 G1.")
    p, s = IR.elem(rng)
    item(15, "G1A", p, s)
    if rng.random() < 0.7:
        item(15, "G1P", PTR, 4)
    p, s = IR.elem(rng, filler=True)
    item(15, "FILLER", p, s)
    p, s = IR.elem(rng)
    item(15, "G1C", p, s)
    if rng.random() < 0.5:
        L.append(f"           15 G1R REDEFINES G1C PIC X({s}).")
    if rng.random() < 0.7:
        m = rng.randint(2, 3)
        L.append(f"           15 T1 OCCURS {m}.")
        pa, sa = IR.elem(rng)
        L.append(f"              20 T1A {pa}.")
        sb = 0
        if rng.random() < 0.6:
            L.append(f"              20 T1P {PTR}.")
            sb = 4
        size += m * (sa + sb)
        cands += [f"T1 ({rng.randint(1, m)})"]
    if rng.random() < 0.6:
        L.append("           15 GS.")
        p, s = IR.elem(rng)
        item(20, "GSA", p, s)
        if rng.random() < 0.6:
            item(20, "GSP", PTR, 4)
        cands.append("GS")
    L.append("        10 G2.")
    p, s = IR.elem(rng)
    item(15, "G2A", p, s)
    L += ["           15 G2B PIC X(4).", "           15 G2C REDEFINES G2B.", f"              20 G2CP {PTR}."]
    size += 4
    p, s = IR.elem(rng)
    item(10, "E1", p, s)
    item(10, "EP", PTR, 4)
    cands += ["G1", "G2", "E1", "D", "G1A"]
    return L, size, cands


def program(rng, k, counts):
    dl, dsize, cands = data_area(rng)
    total = 8 + dsize * (k + 1)
    proc = []
    for j in range(k):
        proc.append("MOVE ALL '#' TO D")
        r = rng.random()
        if r < 0.4:
            ids = rng.sample(cands, rng.choice([1, 1, 2]))
            counts["plain"] = counts.get("plain", 0) + 1
            proc += [f"INITIALIZE {' '.join(ids)}", f"MOVE D TO HS ({j + 1})"]
        elif r < 0.7:
            ids = rng.sample(cands, rng.choice([1, 1, 2]))
            cats = rng.sample(IR.CATS, rng.randint(1, 5))
            counts["replacing"] = counts.get("replacing", 0) + 1
            phr = " ".join(f"{c} BY {rng.choice(IR.OPERANDS[c])}" for c in cats)
            proc += [f"INITIALIZE {' '.join(ids)} REPLACING {phr}", f"MOVE D TO HS ({j + 1})"]
        else:
            x = rng.choice(cands)
            phr = " ".join(f"{c} BY {IR.PLAIN[c]}" for c in rng.sample(IR.CATS, 5))
            counts["pairs"] = counts.get("pairs", 0) + 1
            proc += [f"INITIALIZE {x}", f"MOVE D TO HS ({j + 1})", "MOVE ALL '#' TO D",
                     f"INITIALIZE {x} REPLACING {phr}",
                     f"IF D = HS ({j + 1}) DISPLAY 'C{j + 1} SAME' ELSE DISPLAY 'C{j + 1} DIFF' END-IF"]
    L = ["IDENTIFICATION DIVISION.", "PROGRAM-ID. IPT.", "DATA DIVISION.", "WORKING-STORAGE SECTION.",
         "01  R.", f"    05 SENT PIC X(8) VALUE '{IR.SENT}'.", "    05 D."] + dl + \
        [f"    05 HS OCCURS {k} PIC X({dsize}).", "01  RX REDEFINES R.", f"    05 BYTE PIC X OCCURS {total}.",
         "01  BA PIC A(4) VALUE 'QRST'.", "01  BX PIC X(5) VALUE 'X1Y2Z'.", "01  BI PIC 9(3) VALUE 417.",
         "01  BN PIC S9(3)V99 VALUE -12.34.", "01  IDX PIC 9(5) COMP.", "PROCEDURE DIVISION.", "MAIN-PARA.",
         "    MOVE ALL '#' TO HS (1)"]
    L += [f"    MOVE HS (1) TO HS ({i})" for i in range(2, k + 1)]
    L += ["    " + s for s in proc]
    L += [f"    PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > {total}",
          "       DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING", "    END-PERFORM", "    DISPLAY ' '",
          "    STOP RUN."]
    src = "\n".join(D.wrap_fixed(x) for x in L) + "\n"
    # P: the pointer slots are pointers; T: FILLER PIC X(4) items of the same size
    p = src.replace(f" {PTR}.", " POINTER.")
    lines = []
    for ln in src.split("\n"):
        if ln.endswith(f" {PTR}."):
            head = ln[:len(ln) - len(f" {PTR}.")].rsplit(" ", 1)[0]
            ln = f"{head} FILLER PIC X(4)."
        lines.append(ln)
    return p, "\n".join(lines), total


def model(base, total):
    """(DISPLAY lines, R's bytes) of the front end + cobolrun on base.cob, or (status, detail)."""
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
    mem = bytes(res["mem"])
    off = mem.find(IR.SENT.encode())
    if off < 0:
        return "model-layout", "sentinel not found"
    return [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e], list(mem[off:off + total])


def run(psrc, tsrc, base, total):
    for suf, src in (("_p", psrc), ("_t", tsrc)):
        with open(base + suf + ".cob", "w") as fh:
            fh.write(src)
    c = subprocess.run([D.COBC, "-x"] + D.COBC_FLAGS["std"] + ["-o", base + "_t", base + "_t.cob"],
                       capture_output=True, text=True, timeout=120)
    if c.returncode != 0:
        return "cobc-error", c.stderr[:1500]
    r = subprocess.run([base + "_t"], capture_output=True, env=dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR),
                       timeout=20)
    g = r.stdout.decode("latin-1").splitlines()
    try:
        gdump = [int(x) - 1 for x in g[-1].split()]
    except (ValueError, IndexError):
        return "gnucobol-output", r.stdout[-500:]
    if len(gdump) != total:
        return "gnucobol-output", f"{len(gdump)} bytes dumped, {total} expected"
    mt = model(base + "_t", total)
    if isinstance(mt[0], str):
        return "twin-" + mt[0], mt[1]
    mp = model(base + "_p", total)
    if isinstance(mp[0], str):
        return mp
    if mt[0] != g[:-1]:
        return "twin-mismatch-display", {"gnucobol": g[:-1], "model": mt[0]}
    if mt[1] != gdump:
        i = next(x for x in range(total) if mt[1][x] != gdump[x])
        return "twin-mismatch-storage", {"byte": i, "gnucobol": gdump[i:i + 12], "model": mt[1][i:i + 12]}
    if mp[0] != mt[0]:
        return "mismatch-display", {"twin": mt[0], "pointers": mp[0]}
    if mp[1] != mt[1]:
        i = next(x for x in range(total) if mp[1][x] != mt[1][x])
        return "mismatch-storage", {"byte": i, "twin": mt[1][i:i + 12], "pointers": mp[1][i:i + 12]}
    if any(ln.endswith("DIFF") for ln in mp[0]):
        return "inconsistent", mp[0]
    return "ok", None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=8)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "out_initptr"))
    ap.add_argument("--show", type=int, default=3)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, counts, shown = {}, {}, 0
    for p in range(a.n):
        psrc, tsrc, total = program(random.Random(rng.random()), a.k, counts)
        base = os.path.join(a.out, f"ipt_{a.seed}_{p}")
        st, det = run(psrc, tsrc, base, total)
        bump(tally, a.out, p, st)
        if st != "ok" and shown < a.show:
            shown += 1
            print(f"program {p}: {st}: {json.dumps(det)[:1500] if not isinstance(det, str) else det[:1500]}")
        if st == "ok":
            for s in ("_p", "_t"):
                for e in ("", ".cob", ".fe.json"):
                    if os.path.exists(base + s + e):
                        os.remove(base + s + e)
    print(json.dumps({"tally": dict(sorted(tally.items())), "steps": dict(sorted(counts.items()))}))
    return 0 if set(tally) == {"ok"} else 1


if __name__ == "__main__":
    sys.exit(main())

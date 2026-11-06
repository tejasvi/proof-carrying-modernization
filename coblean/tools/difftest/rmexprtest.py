#!/usr/bin/env python3
"""Differential testing of reference modifiers written as arithmetic expressions.

IBM Enterprise COBOL 6.4 (Reference modification): leftmost-character-position and length "Must
be an arithmetic expression", whose evaluation "must result in a positive nonzero integer". The
front end evaluates integer literals joined by +, -, * and parentheses (unary signs included),
with at most one integer data name of coefficient 1, exactly, to a literal or to name + k.

Each random program runs K statements on reference-modified operands: DISPLAY of the substring,
a comparison with a literal, or a MOVE of a literal into the substring followed by a DISPLAY of
the whole item. The operands are an alphanumeric item, a numeric DISPLAY item, a group and a
table element; the two modifiers are random expressions (or the length is left out) that
evaluate to positions inside the item. Names in the expressions are integer items (DISPLAY,
COMP, COMP-3) whose values the program sets with MOVEs the generator tracks. GnuCOBOL (-std=ibm)
and the front end + cobolrun must produce the same DISPLAY lines. Exit status 0 only when every
program agrees.

Control: the front end of coblean-20261027T0518Z (COBOLFE=<copy>/cobolfe.py) makes most of these
statements unsupported. Planted fault (recipe): in tools/cobolfe/parser.py, sub_of's linear()
returning (a[0], a[1] + c[1]) for "-" too (minus read as plus):
  cp -a tools/cobolfe M && sed -i 's/return (a\\[0\\], a\\[1\\] - c\\[1\\]) if/return (a[0], a[1] + c[1]) if/' M/parser.py
  COBOLFE=M/cobolfe.py python3 -I -B tools/difftest/rmexprtest.py --n 60 --seed 1
must report mismatches.

usage: rmexprtest.py [--n N] [--seed S] [--k K] [--out DIR] [--show K]
"""
import argparse
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import difftest as D  # noqa: E402
from inspecttest import bump, run  # noqa: E402

ALNUM = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
NAMES = [("I1", "PIC 99"), ("I2", "PIC S9(3) COMP"), ("I3", "PIC 9(4) COMP-3")]


def lit(v):
    """A literal of value v (a negative value as a parenthesized unary minus)."""
    return str(v) if v >= 0 else f"(- {-v})"


def atom(s):
    """s as one operand: a literal or a single parenthesized group as it is, else in parentheses."""
    if s.isdigit():
        return s
    if s.startswith("("):
        depth = 0
        for i, ch in enumerate(s):
            depth += {"(": 1, ")": -1}.get(ch, 0)
            if depth == 0:
                if i == len(s) - 1:
                    return s
                break
    return f"({s})"


def const(rng, v, depth):
    """An expression of integer literals that evaluates to v. A unary sign only starts a
    parenthesized group, so no operator is followed by a sign."""
    r = rng.random()
    if depth <= 0 or r < 0.3:
        return lit(v)
    if r < 0.5:
        b = rng.randint(-4, 9)
        return f"{const(rng, v - b, depth - 1)} + {const(rng, b, depth - 1)}"
    if r < 0.7:
        b = rng.randint(-4, 9)
        return f"{const(rng, v + b, depth - 1)} - {atom(const(rng, b, depth - 1))}"
    if r < 0.85:
        d = rng.choice([d for d in range(1, 7) if v % d == 0])
        return f"{atom(const(rng, v // d, depth - 1))} * {atom(const(rng, d, depth - 1))}"
    if r < 0.93:
        return f"(- {atom(const(rng, -v, depth - 1))})" if rng.random() < 0.5 else f"(+ {lit(v)})"
    return f"({const(rng, v, depth - 1)})"


def expr(rng, v, names):
    """An expression that evaluates to v: constant, or one name plus a constant expression."""
    if rng.random() < 0.4:
        return const(rng, v, rng.randint(0, 3))
    n = rng.choice(sorted(names))
    k = v - names[n]
    form = rng.randrange(5)
    if form == 0:
        return n if k == 0 else f"{n} {'+' if k > 0 else '-'} {abs(k)}"
    if form == 1:
        return f"{n} + {const(rng, k, 2)}"
    if form == 2:
        c = const(rng, k, 2)
        return f"({c}) + {n}"
    if form == 3:
        c = const(rng, -k, 2)
        return f"{n} - ({c})"
    k1 = rng.randint(-3, 6)
    return f"({n} + {lit(k1)}) - ({const(rng, k1 - k, 2)})"


def program(rng, k):
    t1 = "".join(rng.choice(ALNUM) for _ in range(20))
    n1 = "".join(rng.choice("0123456789") for _ in range(12))
    names = {n: rng.randint(1, 9) for n, _ in NAMES}
    items = {"T1": 20, "N1": 12, "G1": 14, "TE": 6}
    L = ["IDENTIFICATION DIVISION.", "PROGRAM-ID. RMX.", "DATA DIVISION.",
         "WORKING-STORAGE SECTION.", f"01  T1 PIC X(20) VALUE '{t1}'.", f"01  N1 PIC 9(12) VALUE {n1}.",
         "01  G1.", "    05 G1A PIC X(6) VALUE 'GROUPA'.", "    05 G1B PIC 9(8) VALUE 12345678.",
         "01  TB.", "    05 TE OCCURS 4 PIC X(6)."]
    for (n, pic) in NAMES:
        L.append(f"01  {n} {pic} VALUE {names[n]}.")
    L += ["PROCEDURE DIVISION.", "MAIN-PARA.", "    MOVE 'AAAAAABBBBBBCCCCCCDDDDDD' TO TB"]
    for j in range(k):
        if rng.random() < 0.2:
            n = rng.choice(sorted(names))
            names[n] = rng.randint(1, 9)
            L.append(f"    MOVE {names[n]} TO {n}")
        it = rng.choice(sorted(items))
        size = items[it]
        s = rng.randint(1, size)
        ln = rng.randint(1, size - s + 1)
        opnd = it if it != "TE" else f"TE ({rng.randint(1, 4)})"
        mods = f"{expr(rng, s, names)}:" + ("" if rng.random() < 0.2 else f" {expr(rng, ln, names)}")
        if mods.endswith(":"):
            ln = size - s + 1
        ref = f"{opnd} ({mods})"
        kind = rng.random()
        if kind < 0.5:
            L.append(f"    DISPLAY '{j} [' {ref} ']'")
        elif kind < 0.75:
            v = "".join(rng.choice("AB12") for _ in range(ln))
            L += [f"    IF {ref} = '{v}'", f"        DISPLAY '{j} EQ' ELSE DISPLAY '{j} NE' END-IF"]
        else:
            v = "".join(rng.choice("XYZ789") for _ in range(rng.randint(1, ln + 1)))
            # the numeric item as alphanumeric (it may now hold non-digits)
            whole = {"TE": "TB", "N1": "N1 (1:)"}.get(it, it)
            L += [f"    MOVE '{v}' TO {ref}", f"    DISPLAY '{j} [' {whole} ']'"]
    L.append("    STOP RUN.")
    return "\n".join(D.wrap_fixed(x) for x in L) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=25)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "out_rmexpr"))
    ap.add_argument("--show", type=int, default=3)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, shown = {}, 0
    for p in range(a.n):
        src = program(random.Random(rng.random()), a.k)
        base = os.path.join(a.out, f"rmx_{a.seed}_{p}")
        outs, err = run(src, base)
        if err:
            bump(tally, a.out, p, "error")
            if shown < a.show:
                shown += 1
                print(f"program {p}: {err[:1500]}")
            continue
        g, m = outs
        st = "ok" if g == m else "mismatch"
        bump(tally, a.out, p, st)
        if st != "ok" and shown < a.show:
            shown += 1
            i = next((i for i in range(min(len(g), len(m))) if g[i] != m[i]), min(len(g), len(m)))
            print(f"program {p}: line {i}: gnucobol {g[i] if i < len(g) else None!r} "
                  f"model {m[i] if i < len(m) else None!r} ({len(g)} / {len(m)} lines)")
        if st == "ok":
            for e in ("", ".cob", ".fe.json"):
                if os.path.exists(base + e):
                    os.remove(base + e)
    print(json.dumps({"tally": dict(sorted(tally.items()))}))
    return 0 if set(tally) == {"ok"} else 1


if __name__ == "__main__":
    sys.exit(main())

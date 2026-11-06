#!/usr/bin/env python3
"""Differential testing of switches: SPECIAL-NAMES switch entries, switch-status conditions and
SET mnemonic-name TO ON / OFF.

IBM Enterprise COBOL 6.4: environment-name-2 is an UPSI switch, UPSI-0 to UPSI-7, written
`UPSI-n [[IS] mnemonic-name] [ON [STATUS] [IS] condition-1] [OFF [STATUS] [IS] condition-2]`
(the two phrases in either order); a switch-status condition "is true if the UPSI switch is set
to the value (0 or 1) corresponding to condition-name"; `SET {mnemonic-name}... TO {ON | OFF}`
(repeated) sets the switches. The front end gives each switch a hidden one-byte item.

Each random program declares 1-4 of UPSI-0..UPSI-7 in random spellings and runs K statements:
IF on one condition name, NOT, or AND / OR / parenthesized combinations, EVALUATE TRUE with
switch conditions, and SET of the switches that have a mnemonic name (several names per TO,
several TO phrases per SET). The switches start in random states: GnuCOBOL (-std=ibm) gets them
as COB_SWITCH_n=ON/OFF (or unset = off); the front end reads the same environment
(--profile gnucobol) or, for about half of the programs, gets --switch UPSI-n=ON/OFF while its
environment says the opposite (the option takes precedence). The DISPLAY lines must agree.
Exit status 0 only when every program agrees.

Control: the front end of coblean-20261027T0518Z (COBOLFE=<copy>/cobolfe.py) rejects every
program (the condition names do not resolve). Planted fault (recipe): SET ... TO ON moves "0" and
TO OFF moves "1":
  cp -a tools/cobolfe M && sed -i 's/v = "1" if ts.expect_word("ON", "OFF").val == "ON" else "0"/v = "0" if ts.expect_word("ON", "OFF").val == "ON" else "1"/' M/parser.py
  COBOLFE=M/cobolfe.py python3 -I -B tools/difftest/swtest.py --n 60 --seed 1
must report mismatches.

usage: swtest.py [--n N] [--seed S] [--k K] [--out DIR] [--show K]
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


def decl(rng, n):
    """A switch entry for UPSI-n: (lines, mnemonic or None, {condition name: on})."""
    mnem = f"SW{n}" if rng.random() < 0.7 else None
    phrases = []
    if rng.random() < 0.75 or mnem is None:
        phrases.append(True)
    if rng.random() < 0.75 or not phrases:
        phrases.append(False)
    rng.shuffle(phrases)
    conds, text = {}, [f"UPSI-{n}"]
    if mnem:
        text.append(f"IS {mnem}" if rng.random() < 0.6 else mnem)
    for on in phrases:
        c = f"S{n}-{'ON' if on else 'OFF'}"
        conds[c] = on
        text.append(("ON" if on else "OFF") + (" STATUS" if rng.random() < 0.5 else "") +
                    (" IS" if rng.random() < 0.5 else "") + f" {c}")
    return ["    " + t for t in text], mnem, conds


def cond(rng, conds, depth=0):
    """A condition over switch condition names and its value."""
    r = rng.random()
    if depth >= 2 or r < 0.5:
        c = rng.choice(sorted(conds))
        return c, conds[c]
    if r < 0.65:
        t, v = cond(rng, conds, depth + 1)
        return f"NOT ({t})", not v
    a, va = cond(rng, conds, depth + 1)
    b, vb = cond(rng, conds, depth + 1)
    if rng.random() < 0.5:
        return f"({a}) AND ({b})", va and vb
    return f"({a}) OR ({b})", va or vb


def program(rng, k):
    nums = sorted(rng.sample(range(8), rng.randint(1, 4)))
    state = {n: rng.random() < 0.5 for n in nums}
    L = ["IDENTIFICATION DIVISION.", "PROGRAM-ID. SWX.", "ENVIRONMENT DIVISION.",
         "CONFIGURATION SECTION.", "SPECIAL-NAMES."]
    mnems, conds = {}, {}
    for n in nums:
        lines, m, cs = decl(rng, n)
        L += lines
        if m:
            mnems[m] = n
        conds.update({c: (n, on) for c, on in cs.items()})
    L[-1] += "."
    L += ["DATA DIVISION.", "WORKING-STORAGE SECTION.", "01  W PIC X VALUE 'A'.", "PROCEDURE DIVISION.",
          "MAIN-PARA."]
    for j in range(k):
        r = rng.random()
        vals = {c: state[n] == on for c, (n, on) in conds.items()}
        if r < 0.25 and mnems:
            groups = []
            for _ in range(rng.choice([1, 1, 2])):
                ms = rng.sample(sorted(mnems), rng.randint(1, len(mnems)))
                on = rng.random() < 0.5
                groups.append(f"{' '.join(ms)} TO {'ON' if on else 'OFF'}")
                for m in ms:
                    state[mnems[m]] = on
            L.append("    SET " + " ".join(groups))
        elif r < 0.4:
            L.append("    EVALUATE TRUE")
            for i in range(rng.randint(1, 3)):
                t, _ = cond(rng, vals)
                L.append(f"      WHEN {t} DISPLAY '{j} W{i}'")
            L += [f"      WHEN OTHER DISPLAY '{j} WO'", "    END-EVALUATE"]
        else:
            t, _ = cond(rng, vals)
            L += [f"    IF {t}", f"       DISPLAY '{j} T'", "    ELSE", f"       DISPLAY '{j} F'", "    END-IF"]
    L.append("    STOP RUN.")
    return "\n".join(D.wrap_fixed(x) for x in L) + "\n", nums


def run(src, base, nums, rng):
    with open(base + ".cob", "w") as fh:
        fh.write(src)
    c = subprocess.run([D.COBC, "-x", "-std=ibm", "-o", base, base + ".cob"], capture_output=True,
                       text=True, timeout=120)
    if c.returncode != 0:
        return None, "cobc: " + c.stderr
    start = {n: rng.choice(["ON", "OFF", None]) for n in nums}
    genv = {"PATH": "/usr/bin:/bin", "LD_LIBRARY_PATH": D.LIBDIR}
    genv.update({f"COB_SWITCH_{n}": v for n, v in start.items() if v is not None})
    r = subprocess.run([base], capture_output=True, env=genv, timeout=20)
    fenv = {k: v for k, v in os.environ.items() if not k.startswith("COB_SWITCH_")}
    args = []
    if rng.random() < 0.5:
        fenv.update({f"COB_SWITCH_{n}": v for n, v in start.items() if v is not None})
    else:
        for n, v in start.items():
            on = v == "ON"
            args += ["--switch", f"UPSI-{n}={'ON' if on else 'OFF'}"]
            fenv[f"COB_SWITCH_{n}"] = "OFF" if on else "ON"
    fe = subprocess.run([sys.executable, "-I", D.COBOLFE, base + ".cob", "--profile", "gnucobol", "--main"] +
                        args + ["-o", base + ".fe.json"], capture_output=True, text=True, timeout=120, env=fenv)
    if fe.returncode != 0:
        return None, "cobolfe: " + fe.stderr
    lr = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True, timeout=60)
    if lr.returncode != 0:
        return None, "cobolrun: " + lr.stderr
    res = json.loads(lr.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop"):
        m.append("<model: " + res["signal"] + ">")
    return (r.stdout.decode("latin-1").splitlines(), m), None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=60)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=20)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "out_sw"))
    ap.add_argument("--show", type=int, default=3)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    open(os.path.join(a.out, "results.jsonl"), "w").close()
    rng = random.Random(a.seed)
    tally, shown = {}, 0
    for p in range(a.n):
        prng = random.Random(rng.random())
        src, nums = program(prng, a.k)
        base = os.path.join(a.out, f"swx_{a.seed}_{p}")
        outs, err = run(src, base, nums, prng)
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

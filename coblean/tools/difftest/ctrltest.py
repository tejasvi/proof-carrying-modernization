#!/usr/bin/env python3
"""Differential testing of control flow (PERFORM [THRU], GO TO, loops, EXIT ...).

Random programs of paragraphs (optionally grouped in sections); every paragraph appends its
letter to a trace buffer (reference modification with a variable start) and bumps a step
counter that stops runaway programs.  GnuCOBOL (`-std=ibm`, whose `perform-osvs: yes`
recognises the exit point of any active PERFORM, as IBM does) and the Lean semantics must
produce the same trace and counters.

usage: ctrltest.py [--n N] [--seed S] [--keep]
"""
import argparse
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import difftest as D  # noqa: E402

LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
FRONTEND = False
MAXSTEPS = 60
# GnuCOBOL's EXIT SECTION skips the exit check of the section's last paragraph; IBM documents
# it as an implicit CONTINUE after the last statement (inside the last paragraph)
ALLOW_EXIT_SECTION = False

# item ids
I_R, I_TRACE, I_TLEN, I_STEPS, I_K, I_J, I_FLAG = 1, 2, 3, 4, 5, 6, 7


def ref(i):
    return D.ref(i)


def lit_num(v):
    return {"lit": {"l": {"num": {"v": v, "scale": 0, "digits": 0}}}}


def e_lit(v):
    return D.e_lit(v, 0)


def add_to(item, v):
    return {"add": {"ops": [e_lit(v)], "rcv": [{"ref": ref(item), "rounded": None}], "giving": False,
                    "onSize": None, "notOnSize": []}}


def rel(op, item, v):
    return {"rel": {"op": op, "a": {"ref": {"r": ref(item)}}, "b": lit_num(v)}}


class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.npara = rng.randint(3, 7)
        self.names = [f"P{i}" for i in range(self.npara)]
        # optional sections: contiguous groups
        self.sections = []
        if rng.random() < 0.4:
            cut = sorted(rng.sample(range(1, self.npara), k=min(2, self.npara - 1)))
            bounds = [0] + cut + [self.npara]
            for si in range(len(bounds) - 1):
                self.sections.append((f"S{si}", bounds[si], bounds[si + 1] - 1))

    def sect_of(self, i):
        for (n, a, b) in self.sections:
            if a <= i <= b:
                return n
        return None

    def prologue(self, i):
        letter = LETTERS[i]
        cob = ["ADD 1 TO STEPS", f"IF STEPS > {MAXSTEPS}", "STOP RUN", "END-IF",
               "ADD 1 TO TLEN", f"MOVE '{letter}' TO TRC(TLEN:1)"]
        js = [add_to(I_STEPS, 1),
              {"ite": {"c": rel(">", I_STEPS, MAXSTEPS), "t": ["stopRun"], "e": []}},
              add_to(I_TLEN, 1),
              {"move": {"src": D.op_str(letter),
                        "dsts": [{"item": I_TRACE, "subs": [], "refStart": {"item": {"id": I_TLEN, "k": 0}},
                                  "refLen": {"lit": {"n": 1}}}]}}]
        return cob, js

    def rand_stmt(self, i, depth, inline):
        """A random control statement inside paragraph i."""
        rng = self.rng
        n = self.npara
        r = rng.random()
        later = list(range(i + 1, n))
        if r < 0.30 and later:
            a = rng.choice(later)
            b = rng.choice(range(a, n))
            if self.sections and rng.random() < 0.3:
                # PERFORM a section
                cands = [s for s in self.sections if s[1] > i]
                if cands:
                    s = rng.choice(cands)
                    return [f"PERFORM {s[0]}"], {"perform": {"first": s[0], "last": None, "loop": "once"}}
            loop_c, loop_j = "", "once"
            lr = rng.random()
            if lr < 0.2:
                t = rng.randint(0, 2)
                loop_c, loop_j = f" {t} TIMES", {"times": {"n": e_lit(t)}}
            thru = f" THRU {self.names[b]}" if b != a else ""
            return [f"PERFORM {self.names[a]}{thru}{loop_c}"], \
                {"perform": {"first": self.names[a], "last": self.names[b] if b != a else None, "loop": loop_j}}
        if r < 0.45:
            # mostly forward jumps (backward jumps into a performing paragraph are recursion)
            t = rng.randrange(i, n) if rng.random() < 0.8 else rng.randrange(n)
            guard = rng.randint(5, MAXSTEPS)
            return [f"IF STEPS < {guard}", f"GO TO {self.names[t]}", "END-IF"], \
                {"ite": {"c": rel("<", I_STEPS, guard), "t": [{"goTo": {"target": self.names[t]}}], "e": []}}
        if r < 0.52:
            fwd = self.names[i:] if rng.random() < 0.8 else self.names
            ts = rng.sample(fwd, k=min(3, len(fwd)))
            return [f"GO TO {' '.join(ts)} DEPENDING ON K"], {"goToDep": {"targets": ts, "e": D.e_ref(I_K)}}
        if r < 0.60 and depth == 0:
            # inline loop with possible EXIT PERFORM [CYCLE]
            body_c, body_j = [], []
            for _ in range(rng.randint(1, 2)):
                c, j = self.rand_stmt(i, depth + 1, True)
                body_c += c
                body_j.append(j)
            lim = rng.randint(1, 3)
            return ([f"PERFORM VARYING K FROM 1 BY 1 UNTIL K > {lim}"] + body_c + ["END-PERFORM"],
                    {"performInline": {"body": body_j,
                                       "loop": {"varying": {"testAfter": False, "var": ref(I_K),
                                                            "fromE": e_lit(1), "byE": e_lit(1),
                                                            "c": rel(">", I_K, lim)}}}})
        if r < 0.66 and inline:
            if rng.random() < 0.5:
                return ["IF K = 2", "EXIT PERFORM CYCLE", "END-IF"], \
                    {"ite": {"c": rel("=", I_K, 2), "t": ["exitCycle"], "e": []}}
            return ["IF K = 2", "EXIT PERFORM", "END-IF"], \
                {"ite": {"c": rel("=", I_K, 2), "t": ["exitPerform"], "e": []}}
        if r < 0.72:
            return ["IF STEPS > 10", "EXIT PARAGRAPH", "END-IF"], \
                {"ite": {"c": rel(">", I_STEPS, 10), "t": ["exitPara"], "e": []}}
        if r < 0.76 and self.sect_of(i) and ALLOW_EXIT_SECTION:
            return ["IF STEPS > 12", "EXIT SECTION", "END-IF"], \
                {"ite": {"c": rel(">", I_STEPS, 12), "t": ["exitSection"], "e": []}}
        if r < 0.85 or inline or depth > 0:
            return ["ADD 1 TO J"], add_to(I_J, 1)
        return ["MOVE 2 TO K"], {"move": {"src": lit_num(2), "dsts": [ref(I_K)]}}

    def build(self):
        rng = self.rng
        paras = []
        cob = []
        cur_sect = None
        for i in range(self.npara):
            s = self.sect_of(i)
            if s != cur_sect and s is not None:
                cob.append(f"{s} SECTION.")
                cur_sect = s
            cob.append(f"{self.names[i]}.")
            pc, pj = self.prologue(i)
            sentences_j = [pj]
            sent_c = list(pc)
            for _ in range(rng.randint(1, 3)):
                c, j = self.rand_stmt(i, 0, False)
                sent_c += c
                sentences_j[-1].append(j)
                if rng.random() < 0.25:
                    # sentence boundary
                    cob += ["    " + x for x in sent_c] + ["    ."]
                    sent_c = []
                    sentences_j.append([])
            if i == self.npara - 1 and rng.random() < 0.5:
                sent_c.append("STOP RUN")
                sentences_j[-1].append("stopRun")
            cob += ["    " + x for x in sent_c] + ["    ."]
            paras.append({"name": self.names[i], "sect": s, "sentences": sentences_j})
        return cob, paras


def render(gen, name):
    cob_proc, paras = gen.build()
    lines = ["IDENTIFICATION DIVISION.", f"PROGRAM-ID. {name}.", "DATA DIVISION.",
             "WORKING-STORAGE SECTION.", "01 R.",
             "   05 TRC PIC X(80) VALUE SPACES.",
             "   05 TLEN PIC 9(3) COMP VALUE 0.",
             "   05 STEPS PIC 9(3) COMP VALUE 0.",
             "   05 K PIC 9(3) COMP VALUE 1.",
             "   05 J PIC 9(3) COMP VALUE 0.",
             "   05 FLAG PIC X VALUE 'N'.",
             "01 RX REDEFINES R.", "   05 BYTE PIC X OCCURS 89.", "01 IDX PIC 9(4) COMP.",
             "PROCEDURE DIVISION."]
    # the dump runs in a declarative-free epilogue reached by STOP RUN replacement: we instead
    # dump at the end via a final paragraph that is PERFORMed by an outer driver
    body = ["MAIN-DRIVER.", "    PERFORM P0 THRU " + gen.names[-1], "    PERFORM DUMP", "    STOP RUN."]
    dump = ["DUMP.", "    PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > 89",
            "       DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING",
            "    END-PERFORM", "    DISPLAY ' '."]
    # STOP RUN inside the program must still dump: replace STOP RUN by GO TO STOPPER
    proc = [l.replace("STOP RUN", "GO TO STOPPER") for l in cob_proc]
    stopper = ["STOPPER.", "    PERFORM DUMP", "    STOP RUN."]
    if gen.sections:
        body = ["MAIN SECTION."] + body
        dump = ["DUMPS SECTION."] + dump + stopper
    else:
        dump = dump + stopper
    allp = body + proc + dump
    cobol = "\n".join(D.wrap_fixed(l) for l in lines + allp) + "\n"
    # JSON mirror
    def fix(j):
        # STOP RUN -> GO TO STOPPER in JSON as well
        if j == "stopRun":
            return {"goTo": {"target": "STOPPER"}}
        if isinstance(j, dict):
            return {k: fix(v) for k, v in j.items()}
        if isinstance(j, list):
            return [fix(x) for x in j]
        return j
    paras = fix(paras)
    data = [D.item_json({"id": I_R, "level": 1, "name": "R", "pic": None, "children": [
        {"id": I_TRACE, "level": 5, "name": "TRC", "pic": {"alnum": {"len": 80}}, "value": {"fig": {"f": "space"}}},
        {"id": I_TLEN, "level": 5, "name": "TLEN", "pic": {"num": {"digits": 3, "scale": 0, "signed": False}},
         "usage": "binary", "value": {"num": {"v": 0, "scale": 0}}},
        {"id": I_STEPS, "level": 5, "name": "STEPS", "pic": {"num": {"digits": 3, "scale": 0, "signed": False}},
         "usage": "binary", "value": {"num": {"v": 0, "scale": 0}}},
        {"id": I_K, "level": 5, "name": "K", "pic": {"num": {"digits": 3, "scale": 0, "signed": False}},
         "usage": "binary", "value": {"num": {"v": 1, "scale": 0}}},
        {"id": I_J, "level": 5, "name": "J", "pic": {"num": {"digits": 3, "scale": 0, "signed": False}},
         "usage": "binary", "value": {"num": {"v": 0, "scale": 0}}},
        {"id": I_FLAG, "level": 5, "name": "FLAG", "pic": {"alnum": {"len": 1}}, "value": {"alnum": {"bs": [78]}}},
    ]})]
    sect_main = "MAIN" if gen.sections else None
    sect_dump = "DUMPS" if gen.sections else None
    jparas = [{"name": "MAIN-DRIVER", "sect": sect_main, "sentences": [[
        {"perform": {"first": "P0", "last": gen.names[-1], "loop": "once"}},
        {"perform": {"first": "DUMP", "last": None, "loop": "once"}}, "stopRun"]]}]
    jparas += paras
    jparas += [{"name": "DUMP", "sect": sect_dump, "sentences": [[]]},
               {"name": "STOPPER", "sect": sect_dump, "sentences": [[
                   {"perform": {"first": "DUMP", "last": None, "loop": "once"}}, "stopRun"]]}]
    prog = {"name": name, "config": dict(D.CONFIG), "dialect": {"divExtraForRounded": True},
            "data": data, "paras": jparas, "isMain": True}
    return cobol, prog


def run_one(idx, rng, outdir, keep):
    gen = Gen(rng)
    name = f"C{idx:05d}"
    cobol, prog = render(gen, name)
    base = os.path.join(outdir, name)
    open(base + ".cob", "w").write(cobol)
    json.dump(prog, open(base + ".json", "w"))
    c = subprocess.run([D.COBC, "-x", "-std=ibm", "-o", base, base + ".cob"], capture_output=True, text=True)
    if c.returncode != 0:
        return ("cobc-error", c.stderr[:1500])
    env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
    try:
        r = subprocess.run([base], capture_output=True, text=True, env=env, timeout=20)
    except subprocess.TimeoutExpired:
        return ("gnucobol-timeout", None)
    if r.returncode != 0:
        return ("gnucobol-abend", (r.stdout + r.stderr)[-500:])
    g = [int(x) - 1 for x in r.stdout.split()][:89]
    l = subprocess.run([D.COBOLRUN, base + ".json"], capture_output=True, text=True, timeout=60)
    if l.returncode != 0:
        return ("cobolrun-error", l.stderr[:1500])
    res = json.loads(l.stdout)
    if "abandoned PERFORM" in res["signal"]:
        return ("lean-unsupported-resume", None)
    if "recursive PERFORM" in res["signal"]:
        return ("lean-unsupported-recursion", None)
    if not res["signal"].startswith("stop:"):
        return ("lean-signal", {"signal": res["signal"], "gnucobol_trace": bytes(g[:80]).decode(errors="replace").rstrip()})
    lb = res["mem"][:89]
    if g != lb:
        return ("mismatch", {"gnucobol_trace": bytes(g[:80]).decode(errors="replace").rstrip(),
                             "lean_trace": bytes(lb[:80]).decode(errors="replace").rstrip(),
                             "gnucobol_tail": g[80:], "lean_tail": lb[80:]})
    if FRONTEND:
        fe = subprocess.run([sys.executable, "-I", D.COBOLFE, base + ".cob", "--profile", "gnucobol",
                             "--main", "-o", base + ".fe.json"], capture_output=True, text=True)
        if fe.returncode != 0:
            return ("frontend-error", fe.stderr[:1500])
        unsup = [ln for ln in fe.stderr.splitlines() if "unsupported" in ln and "DISPLAY" not in ln]
        if unsup:
            return ("frontend-unsupported", "\n".join(unsup)[:1500])
        fl = subprocess.run([D.COBOLRUN, base + ".fe.json"], capture_output=True, text=True, timeout=60)
        if fl.returncode != 0:
            return ("frontend-cobolrun-error", fl.stderr[:1500])
        fres = json.loads(fl.stdout)
        # the dump paragraph (DISPLAY ... WITH NO ADVANCING) is outside the IR: it faults there
        if not ("unsupported" in fres["signal"] and "DISPLAY" in fres["signal"]):
            return ("frontend-signal", fres["signal"])
        if fres["mem"][:89] != lb:
            return ("frontend-mismatch", {"lean_trace": bytes(lb[:80]).decode(errors="replace").rstrip(),
                                          "frontend_trace": bytes(fres["mem"][:80]).decode(errors="replace").rstrip(),
                                          "lean_tail": lb[80:], "frontend_tail": fres["mem"][80:89]})
    if not keep:
        for ext in ("", ".cob", ".json", ".fe.json", ".c", ".c.h", ".c.l.h"):
            if os.path.exists(base + ext):
                os.remove(base + ext)
    return ("ok", None)


def bump(tally, out, case, status):
    """Count one case and append it to OUT/results.jsonl (one JSON object per case)."""
    tally[status] = tally.get(status, 0) + 1
    with open(os.path.join(out, "results.jsonl"), "a") as fh:
        fh.write(json.dumps({"case": case, "status": status}) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=50)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=os.path.join(D.ROOT, "tools", "difftest", "out_ctrl"))
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--frontend", action="store_true",
                    help="also check the IR the COBOL front end extracts from the same source")
    args = ap.parse_args()
    global FRONTEND
    FRONTEND = args.frontend
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, fails = {}, []
    for i in range(args.n):
        st, info = run_one(i, random.Random(rng.random()), args.out, args.keep)
        bump(tally, args.out, i, st)
        if st != "ok":
            fails.append((i, st, info))
    print(json.dumps({"tally": tally}))
    for i, st, info in fails[:15]:
        print(f"--- C{i:05d} {st}")
        print(json.dumps(info)[:1200] if not isinstance(info, str) else info[:1200])
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())

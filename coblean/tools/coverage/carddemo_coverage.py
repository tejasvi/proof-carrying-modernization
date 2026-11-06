"""Front-end and semantics coverage over the CardDemo programs.

For each COBOL program: extract it with tools/cobolfe (IBM profile), count its statements and
its `unsupported` statements (by kind), and check that the Lean resolver accepts it (cobolrun
with no input files: any outcome but a resolution error counts).

usage: python3 -I tools/coverage/carddemo_coverage.py CBL_DIR CPY_DIRS OUT_DIR COBOLRUN [FE_OPTS...]
CPY_DIRS is a ':'-separated list of copybook directories; FE_OPTS go to cobolfe (e.g.
--tab-width 4).
"""
import json, os, subprocess, sys

STMT_LIST_KEYS = ("sentences",)

def walk_stmts(node, acc):
    """Count statements: dicts with one key inside statement lists, recursively."""
    if isinstance(node, list):
        for x in node:
            walk_stmts(x, acc)
    elif isinstance(node, dict):
        if len(node) == 1:
            (k, v), = node.items()
            acc.setdefault(k, 0)
            acc[k] += 1
            walk_stmts(v, acc)
        else:
            for v in node.values():
                walk_stmts(v, acc)

def stmt_kinds(prog):
    kinds = {}
    for p in prog["paras"]:
        for sent in p["sentences"]:
            for st in sent:
                count_stmt(st, kinds)
    return kinds

STMT_NESTS = ("then", "else", "body", "stmts", "atEnd", "notAtEnd", "invalid", "notInvalid",
              "onSize", "notOnSize", "whens", "other", "onOverflow", "notOnOverflow", "onException",
              "notOnException", "atEndOf", "eop")

def count_stmt(st, kinds):
    if not isinstance(st, dict) or len(st) != 1:
        return
    (k, v), = st.items()
    kinds[k] = kinds.get(k, 0) + 1
    # nested statement lists anywhere inside the statement's payload
    def nested(x):
        if isinstance(x, list):
            if x and all(isinstance(y, dict) and len(y) == 1 for y in x) and \
               all(next(iter(y)) in KNOWN for y in x):
                for y in x:
                    count_stmt(y, kinds)
            else:
                for y in x:
                    nested(y)
        elif isinstance(x, dict):
            for y in x.values():
                nested(y)
    nested(v)

KNOWN = set()

def main():
    cbl, cpy, out, cobolrun = sys.argv[1:5]
    fe_opts = sys.argv[5:]
    incs = []
    for d in cpy.split(":"):
        incs += ["-I", d]
    os.makedirs(out, exist_ok=True)
    rows = []
    progs = sorted(f for f in os.listdir(cbl) if f.lower().endswith(".cbl"))
    for f in progs:
        name = os.path.splitext(f)[0].upper()
        ir = os.path.join(out, name + ".json")
        r = subprocess.run([sys.executable, "-I", os.path.join(os.path.dirname(__file__), "..", "cobolfe", "cobolfe.py"),
                            os.path.join(cbl, f), *incs, "-o", ir, "--report", *fe_opts],
                           capture_output=True, text=True)
        row = {"program": name, "extracted": r.returncode == 0 and os.path.exists(ir)}
        if not row["extracted"]:
            row["error"] = (r.stderr.strip().splitlines() or ["?"])[-1][:200]
            rows.append(row); continue
        rep = json.loads(r.stdout[r.stdout.index("{"):]) if "{" in r.stdout else {}
        unsup = rep.get("unsupported", [])
        row["unsupported"] = len(unsup)
        kinds = {}
        for u in unsup:
            k = u.get("what", u.get("stmt", str(u)))[:60] if isinstance(u, dict) else str(u)[:60]
            kinds[k] = kinds.get(k, 0) + 1
        row["unsupported_kinds"] = kinds
        prog = json.load(open(ir))
        if not KNOWN:
            pass
        row["paragraphs"] = len(prog["paras"])
        # statements: every one-key dict that appears directly in a sentence or in a nested
        # statement list
        n = [0]
        def count(st):
            if isinstance(st, dict) and len(st) == 1:
                n[0] += 1
                for v in st.values():
                    nest(v)
        def nest(x):
            if isinstance(x, list):
                for y in x:
                    if isinstance(y, list):
                        nest(y)
                    elif isinstance(y, dict) and len(y) == 1 and next(iter(y)) not in NON_STMT:
                        count(y)
                    else:
                        nest(y)
            elif isinstance(x, dict):
                for k2, y in x.items():
                    if k2 in NON_STMT_FIELDS:
                        continue
                    nest(y)
        for p in prog["paras"]:
            for sent in p["sentences"]:
                for st in sent:
                    count(st)
        row["statements"] = n[0]
        rr = subprocess.run([cobolrun, ir, "--fuel", "2000"], capture_output=True, text=True, timeout=600)
        row["resolves"] = rr.returncode == 0
        if rr.returncode == 0:
            try:
                row["signal_no_input"] = json.loads(rr.stdout)["signal"][:60]
            except Exception:
                row["signal_no_input"] = "?"
        else:
            row["resolve_error"] = (rr.stderr.strip().splitlines() or ["?"])[-1][:200]
        rows.append(row)
    json.dump(rows, open(os.path.join(out, "coverage.json"), "w"), indent=1)
    for row in rows:
        print(json.dumps(row))

# one-key dicts that are expressions/operands, not statements
NON_STMT = {"lit", "ref", "str", "num", "fig", "all", "l", "add", "sub", "mul", "div", "neg", "pow",
            "fn", "cmp", "and", "or", "not", "cond", "class", "sign", "alnum", "bs", "v"}
NON_STMT_FIELDS = {"ops", "src", "dst", "dsts", "cond", "expr", "lit", "ref", "from", "into", "key",
                   "giving", "by", "to", "using", "args", "subs"}

if __name__ == "__main__":
    main()

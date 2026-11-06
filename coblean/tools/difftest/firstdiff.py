#!/usr/bin/env python3
"""Find the first statement after which GnuCOBOL and the Lean semantics disagree.

usage: bisect.py out/T00480 [--trunc std|bin]
Truncates the generated program after k statements (k = 1..n) and compares the record
bytes of both implementations."""
import json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(__file__))
import difftest as D  # noqa

class F:
    pass


def fields_of(prog):
    out = []
    for it in prog["data"][0]["children"]:
        f = F()
        f.name, f.id = it["name"], it["id"]
        pic = it["pic"]
        f.sign_lead, f.sign_sep, f.just = it["signLead"], it["signSep"], it["just"]
        if "num" in pic:
            f.kind, f.digits, f.scale, f.signed = "num", pic["num"]["digits"], pic["num"]["scale"], pic["num"]["signed"]
            f.usage = it["usage"]
            f.length = 0
        elif "alnum" in pic:
            f.kind, f.length, f.usage = "alnum", pic["alnum"]["len"], "display"
            f.digits = f.scale = 0; f.signed = False
        else:
            f.kind, f.usage = "edit", "display"
            f.edit = ("", " ".join(map(str, pic["numEdited"]["pic"])))
            f.digits = f.scale = 0; f.signed = False; f.length = 0
        out.append(f)
    return out


def show(fields, bs):
    if bs is None:
        return "-"
    res, off = [], 0
    for f in fields:
        n = D.record_size([f])
        v = D.decode_field(f, bs[off:off + n])
        if f.kind == "num" and f.scale:
            v = f"{v / 10 ** f.scale:.{f.scale}f}"
        elif not isinstance(v, int):
            v = bytes(v).decode(errors="replace")
        res.append(f"{f.name}={v}")
        off += n
    return " ".join(res)


def main():
    base = sys.argv[1]
    trunc = "std"
    if "--trunc" in sys.argv:
        trunc = sys.argv[sys.argv.index("--trunc") + 1]
    prog = json.load(open(base + ".json"))
    cob = open(base + ".cob").read().split("\n")
    stmts = prog["paras"][0]["sentences"][0][:-1]
    # COBOL statement boundaries: lines in the procedure division starting a statement
    start = next(i for i, l in enumerate(cob) if l.strip() == "MAIN-PARA.") + 1
    tail = next(i for i, l in enumerate(cob) if "PERFORM VARYING IDX" in l)
    verbs = ("MOVE", "COMPUTE", "ADD", "SUBTRACT", "MULTIPLY", "DIVIDE", "IF")
    body = cob[start:tail]
    heads = [i for i, l in enumerate(body) if l.strip().split(" ")[0] in verbs
             and not l.strip().startswith(("MOVE 'Y' TO FLAG", "MOVE 'N' TO FLAG"))]
    # statements of IF blocks contain nested MOVEs: keep only top-level heads (indent 11)
    heads = [i for i in heads if body[i].startswith("           ") and not body[i].startswith("            ")]
    assert len(heads) == len(stmts), (len(heads), len(stmts))
    total = int(re.search(r"OCCURS (\d+)", "\n".join(cob)).group(1))
    prev = None
    for k in range(1, len(stmts) + 1):
        end = heads[k] if k < len(heads) else len(body)
        c2 = cob[:start] + body[:end] + cob[tail:]
        p2 = dict(prog)
        p2["paras"] = [dict(prog["paras"][0], sentences=[stmts[:k] + ["stopRun"]])]
        b2 = base + f"_k{k}"
        open(b2 + ".cob", "w").write("\n".join(c2))
        json.dump(p2, open(b2 + ".json", "w"))
        r = subprocess.run([D.COBC, "-x"] + D.COBC_FLAGS[trunc] + ["-o", b2, b2 + ".cob"], capture_output=True, text=True)
        if r.returncode:
            print("cobc failed", r.stderr[:500]); return
        env = dict(os.environ, LD_LIBRARY_PATH=D.LIBDIR)
        g = [int(x) - 1 for x in subprocess.run([b2], capture_output=True, text=True, env=env).stdout.split()]
        l = json.loads(subprocess.run([D.COBOLRUN, b2 + ".json"], capture_output=True, text=True).stdout)["mem"][:total]
        if g != l:
            print(f"first divergence after statement {k}:")
            print("\n".join(body[heads[k-1]:end]))
            fields = fields_of(prog)
            print("before:", show(fields, prev))
            print("gnucobol after:", show(fields, g))
            print("lean after:    ", show(fields, l))
            return
        prev = l
    print("no divergence")

main()

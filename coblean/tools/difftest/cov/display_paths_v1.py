"""Which DISPLAY operands of the theorem programs' IRs fall in the display forms where GnuCOBOL
-std=ibm and coblean differ (so the coverage testers could not compare them)?

usage: python3 -I -B display_paths_v1.py IR.json...
For every DISPLAY statement (any nesting), classifies each operand: alphanumeric or group item,
alphanumeric literal, figurative constant (compared everywhere); numeric DISPLAY item unsigned or
SIGN SEPARATE (compared by cov_f4disp --part items); and the uncompared forms: numeric item with
USAGE COMP-3 signed, COMP/BINARY, COMP-5, numeric DISPLAY item with an embedded sign, numeric
literal with decimal places (compared only under GnuCOBOL -std=default, cov_f4disp --part lit).
"""
import json
import sys


def walk(x):
    if isinstance(x, dict):
        yield x
        for v in x.values():
            yield from walk(v)
    elif isinstance(x, list):
        for v in x:
            yield from walk(v)


def items(ir):
    out = {}

    def rec(lst):
        for it in lst:
            out[it["id"]] = it
            rec(it.get("children", []))
    rec(ir.get("data", []))
    return out


def kind(op, its):
    if "ref" in op:
        it = its.get(op["ref"]["r"]["item"])
        if it is None:
            return "unknown item"
        p = it.get("pic")
        if not (isinstance(p, dict) and "num" in p):
            return "alphanumeric/group/edited item"
        if op["ref"]["r"].get("refStart") is not None:
            return "reference-modified numeric item (bytes)"
        u, sg = it.get("usage"), p["num"].get("signed")
        if u == "display":
            if not sg or it.get("signSep"):
                return "numeric DISPLAY item, unsigned or SIGN SEPARATE (compared)"
            return "UNCOMPARED: numeric DISPLAY item with an embedded sign"
        if u == "packed" and not sg:
            return "unsigned COMP-3 item (compared)"
        return f"UNCOMPARED: numeric item usage {u}{' signed' if sg else ''}"
    if "lit" in op:
        lv = op["lit"]["l"]
        if "num" in lv:
            return ("UNCOMPARED under -std=ibm: numeric literal with decimals"
                    if lv["num"].get("scale", 0) > 0 else "integer numeric literal (compared)")
        return "alphanumeric literal or figurative constant (compared)"
    return "other"


def main():
    total = {}
    for path in sys.argv[1:]:
        ir = json.load(open(path))
        its = items(ir)
        cnt = {}
        for o in walk(ir):
            d = o.get("display")
            if isinstance(d, dict) and isinstance(d.get("ops"), list):
                for op in d["ops"]:
                    k = kind(op, its)
                    cnt[k] = cnt.get(k, 0) + 1
                    total[k] = total.get(k, 0) + 1
        unc = {k: v for k, v in cnt.items() if k.startswith("UNCOMPARED")}
        print(f"== {path.split('/')[-1]}: {sum(cnt.values())} DISPLAY operands; uncompared forms: {unc or 'none'}")
    print("all:", json.dumps(dict(sorted(total.items())), indent=1))


main()

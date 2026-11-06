"""Probe an LLBC file: top-level keys, counts, and the shape of a trait decl (for writing llbc_dyn.py)."""
import json, sys
d = json.load(open(sys.argv[1]))
t = d["translated"]
print("keys", list(t.keys()))
for k, v in t.items():
    if isinstance(v, list):
        print(k, len(v), sum(1 for x in v if x))
td = [x for x in t["trait_decls"] if x and x["item_meta"].get("is_local")]
print("local trait decls", len(td))
x = td[0]
print(json.dumps({k: (v if k != "item_meta" else {kk: vv for kk, vv in v.items() if kk in ("name", "span", "is_local")}) for k, v in x.items()}, default=str)[:3000])

"""Probe: the trait impls of a local trait (name, module path, method list shape) in an LLBC file."""
import json, sys
d = json.load(open(sys.argv[1])); t = d["translated"]; want = sys.argv[2]
def nm(n): return "::".join(c["Ident"][0] if "Ident" in c else "{" + next(iter(c)) + "}" for c in n)
tid = [x["def_id"] for x in t["trait_decls"] if x and nm(x["item_meta"]["name"]).endswith("::" + want)]
print("trait ids", tid)
for x in t["trait_impls"]:
    if not x: continue
    s = json.dumps(x)
    if not x["item_meta"].get("is_local"): continue
    tr = x.get("impl_trait") or {}
    if tr.get("id") in tid:
        print("IMPL", json.dumps(x["item_meta"]["name"])[:600])
        print("  keys", list(x.keys()))
        print("  methods", json.dumps(x.get("methods"))[:800])

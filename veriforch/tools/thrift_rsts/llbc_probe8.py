"""Probe: the JSON of a type decl (by name) in an LLBC, and an opaque foreign type decl for comparison."""
import json, sys
sys.path.insert(0, "/home/user/veriforch/orch")
from veriforch.adapters.rust import build as rb
d = json.load(open(sys.argv[1])); t = d["translated"]
for x in t["type_decls"]:
    if x and rb._name(x["item_meta"]["name"]) == sys.argv[2]:
        print(json.dumps({k: v for k, v in x.items() if k != "item_meta"})[:3000])
        print("META", json.dumps(x["item_meta"])[:800])
n = 0
for x in t["type_decls"]:
    if x and x.get("kind") == "Opaque":
        print("OPAQUE", rb._name(x["item_meta"]["name"]), json.dumps({k: v for k, v in x.items() if k != "item_meta"})[:600])
        n += 1
        if n > 2: break
print("kinds", sorted({(next(iter(x["kind"])) if isinstance(x["kind"], dict) else x["kind"]) for x in t["type_decls"] if x}))

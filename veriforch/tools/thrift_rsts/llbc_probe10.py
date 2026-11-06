"""Probe: the Mixed declaration groups of an LLBC (item kinds and names) and their positions in ordered_decls."""
import json, sys
sys.path.insert(0, "/home/user/veriforch/orch")
from veriforch.adapters.rust import build as rb
d = json.load(open(sys.argv[1])); t = d["translated"]
key = {"Type": "type_decls", "Fun": "fun_decls", "Global": "global_decls", "TraitDecl": "trait_decls", "TraitImpl": "trait_impls"}
first_fun = None
for i, g in enumerate(t["ordered_decls"]):
    k = next(iter(g))
    if k == "Fun" and first_fun is None:
        first_fun = i
    if k == "Mixed":
        items = g[k]["Rec"]
        desc = []
        for e in items:
            ek = next(iter(e)); x = t[key[ek]][e[ek]]
            desc.append(f"{ek}:{rb._name(x['item_meta']['name']) if x else None}")
        print(i, len(items), desc[:6])
print("groups", len(t["ordered_decls"]), "first Fun group at", first_fun)

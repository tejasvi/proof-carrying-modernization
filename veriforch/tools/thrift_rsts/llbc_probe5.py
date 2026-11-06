"""Probe: every item whose JSON mentions a trait decl id in a trait ref ("id": N, "generics"), by kind and locality."""
import json, sys, collections
sys.path.insert(0, "/home/user/veriforch/orch")
from veriforch.adapters.rust import build as rb
d = json.load(open(sys.argv[1])); t = d["translated"]; want = sys.argv[2]
tids = [x["def_id"] for x in t["trait_decls"] if x and rb._name(x["item_meta"]["name"]) == want]
print("trait ids", tids)
for kind in ("fun_decls", "type_decls", "trait_impls", "global_decls", "trait_decls"):
    for x in t[kind]:
        if not x: continue
        s = json.dumps({k: v for k, v in x.items() if k != "body"})
        sb = json.dumps(x.get("body")) if kind == "fun_decls" else ""
        for tid in tids:
            key = f'"id": {tid}, "generics"'
            if key in s or key in sb:
                print(kind, "local" if x["item_meta"].get("is_local") else "lib", rb._name(x["item_meta"]["name"]), "sig" if key in s else "", "body" if key in sb else "")

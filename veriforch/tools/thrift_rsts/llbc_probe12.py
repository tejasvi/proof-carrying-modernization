"""Probe: trait declarations whose method signatures contain a dyn Trait (with spans, for the prune file)."""
import json, sys
sys.path.insert(0, "/home/user/veriforch/orch")
from veriforch.adapters.rust import build as rb
d = json.load(open(sys.argv[1])); t = d["translated"]
items = {(x["kind"], x["id"]): x for x in rb.llbc_items(t)}
for x in t["trait_decls"]:
    if not x: continue
    dyn = [m["skip_binder"]["name"] for m in x.get("methods") or [] if m and '"DynTrait"' in json.dumps(m["skip_binder"].get("signature"))]
    if dyn:
        it = items.get(("trait_decl", x["def_id"]))
        print(json.dumps({"path": rb._name(x["item_meta"]["name"]), "local": x["item_meta"].get("is_local"), "dyn_methods": dyn,
                          "file": it and it["file"], "line": it and it["l0"], "end": it and it["l1"]}))

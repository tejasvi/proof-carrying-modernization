"""Probe: the LLBC items of a dependency crate (name prefix), with opacity and body presence."""
import json, sys
sys.path.insert(0, "/home/user/veriforch/orch")
from veriforch.adapters.rust import build as rb
d = json.load(open(sys.argv[1])); t = d["translated"]; pre = sys.argv[2]
for kind in ("fun_decls", "trait_decls", "trait_impls", "type_decls", "global_decls"):
    for x in t[kind]:
        if not x: continue
        nm = rb._name(x["item_meta"]["name"])
        if nm.startswith(pre):
            body = x.get("body")
            print(kind, nm, "opacity=", x["item_meta"].get("opacity"), "body=", (next(iter(body)) if isinstance(body, dict) else body) if kind == "fun_decls" else "")

"""Probe: local functions calling library functions whose signature has a Pattern bound (find/contains/...);
prints their raw names (for Charon --opaque patterns)."""
import json, sys
sys.path.insert(0, "/home/user/veriforch/orch")
from veriforch.adapters.rust import build as rb
from pathlib import Path
d = json.load(open(sys.argv[1])); t = d["translated"]
want = set(sys.argv[2].split(","))
for x in t["fun_decls"]:
    if not x or not x["item_meta"].get("is_local") or not isinstance(x.get("body"), dict): continue
    ids = rb._fun_ids(x["body"])
    callees = {rb._name(t["fun_decls"][i]["item_meta"]["name"]) for i in ids if i < len(t["fun_decls"]) and t["fun_decls"][i]}
    hit = callees & want
    if hit:
        nm = x["item_meta"]["name"]
        impl = [c for c in nm if "Impl" in c]
        extra = ""
        if impl:
            ie = impl[0]["Impl"]
            if "Trait" in ie:
                ti = t["trait_impls"][ie["Trait"]]
                extra = "trait=" + rb._name(t["trait_decls"][ti["impl_trait"]["id"]]["item_meta"]["name"])
            else:
                extra = "inherent " + json.dumps(ie)[:200]
        sp = rb._span(x["item_meta"]["span"])
        print(rb._name(nm), sorted(hit), extra, sp["beg"]["line"] if sp else "")

"""Probe: local functions whose bodies call library functions generic over core::str::pattern::Pattern."""
import json, sys, collections
sys.path.insert(0, "/home/user/veriforch/orch")
from veriforch.adapters.rust import build as rb
funs, _ = rb.llbc_functions(__import__("pathlib").Path(sys.argv[1]))
d = json.load(open(sys.argv[1])); t = d["translated"]
pat_ids = [x["def_id"] for x in t["trait_decls"] if x and rb._name(x["item_meta"]["name"]) == "core::str::pattern::Pattern"]
print("Pattern trait ids", pat_ids)
# library functions whose signature mentions the Pattern trait (by its id in a trait clause)
def mentions(obj, tid):
    s = json.dumps(obj)
    return f'"id": {tid}, "generics"' in s
lib_pat = set()
for x in t["fun_decls"]:
    if x and not x["item_meta"].get("is_local") and any(mentions(x.get("signature"), tid) for tid in pat_ids):
        lib_pat.add(rb._name(x["item_meta"]["name"]))
print("library functions mentioning Pattern:", len(lib_pat)); print(sorted(lib_pat)[:60])
hits = [f for f in funs if set(f["lib_callees"]) & lib_pat]
print("local functions calling them:", len(hits))
for f in hits:
    print(f["path"], f["file"], f["line"], sorted(set(f["lib_callees"]) & lib_pat))

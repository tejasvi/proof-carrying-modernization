"""Probe: the `vtable` field of trait impls (values seen), and of a trait decl."""
import json, sys, collections
sys.path.insert(0, "/home/user/veriforch/orch")
from veriforch.adapters.rust import build as rb
d = json.load(open(sys.argv[1])); t = d["translated"]
c = collections.Counter()
ex = {}
for x in t["trait_impls"]:
    if not x: continue
    v = x.get("vtable")
    k = json.dumps(v)[:60] if not isinstance(v, dict) else "dict:" + ",".join(v.keys())
    c[k] += 1
    ex.setdefault(k, (rb._name(x["item_meta"]["name"]), json.dumps(v)[:300]))
print(c)
for k, v in ex.items(): print(k, "=>", v)
tdk = collections.Counter()
for x in t["trait_decls"]:
    if not x: continue
    v = x.get("vtable")
    tdk[json.dumps(v)[:80]] += 1
print("trait decl vtable:", tdk.most_common(5))
g = next(x for x in t["global_decls"] if x and rb._name(x["item_meta"]["name"]) == "thrift::protocol::binary::{impl}::{Builtin}")
print("GLOBAL keys", list(g.keys()), json.dumps({k: v for k, v in g.items() if k not in ("item_meta",)})[:800])

"""Probe: shapes needed for the dyn-payload transform: the User variant field type, item_names format, a foreign
opaque type's item_meta."""
import json, sys
sys.path.insert(0, "/home/user/veriforch/orch")
from veriforch.adapters.rust import build as rb
d = json.load(open(sys.argv[1])); t = d["translated"]
e = next(x for x in t["type_decls"] if x and rb._name(x["item_meta"]["name"]) == "thrift::errors::Error")
print("USER", json.dumps(e["kind"]["Enum"][3]["fields"][0]["ty"])[:1500])
print("ITEM_NAMES", type(t["item_names"]).__name__, json.dumps(t["item_names"][:3] if isinstance(t["item_names"], list) else list(t["item_names"].items())[:3])[:600])
print("SHORT_NAMES", json.dumps(t["short_names"][:2] if isinstance(t["short_names"], list) else list(t["short_names"].items())[:2])[:400])
u = next(x for x in t["type_decls"] if x and rb._name(x["item_meta"]["name"]) == "uuid::Uuid")
print("UUID_META", json.dumps(u["item_meta"])[:1200])
print("UUID_KEYS", list(u.keys()))

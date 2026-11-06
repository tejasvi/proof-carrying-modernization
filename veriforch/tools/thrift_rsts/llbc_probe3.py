"""Probe: index == def_id in decl vectors; ordered_decls shape; trait method default refs."""
import json, sys, collections
d = json.load(open(sys.argv[1])); t = d["translated"]
for k in ("fun_decls", "type_decls", "global_decls", "trait_decls", "trait_impls"):
    bad = [i for i, x in enumerate(t[k]) if x and x["def_id"] != i]
    print(k, "len", len(t[k]), "index!=def_id", len(bad))
print("ordered_decls sample", json.dumps(t["ordered_decls"][:3])[:400])
c = collections.Counter()
for g in t["ordered_decls"]:
    k = next(iter(g)); v = g[k]; c[(k, next(iter(v)) if isinstance(v, dict) else type(v).__name__)] += 1
print(c)
mixed = [g for g in t["ordered_decls"] if "Mixed" in g]
print("mixed sample", json.dumps(mixed[:2])[:600])
td = [x for x in t["trait_decls"] if x and x["item_meta"].get("is_local")]
for x in td:
    print("TRAIT", x["def_id"], "::".join(c["Ident"][0] for c in x["item_meta"]["name"] if "Ident" in c), [ (m["skip_binder"]["name"], (m["skip_binder"].get("default") or {}).get("id") if isinstance(m["skip_binder"].get("default"), dict) else m["skip_binder"].get("default")) for m in x["methods"]])

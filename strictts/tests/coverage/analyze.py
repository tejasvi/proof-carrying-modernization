"""Coverage report tables: per project, combined, and the greedy 'lift' sequence (which rule,
when supported, covers the most additional functions)."""
import json, sys, collections
files = sys.argv[1:]
projects = []
for f in files:
    d = json.load(open(f))
    projects.append((d['summary']['label'], d['rows']))

def table(label, rows, nrules=8, next_=5):
    tot = len(rows); cov = sum(r['status'] == 'covered' for r in rows)
    loc = sum(r['loc'] for r in rows); cloc = sum(r['loc'] for r in rows if r['status'] == 'covered')
    fns = collections.Counter(); only = collections.Counter(); ext = collections.Counter()
    for r in rows:
        ks = list(r['rules'])
        for k in ks: fns[k] += 1
        if len(ks) == 1: only[ks[0]] += 1
        for x in set(r['externals']): ext[x] += 1
    onlyext = sum(1 for r in rows if r['rules'] and set(r['rules']) <= {'external-call', 'external-type'})
    out = [f"{label}: functions {cov}/{tot} ({100*cov/tot:.1f}%), LOC {cloc}/{loc} ({100*cloc/max(loc,1):.1f}%), blocked only by external-call/type: {onlyext}"]
    out.append("  rules (functions blocked / only blocker): " + ", ".join(f"{k} {n}/{only[k]}" for k, n in fns.most_common(nrules)))
    out.append("  externals: " + ", ".join(f"{k} {n}" for k, n in ext.most_common(next_)))
    return "\n".join(out)

def greedy(rows, steps=12):
    lifted = set(); base = sum(r['status'] == 'covered' for r in rows)
    sets = [frozenset(r['rules']) for r in rows if r['status'] != 'covered']
    out = [f"greedy lifts (start {base}/{len(rows)} covered):"]
    cur = base
    for _ in range(steps):
        best = None; bestgain = 0
        cands = set().union(*sets) - lifted if sets else set()
        for k in cands:
            gain = sum(1 for s in sets if s <= lifted | {k} and not s <= lifted)
            if gain > bestgain: best, bestgain = k, gain
        if not best: break
        lifted.add(best); cur += bestgain
        out.append(f"  + {best:22s} +{bestgain:5d}  -> {cur}/{len(rows)} ({100*cur/len(rows):.1f}%)")
    return "\n".join(out)

for label, rows in projects:
    print(table(label, rows)); print()
allrows = [r for _, rows in projects for r in rows]
print(table("COMBINED", allrows, 30, 40)); print()
print(greedy(allrows, 15)); print()
# explicit any/unknown keyword vs any-typed values
print("functions with any-type but no explicit any/unknown keyword:", sum(1 for r in allrows if 'any-type' in r['rules'] and 'no-any' not in r['rules']))

# external API families (package, or host object) by functions using them
fam = collections.Counter()
def family(x):
    x = x.replace('new ', '')
    if ':' in x and not x.startswith('<'):
        pkg, rest = x.split(':', 1)
        return pkg
    return x.split('.')[0]
for r in allrows:
    for f in {family(x) for x in r['externals']}: fam[f] += 1
print("external API families (functions):", ", ".join(f"{k} {n}" for k, n in fam.most_common(25)))
print("distinct external callees:", len({x for r in allrows for x in r['externals']}))

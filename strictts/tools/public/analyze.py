"""Coverage tables (Markdown) from the reports of tools/public/coverage.sh.

usage: python3 -I tools/public/analyze.py OUTDIR NAME[:AREA_DEPTH] ...
  reads OUTDIR/NAME.MODE.json for the modes strict, dyn and (if present) dynany; AREA_DEPTH > 0
  also prints a table by source directory (the first AREA_DEPTH path components)
"""
import collections
import json
import os
import sys


def stats(rows):
    tot = len(rows)
    cov = sum(r['status'] == 'covered' for r in rows)
    loc = sum(r['loc'] for r in rows)
    cloc = sum(r['loc'] for r in rows if r['status'] == 'covered')
    tse = sum(r['status'] == 'ts-error' for r in rows)
    return tot, cov, loc, cloc, tse


def pct(a, b):
    return f'{100 * a / b:.1f}%' if b else '-'


def blockers(rows, n=10):
    fns, only = collections.Counter(), collections.Counter()
    for r in rows:
        if r['status'] != 'blocked':
            continue
        ks = list(r['rules'])
        for k in ks:
            fns[k] += 1
        if len(ks) == 1:
            only[ks[0]] += 1
    return [(k, c, only[k]) for k, c in fns.most_common(n)]


def main():
    outdir = sys.argv[1]
    for spec in sys.argv[2:]:
        name, _, depth = spec.partition(':')
        depth = int(depth or 0)
        modes = [m for m in ('strict', 'dyn', 'dynany') if os.path.exists(os.path.join(outdir, f'{name}.{m}.json'))]
        rep = {m: json.load(open(os.path.join(outdir, f'{name}.{m}.json'))) for m in modes}
        print(f'### {name}\n')
        print('| mode | functions covered | LOC covered | TS errors |')
        print('|---|---|---|---|')
        for m in modes:
            tot, cov, loc, cloc, tse = stats(rep[m]['rows'])
            print(f'| {m} | {cov}/{tot} ({pct(cov, tot)}) | {cloc}/{loc} ({pct(cloc, loc)}) | {tse} |')
        print()
        if depth:
            areas = collections.OrderedDict()
            for m in modes:
                for r in rep[m]['rows']:
                    a = '/'.join(r['file'].split('/')[:depth])
                    areas.setdefault(a, {k: [] for k in modes})[m].append(r)
            print('| directory | functions | ' + ' | '.join(f'{m}: functions | {m}: LOC' for m in modes) + ' |')
            print('|---|---|' + '---|---|' * len(modes))
            for a in sorted(areas, key=lambda a: -len(areas[a]['dyn'])):
                cells = []
                for m in modes:
                    tot, cov, loc, cloc, _ = stats(areas[a][m])
                    cells += [f'{cov} ({pct(cov, tot)})', f'{cloc}/{loc} ({pct(cloc, loc)})']
                print(f'| `{a}` | {len(areas[a]["dyn"])} | ' + ' | '.join(cells) + ' |')
            print()
        for m in modes:
            bl = blockers(rep[m]['rows'])
            print(f'Top blockers, {m} (rule: functions blocked / functions it alone blocks): ' +
                  ', '.join(f'`{k}` {c}/{o}' for k, c, o in bl) + '\n')


if __name__ == '__main__':
    main()

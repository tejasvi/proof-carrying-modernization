"""Proof-attempt tables (Markdown) from the verdicts written by tools/public/results.py.

usage: python3 -I tools/public/proof_tables.py AUTODIR LABEL=MODULE ...
"""
import collections
import json
import os
import sys


def main():
    autodir = sys.argv[1]
    allres = collections.OrderedDict()
    for spec in sys.argv[2:]:
        label, _, mod = spec.partition('=')
        allres[label] = json.load(open(os.path.join(autodir, f'{mod}_results.json')))
    false_ = ('A:', 'B:', 'N:', 'M:')
    pct = lambda a, b: f'{100 * a / b:.0f}%' if b else '-'
    print('| functions | attempts | PROVED | statement false for some input (A, B, N, M) | statement may be true | PROVED / may be true | strict: may be true | strict: PROVED |')
    print('|---|---|---|---|---|---|---|---|')
    for label, res in allres.items():
        p = sum(r['verdict'] == 'PROVED' for r in res)
        f = sum(r['category'].startswith(false_) for r in res)
        mt = [r for r in res if not r['category'].startswith(false_)]
        st = [r for r in mt if not r.get('uses_dyn')]
        ps = sum(r['verdict'] == 'PROVED' for r in st)
        print(f'| {label} | {len(res)} | {p} | {f} | {len(mt)} | {p}/{len(mt)} ({pct(p, len(mt))}) | {len(st)} | {ps} |')
    print()
    cats = collections.OrderedDict()
    for label, res in allres.items():
        for r in res:
            cats.setdefault(r['category'], collections.OrderedDict()).setdefault(label, []).append(r['fn'])
    labels = list(allres)
    print('| verdict / failure class | ' + ' | '.join(labels) + ' | examples |')
    print('|---|' + '---|' * len(labels) + '---|')
    for c in sorted(cats, key=lambda c: (not c.startswith('proved'), c)):
        ex = [f for lab in labels for f in cats[c].get(lab, [])][:4]
        print(f'| {c} | ' + ' | '.join(str(len(cats[c].get(lab, []))) for lab in labels) + ' | ' + ', '.join(f'`{f}`' for f in ex) + ' |')


if __name__ == '__main__':
    main()

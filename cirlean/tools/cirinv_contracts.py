#!/usr/bin/env python3
"""Turn cirinv batch results into a contracts report: for every function, the
inferred precondition written in C++ (checked in Lean: the function has no
undefined behaviour under it), and the concrete input with UB outside it.

Usage: cirinv_contracts.py BATCH_DIR [--out CONTRACTS.md]
BATCH_DIR holds results_*.jsonl and scan/*.json (cirinv_batch_v2.py).
"""
import argparse
import collections
import glob
import json
import os
import re


def cxx(fact, params):
    """A precondition fact (Lean) in C++ syntax."""
    s = fact
    # loop-renamed parameters (`n0`) are the parameters' initial values
    for p in params:
        s = re.sub(r'(?<![\w.])' + re.escape(p) + r'0(?![\w])', p, s)
    s = s.replace('«', '').replace('»', '')
    m = re.fullmatch(r'∀ e ∈ (\w+), (.*)', s)
    if m:
        return f'all_of({m.group(1)}, [](auto e) {{ return {cxx(m.group(2), [])}; }})'
    s = re.sub(r'\((\w+)\.length : Int\)', r'\1.size()', s)
    s = re.sub(r'\b(\w+)\.length\b', r'\1.size()', s)
    s = s.replace('≤', '<=').replace('≠', '!=').replace('∧', '&&')
    return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('batch')
    ap.add_argument('--out')
    a = ap.parse_args()
    rs = []
    for f in sorted(glob.glob(os.path.join(a.batch, 'results_*.jsonl'))):
        with open(f) as fh:
            rs += [json.loads(l) for l in fh if l.strip()]
    scans = {}
    for f in glob.glob(os.path.join(a.batch, 'scan', '*.json')):
        with open(f) as fh:
            for l in fh:
                if l.strip():
                    j = json.loads(l)
                    scans[j['sym']] = j
    counts = collections.Counter(r['status'] for r in rs)
    out = ['# Inferred contracts', '',
           f'{len(rs)} functions: ' + ', '.join(f'{k} {v}' for k, v in counts.most_common()) + '.', '',
           '`proved`: no undefined behaviour for any argument values of the parameter types. '
           '`proved_under`: no undefined behaviour when the precondition holds (Lean proof), and the '
           'witness input, outside it, has undefined behaviour. `ub_witness`: an input with undefined '
           'behaviour and no proof under any inferred precondition. Arrays behind `int*` parameters '
           'are assumed non-empty; `p.size()` is then the number of elements reachable from `p`.', '']
    order = {'proved': 0, 'proved_under': 1, 'ub_witness': 2}
    for r in sorted(rs, key=lambda r: (order.get(r['status'], 3), r.get('file', ''), r.get('name', ''))):
        if r['status'] not in order:
            continue
        params = [p['name'] for p in scans.get(r['sym'], {}).get('params', []) if p.get('name')]
        out.append(f'### `{r.get("name", r["sym"])}`')
        out.append(f'{r["status"]} ({r.get("file", "")})')
        pre = r.get('precondition')
        if pre:
            out.append('```cpp')
            out.append('// requires: ' + ' && '.join(cxx(f, params) for f in pre))
            out.append('```')
        if r.get('ub_inputs'):
            u = r['ub_inputs'][0]
            what = 'outside the precondition' if pre else 'witness'
            out.append(f'- {what}: `({", ".join(u["input"])})` gives {u["result"]}')
        if r['status'] == 'ub_witness' and r.get('precondition_tried'):
            out.append('- tried: `' + ' && '.join(cxx(f, params) for f in r['precondition_tried']) + '`')
        if r.get('proof'):
            out.append(f'- proof: `{r["proof"]}`')
        out.append('')
    text = '\n'.join(out) + '\n'
    if a.out:
        with open(a.out, 'w') as fh:
            fh.write(text)
    else:
        print(text)


if __name__ == '__main__':
    main()

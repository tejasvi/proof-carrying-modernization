#!/usr/bin/env python3
"""Run cirinv on every in-scope user function of a corpus (see cirscan) whose
parameters the no-UB stub supports, and collect the reports.

Usage: cirinv_batch.py --cov COVERAGE_OUT --work DIR [--loops 1] [--limit N]
COVERAGE_OUT is the directory written by coverage_v1.sh (cir/, lean/).
Results are appended to DIR/results.jsonl (one report per function); a
function already in it is skipped, so the batch can be resumed.
"""
import argparse
import json
import os
import re
import subprocess
import sys

CIRLEAN = '/home/user/cirlean'
RUN = ['nice', '-n', '10', 'taskset', '-c', os.environ.get('CIRINV_CORE', '29')]
SUPPORTED = re.compile(r'^(\(\.int (true|false) \d+\)|\.bool|\(\.ptr \(\.int (true|false) \d+\)\)|'
                       r'\(\.ptr \(\.record "std::__1::vector<(int|unsigned int|long|unsigned long|'
                       r'long long|unsigned long long|short|unsigned short|char|unsigned char),.*"\)\)|'
                       r'\(\.record "std::__1::vector<(int|unsigned int|long|unsigned long|long long|'
                       r'unsigned long long|short|unsigned short|char|unsigned char),.*"\))$')


def is_test(name):
    return re.match(r'^(main|test|_GLOBAL)', name) or re.search(r'(^|::)test[0-9_A-Za-z]*\(', name)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--cov', required=True)
    ap.add_argument('--work', required=True)
    ap.add_argument('--loops', default='1', help='comma-separated loop counts to include')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--timeout', type=int, default=900)
    ap.add_argument('--shard', default='0/1', help='i/n: this worker takes every n-th function')
    ap.add_argument('--tool', default='cirinv_v2.py')
    a = ap.parse_args()
    shard_i, shard_n = map(int, a.shard.split('/'))
    loops_ok = {int(x) for x in a.loops.split(',')}
    os.makedirs(os.path.join(a.work, 'scan'), exist_ok=True)
    res_path = os.path.join(a.work, f'results_{a.shard.replace("/", "of")}.jsonl')
    done = set()
    if os.path.exists(res_path):
        with open(res_path) as fh:
            for line in fh:
                try:
                    done.add(json.loads(line)['sym'])
                except (ValueError, KeyError):
                    pass
    cirs = sorted(f for f in os.listdir(os.path.join(a.cov, 'cir')) if f.endswith('.cir'))
    n = 0
    for fi, f in enumerate(cirs):
        # shard by file: each module is compiled by one worker only
        if fi % shard_n != shard_i:
            continue
        b = f[:-4]
        lean = os.path.join(a.cov, 'lean', b + '.lean')
        if not os.path.exists(lean):
            continue
        cir = os.path.join(a.cov, 'cir', f)
        scan = os.path.join(a.work, 'scan', b + '.json')
        if not os.path.exists(scan):
            with open(scan, 'w') as fh:
                subprocess.run(RUN + [f'{CIRLEAN}/.lake/build/bin/cirscan', '--json', cir],
                               stdout=fh, stderr=subprocess.DEVNULL, timeout=600)
        with open(scan) as fh:
            funcs = [json.loads(l) for l in fh if l.strip()]
        for fn in funcs:
            if fn['status'] != 'in_scope' or is_test(fn['name']) or fn['loops'] not in loops_ok:
                continue
            if not all(SUPPORTED.match(p['ty']) for p in fn['params']):
                continue
            if fn['sym'] in done:
                continue
            if a.limit and n >= a.limit:
                return
            n += 1
            cmd = ['python3', '-I', f'{CIRLEAN}/tools/{a.tool}', '--out', a.work, '--gen-lean', lean,
                   '--module', f'Gen.{b}', '--cir', cir, '--scan', scan, '--sym', fn['sym']]
            try:
                r = subprocess.run(cmd, capture_output=True, text=True, timeout=a.timeout)
                lines = [l for l in r.stdout.splitlines() if l.startswith('{')]
                rep = json.loads(lines[-1]) if lines else {'sym': fn['sym'], 'status': 'crash',
                                                           'reason': r.stderr[-300:]}
            except subprocess.TimeoutExpired:
                rep = {'sym': fn['sym'], 'status': 'timeout'}
            rep['file'] = b
            rep['name'] = fn['name']
            with open(res_path, 'a') as fh:
                fh.write(json.dumps(rep) + '\n')
            print(f"{rep['status']:16} {b} :: {fn['name'][:90]}", flush=True)


if __name__ == '__main__':
    main()

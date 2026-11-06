"""Counterexample search files for the uniform NoPanic attempts that are not proved.

For each such attempt, one Lean file that runs the function through the compiled interpreter on
random and edge-value inputs (tools/public/lean/PanicSearch.lean) and appends the first panicking
input to a text file next to it; run each with tools/public/prove.sh (a diverging input ends the run at
its timeout without losing what was found before).

usage: python3 -I tools/public/np_search.py NPDIR SEARCHDIR [--runs N] [--keys FILE --tag T [--small] [--seed S]] > FILES.txt
  --keys: only these attempts (module/function, one per line), files named <module>_<T>_<k>;
  --small: small numbers only (no infinities), for functions whose runs a large argument makes too long
  --proved: the proved attempts instead (a cross-check: the search must find no panic there)
"""
import json
import os
import sys


def main():
    argv = sys.argv[1:]
    runs, keys, tag, small, seed = 300, None, 'ps', False, 7
    if '--runs' in argv:
        i = argv.index('--runs'); runs = int(argv[i + 1]); del argv[i:i + 2]
    if '--keys' in argv:
        i = argv.index('--keys'); keys = set(open(argv[i + 1]).read().split()); del argv[i:i + 2]
    if '--tag' in argv:
        i = argv.index('--tag'); tag = argv[i + 1]; del argv[i:i + 2]
    if '--seed' in argv:
        i = argv.index('--seed'); seed = int(argv[i + 1]); del argv[i:i + 2]
    if '--small' in argv:
        argv.remove('--small'); small = True
    proved = '--proved' in argv
    if proved:
        argv.remove('--proved')
    npdir, sdir = argv
    sdir = os.path.abspath(sdir)
    os.makedirs(sdir, exist_ok=True)
    verdicts = json.load(open(os.path.join(npdir, 'verdicts.json')))
    k = 0
    for key, v in sorted(verdicts.items()):
        if v['verdict'] != ('PROVED' if proved else 'NOT PROVED'):
            continue  # (by default) proved, or a strict attempt whose verdict is the dyn one
        if keys is not None and key not in keys:
            continue
        mod, fn = key.split('/', 1)
        meta = json.load(open(os.path.join(npdir, f'{mod}_np.json')))
        ns = meta['namespace']
        name = f'{mod}_{tag}_{k}'
        k += 1
        txt = os.path.join(sdir, name + '.txt')
        lines = [f'import {mod}', 'import PanicSearch', 'open StrictTS StrictTS.Frontend',
                 f'#eval StrictTS.PanicSearch.search Impl.host {ns}.program {ns}.«{fn}Ref» "{key}" "{txt}" {runs} {seed} 1 {"true" if small else "false"}']
        open(os.path.join(sdir, name + '.lean'), 'w').write('\n'.join(lines) + '\n')
        print(os.path.join(sdir, name + '.lean'))


if __name__ == '__main__':
    main()

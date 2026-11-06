"""Which uniform NoPanic attempt files to run (tools/public/nopanic.py wrote them).

Every dyn attempt runs; a strict attempt runs only when no dyn attempt has the same function
(source name, signature) and the same closure digest (the code it reaches, the classes it
mentions, the module body when it reads module variables): equal digests mean the same theorem
about the same code, so the strict verdict is the dyn one.

usage: python3 -I tools/public/np_plan.py NPDIR > FILES.txt
  also writes NPDIR/strict_same_as_dyn.json: {strict module/function: dyn module/function}
"""
import glob
import json
import os
import sys


def main():
    npdir = sys.argv[1]
    dyn, strict = {}, []
    for f in sorted(glob.glob(os.path.join(npdir, '*_np.json'))):
        d = json.load(open(f))
        for a in d['attempts']:
            key = (a['source'], tuple(a['args']), a['ret'], a['closure_hash'])
            item = (d['module'], a['fn'], a['file'])
            if d['set'].endswith(' dyn'):
                dyn.setdefault(key, item)
                print(os.path.join(npdir, a['file']))
            else:
                strict.append((key, item))
    same = {}
    for key, (m, fn, file) in strict:
        if key in dyn:
            same[f'{m}/{fn}'] = f'{dyn[key][0]}/{dyn[key][1]}'
        else:
            print(os.path.join(npdir, file))
    json.dump(same, open(os.path.join(npdir, 'strict_same_as_dyn.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()

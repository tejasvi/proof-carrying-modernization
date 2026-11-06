"""Proof verdicts of the uniform NoPanic attempts (tools/public/nopanic.py, run by prove.sh).

usage: python3 -I tools/public/np_verdicts.py NPDIR [--override DIR]
  reads NPDIR/*_np.json and the .out files next to the attempt files (or, for a file that DIR
  holds as well, DIR's run: the attempts that reached a heartbeat limit, run again with
  `set_option maxHeartbeats` before the theorem); writes NPDIR/verdicts.json:
  one entry per attempt (module/function): proved (standard axioms only, no error), the first
  stuck construct that np_stuck reported (the most specific one over the remaining goals), or
  'timeout' when the run ended before the theorem was checked.
"""
import glob
import json
import os
import re
import sys

sys.dont_write_bytecode = True  # (python -I ignores PYTHONDONTWRITEBYTECODE)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from results import messages  # noqa: E402

STD = {'propext', 'Classical.choice', 'Quot.sound'}
# most specific first: an interpreter step beats an undecided test beats a residual condition
RANK = {'residual condition': 9, 'undecided test': 5}


def main():
    argv = sys.argv[1:]
    override = None
    if '--override' in argv:
        i = argv.index('--override'); override = argv[i + 1]; del argv[i:i + 2]
    npdir = argv[0]
    out = {}
    for f in sorted(glob.glob(os.path.join(npdir, '*_np.json'))):
        d = json.load(open(f))
        for a in d['attempts']:
            p = os.path.join(npdir, a['file'].replace('.lean', '.out'))
            shift = 0
            if override and os.path.exists(os.path.join(override, a['file'].replace('.lean', '.out'))):
                p, shift = os.path.join(override, a['file'].replace('.lean', '.out')), 1
            text = open(p).read() if os.path.exists(p) else None
            key = f"{d['module']}/{a['fn']}"
            e = {'set': d['set'], 'module': d['module'], 'fn': a['fn'], 'source': a['source']}
            if text is None:
                out[key] = {**e, 'verdict': 'NOT RUN'}
                continue
            ms = messages(text)
            errs = [m for m in ms if m['kind'] == 'error' and a['from'] + shift <= m['line'] <= a['to'] + shift + 1]
            ax = re.search(r"'[^']*\." + re.escape(a['theorem']) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text)
            axioms = {x.strip() for x in (ax.group(1) or '').split(',')} - {''} if ax and ax.group(1) else set()
            # np_stuck's info messages are printed without a position (one attempt per file)
            stuck = []
            for line in text.splitlines():
                if line.startswith('NPSTUCK '):
                    kind, _, what = line[len('NPSTUCK '):].partition(' :: ')
                    stuck.append((kind.strip(), what.strip()))
            if ax and not errs and axioms <= STD:
                out[key] = {**e, 'verdict': 'PROVED', 'axioms': sorted(axioms)}
            elif not ax:
                hb = any('maximum number of heartbeats' in m['msg'] for m in errs)
                out[key] = {**e, 'verdict': 'NOT PROVED',
                            'stuck': ['heartbeat limit', 'maxHeartbeats reached'] if hb else ['timeout', 'the run ended before the theorem was checked'],
                            'error': (errs[0]['msg'].strip().split('\n')[0] if errs else '')}
            else:
                best = sorted(stuck, key=lambda s: RANK.get(s[0], 0))[0] if stuck else \
                    ['error', errs[0]['msg'].strip().split('\n')[0][:200] if errs else 'non-standard axioms']
                out[key] = {**e, 'verdict': 'NOT PROVED', 'stuck': list(best), 'goals': len(stuck),
                            'axioms': sorted(axioms)}
    json.dump(out, open(os.path.join(npdir, 'verdicts.json'), 'w'), indent=1)
    n = len(out)
    p = sum(v['verdict'] == 'PROVED' for v in out.values())
    print(f'{p}/{n} PROVED, {sum(v["verdict"] == "NOT RUN" for v in out.values())} not run')


if __name__ == '__main__':
    main()

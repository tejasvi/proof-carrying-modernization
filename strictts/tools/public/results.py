"""Verdicts of the proof attempts (tools/public/attempts.py, run by tools/public/prove.sh).

usage: python3 -I tools/public/results.py AUTODIR MODULE [--goals]
  reads AUTODIR/MODULE_auto.json and the .out files; prints one line per attempt
  (PROVED / FAILED, the first line of the first error, the IR features) and a JSON summary to
  AUTODIR/MODULE_results.json. --goals also prints the start of each residual goal.
"""
import json
import os
import re
import sys

MSG = re.compile(r'^(?P<file>[^\n:]+\.lean):(?P<line>\d+):(?P<col>\d+): (?P<kind>error|warning|info): ', re.M)


def messages(text):
    ms = list(MSG.finditer(text))
    out = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        out.append({'line': int(m.group('line')), 'kind': m.group('kind'), 'msg': text[m.end():end]})
    return out


# Statements found false by reading the code (class M): the input, and what happens.
KNOWN_FALSE = {
    'logTwo': 'n = -1: `-1 >> 1 === -1`, the loop never ends',
    'armstrongNumber': 'num = Infinity: `Math.floor(Infinity / 10) === Infinity`, the loop never ends',
    'jugglerSequence': 'n = Infinity: `for (i = 0; i < n; i++)` never ends',
    'pascalsTriangle': 'n = 0: `arr[arr.length - 1]` reads index -1',
    'generateAllCombos': 'n = Infinity: the loop bound `n - k + 2` is infinite',
    'binarySearchIterative': 'start = -1: `array[start]` is out of bounds',
    'interpolationSearch': 'array = []: `array[0]` is read before the loop',
    'fibonacciSearch': 'array = []: `array[offset + 1]` reads index 0',
    'sentinelSearch': 'target = NaN: no element equals it, the scan runs past the end',
    'gnomeSort': 'arr = [NaN, 1]: the two elements are swapped forever',
    'partition': 'left = -5: the pivot index is out of bounds',
    'CountSmallerItems': 'startIndex = -5: `array[-4]` is out of bounds',
    'bogoSort': 'Math.random() always 0.99, arr = [2, 1]: never sorted',
    'shuffleArray': 'Math.random() = 1: index i + 1 is out of bounds',
    'shuffle<number>': 'Math.random() = 1: index i + 1 is out of bounds',
}

# Failure classes, first match wins. A, B, N, M: the statement itself is false for some arguments
# or worlds (an arbitrary callback can throw; an explicit `throw` is reachable; a reference the
# statement leaves without a cell can be read; an input found by reading the code), so these are
# not tactic failures. C-J: IR features that ts_auto does not handle; E: a `for … of` over a
# Map/Set with none of the other features; K: none of these.
def category(r):
    if r['verdict'] == 'PROVED':
        return 'proved (returns a function: the loop is not run)' if r['ret'].startswith('(.fn') else 'proved'
    if r.get('callback_param'):
        return 'A: callback parameter (an arbitrary function may throw)'
    if r.get('throws') and r.get('statement', 'Returns') == 'Returns':
        return 'B: explicit throw (argument validation)'
    if r.get('dangling'):
        return 'N: reads a reference the statement leaves without a cell'
    if r['source'] in KNOWN_FALSE:
        return 'M: false for an input found by reading the code'
    if 'while' in r['loops'] or 'doWhile' in r['loops']:
        return 'C: while loop (no automatic termination argument)'
    if any(b not in ('array length', 'constant') for b in r.get('for_bounds', [])):
        return 'D: counted loop bound not `i < xs.length` or `i < constant`'
    if r.get('nested_loop') or r.get('loops_count', 0) >= 2:
        return 'F: nested or several loops'
    if r.get('loop_exit'):
        return 'G: return/break inside the loop'
    if r.get('loop_alloc'):
        return 'H: loop body allocates'
    if r.get('loop_writes', 0) >= 2:
        return 'I: loop body writes twice'
    if r.get('loop_call'):
        return 'J: loop body calls a project function'
    if 'forOfMap' in r['loops'] or 'forOfSet' in r['loops']:
        return 'E: for...of over a Map/Set'
    return 'K: other'


STATEMENT_FALSE = ('A:', 'B:', 'N:', 'M:')


def main():
    autodir, mod = sys.argv[1], sys.argv[2]
    show = '--goals' in sys.argv
    meta = json.load(open(os.path.join(autodir, f'{mod}_auto.json')))
    outs = {}
    res = []
    for a in meta['attempts']:
        f = a['file']
        if f not in outs:
            p = os.path.join(autodir, f.replace('.lean', '.out'))
            outs[f] = open(p).read() if os.path.exists(p) else None
        text = outs[f]
        if text is None:
            res.append({**a, 'verdict': 'NOT RUN', 'error': ''})
            continue
        ms = [m for m in messages(text) if a['from'] <= m['line'] <= a['to'] and m['kind'] == 'error']
        ax = re.search(r"'[^']*\." + re.escape(a['theorem']) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text)
        axioms = [x.strip() for x in (ax.group(1) or '').split(',')] if ax and ax.group(1) else []
        ok = ax is not None and not ms and 'sorryAx' not in axioms
        err = ms[0]['msg'] if ms else ('' if ax else 'theorem not checked (run killed?)')
        res.append({**a, 'verdict': 'PROVED' if ok else 'FAILED', 'axioms': axioms, 'error': err})
        res[-1]['category'] = category(res[-1])
        res[-1]['counterexample'] = KNOWN_FALSE.get(a['source'], '') if res[-1]['category'].startswith('M:') else ''
    for r in res:
        first = r['error'].strip().split('\n')[0][:120]
        print(f"{r['verdict']:7s} {r['fn']:32s} loops={','.join(r['loops']) or '-'} cbs={','.join(r['callbacks']) or '-'} [{r.get('category', '')}] {first}")
        if show and r['verdict'] == 'FAILED':
            print('    ' + '\n    '.join(r['error'].strip().split('\n')[1:30]))
    n = len(res)
    p = sum(r['verdict'] == 'PROVED' for r in res)
    t = sum(not r['category'].startswith(STATEMENT_FALSE) for r in res)
    print(f'{mod}: {p}/{n} PROVED; {p}/{t} of the attempts whose statement may be true')
    json.dump(res, open(os.path.join(autodir, f'{mod}_results.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()

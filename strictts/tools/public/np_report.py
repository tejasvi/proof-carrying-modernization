"""Final verdicts and tables of the uniform NoPanic sweep.

PROVED: `ts_auto` proved `JS.NoPanic` (standard axioms only). COUNTEREXAMPLE: the counterexample
search found an input whose Lean run panics; the Node run of the original function on the same
input (with checks, tools/public/node) classifies it:
  * latent bug: Node reaches a value that the TypeScript types exclude (an out-of-bounds read, a
    missing key, `x!` on undefined), and with the checks off that value escapes: the result is
    outside the declared return type, the run throws, or it does not end;
  * unsound read tolerated: Node reaches such a value but the code copes with it (e.g. it tests a
    dictionary read for truthiness); the result stays within the declared type;
  * model limitation: Node runs the input within the types (the Lean panic is the model's).
Inputs that are a method's object built field by field, and functions the project does not
export, are marked. UNKNOWN: neither; the first stuck construct of the remaining goal is given.

usage: python3 -I tools/public/np_report.py NPDIR SEARCHDIR [--before NPDIR0 LABEL0 LABEL]
           [--compare NPDIR0 SEARCHDIR0 LABEL0 LABEL] [--pending f,g,...]
           [--recheck NPDIR1 SEARCHDIR1 LABEL1 f,g,...] [--compare-recheck NPDIR1 SEARCHDIR1 LABEL1 f,g,...]
  writes NPDIR/final.json (one entry per attempt and mode) and prints the Markdown tables;
  --before: also the PROVED counts of the same attempts run with another tree (NPDIR0), the
  functions proved in one run only, and any function proved that has a counterexample (which
  would be a soundness alarm);
  --compare: the same against a run with another translator (its own modules, attempts and
  counterexample search), attempts matched by set, source name and signature; the changed
  verdicts are listed with the first stuck construct of the UNKNOWN side;
  --pending: these functions (source names) count as PENDING whatever their verdict (translated
  with a known translator bug; the verdict waits for the fix);
  --recheck: these functions (source names) take their verdicts from a run on a later commit
  LABEL1 (NPDIR1, SEARCHDIR1; e.g. the fix of such a bug), attempts matched by module and function;
  --compare-recheck: the same for the run of --compare
"""
import collections
import json
import os
import re
import sys


def blocker(stuck, fn):
    """A blocker class for the first stuck construct (kind, pretty-printed construct)."""
    kind, what = stuck[0], stuck[1]
    if kind == 'call':
        m = re.search(r'callFun I program (\S+)Ref', what)
        callee = m.group(1) if m else '?'
        return 'recursive call' if callee == fn else 'call not unfolded (second call, or after the unfolding phase)'
    if kind == 'builtin':
        m = re.search(r'Builtin\.(\w+)', what)
        b = m.group(1) if m else '?'
        if b == 'arrReduce1':
            return 'builtin: reduce without an initial value'
        if 'Val.clo [{' in what:
            return f'builtin: {b} with a callback that captures variables'
        return f'builtin: {b}'
    if kind == 'external call answer':
        m = re.search(r'w\.ext "([^"]+)"', what)
        return f'external call answer ({m.group(1)})' if m else 'external call answer'
    if kind == 'undecided test':
        if re.fullmatch(r'\(?!?val✝( == JSStr[^)]*)?\)? = true|val✝ = true', what):
            return 'undecided test on a value read at run time (dyn operation, string comparison)'
        if re.search(r'val✝ < \w+\.size', what):
            return 'undecided test: index from an argument within bounds'
        if '.includes' in what or '.replaceAll' in what:
            return 'undecided test on string operations'
        return 'undecided test on numbers'
    if kind == 'residual condition':
        last = what.split('| last hypothesis:')[-1] if '| last hypothesis:' in what else ''
        if 'Dyn.' in last:
            return 'dyn operation result (Dyn.typeof, Dyn.eq, Dyn.isArrayTy, Dyn.truthy) not decided'
        if 'HKind.box' in last:
            return 'module variable cell (ModuleInit facts not derived)'
        if 'HKind.obj' in last or 'Val.Live' in last or 'w.Closed' in last:
            return 'cell of a reference below the first level (World.Closed / Val.Live not used)'
        return 'other side condition'
    return kind


def assemble(npdir, sdir, pending=frozenset()):
    """The final verdict of every attempt (and the sets with their not-attempted counts)."""
    verdicts = json.load(open(os.path.join(npdir, 'verdicts.json')))
    same = json.load(open(os.path.join(npdir, 'strict_same_as_dyn.json')))
    node = {}
    p = os.path.join(sdir, 'node.jsonl')
    if os.path.exists(p):
        for line in open(p):
            r = json.loads(line)
            node.setdefault(r['key'], []).append(r)
    done = set()
    for f in os.listdir(sdir):
        if f.endswith('.txt'):
            for line in open(os.path.join(sdir, f)):
                if line.startswith('NPDONE ') or line.startswith('NPUNSUPPORTED '):
                    done.add(line.split()[1])
    final = []
    sets = collections.OrderedDict()
    for f in sorted(os.listdir(npdir)):
        if not f.endswith('_np.json'):
            continue
        meta = json.load(open(os.path.join(npdir, f)))
        label, mod = meta['set'], meta['module']
        sets.setdefault(label, {'skipped': len(meta['skipped'])})
        for a in meta['attempts']:
            key = f'{mod}/{a["fn"]}'
            src_key = same.get(key, key)
            v = verdicts.get(src_key, {'verdict': 'NOT RUN'})
            e = {'set': label, 'key': key, 'verdict_of': src_key, 'fn': a['fn'], 'source': a['source'],
                 'args': a['args'], 'ret': a['ret'], 'uses_dyn': a['uses_dyn'], 'dangling': a['dangling'],
                 'module_init': a['module_init'], 'loops': a['loops'], 'callbacks': a['callbacks']}
            if v['verdict'] == 'PROVED':
                e['verdict'] = 'PROVED'
            else:
                ces = node.get(src_key, [])
                kinds = []
                for c in ces:
                    o = c['node']['outcome']
                    if o == 'violation':
                        pl = c.get('plain', {})
                        escapes = pl.get('outcome') in ('timeout', 'threw', 'no output') or \
                            (pl.get('outcome') == 'returned' and pl.get('conforms') is False)
                        kinds.append('latent bug' if escapes else 'unsound read tolerated')
                    elif o in ('returned', 'threw'):
                        kinds.append('model limitation')
                    else:
                        kinds.append('inconclusive')
                if ces:
                    order = ['latent bug', 'unsound read tolerated', 'model limitation', 'inconclusive']
                    best = min(range(len(ces)), key=lambda i: order.index(kinds[i]))
                    e['verdict'] = 'COUNTEREXAMPLE'
                    e['class'] = kinds[best]
                    e['panic'] = ces[best]['panic']
                    e['input'] = ces[best]['args']
                    e['node'] = ces[best]['node']
                    e['exported'] = ces[best].get('exported')
                    e['plain'] = ces[best].get('plain')
                    e['object_input'] = '__mk(' in ces[best]['args']
                    e['ts'] = f"{ces[best].get('file', '')}:{ces[best].get('item', '')}"
                else:
                    e['verdict'] = 'UNKNOWN'
                    e['stuck'] = v.get('stuck', ['not run', ''])
                    e['blocker'] = blocker(e['stuck'], v.get('fn', a['fn']))
                    e['searched'] = src_key in done
            e['has_counterexample'] = bool(node.get(src_key))
            if a['source'] in pending:
                e['raw_verdict'], e['verdict'] = e['verdict'], 'PENDING'
            final.append(e)
    return final, sets


def recheck(final, npdir1, sdir1, label, names):
    """The attempts of the functions NAMES with their entries from the run in NPDIR1/SEARCHDIR1."""
    later = {e['key']: e for e in assemble(npdir1, sdir1)[0]}
    out = []
    for e in final:
        if e['source'] in names:
            e1 = later[e['key']]
            assert (e1['source'], e1['args'], e1['ret']) == (e['source'], e['args'], e['ret']), e['key']
            assert e1.get('stuck', [''])[0] != 'not run', e['key']
            e = dict(e1, set=e['set'], recheck=label)
        out.append(e)
    return out


def verdict_class(e):
    return e['verdict'] if e['verdict'] != 'COUNTEREXAMPLE' else 'COUNTEREXAMPLE: ' + e['class']


def compare(final, final0, l0, l1):
    """Before/after across translators: attempts matched by set, source name and signature (the
    k-th of equal keys with the k-th)."""
    def keyed(fs):
        out, seen = {}, collections.Counter()
        for e in fs:
            k = (e['set'], e['source'], tuple(e['args']), e['ret'])
            out[k + (seen[k],)] = e
            seen[k] += 1
        return out
    a, b = keyed(final0), keyed(final)
    pend = any(e['verdict'] == 'PENDING' for e in final + final0)
    print(f'| project | mode | attempts, {l0} | attempts, {l1} | PROVED, {l0} | PROVED, {l1} | COUNTEREXAMPLE, {l0} | COUNTEREXAMPLE, {l1} '
          f'(latent bug / tolerated / limitation) | UNKNOWN, {l0} | UNKNOWN, {l1} |' + (' pending (translator bug) |' if pend else ''))
    print('|---|---|---|---|---|---|---|---|---|---|' + ('---|' if pend else ''))
    for proj in ('es-toolkit', 'TheAlgorithms'):
        for mode in ('strict', 'dyn'):
            r0 = [e for e in final0 if e['set'].startswith(proj) and e['set'].endswith(' ' + mode)]
            r1 = [e for e in final if e['set'].startswith(proj) and e['set'].endswith(' ' + mode)]
            c0, c1 = collections.Counter(e['verdict'] for e in r0), collections.Counter(e['verdict'] for e in r1)
            k1 = collections.Counter(e.get('class') for e in r1 if e['verdict'] == 'COUNTEREXAMPLE')
            k0 = collections.Counter(e.get('class') for e in r0 if e['verdict'] == 'COUNTEREXAMPLE')
            pct = lambda x, n: f'{100 * x / n:.0f}%' if n else '-'
            print(f"| {proj} | {mode} | {len(r0)} | {len(r1)} | {c0['PROVED']} ({pct(c0['PROVED'], len(r0))}) | "
                  f"{c1['PROVED']} ({pct(c1['PROVED'], len(r1))}) | {c0['COUNTEREXAMPLE']} ({k0['latent bug']}/{k0['unsound read tolerated']}/{k0['model limitation']}) | "
                  f"{c1['COUNTEREXAMPLE']} ({k1['latent bug']}/{k1['unsound read tolerated']}/{k1['model limitation']}) | {c0['UNKNOWN']} | {c1['UNKNOWN']} |"
                  + (f" {c1['PENDING']} |" if pend else ''))
    print()
    changes = collections.defaultdict(list)
    for k in sorted(set(a) | set(b), key=str):
        e0, e1 = a.get(k), b.get(k)
        name = k[1] + (' (strict)' if k[0].endswith(' strict') else '')
        if e0 is None:
            changes['new attempt'].append(f'{name}: {verdict_class(e1)}' + (f" ({e1['blocker']})" if e1['verdict'] == 'UNKNOWN' else ''))
        elif e1 is None:
            changes['attempt gone'].append(f'{name}: was {verdict_class(e0)}')
        elif verdict_class(e0) != verdict_class(e1):
            changes[f'{verdict_class(e0)} -> {verdict_class(e1)}'].append(
                name + (f" ({e1['blocker']})" if e1['verdict'] == 'UNKNOWN' else
                        f" (was: {e0['blocker']})" if e0['verdict'] == 'UNKNOWN' else ''))
    for kind, names in sorted(changes.items()):
        print(f"* {kind} ({len(names)}): {', '.join('`' + n + '`' for n in names)}")
    print()


def main():
    argv = sys.argv[1:]
    before = cmp = None
    if '--before' in argv:
        i = argv.index('--before'); before = argv[i + 1:i + 4]; del argv[i:i + 4]
    if '--compare' in argv:
        i = argv.index('--compare'); cmp = argv[i + 1:i + 5]; del argv[i:i + 5]
    pending = frozenset()
    if '--pending' in argv:
        i = argv.index('--pending'); pending = frozenset(argv[i + 1].split(',')); del argv[i:i + 2]
    later = clater = None
    if '--compare-recheck' in argv:
        i = argv.index('--compare-recheck'); clater = argv[i + 1:i + 5]; del argv[i:i + 5]
    if '--recheck' in argv:
        i = argv.index('--recheck'); later = argv[i + 1:i + 5]; del argv[i:i + 5]
    npdir, sdir = argv[:2]
    final, sets = assemble(npdir, sdir, pending)
    if later:
        final = recheck(final, *later[:3], frozenset(later[3].split(',')))
    if cmp:
        final0, _ = assemble(cmp[0], cmp[1], pending)
        if clater:
            final0 = recheck(final0, *clater[:3], frozenset(clater[3].split(',')))
        compare(final, final0, cmp[2], cmp[3])
    json.dump(final, open(os.path.join(npdir, 'final.json'), 'w'), indent=1)
    if before:
        final0, _ = assemble(before[0], sdir, pending)
        v0 = {e['key']: e['verdict'] for e in final0}
        print(f'| project | mode | attempts | PROVED, {before[1]} | PROVED, {before[2]} | COUNTEREXAMPLE | UNKNOWN, {before[1]} | UNKNOWN, {before[2]} |')
        print('|---|---|---|---|---|---|---|---|')
        for proj in ('es-toolkit', 'TheAlgorithms'):
            for mode in ('strict', 'dyn'):
                rows = [e for e in final if e['set'].startswith(proj) and e['set'].endswith(' ' + mode)]
                rows0 = [e for e in final0 if e['set'].startswith(proj) and e['set'].endswith(' ' + mode)]
                c, c0 = collections.Counter(e['verdict'] for e in rows), collections.Counter(e['verdict'] for e in rows0)
                n = len(rows)
                print(f"| {proj} | {mode} | {n} | {c0['PROVED']} ({100 * c0['PROVED'] / n:.0f}%) | {c['PROVED']} ({100 * c['PROVED'] / n:.0f}%) | "
                      f"{c['COUNTEREXAMPLE']} | {c0['UNKNOWN']} | {c['UNKNOWN']} |")
        print()
        gained = sorted({e['source'] for e in final if e['set'].endswith(' dyn') and e['verdict'] == 'PROVED' and v0.get(e['key']) != 'PROVED'})
        lost = sorted({e['source'] for e in final if e['set'].endswith(' dyn') and e['verdict'] != 'PROVED' and v0.get(e['key']) == 'PROVED'})
        alarm = sorted({e['source'] for e in final + final0 if e['verdict'] == 'PROVED' and e['has_counterexample']})
        print(f"Proved with {before[2]} only (dyn): {', '.join('`' + x + '`' for x in gained) or 'none'}. "
              f"Proved with {before[1]} only: {', '.join('`' + x + '`' for x in lost) or 'none'}. "
              f"Proved functions with a counterexample: {', '.join(alarm) or 'none'}.\n")

    pend = any(e['verdict'] == 'PENDING' for e in final)
    print('| project | mode | attempts | PROVED | COUNTEREXAMPLE | UNKNOWN | PROVED or COUNTEREXAMPLE |' + (' pending (translator bug) |' if pend else ''))
    print('|---|---|---|---|---|---|---|' + ('---|' if pend else ''))
    for proj in ('es-toolkit', 'TheAlgorithms'):
        for mode in ('strict', 'dyn'):
            rows = [e for e in final if e['set'].startswith(proj) and e['set'].endswith(' ' + mode)]
            c = collections.Counter(e['verdict'] for e in rows)
            n = len(rows)
            dec = c['PROVED'] + c['COUNTEREXAMPLE']
            print(f"| {proj} | {mode} | {n} | {c['PROVED']} ({100 * c['PROVED'] / n:.0f}%) | {c['COUNTEREXAMPLE']} | {c['UNKNOWN']} | {dec} ({100 * dec / n:.0f}%) |"
                  + (f" {c['PENDING']} |" if pend else ''))
    print()
    print('| functions | mode | attempts | PROVED | COUNTEREXAMPLE: latent bug | unsound read tolerated | model limitation | Node inconclusive | UNKNOWN | not attempted (callback parameter) |'
          + (' pending (translator bug) |' if pend else ''))
    print('|---|---|---|---|---|---|---|---|---|---|' + ('---|' if pend else ''))
    for label, info in sets.items():
        rows = [e for e in final if e['set'] == label]
        c = collections.Counter(e['verdict'] if e['verdict'] != 'COUNTEREXAMPLE' else e['class'] for e in rows)
        name, mode = label.rsplit(' ', 1)
        print(f"| {name} | {mode} | {len(rows)} | {c['PROVED']} | {c['latent bug']} | {c['unsound read tolerated']} | "
              f"{c['model limitation']} | {c['inconclusive']} | {c['UNKNOWN']} | {info['skipped']} |" + (f" {c['PENDING']} |" if pend else ''))
    print()
    for mode in ('strict', 'dyn'):
        rows = [e for e in final if e['set'].endswith(' ' + mode) and e['verdict'] == 'UNKNOWN']
        c = collections.Counter(e['blocker'] for e in rows)
        ex = collections.defaultdict(list)
        for e in rows:
            ex[e['blocker']].append(e['source'])
        print(f'| UNKNOWN, {mode}: first stuck construct | functions | examples |')
        print('|---|---|---|')
        for k, n in c.most_common():
            print(f"| {k} | {n} | {', '.join('`' + x + '`' for x in ex[k][:4])} |")
        print()
    for cls in ('latent bug', 'unsound read tolerated', 'model limitation', 'inconclusive'):
        rows = [e for e in final if e['set'].endswith(' dyn') and e['verdict'] == 'COUNTEREXAMPLE' and e['class'] == cls]
        if not rows:
            continue
        print(f'| {cls} (dyn) | API | input | Lean panic | Node, with checks | Node, checks off |')
        print('|---|---|---|---|---|---|')
        dup = collections.Counter(e['source'] for e in rows)
        for e in sorted(rows, key=lambda e: (not e.get('exported'), e['source'])):
            node = e['node'].get('where') or e['node'].get('value') or e['node'].get('message') or e['node'].get('outcome')
            pl = e.get('plain') or {}
            # with the checks off the read is still a call of the pass-through check: name the value
            msg = str(pl.get('message', pl.get('note', ''))).replace('__strictts_ix is not a function or its return value', 'the value read')
            plain = (f"{pl.get('outcome')}" + (f" `{pl.get('value')}` (declared `{pl.get('ret')}`)" if pl.get('outcome') == 'returned' else
                     (f" ({pl.get('name')}: {msg[:50]})" if pl.get('name') else f" ({msg[:50]})"))) if pl else '-'
            inp = e['input'] if len(e['input']) <= 60 else e['input'][:57] + '...'
            api = ('exported' if e.get('exported') else 'internal') + (', object built field by field' if e.get('object_input') else '')
            name = e['source'] + (f" ({e['fn']})" if dup[e['source']] > 1 else '')
            print(f"| `{name}` | {api} | `{inp}` | {e['panic']} | {e['node']['outcome']}: `{str(node)[:70]}` | {plain} |")
        print()


if __name__ == '__main__':
    main()

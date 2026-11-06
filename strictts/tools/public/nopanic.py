"""Uniform `JS.NoPanic` attempts over every function of an emitted coverage module.

For each function (not only those with loops) one file with one theorem

    theorem np_f (I : Impl) (w : World TT) <arguments> <hypotheses> :
        JS.NoPanic (callFun I program fRef <arguments>) w := by
      ts_auto
      np_stuck

in a file that imports the library's root `StrictTS` (the lemma set of a user of the library, as the
difftool's files have; before e57150b only `StrictTS.Proof.Auto`) and ends with `np_used np_f` (the
modules outside Auto's imports whose lemmas the proof uses, tools/public/lean/NoPanicDiag.lean),

with the argument hypotheses of tools/public/attempts.py (array, Map, Set and dictionary
arguments are allocated cells; objects are allocated cells with every field initialised, their
array/Map/Set/dictionary fields allocated cells too), plus, where references below the first level
exist (the inner arrays of `number[][]`, objects held in fields, references inside optional,
union, tuple, record or `unknown` arguments), `w.Closed` (every reference stored in the heap names
a cell) and `Val.Live w v` for each such argument held outside the heap; and
`w.ModuleInit I program` (the module has been initialised) when the code reads a module variable.
`np_stuck` (tools/public/lean/NoPanicDiag.lean) names the first stuck construct of whatever goal
`ts_auto` leaves.

Not attempted (recorded with the reason): functions with a parameter of function type (the
statement would quantify over every callback; their fixed-callback wrappers `cb_*` are attempted
instead), the forwarding wrappers `mono_*` (their instances are attempted), the translator's own
library code (`String.prototype.split`), and functions attempted already in another module
(`--exclude`, by source name and signature).

usage: python3 -I tools/public/nopanic.py MODULE.lean OUTDIR [--exclude A_np.json]...
           [--only-prefix P] [--set LABEL] [--ext-specs]
  (--ext-specs: also the specifications of the externs the code reaches, attempts.EXT_SPECS)
  writes OUTDIR/<Module>_np_<k>.lean and OUTDIR/<Module>_np.json
"""
import hashlib
import json
import os
import re
import sys

sys.dont_write_bytecode = True  # (python -I ignores PYTHONDONTWRITEBYTECODE)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import attempts as A  # noqa: E402  (tools/public/attempts.py: module parsing, statements, IR facts)

LIVE_TY = re.compile(r'\.(arr|obj|map|set|dict|tarr|promise|box|ext|dyn)\b')
# 5x Lean's default: the attempts of 2026-10-24 ran with the default (200,000) and only those that
# reached it were run again with this limit; an attempt that stays under a limit runs the same
# under any higher one
HEARTBEATS = 1000000


def closure(base, defs):
    seen, todo = {base}, [base]
    while todo:
        for c in re.findall(r'«([^»]+)Ref»', defs.get(todo.pop(), '')):
            if c in defs and c not in seen:
                seen.add(c)
                todo.append(c)
    return sorted(seen)


def main():
    argv = sys.argv[1:]
    exclude, only_prefix, label = set(), None, None
    while '--exclude' in argv:
        i = argv.index('--exclude')
        for a in json.load(open(argv[i + 1]))['attempts']:
            exclude.add((a['source'], tuple(a['args']), a['ret']))
        for a in json.load(open(argv[i + 1])).get('skipped', []):
            exclude.add((a['source'], tuple(a['args']), a['ret']))
        del argv[i:i + 2]
    if '--only-prefix' in argv:
        i = argv.index('--only-prefix'); only_prefix = argv[i + 1]; del argv[i:i + 2]
    if '--set' in argv:
        i = argv.index('--set'); label = argv[i + 1]; del argv[i:i + 2]
    ext_specs = '--ext-specs' in argv
    if ext_specs:
        argv.remove('--ext-specs')
    module, outdir = argv
    text = open(module).read()
    mod = os.path.splitext(os.path.basename(module))[0]
    ns, classes, refs, defs = A.parse_module(text)
    fields = {c: f for c, f in re.findall(r'^abbrev «(.+?)»\.fields : Fields := (.*)$', text, re.M)}
    mi = text.find('def mainBlock')
    main_block = text[mi:text.find('\n\n', mi)] if mi >= 0 else ''
    os.makedirs(outdir, exist_ok=True)
    entries, skipped = [], []
    k = 0
    for base, body in defs.items():
        args, ret, src = refs[base]
        info = {'fn': base, 'source': src, 'args': args, 'ret': ret}
        if '.prototype.' in src:
            continue  # the translator's own library code, not the project's
        if only_prefix is not None and not base.startswith(only_prefix):
            continue
        if base.startswith('mono_'):
            continue  # a forwarding wrapper: its instance is attempted
        if (src, tuple(args), ret) in exclude:
            continue
        if any(A.strip_parens(a).startswith('.fn') for a in args):
            skipped.append({**info, 'reason': 'callback parameter (attempted through its cb_ wrapper)'})
            continue
        cl = closure(base, defs)
        reach = '\n'.join(defs[c] for c in cl)
        loops, cbs = A.features(reach)
        binders, hyps, vs, notes = A.statement(base, args, classes)
        extra = []
        plain = lambda t: A.parse_ty(t)[0] == 'other' or (A.parse_ty(t)[0] == 'obj' and A.parse_ty(t)[1] not in classes)
        live = [i for i, t in enumerate(args) if plain(t) and LIVE_TY.search(t)]
        dangling = any(n.startswith('dangling') for n in notes) or bool(live)
        if dangling:
            extra.append('(hcl : w.Closed)')
            extra += [f'(hlv{i} : Val.Live w v{i})' for i in live]
        modinit = '«g_' in reach
        if modinit:
            extra.append('(hmi : w.ModuleInit I program)')
        exts = A.ext_hyps(reach) if ext_specs else []
        extra += exts
        name = f'np_{base}'
        fname = f'{mod}_np_{k}.lean'
        k += 1
        lines = [f'import {mod}', 'import StrictTS', 'import NoPanicDiag',
                 'set_option maxRecDepth 100000', 'open StrictTS StrictTS.Frontend', f'namespace {ns}', '']
        start = len(lines) + 1
        lines.append(f'set_option maxHeartbeats {HEARTBEATS} in')
        lines.append(f'theorem «{name}» (I : Impl) (w : World TT) {" ".join(binders)}'.rstrip())
        hs = hyps + extra
        if hs:
            lines.append(f'    {" ".join(hs)} :')
        else:
            lines[-1] += ' :'
        lines.append(f'    JS.NoPanic (callFun I program «{base}Ref» {vs}) w := by')
        lines.append('  ts_auto')
        lines.append('  np_stuck')
        end = len(lines)
        lines.append(f'#print axioms «{name}»')
        lines.append(f'np_used «{name}»')
        lines.append(f'end {ns}')
        open(os.path.join(outdir, fname), 'w').write('\n'.join(lines) + '\n')
        # what the run depends on: the code it reaches, the classes it mentions, the module body when
        # it reads module variables (so that equal digests in two modules mean the same attempt)
        used = sorted(c for c in fields if f'"{c}"' in reach)
        digest = hashlib.sha256('\n'.join([f'{c}:{refs[c]}:{defs[c]}' for c in cl] + [f'{c}={fields[c]}' for c in used]
                                           + ([main_block] if modinit else [])).encode()).hexdigest()[:16]
        entries.append({**info, 'loops': loops, 'callbacks': cbs, 'async': ret.startswith('(.promise'),
                        'statement': 'NoPanic', **A.static_facts(reach, args), 'notes': notes,
                        'dangling': dangling, 'module_init': modinit, 'closure': cl, 'closure_hash': digest,
                        'uses_dyn': '.dyn' in reach or any('.dyn' in a for a in args),
                        'theorem': name, 'file': fname, 'from': start, 'to': end})
    json.dump({'module': mod, 'namespace': ns, 'set': label or mod, 'statement': 'NoPanic',
               'attempts': entries, 'skipped': skipped},
              open(os.path.join(outdir, f'{mod}_np.json'), 'w'), indent=1)
    print(f'{mod}: {len(defs)} functions, {len(entries)} attempts, {len(skipped)} not attempted')


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Copy JimpleLean's CardDemo proofs (a frozen snapshot's Examples/CardDemo/<Prog>*.lean) into
EquivLean/Modernize/JL/, for the programs whose Java side JimpleLean's session proves.

A copy = a provenance header + the snapshot file with only these changes:
- `import Examples.CardDemo.X` -> `import EquivLean.Modernize.JL.X`;
- the program's `jimple_import "examples_java/<prog>/jimple" as <ALIAS>` -> `import
  EquivLean.Modernize.<Prog>.JavaGen` (the same Jimple files: equiv-lean's generated program);
- `<ALIAS>.` -> `EquivLean.Modernize.<Prog>.Java.Gen.`;
- the namespace `Examples.CardDemo` -> `EquivLean.Modernize.JL`.
All copies share one namespace, as the originals do (CBCUS01C's proofs use CBACT02C's helpers).

  tools/modernize/import_jl.py SNAPSHOT_DIR PROG:ALIAS [PROG:ALIAS ...] [--check]
  e.g. import_jl.py ~/jimplelean_work/snapshots/JimpleLean-20261024T2006Z Cbact02c:CB Cbcus01c:CU
--check compares the existing copies with the snapshot instead of writing.
"""
import os
import re
import sys

R = '/home/user/equivlean'
DST = os.environ.get('JL_DST', f'{R}/EquivLean/Modernize/JL')


def transform(text, prog, alias, stamp, name):
    out = text
    imp_re = re.compile(rf'^jimple_import "examples_java/{prog.lower()}/jimple" as {alias}\s*$', re.M)
    if alias and imp_re.search(out):
        out = imp_re.sub('', out)
        # the generated program comes in by import, which must precede everything else
        out = re.sub(r'^(import [^\n]+\n)(?!import )', rf'\1import EquivLean.Modernize.{prog}.JavaGen\n',
                     out, count=1, flags=re.M)
    out = re.sub(r'^import Examples\.CardDemo\.(\w+)', r'import EquivLean.Modernize.JL.\1', out, flags=re.M)
    if alias:
        out = re.sub(rf'(?<![\w.]){alias}\.', f'EquivLean.Modernize.{prog}.Java.Gen.', out)
    out = out.replace('namespace Examples.CardDemo', 'namespace EquivLean.Modernize.JL')
    out = out.replace('end Examples.CardDemo', 'end EquivLean.Modernize.JL')
    out = out.replace('Examples.CardDemo.', 'EquivLean.Modernize.JL.')
    header = (f'-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/{stamp},\n'
              f'-- Examples/CardDemo/{name}); proved by JimpleLean\'s own session.  Only the imports, the\n'
              f'-- program (`{alias}`, the same Jimple files, is equiv-lean\'s generated\n'
              f'-- `EquivLean.Modernize.{prog}.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).\n')
    return header + out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    check = '--check' in sys.argv
    snap = args[0].rstrip('/')
    stamp = os.path.basename(snap)
    src_dir = f'{snap}/Examples/CardDemo'
    os.makedirs(DST, exist_ok=True)
    bad = 0
    for spec in args[1:]:
        prog, alias = spec.split(':')
        names = sorted(n for n in os.listdir(src_dir) if n.startswith(prog) and n.endswith('.lean'))
        if not names:
            sys.exit(f'no Examples/CardDemo/{prog}*.lean in {snap}')
        for n in names:
            new = transform(open(f'{src_dir}/{n}', encoding='utf-8').read(), prog, alias, stamp, n)
            path = f'{DST}/{n}'
            if check:
                cur = open(path, encoding='utf-8').read() if os.path.exists(path) else None
                ok = cur == new
                bad += not ok
                print(f'{n}: {"same" if ok else "DIFFERS" if cur is not None else "MISSING"}')
            else:
                open(path, 'w', encoding='utf-8').write(new)
                print(f'wrote {path}')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()

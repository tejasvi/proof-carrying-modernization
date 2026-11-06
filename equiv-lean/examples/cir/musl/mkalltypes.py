#!/usr/bin/env python3
"""Generate musl's obj/include/bits/alltypes.h the way its Makefile does
(`sed -f tools/mkalltypes.sed arch/$ARCH/bits/alltypes.h.in include/alltypes.h.in`),
reimplemented here (the tarball's sed script is read as data only, never run).

  mkalltypes.py ARCH_ALLTYPES_IN INCLUDE_ALLTYPES_IN OUT
"""
import re
import sys

def conv(line):
    m = re.match(r'^TYPEDEF (.*) ([^ ]*);$', line)
    if m:
        t, n = m.group(1), m.group(2)
        return (f'#if defined(__NEED_{n}) && !defined(__DEFINED_{n})\n'
                f'typedef {t} {n};\n#define __DEFINED_{n}\n#endif\n')
    m = re.match(r'^STRUCT * ([^ ]*) (.*);$', line)
    if m:
        n, body = m.group(1), m.group(2)
        return (f'#if defined(__NEED_struct_{n}) && !defined(__DEFINED_struct_{n})\n'
                f'struct {n} {body};\n#define __DEFINED_struct_{n}\n#endif\n')
    m = re.match(r'^UNION * ([^ ]*) (.*);$', line)
    if m:
        n, body = m.group(1), m.group(2)
        return (f'#if defined(__NEED_union_{n}) && !defined(__DEFINED_union_{n})\n'
                f'union {n} {body};\n#define __DEFINED_union_{n}\n#endif\n')
    return line + '\n'

out = []
for path in sys.argv[1:3]:
    with open(path, encoding='utf-8') as f:
        for raw in f.read().split('\n')[:-1] if True else []:
            out.append(conv(raw))
with open(sys.argv[3], 'w', encoding='utf-8') as f:
    f.write(''.join(out))

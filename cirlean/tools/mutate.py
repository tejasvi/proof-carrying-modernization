#!/usr/bin/env python3
"""Mutation testing of the verified examples: plant a bug in the C++ source,
rebuild its ClangIR and Lean module, and re-check the unchanged proof file
against it. A proof that still checks on a mutant either has a spec too weak
to notice the change, or the mutant is equivalent; a proof that fails has
"killed" the mutant.

Usage: mutate.py EXAMPLE [--only-proved] [--max K] [--list]
       EXAMPLE is the Lean file name under Examples/ (e.g. Basics); its C++
       source is Examples/cpp/<lowercase>.cpp and the proof file imports
       Examples.Gen.<EXAMPLE>.
Mutant 0 is the unmodified source (positive control: it must check).
Results: one JSON line per mutant on stdout, a summary line at the end.
"""
import argparse
import json
import os
import re
import subprocess
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TC = '/home/user/cirlean_work/toolchain/upstream-4955d32b/bin'
CX = '/home/user/cirlean_work/dl_cir2c_eb2a332/cir2c-eb2a332/libcxx/include/c++/v1'
LEAN_TC = '/home/user/.elan/toolchains/leanprover--lean4---v4.35.0'
LEAN_OPTS = ['-j', '1', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false']

# (pattern, replacement, description); applied to one occurrence at a time
MUTATIONS = [
    (r'(?<![<>=!-])<(?![<=])', '<=', '< to <='),
    (r'<=', '<', '<= to <'),
    (r'(?<![-<>=])>(?![>=])', '>=', '> to >='),
    (r'>=', '>', '>= to >'),
    (r'==', '!=', '== to !='),
    (r'!=', '==', '!= to =='),
    (r'(?<![+=])\+(?![+=])', '-', '+ to -'),
    (r'(?<![-=>])-(?![-=>])', '+', '- to +'),
    (r'\+\+', '--', '++ to --'),
    (r'\+=', '-=', '+= to -='),
    (r'-=', '+=', '-= to +='),
    (r"(?<=[\w)\]]) \* (?=[\w(])", " + ", "* to +"),
    (r'\b1\b', '2', '1 to 2'),
    (r'\b0\b', '1', '0 to 1'),
    (r'&&', '||', '&& to ||'),
    (r'\|\|', '&&', '|| to &&'),
    (r'\btrue\b', 'false', 'true to false'),
    (r'\bfalse\b', 'true', 'false to true'),
]

CONTROL = {'if', 'for', 'while', 'switch', 'catch', 'do', 'else', 'try', 'return'}


def blank_noncode(src):
    """`src` with comments, preprocessor lines and literals replaced by spaces
    (positions preserved)."""
    out = list(src)
    i, n = 0, len(src)

    def blank(a, b):
        for k in range(a, min(b, n)):
            if out[k] != '\n':
                out[k] = ' '
    while i < n:
        if src.startswith('//', i) or (src[i] == '#' and (i == 0 or src[i - 1] == '\n')):
            j = src.find('\n', i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        elif src.startswith('/*', i):
            j = src.find('*/', i)
            j = n if j < 0 else j + 2
            blank(i, j)
            i = j
        elif src[i] in '"\'':
            j = i + 1
            while j < n and src[j] != src[i]:
                j += 2 if src[j] == '\\' else 1
            blank(i, j + 1)
            i = j + 1
        else:
            i += 1
    return ''.join(out)


def scan(src):
    """Code positions inside function bodies, each mapped to the generated
    name of its function (`<Class>_<method>` or `<function>`)."""
    clean = blank_noncode(src)
    owner = {}
    stack = []          # per open brace: ('class', name) | ('func', name) | ('block', None)
    head = 0            # start of the current declaration header
    for i, c in enumerate(clean):
        if c == '{':
            h = clean[head:i]
            m = re.search(r'\b(struct|class)\s+(\w+)[^()]*$', h)
            f = None
            for mm in re.finditer(r'(~?\w+)\s*\(', h):
                if mm.group(1) not in CONTROL:
                    f = mm.group(1)
                    break
            func = next((s for s in stack if s[0] == 'func'), None)
            if func is None and m and not f:
                stack.append(('class', m.group(2)))
            elif func is None and f:
                cls = [s[1] for s in stack if s[0] == 'class']
                stack.append(('func', '_'.join(cls + [f.lstrip('~')])))
            else:
                stack.append(('block', None))
            head = i + 1
        elif c == '}':
            if stack:
                stack.pop()
            head = i + 1
        elif c == ';':
            head = i + 1
        elif c != ' ' and c == src[i]:
            func = next((s for s in stack if s[0] == 'func'), None)
            if func is not None:
                owner[i] = func[1]
    return owner


def mutants(src):
    owner = scan(src)
    out = []
    for pat, rep, desc in MUTATIONS:
        for m in re.finditer(pat, src):
            pos = m.start() + len(m.group(0)) - len(m.group(0).lstrip())
            if pos not in owner:
                continue
            line = src.count('\n', 0, m.start()) + 1
            out.append({'mutation': desc, 'line': line, 'function': owner[pos],
                        'text': src.splitlines()[line - 1].strip(),
                        'src': src[:m.start()] + rep + src[m.end():]})
    return out


def run(cmd, cwd=None, env=None, timeout=900):
    t0 = time.time()
    try:
        r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout + r.stderr, time.time() - t0
    except subprocess.TimeoutExpired:
        return -1, 'timeout', time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('example')
    ap.add_argument('--max', type=int, default=1000)
    ap.add_argument('--only-proved', action='store_true',
                    help='only mutate functions whose fn_<name> the proof file mentions')
    ap.add_argument('--list', action='store_true', help='list the mutants and stop')
    ap.add_argument('--work', default='/home/user/cirlean_work/mutants')
    ap.add_argument('--timeout', type=int, default=900)
    a = ap.parse_args()
    ex = a.example
    assert re.fullmatch(r'[A-Z][A-Za-z0-9]*', ex), ex
    cpp = os.path.join(ROOT, 'Examples', 'cpp', ex.lower() + '.cpp')
    proof = os.path.join(ROOT, 'Examples', ex + '.lean')
    src = open(cpp).read()
    proved = set(re.findall(r'\bfn_(\w+)', open(proof).read()))
    ms = mutants(src)
    if a.only_proved:
        ms = [m for m in ms if m['function'] in proved]
    ms = [{'mutation': 'none (control)', 'line': 0, 'function': '-', 'text': '', 'src': src}] + ms[:a.max]
    if a.list:
        for k, m in enumerate(ms):
            print(k, m['function'], m['line'], m['mutation'], '|', m['text'])
        return
    run_dir = os.path.join(a.work, ex + '_' + time.strftime('%Y%m%dT%H%M%SZ', time.gmtime()))
    os.makedirs(run_dir)
    lp = os.path.join(ROOT, '.lake/build/lib/lean') + ':' + os.path.join(LEAN_TC, 'lib/lean')
    counts = {}
    for k, m in enumerate(ms):
        wd = os.path.join(run_dir, f'm{k}')
        gen_dir = os.path.join(wd, 'src', 'Examples', 'Gen')
        olean_dir = os.path.join(wd, 'olean', 'Examples', 'Gen')
        os.makedirs(gen_dir)
        os.makedirs(olean_dir)
        mcpp = os.path.join(wd, ex.lower() + '.cpp')
        with open(mcpp, 'w') as fh:
            fh.write(m['src'])
        rec = {k2: v for k2, v in m.items() if k2 != 'src'}
        rec['mutant'] = k
        cir = os.path.join(wd, ex.lower() + '.cir')
        rc, out, _ = run([f'{TC}/clang++', '-std=c++20', '-nostdinc++', '-isystem', CX, '-fclangir',
                          '-emit-cir', '-Xclang', '-fno-clangir-call-conv-lowering', '-w', mcpp, '-o', cir],
                         timeout=300)
        if rc != 0:
            rec['result'] = 'does not compile'
        else:
            gen = os.path.join(gen_dir, ex + '.lean')
            rc, out, _ = run([os.path.join(ROOT, '.lake/build/bin/cir2lean'), cir, f'Gen.{ex}', gen], timeout=300)
            env = dict(os.environ)
            env['LEAN_PATH'] = os.path.join(wd, 'olean') + ':' + lp
            if rc == 0:
                rc, out, _ = run([os.path.join(LEAN_TC, 'bin/lean')] + LEAN_OPTS +
                                 ['-R', os.path.join(wd, 'src'), '-o', os.path.join(olean_dir, ex + '.olean'), gen],
                                 cwd=ROOT, env=env, timeout=a.timeout)
            if rc != 0:
                rec['result'] = 'generated module does not compile'
                rec['detail'] = out[-300:]
            else:
                rc, out, secs = run([os.path.join(LEAN_TC, 'bin/lean')] + LEAN_OPTS + [proof],
                                    cwd=ROOT, env=env, timeout=a.timeout)
                errs = [l for l in out.splitlines() if re.match(r'.*\.lean:\d+:\d+: error', l)]
                rec['secs'] = round(secs)
                if rc == 0 and not errs and 'sorry' not in out:
                    rec['result'] = 'SURVIVED'
                elif out == 'timeout':
                    rec['result'] = 'timeout'
                else:
                    rec['result'] = 'killed'
                    # the theorem whose proof failed
                    lines = open(proof).read().splitlines()
                    if errs:
                        ln = int(re.match(r'.*\.lean:(\d+):', errs[0]).group(1))
                        thm = next((l.split()[1] for l in reversed(lines[:ln]) if l.startswith('theorem ')), '?')
                        rec['failed_theorem'] = thm
                        rec['n_errors'] = len(errs)
                    rec['first_error'] = (errs[0] if errs else out[-300:])[:300]
        counts[rec['result']] = counts.get(rec['result'], 0) + 1
        print(json.dumps(rec), flush=True)
    print(json.dumps({'example': ex, 'mutants': len(ms) - 1, 'run_dir': run_dir, 'counts': counts}), flush=True)


if __name__ == '__main__':
    main()

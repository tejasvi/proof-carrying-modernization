"""Confirm the panicking inputs of the counterexample search in Node.

For each `NPCE <module/function> :: <panic message> :: <arguments>` line of SEARCHDIR/*.txt, run
the original TypeScript function (instrumented build of tools/public/node/build.js) on the same
arguments (tools/public/node/run.js under the Node permission model, one guarded job each) and
record whether the run reaches a value its TypeScript type excludes.

usage: python3 -I tools/public/np_node.py NPDIR SEARCHDIR NODEDIR > SEARCHDIR/node.jsonl
  NODEDIR/<project> and NODEDIR/<project>-cb: builds of the project and of its cb_ wrappers
"""
import glob
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def project_of(mod):
    return 'es-toolkit' if mod.startswith('Cov_es_toolkit') else 'thealgorithms-ts'


def doc_params(module_text, fn):
    """Parameter names and StrictTS types from the Lean doc comment of `fn`'s reference."""
    m = re.search(r'/-- `([^`]*)` -/\ndef «' + re.escape(fn) + r'Ref»', module_text)
    if not m:
        return None
    s = m.group(1)
    inner = s[s.index('(') + 1:s.rindex(')')] if '(' in s else ''
    out, depth, cur = [], 0, ''
    for ch in inner:
        depth += ch in '(<[{'
        depth -= ch in ')>]}'
        if ch == ',' and depth == 0:
            out.append(cur.strip()); cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return [tuple(x.split(': ', 1)) if ': ' in x else (x, '') for x in out if x != 'this']


def norm(t):
    return re.sub(r'\s+|readonly', '', t)


def locate(index, display, params):
    """The index item for a Lean function (display name `f`, `C.m`, `C.get p`, `f<number>`)."""
    base = re.sub(r'<[^<>]*>', '', display)
    while re.search(r'<[^<>]*>', base):
        base = re.sub(r'<[^<>]*>', '', base)
    cands = [(f, it) for f, items in index.items() for it in items if it['name'] == base]
    if len(cands) > 1 and params is not None:
        names = [p[0] for p in params]
        cands = [c for c in cands if [p['name'] for p in c[1]['params']] == names] or cands
    if len(cands) > 1 and params is not None:
        tys = [norm(p[1]) for p in params]
        cands = [c for c in cands if [norm(p['type']) for p in c[1]['params']] == tys] or cands
    return cands


def main():
    npdir, sdir, nodedir = sys.argv[1:4]
    nodedir = os.path.abspath(nodedir)
    texts = {}
    for txt in sorted(glob.glob(os.path.join(sdir, '*.txt'))):
        for line in open(txt):
            if not line.startswith('NPCE '):
                continue
            key, msg, args = line[len('NPCE '):].rstrip('\n').split(' :: ', 2)
            mod, fn = key.split('/', 1)
            proj = project_of(mod)
            rec = {'key': key, 'panic': msg, 'args': args}
            src = fn
            if fn.startswith('cb_'):
                build = os.path.join(nodedir, proj + '-cb')
                index = json.load(open(os.path.join(build, 'index.json')))
                cands = [(f, it) for f, items in index.items() for it in items if it['name'] == fn]
            else:
                build = os.path.join(nodedir, proj)
                index = json.load(open(os.path.join(build, 'index.json')))
                if mod not in texts:
                    texts[mod] = open(os.path.join(os.path.dirname(npdir), 'lean', mod + '.lean')).read()
                meta = json.load(open(os.path.join(npdir, f'{mod}_np.json')))
                src = next(a['source'] for a in meta['attempts'] if a['fn'] == fn)
                cands = locate(index, src, doc_params(texts[mod], fn))
            if not cands:
                print(json.dumps({**rec, 'node': {'outcome': 'unlocated', 'candidates': []}}), flush=True)
                continue
            # several functions of that name and signature (e.g. a predicate in src/ and in
            # src/compat/): run each; the outcome counts when they agree
            runs = []
            for f, it in cands[:4]:
                cmd = [os.path.join(ROOT, 'tools', 'run.sh'), '0.02', '60', 'node', '--permission',
                       f'--allow-fs-read={build}', f'--allow-fs-read={os.path.join(HERE, "node")}',
                       os.path.join(HERE, 'node', 'run.js'), build, f, it['name'], it['kind'], args]
                p = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT)
                last = [l for l in p.stdout.splitlines() if l.startswith('{')]
                runs.append((f, it, json.loads(last[-1]) if last else {'outcome': 'no output', 'stderr': p.stderr[-300:]}))
            f, it, node = runs[0]
            if len(runs) > 1 and len({(r[2]['outcome'] == 'violation') for r in runs}) > 1:
                node = {'outcome': 'ambiguous', 'runs': [{'file': r[0], **r[2]} for r in runs]}
            out = {**rec, 'file': f, 'item': it['name'], 'kind': it['kind'], 'exported': it.get('exported'),
                   'candidates': len(runs), 'node': node}
            if node['outcome'] == 'violation':
                # the same input with the checks off: does the value the types exclude escape (a
                # result outside the declared return type, an exception, a run that does not end)?
                ret = it.get('ret', '')
                inst = re.search(r'<([^<>]*)>$', src) if not fn.startswith('cb_') else None
                if inst and it.get('typeParams'):
                    for tp, ty in zip(it['typeParams'], [x.strip() for x in inst.group(1).split(',')]):
                        ret = re.sub(r'\b' + re.escape(tp) + r'\b', ty, ret)
                cmd = [os.path.join(ROOT, 'tools', 'run.sh'), '0.02', '20', 'node', '--permission',
                       f'--allow-fs-read={build}', f'--allow-fs-read={os.path.join(HERE, "node")}',
                       os.path.join(HERE, 'node', 'run.js'), build, f, it['name'], it['kind'], args, 'plain', ret]
                p = subprocess.run(cmd, capture_output=True, text=True, cwd=ROOT)
                last = [l for l in p.stdout.splitlines() if l.startswith('{')]
                out['plain'] = json.loads(last[-1]) if last else {'outcome': 'timeout', 'note': 'no result within 20 s'}
                out['plain']['ret'] = ret
            print(json.dumps(out), flush=True)


if __name__ == '__main__':
    main()

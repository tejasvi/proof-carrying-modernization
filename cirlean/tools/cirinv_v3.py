#!/usr/bin/env python3
"""cirinv: loop invariants for C++ functions, mined from executions and
checked by Lean.

For a function of a ClangIR module (with its cir2lean module), cirinv
  1. states a no-UB theorem with generic arguments (integers in the range of
     their type; vectors and pointees in fresh live blocks): the stub;
  2. runs the function in the Lean semantics (`cirrun`, CIR_TRACE) on sample
     inputs and records the variables at every loop head;
  3. keeps the candidate invariants (linear facts over the loop's variables,
     the parameters and vector lengths) that hold at every recorded head, and
     candidate variants (expressions that decrease and stay non-negative);
  4. Houdini: proves the stub with all candidates; Lean reports each
     candidate that is not established or not preserved (`@FAIL k`), it is
     dropped, and the step repeats until the candidates are inductive;
  5. reports the result: `proved` (the no-UB theorem holds; the final proof
     script is written and checked without `sorry`), or the goals that
     remain (overflow conditions, ... : preconditions for the caller), or a
     sample input on which the function has undefined behaviour.

Usage:
  cirinv.py --out DIR --gen-lean GEN.lean --module Gen.X --cir FILE.cir
            --scan SCAN.json --sym SYMBOL
Everything runs on one core.
"""
import argparse
import itertools
import json
import os
import random
import re
import subprocess
import sys
import time

CIRLEAN = '/home/user/cirlean'
RUN = ['nice', '-n', '10', 'taskset', '-c', os.environ.get('CIRINV_CORE', '29')]
LEAN_KEYWORDS = {'fun', 'end', 'at', 'by', 'do', 'then', 'else', 'if', 'let', 'have', 'show',
                 'from', 'in', 'match', 'with', 'where', 'deriving', 'instance', 'structure',
                 'class', 'theorem', 'def', 'open', 'namespace', 'section', 'variable', 'universe',
                 'import', 'mutual', 'return', 'for', 'unless', 'try', 'catch', 'finally', 'break',
                 'continue', 'mut', 'calc', 'suffices', 'obtain', 'nomatch', 'nofun', 'local',
                 'Type', 'Prop', 'Sort', 'λ', 'notation', 'macro', 'syntax'}

_lean_path = None


def lean_path(extra):
    global _lean_path
    if _lean_path is None:
        r = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=CIRLEAN,
                           capture_output=True, text=True, timeout=120)
        _lean_path = r.stdout.strip()
    return _lean_path + ':' + extra


def ident(name, used):
    """A Lean identifier for a C++ name (guillemets for keywords)."""
    if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', name) and name not in LEAN_KEYWORDS:
        return name
    if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', name):
        return '«' + name + '»'
    base = re.sub(r'[^A-Za-z0-9_]', '_', name) or 'x'
    while base in used:
        base += '_'
    return base


# ---------------------------------------------------------------- types

def int_ty(ty):
    """'(.int true 32)' -> (signed, width), else None."""
    m = re.fullmatch(r'\(?\.int (true|false) (\d+)\)?', ty.strip())
    if not m:
        return None
    return (m.group(1) == 'true', int(m.group(2)))


def bounds(signed, w):
    return (-(2 ** (w - 1)), 2 ** (w - 1) - 1) if signed else (0, 2 ** w - 1)


VEC_ELEMS = {'int': (True, 32), 'unsigned int': (False, 32), 'long': (True, 64),
             'unsigned long': (False, 64), 'long long': (True, 64),
             'unsigned long long': (False, 64), 'short': (True, 16),
             'unsigned short': (False, 16), 'char': (True, 8), 'signed char': (True, 8),
             'unsigned char': (False, 8)}


def vec_elem(ty):
    """'(.ptr (.record "std::__1::vector<int, ...>"))' -> ((signed, w), byref)."""
    m = re.search(r'"std::__1::vector<([^,>]+)', ty)
    if not m:
        return None
    e = VEC_ELEMS.get(m.group(1).strip())
    if e is None:
        return None
    return e, ty.strip().startswith('(.ptr')


# ---------------------------------------------------------------- the stub

class Unsupported(Exception):
    pass


def stub_parts(func, rename):
    """Binders, hypotheses and argument list of the no-UB theorem."""
    binders, hyps, args, params = [], [], [], []
    used = set()
    blocks = []
    for k, p in enumerate(func['params']):
        cname = p['name'] or f'p{k}'
        nm = ident(rename.get(cname, cname), used)
        used.add(nm)
        ty = p['ty']
        it = int_ty(ty)
        if it:
            lo, hi = bounds(*it)
            binders.append(f'({nm} : Int)')
            hyps.append(f'(h_{k} : {lo} ≤ {nm} ∧ {nm} ≤ {hi})')
            args.append(f'.int {nm}')
            params.append({'cname': cname, 'lean': nm, 'kind': 'int', 'bounds': (lo, hi)})
            continue
        if ty.strip() in ('.bool', '(.bool)'):
            binders.append(f'({nm} : Bool)')
            args.append(f'.bool {nm}')
            params.append({'cname': cname, 'lean': nm, 'kind': 'bool'})
            continue
        ve = vec_elem(ty)
        if ve:
            (sg, w), byref = ve
            lo, hi = bounds(sg, w)
            binders.append(f'({nm} : List Int)')
            hyps.append(f'(h_{k} : ∀ x ∈ {nm}, {lo} ≤ x ∧ x ≤ {hi})')
            if byref:
                b, g, kk, t = f'{nm}_b', f'{nm}_g', f'{nm}_k', f'{nm}_t'
                binders.append(f'({b} {g} : Nat) ({kk} : BlockKind) ({t} : Ty)')
                hyps.append(f'(h_{k}b : cirM.blocks {b} = some ⟨{kk}, true, {t}, .vec {g} ({nm}.map .int)⟩)')
                hyps.append(f'(h_{k}l : {b} < cirM.next) (h_{k}k : {kk} ≠ .readonly)')
                hyps.append(f'(h_{k}n : {nm}.length < 2 ^ 31)')
                args.append(f'.ptr (.loc {b} [])')
                blocks.append(b)
            else:
                g = f'{nm}_g'
                binders.append(f'({g} : Nat)')
                hyps.append(f'(h_{k}n : {nm}.length < 2 ^ 31)')
                args.append(f'.vec {g} ({nm}.map .int)')
            params.append({'cname': cname, 'lean': nm, 'kind': 'vec', 'elem': (lo, hi)})
            continue
        m = re.fullmatch(r'\(\.ptr \(\.int (true|false) (\d+)\)\)', ty.strip())
        if m:
            lo, hi = bounds(m.group(1) == 'true', int(m.group(2)))
            b, kk = f'{nm}_b', f'{nm}_k'
            binders.append(f'({nm} : Int) ({b} : Nat) ({kk} : BlockKind)')
            hyps.append(f'(h_{k} : {lo} ≤ {nm} ∧ {nm} ≤ {hi})')
            hyps.append(f'(h_{k}b : cirM.blocks {b} = some ⟨{kk}, true, .int {m.group(1)} {m.group(2)}, .int {nm}⟩)')
            hyps.append(f'(h_{k}l : {b} < cirM.next) (h_{k}k : {kk} ≠ .readonly)')
            args.append(f'.ptr (.loc {b} [])')
            blocks.append(b)
            params.append({'cname': cname, 'lean': nm, 'kind': 'ptrint', 'bounds': (lo, hi)})
            continue
        raise Unsupported(f'parameter type {ty}')
    for a, b in itertools.combinations(blocks, 2):
        hyps.append(f'(h_{a}_{b} : {a} ≠ {b})')
    # the module's globals are blocks 0 .. G-1 of every reachable memory
    nglob = func.get('globals', 0)
    if nglob:
        hyps.append(f'(h_glob : {nglob} ≤ cirM.next)')
        for b in blocks:
            hyps.append(f'(h_glob_{b} : {nglob} ≤ {b})')
    return binders, hyps, args, params


def theorem(module, func, rename, tactics, name='noub'):
    binders, hyps, args, _ = stub_parts(func, rename)
    sig = ' '.join(binders + ['(cirM : Mem)'] + hyps)
    return (f'import CIR\nimport {module}\n\nopen CIR {module}\n\n'
            f'set_option maxHeartbeats 4000000\n\n'
            f'/-- No undefined behaviour in `{func["name"]}`. -/\n'
            f'theorem {name} {sig} :\n'
            f'    Returns ctx {json.dumps(func["sym"])} [{", ".join(args)}] cirM (fun _ _ => True) := by\n'
            + ''.join(f'  {t}\n' for t in tactics))


# ---------------------------------------------------------------- running Lean

MSG = re.compile(r'^(.*?):(\d+):(\d+): (info|warning|error): ?(.*)$')


def run_lean(path, olean_dir, timeout=900):
    env = dict(os.environ)
    env['LEAN_PATH'] = lean_path(olean_dir)
    t0 = time.time()
    try:
        r = subprocess.run(RUN + ['lake', 'env', 'lean', f'--root={os.path.dirname(path)}', path],
                           cwd=CIRLEAN, env=env, capture_output=True, text=True, timeout=timeout)
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return [('error', 'timeout')], time.time() - t0
    msgs = []
    for line in out.splitlines():
        mm = MSG.match(line)
        if mm and mm.group(1).endswith('.lean'):
            msgs.append([mm.group(4), mm.group(5)])
        elif line.startswith('@'):
            # reports of the cirlean tactics (`@FAIL`, `@OTHER`, `@STORED`, ...)
            msgs.append(['info', line])
        elif msgs:
            msgs[-1][1] += '\n' + line
    return [tuple(x) for x in msgs], time.time() - t0


def compile_gen(gen_lean, module, olean_dir, timeout=1800):
    """Compile the cir2lean module (copied under `<out>/src` so that its path
    matches its module name) to `<out>/olean`."""
    rel = module.replace('.', '/')
    target = os.path.join(olean_dir, rel + '.olean')
    if os.path.exists(target) and os.path.getmtime(target) >= os.path.getmtime(gen_lean):
        return True
    src_root = os.path.join(os.path.dirname(olean_dir), 'src')
    src = os.path.join(src_root, rel + '.lean')
    os.makedirs(os.path.dirname(src), exist_ok=True)
    os.makedirs(os.path.dirname(target), exist_ok=True)
    with open(gen_lean) as fi, open(src, 'w') as fo:
        fo.write(fi.read())
    env = dict(os.environ)
    env['LEAN_PATH'] = lean_path(olean_dir)
    r = subprocess.run(RUN + ['lake', 'env', 'lean', f'--root={src_root}', '-o', target, src],
                       cwd=CIRLEAN, env=env, capture_output=True, text=True, timeout=timeout)
    return r.returncode == 0


# ---------------------------------------------------------------- traces

def sample_inputs(params, n, rng, extreme=False):
    pools = []
    for p in params:
        if p['kind'] in ('int', 'ptrint'):
            lo, hi = p['bounds']
            base = (0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 16, 25, 30, -1, -2, -3, -7)
            if extreme:
                base = (lo, hi, hi - 1, lo + 1, 0, 1, -1)
            vals = [v for v in base if lo <= v <= hi]
            pools.append([str(v) if p['kind'] == 'int' else f'&{v}' for v in vals])
        elif p['kind'] == 'bool':
            pools.append(['0', '1'])
        elif p['kind'] == 'vec':
            lo, hi = p['elem']
            lists = [[]]
            for _ in range(30):
                ln = rng.randint(1, 7)
                lists.append([rng.randint(max(lo, -9), min(hi, 20)) for _ in range(ln)])
            pools.append(['[' + ','.join(map(str, xs)) + ']' for xs in lists])
    combos = list(itertools.product(*pools)) if pools else [()]
    rng.shuffle(combos)
    return combos[:n]


def run_traces(cirfile, sym, inputs, timeout=20):
    runs = []
    env = dict(os.environ)
    env['CIR_TRACE'] = '1'
    for inp in inputs:
        try:
            r = subprocess.run(RUN + [f'{CIRLEAN}/.lake/build/bin/cirrun', cirfile, sym] + list(inp),
                               env=env, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            runs.append({'input': inp, 'result': 'timeout', 'heads': []})
            continue
        heads = []
        for line in r.stderr.splitlines():
            if line.startswith('@LOOP'):
                rec = {}
                for tok in line.split()[1:]:
                    if '=' in tok:
                        k, v = tok.split('=', 1)
                        rec[k] = v
                heads.append(rec)
        runs.append({'input': inp, 'result': r.stdout.strip().splitlines()[0] if r.stdout.strip() else '',
                     'heads': heads})
    return runs


def value(v):
    """Trace text -> int (integers, iterator positions, pointees) or list."""
    if v.startswith('@') or v.startswith('*'):
        v = v[1:]
    if v.startswith('['):
        inner = v[1:-1]
        return [int(x) for x in inner.split(',')] if inner else []
    try:
        return int(v)
    except ValueError:
        return None


# ---------------------------------------------------------------- candidates

def head_env(rec, run_input, slots, params):
    """Values of the invariant's atoms at one loop head."""
    env = {}
    for s in slots:
        if s['trace'] in rec:
            v = value(rec[s['trace']])
            if isinstance(v, int):
                env[s['atom']] = v
    for k, p in enumerate(params):
        if p['kind'] == 'int':
            v = value(run_input[k]) if k < len(run_input) else None
            if isinstance(v, int):
                env[p['atom']] = v
        elif p['kind'] == 'vec':
            v = value(run_input[k]) if k < len(run_input) else None
            if isinstance(v, list):
                env[p['atom_len']] = len(v)
    return env


def candidates(envs, atoms):
    cands = []

    def add(text, f):
        try:
            if envs and all(f(e) for e in envs):
                cands.append(text)
        except KeyError:
            pass
    for x in atoms:
        add(f'0 ≤ {x}', lambda e, x=x: e[x] >= 0)
        add(f'1 ≤ {x}', lambda e, x=x: e[x] >= 1)
    for x, y in itertools.permutations(atoms, 2):
        add(f'{x} ≤ {y}', lambda e, x=x, y=y: e[x] <= e[y])
        add(f'{x} < {y}', lambda e, x=x, y=y: e[x] < e[y])
        add(f'{x} ≤ {y} + 1', lambda e, x=x, y=y: e[x] <= e[y] + 1)
        add(f'{x} = {y}', lambda e, x=x, y=y: e[x] == e[y])
        add(f'2 * {x} ≤ {y} + 2', lambda e, x=x, y=y: 2 * e[x] <= e[y] + 2)
    # drop facts implied by stronger kept ones (x < y implies x ≤ y, x ≤ y + 1)
    strong = set(cands)
    out = []
    for c in cands:
        m = re.fullmatch(r'(.+) ≤ (.+?)( \+ 1)?', c)
        if m and f'{m.group(1)} < {m.group(2)}' in strong and not m.group(3):
            continue
        out.append(c)
    return out


def variants(runs_envs, atoms):
    """Expressions that decrease strictly between consecutive heads of every
    run and stay non-negative."""
    out = []

    def ok(f):
        seen = False
        for envs in runs_envs:
            vals = []
            for e in envs:
                try:
                    vals.append(f(e))
                except KeyError:
                    return False
            if any(v < 0 for v in vals[:-1]):
                return False
            if any(b >= a for a, b in zip(vals, vals[1:])):
                return False
            seen = seen or len(vals) > 1
        return seen
    for x in atoms:
        if ok(lambda e, x=x: e[x]):
            out.append(x)
        if ok(lambda e, x=x: abs(e[x])):
            out.append(f'(({x}).natAbs : Int)')
    for y, x in itertools.permutations(atoms, 2):
        if ok(lambda e, x=x, y=y: e[y] - e[x]):
            out.append(f'{y} - {x}')
        if ok(lambda e, x=x, y=y: e[y] + 1 - e[x]):
            out.append(f'{y} + 1 - {x}')
    return out or ['0']


# ---------------------------------------------------------------- main loop

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--gen-lean', required=True)
    ap.add_argument('--module', required=True)
    ap.add_argument('--cir', required=True)
    ap.add_argument('--scan', required=True)
    ap.add_argument('--sym', required=True)
    ap.add_argument('--runs', type=int, default=40)
    ap.add_argument('--rounds', type=int, default=8)
    a = ap.parse_args()

    func = None
    with open(a.scan) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            j = json.loads(line)
            if j['sym'] == a.sym:
                func = j
    report = {'sym': a.sym, 'status': 'error', 'log': []}
    os.makedirs(a.out, exist_ok=True)
    olean_dir = os.path.join(a.out, 'olean')
    base = re.sub(r'[^A-Za-z0-9_]', '_', a.sym)[:80]
    work = os.path.join(a.out, 'work')
    os.makedirs(work, exist_ok=True)

    def finish(**kw):
        report.update(kw)
        print(json.dumps(report))
        sys.exit(0)

    if func is None:
        finish(status='error', reason='function not found in scan')
    report['name'] = func['name']
    if func['sym'] in func.get('callees', []):
        finish(status='recursive', reason='recursive functions need a specification (induction)')
    try:
        _, _, _, params = stub_parts(func, {})
    except Unsupported as e:
        finish(status='unsupported', reason=str(e))
    if not compile_gen(a.gen_lean, a.module, olean_dir):
        finish(status='error', reason='cir2lean module does not compile')

    rng = random.Random(1)
    runs = run_traces(a.cir, a.sym, sample_inputs(params, a.runs, rng))
    # extreme values (type bounds) find overflows; long loops just time out
    runs_x = run_traces(a.cir, a.sym, sample_inputs(params, 20, rng, extreme=True), timeout=3)
    ub = [r for r in runs + runs_x if r['result'].startswith('UB')]
    report['runs'] = len(runs) + len(runs_x)
    if ub:
        # a concrete input within the parameter types on which the semantics
        # reports undefined behaviour: no proof of the stub can exist
        finish(status='ub_witness',
               ub_inputs=[{'input': list(r['input']), 'result': r['result']} for r in ub[:5]])

    # probe: symbolic execution up to the loops
    loops = func['loops']
    probe_tac = ['cir_start', 'cir_vcg']
    if loops == 0:
        probe_tac.append('cir_houdini_report')
    else:
        probe_tac += ['all_goals (try cir_loop_info)', 'all_goals sorry']
    path = os.path.join(work, f'{base}_probe.lean')
    with open(path, 'w') as fh:
        fh.write(theorem(a.module, func, {}, probe_tac))
    msgs, dt = run_lean(path, olean_dir)
    report['log'].append({'step': 'probe', 'secs': round(dt, 1)})
    errs = [m for k, m in msgs if k == 'error']
    if errs:
        finish(status='error', reason='probe: ' + errs[0][:300])
    others = [m[len('@OTHER '):] for k, m in msgs if m.startswith('@OTHER')]
    if loops == 0:
        finish(status='proved' if not others else 'goals_left', other_goals=others[:10])
    stored = [m for k, m in msgs if m.startswith('@STORED')]
    passed = [m for k, m in msgs if m.startswith('@PASSED')]
    if not stored:
        finish(status='no_loop_reached', other_goals=others[:10])
    if len(stored) > 1 or loops > 1:
        report['note'] = 'several loops: only the first is handled'

    def parse_names(line):
        return [t.split(':') for t in line.split()[1:] if ':' in t]
    slot_names = [(n, k) for n, k in parse_names(stored[0]) if k in ('int', 'nat')]
    iters = [(n, k) for n, k in parse_names(passed[0] if passed else '@PASSED')
             if k == 'iter' and n.startswith('__begin')]
    stored_names = {n for n, _ in parse_names(stored[0])}
    # theorem binders: parameters keep their names unless the loop assigns them
    rename = {p['cname']: p['cname'] + '0' for p in params if p['cname'] in stored_names}
    _, _, _, params = stub_parts(func, rename)
    used = {p['lean'] for p in params}
    slots = []
    binders = []
    for n, k in slot_names:
        b = ident(n, used)
        used.add(b)
        binders.append(b)
        slots.append({'trace': n, 'atom': f'({b} : Int)', 'binder': b})
    for n, _ in iters[:1]:
        binders.append('it')
        slots.append({'trace': n, 'atom': '(it : Int)', 'binder': 'it'})
    for p in params:
        if p['kind'] == 'int':
            p['atom'] = f'({p["lean"]} : Int)'
        elif p['kind'] == 'vec':
            p['atom_len'] = f'(({p["lean"]}.length : Nat) : Int)'
    atoms = [s['atom'] for s in slots] + [p['atom'] for p in params if 'atom' in p] + \
            [p['atom_len'] for p in params if 'atom_len' in p]
    runs_envs = [[head_env(rec, r['input'], slots, params) for rec in r['heads']]
                 for r in runs if r['heads'] and not r['result'].startswith('UB')]
    envs = [e for es in runs_envs for e in es]
    cands = candidates(envs, atoms)
    vars_ = variants(runs_envs, atoms)
    report['trace_heads'] = len(envs)
    report['candidates0'] = len(cands)
    if not binders:
        finish(status='no_loop_variables', other_goals=others[:10])

    lam = 'fun ' + ' '.join(binders) + ' =>'
    final = None
    for var in vars_[:4]:
        cur = list(cands)
        for rnd in range(a.rounds):
            body = ' ∧ '.join(f'CIR.Cand {i} ({c})' for i, c in enumerate(cur)) or 'True'
            tac = ['cir_start', 'cir_vcg',
                   f'all_goals (first | cir_loop ({lam} {body}) ({lam} {var}) | skip)',
                   'all_goals cir_vcg', 'cir_houdini_report']
            path = os.path.join(work, f'{base}_h.lean')
            with open(path, 'w') as fh:
                fh.write(theorem(a.module, func, rename, tac))
            msgs, dt = run_lean(path, olean_dir)
            errs = [m for k, m in msgs if k == 'error']
            fails = sorted({int(m.split()[1]) for k, m in msgs if m.startswith('@FAIL')
                            and m.split()[1].isdigit()})
            others = [m[len('@OTHER '):] for k, m in msgs if m.startswith('@OTHER')]
            report['log'].append({'step': f'houdini {var} round {rnd}', 'cands': len(cur),
                                  'fails': len(fails), 'others': len(others),
                                  'errors': len(errs), 'secs': round(dt, 1)})
            if errs:
                report['last_error'] = errs[0][:400]
                break
            if not fails:
                final = (var, cur, others)
                break
            cur = [c for i, c in enumerate(cur) if i not in fails]
        if final and not final[2]:
            break
    if final is None:
        finish(status='houdini_failed')
    var, cur, others = final
    inv = ' ∧ '.join(cur) or 'True'
    report['invariant'] = inv
    report['variant'] = var
    if others:
        finish(status='goals_left', other_goals=others[:10])
    # the certificate: the same proof without candidate markers or sorry
    tac = ['cir_start', 'cir_vcg', f'all_goals (first | cir_loop ({lam} {inv}) ({lam} {var}) | skip)',
           'all_goals cir_vcg']
    path = os.path.join(a.out, f'{base}_proof.lean')
    with open(path, 'w') as fh:
        fh.write(theorem(a.module, func, rename, tac))
    msgs, dt = run_lean(path, olean_dir)
    bad = [m for k, m in msgs if k == 'error' or 'sorry' in m]
    report['log'].append({'step': 'certificate', 'secs': round(dt, 1), 'errors': len(bad)})
    finish(status='proved' if not bad else 'certificate_failed', proof=path,
           reason=(bad[0][:300] if bad else None))


if __name__ == '__main__':
    main()

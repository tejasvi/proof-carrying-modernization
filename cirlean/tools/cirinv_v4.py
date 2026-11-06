#!/usr/bin/env python3
"""cirinv v4: no-UB proofs for C++ functions, with loop invariants mined
from executions and preconditions inferred from UB witnesses. Lean checks
every result.

For a function of a ClangIR module, cirinv
  1. runs the function in the Lean semantics (`cirrun`, CIR_TRACE) on
     sample inputs (small values, values related to vector lengths, type
     extremes), recording the variables at every loop head and every input
     with undefined behaviour;
  2. if some input has UB, infers a precondition: a conjunction of simple
     facts about the parameters (sign, magnitude, non-zero, index below a
     vector length or a program constant, order of two parameters) that
     excludes every UB input seen while excluding few safe ones. It then
     samples inputs that satisfy the precondition and repeats with every new
     UB input (counterexample-guided);
  3. states the no-UB theorem with generic arguments (integers in the range
     of their type; vectors, arrays and pointees in fresh live blocks) and
     the precondition as hypotheses;
  4. runs Houdini on candidate loop invariants (linear facts true at every
     recorded loop head) and variants. Lean reports the candidates that are
     not inductive (`@FAIL k`); they are dropped and the step repeats;
  5. writes the proof script and checks it without `sorry`. If goals
     remain, the magnitude bounds of the precondition are tightened (at most
     twice).
Statuses: proved; proved_under (the precondition; ub_inputs lie outside it);
ub_witness (UB, and no precondition gave a proof); goals_left; recursive
(the UB input and the inferred precondition are reported, no proof is
attempted); unsupported; error.

Usage:
  cirinv_v4.py --cir FILE.cir --sym SYMBOL --out DIR [--json OUT.json]
               [--scan SCAN.json] [--gen-lean GEN.lean --module Gen.X]
Without --scan / --gen-lean, cirscan and cir2lean are run here. Everything
runs on one core (CIRINV_CORE, default 29). CIRLEAN selects the checkout.
"""
import argparse
import itertools
import json
import math
import os
import random
import re
import signal
import subprocess
import sys
import time

CIRLEAN = os.environ.get('CIRLEAN', '/home/user/cirlean')
RUN = ['nice', '-n', '10', 'taskset', '-c', os.environ.get('CIRINV_CORE', '29')]
LEAN_KEYWORDS = {'fun', 'end', 'at', 'by', 'do', 'then', 'else', 'if', 'let', 'have', 'show',
                 'from', 'in', 'match', 'with', 'where', 'deriving', 'instance', 'structure',
                 'class', 'theorem', 'def', 'open', 'namespace', 'section', 'variable', 'universe',
                 'import', 'mutual', 'return', 'for', 'unless', 'try', 'catch', 'finally', 'break',
                 'continue', 'mut', 'calc', 'suffices', 'obtain', 'nomatch', 'nofun', 'local',
                 'Type', 'Prop', 'Sort', 'λ', 'notation', 'macro', 'syntax'}

_lean_path = None


def run_cmd(cmd, timeout, env=None, cwd=None):
    """Run in a new process group and kill the whole group on timeout (lake
    does not pass the signal on to lean). Returns (rc or None, stdout, stderr)."""
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         env=env, cwd=cwd, start_new_session=True)
    try:
        out, err = p.communicate(timeout=timeout)
        return p.returncode, out, err
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.communicate()
        return None, '', 'timeout'


def lean_path(extra):
    global _lean_path
    if _lean_path is None:
        _, out, _ = run_cmd(['lake', 'env', 'printenv', 'LEAN_PATH'], 120, cwd=CIRLEAN)
        _lean_path = out.strip()
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


def ladder(lo, hi):
    """Magnitude bounds 2^k - 1 strictly inside the range [lo, hi]."""
    top = max(-lo, hi)
    return [2 ** k - 1 for k in (63, 62, 32, 31, 30, 24, 20, 16, 15, 12, 10, 8, 7, 5, 3)
            if 2 ** k - 1 < top]


# ---------------------------------------------------------------- the stub

class Unsupported(Exception):
    pass


def stub_parts(func, rename, arrays=frozenset(), pre=()):
    """Binders, hypotheses and argument list of the no-UB theorem. `arrays`:
    indices of `int*` parameters modelled as pointers to the first element
    of an array (otherwise: to one integer). `pre`: precondition facts."""
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
        if m and k in arrays:
            lo, hi = bounds(m.group(1) == 'true', int(m.group(2)))
            b, kk, t = f'{nm}_b', f'{nm}_k', f'{nm}_t'
            binders.append(f'({nm} : List Int) ({b} : Nat) ({kk} : BlockKind) ({t} : Ty)')
            hyps.append(f'(h_{k} : ∀ x ∈ {nm}, {lo} ≤ x ∧ x ≤ {hi})')
            hyps.append(f'(h_{k}b : cirM.blocks {b} = some ⟨{kk}, true, {t}, .arr ({nm}.map .int)⟩)')
            hyps.append(f'(h_{k}l : {b} < cirM.next) (h_{k}k : {kk} ≠ .readonly)')
            hyps.append(f'(h_{k}n : {nm}.length < 2 ^ 31)')
            args.append(f'.ptr (.loc {b} [.idx 0])')
            blocks.append(b)
            params.append({'cname': cname, 'lean': nm, 'kind': 'arr', 'elem': (lo, hi)})
            continue
        if m:
            lo, hi = bounds(m.group(1) == 'true', int(m.group(2)))
            b, kk = f'{nm}_b', f'{nm}_k'
            binders.append(f'({nm} : Int) ({b} : Nat) ({kk} : BlockKind)')
            hyps.append(f'(h_{k} : {lo} ≤ {nm} ∧ {nm} ≤ {hi})')
            hyps.append(f'(h_{k}b : cirM.blocks {b} = some ⟨{kk}, true, .int {m.group(1)} {m.group(2)}, .int {nm}⟩)')
            hyps.append(f'(h_{k}l : {b} < cirM.next) (h_{k}k : {kk} ≠ .readonly)')
            args.append(f'.ptr (.loc {b} [])')
            blocks.append(b)
            params.append({'cname': cname, 'lean': nm, 'kind': 'ptrint', 'bounds': (lo, hi),
                           'ptr_ty': m.group(0)})
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
    for i, fact in enumerate(pre):
        hyps.append(f'(h_pre{i} : {fact})')
    return binders, hyps, args, params


def theorem(module, func, rename, tactics, arrays=frozenset(), pre=(), name='noub'):
    binders, hyps, args, _ = stub_parts(func, rename, arrays, pre)
    sig = ' '.join(binders + ['(cirM : Mem)'] + hyps)
    what = 'under the precondition ' if pre else ''
    return (f'import CIR\nimport {module}\n\nopen CIR {module}\n\n'
            f'set_option maxHeartbeats 4000000\n\n'
            f'/-- No undefined behaviour in `{func["name"]}` {what}(generated by cirinv). -/\n'
            f'theorem {name} {sig} :\n'
            f'    Returns ctx {json.dumps(func["sym"])} [{", ".join(args)}] cirM (fun _ _ => True) := by\n'
            + ''.join(f'  {t}\n' for t in tactics))


# ---------------------------------------------------------------- running Lean

MSG = re.compile(r'^(.*?):(\d+):(\d+): (info|warning|error): ?(.*)$')


def run_lean(path, olean_dir, timeout=900):
    env = dict(os.environ)
    env['LEAN_PATH'] = lean_path(olean_dir)
    t0 = time.time()
    rc, out, err = run_cmd(RUN + ['lake', 'env', 'lean', f'--root={os.path.dirname(path)}', path],
                           timeout, env=env, cwd=CIRLEAN)
    if rc is None:
        return [('error', 'timeout')], time.time() - t0
    msgs = []
    for line in (out + err).splitlines():
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
    rc, _, _ = run_cmd(RUN + ['lake', 'env', 'lean', f'--root={src_root}', '-o', target, src],
                       timeout, env=env, cwd=CIRLEAN)
    return rc == 0


# ---------------------------------------------------------------- executions

SMALL = (0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 16, 25, 30, -1, -2, -3, -7)


def program_consts(cir_text, sym):
    """Small positive integer constants of the function and the array sizes
    of the module (candidate index bounds)."""
    m = re.search(r'^  cir\.func [^\n]*@' + re.escape(sym) + r'\(', cir_text, re.M)
    body = ''
    if m:
        end = cir_text.find('\n  }', m.end())
        body = cir_text[m.start():end if end > 0 else len(cir_text)]
    cs = [int(x) for x in re.findall(r'#cir\.int<(\d+)>', body)]
    cs += [int(x) for x in re.findall(r'!cir\.array<[^<>]* x (\d+)>', cir_text)]
    freq = {}
    for c in cs:
        if 2 <= c <= 2 ** 16:
            freq[c] = freq.get(c, 0) + 1
    return sorted(sorted(freq, key=lambda c: -freq[c])[:8])


def gen_input(params, consts, rng):
    """One random input: a Python value per parameter."""
    vals = [None] * len(params)
    lens = []
    for i, p in enumerate(params):
        if p['kind'] in ('vec', 'arr'):
            lo, hi = p['elem']
            ln = rng.randint(1 if p['kind'] == 'arr' else 0, 7)
            mags = ladder(lo, hi)
            xs = []
            for _ in range(ln):
                r = rng.random()
                if r < 0.75:
                    x = rng.randint(max(lo, -9), min(hi, 20))
                elif r < 0.9 and mags:
                    x = rng.choice(mags) * rng.choice((1, -1) if lo < 0 else (1,))
                else:
                    x = rng.choice((lo, hi))
                xs.append(x)
            vals[i] = xs
            lens.append(ln)
    for i, p in enumerate(params):
        if p['kind'] in ('int', 'ptrint'):
            lo, hi = p['bounds']
            r = rng.random()
            if lens and r < 0.3:
                ln = rng.choice(lens)
                v = rng.choice((ln - 1, ln, ln + 1, ln - 2, 0, ln // 2))
            elif r < 0.6:
                v = rng.choice(SMALL)
            elif r < 0.78:
                mags = ladder(lo, hi)
                v = rng.choice(mags) + rng.choice((0, 0, 1)) if mags else 0
                v = v * rng.choice((1, -1))
            elif r < 0.88 and consts:
                v = rng.choice(consts) + rng.choice((-1, 0, 1))
            else:
                v = rng.choice((lo, hi, lo + 1, hi - 1))
            if not lo <= v <= hi:
                v = min(max(v, lo), hi)
            vals[i] = v
        elif p['kind'] == 'bool':
            vals[i] = rng.randint(0, 1)
    return vals


def encode(params, vals):
    out = []
    for p, v in zip(params, vals):
        if p['kind'] in ('int', 'bool'):
            out.append(str(v))
        elif p['kind'] == 'ptrint':
            out.append(f'&{v}')
        elif p['kind'] == 'vec':
            out.append('[' + ','.join(map(str, v)) + ']')
        elif p['kind'] == 'arr':
            out.append('&[' + ','.join(map(str, v)) + ']')
    return out


def run_traces(cirfile, sym, params, inputs, timeout=3):
    runs = []
    env = dict(os.environ)
    env['CIR_TRACE'] = '1'
    for vals in inputs:
        inp = encode(params, vals)
        rc, out, err = run_cmd(RUN + [f'{CIRLEAN}/.lake/build/bin/cirrun', cirfile, sym] + inp,
                               timeout, env=env)
        if rc is None:
            runs.append({'vals': vals, 'input': inp, 'result': 'timeout', 'heads': []})
            continue
        heads = []
        for line in err.splitlines():
            if line.startswith('@LOOP'):
                rec = {}
                for tok in line.split()[1:]:
                    if '=' in tok:
                        k, v = tok.split('=', 1)
                        rec[k] = v
                heads.append(rec)
        res = out.strip().splitlines()[0] if out.strip() else ('error: ' + err.strip()[-120:])
        runs.append({'vals': vals, 'input': inp, 'result': res, 'heads': heads})
    return runs


def is_ub(r):
    return r['result'].startswith('UB')


def is_safe(r):
    return not is_ub(r) and r['result'] != 'timeout' and not r['result'].startswith('error')


# ---------------------------------------------------------------- preconditions

def atoms_for(params, consts):
    """Candidate precondition facts: Lean text, a test on input values, and a
    rank (higher = preferred among equally good facts)."""
    out = []

    def add(text, f, rank):
        out.append({'text': text, 'f': f, 'rank': rank})
    ints = [(i, p) for i, p in enumerate(params) if p['kind'] in ('int', 'ptrint')]
    seqs = [(i, p) for i, p in enumerate(params) if p['kind'] in ('vec', 'arr')]
    for i, p in ints:
        x = p['lean']
        lo, hi = p['bounds']
        if lo < 0:
            add(f'0 ≤ {x}', lambda v, i=i: v[i] >= 0, 3.0)
            add(f'{x} ≠ 0', lambda v, i=i: v[i] != 0, 3.2)
        add(f'1 ≤ {x}', lambda v, i=i: v[i] >= 1, 3.1)
        for c in sorted(set(consts) | {8, 16, 32, 64}):
            if c < hi:
                add(f'{x} < {c}', lambda v, i=i, c=c: v[i] < c, 2.0)
        for mg in ladder(lo, hi):
            r = 1 + math.log2(mg + 1) / 100
            if lo < 0:
                add(f'-{mg} ≤ {x} ∧ {x} ≤ {mg}', lambda v, i=i, mg=mg: -mg <= v[i] <= mg, r)
                add(f'-{mg} ≤ {x}', lambda v, i=i, mg=mg: -mg <= v[i], r + 0.005)
            add(f'{x} ≤ {mg}', lambda v, i=i, mg=mg: v[i] <= mg, r + 0.005)
    for (i, p), (j, q) in itertools.permutations(ints, 2):
        add(f'{p["lean"]} ≤ {q["lean"]}', lambda v, i=i, j=j: v[i] <= v[j], 2.5)
        add(f'{p["lean"]} < {q["lean"]}', lambda v, i=i, j=j: v[i] < v[j], 2.4)
    for j, q in seqs:
        s = q['lean']
        lo, hi = q['elem']
        add(f'0 < {s}.length', lambda v, j=j: len(v[j]) > 0, 2.6)
        for i, p in ints:
            x = p['lean']
            add(f'{x} < ({s}.length : Int)', lambda v, i=i, j=j: v[i] < len(v[j]), 2.6)
            add(f'{x} ≤ ({s}.length : Int)', lambda v, i=i, j=j: v[i] <= len(v[j]), 2.7)
        if lo < 0:
            add(f'∀ e ∈ {s}, 0 ≤ e', lambda v, j=j: all(e >= 0 for e in v[j]), 2.0)
        add(f'∀ e ∈ {s}, e ≠ 0', lambda v, j=j: all(e != 0 for e in v[j]), 1.9)
        for mg in ladder(lo, hi):
            r = 1 + math.log2(mg + 1) / 100
            if lo < 0:
                add(f'∀ e ∈ {s}, -{mg} ≤ e ∧ e ≤ {mg}',
                    lambda v, j=j, mg=mg: all(-mg <= e <= mg for e in v[j]), r)
            else:
                add(f'∀ e ∈ {s}, e ≤ {mg}', lambda v, j=j, mg=mg: all(e <= mg for e in v[j]), r)
    return out


def holds(atom, vals):
    try:
        return bool(atom['f'](vals))
    except (TypeError, IndexError):
        return False


def learn(atoms, ub_vals, safe_vals):
    """Greedy cover: repeatedly take the fact excluding the most remaining UB
    inputs per safe input it excludes (ties: fewer safe inputs excluded, then
    rank). None if some UB input satisfies every fact."""
    chosen = []
    rest = list(ub_vals)
    while rest:
        best = None
        for at in atoms:
            if at in chosen:
                continue
            kills = sum(1 for u in rest if not holds(at, u))
            if not kills:
                continue
            cost = sum(1 for s in safe_vals if not holds(at, s))
            score = (kills / (1 + cost), -cost, at['rank'])
            if best is None or score > best[0]:
                best = (score, at)
        if best is None:
            return None
        chosen.append(best[1])
        rest = [u for u in rest if holds(best[1], u)]
    return chosen


def tighten(pre, atoms):
    """The same facts with every magnitude bound one step lower on the ladder
    (a magnitude fact's text has the form `... ≤ M` with M = 2^k - 1)."""
    out = []
    changed = False
    for at in pre:
        nums = [int(n) for n in re.findall(r'\b(\d+)\b', at['text'])]
        mg = max(nums) if nums else 0
        if mg >= 7 and (mg + 1) & mg == 0:
            # one ladder step: try 2^(k-1)-1, 2^(k-2)-1, ... until a fact of the same shape exists
            lower = []
            for d in range(1, 12):
                m2 = (mg + 1) // 2 ** d - 1
                lower = [b for b in atoms if b['text'] == at['text'].replace(str(mg), str(m2))]
                if lower:
                    break
            if lower:
                out.append(lower[0])
                changed = True
                continue
        out.append(at)
    return out if changed else None


# ---------------------------------------------------------------- candidates

def value(v):
    """Trace text -> int (integers, iterator positions, pointees) or list."""
    if v.startswith('@') or v.startswith('*'):
        v = v[1:]
    if v.startswith('['):
        inner = v[1:-1]
        try:
            return [int(x) for x in inner.split(',')] if inner else []
        except ValueError:
            return None
    try:
        return int(v)
    except ValueError:
        return None


def head_env(rec, vals, slots, params):
    """Values of the invariant's atoms at one loop head."""
    env = {}
    for s in slots:
        if s['trace'] in rec:
            v = value(rec[s['trace']])
            if isinstance(v, int):
                env[s['atom']] = v
    for k, p in enumerate(params):
        if 'atom' in p and isinstance(vals[k], int):
            env[p['atom']] = vals[k]
        if 'atom_len' in p and isinstance(vals[k], list):
            env[p['atom_len']] = len(vals[k])
    return env


def candidates(envs, atoms, scales=(), slot_atoms=()):
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
    # accumulators: |s| ≤ M * x for the magnitude bounds M of the precondition
    for s in slot_atoms:
        for x in atoms:
            if x == s:
                continue
            for mg in scales:
                add(f'{s} ≤ {mg} * {x}', lambda e, s=s, x=x, mg=mg: e[s] <= mg * e[x])
                add(f'-({mg} * {x}) ≤ {s}', lambda e, s=s, x=x, mg=mg: -(mg * e[x]) <= e[s])
    # drop facts implied by stronger kept ones (x < y implies x ≤ y)
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


# ---------------------------------------------------------------- main

def prepare(a):
    """Scan and Lean module for the CIR file when not given."""
    base = re.sub(r'[^A-Za-z0-9_]', '_', os.path.basename(a.cir).rsplit('.', 1)[0])
    if not a.scan:
        a.scan = os.path.join(a.out, 'scan', base + '.json')
        if not os.path.exists(a.scan):
            os.makedirs(os.path.dirname(a.scan), exist_ok=True)
            rc, out, _ = run_cmd(RUN + [f'{CIRLEAN}/.lake/build/bin/cirscan', '--json', a.cir], 600)
            with open(a.scan, 'w') as fh:
                fh.write(out)
    if not a.gen_lean:
        a.module = 'Gen.' + base
        a.gen_lean = os.path.join(a.out, 'gen', base + '.lean')
        if not os.path.exists(a.gen_lean):
            os.makedirs(os.path.dirname(a.gen_lean), exist_ok=True)
            run_cmd(RUN + [f'{CIRLEAN}/.lake/build/bin/cir2lean', a.cir, a.module, a.gen_lean], 600)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--cir', required=True)
    ap.add_argument('--sym', required=True)
    ap.add_argument('--scan')
    ap.add_argument('--gen-lean')
    ap.add_argument('--module')
    ap.add_argument('--json', help='also write the report here')
    ap.add_argument('--runs', type=int, default=80)
    ap.add_argument('--cegis', type=int, default=3, help='rounds of sampling under the precondition')
    ap.add_argument('--rounds', type=int, default=8, help='Houdini rounds per variant')
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    report = {'sym': a.sym, 'status': 'error', 'log': [], 'tool': 'cirinv_v4'}
    t_start = time.time()

    def finish(**kw):
        report.update(kw)
        report['secs'] = round(time.time() - t_start)
        for k in [k for k, v in report.items() if v is None]:
            del report[k]
        if report['status'] == 'ub_witness' and 'precondition' in report:
            # tried, but no proof under it
            report['precondition_tried'] = report.pop('precondition')
        text = json.dumps(report)
        if a.json:
            with open(a.json, 'w') as fh:
                fh.write(text + '\n')
        print(text, flush=True)
        sys.exit(0)

    prepare(a)
    func = None
    with open(a.scan) as fh:
        for line in fh:
            line = line.strip()
            if line:
                j = json.loads(line)
                if j['sym'] == a.sym:
                    func = j
    if func is None:
        finish(status='error', reason='function not found in scan')
    report['name'] = func['name']
    olean_dir = os.path.join(a.out, 'olean')
    base = re.sub(r'[^A-Za-z0-9_]', '_', a.sym)[:80]
    work = os.path.join(a.out, 'work')
    os.makedirs(work, exist_ok=True)
    recursive = func['sym'] in func.get('callees', [])
    arrays = frozenset()
    try:
        _, _, _, params = stub_parts(func, {})
    except Unsupported as e:
        finish(status='unsupported', reason=str(e))
    with open(a.cir) as fh:
        consts = program_consts(fh.read(), a.sym)
    rng = random.Random(1)

    def sample(params, n, pred=None, tries=40):
        seen, out = set(), []
        for _ in range(n * tries):
            v = gen_input(params, consts, rng)
            key = json.dumps(v)
            if key in seen or (pred and not pred(v)):
                continue
            seen.add(key)
            out.append(v)
            if len(out) >= n:
                break
        return out

    # 1. executions
    runs = run_traces(a.cir, a.sym, params, sample(params, a.runs))
    # pointers that the function indexes: model them as arrays and start again
    ptr_ix = [k for k, p in enumerate(params) if p['kind'] == 'ptrint']
    if ptr_ix and any('pointer arithmetic out of bounds' in r['result'] for r in runs):
        arrays = frozenset(ptr_ix)
        _, _, _, params = stub_parts(func, {}, arrays)
        runs = run_traces(a.cir, a.sym, params, sample(params, a.runs))
        report['arrays'] = [params[k]['lean'] for k in ptr_ix]
    report['runs'] = len(runs)

    # 2. precondition
    pre = []
    atoms = atoms_for(params, consts)
    ub_runs = [r for r in runs if is_ub(r)]
    first_ub = ub_runs[:5]
    if ub_runs:
        for rnd in range(a.cegis + 1):
            chosen = learn(atoms, [r['vals'] for r in ub_runs], [r['vals'] for r in runs if is_safe(r)])
            if chosen is None:
                finish(status='ub_witness', recursive=recursive or None, runs=len(runs),
                       ub_inputs=[{'input': r['input'], 'result': r['result']} for r in first_ub],
                       reason='no precondition of the supported shapes excludes the UB inputs')
            pre = chosen
            if rnd == a.cegis:
                break
            more = run_traces(a.cir, a.sym, params,
                              sample(params, 40, pred=lambda v: all(holds(at, v) for at in pre)))
            runs += more
            new_ub = [r for r in more if is_ub(r)]
            report['log'].append({'step': f'cegis {rnd}', 'pre': [at['text'] for at in pre],
                                  'runs': len(more), 'new_ub': len(new_ub)})
            if not new_ub:
                break
            ub_runs += new_ub
        inside = [r for r in runs if is_safe(r) and all(holds(at, r['vals']) for at in pre)]
        inside_ub = [r for r in runs if is_ub(r) and all(holds(at, r['vals']) for at in pre)]
        if inside_ub:
            finish(status='ub_witness', recursive=recursive or None, runs=len(runs),
                   ub_inputs=[{'input': r['input'], 'result': r['result']} for r in inside_ub[:5]],
                   precondition=[at['text'] for at in pre],
                   reason='UB inputs satisfy the best precondition found')
        if len(inside) < 3:
            # a precondition that (almost) no input satisfies proves nothing useful
            finish(status='ub_witness', recursive=recursive or None, runs=len(runs),
                   ub_inputs=[{'input': r['input'], 'result': r['result']} for r in first_ub],
                   precondition=[at['text'] for at in pre], reason='precondition excludes almost every input')
        report['precondition'] = [at['text'] for at in pre]
        report['ub_inputs'] = [{'input': r['input'], 'result': r['result']} for r in first_ub]
    report['runs'] = len(runs)
    if recursive:
        finish(status='recursive', reason='recursive functions need a specification (induction)')
    if not compile_gen(a.gen_lean, a.module, olean_dir):
        finish(status='error', reason='cir2lean module does not compile')

    # 3. probe: symbolic execution up to the loops
    loops = func['loops']
    pre_text = [at['text'] for at in pre]
    probe_tac = ['cir_start', 'cir_vcg']
    if loops == 0:
        probe_tac.append('cir_houdini_report')
    else:
        probe_tac += ['all_goals (try cir_loop_info)', 'all_goals sorry']
    path = os.path.join(work, f'{base}_probe.lean')
    with open(path, 'w') as fh:
        fh.write(theorem(a.module, func, {}, probe_tac, arrays, pre_text))
    msgs, dt = run_lean(path, olean_dir)
    report['log'].append({'step': 'probe', 'secs': round(dt, 1)})
    errs = [m for k, m in msgs if k == 'error']
    if errs:
        finish(status='error', reason='probe: ' + errs[0][:300])
    others = [m[len('@OTHER '):] for k, m in msgs if m.startswith('@OTHER')]
    done = 'proved_under' if pre else 'proved'
    if loops == 0:
        if others and pre:
            # tighter magnitude bounds, at most twice
            for _ in range(2):
                tp = tighten(pre, atoms)
                if not tp:
                    break
                pre = tp
                pre_text = [at['text'] for at in pre]
                with open(path, 'w') as fh:
                    fh.write(theorem(a.module, func, {}, probe_tac, arrays, pre_text))
                msgs, dt = run_lean(path, olean_dir)
                report['log'].append({'step': 'probe (tighter)', 'pre': pre_text, 'secs': round(dt, 1)})
                others = [m[len('@OTHER '):] for k, m in msgs if m.startswith('@OTHER')]
                if not others and not [m for k, m in msgs if k == 'error']:
                    break
            report['precondition'] = pre_text
        if others:
            finish(status='ub_witness' if pre else 'goals_left', other_goals=others[:10])
        tac = ['cir_start', 'cir_vcg']
        proof = os.path.join(a.out, f'{base}_proof.lean')
        with open(proof, 'w') as fh:
            fh.write(theorem(a.module, func, {}, tac, arrays, pre_text))
        msgs, dt = run_lean(proof, olean_dir)
        bad = [m for k, m in msgs if k == 'error' or 'sorry' in m]
        report['log'].append({'step': 'certificate', 'secs': round(dt, 1), 'errors': len(bad)})
        finish(status=done if not bad else 'certificate_failed', proof=proof,
               reason=(bad[0][:300] if bad else None))
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
    if rename:
        # the precondition speaks about the parameters' initial values
        for at in atoms:
            t = at['text']
            for old, new in rename.items():
                t = re.sub(r'(?<![\w.])' + re.escape(old) + r'(?![\w])', new, t)
            at['text'] = t
        pre_text = [at['text'] for at in pre]
        if pre:
            report['precondition'] = pre_text
    _, _, _, params = stub_parts(func, rename, arrays)
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
        if p['kind'] in ('int', 'ptrint'):
            p['atom'] = f'({p["lean"]} : Int)'
        elif p['kind'] in ('vec', 'arr'):
            p['atom_len'] = f'(({p["lean"]}.length : Nat) : Int)'
    if not binders:
        finish(status='no_loop_variables', other_goals=others[:10])
    inv_atoms = [s['atom'] for s in slots] + [p['atom'] for p in params if 'atom' in p] + \
                [p['atom_len'] for p in params if 'atom_len' in p]
    lam = 'fun ' + ' '.join(binders) + ' =>'
    final = None
    for attempt in range(3):
        ok_runs = [r for r in runs if is_safe(r) and r['heads'] and all(holds(at, r['vals']) for at in pre)]
        runs_envs = [[head_env(rec, r['vals'], slots, params) for rec in r['heads']] for r in ok_runs]
        envs = [e for es in runs_envs for e in es]
        scales = sorted({int(n) for at in pre for n in re.findall(r'\b(\d+)\b', at['text'])
                         if int(n) >= 7 and (int(n) + 1) & int(n) == 0})[:2]
        cands = candidates(envs, inv_atoms, scales, [s['atom'] for s in slots])
        vars_ = variants(runs_envs, inv_atoms)
        report['trace_heads'] = len(envs)
        report['candidates0'] = len(cands)
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
                    fh.write(theorem(a.module, func, rename, tac, arrays, pre_text))
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
        if final and not final[2]:
            break
        # goals left: tighter magnitude bounds in the precondition, then again
        tp = tighten(pre, atoms) if pre else None
        if not tp:
            break
        pre = tp
        pre_text = [at['text'] for at in pre]
        report['precondition'] = pre_text
    if final is None:
        finish(status='ub_witness' if pre else 'houdini_failed')
    var, cur, others = final
    inv = ' ∧ '.join(cur) or 'True'
    report['invariant'] = inv
    report['variant'] = var
    report['cir_loop'] = f'cir_loop ({lam} {inv}) ({lam} {var})'
    if others:
        finish(status='ub_witness' if pre else 'goals_left', other_goals=others[:10])
    # the certificate: the same proof without candidate markers or sorry
    tac = ['cir_start', 'cir_vcg', f'all_goals (first | {report["cir_loop"]} | skip)', 'all_goals cir_vcg']
    proof = os.path.join(a.out, f'{base}_proof.lean')
    with open(proof, 'w') as fh:
        fh.write(theorem(a.module, func, rename, tac, arrays, pre_text))
    msgs, dt = run_lean(proof, olean_dir)
    bad = [m for k, m in msgs if k == 'error' or 'sorry' in m]
    report['log'].append({'step': 'certificate', 'secs': round(dt, 1), 'errors': len(bad)})
    finish(status=done if not bad else 'certificate_failed', proof=proof,
           reason=(bad[0][:300] if bad else None))


if __name__ == '__main__':
    main()

"""Automatic proof attempts on an emitted coverage module (`--coverage --emit-lean`).

For every function of the module whose IR has a loop (`for`, `for … of`, `while`, `do … while`)
or an array callback (`reduce`, `map`, `filter`, `some`, `every`, `find…`, `forEach`, `sort`,
`flatMap`, `Array.from` with a function, `Map`/`Set` `forEach`), write the attempt

    theorem auto_f (I : Impl) (w : World TT) <arguments> <hypotheses> :
        JS.Returns (callFun I program fRef <arguments>) w := by
      ts_auto

Arguments of array, `Map`, `Set` and dictionary type are references to allocated cells
(`hw : w.heap.get? (.arr T, a) = some c`, `hn : a < w.next`, and `hs : c.size < 2 ^ 32` for
arrays); an object argument (e.g. `this` of a method) is an allocated cell whose fields are all
initialised, and its array/`Map`/`Set`/dictionary fields are allocated cells too. Other arguments
are arbitrary values.

usage: python3 -I tools/public/attempts.py MODULE.lean OUTDIR [--per-file N] [--heartbeats H] [--exclude A_auto.json]
    [--select-prefix P] [--statement Returns|NoPanic|NoFault] [--only f,g,…]
  (--exclude: skip the functions, by source name and signature, attempted in another run;
   --select-prefix: attempt only the functions whose name starts with P, e.g. the cb_ wrappers,
   when the code they reach has a loop or a callback; --statement: the contract of
   StrictTS/Proof/Contract.lean to attempt (files and JSON get the suffix _nopanic / _nofault);
   --only: these functions (Lean base names) only)
  writes OUTDIR/<Module>_auto_<k>.lean (each importing the module) and OUTDIR/<Module>_auto.json
  (one entry per attempt: function, file, line range, IR features).
"""
import json
import os
import re
import sys


def match_close(s, i, open_ch, close_ch):
    """Index of the bracket closing the one at s[i]."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] == open_ch:
            depth += 1
        elif s[j] == close_ch:
            depth -= 1
            if depth == 0:
                return j
    raise ValueError(f'unbalanced {open_ch} in {s!r}')


def split_top(s, sep):
    """Split s at `sep` characters outside parentheses, brackets and string literals."""
    out, depth, cur, instr = [], 0, '', False
    for ch in s:
        if instr:
            cur += ch
            if ch == '"':
                instr = False
            continue
        if ch == '"':
            instr = True
        elif ch in '([':
            depth += 1
        elif ch in ')]':
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur)
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [x.strip() for x in out if x.strip()]


def strip_parens(t):
    t = t.strip()
    while t.startswith('(') and match_close(t, 0, '(', ')') == len(t) - 1:
        t = t[1:-1].strip()
    return t


def parse_ty(t):
    """('arr', elem) | ('map', k, v) | ('set', elem) | ('dict', elem) | ('obj', name) | ('other', t)."""
    u = strip_parens(t)
    head, _, rest = u.partition(' ')
    args = split_top(rest, ' ')
    if head == '.arr' and len(args) == 1:
        return ('arr', args[0])
    if head == '.map' and len(args) == 2:
        return ('map', args[0], args[1])
    if head == '.set' and len(args) == 1:
        return ('set', args[0])
    if head == '.dict' and len(args) == 1:
        return ('dict', args[0])
    if head == '.obj' and len(args) == 1 and args[0].startswith('"'):
        return ('obj', args[0][1:-1])
    return ('other', t.strip())


LOOPS = ['forLoop', 'forOf', 'forOfMap', 'forOfSet', 'forOfStr', 'while', 'doWhile']
CALLBACKS = ['arrReduce', 'arrReduceRight', 'arrMap', 'arrFilter', 'arrSome', 'arrEvery', 'arrFind',
             'arrFindIndex', 'arrFindLast', 'arrFindLastIndex', 'arrForEach', 'arrSort', 'arrFlatMap',
             'arrFromFn', 'mapForEach', 'setForEach']


def features(body):
    loops = sorted({k for k in LOOPS if re.search(r'\(\.' + k + r'[ \n]', body)})
    cbs = sorted({k for k in CALLBACKS if re.search(r'\.builtin \(\.' + k + r'[ \n)]', body)})
    return loops, cbs


def static_facts(body, args):
    """IR facts used to classify the attempts: explicit throws, callback parameters, the bound of
    each counted `for` loop (exactly `i < xs.length`, exactly `i < constant`, other), and what
    loop bodies contain (nested loops, return/break, allocation, writes, calls)."""
    bounds = []
    for m in re.finditer(r'\(\.forLoop ', body):
        i = m.end()
        cond = body[i:match_close(body, i, '(', ')') + 1] if body[i] == '(' else body[i:i + 80]
        if re.fullmatch(r'\(\.prim \(\.numCmp \.lt\) args\[var! \d+, \.builtin \(\.arrLength [^\[\]]*\) args\[var! \d+\]\]\)', cond):
            bounds.append('array length')
        elif re.fullmatch(r'\(\.prim \(\.numCmp \.lt\) args\[var! \d+, \.lit \(\.num [^()]*\)\]\)', cond):
            bounds.append('constant')
        else:
            bounds.append('other')
    spans = []
    for m in re.finditer(r'\(\.(' + '|'.join(LOOPS) + r')[ \n]', body):
        spans.append(body[m.start():match_close(body, m.start(), '(', ')') + 1])
    inner = lambda pat: any(re.search(pat, sp) for sp in spans)
    loop_re = r'\(\.(' + '|'.join(LOOPS) + r')[ \n]'
    writes = r'\.setField|\.builtin \(\.(arrSet|arrPush|arrPop|arrShift|arrUnshift|arrSplice|arrSetLength|mapSet|mapDelete|setAdd|setDelete|dictSet|dictDelete)[ )]'
    return {'throws': '(.throw ' in body, 'callback_param': any('.fn ' in a for a in args),
            'loops_count': len(spans), 'for_bounds': bounds,
            'nested_loop': any(len(re.findall(loop_re, sp)) > 1 for sp in spans),
            'loop_exit': inner(r'\(\.(ret|brk) '),
            'loop_alloc': inner(r'\.newObj|_newRef»|\.builtin \(\.(arrOf|mapNew|setNew|dictNew|arrSlice|arrConcat|arrCopy|arrMap|arrFilter)[ )]'),
            'loop_writes': max([len(re.findall(writes, sp)) for sp in spans] or [0]),
            'loop_call': inner(r'\.call «'),
            'uses_dyn': '.dyn' in body or any('.dyn' in a for a in args)}


def parse_module(text):
    ns = re.search(r'^namespace (\S+)', text, re.M).group(1)
    classes = {}
    for m in re.finditer(r'^abbrev «(.+?)»\.fields : Fields := flds\[(.*)\]$', text, re.M):
        fields = []
        for f in split_top(m.group(2), ','):
            name, _, ty = f.partition(' : ')
            fields.append((name.strip().strip('"'), ty.strip()))
        classes[m.group(1)] = fields
    refs = {}
    for m in re.finditer(r'^def «(.+?)Ref» : FunRef tys\[', text, re.M):
        i = m.end() - 1
        j = match_close(text, i, '[', ']')
        args = split_top(text[i + 1:j], ',')
        rest = text[j + 1:text.index('\n', j)]
        ret = rest[:rest.rindex(' := ')].strip()
        src = re.search(r'⟨\d+, "(.*)"⟩', rest).group(1)
        refs[m.group(1)] = (args, ret, src)
    defs = {}
    for m in re.finditer(r'^def «(.+?)Def» : FunDef TT where\n', text, re.M):
        end = text.find('\n\n', m.end())
        defs[m.group(1)] = text[m.end():end if end >= 0 else len(text)]
    return ns, classes, refs, defs


REF = re.compile(r'\.(arr|obj|map|set|dict|tarr|promise|box|ext)\b')


def has_ref(t):
    """Does a value of type t hold a reference to a heap cell (closures excepted: class A)?"""
    return not strip_parens(t).startswith('.fn') and bool(REF.search(t))


# String lengths: ECMA-262 §6.1.4 bounds every String at 2^53 - 1 code units, the string
# counterpart of `hs : c.size < 2 ^ 32` for arrays (the model's strings are unbounded; without
# the bound, `s1.length === s2.length` compared as doubles does not give equal lengths). One form,
# agreed with the tactic side (autosplit, 2026-10-24): string arguments and string fields of
# object arguments, and the elements of string array cells; strings inside Maps, Sets,
# dictionaries, optionals, unions and records are left unconstrained.
def str_hyps(ty, var, tag, elems=False):
    """The length hypothesis `hl<tag>` of the string `var` (a `Val TT .str`), or with `elems` of
    every element of the array cell `var` (an `Array (Val TT .str)`); [] when `ty` is not `.str`."""
    if strip_parens(ty) != '.str':
        return []
    if elems:
        return [f'(hl{tag} : ∀ x ∈ {var}.toList, x.toStr.length < 2 ^ 53)']
    return [f'(hl{tag} : {var}.toStr.length < 2 ^ 53)']


# Specifications of external functions (library answers fixed by ECMA-262; errors stay allowed):
# a hypothesis for each extern the code reaches, by the name its `.extern` node carries. The
# definitions are on the tactic side (`World.ExtSpec` instances, StrictTS/Proof/Extern.lean),
# so the hypotheses are emitted only on request (`--ext-specs`), for trees that define them.
EXT_SPECS = {
    'String.matchAll': 'w.MatchAllFresh',              # §22.1.3.14: a fresh array of match results
    'RegExpExecArray.get:[]': 'w.MatchElementZero',    # §22.2.7.2: element 0 of a match is a string
}


def ext_hyps(reach):
    """The extern specifications for code `reach` (the IR text of a function and its callees)."""
    out = []
    for k, (name, spec) in enumerate(EXT_SPECS.items()):
        if f'"{name}"' in reach:
            out.append(f'(hext{k} : {spec})')
    return out


def statement(base, args, classes):
    """Binders, hypotheses and argument list of the attempt; notes name the references that the
    statement leaves without a cell ('dangling: …'): reads through them fail in some worlds."""
    binders, hyps, vals = [], [], []
    notes = []

    def cell(kind, tag, i):
        """binders/hyps for one allocated cell; returns its value text."""
        a, c = f'a{tag}', f'c{tag}'
        if kind[0] == 'arr':
            binders.append(f'({a} : Nat) ({c} : Array (Val TT {kind[1]}))')
            hyps.append(f'(hw{tag} : w.heap.get? (.arr {kind[1]}, {a}) = some {c}) (hn{tag} : {a} < w.next) (hs{tag} : {c}.size < 2 ^ 32)')
            hyps.extend(str_hyps(kind[1], c, tag, elems=True))
            return f'(.arr {a})'
        if kind[0] == 'map':
            binders.append(f'({a} : Nat) ({c} : JSMap (Val TT {kind[1]}) (Val TT {kind[2]}))')
            hyps.append(f'(hw{tag} : w.heap.get? (.map {kind[1]} {kind[2]}, {a}) = some {c}) (hn{tag} : {a} < w.next)')
            return f'(.map {a})'
        if kind[0] == 'set':
            binders.append(f'({a} : Nat) ({c} : JSMap (Val TT {kind[1]}) Unit)')
            hyps.append(f'(hw{tag} : w.heap.get? (.set {kind[1]}, {a}) = some {c}) (hn{tag} : {a} < w.next)')
            return f'(.set {a})'
        if kind[0] == 'dict':
            binders.append(f'({a} : Nat) ({c} : JSMap JSStr (Val TT {kind[1]}))')
            hyps.append(f'(hw{tag} : w.heap.get? (.dict {kind[1]}, {a}) = some {c}) (hn{tag} : {a} < w.next)')
            return f'(.dict {a})'
        raise ValueError(kind)

    for i, t in enumerate(args):
        k = parse_ty(t)
        if k[0] in ('arr', 'map', 'set', 'dict'):
            vals.append(cell(k, str(i), i))
            if any(has_ref(x) for x in k[1:]):
                notes.append(f'dangling: elements of argument {i}')
        elif k[0] == 'obj' and k[1] in classes:
            fields = classes[k[1]]
            fvals, field_strs = [], []
            for j, (_, fty) in enumerate(fields):
                fk = parse_ty(fty)
                if fk[0] in ('arr', 'map', 'set', 'dict'):
                    fvals.append(cell(fk, f'{i}_{j}', i))
                    if any(has_ref(x) for x in fk[1:]):
                        notes.append(f'dangling: elements of field {j} of argument {i}')
                else:
                    if has_ref(fty):
                        notes.append(f'dangling: field {j} of argument {i}')
                    binders.append(f'(f{i}_{j} : Val TT {fty})')
                    fvals.append(f'f{i}_{j}')
                    field_strs.extend(str_hyps(fty, f'f{i}_{j}', f'{i}_{j}'))
            content = '.nil'
            for v in reversed(fvals):
                content = f'(.cons (some {v}) {content})'
            ftys = ', '.join(fty for _, fty in fields)
            binders.append(f'(a{i} : Nat)')
            hyps.append(f'(hw{i} : w.heap.get? (.obj "{k[1]}" [{ftys}], a{i}) = some {content}) (hn{i} : a{i} < w.next)')
            hyps.extend(field_strs)
            vals.append(f'(.obj a{i})')
            notes.append(f'object {k[1]}')
        else:
            if has_ref(t):
                notes.append(f'dangling: argument {i}')
            binders.append(f'(v{i} : Val TT {t})')
            hyps.extend(str_hyps(t, f'v{i}', str(i)))
            vals.append(f'v{i}')
    vs = '.nil'
    for v in reversed(vals):
        vs = f'(.cons {v} {vs})'
    return binders, hyps, vs, notes


def main():
    argv = sys.argv[1:]
    per_file, hb = 12, 400000
    if '--per-file' in argv:
        i = argv.index('--per-file'); per_file = int(argv[i + 1]); del argv[i:i + 2]
    if '--heartbeats' in argv:
        i = argv.index('--heartbeats'); hb = int(argv[i + 1]); del argv[i:i + 2]
    stmt = 'Returns'
    if '--statement' in argv:
        i = argv.index('--statement'); stmt = argv[i + 1]; del argv[i:i + 2]
        assert stmt in ('Returns', 'NoPanic', 'NoFault'), stmt
    only = None
    if '--only' in argv:
        i = argv.index('--only'); only = set(argv[i + 1].split(',')); del argv[i:i + 2]
    prefix = None
    if '--select-prefix' in argv:
        i = argv.index('--select-prefix'); prefix = argv[i + 1]; del argv[i:i + 2]
    exclude = set()
    if '--exclude' in argv:
        i = argv.index('--exclude')
        for a in json.load(open(argv[i + 1]))['attempts']:
            exclude.add((a['source'], tuple(a['args']), a['ret']))
        del argv[i:i + 2]
    module, outdir = argv
    text = open(module).read()
    mod = os.path.splitext(os.path.basename(module))[0]
    ns, classes, refs, defs = parse_module(text)
    os.makedirs(outdir, exist_ok=True)
    attempts = []
    for base, body in defs.items():
        if only is not None and base not in only:
            continue
        if prefix is not None:
            # wrappers: attempted when the code they reach (callees, transitively) has a loop or a
            # callback; the IR facts are those of that code
            if not base.startswith(prefix):
                continue
            seen, todo = {base}, [base]
            while todo:
                for c in re.findall(r'«([^»]+)Ref»', defs.get(todo.pop(), '')):
                    if c in defs and c not in seen:
                        seen.add(c); todo.append(c)
            body = '\n'.join(defs[c] for c in sorted(seen))
        loops, cbs = features(body)
        if not loops and not cbs:
            continue
        args, ret, src = refs[base]
        if '.prototype.' in src:
            continue    # the translator's own library code (String.prototype.split), not the project's
        if (src, tuple(args), ret) in exclude:
            continue
        attempts.append({'fn': base, 'source': src, 'args': args, 'ret': ret, 'loops': loops, 'callbacks': cbs,
                         'async': ret.startswith('(.promise'), 'statement': stmt, **static_facts(body, args)})
    entries = []
    sfx = '' if stmt == 'Returns' else f'_{stmt.lower()}'
    for k in range(0, len(attempts), per_file):
        chunk = attempts[k:k + per_file]
        fname = f'{mod}{sfx}_auto_{k // per_file}.lean'
        lines = [f'import {mod}', 'import StrictTS.Proof.Auto', 'set_option maxRecDepth 100000',
                 'open StrictTS StrictTS.Frontend', f'namespace {ns}', '']
        for a in chunk:
            binders, hyps, vs, notes = statement(a['fn'], a['args'], classes)
            name = f'auto{sfx}_{a["fn"]}'
            start = len(lines) + 1
            lines.append(f'set_option maxHeartbeats {hb} in')
            lines.append(f'theorem «{name}» (I : Impl) (w : World TT) {" ".join(binders)}'.rstrip())
            if hyps:
                lines.append(f'    {" ".join(hyps)} :')
            else:
                lines[-1] += ' :'
            lines.append(f'    JS.{stmt} (callFun I program «{a["fn"]}Ref» {vs}) w := by')
            lines.append('  ts_auto')
            end = len(lines)
            lines.append(f'#print axioms «{name}»')
            lines.append('')
            entries.append({**a, 'theorem': name, 'file': fname, 'from': start, 'to': end, 'notes': notes,
                            'dangling': any(n.startswith('dangling') for n in notes)})
        lines.append(f'end {ns}')
        open(os.path.join(outdir, fname), 'w').write('\n'.join(lines) + '\n')
    json.dump({'module': mod, 'namespace': ns, 'heartbeats': hb, 'statement': stmt, 'attempts': entries},
              open(os.path.join(outdir, f'{mod}{sfx}_auto.json'), 'w'), indent=1)
    print(f'{mod}{sfx}: {len(defs)} functions, {len(attempts)} attempts in {(len(attempts) + per_file - 1) // per_file} files')


if __name__ == '__main__':
    main()

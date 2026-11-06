#!/usr/bin/env python3
"""Generate the Lean statement of a COBOL -> Java/Rust modernization theorem (Headline A).

Inputs (all mechanical, none written by a model):
  * veriforch's mapping.json for the program (files in SELECT order, records read INTO / written
    FROM / rewritten FROM, linkage items, clock; Java/Rust names by the style guide's naming rule,
    cross-checked in Lean by `cobol_schema` / `rust_record_vals` against coblean's layout of the IR),
  * the program's IR JSON (coblean's front end output) and the harness's init_mem.hex,
  * coblean's all-input theorem for the program: its name, fuel form (`n + c`) read from its
    source text by regex (--cobol-thm-file).

Output: a Lean file defining the record schemas (`cobol_schema`), the initial storage
(`cobol_mem_hex`), the input relations, the outcome relation `Rel` and `Statement : Prop`; the
proof is a separate file.

Statement shape (Java): for all field values of the input records (valid for their schemas), of
the linkage items, and a clock text, for every fuel `n` above the number of input records, for
every Java state holding the inputs as objects (`JRecAt`) with the classes initialized (for a
class with a static initializer, i.e. static state: its `<clinit>` has run, `ClinitRan`, as the
JVM runs it before the first call of a static method of the class),
  Sim Rel (Call.mk Gen.prog runRef args σ)
      (EquivLean.Cobol.run P env (n + c) (P.initState mem files))
with `mem` the harness storage with the linkage values written at their offsets, `env` the
clock environment (a reading of FUNCTION CURRENT-DATE, `CurrentDate`), `files` the encoded input
records.  A program that sets RETURN-CODE also relates `returnCode` / `return_code` to the value of
the RETURN-CODE item at the end of the COBOL run (`itemValue`).  Options: `--ksds` adds coblean's model
assumption on indexed input files (`KsdsValid`: ascending unique record keys) as hypotheses;
`--domain D` adds the hypothesis `D inputs…`, a hand-written domain (kept in its own module).  `Rel`: the Java `Result` holds the COBOL
DISPLAY lines (CP037 text), the records WRITTEN / REWRITTEN per file (decoded by the FROM
record's schema), and `abended` = the run ended with `CALL 'CEE3ABD'`.  Rust: the same with
slices of structs (`rust_record_vals`), Latin-1 lines and `Equiv`, for fewer than 2^28 input
records in all (Aeneas bounds every `Vec` by `Usize.max`, which may be 2^32 - 1).
"""
import argparse, json, os, re, sys


def camel(n):
    return ''.join(w.capitalize() for w in n.split('-') if w)


def lower_first(s):
    return s[0].lower() + s[1:]


def lean_str(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'


def fuel_of_thm(path, name):
    src = open(path).read()
    i = src.find('theorem ' + name)
    if i < 0:
        sys.exit(f'theorem {name} not found in {path}')
    body = src[i:i + 6000]
    stmt = body[:body.find(':= by')] if ':= by' in body else body
    m = re.search(r'\.run \{[^}]*\} \((\w+) \+ (\d+)\)', stmt)
    if m:
        return m.group(1), int(m.group(2))
    m = re.search(r'\+\s*(\d+)\s*≤\s*\w+', stmt)
    if m:
        return 'n', int(m.group(1))
    sys.exit(f'cannot find the fuel `(n + c)` of {name}')


FV = 'EquivLean.Cobol.Rec.FVal'


def item_size(it):
    """Bytes of an IR data item (one occurrence times OCCURS; REDEFINES children skipped)."""
    kids = [c for c in it.get('children', []) if c.get('redefines') is None]
    if kids:
        n = sum(item_size(c) for c in kids)
    else:
        pic = it.get('pic') or {}
        if 'alnum' in pic:
            n = pic['alnum']['len']
        elif 'num' in pic:
            d = pic['num']['digits']
            u = it.get('usage', 'display')
            if u == 'packed':
                n = d // 2 + 1
            elif u == 'binary':
                n = 2 if d <= 4 else 4 if d <= 9 else 8
            else:
                n = d + (1 if it.get('signSep') else 0)
        else:
            sys.exit(f"item {it.get('name')}: no size rule for {pic}")
    return n * (it.get('occurs') or 1)


def record_size(ir, name):
    for it in ir['data']:
        if it.get('level') == 1 and it.get('name') == name:
            return item_size(it)
    sys.exit(f'no 01-level record {name} in the IR')


def snake(n):
    """The Rust name of a COBOL name (naming rule: the words in lower case, joined by `_`)."""
    return '_'.join(w.lower() for w in n.split('-') if w)


def depth0_find(s, sub, start=0):
    """The first occurrence of `sub` in `s` outside brackets, or -1."""
    d = 0
    for i in range(start, len(s)):
        if s[i] in '([{':
            d += 1
        elif s[i] in ')]}':
            d -= 1
        elif d == 0 and s.startswith(sub, i):
            return i
    return -1


def call_thm(path, name):
    """coblean's per-call theorem `name` of a subprogram, read from its source text: its binder
    groups as written, and the parts of its conclusion `P.run ENV FUEL (STATE) = (SIGNAL, …)`."""
    src = open(path).read()
    m = re.search(r'theorem ' + re.escape(name) + r'\s', src)
    if not m:
        sys.exit(f'theorem {name} not found in {path}')
    k = m.end() - 1
    binders = []
    while True:
        while src[k].isspace():
            k += 1
        if src[k] in '({[':
            j, d = k, 0
            while True:
                if src[j] in '({[':
                    d += 1
                elif src[j] in ')}]':
                    d -= 1
                j += 1
                if d == 0:
                    break
            binders.append(' '.join(src[k:j].split()))
            k = j
        elif src[k] == ':':
            break
        else:
            sys.exit(f'{name}: unexpected text among the binders: {src[k:k + 30]!r}')
    concl = ' '.join(src[k + 1:src.find(':= by', k)].split())
    eq = depth0_find(concl, ' = ')
    run = re.fullmatch(r'(\S+)\.run (\S+) (\d+) (\(.*\))', concl[:eq]) if eq > 0 else None
    if not run:
        sys.exit(f'{name}: the conclusion is not `P.run env fuel (state) = …`')
    sig = re.match(r'\((\.stop \.\w+),', concl[eq + 3:])
    if not sig:
        sys.exit(f'{name}: the conclusion does not end the run with `(.stop …, state)`')
    return binders, run.group(2), int(run.group(3)), run.group(4), sig.group(1)


def unused_to_underscore(binders, later):
    """Binder groups with every name that no later binder or `later` text mentions written `_`
    (the hypothesis names of coblean's theorem; the statement only needs the propositions)."""
    out = []
    for i, b in enumerate(binders):
        inner = b[1:-1]
        c = depth0_find(inner, ' : ')
        rest = ' '.join(binders[i + 1:]) + ' ' + later
        names = [n if re.search(r'(?<![\w.])' + re.escape(n) + r'(?!\w)', rest) else '_'
                 for n in inner[:c].split()]
        out.append(b[0] + ' '.join(names) + inner[c:] + b[-1])
    return out


def gen_subprogram(a, mp):
    """`--subprogram`: the statement of ONE call of a CALLed subprogram, whose storage and files
    persist from call to call (CardDemo's CBSTM03B).  The translation keeps, between calls, a
    state with one struct / object per file (`open`, `recs`, `pos`, `eof`), the FD record areas and
    the FILE STATUS items, and takes the parameter areas (the linkage items) and the environment's
    OPEN outcomes.  The COBOL side is coblean's per-call theorem: its binders and hypotheses (read
    from its source) are the statement's, and its run `P.run env fuel (state)` is the source."""
    prog, jcls = mp['program'], mp['java_class']
    crate = a.rust_crate or mp['rust_crate']
    java = a.lang == 'java'
    files = mp['files']
    if not files or any(not f.get('input') or f.get('open') != ['INPUT'] or f.get('write_from') or
                        f.get('rewrite_from') or f.get('fd_record', f['record']) != f['record']
                        for f in files):
        sys.exit('--subprogram: only files opened INPUT only and read into their FD records')
    linkage = mp.get('linkage') or []
    ir = json.load(open(os.path.join(os.path.dirname(os.path.abspath(a.out)), a.ir_rel)))
    names = {it['id']: it['name'] for it in ir['data'] if it.get('level') == 1 and 'id' in it}
    status = {f['id']: names.get(f['status']) for f in ir['files'] if f.get('status') is not None}
    if any(status.get(f['id']) is None for f in files):
        sys.exit('--subprogram: every file needs a FILE STATUS item (a 01-level group)')
    # files read by key (random or dynamic access): a keyed READ stores the key in the FD record area
    # before the search, so in Java that object must not be one of the file's record objects
    access = {f['id']: f.get('access') for f in ir['files']}
    keyed = [f for f in files if access.get(f['id']) in ('random', 'dynamic')]
    binders, envv, fuel, state, sig = call_thm(a.cobol_thm_file, a.cobol_thm)
    binders = unused_to_underscore(binders, f'{envv} {state}')
    if a.domain:
        # the domain is a premise on the theorem's named binders (its values; unused hypotheses are `_`)
        dargs = [n for b in binders if b[0] in '({'
                 for n in b[1:-1][:depth0_find(b[1:-1], ' : ')].split() if n != '_']
        binders = binders + [f'(_ : {a.domain} {" ".join(dargs)})']
    nf = len(files)
    rec = lambda r: mp['records'][r]['class']
    L = []
    w = L.append
    w('import EquivLean.Bridge.Cobol.Behaves')
    w('import EquivLean.Bridge.Cobol.Sub')
    w('import EquivLean.Bridge.Jimple.Behaves' if java else 'import EquivLean.Bridge.Aeneas.Behaves')
    w('import EquivLean.Bridge.Jimple.CobolRec' if java else 'import EquivLean.Bridge.Aeneas.CobolRec')
    w(f'import {a.cobol_module}')
    w(f'import {a.gen_module}')
    if a.domain_module:
        w(f'import {a.domain_module}')
    w('')
    w('/-!')
    w(f'# {prog} → {"Java" if java else "Rust"}: the generated statement of one call')
    w('')
    w("Generated by `tools/modernize/genstmt.py --subprogram` from veriforch's `mapping.json`, coblean's IR")
    w(f"and coblean's per-call theorem `{a.cobol_thm}`; do not edit.  {prog} is a CALLed subprogram whose")
    w('storage and files persist from one call to the next, so the statement is about one call: for every')
    w("callee state and parameter area allowed by coblean's theorem (its binders and hypotheses, copied from")
    w('its source) and every translation state related to them, the call of the translation and the COBOL')
    w('run correspond, and their results are related in the same way.  The relations, all generated:')
    w('* one per file: the open flag, the records (each decoding to the struct / object field values), the')
    w("  read position and the end-of-file flag of coblean's file state (the last record read, `cur`, is")
    w('  not part of it);')
    w('* `StateRel` (the state kept between calls): the files, the FD record areas and the FILE STATUS')
    w('  items, at their storage offsets;')
    w('* one per parameter area (linkage item): its field values at its storage offsets;')
    w("* `EnvRel`: the environment's outcome of `OPEN INPUT` for each file (none, or a failure status);")
    w('* `Rel`: the call returns (no exception / panic) and the COBOL run ends with GOBACK, in related states.')
    if a.domain:
        w('')
        w(f'The inputs are restricted to the domain `{a.domain}`, written by hand in `{a.domain_module}`')
        w('(the one part of the statement not generated).')
    w('-/')
    w('')
    w('open Cobol EquivLean.Cobol.Rec')
    w('open Jimple EquivLean.Jimple' if java else 'open Aeneas Aeneas.Std')
    w('')
    w(f'namespace {a.namespace}')
    w('')
    schemas = [(f['record'], rec(f['record'])) for f in files]
    schemas += [(status[f['id']], camel(status[f['id']])) for f in files]
    schemas += [(l['record'], rec(l['record'])) for l in linkage]
    seen = set()
    for r, cls in schemas:
        if cls in seen:
            continue
        seen.add(cls)
        w(f'cobol_schema {cls} from {lean_str(a.ir_rel)} record {lean_str(r)}')
        w(f'theorem {lower_first(cls)}_contig : {cls}.Contig := by decide')
        if not java and r in mp['records']:
            w(f'rust_record_vals {cls}.vals : {crate}.{cls} from {lean_str(a.ir_rel)} record {lean_str(r)}')
    for l in linkage:
        cls = rec(l['record'])
        w(f'/-- {l["name"]} starts at the offset of the mapping. -/')
        w(f'theorem {lower_first(cls)}_offset : ({cls}.fields.headD default).desc.off = {l["offset"]} := by decide')
    w('')
    fcls = lambda f: f'{jcls}${camel(f["fd"])}'
    # the relations between a file's translation and coblean's file state
    for f in files:
        cls, fn = rec(f['record']), camel(f['fd'])
        w(f'/-- File {f["fd"]} (file {f["id"]}): the open flag, the records, the read position and the')
        if java:
            w("end-of-file flag of coblean's file state; the records are a Java array of record objects (a JVM")
            w('array has fewer than 2^31 elements). -/')
        else:
            w("end-of-file flag of coblean's file state. -/")
        if java:
            k = lean_str(fcls(f))
            w(f'def {fn}At (σ : Jimple.State) (x : Jimple.Value) (s : FileSt) : Prop :=')
            w('  ∃ o fs b l et xs, x = .ref o ∧ σ.heap o = some (.plain ' + k + ' fs) ∧')
            w(f'    Fields.get fs ({k}, "open") = some (.ofBool b) ∧ s.mode = (if b then some .input else none) ∧')
            w(f'    Fields.get fs ({k}, "recs") = some (.ref l) ∧ σ.heap l = some (.array et xs) ∧')
            w('    xs.length < 2147483648 ∧')
            w(f'    Forall2 (fun x r => ∃ vals, JRecAt {cls} {lean_str(jcls + "$" + cls)} σ x vals ∧ {cls}.Valid vals ∧')
            w(f'      r = {cls}.encode vals) xs s.recs ∧')
            w(f'    s.pos < 2147483648 ∧ Fields.get fs ({k}, "pos") = some (.int (BitVec.ofNat 32 s.pos)) ∧')
            w(f'    Fields.get fs ({k}, "eof") = some (.ofBool s.eof)')
        else:
            w(f'def {fn}Rel (f : {crate}.{fn}) (s : FileSt) : Prop :=')
            w('  s.mode = (if f.«open» then some .input else none) ∧')
            w(f'    (∀ r ∈ f.recs.val, {cls}.Valid ({cls}.vals r)) ∧')
            w(f'    s.recs = f.recs.val.map (fun r => {cls}.encode ({cls}.vals r)) ∧')
            w('    s.pos = f.pos.val ∧ s.eof = f.eof')
        w('')
    # the state kept between calls
    stc = lean_str(f'{jcls}$State')
    if java and keyed:
        w('/-- The record object `x` is not one of the record objects of the file object `y` (of class `k`). -/')
        w('def NotRecOf (σ : Jimple.State) (k : ClassName) (x y : Jimple.Value) : Prop :=')
        w('  ∀ o fs l et xs, y = .ref o → σ.heap o = some (.plain k fs) → Fields.get fs (k, "recs") = some (.ref l) →')
        w('    σ.heap l = some (.array et xs) → x ∉ xs')
        w('')
    w('/-- The state the translation keeps between calls, against the callee\'s COBOL state: the files,')
    if java and keyed:
        w('the FD record areas (field values at their storage offsets) and the FILE STATUS items.  The FD')
        w(f'record areas of the files read by key ({", ".join(f["fd"] for f in keyed)}) are not shared with the file\'s record')
        w('objects (a keyed READ first stores the key in the record area); the translation keeps this, since a')
        w('read stores a fresh copy. -/')
    else:
        w('the FD record areas (field values at their storage offsets) and the FILE STATUS items. -/')
    parts = []
    if java:
        w('def StateAt (σ : Jimple.State) (st : Addr) (cs : Cobol.State) : Prop :=')
        w(f'  ∃ fs, σ.heap st = some (.plain {stc} fs) ∧')
        for f in files:
            parts.append(f'(∃ x s, Fields.get fs ({stc}, {lean_str(f["java_param"])}) = some x ∧ '
                         f'cs.files.lookup {f["id"]} = some s ∧ {camel(f["fd"])}At σ x s)')
        for f in files:
            r, cls = f['record'], rec(f['record'])
            parts.append(f'(∃ x vals, Fields.get fs ({stc}, {lean_str(lower_first(camel(r)))}) = some x ∧ '
                         f'JRecAt {cls} {lean_str(jcls + "$" + cls)} σ x vals ∧\n      {cls}.Valid vals ∧ {cls}.At cs.mem vals)')
        for f in files:
            sn = status[f['id']]
            parts.append(f'(∃ x bs, Fields.get fs ({stc}, {lean_str(lower_first(camel(sn)))}) = some x ∧ '
                         f'JStrAt σ x (cp037Str bs) ∧ {camel(sn)}.BytesAt cs.mem bs)')
        for f in keyed:
            parts.append(f'(∀ x y, Fields.get fs ({stc}, {lean_str(lower_first(camel(f["record"])))}) = some x → '
                         f'Fields.get fs ({stc}, {lean_str(f["java_param"])}) = some y →\n'
                         f'      NotRecOf σ {lean_str(fcls(f))} x y)')
    else:
        w(f'def StateRel (st : {crate}.State) (cs : Cobol.State) : Prop :=')
        for f in files:
            parts.append(f'(∃ s, cs.files.lookup {f["id"]} = some s ∧ {camel(f["fd"])}Rel st.{f["rust_param"]} s)')
        for f in files:
            r, cls = f['record'], rec(f['record'])
            parts.append(f'{cls}.Valid ({cls}.vals st.{snake(r)}) ∧ {cls}.At cs.mem ({cls}.vals st.{snake(r)})')
        for f in files:
            sn = status[f['id']]
            parts.append(f'{camel(sn)}.BytesAt cs.mem (st.{snake(sn)}.val.map (fun u => ebcdicOfLatin1 u.val))')
    w(('    ' if java else '  ') + ' ∧\n    '.join(parts))
    w('')
    # the parameter areas
    for l in linkage:
        cls = rec(l['record'])
        w(f'/-- The parameter area {l["name"]}: its field values at their storage offsets. -/')
        if java:
            w(f'def {cls}At (σ : Jimple.State) (p : Addr) (m : Mem) : Prop :=')
            w(f'  ∃ vals, JRecAt {cls} {lean_str(jcls + "$" + cls)} σ (.ref p) vals ∧ {cls}.Valid vals ∧ {cls}.At m vals')
        else:
            w(f'def {cls}Rel (q : {crate}.{cls}) (m : Mem) : Prop :=')
            w(f'  {cls}.Valid ({cls}.vals q) ∧ {cls}.At m ({cls}.vals q)')
        w('')
    # the environment's OPEN outcomes
    w(f'/-- The OPEN outcomes: element `i` is the status of a failed `OPEN INPUT` of file `i + 1`, or')
    w(f'{"null" if java else "`None`"} when the OPEN succeeds (`Env.openError`).  A failure is a FILE STATUS, which is')
    w('two decimal digits (IBM statuses are 00–99): every failure the environment reports is below 100. -/')
    if java:
        w('def EnvAt (σ : Jimple.State) (oe : Addr) (env : Env) : Prop :=')
        w(f'  ∃ et xs, σ.heap oe = some (.array et xs) ∧ xs.length = {nf} ∧ ∀ i, i < {nf} →')
        w('    (xs.getD i .null = .null ∧ env.openError (i + 1) .input = none) ∨')
        w('    (∃ o c, xs.getD i .null = .ref o ∧ σ.heap o = some (.boxed "java.lang.Integer" (.int (BitVec.ofNat 32 c))) ∧')
        w('      c < 100 ∧ env.openError (i + 1) .input = some c)')
    else:
        w(f'def EnvRel (oe : Std.Array (Option Std.U8) {nf}#usize) (env : Env) : Prop :=')
        w(f'  ∀ i, i < {nf} → (oe.val.getD i none).map (fun c => c.val) = env.openError (i + 1) .input ∧')
        w('    ∀ c, env.openError (i + 1) .input = some c → c < 100')
    w('')
    qs = [f'q{i + 1}' for i in range(len(linkage))]
    if java:
        w('/-- The outcome relation: the call returns normally, the COBOL run ends with GOBACK, and the state')
        w('object and the parameter areas hold the COBOL state at the end of the call. -/')
        w(f'def Rel (st {" ".join(qs)} : Addr) (ot : Out) (os : Signal × Cobol.State) : Prop :=')
        w(f"  ∃ σ', ot = .normal none σ' ∧ os.1 = {sig} ∧ StateAt σ' st os.2" +
          ''.join(f" ∧ {rec(l['record'])}At σ' {q} os.2.mem" for q, l in zip(qs, linkage)))
    else:
        tys = ' × '.join([f'{crate}.State'] + [f'{crate}.{rec(l["record"])}' for l in linkage])
        w('/-- The outcome relation: the call returns (no panic) the new state and parameter areas, the COBOL')
        w('run ends with GOBACK, and the results are related as before the call. -/')
        w(f'def Rel (o : Except Error ({tys})) (os : Signal × Cobol.State) : Prop :=')
        w(f'  ∃ st {" ".join(qs)}, o = .ok ({", ".join(["st"] + qs)}) ∧ os.1 = {sig} ∧ StateRel st os.2' +
          ''.join(f" ∧ {rec(l['record'])}Rel {q} os.2.mem" for q, l in zip(qs, linkage)))
    w('')
    cobol = f'(EquivLean.Cobol.run {a.cobol_prog} {envv} {fuel} {state})'
    w(f'open {a.cobol_prog} in')
    w(f'/-- **{prog} → {"Java" if java else "Rust"}, one call, every input**: the statement. -/')
    w('def Statement : Prop :=')
    w('  ∀ ' + '\n    '.join(binders) + ',')
    if java:
        w(f'  ∀ (σ : Jimple.State) (oe st {" ".join(qs)} : Addr),')
        w(f'    EnvAt σ oe {envv} → StateAt σ st {state} →')
        for q, l in zip(qs, linkage):
            w(f'    {rec(l["record"])}At σ {q} {state}.mem →')
        classes = [jcls, jcls + '$State'] + [fcls(f) for f in files]
        classes += sorted({f'{jcls}${rec(r)}' for r in [f['record'] for f in files] + [l['record'] for l in linkage]})
        if a.jimple_dir and os.path.isdir(a.jimple_dir):
            extra = sorted(f[:-len('.jimple')] for f in os.listdir(a.jimple_dir) if f.endswith('.jimple'))
            classes += [k for k in extra if k not in classes]
        for k in classes:
            jf = os.path.join(a.jimple_dir or '', k + '.jimple')
            if a.jimple_dir and os.path.exists(jf) and '<clinit>' in open(jf).read():
                w(f'    ClinitRan {a.gen_ns}.prog {lean_str(k)} σ →')
            else:
                w(f'    σ.initOf {lean_str(k)} = .done →')
        sig_j = ['java.lang.Integer[]', f'{jcls}$State'] + [f'{jcls}${rec(l["record"])}' for l in linkage]
        ref = f'{a.gen_ns}.{jcls}.«{a.call_fn}({",".join(sig_j)})».ref'
        args = ', '.join(['.ref oe', '.ref st'] + [f'.ref {q}' for q in qs])
        w(f'    Sim (Rel st {" ".join(qs)}) (Call.mk {a.gen_ns}.prog {ref} [{args}] σ)')
        w(f'      {cobol}')
    else:
        sb = ' '.join([f'(oe : Std.Array (Option Std.U8) {nf}#usize)', f'(st : {crate}.State)'] +
                      [f'({q} : {crate}.{rec(l["record"])})' for q, l in zip(qs, linkage)])
        w(f'  ∀ {sb},')
        w(f'    EnvRel oe {envv} → StateRel st {state} →')
        for q, l in zip(qs, linkage):
            w(f'    {rec(l["record"])}Rel {q} {state}.mem →')
        w(f'    Equiv Rel ({crate}.{a.call_fn} {" ".join(["oe", "st"] + qs)})')
        w(f'      {cobol}')
    w('')
    w(f'end {a.namespace}')
    open(a.out, 'w').write('\n'.join(L) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mapping', required=True)
    ap.add_argument('--lang', choices=['java', 'rust'], required=True)
    ap.add_argument('--ir-rel', required=True, help='IR path relative to the output file')
    ap.add_argument('--mem-rel', required=True, help='init_mem.hex path relative to the output file')
    ap.add_argument('--cobol-module', required=True)
    ap.add_argument('--cobol-prog', required=True)
    ap.add_argument('--cobol-thm-file', required=True)
    ap.add_argument('--cobol-thm', required=True)
    ap.add_argument('--gen-module', required=True)
    ap.add_argument('--gen-ns', default='Gen', help="how the statement names the generated Java program's namespace (default `Gen`, i.e. <namespace>.Gen when the statement's namespace is the program's Java namespace; a variant statement in another namespace gives the full name)")
    ap.add_argument('--namespace', required=True)
    ap.add_argument('--jimple-dir', help="the translation's Jimple directory (Java): every class in it gets a class-init hypothesis")
    ap.add_argument('--rust-crate', help='Lean namespace of the Rust crate, if it differs from mapping.json (a crate renamed to avoid a clash)')
    ap.add_argument('--ksds', action='store_true', help="hypothesis `KsdsValid` on every indexed input file (coblean's model assumption: ascending unique record keys, unique alternate keys), for COBOL theorems that need it")
    ap.add_argument('--domain', help='name of a domain predicate on the input values (inputs in SELECT order, then linkage values), defined by hand in --domain-module; a hypothesis of the statement')
    ap.add_argument('--domain-module', help='the module defining --domain')
    ap.add_argument('--subprogram', action='store_true', help="one call of a CALLed subprogram whose storage and files persist between calls (see gen_subprogram); --cobol-thm is coblean's per-call theorem")
    ap.add_argument('--call-fn', default='call', help="--subprogram: the translation's entry point (default `call`)")
    ap.add_argument('-o', '--out', required=True)
    a = ap.parse_args()
    mp = json.load(open(a.mapping))
    if a.subprogram:
        return gen_subprogram(a, mp)
    prog, jcls, crate = mp['program'], mp['java_class'], mp['rust_crate']
    if a.rust_crate:
        crate = a.rust_crate
    java = a.lang == 'java'
    var, c = fuel_of_thm(a.cobol_thm_file, a.cobol_thm)
    rc = bool(mp.get('return_code'))
    rcv = f'(itemValue {a.cobol_prog}.RETURN_CODE {a.cobol_prog}.RETURN_CODE.fmt os.2)'
    inputs = [f for f in mp['files'] if f.get('input')]
    writes = [f for f in mp['files'] if f.get('write_from')]
    rewrites = [f for f in mp['files'] if f.get('rewrite_from')]
    linkage = mp.get('linkage') or []
    clock = bool(mp.get('clock'))
    recs = {}
    for r in ([f['record'] for f in inputs] + [f['write_from'] for f in writes if not f.get('varying')] +
              [f['rewrite_from'] for f in rewrites] + [l['record'] for l in linkage]):
        if r not in recs:
            recs[r] = mp['records'][r]['class']
    # records with items under OCCURS: the Java translations hold each such item in an array
    # (`JRecOccAt`, Bridge/Jimple/CobolOcc.lean); one level only
    occ = {r for r in recs if any('occurs' in fd for fd in mp['records'][r]['fields'])}
    if any(not isinstance(fd['occurs'], int) for r in occ for fd in mp['records'][r]['fields']
           if 'occurs' in fd):
        sys.exit('nested OCCURS are not in this template yet')

    def jrec(r):
        return 'JRecOccAt' if r in occ else 'JRecAt'
    L = []
    w = L.append
    w('import EquivLean.Bridge.Cobol.Behaves')
    w('import EquivLean.Bridge.Jimple.Behaves' if java else 'import EquivLean.Bridge.Aeneas.Behaves')
    w('import EquivLean.Bridge.Jimple.CobolRec' if java else 'import EquivLean.Bridge.Aeneas.CobolRec')
    if java and occ:
        w('import EquivLean.Bridge.Jimple.CobolOcc')
    if java and a.jimple_dir and any('<clinit>' in open(os.path.join(a.jimple_dir, f)).read()
                                     for f in os.listdir(a.jimple_dir) if f.endswith('.jimple')):
        w('import EquivLean.Bridge.Jimple.Init')
    w(f'import {a.cobol_module}')
    w(f'import {a.gen_module}')
    if a.domain_module:
        w(f'import {a.domain_module}')
    w('')
    w('/-!')
    w(f'# {prog} → {"Java" if java else "Rust"}: the generated statement')
    w('')
    w("Generated by `tools/modernize/genstmt.py` from veriforch's `mapping.json`, coblean's IR and the")
    w("harness's initial storage; do not edit.  The record schemas come from coblean's layout of the IR")
    w("(`cobol_schema`); the COBOL run is coblean's semantics of the unmodified program, with the fuel")
    w(f"form of coblean's theorem `{a.cobol_thm}`.")
    if a.ksds:
        w('')
        w("Each indexed input file carries `KsdsValid` (coblean's model assumption for indexed files:")
        w('ascending unique record keys, unique alternate keys without DUPLICATES).')
    if a.domain:
        w('')
        w(f'The inputs are restricted to the domain `{a.domain}`, written by hand in `{a.domain_module}`')
        w('(the one part of the statement not generated).')
    w('-/')
    w('')
    w('open Cobol EquivLean.Cobol.Rec')
    w('open Jimple EquivLean.Jimple' if java else 'open Aeneas Aeneas.Std')
    w('')
    w(f'namespace {a.namespace}')
    w('')
    for r, cls in recs.items():
        w(f'cobol_schema {cls} from {lean_str(a.ir_rel)} record {lean_str(r)}')
        w(f'theorem {lower_first(cls)}_contig : {cls}.Contig := by decide')
        if java and r in occ:
            # every occurrence has one index (`jFieldOccAt` is `False` for nested ones)
            w(f'theorem {lower_first(cls)}_occ1 : ∀ f ∈ {cls}.fields, f.idx.length ≤ 1 := by decide')
        if not java:
            w(f'rust_record_vals {cls}.vals : {crate}.{cls} from {lean_str(a.ir_rel)} record {lean_str(r)}')
    w('')
    mem_path = os.path.join(os.path.dirname(os.path.abspath(a.out)), a.mem_rel)
    mem_bytes = bytes.fromhex(''.join(open(mem_path).read().split()))
    if len(mem_bytes) <= 8192:
        w(f'cobol_mem_hex initMem from {lean_str(a.mem_rel)}')
        w('set_option maxRecDepth 10000 in')
        w(f'theorem initMem_size : initMem.size = Program.memSize {a.cobol_prog} := by')
        w(f'  rw [{a.cobol_prog}.memSize_eq]; rfl')
    else:
        runs = []
        i = 0
        while i < len(mem_bytes):
            j = i + 1
            while j < len(mem_bytes) and mem_bytes[j] == mem_bytes[i]:
                j += 1
            runs.append((j - i, mem_bytes[i]))
            i = j
        items = [f'({k}, {b})' for k, b in runs]
        w('/-- Run-length encoding of `init_mem.hex` (`(count, byte)` pairs). -/')
        w('def initMemRuns : List (Nat × UInt8) :=')
        for idx in range(0, len(items), 8):
            pfx = '  [ ' if idx == 0 else '    '
            sfx = ' ]' if idx + 8 >= len(items) else ','
            w(pfx + ', '.join(items[idx:idx + 8]) + sfx)
        w('')
        w('def initMem : Mem := ⟨(initMemRuns.flatMap (fun p => List.replicate p.1 p.2)).toArray⟩')
        w(f'theorem initMem_size : initMem.size = Program.memSize {a.cobol_prog} := by')
        w('  have h : ∀ l : List (Nat × UInt8),')
        w('      (l.flatMap (fun p => List.replicate p.1 p.2)).length = (l.map Prod.fst).sum := by')
        w('    intro l; induction l with')
        w('    | nil => rfl')
        w('    | cons p ls ih => simp [List.flatMap_cons, List.length_replicate, ih]')
        w(f'  rw [{a.cobol_prog}.memSize_eq]')
        w(f'  show (initMemRuns.flatMap (fun p => List.replicate p.1 p.2)).length = {len(mem_bytes)}')
        w('  rw [h]')
        w('  decide')
    if java:
        sig = [f'{jcls}${mp["records"][f["record"]]["class"]}[]' for f in inputs]
        sig += [f'{jcls}${mp["records"][l["record"]]["class"]}' for l in linkage]
        if clock:
            sig.append('java.lang.String')
        w('')
        w(f'/-- The entry point `{jcls}.run`. -/')
        w(f'abbrev runRef : MethodRef := {a.gen_ns}.{jcls}.«run({",".join(sig)})».ref')
    w('')
    params = []
    for f in inputs:
        cls = recs[f['record']]
        fname = camel(f['fd'])
        if java:
            w(f'/-- Input file {f["fd"]}: a Java array of `{jcls}${cls}` objects holding the records (a JVM')
            w('array has fewer than 2^31 elements). -/')
            w(f'def {fname}At (σ : Jimple.State) (a : Addr) (vals : List (List {FV})) : Prop :=')
            w('  ∃ et xs, σ.heap a = some (.array et xs) ∧ xs.length < 2147483648 ∧')
            w(f'    Forall2 ({jrec(f["record"])} {cls} {lean_str(jcls + "$" + cls)} σ) xs vals')
        else:
            w(f'/-- Input file {f["fd"]}: a Rust slice of `{cls}` structs holding the records. -/')
            w(f'def {fname}Of (s : Slice {crate}.{cls}) (vals : List (List {FV})) : Prop :=')
            w(f'  s.val.map {cls}.vals = vals')
        params.append((f, cls, fname))
        w('')
    outs = [(f, 'writes') for f in writes] + [(f, 'rewrites') for f in rewrites]
    disp_expr = '((displays os.2).drop 11)' if mp.get('exclude_display_patterns') else '(displays os.2)'
    if java:
        res = jcls + '$Result'
        if outs:
            w('/-- The outcome relation: the Java `Result` holds the COBOL DISPLAY lines (CP037 text), the')
            w("records written / rewritten per file (each decoding to the Java object's field values), and")
            w("`abended` = 1 exactly when the COBOL run ends with `CALL 'CEE3ABD'`. -/")
        else:
            w('/-- The outcome relation: `Result.displays` holds the COBOL DISPLAY lines (CP037 text), in order;')
            w("`Result.abended` is 1 exactly when the COBOL run ends with `CALL 'CEE3ABD'`. -/")
        w('def Rel (ot : Out) (os : Signal × Cobol.State) : Prop :=')
        w("  ∃ σ' res fs l k xs mods, ot = .normal (some (.ref res)) σ' ∧")
        w(f"    σ'.heap res = some (.plain {lean_str(res)} fs) ∧")
        w(f"    Fields.get fs ({lean_str(res)}, \"displays\") = some (.ref l) ∧ σ'.heap l = some (.list k xs mods) ∧")
        w(f"    Forall2 (JLineAt σ') xs {disp_expr} ∧")
        for f, kind in outs:
            rec = f['write_from'] if kind == 'writes' else f['rewrite_from']
            cls = recs.get(rec)
            jf = f['java_writes'] if kind == 'writes' else f['java_rewrites']
            w(f"    (∃ lw kw ws mw, Fields.get fs ({lean_str(res)}, {lean_str(jf)}) = some (.ref lw) ∧")
            w("      σ'.heap lw = some (.list kw ws mw) ∧")
            if f.get('varying'):
                # a variable-length record: its text, as a DISPLAY line
                w(f"      Forall2 (JLineAt σ') ws ({kind} {f['id']} os.2)) ∧")
            else:
                w(f"      Forall2 (fun x rec => ∃ vals, {jrec(rec)} {cls} {lean_str(jcls + '$' + cls)} σ' x vals ∧")
                w(f"        {cls}.decode rec = some vals) ws ({kind} {f['id']} os.2)) ∧")
        if rc:
            w(f"    Fields.get fs ({lean_str(res)}, \"returnCode\") = some (.int (BitVec.ofInt 32 {rcv})) ∧")
        w(f"    Fields.get fs ({lean_str(res)}, \"abended\") = some (.int (if abended os.1 then 1 else 0))")
    else:
        if outs:
            w('/-- The outcome relation: `Output.displays` holds the Latin-1 bytes of the CP037 text of the COBOL')
            w("DISPLAY lines; the records written / rewritten per file decode to the structs' field values;")
            w("`Output.abended` is true exactly when the COBOL run ends with `CALL 'CEE3ABD'`. -/")
        else:
            w('/-- The outcome relation: `Output.displays` holds the Latin-1 bytes of the CP037 text of the COBOL')
            w('DISPLAY lines, in order; `Output.abended` is true exactly when the COBOL run ends with')
            w("`CALL 'CEE3ABD'`. -/")
        w(f'def Rel (o : Except Error {crate}.Output) (os : Signal × Cobol.State) : Prop :=')
        w('  ∃ out, o = .ok out ∧')
        w(f'    out.displays.val.map (fun l => l.val.map (·.val)) = {disp_expr}.map rustLine ∧')
        for f, kind in outs:
            rec = f['write_from'] if kind == 'writes' else f['rewrite_from']
            cls = recs.get(rec)
            rf = f['rust_writes'] if kind == 'writes' else f['rust_rewrites']
            if f.get('varying'):
                # a variable-length record: its text (Latin-1 bytes), as a DISPLAY line
                w(f'    ({kind} {f["id"]} os.2).map rustLine = out.{rf}.val.map (fun l => l.val.map (·.val)) ∧')
            else:
                w(f'    ({kind} {f["id"]} os.2).map {cls}.decode = out.{rf}.val.map (fun x => some ({cls}.vals x)) ∧')
        if rc:
            w(f'    out.return_code.val = {rcv} ∧')
        w('    out.abended = abended os.1')
    w('')
    vs = [f'vals{i + 1}' for i in range(len(params))]
    ls = [f'link{i + 1}' for i in range(len(linkage))]
    w(f'/-- **{prog} → {"Java" if java else "Rust"}, every input**: the statement. -/')
    w('def Statement : Prop :=')
    binders = ' '.join(f'({v} : List (List {FV}))' for v in vs)
    w(f'  ∀ {binders},')
    for v, (f, cls, fname) in zip(vs, params):
        w(f'    (∀ v ∈ {v}, {cls}.Valid v) →')
    for lv, l in zip(ls, linkage):
        w(f'    ∀ ({lv} : List {FV}), {recs[l["record"]]}.Valid {lv} →')
    if clock:
        w('    ∀ (clk : List UInt8), CurrentDate clk →')
    if a.ksds:
        ir = json.load(open(os.path.join(os.path.dirname(os.path.abspath(a.out)), a.ir_rel)))
        org = {f['id']: f['org'] for f in ir['files']}
        for v, (f, cls, fname) in zip(vs, params):
            if org.get(f['id']) == 'indexed':
                w(f'    KsdsValid {a.cobol_prog} {f["id"]} ({v}.map {cls}.encode) →')
    if a.domain:
        w(f'    {a.domain} {" ".join(vs + ls)} →')
    lens = ' + '.join(f'{v}.length' for v in vs) if vs else '0'
    if not java and vs:
        # Rust: the outputs are Vecs, whose lengths Aeneas bounds by Usize.max, which may be
        # 2^32 - 1 (a 32-bit target); bound the number of input records so that 16 output lines per
        # record still fit (any real input is far below)
        w(f'    {lens} < 2 ^ 28 →')
    if java and vs:
        # Java: collections are int-indexed (`List.size()` is an int, 2^31 - 1 at most; a JVM cannot
        # hold more); bound the number of input records so that 16 list elements per record stay
        # below 2^31 (found by javatrn: CBTRN02C's category list searched through `size()`)
        w(f'    {lens} < 2 ^ 27 →')
    w(f'    ∀ {var} : Nat, {lens} < {var} →')
    mem = 'initMem'
    for lv, l in zip(ls, linkage):
        mem = f'(Cobol.Mem.write {mem} {l["offset"]} ({recs[l["record"]]}.encode {lv}))'
    calls = bool(mp.get('externals'))
    env_parts = []
    if clock:
        env_parts.append('clock := fun _ => clk')
    if calls:
        # CALLed subprograms (e.g. CardDemo's COBDATFT): coblean's models of them
        env_parts.append(f'call := Cobol.Ext.cardDemoCalls {a.cobol_prog}.cfg')
    if mp.get('addrspace'):
        env_parts.append('addrSpace := Cobol.Stm.asp')
    env = '{ ' + ', '.join(env_parts) + ' }' if env_parts else '{}'
    ir = json.load(open(os.path.join(os.path.dirname(os.path.abspath(a.out)), a.ir_rel)))

    def contents(v, f, cls):
        # READ … INTO a record shorter than the file's: the file record is the INTO record padded
        # with spaces to the FD record's length (as the harness writes it; the program never reads
        # the rest)
        fd, rec = f.get('fd_record'), f['record']
        pad = record_size(ir, fd) - record_size(ir, rec) if fd and fd != rec else 0
        if pad > 0:
            return f'({f["id"]}, {v}.map (fun r => {cls}.encode r ++ List.replicate {pad} 64))'
        return f'({f["id"]}, {v}.map {cls}.encode)'
    files = ', '.join(contents(v, f, cls) for v, (f, cls, fname) in zip(vs, params))
    cobol = (f'(EquivLean.Cobol.run {a.cobol_prog} {env} ({var} + {c})\n'
             f'        ({a.cobol_prog}.initState {mem} [{files}]))')
    if java:
        objs = [f'(a{i + 1} : Addr)' for i in range(len(params))] + [f'(p{i + 1} : Addr)' for i in range(len(linkage))]
        if clock:
            objs.append('(cs : Addr)')
        w('    ∀ (σ : Jimple.State) ' + ' '.join(objs) + ',')
        for i, (v, (f, cls, fname)) in enumerate(zip(vs, params)):
            w(f'    {fname}At σ a{i + 1} {v} →')
        for i, (lv, l) in enumerate(zip(ls, linkage)):
            cls = recs[l['record']]
            w(f'    {jrec(l["record"])} {cls} {lean_str(jcls + "$" + cls)} σ (.ref p{i + 1}) {lv} →')
        if clock:
            w('    JStrAt σ (.ref cs) (cp037Str clk) →')
        classes = [jcls, jcls + '$Result'] + sorted({jcls + '$' + cls for cls in
                   [recs[f['record']] for f in inputs]})
        if a.jimple_dir:
            extra = sorted(f[:-len('.jimple')] for f in os.listdir(a.jimple_dir) if f.endswith('.jimple'))
            classes += [k for k in extra if k not in classes]
        # a class with a static initializer (static tables, e.g. CBTRN02C's CP037): its
        # `<clinit>` has run (`ClinitRan`, as the JVM does before the first static call); any
        # other class has no static state, so it counts as initialized
        def has_clinit(k):
            if not a.jimple_dir:
                return False
            f = os.path.join(a.jimple_dir, k + '.jimple')
            return os.path.exists(f) and '<clinit>' in open(f).read()
        for k in classes:
            if has_clinit(k):
                w(f'    ClinitRan {a.gen_ns}.prog {lean_str(k)} σ →')
            else:
                w(f'    σ.initOf {lean_str(k)} = .done →')
        args = [f'.ref a{i + 1}' for i in range(len(params))] + [f'.ref p{i + 1}' for i in range(len(linkage))]
        if clock:
            args.append('.ref cs')
        w(f'    Sim Rel (Call.mk {a.gen_ns}.prog runRef [{", ".join(args)}] σ)')
        w(f'      {cobol}')
    else:
        sb = [f'(s{i + 1} : Slice {crate}.{cls})' for i, (f, cls, fname) in enumerate(params)]
        sb += [f'(q{i + 1} : {crate}.{recs[l["record"]]})' for i, l in enumerate(linkage)]
        if clock:
            sb.append('(rclk : Std.Array Std.U8 21#usize)')
        w('    ∀ ' + ' '.join(sb) + ',')
        for i, (v, (f, cls, fname)) in enumerate(zip(vs, params)):
            w(f'    {fname}Of s{i + 1} {v} →')
        for i, (lv, l) in enumerate(zip(ls, linkage)):
            w(f'    {recs[l["record"]]}.vals q{i + 1} = {lv} →')
        if clock:
            w('    rclk.val.map (·.val) = rustLine clk →')
        args = [f's{i + 1}' for i in range(len(params))] + [f'q{i + 1}' for i in range(len(linkage))]
        if clock:
            args.append('rclk')
        w(f'    Equiv Rel ({crate}.run {" ".join(args)})')
        w(f'      {cobol}')
    w('')
    w(f'end {a.namespace}')
    open(a.out, 'w').write('\n'.join(L) + '\n')


if __name__ == '__main__':
    main()

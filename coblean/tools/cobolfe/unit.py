"""Link the programs of one compilation unit into one surface IR (IBM Enterprise COBOL 6.4 rules).

A unit is one source file: a sequence of separately compiled programs (a batch, each but the last ended
by END PROGRAM) and the programs they contain. The first program is the one the unit is extracted as
(`--main` / `--sub`); the others are linked into it as `tools/cobolfe/link.py` links a called program:
their data items and files follow (item ids and file numbers are already unique in the unit), their
paragraphs follow a `GOBACK` barrier with names prefixed `%NAME::`, and their `EXIT PROGRAM` becomes
`GOBACK`. What the rules add:

* CALL resolution (LR, Conventions for program-names): a directly contained program, then a COMMON
  program directly contained in a program that contains the caller (unless the caller is in it), then a
  separately compiled program of the unit; any other name is outside the unit (`call` as before, linked
  later by link.py or supplied by the environment). `CALL identifier` compares the identifier with the
  name of every program the caller can call, as a nonnumeric relation (trailing spaces do not count); no
  match is outside the unit. A recursive CALL (of the first program, the caller or a program containing
  it) is unsupported, and so is a CALL of an active program, found at run time: a hidden flag per
  callable program is '1' from its CALL to its return.
* ON EXCEPTION / ON OVERFLOW / NOT ON EXCEPTION: a program of the unit is always available, so after
  the return the NOT ON EXCEPTION statements run; outside the unit availability is not modelled
  (`callDyn`, unsupported unless link.py links the program).
* BY REFERENCE is copy-in/copy-out (`callLocal`), which is the same storage only when nothing else names
  the arguments' storage while the called program runs: overlapping arguments, arguments in GLOBAL or
  EXTERNAL storage that the called program (or a program it calls, or a GLOBAL declarative that can run
  meanwhile) names, and LINKAGE arguments when those name any GLOBAL or EXTERNAL storage, are unsupported.
  The same item passed twice is one storage: a variant of the called program names the second
  parameter through a hidden REDEFINES of the first (`variant`).
* INITIAL called programs and CANCEL: the program and the programs it contains are put in their initial
  state by MOVEs from hidden copies of their WORKING-STORAGE records with the same VALUE clauses
  (`init_stmts`); not when a file of theirs may be open. A CANCEL of a program outside the unit is left
  to link.py (`cancel`).
* EXTERNAL records: every later description of the same record name in the unit becomes a REDEFINES
  of the first (one storage per run unit); the records must have the same length.
* RETURN-CODE: one item per separately compiled program (implicitly GLOBAL in its outermost program);
  after a CALL of another separately compiled program of the unit, the caller's is set to the called
  program's (LR, RETURN-CODE).
* USE declaratives: the semantics selects among all declaratives of the linked program (`Sem.useProc?`:
  file-specific first, then mode-specific); IBM selects by the program of the I/O statement (own
  file-specific, own mode-specific, then the GLOBAL ones of each containing program outward). An I/O
  statement for which the two selections can differ, for any open mode, is unsupported.
"""
import copy

from datadiv import CondEntry, Entry, item_size

MODES = (None, "INPUT", "OUTPUT", "I-O", "EXTEND")
IO_STMTS = ("fopen", "fclose", "fread", "fwrite", "frewrite", "fdelete", "fstart", "read", "write", "fcloseOpt",
            "fopenRev")


def walk_entries(es):
    for e in es:
        yield e
        yield from walk_entries(e.children)


def unsup(what):
    return {"unsupported": {"what": what}}


def prefix_stmts(node, pre, ctor=None):
    """A called program's statements: the paragraph and section names of its PERFORM and GO TO
    statements prefixed (the targets of `callLocal` already name the unit's paragraphs), and its
    EXIT PROGRAM as GOBACK (link.py: the linked program is a main program, where the semantics
    ignores EXIT PROGRAM)."""
    if isinstance(node, dict):
        out = {}
        for k, v in node.items():
            if k in ("first", "last", "target") and ctor in ("perform", "goTo") and isinstance(v, str):
                out[k] = pre + v
            elif k == "targets" and ctor == "goToDep":
                out[k] = [pre + t for t in v]
            else:
                out[k] = prefix_stmts(v, pre, k if isinstance(v, dict) else ctor)
        return out
    if isinstance(node, list):
        return ["goback" if v == "exitProgram" else prefix_stmts(v, pre, ctor) for v in node]
    return node


class Linker:
    def __init__(self, unit):
        self.unit = unit
        self.progs = unit.programs
        self.main = self.progs[0]
        names = [p.name for p in self.progs]
        self.prefix = {}
        for p in self.progs[1:]:
            n = p.name if names.count(p.name) == 1 else f"{p.outermost().name}.{p.name}"
            self.prefix[p] = f"%{n}::"
        self.prefix[self.main] = ""
        self.entries = {}       # item id -> Entry (data items, also of every program)
        self.owner = {}         # item id -> program
        for p in self.progs:
            for e in walk_entries(p.dd.records):
                self.entries[e.id] = e
                self.owner[e.id] = p
            for c in p.dd.by_name.values():
                for x in c:
                    if isinstance(x, CondEntry):
                        self.entries[x.id] = x
                        self.owner[x.id] = p
        self.files = {}         # file id -> (File, program)
        for p in self.progs:
            for f in p.files.values():
                self.files[f.id] = (f, p)

    # ------------------------------------------------------------------ CALL resolution
    def resolve(self, caller, name):
        """("prog", t) | ("recursive", t) | ("case", t) | ("outside", None) for CALL name in caller."""
        root = caller.outermost()
        tree = [p for p in self.progs if p.outermost() is root and p.name == name]
        if tree:
            t = tree[0]
            if t is caller or t in caller.ancestors() or t is self.main:
                return ("recursive", t)
            if t.parent is caller or (t.common and t.parent in caller.ancestors()):
                return ("prog", t)
        outs = [p for p in self.progs if p.parent is None and p.name == name]
        if outs:
            # the unit's first program runs as long as any other does: calling it is recursive
            t = outs[0]
            return ("recursive", t) if t is root or t is self.main else ("prog", t)
        if any(p.name.upper() == name.upper() for p in self.progs):
            return ("case", None)
        return ("outside", None)

    def callable_from(self, caller):
        """(name, result) for every program name of the unit that a CALL in caller reaches."""
        out = []
        for n in dict.fromkeys(p.name for p in self.progs):
            r = self.resolve(caller, n)
            if r[0] in ("prog", "recursive"):
                out.append((n, r))
        return out

    def entry_para(self, t):
        return self.prefix[t] + (t.paras[0]["name"] or "ENTRY") if t.paras else None

    # ------------------------------------------------------------------ storage relations
    def record(self, e):
        return e.root()

    def storage_group(self, rec):
        """Records sharing storage: level-01 REDEFINES chains (FD records redefine the first), and an
        EXTERNAL record's descriptions in all programs (key: the record name)."""
        r = rec
        while r.redefines is not None:
            r = r.redefines
        if r.is_external:
            return ("ext", r.name)
        return ("rec", r.id)

    def group_of_item(self, iid):
        e = self.entries.get(iid)
        if e is None:
            return None
        if isinstance(e, CondEntry):
            e = e.parent
        return self.storage_group(self.record(e))

    def refs(self, p, paras=None):
        """Storage groups that program p names in its statements (data references, condition names,
        record areas of the files of its I/O statements)."""
        acc = set()

        def add(iid):
            g = self.group_of_item(iid)
            if g is not None:
                acc.add(g)

        def go(j):
            if isinstance(j, dict):
                if isinstance(j.get("item"), int):
                    add(j["item"])
                for k, v in j.items():
                    if k in ("cond88", "setTrue") and isinstance(v, dict) and isinstance(v.get("id"), int):
                        add(v["id"])
                    elif k in IO_STMTS and isinstance(v, dict) and isinstance(v.get("file"), int):
                        f = self.files.get(v["file"])
                        if f is not None:
                            for r in f[0].records:
                                acc.add(self.storage_group(r))
                    go(v)
            elif isinstance(j, list):
                for v in j:
                    go(v)
        go(p.paras if paras is None else paras)
        return acc

    def is_shared(self, g):
        """Storage that programs other than its own can name: GLOBAL or EXTERNAL records."""
        if g[0] == "ext":
            return True
        e = self.entries[g[1]]
        return e.is_global or (e.file_obj is not None and e.file_obj.is_global)

    def path(self, e):
        return list(reversed([e] + e.ancestors()))

    def may_overlap(self, ra, rb):
        ea, eb = self.entries[ra["item"]], self.entries[rb["item"]]
        if self.storage_group(self.record(ea)) != self.storage_group(self.record(eb)):
            return False
        if self.record(ea) is not self.record(eb):
            return True
        pa, pb = self.path(ea), self.path(eb)
        k = 0
        while k < min(len(pa), len(pb)) and pa[k] is pb[k]:
            k += 1
        if k == len(pa) and k == len(pb):        # the same item
            sa, sb = ra["subs"], rb["subs"]
            if sa != sb and all("lit" in s for s in sa + sb):
                return False                     # different occurrences
            if sa == sb and ra["refStart"] is not None and rb["refStart"] is not None and \
                    all(x is not None and "lit" in x for x in (ra["refStart"], ra["refLen"],
                                                               rb["refStart"], rb["refLen"])):
                a0, a1 = ra["refStart"]["lit"]["n"], ra["refStart"]["lit"]["n"] + ra["refLen"]["lit"]["n"]
                b0, b1 = rb["refStart"]["lit"]["n"], rb["refStart"]["lit"]["n"] + rb["refLen"]["lit"]["n"]
                return a0 < b1 and b0 < a1
            return True
        if k == len(pa) or k == len(pb):         # one contains the other
            return True
        ca, cb = pa[k], pb[k]                    # different children of a common group

        def base(x):
            while x.redefines is not None:
                x = x.redefines
            return x
        return base(ca) is base(cb)

    def reach(self, t):
        """t and the programs of the unit it can call, transitively."""
        seen, todo = [], [t]
        while todo:
            q = todo.pop()
            if q in seen:
                continue
            seen.append(q)
            for c in q.calls:
                if c["prog"] is not None:
                    r = self.resolve(q, c["prog"])
                    if r[0] == "prog":
                        todo.append(r[1])
                elif c["target"] is not None:
                    todo.extend(r[1] for _, r in self.callable_from(q) if r[0] == "prog")
        return seen

    def named_while_running(self, caller, t):
        """Storage groups named by programs that can run while t is active (called by `caller`): t,
        the programs it calls, and the programs whose GLOBAL declaratives can run for their I/O
        statements. The caller and the programs containing it are active, so they do not run again
        (a CALL of an active program is an unsupported recursive CALL, `call_stmts`); their GLOBAL
        storage is named by the programs they contain, and their declaratives count."""
        active = [caller] + caller.ancestors()
        progs = [q for q in self.reach(t) if q not in active]
        acc = set()
        for q in progs:
            acc |= self.refs(q)
        if any(self.has_io(q) for q in progs):
            for a in dict.fromkeys(a for q in progs for a in q.ancestors() if a.use_global):
                acc |= self.refs(a, self.declarative_paras(a))
        return acc

    @staticmethod
    def has_io(p):
        def go(j):
            if isinstance(j, dict):
                return any(k in IO_STMTS for k in j) or any(go(v) for v in j.values())
            if isinstance(j, list):
                return any(go(v) for v in j)
            return False
        return go(p.paras)

    @staticmethod
    def declarative_paras(a):
        """The paragraphs a's declaratives can run: their sections and, transitively, the paragraphs
        and sections their PERFORM statements name; every paragraph of a once a GO TO or a PERFORM
        ... THRU is met (control could then pass anywhere)."""
        names = {}
        for q in a.paras:
            names.setdefault(q["name"], []).append(q)
            if q.get("sect"):
                names.setdefault(q["sect"], []).append(q)
        todo = [q for q in a.paras if q.get("sect") in {u["sect"] for u in a.use}]
        seen, anywhere = [], [False]
        while todo and not anywhere[0]:
            q = todo.pop()
            if any(q is s for s in seen):
                continue
            seen.append(q)

            def go(j, ctor=None):
                if isinstance(j, dict):
                    for k, v in j.items():
                        if k in ("goTo", "goToDep") or (k == "perform" and isinstance(v, dict) and v.get("last")):
                            anywhere[0] = True
                        elif k == "first" and ctor == "perform" and isinstance(v, str):
                            todo.extend(names.get(v, []))
                        else:
                            go(v, k if isinstance(v, dict) else ctor)
                elif isinstance(j, list):
                    for v in j:
                        go(v, ctor)
            go(q["sentences"])
        return a.paras if anywhere[0] else seen

    def alias_problem(self, caller, t, args):
        """Why copy-in/copy-out of `args` may differ from BY REFERENCE for a CALL of t, or None."""
        for i, a in enumerate(args):
            for b in args[i + 1:]:
                if self.may_overlap(a, b):
                    return "arguments that share storage (BY REFERENCE)"
        if not args:
            return None
        named = self.named_while_running(caller, t)
        groups = [self.storage_group(self.record(self.entries[a["item"]])) for a in args]
        for g in groups:
            if g in named:
                return "an argument the called program also names"
        linkage = [a for a in args if self.record(self.entries[a["item"]]).section == "linkage"]
        if linkage and (any(self.is_shared(g) for g in named) or any(self.is_shared(g) for g in groups)):
            return "a LINKAGE argument, GLOBAL/EXTERNAL storage named"
        return None

    # ------------------------------------------------------------------ statements
    def rc_item(self, p):
        e = p.outermost().dd.by_name.get("RETURN-CODE")
        return e[0] if e else None

    def call_stmts(self, caller, c):
        args = c["args"]
        on_exc, not_exc = c["onExc"], c["notOnExc"] or []

        def local(t, cond_name=None):
            params = [e.id for e in t.using]
            what = f"CALL {cond_name or c['prog']}"
            if len(args) != len(params):
                return [unsup(f"{what} (line {c['line']}): {len(args)} arguments for {len(params)} parameters")]
            # the same item passed twice BY REFERENCE: both parameters are one storage (IBM: "the
            # corresponding data item in the calling program occupies the same storage area as the
            # data item in the called program"); a variant of the called program names the second
            # through a REDEFINES of the first, and only the first is copied in and out
            dups = {j: next(i for i in range(j) if args[i] == args[j]) for j in range(len(args))
                    if any(args[i] == args[j] for i in range(j))}
            entry = self.entry_para(t)
            if dups:
                why = self.variant_problem(t, dups)
                if why is not None:
                    return [unsup(f"{what} (line {c['line']}): {why}")]
                entry = self.variant(t, dups)
            cargs = [a for k, a in enumerate(args) if k not in dups]
            cparams = [p for k, p in enumerate(params) if k not in dups]
            why = self.alias_problem(caller, t, cargs)
            if why is not None:
                return [unsup(f"{what} (line {c['line']}): {why}")]
            ref = lambda i: {"item": i, "subs": [], "refStart": None, "refLen": None}  # noqa: E731
            lit = lambda s: {"lit": {"l": {"str": {"s": s}}}}  # noqa: E731
            act = ref(self.active[t].id)
            init = []
            if t.initial:
                # IBM: an INITIAL program and the programs it contains start in their initial state
                # every time it is called
                init = self.init_stmts(t)
                if init is None:
                    return [unsup(f"{what} (line {c['line']}): an INITIAL program whose files may be open")]
            # the program is active from the CALL to its return: a CALL of an active program is
            # recursive (IBM: only RECURSIVE programs, which contain no programs, may be)
            out = init + [{"move": {"src": lit("1"), "dsts": [act]}},
                   {"callLocal": {"para": entry,
                                  "binds": [[copy.deepcopy(a), ref(p)] for a, p in zip(cargs, cparams)]}},
                   {"move": {"src": lit("0"), "dsts": [copy.deepcopy(act)]}}]
            rc_t, rc_c = self.rc_item(t), self.rc_item(caller)
            if t.outermost() is not caller.outermost() and rc_t is not None and rc_c is not None:
                # the caller's RETURN-CODE is set to the called program's (LR, RETURN-CODE)
                out.append({"move": {"src": {"ref": {"r": ref(rc_t.id)}}, "dsts": [ref(rc_c.id)]}})
            return [{"ite": {"c": {"rel": {"op": "=", "a": {"ref": {"r": copy.deepcopy(act)}}, "b": lit("1")}},
                             "t": [unsup(f"{what} (line {c['line']}): a recursive CALL")],
                             "e": out + copy.deepcopy(not_exc)}}]

        if c["prog"] is not None:
            kind, t = self.resolve(caller, c["prog"])
            if kind == "prog":
                if not t.paras:
                    return [unsup(f"CALL {c['prog']} (line {c['line']}): the program has no PROCEDURE DIVISION")]
                return local(t)
            if kind == "recursive":
                return [unsup(f"CALL {c['prog']} (line {c['line']}): a recursive CALL")]
            if kind == "case":
                return [unsup(f"CALL {c['prog']} (line {c['line']}): the name matches a program of the unit "
                              f"only in letter case")]
            if c["onExc"] is None and c["notOnExc"] is None:
                return [{"call": {"prog": c["prog"], "args": args}}]
            return [{"callDyn": {"prog": c["prog"], "target": None, "args": args, "onExc": on_exc,
                                 "notOnExc": not_exc}}]
        # CALL identifier
        stmt = [{"callDyn": {"prog": None, "target": c["target"], "args": args, "onExc": on_exc,
                             "notOnExc": not_exc}}]
        for n, (kind, t) in reversed(self.callable_from(caller)):
            if kind == "prog":
                branch = local(t, n) if t.paras else \
                    [unsup(f"CALL {n} (line {c['line']}): the program has no PROCEDURE DIVISION")]
            else:
                branch = [unsup(f"CALL {n} (line {c['line']}): a recursive CALL")]
            stmt = [{"ite": {"c": {"rel": {"op": "=", "a": {"ref": {"r": copy.deepcopy(c["target"])}},
                                           "b": {"lit": {"l": {"str": {"s": n}}}}}},
                             "t": branch, "e": stmt}}]
        return stmt

    # ------------------------------------------------------------------ initial state
    def subtree(self, t):
        return [p for p in self.progs if p is t or t in p.ancestors()]

    @staticmethod
    def eligible(q, e):
        """A record of q that its initial state sets: WORKING-STORAGE, not EXTERNAL (LR, CANCEL: "The
        contents of data items in external data records ... are not changed"), not a REDEFINES (its
        storage is the redefined record's), not a switch (one per run unit), and RETURN-CODE only in a
        separately compiled program (special registers are initialized after a cancel; a contained
        program uses its outermost program's)."""
        return e.section in ("working", "working-storage") and not e.is_external and e.redefines is None \
            and not e.name.startswith(("%UPSI-", "%SWITCH-", "%ACTIVE ", "%INIT ")) \
            and (e.name != "RETURN-CODE" or q.parent is None)

    def clone_entry(self, e, parent=None, ids=None):
        """A copy of record e with its VALUE clauses (a hidden record whose initial contents are e's)."""
        ids = {} if ids is None else ids
        c = Entry(self.main.fresh(), e.level if parent is not None else 1,
                  e.name if parent is not None else f"%INIT {e.name}", parent, e.tok, e.section)
        ids[e.id] = c
        for a in ("pic", "cat", "pic_text", "ae", "pointer", "just", "bwz", "sync", "usage_kw", "sign",
                  "occurs", "value"):
            setattr(c, a, getattr(e, a))
        if parent is not None and e.redefines is not None:
            c.redefines = ids[e.redefines.id]
        c.children = [self.clone_entry(k, c, ids) for k in e.children]
        return c

    def variant_problem(self, t, dups):
        """Why a duplicate-argument variant of t (parameter j named through parameter i) would not be
        exact, or None."""
        if t.use:
            return "the same argument twice, and the called program has declaratives"

        def walk(e):
            yield e.id
            for k in e.children:
                yield from walk(k)
        for j, i in dups.items():
            pj, pi = t.using[j], t.using[i]
            mine = set(walk(pj)) | set(walk(pi))
            if any(a["item"] in mine for c in t.calls for a in c["args"]):
                return "the same argument twice, passed on by the called program"
            if item_size(pj) != item_size(pi):
                return "the same argument twice for parameters of different lengths"
            if pj.is_global or pj.redefines is not None or \
                    any(e.redefines is pj for e in t.dd.records):
                return "the same argument twice for a GLOBAL or redefined parameter"
        return None

    def clone_alias(self, e, base, parent=None, ids=None, conds=None, objs=None):
        """A copy of record e (parameter j) as a REDEFINES of base (parameter i), with its condition
        names; ids / conds: original id -> copy id."""
        objs = {} if objs is None else objs
        c = Entry(self.main.fresh(), e.level if parent is not None else 1,
                  e.name if parent is not None else f"%ALIAS {e.name}", parent, e.tok, e.section)
        ids[e.id], objs[e.id] = c.id, c
        for a in ("pic", "cat", "pic_text", "ae", "pointer", "just", "bwz", "sync", "usage_kw", "sign",
                  "occurs"):
            setattr(c, a, getattr(e, a))
        if parent is None:
            c.redefines = base
        elif e.redefines is not None:
            c.redefines = objs[e.redefines.id]
        for k in e.conds:
            ck = CondEntry(self.main.fresh(), k.name, c, k.tok)
            ck.values, ck.false_value = k.values, k.false_value
            c.conds.append(ck)
            conds[k.id] = ck.id
        c.children = [self.clone_alias(k, base, c, ids, conds, objs) for k in e.children]
        return c

    def variant(self, t, dups):
        """The entry paragraph of t's variant for duplicate arguments `dups` (parameter j -> i): its
        paragraphs are t's with every reference to parameter j's items made to the items of a copy of
        parameter j that REDEFINES parameter i (built in link(), once t's statements are resolved)."""
        key = (t, tuple(sorted(dups.items())))
        if key not in self.variants:
            pre = f"%V{len(self.variants) + 1}:{t.name}::"
            ids, conds, copies = {}, {}, []
            for j, i in sorted(dups.items()):
                copies.append(self.clone_alias(t.using[j], t.using[i], ids=ids, conds=conds))
            self.variants[key] = {"t": t, "prefix": pre, "ids": ids, "conds": conds, "copies": copies}
        v = self.variants[key]
        return v["prefix"] + (t.paras[0]["name"] or "ENTRY")

    @staticmethod
    def substitute(node, ids, conds, ctor=None):
        if isinstance(node, dict):
            out = {}
            for k, v in node.items():
                if k == "item" and isinstance(v, int):
                    out[k] = ids.get(v, v)
                elif k == "id" and ctor in ("cond88", "setTrue") and isinstance(v, int):
                    out[k] = conds.get(v, v)
                elif k == "key" and ctor in ("fread", "fstart") and isinstance(v, int):
                    out[k] = ids.get(v, v)
                else:
                    out[k] = Linker.substitute(v, ids, conds, k if isinstance(v, dict) else ctor)
            return out
        if isinstance(node, list):
            return [Linker.substitute(v, ids, conds, ctor) for v in node]
        return node

    def init_stmts(self, t):
        """MOVEs that put t and the programs it contains in their initial state (LR, PROGRAM-ID:
        WORKING-STORAGE items get their VALUE, files are not open, PERFORM and altered GO TO
        states are reset), or None when that is not exact: a file of theirs may be open (closing it
        is not expressible). Each record gets the bytes of a hidden copy with the same VALUE
        clauses, so items without VALUE get the copy's initial contents (IBM: undefined)."""
        sub = self.subtree(t)
        own = {f.id for q in sub for f in q.files.values()}

        def opens(j):
            if isinstance(j, dict):
                o = j.get("fopen")
                if isinstance(o, dict) and o.get("file") in own:
                    return True
                o = j.get("fopenRev")    # OPEN INPUT ... REVERSED
                if isinstance(o, dict) and o.get("file") in own:
                    return True
                return any(opens(v) for v in j.values())
            if isinstance(j, list):
                return any(opens(v) for v in j)
            return False
        if any(opens(q.paras) for q in sub):
            return None
        whole = lambda i: {"item": i, "subs": [], "refStart": {"lit": {"n": 1}}, "refLen": None}  # noqa: E731
        out = []
        for q in sub:
            for e in q.dd.records:
                if self.eligible(q, e):
                    if e.id not in self.clones:
                        self.clones[e.id] = (q, self.clone_entry(e))
                    c = self.clones[e.id][1]
                    out.append({"move": {"src": {"ref": {"r": whole(c.id)}}, "dsts": [whole(e.id)]}})
        return out

    def cancel_stmts(self, caller, c):
        """CANCEL of a program of the unit: its initial state (unless it is active); of another
        program: `cancel`, left to link.py."""
        what = lambda n: f"CANCEL {n} (line {c['line']})"  # noqa: E731

        def local(t, n):
            init = self.init_stmts(t)
            if init is None:
                return [unsup(f"{what(n)}: the program has files that may be open")]
            act = {"item": self.active[t].id, "subs": [], "refStart": None, "refLen": None}
            return [{"ite": {"c": {"rel": {"op": "=", "a": {"ref": {"r": act}},
                                           "b": {"lit": {"l": {"str": {"s": "1"}}}}}},
                             "t": [unsup(f"{what(n)}: the program is active")], "e": init}}]
        if c["prog"] is not None:
            kind, t = self.resolve(caller, c["prog"])
            if kind == "prog":
                return local(t, c["prog"])
            if kind == "recursive":
                return [unsup(f"{what(c['prog'])}: the program is active")]
            if kind == "case":
                return [unsup(f"{what(c['prog'])}: the name matches a program only in letter case")]
            return [{"cancel": {"prog": c["prog"], "target": None}}]
        stmt = [{"cancel": {"prog": None, "target": c["target"]}}]
        for n, (kind, t) in reversed(self.callable_from(caller)):
            branch = local(t, n) if kind == "prog" else [unsup(f"{what(n)}: the program is active")]
            stmt = [{"ite": {"c": {"rel": {"op": "=", "a": {"ref": {"r": copy.deepcopy(c["target"])}},
                                           "b": {"lit": {"l": {"str": {"s": n}}}}}},
                             "t": branch, "e": stmt}}]
        return stmt

    def resolve_calls(self, p, j):
        """Replace the CALL and CANCEL placeholders of program p in the statement structure j."""
        if isinstance(j, list):
            out = []
            for v in j:
                if isinstance(v, dict) and "%call" in v:
                    out.extend(self.resolve_calls(p, self.call_stmts(p, p.calls[v["%call"]])))
                elif isinstance(v, dict) and "%cancel" in v:
                    out.extend(self.cancel_stmts(p, p.cancels[v["%cancel"]]))
                else:
                    out.append(self.resolve_calls(p, v))
            return out
        if isinstance(j, dict):
            return {k: self.resolve_calls(p, v) for k, v in j.items()}
        return j

    # ------------------------------------------------------------------ declaratives
    def merged_use(self):
        return [(p, i, u) for p in self.progs for i, u in enumerate(p.use)]

    @staticmethod
    def mode_of(u):
        return u["mode"]

    def merged_sel(self, merged, fid, m):
        for p, i, u in merged:
            if fid in u["files"]:
                return (p, i)
        for p, i, u in merged:
            if u["mode"] is not None and u["mode"] == m:
                return (p, i)
        return None

    def chain_sel(self, q, fid, m):
        for lvl, a in enumerate([q] + q.ancestors()):
            cands = [(i, u) for i, u in enumerate(a.use) if lvl == 0 or u["sect"] in a.use_global]
            for i, u in cands:
                if fid in u["files"]:
                    return (a, i)
            for i, u in cands:
                if u["mode"] is not None and u["mode"] == m:
                    return (a, i)
        return None

    def check_io(self, p, j, merged):
        """Replace the I/O statements of program p whose declarative the semantics could select
        differently from IBM's precedence rules."""
        if isinstance(j, list):
            return [self.check_io(p, v, merged) for v in j]
        if isinstance(j, dict):
            for k in IO_STMTS:
                v = j.get(k)
                if isinstance(v, dict) and isinstance(v.get("file"), int) and len(j) == 1:
                    fid = v["file"]
                    if any(self.chain_sel(p, fid, m) != self.merged_sel(merged, fid, m) for m in MODES):
                        f = self.files[fid][0]
                        return unsup(f"{k} of {f.name}: USE precedence of nested programs differs")
            return {k: self.check_io(p, v, merged) for k, v in j.items()}
        return j

    # ------------------------------------------------------------------ EXTERNAL records
    def externals(self, datas):
        """Later descriptions of an EXTERNAL record become REDEFINES of the first; the item JSON of
        every program is patched in place (`datas`: program -> its data JSON)."""
        first = {}
        alias = {}              # alias record id -> first record id
        faults = {}
        for p in self.progs:
            for e in p.dd.records:
                if not e.is_external:
                    continue
                if e.name in first:
                    b = first[e.name]
                    if item_size(e) != item_size(b):
                        faults.setdefault(p, []).append(
                            f"EXTERNAL record {e.name}: {item_size(e)} bytes here, {item_size(b)} bytes in "
                            f"program {self.owner[b.id].name}")
                    if any(x.index for x in walk_entries([e, b])):
                        # one storage, two descriptions: its index values could meet tables of other
                        # element lengths in the other program (Program.ix_finish)
                        faults.setdefault(p, []).append(f"EXTERNAL record {e.name} with index data items "
                                                        "described in several programs")
                    alias[e.id] = b.id
                else:
                    first[e.name] = e
        for p, data in datas.items():
            for it in data:
                if it["id"] in alias:
                    it["redefines"] = alias[it["id"]]
                elif it.get("redefines") in alias:
                    it["redefines"] = alias[it["redefines"]]
        return faults

    # ------------------------------------------------------------------ the unit
    def link(self):
        if any(self.rc_item(p) is not None for p in self.progs):
            # every separately compiled program gets its RETURN-CODE item (VALUE ZERO), so that the
            # caller's can be set from it after a CALL
            for p in self.progs:
                if p.parent is None and self.rc_item(p) is None:
                    p.special_register("RETURN-CODE", p.ts.peek())
                    e = p.dd.by_name["RETURN-CODE"][0]
                    self.entries[e.id], self.owner[e.id] = e, p
        self.clones = {}         # record id -> (program, its hidden copy), see init_stmts
        self.variants = {}       # (program, duplicate parameters) -> its variant, see variant
        # one hidden flag per program that can be called, '1' while it is active (after the main
        # program's other items, so no offset changes)
        self.active = {}
        for p in self.progs[1:]:
            e = Entry(self.main.fresh(), 1, f"%ACTIVE {p.name}", None, self.main.ts.peek(), "working")
            e.pic, e.cat, e.value = {"alnum": {"len": 1}}, "alnum", ("str", "0")
            self.main.dd.records.append(e)
            self.active[p] = e
            self.entries[e.id], self.owner[e.id] = e, self.main
        js = {p: p.json() for p in self.progs}
        for p in self.progs:
            js[p]["paras"] = self.resolve_calls(p, js[p]["paras"])
        merged = self.merged_use()
        if merged:
            for p in self.progs:
                js[p]["paras"] = self.check_io(p, js[p]["paras"], merged)
        faults = self.externals({p: js[p]["data"] for p in self.progs})
        # one PROGRAM COLLATING SEQUENCE for the linked unit, the first program's; a contained program
        # has its outermost program's (IBM: CONFIGURATION SECTION entries apply to contained programs)
        coll = js[self.main].get("collating")
        for p in self.progs[1:]:
            own, outer = js[p].get("collating"), js[p.outermost()].get("collating")
            if outer != coll or (own is not None and own != outer):
                faults.setdefault(p, []).append("PROGRAM COLLATING SEQUENCE other than the first program's")
        for p, whats in faults.items():
            first = [unsup("program: " + "; ".join(whats))]
            if js[p]["paras"]:
                js[p]["paras"][0]["sentences"].insert(0, first)
        if len(self.progs) == 1:
            return js[self.main]
        out = dict(js[self.main])
        data, files, paras, use = list(out["data"]), list(out["files"]), list(out["paras"]), \
            list(js[self.main].get("use", []))
        for p in self.progs[1:]:
            pre = self.prefix[p]
            data += js[p]["data"]
            files += js[p]["files"]
            paras.append({"name": pre + "LINK-BARRIER", "sect": None, "sentences": [["goback"]]})
            paras += [dict(q, name=pre + (q["name"] or "ENTRY"),
                           sect=(pre + q["sect"] if q.get("sect") else q.get("sect")),
                           sentences=prefix_stmts(q["sentences"], pre)) for q in js[p]["paras"]]
            use += [dict(u, sect=pre + u["sect"]) for u in js[p].get("use", [])]
        # the variants for duplicate arguments (after every program, each after a GOBACK barrier)
        for v in self.variants.values():
            t, pre = v["t"], v["prefix"]
            paras.append({"name": pre + "LINK-BARRIER", "sect": None, "sentences": [["goback"]]})
            paras += [dict(q, name=pre + (q["name"] or "ENTRY"),
                           sect=(pre + q["sect"] if q.get("sect") else q.get("sect")),
                           sentences=prefix_stmts(self.substitute(q["sentences"], v["ids"], v["conds"]), pre))
                      for q in js[t]["paras"]]
            data += [t.dd.item_json(c) for c in v["copies"]]
        # the hidden copies for initial states, after every other item
        data += [q.dd.item_json(c) for q, c in self.clones.values()]
        out.update(data=data, files=files, paras=paras)
        if use:
            out["use"] = use
        # the OCCURS DEPENDING ON tables of every program (item ids are unique in the unit)
        odo = [o for p in self.progs for o in js[p].get("odo", [])]
        if odo:
            out["odo"] = odo
        # for link.py (written next to the output by cobolfe.py): the unit's other separately
        # compiled programs, whose storage and files are not the first program's
        self.unit.sidecar = {"linked": [
            {"name": b.name, "kind": "unit", "prefix": self.prefix[b],
             "all": [e.id for q in self.subtree(b) for e in q.dd.records],
             "files": [f.id for q in self.subtree(b) for f in q.files.values()]}
            for b in self.progs[1:] if b.parent is None]}
        return out


def link_unit(unit):
    return Linker(unit).link()

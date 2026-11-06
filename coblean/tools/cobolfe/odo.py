"""OCCURS DEPENDING ON in statements: the surface IR of each statement that references a table
`OCCURS integer-1 TO integer-2 DEPENDING ON object`, a group containing one, or searches one
(IBM Enterprise COBOL 6.4, OCCURS DEPENDING ON clause).

The layout gives the table integer-2 occurrences, as IBM allocates it, so the declared length of
a group containing the table is its maximum length. A statement's own references (not those of
the statements nested in it) are classified:
* a group containing the table, as a receiving item of a statement of IBM's maximum length rule
  (MOVE, STRING / UNSTRING ... INTO, DELIMITER IN, READ ... INTO, ACCEPT, CALL ... BY REFERENCE)
  when the object lies in the group: the declared (maximum) length;
* any other reference to such a group (a sender, an operand of a condition, INSPECT, DISPLAY, the
  record of WRITE / REWRITE, a receiver whose object is outside it): the length for the object's
  value at the start of the statement. The statement becomes an EVALUATE on the object's values
  integer-1 .. integer-2, one copy per value with the reference marked (`odo`: the resolver gives
  the group that many occurrences), WHEN OTHER a range fault; a SEARCH / SEARCH ALL of the table
  is expanded the same way, with that number of occurrences;
* the table and its subordinate items: the declared descriptors (subscripts up to integer-2).
IBM: whenever the table, a subordinate or a group containing it is referenced the object must be
within integer-1 .. integer-2, else the behavior is undefined. The expansion checks it; the other
references are checked by `odoCheck` (a range fault outside), ANDed into the statement's own
conditions (IF, EVALUATE, UNTIL, SEARCH WHEN) when they hold all such references, else tested by
an IF around the statement. The groups passed to CALL ... BY REFERENCE are not checked (IBM: the
object need not be set then).
A statement in which a receiver stores into an object before a reference that depends on it is
unsupported, and so are references this scheme cannot place: level-88 names and INITIALIZE of
such a group, groups in an UNTIL condition, ODO items in a VARYING phrase, SET ADDRESS OF.
"""
import copy

from datadiv import CondEntry, item_size, place_list

# the most object values one statement is expanded for (all its tables together)
CAP = 4096

# statement fields that hold nested statements (`evaluate.arms`: [condition, statements] pairs,
# `search.bodies`: a list of statement lists)
NESTED = {"compute": ("onSize", "notOnSize"), "add": ("onSize", "notOnSize"),
          "subtract": ("onSize", "notOnSize"), "multiply": ("onSize", "notOnSize"),
          "divide": ("onSize", "notOnSize"), "ite": ("t", "e"), "evaluate": ("arms", "other"),
          "performInline": ("body",), "read": ("atEnd", "notAtEnd"), "fread": ("exc", "noExc"),
          "fwrite": ("exc", "noExc"), "frewrite": ("exc", "noExc"), "fdelete": ("exc", "noExc"),
          "fstart": ("exc", "noExc"), "search": ("atEnd", "bodies"), "searchAll": ("atEnd", "body"),
          "unstring": ("onOvf", "notOnOvf"), "stringInto": ("onOvf", "notOnOvf")}

def is_ref(j):
    return isinstance(j, dict) and isinstance(j.get("item"), int) and isinstance(j.get("subs"), list)


def walk_entries(es):
    for e in es:
        yield e
        yield from walk_entries(e.children)


class Ref:
    """One own reference of a statement: the JSON ref (None for the parent of a level-88 name),
    its entry, its role ('send', 'recv', 'call'), receiver order (0 for operands), whether it
    lies in a condition, and whether a group there keeps its maximum length."""

    def __init__(self, j, entry, role, time, in_cond, maxlen):
        self.j, self.entry, self.role, self.time, self.in_cond, self.maxlen = \
            j, entry, role, time, in_cond, maxlen


class Odo:
    def __init__(self, prog):
        self.p = prog
        dd = prog.dd
        # entry id -> ((table, integer-1, object), 'elem' | 'group')
        self.fam = {}
        for t, lo, obj in dd.odo_tables:
            info = (t, lo, obj)
            for d in walk_entries([t]):
                self.fam[d.id] = (info, "elem")
            for a in t.ancestors():
                self.fam[a.id] = (info, "group")
        self.tables = {t.id: (t, lo, obj) for t, lo, obj in dd.odo_tables}
        self.idx_table = {ie.id: ie.table for ie in dd.indexes}
        self.cond_parent = {c.id: c.parent for lst in dd.by_name.values() for c in lst
                            if isinstance(c, CondEntry)}
        self.entries = {}
        self.done = set()
        self.keep = []           # every statement dict seen here stays alive, so ids stay unique
        self._ext = None
        self._ext_n = -1

    # ------------------------------------------------------------------ data
    def entry(self, i):
        if not self.entries or i not in self.entries:
            self.entries = {e.id: e for e in walk_entries(self.p.dd.records)}
        return self.entries.get(i)

    def kind(self, e):
        """'group' / 'elem' for an item of an OCCURS DEPENDING ON table's family, else None."""
        f = self.fam.get(e.id) if e is not None else None
        return f[1] if f else None

    def info(self, e):
        return self.fam[e.id][0]

    def extents(self):
        """Absolute (start, end) of each item's storage, every occurrence of its tables included
        (Layout.lean placeRecords / Item.place)."""
        recs = self.p.dd.records
        if self._ext is not None and self._ext_n == len(recs):
            return self._ext
        out, placed, off = {}, {}, 0

        def place(e, start, rel):
            n = e.occurs or 1
            out[e.id] = (start, start + item_size(e, rel) * n)
            crel = 0 if e.occurs is not None else rel
            _, starts = place_list(e.children, crel)
            for c in e.children:
                place(c, start + starts[c.id], crel + starts[c.id])
        for r in recs:
            sz = item_size(r, 0) * (r.occurs or 1)
            if r.redefines is not None and r.redefines.id in placed:
                start, ln = placed[r.redefines.id]
                off = max(off, start + max(ln, sz))
            else:
                start = off
                placed[r.id] = (start, sz)
                off += sz
            place(r, start, 0)
        # an item inside a table: the extent of the outermost table
        ext = {}
        for e in walk_entries(recs):
            tabs = [x for x in [e] + e.ancestors() if x.occurs is not None]
            ext[e.id] = out[tabs[-1].id] if tabs else out[e.id]
        self._ext, self._ext_n = ext, len(recs)
        return ext

    def overlap(self, a, b):
        ex = self.extents()
        (s1, e1), (s2, e2) = ex[a.id], ex[b.id]
        return s1 < e2 and s2 < e1

    # ------------------------------------------------------------------ JSON helpers
    @staticmethod
    def obj_ref(obj):
        return {"item": obj.id, "subs": [], "refStart": None, "refLen": None}

    @staticmethod
    def check(t):
        return {"odoCheck": {"id": t.id}}

    def mark(self, node):
        if isinstance(node, dict):
            self.done.add(id(node))
            self.keep.append(node)
            for v in node.values():
                self.mark(v)
        elif isinstance(node, list):
            for v in node:
                self.mark(v)

    # ------------------------------------------------------------------ statements
    def lower(self, stmts):
        """The statements of a handler's output, each expanded as described above."""
        out = []
        for s in stmts:
            out.extend(self.stmt(s))
        return out

    def stmt(self, s):
        if not isinstance(s, dict) or id(s) in self.done:
            return [s]
        ctor = next(iter(s))
        f = s[ctor]
        # statements nested in s that a handler generated (not through Program.statement)
        for key in NESTED.get(ctor, ()):
            v = f.get(key)
            if v is None:
                continue
            if ctor == "evaluate" and key == "arms":
                f[key] = [[c, self.lower(b)] for c, b in v]
            elif ctor == "search" and key == "bodies":
                f[key] = [self.lower(b) for b in v]
            else:
                f[key] = self.lower(v)
        out = self.expand(ctor, s)
        self.mark(out)
        return out

    def own_refs(self, ctor, f, visit):
        """Call visit(json, entry, role, time, in_cond, maxlen, holder) for each own reference of
        statement `ctor` (fields f); `holder` is (dict, key) of a level-88 name or SET TO TRUE."""
        t = [0]

        def nxt():
            t[0] += 1
            return t[0]

        def scan(j, role, in_cond, tm, maxlen=False):
            if is_ref(j):
                visit(j, self.entry(j["item"]), role, tm, in_cond, maxlen, None)
                return
            if isinstance(j, dict):
                if "cond88" in j and isinstance(j["cond88"], dict):
                    visit(None, self.cond_parent.get(j["cond88"]["id"]), role, tm, in_cond, False, j)
                    return
                for v in j.values():
                    scan(v, role, in_cond, tm, maxlen)
            elif isinstance(j, list):
                for v in j:
                    scan(v, role, in_cond, tm, maxlen)
        skip = set(NESTED.get(ctor, ()))
        if ctor == "move":
            scan(f["src"], "send", False, 0)
            for d in f["dsts"]:
                scan(d, "recv", False, nxt(), True)
        elif ctor in ("compute", "add", "subtract", "multiply", "divide"):
            for k, v in f.items():
                if k not in skip and k not in ("rcv", "remainder"):
                    scan(v, "send", False, 0)
            for r in f["rcv"]:
                scan(r["ref"], "recv", False, nxt())
            if ctor == "divide" and f.get("remainder") is not None:
                scan(f["remainder"], "recv", False, nxt())
        elif ctor in ("clock", "accept"):
            scan(f["dst"], "recv", False, nxt(), True)
        elif ctor == "unstring":
            scan(f["src"], "send", False, 0)
            scan(f["delims"], "send", False, 0)
            for r in f["into"]:
                scan(r["rcv"], "recv", False, nxt(), True)
                if r.get("delim") is not None:
                    scan(r["delim"], "recv", False, nxt(), True)
                if r.get("count") is not None:
                    scan(r["count"], "recv", False, nxt())
            for k in ("ptr", "tally"):
                if f.get(k) is not None:
                    scan(f[k], "recv", False, nxt())
        elif ctor == "stringInto":
            scan(f["groups"], "send", False, 0)
            scan(f["into"], "recv", False, nxt(), True)
            if f.get("ptr") is not None:
                scan(f["ptr"], "recv", False, nxt())
        elif ctor in ("fread", "read"):
            nxt()      # the record area is stored before the INTO item
            if f.get("into") is not None:
                scan(f["into"], "recv", False, nxt(), True)
        elif ctor == "initialize":
            for d in f["dsts"]:
                scan(d, "recv", False, nxt())
        elif ctor == "setTrue":
            visit(None, self.cond_parent.get(f["id"]), "recv", nxt(), False, False, f)
        elif ctor == "call":
            scan(f["args"], "call", False, 0)
        elif ctor == "callLocal":
            scan(f["binds"], "call", False, 0)
        elif ctor in ("%call", "%cancel"):
            # a CALL or CANCEL that unit.py resolves after the parse (f indexes the program's calls /
            # cancels): the arguments as those of "call"; the identifier naming the program
            c = (self.p.calls if ctor == "%call" else self.p.cancels)[f]
            scan(c.get("args", []), "call", False, 0)
            if c.get("target") is not None:
                scan(c["target"], "target", False, 0)
        elif ctor == "inspect":
            scan(f["target"], "send", False, 0)
            for ph in f["tally"] + f["replace"]:
                for k in ("pat", "rep", "before", "after"):
                    if ph.get(k) is not None:
                        scan(ph[k], "send", False, 0)
            for ph in f["tally"]:
                if ph.get("counter") is not None:
                    scan(ph["counter"], "recv", False, nxt())
        elif ctor == "search":
            if f.get("varRef") is not None:
                scan(f["varRef"], "recv", False, nxt())
            scan(f["conds"], "send", True, 0)
        elif ctor == "searchAll":
            scan(f["keys"], "send", False, 0)
            scan(f["c"], "send", True, 0)
        elif ctor == "ite":
            scan(f["c"], "send", True, 0)
        elif ctor == "evaluate":
            for c, _ in f["arms"]:
                scan(c, "send", True, 0)
        elif ctor in ("perform", "performInline"):
            # UNTIL conditions are evaluated again and again; the VARYING item, FROM and BY make
            # statements the resolver repeats (role 'vary')
            loop = f["loop"]
            if isinstance(loop, dict):
                k, lv = next(iter(loop.items()))
                for kk, v in lv.items():
                    scan(v, "send" if kk in ("c", "n") else "vary", kk == "c", 0)
        else:
            for k, v in f.items():
                if k not in skip:
                    scan(v, "send", False, 0)

    def expand(self, ctor, s):
        f = s[ctor]
        refs = []
        self.own_refs(ctor, f, lambda j, e, role, tm, in_cond, maxlen, holder:
                      refs.append(Ref(j, e, role, tm, in_cond, maxlen)))
        split, checks, need = [], [], {}
        why = []

        def add(lst, info):
            if all(x[0] is not info[0] for x in lst):
                lst.append(info)
        for r in refs:
            k = self.kind(r.entry)
            if k is None:
                continue
            info = self.info(r.entry)
            t, lo, obj = info
            if r.role == "vary":
                why.append(f"an item of the OCCURS DEPENDING ON table {t.name} or a group containing it "
                           "in a VARYING phrase")
                continue
            if r.role == "target":
                why.append(f"an item of the OCCURS DEPENDING ON table {t.name} or a group containing it "
                           "naming the program of a CALL or CANCEL")
                continue
            if k == "group":
                if r.j is None:
                    why.append(f"level-88 condition name of a group containing the OCCURS DEPENDING ON "
                               f"table {t.name}")
                    continue
                if ctor == "initialize":
                    why.append(f"INITIALIZE of a group containing the OCCURS DEPENDING ON table {t.name} "
                               "(IBM: not allowed)")
                    continue
                if r.role == "call":
                    continue
                if r.maxlen and r.entry in obj.ancestors():
                    add(checks, info)
                    need[id(r)] = ("check", info)
                    continue
                if ctor in ("perform", "performInline") and r.in_cond:
                    why.append(f"a group containing the OCCURS DEPENDING ON table {t.name} in an UNTIL condition")
                    continue
                add(split, info)
                need[id(r)] = ("len", info)
            else:
                add(checks, info)
                need[id(r)] = ("check", info)
        if ctor in ("search", "searchAll"):
            tab = self.idx_table.get(f["idx"])
            if tab is not None and tab.id in self.tables:
                add(split, self.tables[tab.id])
        if ctor == "setAddress" and need:
            why.append("SET ADDRESS OF an item of an OCCURS DEPENDING ON table")
        if not split and not checks and not why:
            return [s]
        # a receiver that stores into an object before a reference that depends on it
        recvs = [r for r in refs if r.role == "recv" and r.entry is not None]
        for r in refs:
            if id(r) not in need:
                continue
            _, (t, lo, obj) = need[id(r)]
            if any(w.time < r.time and self.overlap(w.entry, obj) for w in recvs):
                why.append(f"a receiver stores into the OCCURS DEPENDING ON object {obj.name} before a "
                           "later reference that depends on it")
        if ctor in ("fread", "read"):
            area = next((fl.records for fl in self.p.files.values() if fl.id == f["file"]), [])
            for r in refs:
                if id(r) in need and any(self.overlap(a, need[id(r)][1][2]) for a in area):
                    why.append("READ ... INTO an item whose OCCURS DEPENDING ON object is in the record area")
        if ctor == "search" and f.get("varRef") is not None:
            ve = self.entry(f["varRef"]["item"])
            if any(self.overlap(ve, obj) for _, _, obj in split + checks):
                why.append("SEARCH VARYING an OCCURS DEPENDING ON object")
        checks = [c for c in checks if all(c[0] is not x[0] for x in split)]
        n = 1
        for t, lo, obj in split:
            n *= t.occurs - lo + 1
        if n > CAP:
            why.append(f"OCCURS DEPENDING ON: more than {CAP} object values in one statement")
        if why:
            for w in dict.fromkeys(why):
                self.p.unsup(w)
            return [s]
        # checks: ANDed into the statement's conditions when every checked reference lies in them
        cond_ok = ctor in ("ite", "evaluate", "search", "searchAll", "perform", "performInline")
        embed = [c for c in checks if cond_ok and
                 all(r.in_cond for r in refs if id(r) in need and need[id(r)][1][0] is c[0])]
        guard = [c for c in checks if all(c[0] is not x[0] for x in embed)]

        def finish(st):
            """The checks of one copy of the statement: in its conditions, or around it."""
            g = st[ctor]
            if embed:
                def conj(c, refs_in):
                    for t, _, _ in embed:
                        if t.id in refs_in:
                            c = {"and": {"a": c, "b": self.check(t)}}
                    return c

                def tabs_in(c):
                    found = set()

                    def visit(j, e, role, tm, in_cond, maxlen, holder):
                        if self.kind(e) is not None:
                            found.add(self.info(e)[0].id)

                    def sc(x):
                        if is_ref(x):
                            visit(x, self.entry(x["item"]), None, 0, True, False, None)
                        elif isinstance(x, dict):
                            if "cond88" in x and isinstance(x["cond88"], dict):
                                visit(None, self.cond_parent.get(x["cond88"]["id"]), None, 0, True, False, x)
                                return
                            for v in x.values():
                                sc(v)
                        elif isinstance(x, list):
                            for v in x:
                                sc(v)
                    sc(c)
                    return found
                if ctor in ("ite", "searchAll"):
                    g["c"] = conj(g["c"], tabs_in(g["c"]))
                elif ctor == "evaluate":
                    g["arms"] = [[conj(c, tabs_in(c)), b] for c, b in g["arms"]]
                elif ctor == "search":
                    g["conds"] = [conj(c, tabs_in(c)) for c in g["conds"]]
                else:
                    lv = next(iter(g["loop"].values()))
                    lv["c"] = conj(lv["c"], tabs_in(lv["c"]))
            if guard:
                c = self.check(guard[0][0])
                for t, _, _ in guard[1:]:
                    c = {"and": {"a": c, "b": self.check(t)}}
                return {"ite": {"c": c, "t": [st], "e": []}}
            return st
        if not split:
            return [finish(copy.deepcopy(s))]
        # one copy per combination of the objects' values
        combos = [[]]
        for t, lo, obj in split:
            combos = [c + [(t, obj, v)] for c in combos for v in range(lo, t.occurs + 1)]
        arms = []
        for combo in combos:
            vals = {t.id: v for t, _, v in combo}
            st = copy.deepcopy(s)
            g = st[ctor]
            marks = []
            self.own_refs(ctor, g, lambda j, e, role, tm, in_cond, maxlen, holder:
                          marks.append(Ref(j, e, role, tm, in_cond, maxlen)))
            for r in marks:
                if self.kind(r.entry) == "group" and r.j is not None and r.role != "call":
                    t, lo, obj = self.info(r.entry)
                    if t.id in vals and not (r.maxlen and r.entry in obj.ancestors()):
                        r.j["odo"] = vals[t.id]
            if ctor in ("search", "searchAll"):
                tab = self.idx_table.get(g["idx"])
                if tab is not None and tab.id in vals:
                    g["occurs"] = vals[tab.id]
            c = None
            for t, obj, v in combo:
                e = {"rel": {"op": "=", "a": {"ref": {"r": self.obj_ref(obj)}},
                             "b": {"lit": {"l": {"num": {"v": v, "scale": 0, "digits": 0}}}}}}
                c = e if c is None else {"and": {"a": c, "b": e}}
            arms.append([c, [finish(st)]])
        fault = self.check(split[0][0])
        for t, _, _ in split[1:]:
            fault = {"and": {"a": fault, "b": self.check(t)}}
        return [{"evaluate": {"arms": arms, "other": [{"ite": {"c": fault, "t": [], "e": []}}]}}]

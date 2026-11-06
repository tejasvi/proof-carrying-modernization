"""Link a called COBOL program into its caller (surface IR JSON).

usage: python3 -I tools/cobolfe/link.py CALLER.json CALLEE.json -o LINKED.json

The callee's data items, files and paragraphs are appended to the caller's (item ids and
file numbers renumbered; paragraph names, section names and the targets of the callee's own
local calls prefixed with `CALLEE::`).  Every `CALL 'CALLEE' USING args` of the caller becomes
`callLocal`: the arguments' bytes go to the callee's `USING` items, its paragraphs run from its
first one until `GOBACK`, `EXIT PROGRAM` or their end, and the parameters' bytes come back.
The callee's `EXIT PROGRAM` is linked as `GOBACK`: the linked program is a main program, where
the semantics ignores `EXIT PROGRAM`, while in the called program it returns.  The callee keeps
its storage and its open files from one call to the next, as a called COBOL program does until
`CANCEL`.  A paragraph with `GOBACK` separates the two procedure divisions, so that the caller
cannot fall into the callee.  Copying the arguments in and out is the storage sharing of `BY
REFERENCE` only when no two arguments overlap: such a CALL becomes `unsupported`.  A `callDyn` of
the callee (cobolfe's unit.py: `ON EXCEPTION` / `NOT ON EXCEPTION`, or `CALL identifier`) is linked
too: the callee is available, so `NOT ON EXCEPTION` follows the return, and `CALL identifier`
becomes `IF identifier = 'CALLEE'` with the remaining `callDyn` in its `ELSE`.  Programs that both
describe an `EXTERNAL` record of the same name are not linked (unsupported).
"""
import argparse, copy, json, os, sys


def max_id(node, best=0):
    if isinstance(node, dict):
        for k, v in node.items():
            if k in ("id", "item") and isinstance(v, int):
                best = max(best, v)
            elif k == "conds" and isinstance(v, list):
                for c in v:
                    if isinstance(c, list) and c and isinstance(c[0], int):
                        best = max(best, c[0])
            best = max_id(v, best)
    elif isinstance(node, list):
        for v in node:
            best = max_id(v, best)
    return best


def renum_data(node, off):
    """Item ids in data descriptions."""
    if isinstance(node, dict):
        out = {}
        for k, v in node.items():
            if k in ("id", "redefines") and isinstance(v, int):
                out[k] = v + off
            elif k == "conds":
                out[k] = [[c[0] + off, c[1]] for c in v]
            else:
                out[k] = renum_data(v, off)
        return out
    if isinstance(node, list):
        return [renum_data(v, off) for v in node]
    return node


FILE_STMTS = {"read", "write", "fopen", "fclose", "fread", "fwrite", "frewrite", "fdelete", "fstart", "fcloseOpt",
              "fopenRev"}


def renum_stmt(node, off, foff, prefix, ctor=None):
    """Item ids, file numbers and paragraph names in statements."""
    if isinstance(node, dict):
        out = {}
        for k, v in node.items():
            if k in ("item", "id") and isinstance(v, int):
                out[k] = v + off
            elif k == "key" and ctor in ("fread", "fstart") and isinstance(v, int):
                out[k] = v + off
            elif k == "file" and ctor in FILE_STMTS and isinstance(v, int):
                out[k] = v + foff
            elif k in ("first", "last", "target") and ctor in ("perform", "goTo") and isinstance(v, str):
                out[k] = prefix + v
            elif k == "targets" and ctor == "goToDep":
                out[k] = [prefix + t for t in v]
            elif k == "para" and ctor == "callLocal" and isinstance(v, str):
                out[k] = prefix + v
            else:
                out[k] = renum_stmt(v, off, foff, prefix, k if isinstance(v, dict) else ctor)
        return out
    if isinstance(node, list):
        # a bare string in a statement list is a statement without arguments
        return ["goback" if v == "exitProgram" else renum_stmt(v, off, foff, prefix, ctor)
                for v in node]
    return node


def json_items(data):
    """item id -> (item JSON, parent id or None, top-level record id)."""
    out = {}

    def go(it, parent, rec):
        out[it["id"]] = (it, parent, rec)
        for c in it.get("children", []):
            go(c, it["id"], rec)
    for it in data:
        go(it, None, it["id"])
    return out


def may_overlap(items, ra, rb):
    """Whether two data references can share storage (conservative): their records are the same or
    REDEFINES one another, and they are not provably apart (distinct non-redefining parts of one group,
    distinct literal occurrences of one item, distinct literal reference modifications)."""
    def group(rec):
        while items[rec][0].get("redefines") is not None:
            rec = items[rec][0]["redefines"]
        return rec

    def path(i):
        p = []
        while i is not None:
            p.append(i)
            i = items[i][1]
        return p[::-1]
    ia, ib = ra["item"], rb["item"]
    if ia not in items or ib not in items:
        return True
    if group(items[ia][2]) != group(items[ib][2]):
        return False
    if items[ia][2] != items[ib][2]:
        return True
    pa, pb = path(ia), path(ib)
    k = 0
    while k < min(len(pa), len(pb)) and pa[k] == pb[k]:
        k += 1
    if k == len(pa) and k == len(pb):
        sa, sb = ra["subs"], rb["subs"]
        if sa != sb and all("lit" in s for s in sa + sb):
            return False
        if sa == sb and all(x is not None and "lit" in x for x in (ra["refStart"], ra["refLen"],
                                                                   rb["refStart"], rb["refLen"])):
            a0, b0 = ra["refStart"]["lit"]["n"], rb["refStart"]["lit"]["n"]
            return a0 < b0 + rb["refLen"]["lit"]["n"] and b0 < a0 + ra["refLen"]["lit"]["n"]
        return True
    if k == len(pa) or k == len(pb):
        return True

    def base(i):
        while items[i][0].get("redefines") is not None:
            i = items[i][0]["redefines"]
        return i
    return base(pa[k]) == base(pb[k])


def local_call(callee, entry, params, args, items, variants=None):
    """`callLocal` of the linked callee, or `unsupported` when copy-in/copy-out would not be the same
    storage as BY REFERENCE (overlapping arguments). The same item passed twice is one storage in the
    callee (IBM: "the corresponding data item in the calling program occupies the same storage area as
    the data item in the called program"): a variant of the callee names the second parameter through a
    REDEFINES of the first (`Variants`); the second is still bound, before the others, so that its length
    is checked and its stale copy-back is overwritten by the first's."""
    if len(args) != len(params):
        return {"unsupported": {"what": f"CALL {callee}: {len(args)} arguments for {len(params)} parameters"}}
    dups = {j: next(i for i in range(j) if args[i] == args[j]) for j in range(len(args))
            if any(args[i] == args[j] for i in range(j))}
    rest = [k for k in range(len(args)) if k not in dups]
    for x, i in enumerate(rest):
        for k in rest[x + 1:]:
            if may_overlap(items, args[i], args[k]):
                return {"unsupported": {"what": f"CALL {callee}: arguments that share storage (BY REFERENCE)"}}
    ref = lambda p: {"item": p, "subs": [], "refStart": None, "refLen": None}  # noqa: E731
    if dups:
        why = variants.problem(dups) if variants is not None else "no variant"
        if why is not None:
            return {"unsupported": {"what": f"CALL {callee}: {why}"}}
        entry = variants.entry(dups)
        order = sorted(dups) + rest
        return {"callLocal": {"para": entry, "binds": [[args[k], ref(params[k])] for k in order]}}
    return {"callLocal": {"para": entry, "binds": [[a, ref(p)] for a, p in zip(args, params)]}}


class Variants:
    """Variants of the callee for duplicate arguments: its own paragraphs (those before the first
    LINK-BARRIER) with every reference to parameter j's items made to a copy of parameter j that
    REDEFINES parameter i, after a GOBACK barrier, named `%Vk:` + the paragraph name."""

    def __init__(self, inits, bparas, params, data_items):
        self.inits, self.params, self.items = inits, params, data_items
        k = next((n for n, p in enumerate(bparas) if p["name"].endswith("::LINK-BARRIER")), len(bparas))
        self.own, self.others = bparas[:k], bparas[k:]
        self.made = {}

    def ids_under(self, rid):
        out = []

        def go(it):
            out.append(it["id"])
            for c in it.get("children", []):
                go(c)
        go(self.items[rid][0])
        return set(out)

    def problem(self, dups):
        for j, i in dups.items():
            mine = self.ids_under(self.params[j]) | self.ids_under(self.params[i])
            if any(item_refs(p["sentences"], mine, args_only=True) for p in self.own):
                return "the same argument twice, passed on by the called program"
            if any(item_refs(p["sentences"], self.ids_under(self.params[j])) for p in self.others):
                return "the same argument twice for a parameter other programs name"
            if any(d.get("redefines") in (self.params[j],) or (d["id"] == self.params[j] and d.get("redefines"))
                   for d in self.inits.data):
                return "the same argument twice for a redefined parameter"
        return None

    def entry(self, dups):
        key = tuple(sorted(dups.items()))
        if key not in self.made:
            pre = f"%V{len(self.made) + 1}:"
            ids, conds = {}, {}
            for j, i in sorted(dups.items()):
                self.inits.data.append(self.copy(self.items[self.params[j]][0], self.params[i], ids, conds, True))
            paras = [{"name": pre + "LINK-BARRIER", "sect": None, "sentences": [["goback"]]}] + \
                [dict(p, name=pre + p["name"], sect=(pre + p["sect"] if p.get("sect") else p.get("sect")),
                      sentences=vprefix(vsubst(p["sentences"], ids, conds), pre)) for p in self.own]
            self.made[key] = (pre + self.own[0]["name"], paras)
        return self.made[key][0]

    def copy(self, it, base, ids, conds, top):
        n = dict(it)
        n["id"] = ids[it["id"]] = self.inits.next_id
        self.inits.next_id += 1
        if top:
            n["name"], n["level"], n["redefines"] = "%ALIAS " + it["name"], 1, base
        elif it.get("redefines") is not None:
            n["redefines"] = ids[it["redefines"]]
        n.pop("external", None)
        cs = []
        for c in it.get("conds", []):
            conds[c[0]] = self.inits.next_id
            cs.append([self.inits.next_id, c[1]])
            self.inits.next_id += 1
        n["conds"] = cs
        n["children"] = [self.copy(c, base, ids, conds, False) for c in it.get("children", [])]
        return n

    def paragraphs(self):
        return [p for _, ps in self.made.values() for p in ps]


def item_refs(node, ids, args_only=False, in_args=False):
    """Whether node refers to one of the items `ids` (with args_only: as an argument of a CALL)."""
    if isinstance(node, dict):
        if isinstance(node.get("item"), int) and node["item"] in ids and (in_args or not args_only):
            return True
        for k, v in node.items():
            sub = in_args or k in ("binds", "args")
            if item_refs(v, ids, args_only, sub):
                return True
        return False
    if isinstance(node, list):
        return any(item_refs(v, ids, args_only, in_args) for v in node)
    return False


def vsubst(node, ids, conds, ctor=None):
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
                out[k] = vsubst(v, ids, conds, k if isinstance(v, dict) else ctor)
        return out
    if isinstance(node, list):
        return [vsubst(v, ids, conds, ctor) for v in node]
    return node


def vprefix(node, pre, ctor=None):
    """Paragraph and section names of PERFORM and GO TO statements prefixed (not `callLocal` targets)."""
    if isinstance(node, dict):
        out = {}
        for k, v in node.items():
            if k in ("first", "last", "target") and ctor in ("perform", "goTo") and isinstance(v, str):
                out[k] = pre + v
            elif k == "targets" and ctor == "goToDep":
                out[k] = [pre + t for t in v]
            else:
                out[k] = vprefix(v, pre, k if isinstance(v, dict) else ctor)
        return out
    if isinstance(node, list):
        return [vprefix(v, pre, ctor) for v in node]
    return node


def replace_calls(node, callee, entry, params, items, pre=(), variants=None):
    """The CALLs of `callee` in node: `call` by its name, and `callDyn` (cobolfe's unit.py: a CALL with
    ON EXCEPTION / NOT ON EXCEPTION, or of a program named by an identifier) whose literal is its name
    or whose identifier may hold it; the callee is in the run unit, so NOT ON EXCEPTION follows the
    return. A CALL identifier becomes IF identifier = 'callee' ... ELSE the remaining callDyn. `pre`:
    statements before each CALL (an INITIAL callee's initial state)."""
    def call(args):
        return [copy.deepcopy(s) for s in pre] + [local_call(callee, entry, params, args, items, variants)]
    if isinstance(node, dict):
        return {k: replace_calls(v, callee, entry, params, items, pre, variants) for k, v in node.items()}
    if isinstance(node, list):
        out = []
        for v in node:
            c = v.get("call") if isinstance(v, dict) else None
            d = v.get("callDyn") if isinstance(v, dict) else None
            if isinstance(c, dict) and c.get("prog") == callee:
                if len(c["args"]) != len(params):
                    raise SystemExit(f"CALL {callee}: {len(c['args'])} arguments for {len(params)} parameters")
                out.extend(call(c["args"]))
            elif isinstance(d, dict) and d.get("prog") == callee:
                out.extend(call(d["args"]))
                out.extend(replace_calls(d["notOnExc"], callee, entry, params, items, pre, variants))
            elif isinstance(d, dict) and d.get("prog") is None and d.get("target") is not None:
                hit = call(d["args"]) + replace_calls(d["notOnExc"], callee, entry, params, items, pre, variants)
                out.append({"ite": {"c": {"rel": {"op": "=", "a": {"ref": {"r": d["target"]}},
                                                  "b": {"lit": {"l": {"str": {"s": callee}}}}}},
                                    "t": hit, "e": [replace_calls(v, callee, entry, params, items, pre, variants)]}})
            else:
                out.append(replace_calls(v, callee, entry, params, items, pre, variants))
        return out
    return node


def read_side(path):
    """The programs linked into a JSON file (`PATH.link.json`, written by link.py and, for a source with
    several separately compiled programs, by cobolfe.py): name, kind (`linked` by link.py, `unit` by
    cobolfe), paragraph prefix, top-level record ids (`all`), file ids, and for `linked` ones the records
    their initial state sets (`records`) and whether a file of theirs is opened (`open`)."""
    p = path + ".link.json"
    if os.path.exists(p):
        with open(p) as fh:
            return json.load(fh)
    return {"linked": []}


def opens(node, fids):
    if isinstance(node, dict):
        o = node.get("fopen")
        if isinstance(o, dict) and o.get("file") in fids:
            return True
        o = node.get("fopenRev")    # OPEN INPUT ... REVERSED
        if isinstance(o, dict) and o.get("file") in fids:
            return True
        return any(opens(v, fids) for v in node.values())
    if isinstance(node, list):
        return any(opens(v, fids) for v in node)
    return False


def own_program(J, side):
    """The program a JSON file is for, with the programs it contains, but not the programs linked into
    it: (top-level record ids, the records its initial state sets, file ids, a file of its opened?).
    The initial state (LR, PROGRAM-ID): WORKING-STORAGE items get their VALUE; not EXTERNAL records,
    REDEFINES records (their storage is the redefined one's), switches, parameters or file areas."""
    other = {r for e in side["linked"] for r in e["all"]}
    other_files = {f for e in side["linked"] for f in e["files"]}
    fids = [f["id"] for f in J["files"] if f["id"] not in other_files]
    areas = {f["record"] for f in J["files"] if f["id"] in fids}
    params = set(J["using"])
    allr = [d["id"] for d in J["data"] if d["id"] not in other]
    recs = [d["id"] for d in J["data"] if d["id"] not in other and d.get("redefines") is None and
            not d.get("external") and d["id"] not in params and d["id"] not in areas and
            not d["name"].startswith(("%UPSI-", "%SWITCH-", "%ACTIVE ", "%INIT "))]
    return allr, recs, fids, opens(J["paras"], set(fids))


class Inits:
    """Statements that put a linked program in its initial state: each record gets the bytes of a hidden
    copy with the same VALUE clauses (appended after every other item); items without VALUE get the
    copy's initial contents (IBM: undefined)."""

    def __init__(self, data, next_id):
        self.data, self.next_id, self.copies = data, next_id, {}

    def copy(self, rid):
        if rid in self.copies:
            return self.copies[rid]
        ids = {}

        def cp(it, top):
            n = {k: v for k, v in it.items() if k not in ("external",)}
            ids[it["id"]] = self.next_id
            n["id"] = self.next_id
            self.next_id += 1
            if top:
                n["name"], n["level"], n["redefines"] = "%INIT " + it["name"], 1, None
            elif it.get("redefines") is not None:
                n["redefines"] = ids[it["redefines"]]
            n["conds"] = []
            n["children"] = [cp(c, False) for c in it.get("children", [])]
            return n
        src = next(d for d in self.data if d["id"] == rid)
        self.data.append(cp(src, True))
        self.copies[rid] = ids[rid]
        return ids[rid]

    def stmts(self, name, entry):
        """For a sidecar entry (or the callee's own program): the MOVEs, or unsupported."""
        if entry["open"]:
            return [{"unsupported": {"what": f"{name}: the program has files that may be open"}}]
        whole = lambda i: {"item": i, "subs": [], "refStart": {"lit": {"n": 1}}, "refLen": None}  # noqa: E731
        return [{"move": {"src": {"ref": {"r": whole(self.copy(r))}}, "dsts": [whole(r)]}}
                for r in entry["records"]]


def replace_cancels(node, targets, inits):
    """The `cancel` nodes (cobolfe: a CANCEL of a program not in its unit) of the linked programs
    `targets` (name -> sidecar entry): the program's initial state (LR, CANCEL: "the referenced
    subprogram is entered in initial state the next time that it is called"); a CANCEL identifier
    becomes IF identifier = 'NAME' ... ELSE the remaining cancel."""
    if isinstance(node, dict):
        return {k: replace_cancels(v, targets, inits) for k, v in node.items()}
    if isinstance(node, list):
        out = []
        for v in node:
            d = v.get("cancel") if isinstance(v, dict) else None
            if isinstance(d, dict) and d.get("prog") in targets:
                out.extend(inits.stmts(f"CANCEL {d['prog']}", targets[d["prog"]]))
            elif isinstance(d, dict) and d.get("prog") is None and d.get("target") is not None:
                st = v
                for n in sorted(targets, reverse=True):
                    st = {"ite": {"c": {"rel": {"op": "=", "a": {"ref": {"r": d["target"]}},
                                                "b": {"lit": {"l": {"str": {"s": n}}}}}},
                                  "t": inits.stmts(f"CANCEL {n}", targets[n]), "e": [st]}}
                out.append(st)
            else:
                out.append(replace_cancels(v, targets, inits))
        return out
    return node


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("caller"); ap.add_argument("callee"); ap.add_argument("-o", dest="out", required=True)
    a = ap.parse_args()
    A = json.load(open(a.caller)); B = json.load(open(a.callee))
    callee = B["name"]
    if "using" not in B:
        raise SystemExit("the callee's JSON has no USING list (re-extract it)")
    # USE declaratives are local to their program: a callee's are not linked, and a caller's
    # open-mode declaratives would also catch the callee's files once both share one file list
    if B.get("use"):
        raise SystemExit("unsupported: the called program has USE declaratives")
    if B["files"] and any(u.get("mode") for u in A.get("use", [])):
        raise SystemExit("unsupported: the caller's open-mode USE declaratives would apply to "
                         "the called program's files")
    # a switch is one per run unit, but each program has its own hidden item for it (cobolfe's
    # make_switches): a SET in one program would not reach the other
    shared = {d["name"] for d in A["data"] if d["name"].startswith(("%UPSI-", "%SWITCH-"))} & \
        {d["name"] for d in B["data"] if d["name"].startswith(("%UPSI-", "%SWITCH-"))}
    if shared:
        raise SystemExit(f"unsupported: both programs use the switch {sorted(shared)[0][1:]}")
    # an EXTERNAL record is one storage per run unit; cobolfe shares it among the programs of one
    # source (unit.py), not across separately linked programs
    ext = {d["name"] for d in A["data"] if d.get("external")} & \
        {d["name"] for d in B["data"] if d.get("external")}
    if ext:
        raise SystemExit(f"unsupported: both programs describe the EXTERNAL record {sorted(ext)[0]}")
    # one PROGRAM COLLATING SEQUENCE per linked program: the caller's would apply to the callee
    if A.get("collating") != B.get("collating"):
        raise SystemExit("unsupported: the called program's PROGRAM COLLATING SEQUENCE differs from the caller's")
    off = max(max_id(A["data"]), max_id(A["paras"])) + 1
    foff = max([f["id"] for f in A["files"]] or [0])
    prefix = callee + "::"
    data = A["data"] + renum_data(B["data"], off)
    files = A["files"] + [dict(f, id=f["id"] + foff, record=f["record"] + off,
                               key=(f["key"] + off if f.get("key") is not None else None),
                               status=(f["status"] + off if f.get("status") is not None else None),
                               dependsOn=(f["dependsOn"] + off if f.get("dependsOn") is not None else None),
                               alt=[[k + off, d] for k, d in f.get("alt", [])])
                          for f in B["files"]]
    bparas = [dict(p, name=prefix + (p["name"] or "ENTRY"),
                   sect=(prefix + p["sect"] if p.get("sect") else p.get("sect")),
                   sentences=renum_stmt(p["sentences"], off, foff, prefix)) for p in B["paras"]]
    entry = bparas[0]["name"]
    params = [u + off for u in B["using"]]
    # the programs linked into each file before (link.py's sidecars), and the callee's own program
    A_side, B_side = read_side(a.caller), read_side(a.callee)
    b_all, b_recs, b_files, b_open = own_program(B, B_side)
    b_entry = {"name": callee, "kind": "linked", "prefix": prefix, "all": [r + off for r in b_all],
               "records": [r + off for r in b_recs], "files": [f + foff for f in b_files], "open": b_open}
    b_side = [dict(e, prefix=prefix + e["prefix"], all=[r + off for r in e["all"]],
                   files=[f + foff for f in e["files"]],
                   **({"records": [r + off for r in e["records"]]} if "records" in e else {}))
              for e in B_side["linked"]]
    inits = Inits(data, max(max_id(data), max_id(A["paras"]), max_id(bparas)) + 1)
    # an INITIAL callee starts in its initial state at every CALL (LR, PROGRAM-ID)
    pre = inits.stmts(f"CALL {callee}", b_entry) if B.get("initial") else []
    # CANCELs in the callee of the programs linked into the caller before (none of them can be active
    # there: each subprogram is linked once, under its only caller)
    bparas = replace_cancels(bparas, {e["name"]: e for e in A_side["linked"] if e["kind"] == "linked"}, inits)
    variants = Variants(inits, bparas, params, json_items(data))
    aparas = replace_calls(A["paras"], callee, entry, params, json_items(A["data"]), pre, variants)
    # CANCELs in the caller of the callee and of the programs linked into it
    aparas = replace_cancels(aparas, {callee: b_entry, **{e["name"]: e for e in b_side if e["kind"] == "linked"}},
                             inits)
    barrier = {"name": prefix + "LINK-BARRIER", "sect": None, "sentences": [["goback"]]}
    # OCCURS DEPENDING ON tables of both programs (the key only when there is one)
    odo = A.get("odo", []) + [dict(o, subject=o["subject"] + off, obj=o["obj"] + off)
                              for o in B.get("odo", [])]
    out = dict(A, data=inits.data, files=files, paras=aparas + [barrier] + bparas + variants.paragraphs(),
               **({"odo": odo} if odo else {}))
    json.dump(out, open(a.out, "w"), indent=1)
    with open(a.out + ".link.json", "w") as fh:
        json.dump({"linked": A_side["linked"] + b_side + [b_entry]}, fh, indent=1)
    print(f"linked {callee} into {A['name']}: items +{off}, files +{foff}, entry {entry}, "
          f"{len(params)} parameter(s)")


if __name__ == "__main__":
    main()

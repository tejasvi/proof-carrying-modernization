"""compile_commands.json as the C/C++ build input (read as data: no build script of the target runs).

Each entry becomes one build variant (one translation unit) with the entry's recorded flags: `-D`/`-U`/`-I`/
`-isystem`/`-include`/`-std` and the other language flags are kept, include paths are made absolute against the
entry's directory, and output/dependency flags are dropped. `link_callgraph` joins the units of all variants into
one call graph: a call to a function defined in another TU becomes a cross-TU edge. Verification stays per TU
(cirlean has one context per module), so a caller of another TU's function is a gap until contexts can be linked.
"""
from __future__ import annotations

import json
import re
import shlex
from pathlib import Path

from ...model import Target, Variant, write_json

_DROP_WITH_ARG = {"-o", "-MF", "-MT", "-MQ", "-Xclang"}
_DROP = {"-c", "-MD", "-MMD", "-M", "-MM", "-MP", "-S", "-E", "-pipe", "-fcolor-diagnostics"}
_PATH_FLAGS = ("-I", "-isystem", "-iquote", "-include", "-imacros", "-idirafter")


def _ident(s: str) -> str:
    out = re.sub(r"[^A-Za-z0-9_]", "_", s)
    return out if out[:1].isalpha() else "tu_" + out


def entry_flags(entry: dict) -> list[str]:
    args = entry.get("arguments") or shlex.split(entry.get("command", ""))
    d = Path(entry.get("directory", "."))
    src = entry["file"]
    out, i = [], 1                      # args[0] is the compiler
    while i < len(args):
        a = args[i]
        if a in _DROP_WITH_ARG:
            i += 2
            continue
        if a in _DROP or a == src or (Path(a).name == Path(src).name and not a.startswith("-")):
            i += 1
            continue
        if a.startswith(("-o", "-MF", "-MT", "-MQ")) and len(a) > 3:
            i += 1
            continue
        for f in _PATH_FLAGS:
            if a == f and i + 1 < len(args):
                p = Path(args[i + 1])
                out += [f, str(p if p.is_absolute() else (d / p).resolve())]
                i += 2
                break
            if a.startswith(f) and len(a) > len(f) and f in ("-I",):
                p = Path(a[len(f):])
                out.append(f + str(p if p.is_absolute() else (d / p).resolve()))
                i += 1
                break
        else:
            if a.startswith("-") and not a.startswith(("-W", "-g", "-O", "-f")):   # language flags (-D, -U, -std, -m...)
                out.append(a)
            elif a.startswith("-f") and a.startswith(("-fno-exceptions", "-fexceptions", "-fno-rtti", "-frtti",
                                                         "-fsigned-char", "-funsigned-char", "-fwrapv")):
                out.append(a)
            i += 1
    return out


def variants_from_compdb(target: Target) -> list[Variant]:
    db = Path(target.extra.get("compile_commands_abs") or Path(target.root) / target.extra["compile_commands"])
    entries = json.loads(db.read_text())
    root = Path(target.root).resolve()
    # a materialised revision (CI) has another root: re-root the recorded directories so that the old revision
    # is built with its own headers, not the current checkout's
    orig = str(Path(target.extra.get("orig_root", target.root)).resolve())
    if orig != str(root):
        entries = [json.loads(json.dumps(e).replace(orig, str(root))) for e in entries]
    groups = target.extra.get("link_groups")
    if groups:
        # programs: TUs linked together (the link structure is data in the target file, like the database);
        # each group is one module, so calls between its TUs are ordinary calls
        by_file = {}
        for e in entries:
            f = Path(e["file"])
            f = (Path(e.get("directory", ".")) / f).resolve() if not f.is_absolute() else f.resolve()
            by_file[str(f.relative_to(root)) if str(f).startswith(str(root)) else str(f)] = e
        # per-file flags, for builds that compile each source on its own (linked builds)
        target.extra["compdb_flags"] = {rel: entry_flags(e) for rel, e in by_file.items()}
        out = []
        # a group is named after its most distinctive member: the one in the fewest groups (e.g. the test file, not
        # the test framework or library linked into many programs); ties go to the earliest member
        freq = {m: sum(m in g for g in groups) for g in groups for m in g}
        for g in groups:
            flags: list[str] = []
            for rel in g:
                if rel not in by_file:
                    raise ValueError(f"link group member {rel} is not in {db}")
                for fl in entry_flags(by_file[rel]):
                    if fl not in flags:
                        flags.append(fl)
            best = min(g, key=lambda m: (freq[m], g.index(m)))
            out.append(Variant(name=_ident(str(Path(best).with_suffix(""))), flags=flags, sources=list(g)))
        names = [v.name for v in out]
        dup = {n for n in names if names.count(n) > 1}
        if dup:
            raise ValueError(f"link groups give duplicate variant names {sorted(dup)}: name them apart")
        return out
    out, seen = [], set()
    for e in entries:
        f = Path(e["file"])
        f = (Path(e.get("directory", ".")) / f).resolve() if not f.is_absolute() else f.resolve()
        try:
            rel = f.relative_to(root)
        except ValueError:
            continue                    # a TU outside the target tree
        name = _ident(str(rel.with_suffix("")))
        if name in seen:
            continue
        seen.add(name)
        out.append(Variant(name=name, flags=entry_flags(e), sources=[str(rel)]))
    return out


def link_callgraph(builds: list, out: Path) -> dict:
    """One call graph over all TUs: intra-TU edges from each unit's callees, cross-TU edges from calls to
    functions defined (with a body) in another TU. Writes out/callgraph.json."""
    defined: dict[str, str] = {}
    for b in builds:
        for u in b.units:
            defined.setdefault(u.sym, b.variant.name)
    nodes, edges, cross = [], [], []
    for b in builds:
        for u in b.units:
            nodes.append({"tu": b.variant.name, "unit": u.name, "sym": u.sym, "scope": u.scope})
            for c in u.callees:
                edges.append({"from": [b.variant.name, u.name], "to": [b.variant.name, c]})
            for x in (u.signature or {}).get("externals", []) if isinstance(u.signature, dict) else []:
                if x in defined and defined[x] != b.variant.name:
                    e = {"from": [b.variant.name, u.name], "to": [defined[x], x], "cross_tu": True}
                    edges.append(e)
                    cross.append(e)
    g = {"nodes": nodes, "edges": edges, "cross_tu_edges": len(cross)}
    write_json(out / "callgraph.json", g)
    return g

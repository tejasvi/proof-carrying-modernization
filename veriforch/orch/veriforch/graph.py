"""Call graph: strongly connected components and the bottom-up order (callees before callers)."""
from __future__ import annotations

from collections.abc import Iterable

from .model import Unit


def sccs(nodes: Iterable[str], edges: dict[str, list[str]]) -> list[list[str]]:
    """Tarjan's algorithm, iterative. Components come out callees-first (reverse topological order)."""
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    on: set[str] = set()
    stack: list[str] = []
    out: list[list[str]] = []
    counter = 0
    for root in nodes:
        if root in index:
            continue
        work = [(root, iter(edges.get(root, [])))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on.add(root)
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter
                    counter += 1
                    stack.append(w)
                    on.add(w)
                    work.append((w, iter(edges.get(w, []))))
                    advanced = True
                    break
                if w in on:
                    low[v] = min(low[v], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    comp.append(w)
                    if w == v:
                        break
                out.append(sorted(comp))
    return out


def bottom_up(units: list[Unit]) -> list[list[str]]:
    names = [u.name for u in units]
    known = set(names)
    edges = {u.name: [c for c in u.callees if c in known] for u in units}
    return sccs(names, edges)


def reachable(units: list[Unit], roots: Iterable[str]) -> set[str]:
    by = {u.name: u for u in units}
    seen: set[str] = set()
    todo = [r for r in roots if r in by]
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        todo += [c for c in by[n].callees if c in by and c not in seen]
    return seen


def depends_on_gap(units: list[Unit]) -> dict[str, list[str]]:
    """For each unit, the out-of-scope units it reaches (directly or through callees)."""
    by = {u.name: u for u in units}
    gaps = {u.name for u in units if not u.in_scope}
    res = {}
    for u in units:
        r = reachable(units, [u.name]) & gaps
        r.discard(u.name) if u.in_scope else None
        res[u.name] = sorted(r)
    return res

#!/usr/bin/env python3
"""Differential testing of the CORRESPONDING phrase (MOVE, ADD and SUBTRACT CORRESPONDING) and of
level-66 RENAMES items against GnuCOBOL 3.2.

Each random program declares a record R1 of random items (names unique within each record, up to
three levels of groups below the record; alphanumeric, numeric DISPLAY and COMP-3, numeric-edited
and USAGE INDEX items, FILLER, OCCURS 2 items and groups, alphanumeric REDEFINES items), records
R2 and R3 and the table element TR (OCCURS 3 in T1) derived from R1 by random changes (items
dropped, added, renamed, retyped, reordered, made FILLER or OCCURS, moved one group level down
under a new group), so that the corresponding pairs of two groups vary in many ways, and a record
RN of DISPLAY items followed by level-66 entries: an elementary item renamed, a group renamed and
ranges data-name-2 THROUGH data-name-3 (operands sometimes qualified, the level-66 names sometimes
equal to item names of the other records). It runs K steps, each starting with DISPLAY 'S nn':
  MOVE / ADD / SUBTRACT CORRESPONDING between groups of two records (or one group with itself,
  or two different occurrences TR (i) and TR (j)): the records, groups of the same name inside
  them, TR with a literal or data-name subscript; ADD and SUBTRACT with or without ROUNDED, with
  ON SIZE ERROR alone, with both SIZE ERROR phrases or with neither, after new values for the
  pairs' numeric items (some close to their maximum, for size errors); then every named elementary
  item of the receiver (each occurrence of OCCURS items, also the items that do not correspond);
  through a level-66 item: MOVE of a literal (alphanumeric for groups, numeric for numeric items),
  ADD of a literal with ON SIZE ERROR, MOVE to an alphanumeric work item, a comparison with a
  literal; then RN and the level-66 item.
Numeric items are displayed as a sign from a comparison with zero and the absolute value moved to
an unsigned DISPLAY item (neither the sign of a zero nor the DISPLAY conventions for signed items
are compared). GnuCOBOL (-std=ibm) and the front end + cobolrun must produce the same DISPLAY
lines.

Left out of generation (named GnuCOBOL departures or model limits, see README):
  NOT ON SIZE ERROR without ON SIZE ERROR (NIST triage cause C1: GnuCOBOL keeps the receiver, IBM
  truncates); COMP and COMP-5 items (GnuCOBOL's size error by binary capacity); SUBTRACT ROUNDED
  into COMP-3 (GnuCOBOL ignores ROUNDED); COMP-3 items with an even number of digits (pad nibble);
  MOVE CORRESPONDING pairs that IBM's table of elementary moves forbids (a non-integer numeric item
  to an alphanumeric item: GnuCOBOL moves the digits, the model is unsupported; alphabetic items:
  GnuCOBOL rejects the program) or that read alphanumeric or group bytes as numbers (alphanumeric
  -> numeric, group <-> numeric item, group <-> group with numeric or index items, numeric-edited
  -> numeric or numeric-edited: de-editing, a model limit); G-renusage (a level-66 entry renaming
  one COMP, COMP-3 or COMP-5 item: GnuCOBOL gives the level-66 item DISPLAY storage); operands
  that may share storage (unsupported in the model).

usage: corrtest.py [--n N] [--seed S] [--k K] [--out DIR] [--root TREE] [--show K] [--run F.cob...]
"""
import argparse
import copy
import json
import os
import random
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from inspecttest import wrap  # noqa: E402

POOL = ["A", "B", "C", "D", "E", "F", "G", "H", "J", "K", "L", "M"]
EDITED = ["ZZ9", "Z9.99", "-ZZ9.9", "ZZZ9", "999.99", "+ZZ9"]
LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


class It:
    """An item: kind 'grp' (group), 'x' (PIC X(length)), 'n' (numeric: digits in all, scale,
    signed, packed = COMP-3), 'e' (numeric-edited picture pic), 'ix' (USAGE INDEX)."""

    def __init__(self, name, kind, **kw):
        self.name, self.kind = name, kind
        self.children = []
        self.occurs = None
        self.redef = None
        self.filler = False
        self.length = 0
        self.digits = self.scale = 0
        self.signed = self.packed = False
        self.pic = None
        self.value = None
        self.parent = None
        self.__dict__.update(kw)


def size(it):
    if it.kind == "grp":
        return sum(size(c) * (c.occurs or 1) for c in it.children if c.redef is None)
    if it.kind == "x":
        return it.length
    if it.kind == "n":
        return it.digits // 2 + 1 if it.packed else it.digits
    if it.kind == "e":
        return len(it.pic)
    return 4


def walk(it):
    yield it
    for c in it.children:
        yield from walk(c)


def maxv(it):
    return 10 ** it.digits - 1


def numlit(v, scale):
    s = str(abs(v)).rjust(scale + 1, "0")
    t = s[:-scale] + "." + s[-scale:] if scale else s
    return ("-" if v < 0 else "") + t


def rnd_value(rng, it, big=False):
    m = maxv(it)
    if big:
        v = rng.randint(m * 7 // 10, m)
    else:
        v = rng.randint(0, m)
    if it.signed and rng.random() < 0.5 and v != 0:
        v = -v
    return v


def elem(rng, name, display_only=False):
    r = rng.random()
    if r < 0.35:
        return It(name, "x", length=rng.randint(1, 4))
    if r < 0.85:
        packed = not display_only and rng.random() < 0.3
        while True:
            d, s = rng.randint(1, 5), rng.choice([0, 0, 1, 2])
            if d + s <= 6 and not (packed and (d + s) % 2 == 0):
                break
        return It(name, "n", digits=d + s, scale=s, signed=rng.random() < 0.5, packed=packed)
    return It(name, "e", pic=rng.choice(EDITED))


class Gen:
    def __init__(self, rng, k):
        self.rng, self.k = rng, k
        self.step = 0
        self.labels = 0
        self.stats = {}

    def bump(self, key, n=1):
        self.stats[key] = self.stats.get(key, 0) + n

    # ------------------------------------------------------------------ data
    def group(self, depth, used):
        rng = self.rng
        n = rng.randint(2, 4) if depth == 0 else rng.randint(1, 3)
        kids = []
        for _ in range(n):
            free = [x for x in POOL if x not in used]
            if not free:
                break
            nm = rng.choice(free)
            used.add(nm)
            if depth < 2 and rng.random() < 0.35:
                g = It(nm, "grp")
                g.children = self.group(depth + 1, used)
                kids.append(g if g.children else elem(rng, nm))
            else:
                kids.append(elem(rng, nm))
        return kids

    def mutate(self, kids, depth, used, in_occ):
        rng = self.rng
        out = []
        for c in kids:
            if c.kind == "ix":
                # (index data items are never copied: G-corrindex, see specials)
                continue
            c2 = copy.deepcopy(c)
            r = rng.random()
            if r < 0.08:
                continue
            if r < 0.14:
                free = [x for x in POOL if x not in used]
                if free:
                    c2.name = rng.choice(free)
            elif r < 0.22 and c2.kind != "grp":
                c2 = elem(rng, c2.name)
                c2.filler = c.filler
            elif r < 0.27:
                c2.filler = True
            elif r < 0.33 and depth < 2:
                free = [x for x in POOL if x not in used and x != c2.name]
                if free:
                    w = It(rng.choice(free), "grp")
                    used.add(w.name)
                    w.children = [c2]
                    c2 = w
            elif r < 0.39 and not in_occ and c2.kind != "ix":
                c2.occurs = 2
            elif r < 0.45 and c2.kind == "grp" and c2.redef is None:
                # a group against an elementary item of the same name
                c2 = It(c2.name, "x", length=min(size(c2), 9), filler=c2.filler, occurs=c2.occurs)
            elif r < 0.51 and c2.kind == "x" and c2.redef is None and depth < 2:
                free = [x for x in POOL if x not in used]
                if len(free) >= 2:
                    a, b = rng.sample(free, 2)
                    used.update((a, b))
                    c2 = It(c2.name, "grp", filler=c2.filler, occurs=c2.occurs,
                            children=[It(a, "x", length=rng.randint(1, 3)), It(b, "x", length=rng.randint(1, 3))])
            if c2.kind == "grp":
                c2.children = self.mutate(c2.children, depth + 1, used, in_occ or c2.occurs is not None)
                if not c2.children:
                    c2 = elem(rng, c2.name)
            out.append(c2)
        if rng.random() < 0.3:
            free = [x for x in POOL if x not in used]
            if free:
                nm = rng.choice(free)
                used.add(nm)
                out.insert(rng.randint(0, len(out)), elem(rng, nm))
        if rng.random() < 0.3:
            rng.shuffle(out)
        return out or [elem(rng, rng.choice([x for x in POOL if x not in used] or ["M"]))]

    def specials(self, kids, depth, used, in_occ):
        """FILLER, REDEFINES (an alphanumeric item over a preceding alphanumeric-only sibling of the
        same size) and USAGE INDEX items, at random."""
        rng = self.rng
        out = []
        for c in kids:
            out.append(c)
            if c.kind == "grp":
                c.children = self.specials(c.children, depth + 1, used, in_occ or c.occurs is not None)
            if c.redef is None and not c.filler and rng.random() < 0.15 and \
                    all(x.kind in ("x", "grp") for x in walk(c)) and c.occurs is None:
                free = [x for x in POOL if x not in used]
                if free:
                    nm = rng.choice(free)
                    used.add(nm)
                    out.append(It(nm, "x", length=size(c), redef=c.name))
        if rng.random() < 0.15:
            out.append(It("FILLER", "x", length=rng.randint(1, 3), filler=True))
        if rng.random() < 0.12 and not in_occ:
            # a name of its own (never corresponding: GnuCOBOL moves and adds index data items in
            # MOVE / ADD CORRESPONDING, IBM leaves them out: G-corrindex)
            self.ixn = getattr(self, "ixn", 0) + 1
            out.append(It(f"IX{self.ixn}", "ix"))
        return out

    def dedupe(self, rec):
        """Names unique within the record (FILLER aside), so that NAME OF RECORD is a unique
        reference; a REDEFINES item keeps following the item it redefines."""
        seen = set()
        for it in walk(rec):
            if it is rec or it.filler:
                continue
            if it.name in seen:
                it.filler = True if it.redef is None and it.kind != "ix" else it.filler
                if it.kind == "ix" or it.redef is not None:
                    free = [x for x in POOL if x not in seen]
                    it.name = free[0] if free else it.name
            if not it.filler:
                seen.add(it.name)
        for it in walk(rec):
            for i, c in enumerate(it.children):
                if c.redef is not None:
                    prev = it.children[i - 1] if i > 0 else None
                    if prev is None or prev.filler or prev.redef is not None or size(prev) != c.length \
                            or prev.occurs is not None or c.occurs is not None or c.kind != "x" \
                            or not all(x.kind in ("x", "grp") for x in walk(prev)):
                        c.redef = None
                        c.filler = True
                    else:
                        c.redef = prev.name

    def values(self, rec, in_redef=False):
        rng = self.rng
        for c in rec.children:
            under = in_redef or c.redef is not None
            if c.kind == "x" and not under:
                c.value = "".join(rng.choice(LETTERS) for _ in range(c.length))
            elif c.kind == "n" and not under:
                c.value = rnd_value(rng, c, rng.random() < 0.3)
            if c.kind == "grp":
                self.values(c, under)

    def link(self, rec):
        for it in walk(rec):
            for c in it.children:
                c.parent = it

    def records(self):
        rng = self.rng
        used = set()
        r1 = It("R1", "grp", children=self.group(0, used))
        r1.children = self.specials(r1.children, 0, used, False)
        recs = [r1]
        for nm in ("R2", "R3"):
            used = {x.name for x in walk(r1) if x is not r1}
            r = It(nm, "grp", children=self.mutate(r1.children, 0, used, False))
            r.children = self.specials(r.children, 0, used, False)
            recs.append(r)
        used = {x.name for x in walk(r1) if x is not r1}
        tr = It("TR", "grp", occurs=3, children=self.mutate(r1.children, 0, used, True))
        tr.children = self.specials(tr.children, 0, used, True)
        t1 = It("T1", "grp", children=[tr])
        recs.append(t1)
        for r in recs:
            self.dedupe(r if r.name != "T1" else tr)
            self.values(r)
            self.link(r)
        self.recs = recs
        self.tr = tr
        self.rn = self.rn_record()
        self.link(self.rn)

    def rn_record(self):
        """RN: DISPLAY items (names N1.. and groups NG1..), then level-66 entries Q1.. over an
        elementary item, a group, and ranges."""
        rng = self.rng
        cnt = [0, 0]

        def kids(depth):
            out = []
            for _ in range(rng.randint(2, 3) if depth == 0 else rng.randint(1, 3)):
                if depth < 2 and rng.random() < 0.35:
                    cnt[1] += 1
                    g = It(f"NG{cnt[1]}", "grp")
                    g.children = kids(depth + 1)
                    out.append(g)
                else:
                    cnt[0] += 1
                    out.append(elem(rng, f"N{cnt[0]}", display_only=True))
            return out
        rn = It("RN", "grp", children=kids(0))
        self.values(rn)
        self.link(rn)
        order = [x for x in walk(rn) if x is not rn]
        leaves = [x for x in order if x.kind != "grp"]
        groups = [x for x in order if x.kind == "grp"]
        ren = []
        k = 0

        def qual(it):
            # data-name-2 / 3, sometimes qualified
            if it.parent is not rn and rng.random() < 0.4:
                return f"{it.name} OF {it.parent.name}"
            return it.name if rng.random() < 0.7 else f"{it.name} OF RN"

        def newname():
            nonlocal k
            k += 1
            return rng.choice(POOL) if rng.random() < 0.25 else f"Q{k}"
        names = set()
        for _ in range(rng.randint(1, 3)):
            r = rng.random()
            nm = newname()
            while nm in names:
                nm = f"Q{k}{len(names)}"
            names.add(nm)
            if r < 0.35:
                a = rng.choice(leaves)
                ren.append({"name": nm, "a": a, "b": None, "text": f"66  {nm} RENAMES {qual(a)}."})
            elif r < 0.55 and groups:
                a = rng.choice(groups)
                ren.append({"name": nm, "a": a, "b": None, "text": f"66  {nm} RENAMES {qual(a)}."})
            else:
                # a THROUGH b: b starts no earlier and ends no earlier than a, b not inside a
                i = rng.randrange(len(order))
                a = order[i]
                cands = [b for b in order[i + 1:] if a not in b_ancestors(b) and
                         offset(b) >= offset(a) and offset(b) + size(b) >= offset(a) + size(a)]
                if not cands:
                    continue
                b = rng.choice(cands)
                kw = rng.choice(["THRU", "THROUGH"])
                ren.append({"name": nm, "a": a, "b": b,
                            "text": f"66  {nm} RENAMES {qual(a)} {kw} {qual(b)}."})
        rn.renames = ren
        return rn

    # ------------------------------------------------------------------ references
    def rec_of(self, it):
        while it.parent is not None and it.name != "TR":
            it = it.parent
        return it

    def ref(self, it, subs=()):
        """NAME OF RECORD (or OF TR) with subscripts."""
        top = self.rec_of(it)
        s = list(subs)
        r = it.name if it is top else f"{it.name} OF {top.name}"
        return r + (f" ({' '.join(s)})" if s else "")

    def leaves_of(self, g):
        """(item, extra subscripts) of the named elementary items to display under g: every
        occurrence of OCCURS items; not under FILLER or REDEFINES items, no index data items."""
        out = []

        def go(it, occ):
            for c in it.children:
                if c.filler or c.redef is not None or c.kind == "ix":
                    continue
                occs = [occ + [str(j)] for j in range(1, (c.occurs or 1) + 1)] if c.occurs else [occ]
                for o in occs:
                    if c.kind == "grp":
                        go(c, o)
                    else:
                        out.append((c, o))
        go(g, [])
        return out

    def show(self, it, subs):
        """Statements displaying one elementary item."""
        self.labels += 1
        r = self.ref(it, subs)
        lab = f"L{self.labels % 1000:03d}"
        if it.kind == "n":
            return [f"MOVE {r} TO DV",
                    f"IF {r} < 0 MOVE '-' TO DS ELSE MOVE '+' TO DS END-IF",
                    f"DISPLAY '{lab} ' DS DV"]
        return [f"DISPLAY '{lab} ' {r}"]

    # ------------------------------------------------------------------ CORRESPONDING
    def operands(self):
        """Groups usable as CORRESPONDING operands: (item, subscripts of the operand)."""
        out = []
        for r in self.recs + [self.rn]:
            for it in walk(r):
                if it.kind != "grp" or it.filler or it.redef is not None or it.name == "T1":
                    continue
                if any(a.occurs for a in [it] + anc(it) if a.name != "TR"):
                    continue
                if it.name == "TR" or self.rec_of(it).name == "TR":
                    for s in ("1", "2", "3", "SUBX"):
                        out.append((it, [s]))
                else:
                    out.append((it, []))
        return out

    def pick_operands(self):
        rng = self.rng
        ops = self.operands()
        tops = ("R1", "R2", "R3", "TR")
        top_ops = [o for o in ops if o[0].name in tops]
        x1 = rng.choice(top_ops if rng.random() < 0.55 else ops)
        r = rng.random()
        if r < 0.05:
            return (x1, (x1[0], list(x1[1]))) if self.rec_of(x1[0]) is not self.rn else None
        if x1[0].name in tops:
            # the records derived from R1 share most names
            same = [o for o in ops if o[0].name in tops and o[0] is not x1[0]]
        else:
            same = [o for o in ops if o[0].name == x1[0].name and o[0] is not x1[0]]
        if r < 0.75 and same:
            x2 = rng.choice(same)
        else:
            x2 = rng.choice(ops)
        t1, t2 = self.rec_of(x1[0]), self.rec_of(x2[0])
        if t2 is self.rn:
            # RN is displayed whole, so a negative zero stored there would show its sign byte
            # (GnuCOBOL keeps -0): RN only sends
            return None
        if t1 is t2:
            if t1.name != "TR":
                return None
            # two occurrences of TR: only literal and different subscripts (disjoint)
            if "SUBX" in x1[1] + x2[1] or x1[1] == x2[1]:
                return None
        return x1, x2

    def pairs(self, g1, g2, arith):
        out = []

        def ok(c):
            return not c.filler and c.redef is None and c.occurs is None and c.kind != "ix"
        k2 = [c for c in g2.children if ok(c)]
        for c1 in [c for c in g1.children if ok(c)]:
            m = [c2 for c2 in k2 if c2.name == c1.name]
            if not m:
                continue
            c2 = m[0]
            if c1.kind == "grp" and c2.kind == "grp":
                out += self.pairs(c1, c2, arith)
            elif not arith or (c1.kind == "n" and c2.kind == "n"):
                out.append((c1, c2))
        return out

    def move_ok(self, a, b):
        """The pair's MOVE is permitted by IBM and reads no bytes as numbers in another way than
        the two sides agree on (see the module docstring)."""
        def alnum_group(g):
            return g.kind == "grp" and all(x.kind in ("x", "grp") for x in walk(g))
        if a.kind == "grp" or b.kind == "grp":
            g, e = (a, b) if a.kind == "grp" else (b, a)
            return alnum_group(g) and e.kind == "x"
        if a.kind == "x":
            return b.kind == "x"
        if a.kind == "n":
            return b.kind in ("n", "e") or (b.kind == "x" and a.scale == 0)
        if a.kind == "e":
            return b.kind == "x"
        return False

    def st_corr(self):
        rng = self.rng
        p = self.pick_operands()
        if p is None:
            return None
        (g1, s1), (g2, s2) = p
        verb = rng.choices(["MOVE", "ADD", "SUBTRACT"], [4, 3, 3])[0]
        arith = verb != "MOVE"
        pairs = self.pairs(g1, g2, arith)
        if not arith and not all(self.move_ok(a, b) for a, b in pairs):
            return None
        o1, o2 = self.ref(g1, s1), self.ref(g2, s2)
        lines = []
        if not arith:
            for a, _ in pairs:
                if a.kind == "x" and rng.random() < 0.3:
                    lines.append(f"MOVE '{''.join(rng.choice(LETTERS) for _ in range(a.length))}' "
                                 f"TO {self.ref(a, s1)}")
            lines.append(f"MOVE CORRESPONDING {o1} TO {o2}")
            self.bump("move")
        else:
            for a, b in pairs:
                for it, s in ((a, s1), (b, s2)):
                    if rng.random() < 0.6:
                        v = rnd_value(rng, it, rng.random() < 0.4)
                        lines.append(f"MOVE {numlit(v, it.scale)} TO {self.ref(it, s)}")
            rounded = rng.random() < 0.4
            if verb == "SUBTRACT" and any(b.packed for _, b in pairs):
                rounded = False
            r = rng.random()
            n = self.step
            phr = ""
            if pairs and r < 0.3:
                phr = f" ON SIZE ERROR DISPLAY 'E {n:02d}'"
                self.bump("on-size")
            elif pairs and r < 0.55:
                phr = f" ON SIZE ERROR DISPLAY 'E {n:02d}' NOT ON SIZE ERROR DISPLAY 'K {n:02d}'"
                self.bump("both-size")
            word = "TO" if verb == "ADD" else "FROM"
            end = "END-ADD" if verb == "ADD" else "END-SUBTRACT"
            lines.append(f"{verb} {rng.choice(['CORRESPONDING', 'CORR'])} {o1} {word} {o2}"
                         f"{' ROUNDED' if rounded else ''}{phr} {end}")
            self.bump(verb.lower())
            if rounded:
                self.bump("rounded")
        self.bump("pairs", len(pairs))
        if not pairs:
            self.bump("no-pairs")
        if s1 or s2:
            self.bump("subscripted")
        if g1 is g2 and s1 == s2:
            self.bump("same-operand")
        self.bump("group-pairs", sum(1 for a, b in pairs if "grp" in (a.kind, b.kind)))
        # names that occur under both operands but do not correspond (other qualifiers, FILLER,
        # REDEFINES, OCCURS, index data items, a group against an elementary item in ADD / SUBTRACT)
        n1 = {x.name for x in walk(g1) if x is not g1 and not x.filler}
        n2 = {x.name for x in walk(g2) if x is not g2 and not x.filler}
        paired = {a.name for a, _ in pairs}
        self.bump("names-not-paired", len((n1 & n2) - paired))
        for it, o in self.leaves_of(g2):
            lines += self.show(it, s2 + o)
        return lines

    # ------------------------------------------------------------------ RENAMES
    def st_ren(self):
        rng = self.rng
        if not self.rn.renames:
            return None
        q = rng.choice(self.rn.renames)
        a, b = q["a"], q["b"]
        # (a level-66 name equal to an item name of another record must be qualified)
        nm = q["name"] if rng.random() < 0.6 and q["name"] not in POOL else f"{q['name']} OF RN"
        elementary = b is None and a.kind != "grp"
        area = [x for x in walk(self.rn) if x.kind != "grp" and in_area(x, q)]
        numeric_inside = any(x.kind == "n" for x in area)
        ln = size(a) if b is None else offset(b) + size(b) - offset(a)
        n = self.step
        lines = []
        r = rng.random()
        if elementary and a.kind == "n":
            if r < 0.4:
                v = rnd_value(rng, a, rng.random() < 0.3)
                lines.append(f"MOVE {numlit(v, a.scale)} TO {nm}")
            elif r < 0.7:
                v = rnd_value(rng, a, rng.random() < 0.5)
                lines.append(f"ADD {numlit(v, a.scale)} TO {nm} ON SIZE ERROR DISPLAY 'E {n:02d}' END-ADD")
            elif a.scale == 0:
                lines += [f"MOVE {nm} TO W", "DISPLAY 'W ' W"]
            else:
                v = rnd_value(rng, a)
                lines.append(f"IF {nm} = {numlit(v, a.scale)} DISPLAY 'T {n:02d}' ELSE DISPLAY "
                             f"'F {n:02d}' END-IF")
            self.bump("ren-num")
        elif elementary and a.kind == "e":
            lines += [f"MOVE {nm} TO W", "DISPLAY 'W ' W"]
            self.bump("ren-edited")
        else:
            if r < 0.5:
                if numeric_inside or any(x.kind == "e" for x in area):
                    lit = "".join(rng.choice("0123456789") for _ in range(ln + rng.randint(0, 2)))
                else:
                    lit = "".join(rng.choice(LETTERS) for _ in range(rng.randint(1, ln + 2)))
                lines.append(f"MOVE '{lit}' TO {nm}")
            elif r < 0.75:
                lines += [f"MOVE {nm} TO W", "DISPLAY 'W ' W"]
            else:
                lit = "".join(rng.choice(LETTERS) for _ in range(rng.randint(1, ln)))
                lines.append(f"IF {nm} = '{lit}' DISPLAY 'T {n:02d}' ELSE DISPLAY 'F {n:02d}' END-IF")
            self.bump("ren-thru" if b is not None else ("ren-alnum" if a.kind == "x" else "ren-group"))
        lines.append("DISPLAY 'RN ' RN")
        if elementary and a.kind == "n":
            self.labels += 1
            lines += [f"MOVE {nm} TO DV", f"IF {nm} < 0 MOVE '-' TO DS ELSE MOVE '+' TO DS END-IF",
                      f"DISPLAY 'Q ' DS DV"]
        else:
            lines.append(f"DISPLAY 'Q ' {nm}")
        return lines

    # ------------------------------------------------------------------ program
    def data_lines(self):
        out = ["       01  DV PIC 9(9)V9(4).", "       01  DS PIC X.", "       01  W PIC X(12).",
               "       01  SUBX PIC 9 VALUE 2."]

        def emit(it, level, ind):
            nm = "FILLER" if it.filler else it.name
            s = f"{' ' * ind}{level:02d}  {nm}"
            if it.redef:
                s += f" REDEFINES {it.redef}"
            if it.occurs:
                s += f" OCCURS {it.occurs}"
            if it.kind == "grp":
                out.append(s + ".")
                for c in it.children:
                    emit(c, level + 5 if level > 1 else 5, ind + 4)
                return
            if it.kind == "x":
                s += f" PIC X({it.length})"
                if it.value is not None:
                    s += f" VALUE '{it.value}'"
            elif it.kind == "n":
                i = it.digits - it.scale
                s += f" PIC {'S' if it.signed else ''}9({i})" + (f"V9({it.scale})" if it.scale else "")
                if it.packed:
                    s += " COMP-3"
                if it.value is not None:
                    s += f" VALUE {numlit(it.value, it.scale)}"
            elif it.kind == "e":
                s += f" PIC {it.pic}"
            else:
                s += " USAGE INDEX"
            out.append(s + ".")
        for r in self.recs + [self.rn]:
            emit(r, 1, 7)
        for q in self.rn.renames:
            out.append("       " + q["text"])
        return out

    def program(self):
        rng = self.rng
        self.records()
        body = []
        # numeric-edited items get a value first (no VALUE clause)
        for r in self.recs + [self.rn]:
            for it in walk(r):
                if it.kind == "e" and not any(a.filler or a.redef for a in [it] + anc(it)):
                    for o in occ_subs(it):
                        body.append(f"MOVE ZERO TO {self.ref(it, o)}")
        for i in range(self.k):
            self.step = i
            for _ in range(200):
                lines = self.st_ren() if rng.random() < 0.25 else self.st_corr()
                if lines is not None:
                    break
            else:
                lines = ["CONTINUE"]
            body += [f"DISPLAY 'S {i:02d}'"] + lines
        lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. CORRT.",
                 "       DATA DIVISION.", "       WORKING-STORAGE SECTION."] + self.data_lines() + \
                ["       PROCEDURE DIVISION.", "       P0."]
        for s in body:
            lines += wrap(s)
        lines.append("           STOP RUN.")
        for l in lines:
            assert len(l) <= 72, l
        return "\n".join(lines) + "\n"


def walk_list(kids):
    for k in kids:
        yield from walk(k)


def anc(it):
    out = []
    p = it.parent
    while p is not None:
        out.append(p)
        p = p.parent
    return out


def b_ancestors(it):
    return anc(it)


def occ_subs(it):
    """Subscript lists for every occurrence of it (outermost first)."""
    dims = [a.occurs for a in reversed([it] + anc(it)) if a.occurs]
    subs = [[]]
    for n in dims:
        subs = [s + [str(j)] for s in subs for j in range(1, n + 1)]
    return subs


def offset(it):
    """Offset of it from the start of its record (no tables in RN)."""
    off = 0
    while it.parent is not None:
        p = it.parent
        o = 0
        for c in p.children:
            if c is it:
                break
            if c.redef is None:
                o += size(c) * (c.occurs or 1)
        off += o
        it = p
    return off


def in_area(x, q):
    a, b = q["a"], q["b"]
    lo = offset(a)
    hi = lo + size(a) if b is None else offset(b) + size(b)
    return lo <= offset(x) and offset(x) + size(x) <= hi


# ---------------------------------------------------------------------- running
def run(root, src, base):
    cobc = os.path.join(root, "scripts", "cobc.sh")
    lib = os.path.join(root, "third_party", "gnucobol", "usr", "lib", "x86_64-linux-gnu")
    fe = os.environ.get("COBOLFE", os.path.join(root, "tools", "cobolfe", "cobolfe.py"))
    crun = os.path.join(root, ".lake", "build", "bin", "cobolrun")
    if src is not None:
        with open(base + ".cob", "w") as fh:
            fh.write(src)
    c = subprocess.run([cobc, "-x", "-std=ibm", "-o", base, base + ".cob"], capture_output=True, text=True,
                       timeout=120)
    if c.returncode != 0:
        return None, "cobc: " + c.stderr
    env = dict(os.environ, LD_LIBRARY_PATH=lib)
    r = subprocess.run([base], capture_output=True, env=env, timeout=20)
    g = r.stdout.decode("latin-1").splitlines()
    f = subprocess.run([sys.executable, "-I", "-B", fe, base + ".cob", "--profile", "gnucobol", "--main", "-o",
                        base + ".fe.json"], capture_output=True, text=True, timeout=120)
    if f.returncode != 0:
        return (g, None), "frontend: " + f.stderr.strip().splitlines()[-1][:300]
    l = subprocess.run([crun, base + ".fe.json"], capture_output=True, text=True, timeout=60)
    if l.returncode != 0:
        return (g, None), "cobolrun: " + l.stderr[:300]
    res = json.loads(l.stdout)
    m = [bytes(e["display"]).decode("latin-1") for e in res["out"] if "display" in e]
    if not res["signal"].startswith("stop"):
        m.append("<model: " + res["signal"] + ">")
    return (g, m), None


def classify(outs, err):
    if err is not None:
        return "frontend-error" if err.startswith("frontend") else ("cobc-error" if err.startswith("cobc")
                                                                    else "cobolrun-error")
    g, m = outs
    if g == m:
        return "ok"
    if m and m[-1].startswith("<model: fault:Cobol.Fault.unsupported"):
        return "model-unsupported"
    return "mismatch"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=12)
    ap.add_argument("--out", required=True)
    ap.add_argument("--root", default=os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                                   "..", "..")))
    ap.add_argument("--show", type=int, default=3)
    ap.add_argument("--run", nargs="*", help="hand-written programs instead of random ones")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=False)
    tally, shown, stats = {}, 0, {}
    res = open(os.path.join(args.out, "results.jsonl"), "w")
    if args.run:
        for p in args.run:
            base = os.path.join(args.out, os.path.basename(p)[:-4])
            with open(p) as fh, open(base + ".cob", "w") as oh:
                oh.write(fh.read())
            outs, err = run(args.root, None, base)
            st = classify(outs, err)
            tally[st] = tally.get(st, 0) + 1
            res.write(json.dumps({"case": p, "status": st, "err": err}) + "\n")
            print(f"{p}: {st}" + (f" ({err})" if err else ""))
            if st != "ok" and outs is not None and outs[1] is not None:
                g, m = outs
                i = next((j for j, (x, y) in enumerate(zip(g, m)) if x != y), min(len(g), len(m)))
                print(f"  first difference at line {i}: gnucobol {g[i:i + 1]!r} model {m[i:i + 1]!r}")
        print(json.dumps({"tally": tally}))
        return 0
    rng = random.Random(args.seed)
    for p in range(args.n):
        gen = Gen(rng, args.k)
        src = gen.program()
        for key, v in gen.stats.items():
            stats[key] = stats.get(key, 0) + v
        base = os.path.join(args.out, f"corr_{args.seed}_{p}")
        outs, err = run(args.root, src, base)
        st = classify(outs, err)
        tally[st] = tally.get(st, 0) + 1
        if outs is not None:
            g = outs[0]
            stats["gc-size-errors"] = stats.get("gc-size-errors", 0) + sum(1 for x in g if x.startswith("E "))
            stats["gc-no-size-errors"] = stats.get("gc-no-size-errors", 0) + sum(1 for x in g if x.startswith("K "))
            stats["display-lines"] = stats.get("display-lines", 0) + len(g)
        res.write(json.dumps({"case": p, "status": st, "err": err}) + "\n")
        if st != "ok" and shown < args.show:
            shown += 1
            if outs is None or outs[1] is None:
                print(f"program {p}: {st}: {err[:300]}")
            else:
                g, m = outs
                i = next((j for j, (x, y) in enumerate(zip(g, m)) if x != y), min(len(g), len(m)))
                print(f"program {p}: {st}: first difference at line {i}: gnucobol {g[i:i + 1]!r} model "
                      f"{m[i:i + 1]!r} ({len(g)} vs {len(m)} lines)")
    res.close()
    print(json.dumps({"tally": tally, "coverage": dict(sorted(stats.items()))}))
    return 0 if tally.get("ok", 0) == args.n else 1


sys.exit(main())

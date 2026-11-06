#!/usr/bin/env python3
"""Differential testing of index data items (USAGE INDEX) and index names.

Each random program declares tables with index names (element lengths 1, 2, 3 and 4; one table
of 3 rows of 4 elements) and index data items: 77-level items, the two items of a USAGE INDEX
group, an item inside a record between two fields (with a REDEFINES of the field after it), the
same layout in a second record, and a table of 4 index data items. It runs K steps, each
starting with DISPLAY 'S nn':
  SET index-name TO literal / integer item / index name, SET index-name UP / DOWN BY;
  SET index data item TO index name / index data item, SET index name TO index data item, also
  for elements of the table of index data items (literal and data-name subscripts);
  comparisons of an index data item with an index name or another index data item (every
  relational operator, abbreviated combined relations), and of index names;
  table elements through index names (one and two levels, relative indexing);
  SEARCH VARYING an index data item (one or two WHEN phrases, with and without AT END);
  PERFORM VARYING index names (inline and out of line, TEST BEFORE and AFTER, FROM a literal, an
  integer item or an index name, BY 1, 2, -1 or an integer item, one level or with AFTER a
  second index name or an integer item; UNTIL conditions on the index and on an index data item,
  with a guard counter), PERFORM VARYING an integer item FROM an index name;
  a group MOVE between the two records with an index data item at the same offset;
  INITIALIZE of a group holding index data items, then its other fields;
  LENGTH OF those groups and of an index data item, and a MOVE to the field after the index data
  item displayed through the REDEFINES (the item's 4 bytes place that field).
Index names and index data items are displayed through integer items after every change.
GnuCOBOL (-std=ibm) and the front end + cobolrun must produce the same DISPLAY lines.

Each index data item exchanges values only with index names of tables of one element length
(IBM keeps an index value as a displacement, (occurrence - 1) x element length, and moves it to
and from index data items without conversion; GnuCOBOL keeps occurrence numbers, and so does the
model: the two agree exactly then). With --mixed, one step of each program moves a value between
an index data item and an index name of another element length: the model must stop with
`unsupported` at the first statement that touches the items exchanging values with it (every
display before that agrees with GnuCOBOL, the last step marker shown is that statement's step).

Left out of generation (GnuCOBOL departs from IBM's documented rule):
  G-initindex       INITIALIZE sets index data items to 0 (also under REPLACING NUMERIC BY v,
                    where they take v); IBM excludes "any identifiers that are not valid receiving
                    operands of a MOVE statement", so they keep their values. After an INITIALIZE
                    an index data item is not read until it is SET again.
  G-search-varying  SEARCH VARYING an index data item sets it to the search index's occurrence
                    number at each step; IBM increases it "by the same amount" as the index. Each
                    SEARCH here starts with the item equal to the search index.
Also left out: reading an index data item before any SET (IBM: "If the initial value is not
explicitly specified, the value is unpredictable"; GnuCOBOL gives 0, the model stops), and index
values outside a table's occurrences except as the final values of loops (IBM: values must
correspond to occurrence numbers).

usage: indextest.py [--n N] [--seed S] [--k K] [--out DIR] [--show K] [--mixed]
"""
import argparse
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from inspecttest import run, wrap  # noqa: E402

# index name: (table element, occurrences, element length)
IDX = {"IA": ("TAE", 6, 2), "IA2": ("TAE", 6, 2), "IB": ("TBE", 8, 2), "IC": ("TCE", 5, 3),
       "ID1": ("TDR", 3, 4), "ID2": ("TDE", 4, 1)}
# display-only index names, one per element length
SCRATCH = {2: "IS2", 3: "IS3", 4: "IS4", 1: "IS1"}
OCC = dict({n: v[1] for n, v in IDX.items()}, IS2=6, IS3=5, IS4=3, IS1=4)
LEN = dict({n: v[2] for n, v in IDX.items()}, IS2=2, IS3=3, IS4=4, IS1=1)
# index data items and the element length of the index names they exchange values with
ITEMS = {"X1": 2, "X2": 2, "XK1": 2, "XK2": 3, "XRX": 3, "YRX": 3, "X3": 1}
XT = [("XTX", k) for k in range(1, 5)]
OPS = ["=", "NOT =", "<", ">", "<=", ">=", "EQUAL TO", "GREATER THAN", "LESS THAN", "NOT <",
       "NOT >", "IS NOT EQUAL TO", "GREATER THAN OR EQUAL TO"]
GUARD = "CNT > 30"

DATA = """\
       01  TA.
           05  TAE PIC XX OCCURS 6 INDEXED BY IA IA2 IS2.
       01  TB.
           05  TBE PIC XX OCCURS 8 INDEXED BY IB.
       01  TC.
           05  TCE PIC XXX OCCURS 5 INDEXED BY IC IS3.
       01  TD.
           05  TDR OCCURS 3 INDEXED BY ID1 IS4.
               10  TDE PIC X OCCURS 4 INDEXED BY ID2 IS1.
       77  X1 USAGE INDEX.
       77  X2 INDEX.
       77  X3 USAGE IS INDEX.
       01  XG USAGE INDEX.
           05  XK1.
           05  XK2.
       01  XR.
           05  XA PIC X VALUE "a".
           05  XRX USAGE INDEX.
           05  XB PIC X(3) VALUE "bcd".
       01  XR2 REDEFINES XR.
           05  FILLER PIC X(5).
           05  XB2 PIC X(3).
       01  XS.
           05  YA PIC X VALUE "y".
           05  YRX USAGE INDEX.
           05  YB PIC X(3) VALUE "yyy".
       01  XT.
           05  XTE OCCURS 4.
               10  XTC PIC X VALUE "t".
               10  XTX USAGE INDEX.
       01  N PIC S9(4) VALUE 0.
       01  V2 PIC S9(3) VALUE 0.
       01  E PIC -9999.
       01  W1 PIC 9 VALUE 1.
       01  W2 PIC S9(3) VALUE 1.
       01  K PIC 9 VALUE 1.
       01  CNT PIC 9(4) VALUE 0.
"""
TABS = {"TAE": [f"a{i}" for i in range(1, 7)], "TBE": [f"b{i}" for i in range(1, 9)],
        "TCE": [f"c0{i}" for i in range(1, 6)]}


def cls(x):
    return 4 if isinstance(x, tuple) else ITEMS[x]


def ref(x):
    return f"XTX ({x[1]})" if isinstance(x, tuple) else x


class Gen:
    def __init__(self, rng, mixed):
        self.rng = rng
        self.idx = {n: None for n in OCC}       # occurrence number, "?" (set, not tracked) or None
        self.ixd = {x: None for x in list(ITEMS) + XT}
        self.div = set()                        # items GnuCOBOL changed (G-initindex) since their SET
        self.tab = {t: list(v) for t, v in TABS.items()}
        self.paras = []
        self.nlabel = 0
        self.mixed = mixed
        # union-find of index data items, as the front end's: the elements of the table XTX are
        # one item
        self.uf = {x: XT[0] for x in XT[1:]}
        self.touched = []                       # per step: index data items touched
        self.mix_item = None

    # -------------------------------------------------------------- bookkeeping
    def find(self, x):
        while self.uf.get(x, x) != x:
            x = self.uf[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.uf[ra] = rb

    def touch(self, *xs):
        self.touched[-1].update(xs)

    def readable(self, x):
        return self.ixd[x] is not None and x not in self.div

    def setv(self, x, v):
        self.ixd[x] = v
        self.div.discard(x)

    def names(self, length=None, known=False, inrange=False):
        out = []
        for n in IDX:
            if length is not None and LEN[n] != length:
                continue
            v = self.idx[n]
            if known and not isinstance(v, int):
                continue
            if inrange and not (isinstance(v, int) and 1 <= v <= OCC[n]):
                continue
            out.append(n)
        return out

    def items(self, length=None, readable=False):
        return [x for x in self.ixd if (length is None or cls(x) == length) and
                (not readable or self.readable(x))]

    def label(self):
        self.nlabel += 1
        return f"L{self.nlabel}"

    # -------------------------------------------------------------- displays
    def show_idx(self, n):
        return [f"SET N TO {n}", "MOVE N TO E", f"DISPLAY '{self.label()} {n} ' E"]

    def show_ixd(self, x):
        s = SCRATCH[cls(x)]
        self.idx[s] = self.ixd[x]
        self.touch(x)
        return [f"SET {s} TO {ref(x)}", f"SET N TO {s}", "MOVE N TO E",
                f"DISPLAY '{self.label()} {ref(x)} ' E"]

    # -------------------------------------------------------------- steps (None: not applicable now)
    def st_setlit(self):
        ns = self.rng.sample(list(IDX), self.rng.choice([1, 1, 2]))
        v = self.rng.randint(1, min(OCC[n] for n in ns))
        for n in ns:
            self.idx[n] = v
        return [f"SET {' '.join(ns)} TO {v}"] + sum((self.show_idx(n) for n in ns), [])

    def st_setw(self):
        n = self.rng.choice(list(IDX))
        v = self.rng.randint(1, min(OCC[n], 9))
        self.idx[n] = v
        return [f"MOVE {v} TO W1", f"SET {n} TO W1"] + self.show_idx(n)

    def st_setidx(self):
        src = [n for n in IDX if self.idx[n] is not None]
        if not src:
            return None
        b = self.rng.choice(src)
        a = self.rng.choice([n for n in IDX if n != b])
        self.idx[a] = self.idx[b]
        return [f"SET {a} TO {b}"] + self.show_idx(a)

    def mix_ok(self):
        return self.mixed and self.mix_item is None and self.mix_at <= len(self.touched) - 1

    def st_set_x_i(self):
        if self.mix_ok():
            xs = self.items()
            x = self.rng.choice(xs)
            ns = [n for n in IDX if LEN[n] != cls(x) and self.idx[n] is not None]
            if ns:
                n = self.rng.choice(ns)
                self.mix_item = x
                self.touch(x)
                self.setv(x, "?")
                return [f"SET {ref(x)} TO {n}"] + self.show_ixd(x)
        x = self.rng.choice(self.items())
        ns = [n for n in self.names(cls(x)) if self.idx[n] is not None]
        if not ns:
            return None
        n = self.rng.choice(ns)
        self.setv(x, self.idx[n])
        self.touch(x)
        return [f"SET {ref(x)} TO {n}"] + self.show_ixd(x)

    def st_set_i_x(self):
        xs = self.items(readable=True)
        if not xs:
            return None
        x = self.rng.choice(xs)
        ns = self.names(cls(x))
        n = self.rng.choice(ns)
        self.idx[n] = self.ixd[x]
        self.touch(x)
        return [f"SET {n} TO {ref(x)}"] + self.show_idx(n)

    def st_set_x_x(self):
        xs = self.items(readable=True)
        if not xs:
            return None
        x = self.rng.choice(xs)
        ys = [y for y in self.items(cls(x)) if y != x]
        if not ys:
            return None
        y = self.rng.choice(ys)
        self.setv(y, self.ixd[x])
        self.union(x, y)
        self.touch(x, y)
        return [f"SET {ref(y)} TO {ref(x)}"] + self.show_ixd(y)

    def st_updown(self):
        ns = self.names(known=True, inrange=True)
        if not ns:
            return None
        n = self.rng.choice(ns)
        v = self.idx[n]
        ups = [d for d in (1, 2) if v + d <= OCC[n]]
        downs = [d for d in (1, 2) if v - d >= 1]
        opts = [("UP", d) for d in ups] + [("DOWN", d) for d in downs]
        if not opts:
            return None
        w, d = self.rng.choice(opts)
        self.idx[n] = v + d if w == "UP" else v - d
        if self.rng.random() < 0.3:
            return [f"MOVE {d} TO W2", f"SET {n} {w} BY W2"] + self.show_idx(n)
        return [f"SET {n} {w} BY {d}"] + self.show_idx(n)

    def st_cmp(self):
        rng = self.rng
        kind = rng.choice(["xi", "ix", "xx", "ii", "il", "abbr", "xi", "ix"])
        op = rng.choice(OPS)
        xs = self.items(readable=True)
        set_names = [n for n in IDX if self.idx[n] is not None]
        if kind in ("xi", "ix", "abbr"):
            pairs = [(x, n) for x in xs for n in set_names if LEN[n] == cls(x)]
            if not pairs:
                return None
            x, n = rng.choice(pairs)
            self.touch(x)
            if kind == "abbr":
                others = [m for m in set_names if LEN[m] == cls(x) and m != n]
                if not others:
                    return None
                c = f"{ref(x)} {op} {n} OR {rng.choice(others)}"
            else:
                c = f"{ref(x)} {op} {n}" if kind == "xi" else f"{n} {op} {ref(x)}"
        elif kind == "xx":
            pairs = [(x, y) for x in xs for y in xs if x != y and cls(x) == cls(y)]
            if not pairs:
                return None
            x, y = rng.choice(pairs)
            self.union(x, y)
            self.touch(x, y)
            c = f"{ref(x)} {op} {ref(y)}"
        elif kind == "ii":
            if len(set_names) < 2:
                return None
            a, b = rng.sample(set_names, 2)
            c = f"{a} {op} {b}"
        else:
            if not set_names:
                return None
            c = f"{rng.choice(set_names)} {op} {rng.randint(0, 7)}"
        return [f"IF {c} DISPLAY '{self.label()} T' ELSE DISPLAY '{self.label()} F' END-IF"]

    def st_sub(self):
        rng = self.rng
        choices = []
        for n in self.names(inrange=True, known=True):
            t = IDX[n][0]
            if t in self.tab:
                choices.append(n)
        r = rng.random()
        if r < 0.25 and isinstance(self.idx["ID1"], int) and 1 <= self.idx["ID1"] <= 3 and \
                isinstance(self.idx["ID2"], int) and 1 <= self.idx["ID2"] <= 4:
            return [f"DISPLAY '{self.label()} ' TDE (ID1 ID2) ' ' TDR (ID1)"]
        if not choices:
            return None
        n = rng.choice(choices)
        t, occ, _ = IDX[n]
        v = self.idx[n]
        if r < 0.45 and v + 1 <= occ:
            return [f"DISPLAY '{self.label()} ' {t} ({n} + 1)"]
        if r < 0.7:
            s = rng.choice(["zz", "qq", "a3", "b2", "x"]).ljust(len(self.tab[t][0]))[:len(self.tab[t][0])]
            self.tab[t][v - 1] = s
            return [f"MOVE '{s}' TO {t} ({n})", f"DISPLAY '{self.label()} ' {t[:2]}"]
        return [f"DISPLAY '{self.label()} ' {t} ({n})"]

    def st_search(self):
        rng = self.rng
        t = rng.choice(list(self.tab))
        si = {"TAE": "IA", "TBE": "IB", "TCE": "IC"}[t]
        occ, length = IDX[si][1], IDX[si][2]
        x = rng.choice(self.items(length))
        s = rng.randint(1, occ + 1 if rng.random() < 0.15 else occ)
        vals = self.tab[t]
        lit1 = rng.choice(vals + ["zz", "c03", "a5"])[:len(vals[0])].ljust(len(vals[0]))
        lit2 = rng.choice(vals)
        two = rng.random() < 0.4
        at_end = rng.random() < 0.7
        sc = SCRATCH[length]
        body = [f"SET {sc} TO {ref(x)}", f"SET N TO {sc}", "MOVE N TO E"]
        self.touch(x)
        self.union(x, x)
        lines = [f"SET {si} TO {s}", f"SET {ref(x)} TO {si}"]
        head = f"SEARCH {t} VARYING {ref(x)}"
        if at_end:
            head += f" AT END DISPLAY '{self.label()} AE'"
        lines.append(head)
        lines.append(f"WHEN {t} ({si}) = '{lit1}' " + " ".join(body) + f" DISPLAY '{self.label()} W1 ' E")
        if two:
            lines.append(f"WHEN {t} ({si}) = '{lit2}' DISPLAY '{self.label()} W2'")
        lines.append("END-SEARCH")
        v = s
        while v <= occ:
            if vals[v - 1] == lit1 or (two and vals[v - 1] == lit2):
                break
            v += 1
        self.idx[si] = v
        self.setv(x, v)
        self.idx[sc] = "?"
        return lines + self.show_idx(si) + self.show_ixd(x)

    def loop_level(self, var, length_of_var=None):
        """(FROM, BY, UNTIL condition, setup lines) for an index-name level `var`."""
        rng = self.rng
        occ = OCC[var]
        setup = []
        neg = rng.random() < 0.25
        r = rng.random()
        if r < 0.2:
            frm = rng.randint(1, min(occ, 9))
            setup.append(f"MOVE {frm} TO W1")
            frm_s = "W1"
        elif r < 0.4:
            srcs = [n for n in self.names(known=True, inrange=True) if n != var and self.idx[n] <= occ]
            if srcs:
                frm_s = rng.choice(srcs)
                frm = self.idx[frm_s]
            else:
                frm = rng.randint(1, occ)
                frm_s = str(frm)
        else:
            frm = rng.randint(1, occ)
            frm_s = str(frm)
        if neg:
            by = "-1"
            lim = rng.randint(0, frm)
            c = f"{var} < {lim}" if lim > 0 else f"{var} < 1"
        else:
            if rng.random() < 0.2:
                setup.append("MOVE 1 TO W2")
                by = "W2"
            else:
                by = rng.choice(["1", "1", "2"])
            c = f"{var} > {rng.randint(max(frm - 1, 0), occ)}"
        xs = [x for x in self.items(LEN[var], readable=True)]
        if xs and rng.random() < 0.3:
            x = rng.choice(xs)
            self.touch(x)
            c += f" OR {var} = {ref(x)}"
        return frm_s, by, f"({c} OR {GUARD})", setup

    def st_vary(self):
        rng = self.rng
        a = rng.choice(list(IDX))
        fa, ba, ca, setup = self.loop_level(a)
        lv = [f"VARYING {a} FROM {fa} BY {ba} UNTIL {ca}"]
        shown = self.show_idx(a)
        second = None
        if rng.random() < 0.35:
            if rng.random() < 0.6:
                b = rng.choice([n for n in IDX if n != a])
                fb, bb, cb, s2 = self.loop_level(b)
                setup += s2
                lv.append(f"AFTER {b} FROM {fb} BY {bb} UNTIL {cb}")
                second = b
                shown = shown + self.show_idx(b)
            else:
                lim = rng.randint(0, 3)
                lv.append(f"AFTER V2 FROM {rng.randint(0, 2)} BY 1 UNTIL (V2 > {lim} OR {GUARD})")
                second = "V2"
                shown = shown + ["MOVE V2 TO E", f"DISPLAY '{self.label()} V2 ' E"]
        test = rng.choice(["", "", "WITH TEST BEFORE ", "WITH TEST AFTER "])
        body = ["ADD 1 TO CNT"] + shown
        xs = self.items(LEN[a])
        if xs and rng.random() < 0.3:
            x = rng.choice(xs)
            body += [f"SET {ref(x)} TO {a}"] + self.show_ixd(x)
            # with TEST BEFORE the body may not run: then x keeps its state (unset, or changed by
            # GnuCOBOL's INITIALIZE), so it counts as set afterwards only if it was set before
            if test == "WITH TEST AFTER " or self.readable(x):
                self.setv(x, "?")
            self.touch(x)
        out = setup + ["MOVE 0 TO CNT"]
        head = " ".join(lv)
        if rng.random() < 0.4:
            p = f"PV{len(self.paras) + 1}"
            self.paras.append((p, body))
            out.append(f"PERFORM {p} {test}{head}")
        else:
            out += [f"PERFORM {test}{head}"] + body + ["END-PERFORM"]
        self.idx[a] = "?"
        if second in IDX:
            self.idx[second] = "?"
        for s in SCRATCH.values():
            self.idx[s] = "?"
        out += self.show_idx(a)
        if second in IDX:
            out += self.show_idx(second)
        return out

    def st_varyn(self):
        ns = self.names(known=True)
        if not ns:
            return None
        n = self.rng.choice(ns)
        lim = self.rng.randint(0, 6)
        return ["MOVE 0 TO CNT",
                f"PERFORM VARYING V2 FROM {n} BY 1 UNTIL V2 > {lim} OR {GUARD}",
                "ADD 1 TO CNT", "MOVE V2 TO E", f"DISPLAY '{self.label()} N ' E", "END-PERFORM",
                "MOVE V2 TO E", f"DISPLAY '{self.label()} NE ' E"]

    def st_gmove(self):
        fwd = self.rng.random() < 0.6
        a, b = ("XR", "XS") if fwd else ("XS", "XR")
        xa, xb = ("XRX", "YRX") if fwd else ("YRX", "XRX")
        self.ixd[xb] = self.ixd[xa]
        if xa in self.div:
            self.div.add(xb)
        else:
            self.div.discard(xb)
        self.union(xa, xb)
        self.touch(xa, xb)
        out = [f"MOVE {a} TO {b}", f"DISPLAY '{self.label()} [' XA '][' XB '][' YA '][' YB ']'"]
        if self.readable(xb):
            out += self.show_ixd(xb)
        return out

    def st_init(self):
        g = self.rng.choice(["XR", "XS", "XG", "XT"])
        hit = {"XR": ["XRX"], "XS": ["YRX"], "XG": ["XK1", "XK2"], "XT": XT}[g]
        self.div.update(hit)
        return [f"INITIALIZE {g}",
                f"DISPLAY '{self.label()} [' XA '][' XB '][' YA '][' YB '][' XTC (2) ']'"]

    def st_layout(self):
        s = "".join(self.rng.choice("PQRSTU") for _ in range(3))
        w = self.rng.choice(["XR", "XS", "XG", "XT", "X1", "XTE (2)"])
        return [f"MOVE '{s}' TO XB", f"DISPLAY '{self.label()} ' XB2",
                f"MOVE LENGTH OF {w} TO N", "MOVE N TO E", f"DISPLAY '{self.label()} LEN ' E"]

    def st_xt(self):
        rng = self.rng
        r = rng.random()
        k = rng.randint(1, 4)
        x = ("XTX", k)
        sub = []
        if rng.random() < 0.4:
            sub = [f"MOVE {k} TO K"]
            xr = "XTX (K)"
        else:
            xr = ref(x)
        if r < 0.4:
            ns = [n for n in self.names(4) if self.idx[n] is not None]
            if not ns:
                return None
            n = rng.choice(ns)
            self.setv(x, self.idx[n])
            self.touch(x)
            return sub + [f"SET {xr} TO {n}"] + self.show_ixd(x)
        if r < 0.65:
            if not self.readable(x):
                return None
            self.idx["ID1"] = self.ixd[x]
            self.touch(x)
            return sub + [f"SET ID1 TO {xr}"] + self.show_idx("ID1")
        ys = [y for y in XT if self.readable(y)]
        if r < 0.85:
            if len(ys) < 2:
                return None
            a, b = rng.sample(ys, 2)
            self.union(a, b)
            self.touch(a, b)
            return [f"IF {ref(a)} {rng.choice(OPS)} {ref(b)} DISPLAY '{self.label()} T' "
                    f"ELSE DISPLAY '{self.label()} F' END-IF"]
        if not ys:
            return None
        a = rng.choice(ys)
        if a == x:
            return None
        self.setv(x, self.ixd[a])
        self.union(a, x)
        self.touch(a, x)
        return sub + [f"SET {xr} TO {ref(a)}"] + self.show_ixd(x)


STEPS = [("st_setlit", 8), ("st_setw", 4), ("st_setidx", 6), ("st_set_x_i", 10), ("st_set_i_x", 10),
         ("st_set_x_x", 6), ("st_updown", 6), ("st_cmp", 12), ("st_sub", 6), ("st_search", 6),
         ("st_vary", 10), ("st_varyn", 3), ("st_gmove", 4), ("st_init", 3), ("st_layout", 2),
         ("st_xt", 6)]


def program(rng, k, mixed):
    g = Gen(rng, mixed)
    g.mix_at = rng.randint(0, k - 1)
    names, weights = zip(*STEPS)
    used = {}
    body = ["MOVE 'a1a2a3a4a5a6' TO TA", "MOVE 'b1b2b3b4b5b6b7b8' TO TB",
            "MOVE 'c01c02c03c04c05' TO TC", "MOVE 'ABCDEFGHIJKL' TO TD"]
    for i in range(k):
        g.touched.append(set())
        while True:
            name = rng.choices(names, weights)[0]
            lines = getattr(g, name)()
            if lines is not None:
                used[name] = used.get(name, 0) + 1
                break
        body += [f"DISPLAY 'S {i:02d}'"] + lines
    if mixed and g.mix_item is None:
        # no mixing step was possible: force one at the end
        x = g.items()[0]
        n = next(n for n in IDX if LEN[n] != cls(x))
        g.touched.append({x})
        body += [f"DISPLAY 'S {k:02d}'", f"SET {n} TO 1", f"SET {ref(x)} TO {n}",
                 f"SET {SCRATCH[cls(x)]} TO {ref(x)}"]
        g.mix_item = x
    lines = ["       IDENTIFICATION DIVISION.", "       PROGRAM-ID. IXT.",
             "       DATA DIVISION.", "       WORKING-STORAGE SECTION."] + DATA.splitlines() + \
            ["       PROCEDURE DIVISION.", "       P0."]
    for s in body:
        lines += wrap(s)
    lines.append("           STOP RUN.")
    for p, stmts in g.paras:
        lines.append(f"       {p}.")
        for s in stmts:
            lines += wrap(s)
        lines.append("           .")
    for l in lines:
        assert len(l) <= 72, l
    first = None
    if mixed:
        root = g.find(g.mix_item)
        first = next(i for i, t in enumerate(g.touched) if any(g.find(x) == root for x in t))
    return "\n".join(lines) + "\n", first, used


def bump(tally, out, case, status):
    tally[status] = tally.get(status, 0) + 1
    with open(os.path.join(out, "results.jsonl"), "a") as fh:
        fh.write(json.dumps({"case": case, "status": status}) + "\n")


def mixed_ok(g, m, first):
    """The model agrees with GnuCOBOL up to its stop, stops with `unsupported` for the element
    lengths, and the last step marker it shows is the first step touching the mixed items."""
    if not m or not m[-1].startswith("<model: fault:Cobol.Fault.unsupported") or "element lengths" not in m[-1]:
        return False
    shown = m[:-1]
    if shown != g[:len(shown)]:
        return False
    marks = [l for l in shown if l.startswith("S ") and l[2:].isdigit()]
    return bool(marks) and int(marks[-1][2:]) == first


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=20)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--k", type=int, default=20)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "out_index"))
    ap.add_argument("--show", type=int, default=3)
    ap.add_argument("--mixed", action="store_true")
    ap.add_argument("--keep", action="store_true", help="keep the files of agreeing programs")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    tally, shown, steps = {"ok": 0}, 0, {}
    for p in range(args.n):
        src, first, used = program(rng, args.k, args.mixed)
        for s, c in used.items():
            steps[s[3:]] = steps.get(s[3:], 0) + c
        base = os.path.join(args.out, f"ix_{args.seed}_{p}")
        outs, err = run(src, base)
        if err:
            bump(tally, args.out, p, "error")
            print(f"program {p}: {err[:300]}")
            continue
        g, m = outs
        if (mixed_ok(g, m, first) if args.mixed else g == m):
            bump(tally, args.out, p, "ok")
            for e in (".cob", "", ".fe.json") if not args.keep else ():
                if os.path.exists(base + e):
                    os.remove(base + e)
            continue
        bump(tally, args.out, p, "mismatch")
        if shown < args.show:
            shown += 1
            i = next((j for j, (a, b) in enumerate(zip(g, m)) if a != b), min(len(g), len(m)))
            print(f"program {p}: first difference at line {i}: gnucobol {g[i:i + 1]!r} model {m[i:i + 1]!r}"
                  f" ({len(g)} vs {len(m)} lines)" + (f", first touching step {first}" if args.mixed else ""))
    print(json.dumps({"tally": tally, "steps": dict(sorted(steps.items()))}))
    return 0 if tally["ok"] == args.n else 1


sys.exit(main())

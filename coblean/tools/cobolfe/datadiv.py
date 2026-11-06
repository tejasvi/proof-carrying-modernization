"""Data division: data description entries -> item trees (surface `Item` JSON) and the
symbol table used for name resolution."""
import copy

import pic as picmod
from reserved import FIGURATIVE, is_user_word
from tokens import ParseError, lit_number


USAGE = {"DISPLAY": "display",
         "COMP": "binary", "COMPUTATIONAL": "binary", "COMP-4": "binary",
         "COMPUTATIONAL-4": "binary", "BINARY": "binary",
         "COMP-3": "packed", "COMPUTATIONAL-3": "packed", "PACKED-DECIMAL": "packed",
         "COMP-5": "comp5", "COMPUTATIONAL-5": "comp5", "INDEX": "index"}
# a USAGE keyword for each usage (the description of a level-66 item renaming an elementary item)
USAGE_KW = {"display": "DISPLAY", "binary": "BINARY", "packed": "PACKED-DECIMAL", "comp5": "COMP-5"}
UNSUPPORTED_USAGE = {"COMP-1", "COMP-2", "COMPUTATIONAL-1", "COMPUTATIONAL-2",
                     "PROCEDURE-POINTER", "FUNCTION-POINTER", "NATIONAL", "DISPLAY-1", "UTF-8"}
# An index data item (USAGE INDEX) is 4 bytes, as on IBM (LP(32)) and GnuCOBOL. What the bytes
# hold is implementation-defined (IBM: a displacement, GnuCOBOL: a binary occurrence number); the
# surface IR makes the item a group of one hidden FILLER child holding the occurrence number as
# S9(7) COMP-3, whose VALUE (4 zero bytes, an invalid packed sign) makes a read before the first
# SET fault. No supported statement observes these bytes (see DataDiv.overlap_ix).
IX_PIC = {"num": {"digits": 7, "scale": 0, "signed": True}}
IX_UNSET = [0, 0, 0, 0]
FIG_VALUE = {"ZERO": "zero", "SPACE": "space", "HIGH-VALUE": "high", "LOW-VALUE": "low",
             "QUOTE": "quote"}
# DECIMAL-POINT IS COMMA: a PICTURE string is read with "." and "," exchanged
DPC_SWAP = str.maketrans(".,", ",.")


class Entry:
    """A data item (levels 01-49, 77)."""

    def __init__(self, id, level, name, parent, tok, section):
        self.id, self.level, self.name, self.parent = id, level, name, parent
        self.tok, self.section = tok, section
        self.children = []
        self.pic_text = None
        self.pic = None          # surface Pic JSON
        self.cat = None          # 'alnum' | 'num' | 'numEdited' | None (group)
        self.usage_kw = None     # USAGE as written (own clause)
        self.sign = None         # (leading, separate) as written
        self.occurs = None       # (n, table) when OCCURS is present
        self.odo = None          # OCCURS ... DEPENDING ON: (integer-1, (token, qualified object name))
        self.redefines_name = None
        self.redefines = None    # Entry
        self.value = None        # raw literal
        self.just = self.bwz = self.sync = False
        self.conds = []
        self.indexes = []
        self.keys = []           # OCCURS ASCENDING / DESCENDING KEY: (ascending, name)
        self.file = None         # file name, for FD records
        self.pointer = False     # USAGE POINTER: a 4-byte address
        self.ae = None           # alphanumeric-edited: pic.ae_pattern (the item is stored as alnum)
        self.index = False       # an index data item (elementary, USAGE INDEX; set by finish)
        self.ixid = None         # id of its hidden FILLER child (the value; see IX_PIC)
        self.is_global = False   # GLOBAL clause (level 01): visible in contained programs
        self.is_external = False  # EXTERNAL clause (level 01): one storage per run unit
        self.file_obj = None     # FD records: the parser's File
        self.rn = None           # a level-66 item: the level-01 record it renames in (finish_renames)

    def ancestors(self):
        out = []
        p = self.parent
        while p is not None:
            out.append(p)
            p = p.parent
        return out

    def root(self):
        e = self
        while e.parent is not None:
            e = e.parent
        return e

    def dims(self):
        return sum(1 for e in [self] + self.ancestors() if e.occurs is not None)

    def usage(self):
        for e in [self] + self.ancestors():
            if e.usage_kw is not None:
                return USAGE[e.usage_kw]
        return "display"

    def sign_clause(self):
        for e in [self] + self.ancestors():
            if e.sign is not None:
                return e.sign
        return None

    def is_group(self):
        return self.pic is None and not self.index

    def numeric(self):
        return self.cat == "num"

    def __repr__(self):
        return f"Entry({self.id}, {self.level}, {self.name})"


class CondEntry:
    """A level-88 condition name."""

    def __init__(self, id, name, parent, tok):
        self.id, self.name, self.parent, self.tok = id, name, parent, tok
        self.values = []         # [(lo, hi or None)] raw literals
        self.false_value = None

    def ancestors(self):
        return [self.parent] + self.parent.ancestors()

    def dims(self):
        return self.parent.dims()


class IndexEntry:
    def __init__(self, id, name, table):
        self.id, self.name, self.table = id, name, table


class DataDiv:
    def __init__(self, charset, ids):
        self.charset = charset   # 'ebcdic' | 'ascii'
        self.ids = ids           # shared id counter: callable returning a fresh id
        self.records = []        # top-level entries in storage order
        self.by_name = {}
        # (where, what): clauses the model does not cover; each makes the whole program
        # unsupported (the parser turns them into a fault at its first statement)
        self.unsupported = []
        self.ix_items = []       # index data items (Entry.index), set by finish
        self._ix_overlap = {}    # entry id -> an index data item sharing its bytes, or None
        # OCCURS DEPENDING ON tables: (table entry, integer-1, object entry), see finish_odo
        self.odo_tables = []
        # level-66 entries: (token, data-name-1, record, data-name-2, data-name-3 or None), each name
        # a (token, [name, qualifier, ...]); see finish_renames
        self.renames = []
        # SPECIAL-NAMES, set by the parser: DECIMAL-POINT IS COMMA, and the currency symbols
        # (upper case) -> the byte of the currency sign value; see pic_classify
        self.dpc = False
        self.currency = {}

    def pic_classify(self, p):
        """Surface Pic and category of the PICTURE string of token p. With DECIMAL-POINT IS COMMA
        "." and "," exchange their functions, and with a CURRENCY SIGN clause its symbol is the
        currency symbol, not $ (IBM): the string is read with the standard roles, and a
        numeric-edited picture whose "." / "," or currency symbol are written otherwise gets
        ESym.chars first, with the bytes they are written with (Cobol/Edit.lean `edit`)."""
        text = p.val.translate(DPC_SWAP) if self.dpc else p.val
        cs = None
        if self.currency:
            used = [s for s in self.currency if s in text]
            if len(used) > 1:
                raise ParseError(p, f"PICTURE {p.val} with two currency symbols")
            if "$" in text and "$" not in self.currency:
                raise ParseError(p, f"PICTURE {p.val}: $ is not a currency symbol of this program")
            if used:
                cs = self.currency[used[0]]
                text = text.replace(used[0], "$")
        try:
            pic, cat = picmod.classify(text)
        except picmod.PicError as err:
            raise ParseError(p, str(err))
        if cat == "numEdited":
            es = pic["numEdited"]["pic"]
            dot, comma, dollar = (self.encode(ch, p)[0] for ch in ".,$")
            dpc = self.dpc and ("dot" in es or "comma" in es)
            if dpc or (cs is not None and cs != dollar):
                es.insert(0, {"chars": {"dotCh": comma if self.dpc else dot,
                                        "commaCh": dot if self.dpc else comma,
                                        "csCh": cs if cs is not None else dollar}})
        return pic, cat, text

    # ------------------------------------------------------------------ parsing
    def parse_section(self, ts, section, file=None):
        """Entries up to the next FD / SD / section / division header."""
        stack = []
        first_record = None
        record = None            # the level-01 record of the level-66 entries that follow it
        while ts.peek().kind == "NUM":
            t = ts.next()
            try:
                level = int(t.val)
            except ValueError:
                raise ParseError(t, f"bad level number {t.val}")
            name = "FILLER"
            if ts.peek().is_word("FILLER"):
                ts.next()
            elif is_user_word(ts.peek()):
                name = ts.next().val
            if level == 88:
                if not stack:
                    raise ParseError(t, "level 88 without a parent item")
                self.parse_cond(ts, t, name, stack[-1])
                continue
            if level == 66:
                self.parse_renames(ts, t, name, record)
                # IBM: "All RENAMES entries associated with one logical record must immediately
                # follow the last data description entry of that record."
                stack = []
                continue
            if not (1 <= level <= 49 or level == 77):
                raise ParseError(t, f"bad level number {level}")
            if level in (1, 77):
                parent = None
                stack = []
                record = None
            else:
                while stack and stack[-1].level >= level:
                    stack.pop()
                if not stack:
                    raise ParseError(t, f"level {level} item {name} outside a record")
                parent = stack[-1]
            e = Entry(self.ids(), level, name, parent, t, section)
            self.parse_clauses(ts, e)
            if parent is None:
                if file is not None:
                    e.file = file
                    if first_record is None:
                        first_record = e
                    elif e.redefines_name is None:
                        e.redefines = first_record     # records of one FD share the area
                self.records.append(e)
                if level == 1:
                    record = e
            else:
                parent.children.append(e)
            stack.append(e)
            if name != "FILLER":
                self.by_name.setdefault(name, []).append(e)

    def parse_clauses(self, ts, e):
        while True:
            t = ts.peek()
            if t.kind == "PERIOD":
                ts.next()
                self.check_clauses(e)
                return
            if t.kind != "WORD":
                raise ParseError(t, f"unexpected {t.val!r} in the description of {e.name}")
            w = t.val
            ts.next()
            if w == "REDEFINES":
                e.redefines_name = ts.expect_user_word().val
            elif w in ("PIC", "PICTURE"):
                ts.accept_word("IS")
                p = ts.expect_kind("PIC")
                e.pic_text = p.val
                e.pic, e.cat, text = self.pic_classify(p)
                if e.cat == "alnumEdited":
                    e.ae, e.cat = picmod.ae_pattern(text), "alnum"
            elif w == "USAGE":
                ts.accept_word("IS")
                u = ts.next()
                self.set_usage(e, u)
            elif w in USAGE or w in UNSUPPORTED_USAGE or w == "POINTER":
                self.set_usage(e, t)
            elif w in ("SIGN", "LEADING", "TRAILING"):
                if w == "SIGN":
                    ts.accept_word("IS")
                    lt = ts.expect_word("LEADING", "TRAILING")
                    w = lt.val
                sep = False
                if ts.accept_word("SEPARATE"):
                    ts.accept_word("CHARACTER")
                    sep = True
                e.sign = (w == "LEADING", sep)
            elif w == "OCCURS":
                self.parse_occurs(ts, e, t)
            elif w in ("SYNC", "SYNCHRONIZED"):
                ts.accept_word("LEFT", "RIGHT")
                e.sync = True
            elif w in ("JUST", "JUSTIFIED"):
                ts.accept_word("RIGHT")
                e.just = True
            elif w == "BLANK":
                ts.accept_word("WHEN")
                ts.expect_word("ZERO", "ZEROS", "ZEROES")
                e.bwz = True
            elif w in ("VALUE", "VALUES"):
                ts.accept_word("IS", "ARE")
                e.value = parse_literal(ts)
            elif w in ("EXTERNAL", "GLOBAL") or (w == "IS" and ts.at_word("EXTERNAL", "GLOBAL")):
                if w == "IS":
                    w = ts.next().val
                # IBM: GLOBAL "only in data description entries whose level-number is 01" (any
                # section); EXTERNAL "only on data description entries whose level-number is 01
                # ... in the WORKING-STORAGE SECTION"
                if e.level != 1 or (w == "EXTERNAL" and e.section != "working"):
                    self.unsupported.append((t.where(), f"{w} clause on {e.name}"))
                elif w == "GLOBAL":
                    e.is_global = True
                else:
                    e.is_external = True
            else:
                raise ParseError(t, f"unsupported clause {w} in the description of {e.name}")

    def check_clauses(self, e):
        """Clauses that the model would ignore on this item (BLANK WHEN ZERO only takes effect on
        a numeric-edited item, JUSTIFIED on an alphanumeric one, a SIGN clause written on the
        item on a signed DISPLAY numeric one): recorded as unsupported, never dropped."""
        where = e.tok.where()
        if e.bwz and e.cat == "num" and e.usage() == "display" and not e.pic["num"]["signed"]:
            # IBM: "A BLANK WHEN ZERO clause that is specified for an item defined as numeric by its
            # picture character string defines the item as category numeric-edited" (S is not
            # allowed). P is not modelled in edited pictures, and "The BLANK WHEN ZERO clause does
            # not affect initial settings as determined by the VALUE clause", which GnuCOBOL 3.2
            # does not follow for VALUE ZERO / a numeric VALUE (it blanks them): those stay
            # unsupported.
            syms = picmod.symbols(e.pic_text)
            if "P" not in syms and (e.value is None or e.value[0] in ("str", "hex")):
                e.pic, e.cat = {"numEdited": {"pic": [picmod.EDIT_SYM[s] for s in syms]}}, "numEdited"
        if e.bwz and e.cat != "numEdited":
            self.unsupported.append((where, f"BLANK WHEN ZERO on {e.name}, which is not numeric-edited"))
        if e.just and (e.cat != "alnum" or e.ae is not None):
            self.unsupported.append((where, f"JUSTIFIED on {e.name}, which is not alphanumeric"))
        if e.sign is not None and e.pic is not None and \
                not (e.cat == "num" and e.pic["num"]["signed"] and e.usage() == "display"):
            self.unsupported.append((where, f"SIGN clause on {e.name}, which is not a signed DISPLAY numeric item"))
        if e.is_external and e.redefines_name is not None:
            self.unsupported.append((where, f"EXTERNAL clause on {e.name}, which has a REDEFINES clause"))
        if e.value is not None and e.root().is_external:
            # IBM: "The VALUE clause must not be specified for a data description entry that contains
            # or is subordinate to an entry that contains ... an EXTERNAL ... clause"
            self.unsupported.append((where, f"VALUE clause on {e.name} in an EXTERNAL record"))

    def set_usage(self, e, u):
        if u.kind == "WORD" and u.val == "POINTER":
            # an address: 4 bytes, full binary range (COMP-5 with 9 digits)
            e.pointer = True
            e.usage_kw = "COMP-5"
            e.pic, e.cat = {"num": {"digits": 9, "scale": 0, "signed": False}}, "num"
            return
        if u.kind != "WORD" or (u.val not in USAGE and u.val not in UNSUPPORTED_USAGE):
            raise ParseError(u, f"unknown USAGE {u.val}")
        if u.val in UNSUPPORTED_USAGE:
            raise ParseError(u, f"USAGE {u.val} is not supported")
        e.usage_kw = u.val

    def parse_occurs(self, ts, e, t):
        n = ts.expect_kind("NUM")
        count = int(n.val)
        lo = None
        if ts.accept_word("TO"):
            hi = ts.expect_kind("NUM")
            lo, count = count, int(hi.val)
        ts.accept_word("TIMES")
        dep = None
        while True:
            if ts.accept_word("DEPENDING"):
                ts.accept_word("ON")
                d = ts.expect_user_word()
                names = [d.val]
                while ts.accept_word("OF", "IN"):
                    names.append(ts.expect_user_word().val)
                dep = (d, names)
            elif ts.peek().is_word("ASCENDING", "DESCENDING"):
                asc = ts.next().val == "ASCENDING"
                ts.accept_word("KEY")
                ts.accept_word("IS")
                while is_user_word(ts.peek()):
                    e.keys.append((asc, ts.next().val))
            elif ts.accept_word("INDEXED"):
                ts.accept_word("BY")
                while is_user_word(ts.peek()):
                    it = ts.next()
                    e.indexes.append(it.val)
            else:
                break
        if dep is not None:
            # OCCURS [integer-1 TO] integer-2 DEPENDING ON data-name-1 (IBM: integer-1 >= 0 and
            # below integer-2; when it is left out, 1); the layout allocates integer-2 occurrences
            if lo is None:
                lo = 1
            if lo >= count:
                raise ParseError(t, f"OCCURS {lo} TO {count}: integer-1 must be below integer-2")
            e.odo = (lo, dep)
        elif lo is not None:
            raise ParseError(t, "OCCURS ... TO without DEPENDING ON")
        if count == 1:
            raise ParseError(t, "OCCURS 1 is not supported (the layout has no one-element tables)")
        if count < 1:
            raise ParseError(t, "OCCURS 0")
        e.occurs = count

    def parse_cond(self, ts, t, name, parent):
        c = CondEntry(self.ids(), name, parent, t)
        ts.expect_word("VALUE", "VALUES")
        ts.accept_word("IS", "ARE")
        while ts.peek().kind != "PERIOD":
            if ts.peek().is_word("WHEN", "FALSE"):
                ts.accept_word("WHEN")
                if ts.accept_word("SET"):
                    ts.expect_word("TO")
                ts.expect_word("FALSE")
                ts.accept_word("IS")
                c.false_value = parse_literal(ts)
                continue
            lo = parse_literal(ts)
            hi = None
            if ts.accept_word("THRU", "THROUGH"):
                hi = parse_literal(ts)
            c.values.append((lo, hi))
        ts.next()
        if not c.values:
            raise ParseError(t, f"condition {name} without values")
        parent.conds.append(c)
        self.by_name.setdefault(name, []).append(c)

    def parse_renames(self, ts, t, name, record):
        """`66 data-name-1 RENAMES data-name-2 [THROUGH data-name-3]`, after the entries of its
        level-01 record; resolved by finish_renames."""
        if record is None:
            raise ParseError(t, f"level-66 entry {name} does not follow a level-01 record")
        if name == "FILLER":
            raise ParseError(t, "level-66 entry without a data-name")
        ts.expect_word("RENAMES")

        def qualified():
            d = ts.expect_user_word()
            names = [d.val]
            while ts.accept_word("OF", "IN"):
                names.append(ts.expect_user_word().val)
            return d, names
        a = qualified()
        b = qualified() if ts.accept_word("THROUGH", "THRU") else None
        ts.expect_kind("PERIOD")
        self.renames.append((t, name, record, a, b))

    # ------------------------------------------------------------------ after parsing
    def finish(self, files):
        """Resolve REDEFINES and INDEXED BY; check elementary items."""
        indexes = []

        def walk(siblings):
            for k, e in enumerate(siblings):
                if e.redefines_name is not None:
                    prev = [s for s in siblings[:k] if s.name == e.redefines_name]
                    if not prev:
                        raise ParseError(e.tok, f"{e.name} REDEFINES {e.redefines_name}: not a preceding item at the same level")
                    e.redefines = prev[-1]
                index = e.pic is None and not e.children and e.usage() == "index"
                if e.pic is None and not e.children and not index:
                    raise ParseError(e.tok, f"elementary item {e.name} without PICTURE")
                if e.pic is not None and e.usage() == "index":
                    raise ParseError(e.tok, f"USAGE INDEX item {e.name} with PICTURE")
                if e.pic is None and e.children and e.usage() == "index" and e.value is not None:
                    raise ParseError(e.tok, f"VALUE clause on the USAGE INDEX group {e.name}")
                if index:
                    self.index_item(e)
                if e.pic is not None and e.children:
                    raise ParseError(e.tok, f"group item {e.name} with PICTURE")
                if e.pic is not None and e.cat != "num" and e.usage() != "display":
                    if e.usage_kw is not None:
                        raise ParseError(e.tok, f"USAGE {e.usage_kw} on non-numeric item {e.name}")
                if item_align(e) > 1 and any(a.occurs is not None for a in e.ancestors()):
                    # IBM and GnuCOBOL add slack bytes to such tables; where is not modelled
                    self.unsupported.append((e.tok.where(), f"SYNCHRONIZED {e.name} inside a table (OCCURS)"))
                for iname in e.indexes:
                    ie = IndexEntry(self.ids(), iname, e)
                    indexes.append(ie)
                    self.by_name.setdefault(iname, []).append(ie)
                walk(e.children)

        walk(self.records)
        self.indexes = indexes
        self.finish_odo(files)
        if self.renames:
            self.finish_renames()

    def finish_odo(self, files):
        """OCCURS DEPENDING ON tables: resolve each object (IBM: an integer item, outside the table;
        no subscripts) and record as unsupported the forms the model leaves out, IBM's complex ODO
        among them: items after the table in its record (variably located items), a table inside a
        table or containing an OCCURS DEPENDING ON table, a REDEFINES clause on the table or on a
        group containing it, or redefining one of them (the records of one FD share their area,
        which IBM allows), and VALUE clauses in the table or on a group containing it."""
        def walk(es):
            for e in es:
                yield e
                yield from walk(e.children)
        entries = list(walk(self.records))
        for e in entries:
            if e.odo is None:
                continue
            lo, (dtok, names) = e.odo
            obj = self.lookup(dtok, names, files=files)
            if not isinstance(obj, Entry) or not obj.numeric() or obj.pic["num"]["scale"] != 0 \
                    or obj.dims() != 0:
                raise ParseError(dtok, f"OCCURS DEPENDING ON object {' OF '.join(names)} is not an "
                                       "integer item outside every table")
            if obj is e or e in obj.ancestors():
                raise ParseError(dtok, f"OCCURS DEPENDING ON object {obj.name} lies in the table {e.name}")
            chain = [e] + e.ancestors()
            what = None
            outer = [a for a in e.ancestors() if a.odo is not None]
            if outer:
                what = f"OCCURS DEPENDING ON table {outer[-1].name} containing one"
            elif any(a.occurs is not None for a in e.ancestors()):
                what = f"OCCURS DEPENDING ON table {e.name} inside a table"
            elif any(d.odo is not None for d in walk(e.children)):
                what = f"OCCURS DEPENDING ON table {e.name} containing one"
            elif any(x.parent is not None and x.parent.children[-1] is not x for x in chain):
                what = f"variably located items after the OCCURS DEPENDING ON table {e.name}"
            elif any(x.redefines_name is not None for x in chain) or \
                    any(o.redefines in chain and o.redefines_name is not None for o in entries):
                what = f"OCCURS DEPENDING ON table {e.name} in a REDEFINES"
            elif any(x.value is not None for x in chain + list(walk(e.children))):
                what = f"VALUE clause in or on the OCCURS DEPENDING ON table {e.name}"
            if what is not None:
                # the program is unsupported: its statements never run, the table is left as declared
                self.unsupported.append((e.tok.where(), what))
            else:
                self.odo_tables.append((e, lo, obj))

    def odo_json(self):
        """Surface `OdoDecl`s of the OCCURS DEPENDING ON tables."""
        return [{"subject": e.id, "min": lo, "obj": obj.id} for e, lo, obj in self.odo_tables]

    def finish_renames(self):
        """Level-66 entries (IBM RENAMES clause). data-name-2 and data-name-3 are looked up among
        the items of the entry's level-01 record ("they must name elementary or group items within
        the associated level-01 entry"). Each entry becomes a hidden level-01 record that
        REDEFINES its record's storage: FILLER up to the renamed area, then data-name-1 over the
        area. Without THROUGH and with an elementary data-name-2, data-name-1 is an elementary item
        with data-name-2's description ("All of the data attributes of data-name-2 become the data
        attributes for data-name-1"), without its VALUE clause or condition names; otherwise it is
        an alphanumeric group item as long as the area (one FILLER child). The records follow every
        other item and are never longer than the record they redefine, so no offset changes.
        data-name-1 is qualified only by its record or file name (lookup)."""
        def walk(e):
            yield e
            for c in e.children:
                yield from walk(c)

        def leaves(e):
            return [x for x in walk(e) if not x.children]

        for t, name, rec, a, b in self.renames:
            def operand(ref):
                tok, names = ref
                quals = names[1:]

                def ok(c):
                    k = 0
                    for x in c.ancestors():
                        if k < len(quals) and x.name == quals[k]:
                            k += 1
                    return k == len(quals)
                found = [c for c in self.by_name.get(names[0], []) if isinstance(c, Entry)
                         and c.rn is None and c.root() is rec and ok(c)]
                if not found:
                    raise ParseError(tok, f"RENAMES: no item {' OF '.join(names)} in the record {rec.name}")
                if len(found) > 1:
                    raise ParseError(tok, f"RENAMES: ambiguous data name {' OF '.join(names)}: qualify it")
                e = found[0]
                if e is rec:
                    raise ParseError(tok, f"RENAMES: a level-66 entry cannot rename the level-01 entry {rec.name}")
                if any(x.occurs is not None for x in [e] + e.ancestors()):
                    raise ParseError(tok, f"RENAMES: {e.name} is or is subordinate to an item with OCCURS")
                return e
            e2 = operand(a)
            e3 = operand(b) if b is not None else None
            what = None
            lo = rec_offset(e2)
            if e3 is None:
                ln = item_size(e2)
                if e2.index or e2.pointer:
                    what = f"RENAMES of the {'index data item' if e2.index else 'pointer'} {e2.name}"
                elif any(x.odo is not None for x in walk(e2)):
                    what = f"RENAMES of the group {e2.name} with an OCCURS DEPENDING ON table"
            else:
                if e3 is e2:
                    raise ParseError(t, f"RENAMES {e2.name} THROUGH {e3.name}: the same item")
                hi2, lo3 = lo + item_size(e2), rec_offset(e3)
                hi3 = lo3 + item_size(e3)
                # "data-name-3 cannot be totally subordinate to data-name-2"
                if lo3 < lo or hi3 < hi2 or e2 in e3.ancestors():
                    raise ParseError(t, f"RENAMES {e2.name} THROUGH {e3.name}: {e3.name} starts or ends before "
                                        f"{e2.name}, or lies within it")
                order = list(walk(rec))
                inside = order[order.index(e2):order.index(list(walk(e3))[-1]) + 1]
                if any(x.odo is not None for x in inside):
                    raise ParseError(t, f"RENAMES {e2.name} THROUGH {e3.name}: an OCCURS DEPENDING ON table "
                                        "lies between them")
                ln = hi3 - lo
                first, last = leaves(e2)[0], leaves(e3)[-1]
                if rec_offset(first) != lo or span(last)[1] != hi3:
                    # (the area runs from the first elementary item of data-name-2 to the last one
                    # of data-name-3)
                    what = f"RENAMES {e2.name} THROUGH {e3.name}: elementary items do not start and end the area"
            if what is not None:
                # the program is unsupported: its statements never run
                self.unsupported.append((t.where(), what))
            hid = Entry(self.ids(), 1, f"%RENAMES {name}", None, t, rec.section)
            hid.redefines = rec_group(rec)
            if lo > 0:
                f = Entry(self.ids(), 2, "FILLER", hid, t, rec.section)
                f.pic, f.cat, f.pic_text = {"alnum": {"len": lo}}, "alnum", f"X({lo})"
                hid.children.append(f)
            al = Entry(self.ids(), 2, name, hid, t, rec.section)
            al.rn = rec
            if e3 is None and e2.pic is not None:
                al.pic, al.cat, al.pic_text = copy.deepcopy(e2.pic), e2.cat, e2.pic_text
                al.usage_kw = USAGE_KW[e2.usage()]
                al.sign, al.just, al.bwz, al.ae = e2.sign_clause(), e2.just, e2.bwz, e2.ae
            else:
                f = Entry(self.ids(), 3, "FILLER", al, t, rec.section)
                f.pic, f.cat, f.pic_text = {"alnum": {"len": ln}}, "alnum", f"X({ln})"
                al.children.append(f)
            hid.children.append(al)
            self.records.append(hid)
            self.by_name.setdefault(name, []).append(al)

    def index_item(self, e):
        """Check an index data item and give it the id of its hidden child. IBM: JUSTIFIED,
        PICTURE, BLANK WHEN ZERO and VALUE cannot describe it, and it cannot be a conditional
        variable. Bytes that other items or I/O can reach make the program unsupported."""
        for bad, what in ((e.value is not None, "VALUE"), (e.just, "JUSTIFIED"),
                          (e.bwz, "BLANK WHEN ZERO"), (e.sign is not None, "SIGN")):
            if bad:
                raise ParseError(e.tok, f"{what} clause on the index data item {e.name}")
        if e.conds:
            raise ParseError(e.conds[0].tok, f"the index data item {e.name} cannot be a conditional variable")
        e.index, e.cat, e.ixid = True, "index", self.ids()
        chain = [e] + e.ancestors()
        where = e.tok.where()
        if e.root().file is not None:
            # (I/O statements would move its bytes, whose contents are implementation-defined)
            self.unsupported.append((where, f"index data item {e.name} in a file record (I/O moves its bytes)"))
        elif any(a.redefines is not None for a in chain):
            self.unsupported.append((where, f"index data item {e.name} in the scope of a REDEFINES "
                                            "(other items share its bytes)"))
        if any(a.sync for a in chain):
            self.unsupported.append((where, f"SYNCHRONIZED index data item {e.name} (its alignment is not modelled)"))
        self.ix_items.append(e)

    def overlap_ix(self, e):
        """An index data item whose bytes the item e (not itself one) shares, or None: e contains
        it, or e is in a record or REDEFINES area overlaying it. Exact for each occurrence, except
        that tables of more than OCC_CAP occurrences are taken as a whole."""
        if not self.ix_items or not isinstance(e, Entry) or e.index:
            return None
        if e.id not in self._ix_overlap:
            found = self.overlap_ix_all(e)
            self._ix_overlap[e.id] = found[0] if found else None
        return self._ix_overlap[e.id]

    def overlap_ix_all(self, e):
        """Every index data item whose bytes the item e shares (see overlap_ix)."""
        if e.index:
            return []
        g = rec_group(e)
        found = []
        er = None
        for x in self.ix_items:
            if rec_group(x) is not g or not ranges_meet([span(e)], [span(x)]):
                continue
            if er is None:
                er = occ_ranges(e)
            xr = occ_ranges(x)
            if er is None or xr is None or ranges_meet(er, xr):
                found.append(x)
        return found

    def encode(self, s, tok):
        try:
            return list(s.encode("cp037" if self.charset == "ebcdic" else "latin-1"))
        except UnicodeEncodeError:
            raise ParseError(tok, f"literal {s!r} is not representable")

    def value_json(self, lit, cat, tok):
        """Surface `Value` of a literal for an item of category `cat` (None = group)."""
        kind = lit[0]
        if kind == "num":
            if cat not in ("num", "numEdited"):
                raise ParseError(tok, "numeric VALUE for a non-numeric item")
            return {"num": {"v": lit[1], "scale": lit[2]}}
        if kind == "fig":
            if lit[1] not in FIG_VALUE:
                raise ParseError(tok, f"VALUE {lit[1]} is not supported")
            return {"fig": {"f": FIG_VALUE[lit[1]]}}
        if kind == "all" and lit[1] == ("fig", "ZERO"):
            # IBM: "When literal is a figurative constant, the word ALL has no meaning", and ZERO
            # is the figurative constant that may stand for a numeric literal
            return self.value_json(lit[1], cat, tok)
        if cat == "num":
            raise ParseError(tok, "nonnumeric VALUE for a numeric item")
        if kind == "str":
            return {"alnum": {"bs": self.encode(lit[1], tok)}}
        if kind == "hex":
            return {"alnum": {"bs": list(lit[1])}}
        if kind == "all":
            inner = lit[1]
            if inner[0] == "fig":
                return self.value_json(inner, cat, tok)
            bs = self.encode(inner[1], tok) if inner[0] == "str" else list(inner[1])
            return {"fig": {"f": {"all": {"bs": bs}}}}
        raise ParseError(tok, f"unsupported VALUE literal {lit}")

    def item_json(self, e):
        if e.index:
            # a group of one hidden FILLER child: INITIALIZE leaves it alone (IBM: not a valid MOVE
            # receiver), and the child's VALUE marks it as not yet SET
            child = {"id": e.ixid, "level": 49, "name": "FILLER", "pic": IX_PIC, "usage": "packed",
                     "occurs": 1, "redefines": None, "value": {"alnum": {"bs": IX_UNSET}},
                     "just": False, "signSep": False, "signLead": False, "bwz": False, "sync": False,
                     "conds": [], "children": []}
            return {"id": e.id, "level": e.level, "name": e.name, "pic": None, "usage": "display",
                    "occurs": e.occurs or 1,
                    "redefines": e.redefines.id if e.redefines is not None else None,
                    "value": None, "just": False, "signSep": False, "signLead": False, "bwz": False,
                    "sync": False, "conds": [], "children": [child]}
        usage = e.usage() if e.cat == "num" else "display"
        sign = e.sign_clause() if e.cat == "num" else None
        signed = e.cat == "num" and e.pic["num"]["signed"]
        conds = []
        for c in e.conds:
            vals = [{"lo": self.value_json(lo, e.cat, c.tok),
                     "hi": self.value_json(hi, e.cat, c.tok) if hi is not None else None}
                    for (lo, hi) in c.values]
            conds.append([c.id, [c.name, vals]])
        return {"id": e.id, "level": e.level, "name": e.name, "pic": e.pic, "usage": usage,
                "occurs": e.occurs or 1,
                "redefines": e.redefines.id if e.redefines is not None else None,
                "value": self.value_json(e.value, e.cat, e.tok) if e.value is not None else None,
                "just": e.just, "signSep": bool(signed and sign and sign[1]),
                "signLead": bool(signed and sign and sign[0]), "bwz": e.bwz, "sync": e.sync,
                "conds": conds, "children": [self.item_json(c) for c in e.children],
                # an EXTERNAL record (for tools/cobolfe/link.py; the resolver ignores the key)
                **({"external": True} if e.is_external else {})}

    def json(self):
        return [self.item_json(e) for e in self.records]

    def ae_tmp(self, tok):
        """The hidden alphanumeric item (one per program, as long as the most data positions of
        an alphanumeric-edited item) through which the parser moves data into such items; placed
        after every other item, so no other offset changes."""
        if getattr(self, "_ae_tmp", None) is None:
            def walk(es):
                for e in es:
                    yield e
                    yield from walk(e.children)
            n = max(e.ae.count("d") for e in walk(self.records) if e.ae is not None)
            t = Entry(self.ids(), 1, "%AE-TMP", None, tok, "working")
            t.pic, t.cat = {"alnum": {"len": n}}, "alnum"
            self.records.append(t)
            self._ae_tmp = t
        return self._ae_tmp

    def hidden_num(self, tok, name, digits):
        """The hidden unsigned numeric DISPLAY item `name` PIC 9(digits) (one per program and name,
        e.g. for ACCEPT FROM DAY); placed after every other item, so no other offset changes."""
        hid = self.__dict__.setdefault("_hidden", {})
        if name not in hid:
            e = Entry(self.ids(), 1, name, None, tok, "working")
            e.pic, e.cat, e.pic_text = {"num": {"digits": digits, "scale": 0, "signed": False}}, "num", f"9({digits})"
            self.records.append(e)
            hid[name] = e
        return hid[name]

    # ------------------------------------------------------------------ name resolution
    # A contained program's data division (`outer`: the data division of the program that directly
    # contains it, `outer_files` that program's files) also sees the global names of its containing
    # programs. IBM (Scope of names): "Declarations in the program are searched. If no match is
    # found, only global declarations are searched in successive outer containing programs."
    outer = None
    outer_files = None

    def knows(self, name):
        """`name` is a data, condition or index name declared here or global in a containing program."""
        return name in self.by_name or (self.outer is not None and self.outer.knows_global(name))

    def knows_global(self, name):
        return any(is_global_entry(c) for c in self.by_name.get(name, [])) or \
            (self.outer is not None and self.outer.knows_global(name))

    def lookup(self, tok, names, files=None, kinds=None, only_global=False):
        """The entry named by `names` = [name, qualifier, ...] (`A OF B IN C`)."""
        cands = self.by_name.get(names[0], [])
        if only_global:
            cands = [c for c in cands if is_global_entry(c)]
        if kinds is not None:
            cands = [c for c in cands if isinstance(c, kinds)]
        quals = names[1:]

        def ok(c):
            if isinstance(c, IndexEntry):
                chain = [c.table] + c.table.ancestors()
            elif isinstance(c, Entry) and c.rn is not None:
                # a level-66 item "can be qualified only by the names of level indicator entries
                # or level-01 entries"
                chain = [c.rn]
            else:
                chain = c.ancestors()
            k = 0
            for a in chain:
                if k < len(quals) and a.name == quals[k]:
                    k += 1
            if k < len(quals) and files and len(quals) - k == 1:
                root = chain[-1] if chain else c
                if root.file == quals[k]:
                    k += 1
            return k == len(quals)

        found = [c for c in cands if ok(c)]
        if not found and self.outer is not None:
            return self.outer.lookup(tok, names, files=self.outer_files, kinds=kinds, only_global=True)
        if not found:
            raise ParseError(tok, f"unknown data name {' OF '.join(names)}")
        if len(found) > 1:
            raise ParseError(tok, f"ambiguous data name {' OF '.join(names)}: qualify it")
        return found[0]


def is_global_entry(c):
    """A data, condition or index name is global when its record has the GLOBAL clause, or is a
    record of a file whose FD has it (IBM: "All data-names subordinate to or condition-names or
    indexes associated with a global name are global names")."""
    r = (c.table if isinstance(c, IndexEntry) else c.parent if isinstance(c, CondEntry) else c).root()
    return r.is_global or (r.file_obj is not None and r.file_obj.is_global)


def parse_literal(ts):
    """A literal of a VALUE clause: ('num', v, scale, digits) | ('str', s) | ('hex', bytes) |
    ('fig', NAME) | ('all', literal)."""
    t = ts.next()
    if t.kind == "NUM":
        return ("num",) + lit_number(t)
    if t.kind == "STR":
        return ("str", t.val)
    if t.kind == "HEX":
        return ("hex", t.val)
    if t.kind == "WORD" and t.val in FIGURATIVE:
        return ("fig", FIGURATIVE[t.val])
    if t.is_word("ALL"):
        return ("all", parse_literal(ts))
    raise ParseError(t, f"expected a literal, found {t.val!r}")


# ---------------------------------------------------------------------- sizes (mirror Layout.lean)
def bin_bytes(digits):
    return 2 if digits <= 4 else (4 if digits <= 9 else 8)


def elem_size(e):
    if e.cat == "alnum":
        return e.pic["alnum"]["len"]
    if e.cat == "numEdited":
        # (the ESym.chars of a DECIMAL-POINT IS COMMA / CURRENCY SIGN picture is no position)
        return sum(0 if s in ("v", "p") or isinstance(s, dict) else (2 if s in ("cr", "db") else 1)
                   for s in e.pic["numEdited"]["pic"])
    n = e.pic["num"]
    u = e.usage()
    if u == "display":
        sign = e.sign_clause()
        return n["digits"] + (1 if n["signed"] and sign and sign[1] else 0)
    if u == "packed":
        return n["digits"] // 2 + 1
    return bin_bytes(n["digits"])


def item_size(e, rel=None):
    """Bytes of one occurrence of an item (`Item.size`); `rel` is its distance from its alignment
    base (its record, or the occurrence of the innermost enclosing table), found from the record
    when not given."""
    if getattr(e, "index", False):
        return 4
    if e.pic is not None:
        return elem_size(e)
    if rel is None:
        rel = base_offset(e)
    return size_list(e.children, 0 if e.occurs is not None else rel)


def item_align(e):
    if e.sync and e.cat == "num" and e.usage() in ("binary", "comp5"):
        return bin_bytes(e.pic["num"]["digits"])
    return 1


def place_list(items, rel):
    """(end offset, {id: start}) of siblings whose parent is `rel` bytes from its alignment base
    (`Item.sizeList` / `Item.placeList`)."""
    off = 0
    placed = {}
    starts = {}
    for it in items:
        if it.redefines is not None:
            j = it.redefines.id
            if j in placed:
                start, ln = placed[j]
                starts[it.id] = start
                off = max(off, start + max(ln, item_size(it, rel + start) * (it.occurs or 1)))
            else:
                sz = item_size(it, rel + off) * (it.occurs or 1)
                placed[it.id] = (off, sz)
                starts[it.id] = off
                off += sz
            continue
        a = item_align(it)
        start = off if a <= 1 else (rel + off + a - 1) // a * a - rel
        sz = item_size(it, rel + start) * (it.occurs or 1)
        placed[it.id] = (start, sz)
        starts[it.id] = start
        off = start + sz
    return off, starts


def size_list(items, rel=0):
    return place_list(items, rel)[0]


def base_offset(e):
    """Distance of `e` from its alignment base: its record, or the occurrence of the innermost
    enclosing table."""
    path = list(reversed([e] + e.ancestors()))
    rel = 0
    for parent, child in zip(path, path[1:]):
        crel = 0 if parent.occurs is not None else rel
        rel = crel + place_list(parent.children, crel)[1][child.id]
    return rel


# ---------------------------------------------------------------------- shared bytes (index data items)
OCC_CAP = 4096


def rec_offset(e):
    """Offset of the first occurrence of `e` from the start of its record."""
    path = list(reversed([e] + e.ancestors()))
    off = rel = 0
    for parent, child in zip(path, path[1:]):
        crel = 0 if parent.occurs is not None else rel
        start = place_list(parent.children, crel)[1][child.id]
        off += start
        rel = crel + start
    return off


def table_dims(e):
    """(stride, count) of `e` and of each table enclosing it."""
    return [(item_size(a), a.occurs) for a in [e] + e.ancestors() if a.occurs is not None]


def span(e):
    """Bytes [a, b) from the first occurrence of `e` to the end of its last, from its record's start."""
    a = rec_offset(e)
    return (a, a + sum((n - 1) * s for s, n in table_dims(e)) + item_size(e))


def occ_ranges(e):
    """Bytes [a, b) of every occurrence of `e`, from its record's start (None: over OCC_CAP)."""
    starts = [rec_offset(e)]
    for stride, n in table_dims(e):
        if len(starts) * n > OCC_CAP:
            return None
        starts = [s + k * stride for s in starts for k in range(n)]
    ln = item_size(e)
    return [(s, s + ln) for s in starts]


def ranges_meet(r1, r2):
    """Whether two lists of disjoint byte ranges [a, b) share a byte."""
    r1, r2 = sorted(r1), sorted(r2)
    i = j = 0
    while i < len(r1) and j < len(r2):
        (a, b), (c, d) = r1[i], r2[j]
        if a < d and c < b:
            return True
        if b <= d:
            i += 1
        else:
            j += 1
    return False


def rec_group(e):
    """The record whose storage `e`'s record occupies (a level-01 REDEFINES overlays the record it
    redefines; the records of an FD share its first record's area)."""
    r = e.root()
    while r.redefines is not None:
        r = r.redefines
    return r


def sub_ix_offsets(e):
    """(offset from the start of one occurrence of `e`, item) of every occurrence of an index data
    item inside it, in offset order."""
    out = []

    def walk(x, off):
        if x.index:
            out.append((off, x))
            return
        starts = place_list(x.children, 0 if x.occurs is not None else base_offset(x))[1]
        for c in x.children:
            for k in range(c.occurs or 1):
                walk(c, off + starts[c.id] + k * item_size(c))
    walk(e, 0)
    return sorted(out, key=lambda p: p[0])

"""COBOL program -> surface IR JSON (the extraction contract, `Cobol/Frontend/Surface.lean`).

The parser resolves every name (qualified data names, condition names, index names, files,
paragraphs and sections) and emits the surface IR directly.  A statement it cannot express
in the IR becomes `unsupported` (the semantics faults there, so no proof can rely on it), and
is listed in the report; constructs of the data division it cannot express are errors.
"""
import copy
import dataclasses
import datetime
import os
import re

import odo as odomod
import pic as picmod
from datadiv import DataDiv, Entry, CondEntry, IndexEntry, parse_literal, item_size, sub_ix_offsets, item_align, \
    is_global_entry
from datadiv import occ_ranges, ranges_meet, rec_group, rec_offset, table_dims
from reserved import VERBS, RESERVED, FIGURATIVE, is_user_word
from tokens import TS, ParseError, lit_number, EOF


def _has_key(j, key):
    """Whether the JSON value j contains a dict with key `key`."""
    if isinstance(j, dict):
        return key in j or any(_has_key(v, key) for v in j.values())
    if isinstance(j, list):
        return any(_has_key(v, key) for v in j)
    return False


def eval_own(c):
    """An EVALUATE subject compared with an object, as rel_json gave it: when a side is an arithmetic
    expression with a division or a power with a variable exponent, the node relOwn (IBM: with no
    relational operator written, each arithmetic expression "is evaluated without regard to the
    attributes of its comparand", so each side gets the dmax of its own operands); else c unchanged."""
    r = c.get("relExpr") if isinstance(c, dict) else None
    if r is not None and any(_has_key(r[s], k) for s in ("a", "b") for k in ("div", "powE")):
        return {"relOwn": r}
    return c


def _has_exit_perform(stmts):
    """Whether an EXIT PERFORM [CYCLE] in these statements belongs to the enclosing inline PERFORM
    (one inside a nested inline PERFORM belongs to that one)."""
    def go(j):
        if j in ("exitPerform", "exitCycle"):
            return True
        if isinstance(j, dict):
            return any(go(v) for k, v in j.items() if k != "performInline")
        if isinstance(j, list):
            return any(go(v) for v in j)
        return False
    return go(stmts)


def dpc_literals(toks):
    """The tokens after `DECIMAL-POINT IS COMMA`, whose numeric literals are written with a
    comma (IBM: the clause "exchanges the functions of the period and the comma ... in numeric
    literals"). The lexer reads `12,5` as NUM "12", a separator comma and NUM "5": with nothing
    between them on one line they become one NUM "12.5", the form the parser reads; `,5` is "0.5"
    and `-,5` "-0.5". A NUM written with a period is no literal there (GnuCOBOL: a separator
    period)."""
    out = []
    for t in toks:
        prev = out[-1] if out else None
        same = prev is not None and prev.file == t.file and prev.line == t.line
        if t.kind == "NUM" and t.sepch == "," and t.val.isdigit():
            # the comma is written directly before t (lexer.Tok.sepch)
            if same and prev.kind == "NUM" and prev.val.lstrip("+-").isdigit() and \
                    prev.col + len(prev.val) + 1 == t.col:
                out[-1] = dataclasses.replace(prev, val=prev.val + "." + t.val)
                continue
            if same and prev.kind == "OP" and prev.val in ("+", "-") and prev.col + 2 == t.col:
                out[-1] = dataclasses.replace(prev, kind="NUM", val=prev.val + "0." + t.val)
                continue
            # the comma starts the literal unless it ends a name or parenthesis (`A,5`: two
            # operands, as without the clause)
            glued = same and prev.kind in ("WORD", "NUM", "RPAR") and \
                prev.col + len(prev.val) == t.col - 1
            if not glued:
                out.append(dataclasses.replace(t, val="0." + t.val, sep=False, sepch=""))
                continue
        if t.kind == "NUM" and "." in t.val:
            raise ParseError(t, f"numeric literal {t.val} written with a period under DECIMAL-POINT IS COMMA")
        out.append(t)
    return out


def program_end(toks, i):
    """The index of the END PROGRAM marker that ends the separately compiled program whose tokens
    continue at i (IDENTIFICATION / ID DIVISION opens a contained program, END PROGRAM closes
    it), or len(toks) when that program runs to the end of the source."""
    depth = 0
    for k in range(i, len(toks) - 1):
        t, u = toks[k], toks[k + 1]
        if t.is_word("IDENTIFICATION", "ID") and u.is_word("DIVISION"):
            depth += 1
        elif t.is_word("END") and u.is_word("PROGRAM"):
            if depth == 0:
                return k
            depth -= 1
    return len(toks)


IBM = {"charset": "ebcdic", "zonedSign": "ebcdic", "trunc": "std", "numprocPfd": False,
       "binaryLE": False, "comp5LE": False, "binary1Byte": False, "sizeErrorTruncates": True}
GNUCOBOL = dict(IBM, charset="ascii", zonedSign="asciiMF", comp5LE=True)
PROFILES = {"ibm": IBM, "gnucobol": GNUCOBOL}
# switch names (SPECIAL-NAMES environment-name-2): IBM's UPSI-0 to UPSI-7; GnuCOBOL's SWITCH-0 to
# SWITCH-36 and, under -std=ibm, UPSI-0 to UPSI-7 (switch n is GnuCOBOL's COB_SWITCH_n)
SWITCH_NAMES = {"ibm": re.compile(r"UPSI-([0-7])$"),
                "gnucobol": re.compile(r"(?:UPSI-([0-7])|SWITCH-([0-9]|[12][0-9]|3[0-6]))$")}


def switch_number(profile, name):
    """The number of switch `name` in the profile, or None."""
    m = SWITCH_NAMES[profile].match(name)
    return None if m is None else int(next(g for g in m.groups() if g is not None))

# SPECIAL-NAMES environment-name-1 (IBM, Table 1 "Meanings of environment names"); SYSIN and SYSIPT
# are the system input device ("System logical input unit")
DEVICE_NAMES = {"SYSIN", "SYSIPT", "SYSOUT", "SYSLIST", "SYSLST", "SYSPUNCH", "SYSPCH", "CONSOLE",
                "CSP", "AFP-5A"} | {f"C{i:02d}" for i in range(1, 13)} | {f"S{i:02d}" for i in range(1, 6)}
SYSIN_NAMES = ("SYSIN", "SYSIPT")

SIMPLE = {"ref", "num", "str", "hex", "fig", "all"}
FUNCTIONS = {"ABS", "INTEGER", "INTEGER-PART", "MOD", "REM", "MIN", "MAX", "SUM", "RANGE", "FACTORIAL",
             "INTEGER-OF-DATE", "DATE-OF-INTEGER", "INTEGER-OF-DAY", "DAY-OF-INTEGER"}
# alphanumeric functions of one alphanumeric argument (values of the argument's length)
AFUNCTIONS = {"UPPER-CASE", "LOWER-CASE", "REVERSE"}
# functions of the program collating sequence (the native one when none is declared), with MAX
# and MIN of alphanumeric arguments
SEQ_FUNCTIONS = {"ORD", "CHAR", "ORD-MAX", "ORD-MIN"}
NEG_OP = {"=": "<>", "<>": "=", "<": ">=", ">=": "<", ">": "<=", "<=": ">"}
ROUNDING_MODES = {"AWAY-FROM-ZERO", "NEAREST-AWAY-FROM-ZERO", "NEAREST-EVEN", "NEAREST-TOWARD-ZERO",
                  "PROHIBITED", "TOWARD-GREATER", "TOWARD-LESSER", "TRUNCATION"}
CLASSES = {"NUMERIC", "ALPHABETIC", "ALPHABETIC-LOWER", "ALPHABETIC-UPPER"}
# the most comparisons a class condition with a class name (SPECIAL-NAMES CLASS) expands to
CLASS_CAP = 4096
# characters IBM does not allow as a one-character CURRENCY SIGN (the lowercase letters are
# refused separately)
CURRENCY_BAD = set("0123456789ABCDEGNPRSUVXZ +-,.*/;()\"='")
# the category names of INITIALIZE ... REPLACING / TO VALUE (IBM; EGCS = DBCS)
INIT_CATEGORIES = ("ALPHABETIC", "ALPHANUMERIC", "ALPHANUMERIC-EDITED", "DBCS", "EGCS", "NATIONAL",
                   "NATIONAL-EDITED", "NUMERIC", "NUMERIC-EDITED", "UTF-8")
# IBM: "Direct references to an index data item can be made only in a SEARCH statement, a SET
# statement, a relation condition" (with an index name or index data item) and USING phrases
IX_DIRECT = "index data item used outside SET, SEARCH VARYING and comparisons with index names or index data items"
IX_RANGE = "index data item: an occurrence number of more than 7 digits"
SIGNS = {"POSITIVE": "POSITIVE", "NEGATIVE": "NEGATIVE", "ZERO": "ZERO", "ZEROS": "ZERO",
         "ZEROES": "ZERO"}


class X:
    """Parsed operand / arithmetic expression."""

    def __init__(self, kind, tok, **kw):
        self.kind = kind
        self.tok = tok
        self.__dict__.update(kw)

    def __repr__(self):
        return f"X({self.kind}, {self.__dict__})"


class File:
    def __init__(self, id, name, tok):
        self.id, self.name, self.tok = id, name, tok
        self.org = "SEQUENTIAL"
        self.access = "SEQUENTIAL"
        self.key = None
        self.alt_keys = []
        self.status = None
        self.records = []
        self.min_len = None      # RECORD VARYING FROM / RECORD CONTAINS n TO m
        self.max_len = None
        self.contains = None     # RECORD CONTAINS n (fixed length)
        self.depending = None    # DEPENDING ON item (qualified name, resolved after the data division)
        self.optional = False    # SELECT OPTIONAL
        self.is_global = False   # FD ... GLOBAL: visible in contained programs


class Unit:
    """A compilation unit: one or more separately compiled programs (a batch) and their contained
    programs, parsed from one source. Item ids and file numbers are unique in the unit, so that the
    programs' surface IRs can be linked without renumbering (`tools/cobolfe/unit.py`)."""

    def __init__(self):
        self.next_id = 0
        self.next_file = 0
        self.programs = []       # every program, in source order (a containing program first)

    def fresh(self):
        self.next_id += 1
        return self.next_id

    def file_id(self):
        self.next_file += 1
        return self.next_file


class Program:
    """Parse state of one program."""

    def __init__(self, toks, profile="ibm", trunc="std", div_scale=None, is_main=None, when_compiled=None,
                 switches=None, unit=None, parent=None, ts=None):
        # a contained program, or a later program of a batch, continues the unit's token stream
        self.ts = ts if ts is not None else TS(toks)
        self.opts = dict(profile=profile, trunc=trunc, div_scale=div_scale, when_compiled=when_compiled,
                         switches=switches)
        self.unit = unit if unit is not None else Unit()
        self.unit.programs.append(self)
        self.parent = parent     # the directly containing program (None: separately compiled)
        self.children = []       # directly contained programs
        self.common = False      # PROGRAM-ID ... IS COMMON
        self.initial = False     # PROGRAM-ID ... IS INITIAL
        self.calls = []          # CALL statements, resolved when the unit is linked (unit.py)
        self.cancels = []        # CANCEL operands, likewise
        self.profile = profile
        # switch states at the start of the run (switch number -> ON), see switch_on
        self.switch_opts = switches or {}
        self.switch_decls = []   # SPECIAL-NAMES switch entries, see switch_entry
        self.switch_items = {}   # switch number -> its hidden item
        self.switch_mnem = {}    # mnemonic name -> the hidden item of its switch
        self.devices = {}        # mnemonic name -> its environment-name-1 (device_entry)
        # FUNCTION WHEN-COMPILED: the compilation (front end) time, YYYYMMDDhhmmsshh+hhmm
        self.when_compiled = when_compiled
        self.config = dict(PROFILES[profile], trunc=trunc)
        self.div_scale = div_scale
        self.is_main = is_main
        self.dd = DataDiv(self.config["charset"], self.fresh)
        self.files = {}
        self.same = []           # SAME [RECORD] AREA clauses: (kind, file names, token)
        if parent is not None:
            # global names of the containing programs; their switches (contained programs have no
            # CONFIGURATION SECTION: IBM, Calling nested COBOL programs)
            self.dd.outer, self.dd.outer_files = parent.dd, parent.files
            self.switch_items, self.switch_mnem = parent.switch_items, parent.switch_mnem
            # its DECIMAL-POINT IS COMMA and currency signs, which read the PICTURE strings (IBM:
            # "In the outermost program, code any CONFIGURATION SECTION entries that might be
            # required"); the literals are read so by decimal_point_clause, the classes below
            self.dd.dpc, self.dd.currency = parent.dd.dpc, dict(parent.dd.currency)
            self.devices = parent.devices
        self.name = ""
        self.using = []
        self.frames = []
        self.unsupported = []
        # constructs outside statements that the model does not cover: they make the whole
        # program unsupported (a fault at its first statement), so no run or proof relies on
        # a program whose meaning they would change
        self.dropped = []
        self.paras = []
        self.para_sects = {}     # paragraph name -> sections it occurs in
        self.sections = set()
        self.cur_sect = None
        self.special = {}
        # index data items: classes of items exchanging values (union-find by entry id), the
        # element lengths of the index names each class meets, the index data items each
        # statement touches (one list per statement being parsed), and those statements
        self.ix_parent, self.ix_entries, self.ix_lens = {}, {}, {}
        self.ix_frames, self.ix_stmts, self.ix_done = [], [], set()
        if self.unit.programs[0] is not self:
            # one set of classes for the unit: a GLOBAL index data item is one item in every program
            first = self.unit.programs[0]
            self.ix_parent, self.ix_entries, self.ix_lens, self.ix_stmts, self.ix_done = \
                first.ix_parent, first.ix_entries, first.ix_lens, first.ix_stmts, first.ix_done
        self.ix_allow = []       # stack: statements that check shared-storage references themselves
        self.ix_watch = None     # the VARYING index data item of the SEARCH whose WHEN is parsed
        # PROGRAM COLLATING SEQUENCE: the alphabet name's token, the ALPHABET clauses (name ->
        # (ALPHABET token, "STANDARD-1" / "STANDARD-2" / "NATIVE" / "EBCDIC" or the list of literal
        # phrases)), and the phrases emitted as "collating" (an alphabet given by literals only)
        self.coll_name = None
        self.alphabets = {}
        self.collating = None
        self.odo = None          # odo.Odo when the program has OCCURS DEPENDING ON tables
        # SPECIAL-NAMES CLASS: class name -> the byte values of its characters (class_clause; a
        # contained program has its containing program's); the number of CURRENCY SIGN clauses;
        # DECIMAL-POINT IS COMMA and the currency sign are kept in self.dd (dpc, currency), which
        # reads the PICTURE strings
        self.classes = dict(parent.classes) if parent is not None else {}
        self.currency_clauses = 0

    def fresh(self):
        return self.unit.fresh()

    def outermost(self):
        p = self
        while p.parent is not None:
            p = p.parent
        return p

    def ancestors(self):
        out, p = [], self.parent
        while p is not None:
            out.append(p)
            p = p.parent
        return out

    def file_named(self, name):
        """The file `name` refers to here: one of this program's, else a global one of a containing
        program (IBM: "only global declarations are searched in successive outer containing
        programs")."""
        f = self.files.get(name)
        if f is not None:
            return f
        for p in self.ancestors():
            g = p.files.get(name)
            if g is not None and g.is_global:
                return g
        return None

    def at_program_start(self):
        """At the IDENTIFICATION DIVISION of a contained program (or of the next program of a batch)."""
        return self.ts.at_word("IDENTIFICATION", "ID") and self.ts.peek(1).is_word("DIVISION")

    def at_end_program(self):
        return self.ts.at_word("END") and self.ts.peek(1).is_word("PROGRAM")

    def unit_main(self):
        """This program is the unit's first program and is extracted as a main program."""
        return self.parent is None and self.unit.programs[0] is self and \
            (self.is_main if self.is_main is not None else not self.using)

    def odo_group(self, e):
        """e is a group containing an OCCURS DEPENDING ON table (a variable-length item)."""
        return self.odo is not None and e is not None and self.odo.kind(e) == "group"

    def odo_slack(self, r):
        """Bytes of record r beyond its shortest length: the occurrences of its OCCURS DEPENDING ON
        table above integer-1 (0 for a record without one)."""
        return sum((t.occurs - lo) * item_size(t) for t, lo, _ in self.dd.odo_tables if t.root() is r)

    def drop(self, where, what):
        """Record a construct outside the statements that the model does not cover (it makes
        the program unsupported, see `dropped`)."""
        self.dropped.append(what)
        self.unsupported.append((where, what))

    # ================================================================== program structure
    def parse(self):
        ts = self.ts
        ts.expect_word("IDENTIFICATION", "ID")
        ts.expect_word("DIVISION")
        ts.expect_kind("PERIOD")
        ts.expect_word("PROGRAM-ID")
        ts.accept_kind("PERIOD")
        t = ts.next()
        if t.kind not in ("WORD", "STR"):
            raise ParseError(t, "expected a program name")
        self.name = t.val
        initial = None
        while ts.peek().kind not in ("PERIOD", "EOF"):
            w = ts.next()
            if w.is_word("INITIAL"):
                initial = w
            elif w.is_word("COMMON"):
                # (IBM: "The COMMON clause can be used only in nested programs"; elsewhere it has no
                # effect and is ignored, as before nested programs)
                self.common = self.parent is not None
        ts.accept_kind("PERIOD")
        while not (ts.at_word("ENVIRONMENT", "DATA", "PROCEDURE") and ts.peek(1).is_word("DIVISION")):
            if ts.peek().kind == "EOF":
                raise ParseError(ts.peek(), "no PROCEDURE DIVISION")
            if self.at_end_program() or self.at_program_start():
                break        # a program without other divisions (IBM: all but the first are optional)
            if ts.peek().is_word("REPLACE"):
                self.drop(ts.peek().where(), "REPLACE statement")
            ts.next()
        if ts.at_word("ENVIRONMENT"):
            self.environment()
        if ts.at_word("DATA"):
            self.data()
        self.dd.finish(self.files)
        # OCCURS DEPENDING ON tables: their statements are expanded (odo.py), not for an object of a
        # containing program (a GLOBAL item; odo.py places only this program's items)
        outer = [t for t, _, obj in self.dd.odo_tables if obj.root() not in self.dd.records]
        for t in outer:
            self.drop(t.tok.where(), f"OCCURS DEPENDING ON object of a containing program (table {t.name})")
        self.odo = odomod.Odo(self) if self.dd.odo_tables and not outer else None
        self.make_switches()
        for f in self.files.values():
            f.records = [e for e in self.dd.records if e.file == f.name]
            for e in f.records:
                e.file_obj = f
            if f.contains is not None and any(self.odo_slack(r) for r in f.records):
                self.drop(f.tok.where(), f"RECORD CONTAINS {f.contains} with OCCURS DEPENDING ON (file {f.name})")
        self.same_areas()
        for where, what in self.dd.unsupported:
            self.drop(where, what)
        if ts.at_word("PROCEDURE"):
            self.procedure()
        else:
            self.use = []
            self.use_global = set()
        self.ix_finish()
        # INITIAL: the program and the programs it contains start in their initial state on every CALL
        # (unit.py for a program of the unit, link.py for one linked into its caller); no effect on the
        # main program of the run, which is entered once
        self.initial = initial is not None and not self.unit_main()
        local = getattr(self, "local_storage", None)
        if local is not None and not (self.is_main if self.is_main is not None else not self.using):
            self.drop(local.where(), "LOCAL-STORAGE in a called program (initialized again on every CALL)")
        # contained programs follow the procedure division, then this program's END PROGRAM
        while self.at_program_start():
            child = Program(None, is_main=False, unit=self.unit, parent=self, ts=ts, **self.opts)
            self.children.append(child)
            child.parse()
        g = [t for t, _, _ in self.dd.odo_tables if is_global_entry(t)] if self.children else []
        if g:
            # the contained programs' statements are not expanded for the table (odo.py works per program)
            self.drop(g[0].tok.where(), f"GLOBAL record with an OCCURS DEPENDING ON table ({g[0].name}) in a "
                      "program that contains programs")
        if self.at_end_program():
            ts.next(), ts.next()
            n = ts.next()
            if n.kind not in ("WORD", "STR") or n.val.upper() != self.name.upper():
                raise ParseError(n, f"END PROGRAM {n.val} does not end program {self.name}")
            ts.accept_kind("PERIOD")
        elif self.parent is not None or self.children:
            raise ParseError(ts.peek(), f"END PROGRAM {self.name} missing")
        elif ts.peek().kind != "EOF":
            raise ParseError(ts.peek(), f"unexpected {ts.peek().val!r} after program {self.name}")
        if self.dropped:
            # the program's first statement faults: COBOL starts at the first paragraph
            what = "program: " + "; ".join(dict.fromkeys(self.dropped))
            first = [{"unsupported": {"what": what}}]
            if self.paras:
                self.paras[0]["sentences"].insert(0, first)
            else:
                self.paras.append({"name": "", "sect": None, "sentences": [first]})
        return self.json()

    def environment(self):
        ts = self.ts
        ts.expect_word("ENVIRONMENT")
        ts.expect_word("DIVISION")
        ts.expect_kind("PERIOD")
        while not ts.at_word("DATA", "PROCEDURE"):
            t = ts.peek()
            if t.kind == "EOF":
                raise ParseError(t, "no PROCEDURE DIVISION")
            if self.at_end_program() or self.at_program_start():
                break
            if t.is_word("SELECT"):
                self.select()
            elif t.is_word("DECIMAL-POINT"):
                self.decimal_point_clause()
            elif t.is_word("ALPHABET"):
                self.alphabet_clause()
            elif t.is_word("CLASS"):
                self.class_clause()
            elif t.is_word("CURRENCY"):
                self.currency_clause()
            elif t.is_word("SYMBOLIC"):
                self.drop(t.where(), f"SPECIAL-NAMES {t.val}")
                ts.next()
            elif t.is_word("COLLATING"):
                self.collating_clause()
            elif t.is_word("DEBUGGING"):
                self.drop(t.where(), "WITH DEBUGGING MODE (debugging lines, USE FOR DEBUGGING)")
                ts.next()
            elif t.is_word("SAME"):
                self.same_clause()
            elif t.is_word("REPLACE"):
                self.drop(t.where(), "REPLACE statement")
                ts.next()
            elif t.kind == "WORD" and switch_number(self.profile, t.val) is not None:
                self.switch_entry()
            elif t.kind == "WORD" and t.val in DEVICE_NAMES:
                self.device_entry()
            else:
                # paragraph and computer names, the other implementor names and their mnemonic
                # names (their uses in DISPLAY UPON, ACCEPT FROM and WRITE ADVANCING are unsupported
                # statements), I-O-CONTROL entries other than SAME
                ts.next()
        if self.coll_name is not None:
            self.collating_finish()

    def collating_clause(self):
        """`[PROGRAM] COLLATING SEQUENCE [IS] alphabet-name` of OBJECT-COMPUTER (IBM's only form;
        PROGRAM is skipped as an unknown word before this). Another form is dropped."""
        ts = self.ts
        t = ts.next()
        if not ts.at_word("SEQUENCE"):
            self.drop(t.where(), "PROGRAM COLLATING SEQUENCE")
            return
        ts.next()
        ts.accept_word("IS")
        n = ts.peek()
        if self.coll_name is not None or not is_user_word(n):
            self.drop(t.where(), "PROGRAM COLLATING SEQUENCE")
            return
        ts.next()
        self.coll_name = n

    def alpha_lit_at(self):
        t = self.ts.peek()
        return t.kind in ("STR", "HEX") or (t.kind == "NUM" and t.val.isdigit()) or \
            (t.kind == "WORD" and t.val in FIGURATIVE and FIGURATIVE[t.val] != "NULL")

    def alpha_lit(self):
        """One literal of an ALPHABET clause as a surface literal (Surface.Lit), or None."""
        if not self.alpha_lit_at():
            return None
        t = self.ts.next()
        if t.kind == "STR":
            return {"str": {"s": t.val}}
        if t.kind == "HEX":
            return {"hex": {"h": t.val.hex().upper()}}
        if t.kind == "NUM":
            return {"num": {"v": int(t.val), "scale": 0, "digits": len(t.val)}}
        return {"fig": {"name": FIGURATIVE[t.val]}}

    def alphabet_clause(self):
        """`ALPHABET alphabet-name [IS] {STANDARD-1 | STANDARD-2 | NATIVE | EBCDIC | phrase...}`,
        each phrase `literal [{THROUGH | THRU} literal | {ALSO literal}...]` (SPECIAL-NAMES). Only
        a PROGRAM COLLATING SEQUENCE uses it (CODE-SET and SYMBOLIC CHARACTERS are dropped). A
        clause that does not parse is dropped."""
        ts = self.ts
        t = ts.next()
        nt = ts.peek()
        if not is_user_word(nt):
            self.drop(t.where(), "SPECIAL-NAMES ALPHABET")
            return
        ts.next()
        ts.accept_word("IS")
        k = ts.peek()
        if k.is_word("STANDARD-1", "STANDARD-2", "NATIVE", "EBCDIC"):
            ts.next()
            self.alphabets[nt.val] = (t, k.val)
            return
        phrases, ok = [], True
        while ok and self.alpha_lit_at():
            ph = {"lit": self.alpha_lit(), "thru": None, "also": []}
            if ts.accept_word("THROUGH", "THRU"):
                ph["thru"] = self.alpha_lit()
                ok = ph["thru"] is not None
            else:
                while ok and ts.accept_word("ALSO"):
                    lit = self.alpha_lit()
                    ok = lit is not None
                    ph["also"].append(lit)
            phrases.append(ph)
        # what follows the list must start another clause (`"A" THRU "B" ALSO "C"`, `ALL "A"` do not parse)
        n = ts.peek()
        if n.kind in ("STR", "HEX", "NUM", "NSTR", "ZSTR") or n.is_word("ALSO", "THROUGH", "THRU", "ALL"):
            ok = False
        if not ok or not phrases:
            self.drop(t.where(), "SPECIAL-NAMES ALPHABET")
            return
        self.alphabets[nt.val] = (t, phrases)

    def collating_finish(self):
        """The PROGRAM COLLATING SEQUENCE's alphabet: the native order (NATIVE; STANDARD-1 and
        STANDARD-2, ASCII, with ASCII data; EBCDIC with EBCDIC data) needs nothing; an alphabet
        given by literals becomes "collating" (Cobol/Frontend/Resolve.lean `collation`). The
        others are dropped: STANDARD-1 / STANDARD-2 with EBCDIC data (where IBM puts the EBCDIC
        characters outside ASCII is not modelled) and EBCDIC with ASCII data (GnuCOBOL's own
        conversion table)."""
        n = self.coll_name
        a = self.alphabets.get(n.val)
        if a is None:
            self.drop(n.where(), f"PROGRAM COLLATING SEQUENCE: no alphabet {n.val}")
            return
        kind = a[1]
        ascii_data = self.config["charset"] == "ascii"
        if isinstance(kind, list):
            self.collating = kind
        elif kind in ("STANDARD-1", "STANDARD-2") and not ascii_data:
            self.drop(n.where(), f"PROGRAM COLLATING SEQUENCE {kind} with EBCDIC data")
        elif kind == "EBCDIC" and ascii_data:
            self.drop(n.where(), "PROGRAM COLLATING SEQUENCE EBCDIC with ASCII data")

    def same_clause(self):
        """`SAME [RECORD | SORT | SORT-MERGE] [AREA] [FOR] file-name ...` of I-O-CONTROL (applied
        after the data division, see same_areas)."""
        ts = self.ts
        t = ts.next()
        kind = "AREA"
        if ts.accept_word("RECORD"):
            kind = "RECORD"
        elif ts.accept_word("SORT", "SORT-MERGE"):
            kind = "SORT"
        ts.accept_word("AREA")
        ts.accept_word("FOR")
        names = []
        while is_user_word(ts.peek()) and ts.peek().val in self.files:
            names.append(ts.next().val)
        self.same.append((kind, names, t))

    def same_areas(self):
        """IBM: the files of a SAME RECORD AREA clause "use the same main storage area for
        processing the current logical record", so the records of those files all start at the
        first of them in storage order (an implicit REDEFINES of it, as the records of one FD
        share their first record's area). SAME AREA and SAME SORT AREA clauses have no effect
        here ("The SAME AREA clause is syntax checked, but has no effect on the execution of the
        program"; sort files are not modelled)."""
        group = {}               # file name -> representative (union-find)

        def find(n):
            while group.setdefault(n, n) != n:
                n = group[n]
            return n
        for kind, names, t in self.same:
            if kind != "RECORD":
                continue
            for n in names[1:]:
                group[find(n)] = find(names[0])
        roots = {}
        for e in self.dd.records:
            if e.file is not None and e.file in group:
                r = find(e.file)
                if r not in roots:
                    roots[r] = e
                elif roots[r] is not e:
                    e.redefines = roots[r]

    def decimal_point_clause(self):
        """`DECIMAL-POINT [IS] COMMA` (SPECIAL-NAMES): the comma and the period exchange their
        functions in numeric literals and PICTURE strings (IBM). The numeric literals of the rest
        of the program are read here (dpc_literals), the PICTURE strings by the data division
        (DataDiv.pic_classify)."""
        ts = self.ts
        ts.next()
        ts.accept_word("IS")
        ts.expect_word("COMMA")
        if not self.dd.dpc:
            self.dd.dpc = True
            # up to the END PROGRAM of this separately compiled program (the programs it contains
            # are inside; a later program of the source has its own SPECIAL-NAMES)
            end = program_end(ts.toks, ts.i)
            ts.toks[ts.i:end] = dpc_literals(ts.toks[ts.i:end])

    def class_lit(self):
        """One literal of a CLASS clause: ("num", n) for an unsigned integer, ("chars", bytes)
        for an alphanumeric or hex literal or SPACE, ZERO, QUOTE, HIGH-VALUE, LOW-VALUE; or None."""
        ts = self.ts
        t = ts.peek()
        if t.kind == "NUM" and t.val.isdigit():
            ts.next()
            return ("num", int(t.val))
        if t.kind in ("STR", "HEX") and t.val:
            ts.next()
            return ("chars", self.dd.encode(t.val, t) if t.kind == "STR" else list(t.val))
        fig = FIGURATIVE.get(t.val) if t.kind == "WORD" else None
        if fig in ("SPACE", "ZERO", "QUOTE", "HIGH-VALUE", "LOW-VALUE"):
            ts.next()
            if fig in ("HIGH-VALUE", "LOW-VALUE"):
                return ("chars", [0xFF if fig == "HIGH-VALUE" else 0x00])
            return ("chars", self.dd.encode({"SPACE": " ", "ZERO": "0", "QUOTE": '"'}[fig], t))
        return None

    def class_clause(self):
        """`CLASS class-name [IS] {literal [THROUGH | THRU literal]}...` (SPECIAL-NAMES): the byte
        values of the class's characters (IBM, CLASS clause): every character of an alphanumeric or
        hex literal; for a numeric literal n, the character at ordinal position n of the native
        collating sequence (byte n - 1); SPACE, ZERO, QUOTE, HIGH-VALUE, LOW-VALUE as one character
        (GnuCOBOL accepts them); `a THROUGH b`, one character each and both numeric or both not,
        every byte value from a to b, in either order. A clause that does not parse makes the
        program unsupported."""
        ts = self.ts
        t = ts.next()
        nt = ts.peek()
        if not is_user_word(nt) or nt.val in self.classes:
            self.drop(t.where(), "SPECIAL-NAMES CLASS")
            return
        ts.next()
        ts.accept_word("IS")

        def byte_values(lit):
            if lit[0] == "num":
                return [lit[1] - 1] if 1 <= lit[1] <= 256 else None
            return lit[1]
        members, ok = set(), True
        while ok:
            lo = self.class_lit()
            if lo is None:
                break
            a = byte_values(lo)
            if ts.accept_word("THROUGH", "THRU"):
                hi = self.class_lit()
                b = byte_values(hi) if hi is not None else None
                ok = a is not None and b is not None and len(a) == 1 and len(b) == 1 and lo[0] == hi[0]
                if ok:
                    members |= set(range(min(a[0], b[0]), max(a[0], b[0]) + 1))
            else:
                ok = a is not None
                if ok:
                    members |= set(a)
        # what follows the list must start another clause (`"A" THRU "B" THRU "C"`, `ALL "A"` do not)
        n = ts.peek()
        if n.kind in ("STR", "HEX", "NUM", "NSTR", "ZSTR") or n.is_word("THROUGH", "THRU", "ALL"):
            ok = False
        if not ok or not members:
            self.drop(t.where(), "SPECIAL-NAMES CLASS")
            return
        self.classes[nt.val] = frozenset(members)

    def currency_clause(self):
        """`CURRENCY [SIGN] [IS] literal [[WITH] PICTURE SYMBOL literal]` (SPECIAL-NAMES). Modelled:
        one clause, one character and no PICTURE SYMBOL phrase (IBM: the literal "Specifies both a
        currency sign value and the currency symbol"): that character is the currency symbol of
        PICTURE strings, written as itself, and $ is not one (DataDiv.pic_classify). The program is
        unsupported with the PICTURE SYMBOL phrase or more than one CURRENCY SIGN clause (GnuCOBOL
        3.2 implements neither: no reference to check them against), a lowercase letter (the lexer
        upper-cases PICTURE strings; currency symbols are case-sensitive) or a character IBM does
        not allow (digits, A B C D E G N P R S U V X Z, space, + - , . * / ; ( ) " = '); its
        PICTURE strings are still read with the symbol (DataDiv.currency)."""
        ts = self.ts
        t = ts.next()
        ts.accept_word("SIGN")
        ts.accept_word("IS")
        lt = ts.peek()
        if lt.kind != "STR":
            self.drop(t.where(), "SPECIAL-NAMES CURRENCY SIGN")
            return
        ts.next()
        sym = lt.val
        self.currency_clauses += 1
        if ts.at_word("WITH", "PICTURE"):
            ts.accept_word("WITH")
            ts.expect_word("PICTURE")
            # the lexer reads the word after PICTURE as a PICTURE string
            if ts.peek().kind == "PIC" and ts.peek().val == "SYMBOL":
                ts.next()
            else:
                ts.expect_word("SYMBOL")
            st = ts.expect_kind("STR")
            sym = st.val
            self.drop(t.where(), "SPECIAL-NAMES CURRENCY SIGN ... WITH PICTURE SYMBOL")
        elif self.currency_clauses > 1:
            self.drop(t.where(), "SPECIAL-NAMES CURRENCY SIGN: more than one clause")
        elif len(sym) != 1 or sym.islower() or sym in CURRENCY_BAD:
            self.drop(t.where(), f"SPECIAL-NAMES CURRENCY SIGN {sym!r}")
        if len(sym) == 1 and sym.upper() not in CURRENCY_BAD and lt.val:
            self.dd.currency[sym.upper()] = self.dd.encode(lt.val, lt)[0]

    def switch_entry(self):
        """`environment-name-2 [[IS] mnemonic-name-2] [ON [STATUS] [IS] condition-1]
        [OFF [STATUS] [IS] condition-2]` (the two phrases in either order) of SPECIAL-NAMES."""
        ts = self.ts
        t = ts.next()
        d = {"num": switch_number(self.profile, t.val), "tok": t, "mnem": None, "conds": []}
        if ts.accept_word("IS") or (is_user_word(ts.peek()) and
                                    switch_number(self.profile, ts.peek().val) is None):
            d["mnem"] = ts.expect_user_word()
        while ts.at_word("ON", "OFF") and len(d["conds"]) < 2:
            on = ts.next().is_word("ON")
            ts.accept_word("STATUS")
            ts.accept_word("IS")
            d["conds"].append((ts.expect_user_word(), on))
        self.switch_decls.append(d)

    def device_entry(self):
        """`environment-name-1 [IS] mnemonic-name-1` of SPECIAL-NAMES (a name of DEVICE_NAMES): the
        mnemonic name stands for that device in ACCEPT FROM (st_ACCEPT; its other uses, DISPLAY UPON
        and WRITE ADVANCING, are unsupported statements)."""
        ts = self.ts
        t = ts.next()
        ts.accept_word("IS")
        if is_user_word(ts.peek()):
            self.devices[ts.next().val] = t.val

    def switch_on(self, num, tok):
        """The state of switch `num` at the start of the run: the --switch option; else, with the
        gnucobol profile, the environment variable COB_SWITCH_num as GnuCOBOL reads it at the start
        of a run; else OFF (IBM's UPSI run-time option defaults to UPSI(00000000))."""
        if num in self.switch_opts:
            return self.switch_opts[num]
        v = os.environ.get(f"COB_SWITCH_{num}") if self.profile == "gnucobol" else None
        if v is None:
            return False
        if v.upper() not in ("ON", "OFF"):
            raise ParseError(tok, f"COB_SWITCH_{num}={v!r}: give ON or OFF")
        return v.upper() == "ON"

    def make_switches(self):
        """Each switch named in SPECIAL-NAMES becomes a hidden one-byte alphanumeric item, "1" when
        the switch is on and "0" when it is off (IBM: a switch-status condition "is true if the UPSI
        switch is set to the value (0 or 1) corresponding to condition-name"), with its condition
        names as level-88 entries; SET mnemonic-name TO ON / OFF moves "1" / "0" into it. The items
        follow every other item, so no other offset changes."""
        for d in self.switch_decls:
            e = self.switch_items.get(d["num"])
            if e is None:
                name = f"%{'UPSI' if self.profile == 'ibm' else 'SWITCH'}-{d['num']}"
                e = Entry(self.fresh(), 1, name, None, d["tok"], "working")
                e.pic, e.cat, e.pic_text = {"alnum": {"len": 1}}, "alnum", "X"
                e.value = ("str", "1" if self.switch_on(d["num"], d["tok"]) else "0")
                e.is_global = True   # the switch and its condition names also serve contained programs
                self.dd.records.append(e)
                self.switch_items[d["num"]] = e
            if d["mnem"] is not None:
                self.switch_mnem[d["mnem"].val] = e
            for ct, on in d["conds"]:
                c = CondEntry(self.fresh(), ct.val, e, ct)
                c.values = [(("str", "1" if on else "0"), None)]
                c.switch = True
                e.conds.append(c)
                self.dd.by_name.setdefault(ct.val, []).append(c)

    def select(self):
        ts = self.ts
        ts.expect_word("SELECT")
        opt = ts.accept_word("OPTIONAL")
        nt = ts.expect_user_word()
        # numbered in SELECT order from 1, through all the programs of the unit
        f = File(self.unit.file_id(), nt.val, nt)
        # an absent OPTIONAL file opens with status 05 (the run's environment says which are absent)
        f.optional = opt is not None
        while ts.peek().kind not in ("PERIOD", "EOF"):
            t = ts.next()
            if t.is_word("ASSIGN"):
                ts.accept_word("TO")
                ts.next()
            elif t.is_word("ORGANIZATION"):
                ts.accept_word("IS")
                if ts.accept_word("LINE"):
                    f.org = "LINE SEQUENTIAL"
                    ts.expect_word("SEQUENTIAL")
                else:
                    f.org = ts.expect_word("SEQUENTIAL", "INDEXED", "RELATIVE").val
            elif t.is_word("INDEXED", "RELATIVE"):
                f.org = t.val
            elif t.is_word("LINE") and ts.at_word("SEQUENTIAL"):
                ts.next()
                f.org = "LINE SEQUENTIAL"
            elif t.is_word("ACCESS"):
                ts.accept_word("MODE")
                ts.accept_word("IS")
                f.access = ts.expect_word("SEQUENTIAL", "RANDOM", "DYNAMIC").val
            elif t.is_word("RECORD") and not ts.at_word("DELIMITER"):
                # RECORD [KEY] [IS] data-name (IBM: KEY and IS are optional words)
                ts.accept_word("KEY")
                ts.accept_word("IS")
                f.key = self.qualname()
            elif t.is_word("ALTERNATE"):
                # ALTERNATE [RECORD] [KEY] [IS] data-name (IBM: RECORD, KEY and IS are optional)
                ts.accept_word("RECORD")
                ts.accept_word("KEY")
                ts.accept_word("IS")
                k = self.qualname()
                dups = False
                if ts.accept_word("WITH"):
                    ts.expect_word("DUPLICATES")
                    dups = True
                elif ts.accept_word("DUPLICATES"):
                    dups = True
                f.alt_keys.append((k, dups))
            elif t.is_word("FILE") and ts.at_word("STATUS") or t.is_word("STATUS"):
                ts.accept_word("STATUS")
                ts.accept_word("IS")
                f.status = self.qualname()
                if is_user_word(ts.peek()):
                    self.drop(t.where(), f"VSAM extended FILE STATUS of {f.name}")
                    self.qualname()
            # other clauses (RESERVE, PADDING CHARACTER, RECORD DELIMITER, LOCK MODE, SHARING) only
            # concern media and concurrent access, which the model does not observe
        ts.expect_kind("PERIOD")
        self.files[f.name] = f

    def qualname(self):
        t = self.ts.expect_user_word()
        names = [t.val]
        while self.ts.accept_word("OF", "IN"):
            names.append(self.ts.expect_user_word().val)
        return (t, names)

    def data(self):
        ts = self.ts
        ts.expect_word("DATA")
        ts.expect_word("DIVISION")
        ts.expect_kind("PERIOD")
        while not ts.at_word("PROCEDURE"):
            t = ts.peek()
            if self.at_end_program() or self.at_program_start():
                break
            if t.is_word("FILE") and ts.peek(1).is_word("SECTION"):
                ts.next(), ts.next(), ts.expect_kind("PERIOD")
                while ts.at_word("FD", "SD"):
                    kind = ts.next()
                    fname = ts.expect_user_word()
                    if kind.val == "SD":
                        self.drop(kind.where(), f"sort file (SD {fname.val})")
                    elif fname.val not in self.files:
                        raise ParseError(fname, f"FD {fname.val} without SELECT")
                    while ts.peek().kind not in ("PERIOD", "EOF"):
                        w = ts.next()
                        if w.is_word("RECORD") and kind.val == "FD":
                            self.fd_record_clause(self.files[fname.val])
                        elif w.is_word("GLOBAL") and kind.val == "FD":
                            # the file and its records are global names (IBM: GLOBAL clause, FD)
                            self.files[fname.val].is_global = True
                        elif w.is_word("LINAGE", "CODE-SET", "REPORT", "REPORTS", "EXTERNAL", "GLOBAL"):
                            self.drop(w.where(), f"{w.val} clause of {kind.val} {fname.val}")
                        # BLOCK CONTAINS, LABEL RECORDS, VALUE OF, DATA RECORDS and RECORDING MODE
                        # do not change the records the model reads and writes
                    ts.expect_kind("PERIOD")
                    self.dd.parse_section(ts, "file", file=fname.val)
            elif t.is_word("WORKING-STORAGE", "LOCAL-STORAGE", "LINKAGE") and ts.peek(1).is_word("SECTION"):
                ts.next(), ts.next(), ts.expect_kind("PERIOD")
                n = len(self.dd.records)
                self.dd.parse_section(ts, {"WORKING-STORAGE": "working", "LOCAL-STORAGE": "local",
                                           "LINKAGE": "linkage"}[t.val])
                if t.val == "LOCAL-STORAGE" and len(self.dd.records) > n:
                    # the same as WORKING-STORAGE in a main program; see parse() for a called one
                    self.local_storage = t
            elif t.kind == "EOF":
                raise ParseError(t, "no PROCEDURE DIVISION")
            else:
                raise ParseError(t, f"unexpected {t.val!r} in the DATA DIVISION")

    def fd_record_clause(self, f):
        """`RECORD [IS] VARYING [IN] [SIZE] [FROM n] [TO m] [CHARACTERS] [DEPENDING [ON] item]`
        or `RECORD [CONTAINS] n [TO m] [CHARACTERS]` (after the word RECORD)."""
        ts = self.ts

        def integer():
            t = ts.next()
            if t.kind != "NUM" or not t.val.isdigit():
                raise ParseError(t, "record length must be an unsigned integer")
            return int(t.val)
        ts.accept_word("IS")
        if ts.accept_word("VARYING"):
            ts.accept_word("IN")
            ts.accept_word("SIZE")
            if ts.accept_word("FROM"):
                f.min_len = integer()
            if ts.accept_word("TO"):
                f.max_len = integer()
            ts.accept_word("CHARACTERS")
            if ts.accept_word("DEPENDING"):
                ts.accept_word("ON")
                f.depending = self.qualname()
            if f.min_len is None and f.max_len is None and f.depending is None:
                f.min_len = 1
        else:
            ts.accept_word("CONTAINS")
            if ts.peek().kind == "NUM":
                n = integer()
                if ts.accept_word("TO"):
                    f.min_len, f.max_len = n, integer()
                else:
                    f.contains = n
            ts.accept_word("CHARACTERS")

    # ================================================================== procedure division
    def procedure(self):
        ts = self.ts
        ts.expect_word("PROCEDURE")
        ts.expect_word("DIVISION")
        if ts.accept_word("USING"):
            while True:
                if ts.accept_word("BY"):
                    m = ts.expect_word("REFERENCE", "VALUE", "CONTENT")
                    if m.val != "REFERENCE":
                        self.drop(m.where(), f"PROCEDURE DIVISION USING BY {m.val}")
                if not is_user_word(ts.peek()):
                    break
                t, names = self.qualname()
                u = self.dd.lookup(t, names)
                if getattr(u, "index", False) or self.dd.overlap_ix(u) is not None:
                    # the caller's argument bytes become the values of the index data items
                    self.drop(t.where(), f"PROCEDURE DIVISION USING {u.name}, which is or contains an index data item")
                self.using.append(u)
        if ts.accept_word("RETURNING"):
            self.drop(ts.peek().where(), "PROCEDURE DIVISION RETURNING")
            self.qualname()
        ts.expect_kind("PERIOD")
        self.prescan()
        self.use = []
        self.use_global = set()
        if ts.at_word("DECLARATIVES"):
            self.declaratives()
        ndecl = len(self.paras)
        self.body(decl=False)
        if self.use:
            # execution starts after END DECLARATIVES: a first paragraph jumps there (the
            # declarative sections run only as USE procedures or when performed)
            if ndecl == len(self.paras):
                self.paras.append({"name": "", "sect": None, "sentences": []})
            main = self.paras[ndecl]
            if not main["name"]:
                main["name"] = "*MAIN"
            self.paras.insert(0, {"name": "", "sect": None,
                                  "sentences": [[{"goTo": {"target": main["name"]}}]]})

    def body(self, decl):
        """Paragraphs and sentences up to the end of the program, or, in the declaratives
        (`decl`), up to the next section header or END DECLARATIVES."""
        ts = self.ts
        para = None
        while ts.peek().kind != "EOF":
            t = ts.peek()
            if decl and t.is_word("END") and ts.peek(1).is_word("DECLARATIVES"):
                break
            if (t.is_word("END") and ts.peek(1).is_word("PROGRAM")) or self.at_program_start():
                # the END PROGRAM marker or a contained program (parse() reads both)
                if decl:
                    raise ParseError(t, "DECLARATIVES without END DECLARATIVES")
                break
            if self.is_header(0):
                if decl and ts.peek(1).is_word("SECTION"):
                    break
                name = ts.next().val
                if ts.accept_word("SECTION"):
                    ts.accept_kind("NUM")
                    ts.expect_kind("PERIOD")
                    self.cur_sect = name
                    para = None
                    if ts.at_word("USE"):
                        raise ParseError(ts.peek(), "USE outside the DECLARATIVES")
                    continue
                ts.expect_kind("PERIOD")
                self.cur_para = name
                para = {"name": self.para_name(name, self.cur_sect), "sect": self.cur_sect,
                        "sentences": []}
                self.paras.append(para)
                continue
            if para is None:
                para = {"name": "", "sect": self.cur_sect, "sentences": []}
                self.paras.append(para)
            stmts = self.stmts()
            p = ts.peek()
            if p.kind != "PERIOD":
                raise ParseError(p, f"unexpected {p.val!r}")
            ts.next()
            if stmts:
                para["sentences"].append(stmts)
        if decl and ts.peek().kind == "EOF":
            raise ParseError(t, "DECLARATIVES without END DECLARATIVES")

    def declaratives(self):
        """`DECLARATIVES. {section-name SECTION. USE ... . paragraphs} END DECLARATIVES.`
        `USE AFTER STANDARD EXCEPTION/ERROR PROCEDURE ON files | INPUT | OUTPUT | I-O | EXTEND`
        declaratives are modelled (IBM rules, Cobol/Sem/Exec.lean `ioErr`); other USE forms
        make the program unsupported."""
        ts = self.ts
        start = ts.next()
        ts.expect_kind("PERIOD")
        while not (ts.at_word("END") and ts.peek(1).is_word("DECLARATIVES")):
            t = ts.peek()
            if t.kind == "EOF":
                raise ParseError(start, "DECLARATIVES without END DECLARATIVES")
            if not (self.is_header(0) and ts.peek(1).is_word("SECTION")):
                raise ParseError(t, "a declarative section header expected")
            name = ts.next().val
            ts.next()
            ts.accept_kind("NUM")
            ts.expect_kind("PERIOD")
            self.cur_sect = name
            nuse = len(self.use)
            self.use_stmt(name)
            n = len(self.paras)
            self.body(decl=True)
            if len(self.paras) == n and len(self.use) > nuse:
                # a (modelled) declarative without statements: an empty paragraph makes its section
                # exist for the resolver
                self.paras.append({"name": "", "sect": name, "sentences": []})
        ts.next(), ts.next(), ts.expect_kind("PERIOD")
        self.cur_sect = None

    def use_stmt(self, sect):
        """The USE statement heading a declarative section."""
        ts = self.ts
        u = ts.peek()
        if not u.is_word("USE"):
            raise ParseError(u, "a declarative section must begin with a USE statement")
        ts.next()
        unmodelled = None
        # USE GLOBAL: the declarative also serves the contained programs (IBM precedence rules for
        # nested programs; tools/cobolfe/unit.py)
        is_global = ts.accept_word("GLOBAL") is not None
        if ts.at_word("FOR", "DEBUGGING"):
            unmodelled = "USE FOR DEBUGGING"
        elif ts.at_word("BEFORE"):
            unmodelled = "USE BEFORE REPORTING"
        if unmodelled:
            self.drop(u.where(), unmodelled)
            ts.skip_to_period()
            return
        ts.expect_word("AFTER")
        ts.accept_word("STANDARD")
        ts.expect_word("EXCEPTION", "ERROR")
        ts.expect_word("PROCEDURE")
        ts.accept_word("ON")
        files, mode = [], None
        while ts.peek().kind not in ("PERIOD", "EOF"):
            t = ts.next()
            if t.is_word("INPUT", "OUTPUT", "I-O", "EXTEND") and not files and mode is None:
                mode = t.val
            elif is_user_word(t) and self.file_named(t.val) is not None and mode is None:
                files.append(self.file_named(t.val).id)
            else:
                raise ParseError(t, f"unexpected {t.val!r} in USE")
        ts.expect_kind("PERIOD")
        if not files and mode is None:
            raise ParseError(u, "USE without files or an open mode")
        self.use.append({"sect": sect, "files": files, "mode": mode})
        if is_global:
            self.use_global.add(sect)

    def is_header(self, k):
        t = self.ts.peek(k)
        if t.kind == "NUM" or is_user_word(t):
            n = self.ts.peek(k + 1)
            return n.kind == "PERIOD" or n.is_word("SECTION")
        return False

    def prescan(self):
        toks = self.ts.toks
        start = True
        sect = None
        # this program's procedure division ends at its END PROGRAM marker or at its first contained
        # program (or at the end of the source)
        end = next((i for i in range(self.ts.i, len(toks) - 1)
                    if (toks[i].is_word("END") and toks[i + 1].is_word("PROGRAM")) or
                    (toks[i].is_word("IDENTIFICATION", "ID") and toks[i + 1].is_word("DIVISION"))),
                   len(toks))
        # `ALTER p TO [PROCEED TO] q ...`: the targets each altered paragraph can be given
        self.alter = {}
        for i in range(self.ts.i, end):
            if toks[i].is_word("ALTER"):
                j = i + 1
                while j + 2 < end and is_user_word(toks[j]) and toks[j + 1].is_word("TO"):
                    k = j + 2
                    if toks[k].is_word("PROCEED") and toks[k + 1].is_word("TO"):
                        k += 2
                    if not is_user_word(toks[k]):
                        break
                    lst = self.alter.setdefault(toks[j].val, [])
                    if toks[k].val not in lst:
                        lst.append(toks[k].val)
                    j = k + 1
        # one hidden numeric item per altered paragraph: the position of its current target
        # in its target list (its GO TO becomes GO TO ... DEPENDING ON this item)
        self.alter_item = {}
        for p in self.alter:
            e = Entry(self.dd.ids(), 1, f"ALTER-STATE {p}", None, toks[self.ts.i], "working-storage")
            e.pic, e.cat = {"num": {"digits": 4, "scale": 0, "signed": False}}, "num"
            e.value = ("num", 1, 0)
            self.dd.records.append(e)
            self.alter_item[p] = e
        for i in range(self.ts.i, end):
            t = toks[i]
            if start and (t.kind == "NUM" or is_user_word(t)) and i + 1 < len(toks):
                n = toks[i + 1]
                if n.is_word("SECTION"):
                    sect = t.val
                    self.sections.add(t.val)
                elif n.kind == "PERIOD":
                    self.para_sects.setdefault(t.val, []).append(sect)
            start = t.kind == "PERIOD"

    def para_name(self, name, sect):
        """Emitted name of a paragraph: `NAME`, or `NAME OF SECT` when the name is reused in
        several sections."""
        if len(self.para_sects.get(name, [])) > 1:
            return f"{name} OF {sect}"
        return name

    def is_proc_name(self, t):
        return (t.kind == "NUM" or is_user_word(t)) and (t.val in self.para_sects or t.val in self.sections)

    def proc_ref(self):
        """A procedure name in PERFORM / GO TO: the emitted paragraph or section name."""
        ts = self.ts
        t = ts.next()
        if not self.is_proc_name(t):
            raise ParseError(t, f"unknown procedure name {t.val}")
        q = None
        if ts.at_word("OF", "IN") and (self.ts.peek(1).val in self.sections):
            ts.next()
            q = ts.next().val
        if t.val in self.sections and t.val not in self.para_sects:
            return t.val
        sects = self.para_sects.get(t.val, [])
        if len(sects) <= 1:
            return t.val
        s = q if q is not None else self.cur_sect
        if s not in sects:
            raise ParseError(t, f"ambiguous paragraph name {t.val}: qualify it")
        return f"{t.val} OF {s}"

    # ================================================================== statements
    def stmts(self):
        out = []
        ts = self.ts
        while True:
            t = ts.peek()
            if t.kind == "EXEC":
                out.extend(self.statement(self.st_EXEC))
                continue
            if t.kind != "WORD":
                break
            if t.val == "NEXT" and ts.peek(1).is_word("SENTENCE"):
                ts.next(), ts.next()
                out.append("nextSentence")
                continue
            if t.val not in VERBS:
                break
            h = getattr(self, "st_" + t.val.replace("-", "_"), None) or self.st_generic
            out.extend(self.statement(h))
        return out

    def statement(self, handler):
        t = self.ts.peek()
        self.frames.append([])
        self.ix_frames.append([])
        try:
            out = handler(t)
            if self.odo is not None and not self.frames[-1]:
                out = self.odo.lower(out)
        finally:
            reasons = self.frames.pop()
            touched = self.ix_frames.pop()
        if reasons:
            what = f"{t.val if t.kind == 'WORD' else 'EXEC'} (line {t.line}): " + \
                "; ".join(dict.fromkeys(reasons))
            self.unsupported.append((t.where(), what))
            return [{"unsupported": {"what": what}}]
        if touched:
            self.ix_stmts.append((out, touched, t))
        return out

    def unsup(self, what):
        if not self.frames:
            raise ParseError(self.ts.peek(), what)
        self.frames[-1].append(what)

    # ------------------------------------------------------------------ operands
    def at_identifier(self):
        return is_user_word(self.ts.peek()) and not self.is_proc_only(self.ts.peek())

    def is_proc_only(self, t):
        return not self.dd.knows(t.val) and t.val not in ("RETURN-CODE",)

    def identifier(self):
        ts = self.ts
        t = ts.expect_user_word()
        names = [t.val]
        while ts.at_word("OF", "IN"):
            ts.next()
            names.append(ts.expect_user_word().val)
        if len(names) > 1 and self.switch_mnem:
            # IBM: a switch's mnemonic name is its condition names' conditional variable
            names = names[:1] + [self.switch_mnem[q].name if q in self.switch_mnem else q
                                 for q in names[1:]]
        if names == ["RETURN-CODE"] and not self.dd.knows("RETURN-CODE"):
            # IBM: "When used in nested programs, this special register is implicitly defined with
            # the GLOBAL clause in the outermost program."
            self.outermost().special_register("RETURN-CODE", t)
        ent = self.dd.lookup(t, names, files=self.files)
        if isinstance(ent, IndexEntry):
            return X("idx", t, id=ent.id, entry=ent)
        subs = []
        if ts.peek().kind == "LPAR" and ent.dims() > 0 and not self.paren_has_colon():
            subs = self.subscripts()
        if len(subs) != ent.dims():
            self.unsup(f"{ent.name}: {len(subs)} subscripts for {ent.dims()} table levels")
        if isinstance(ent, CondEntry):
            self.ix_shared(ent.parent)
            return X("cond", t, id=ent.id, subs=subs, entry=ent)
        rs = rl = None
        if ts.peek().kind == "LPAR" and self.paren_has_colon():
            ts.next()
            rs = self.sub_of(self.arith(), "reference modification")
            ts.expect_kind("COLON")
            if ts.peek().kind != "RPAR":
                rl = self.sub_of(self.arith(), "reference modification")
            ts.expect_kind("RPAR")
        if ent.index:
            if rs is not None:
                self.unsup(IX_DIRECT)
            if ent is self.ix_watch:
                self.unsup("the VARYING index data item of a SEARCH in a WHEN condition")
            return X("ixd", t, entry=ent, subs=subs)
        self.ix_shared(ent)
        return X("ref", t, entry=ent, subs=subs, rs=rs, rl=rl)

    # ------------------------------------------------------------------ index data items
    def ix_shared(self, ent):
        """A reference to an item sharing bytes with an index data item, whose contents are
        implementation-defined, is unsupported, except where the caller has asked to check the
        statement itself (`ix_allow`: LENGTH OF, INITIALIZE, a group MOVE)."""
        x = self.dd.overlap_ix(ent)
        if x is None:
            return
        if self.ix_allow:
            self.ix_allow[-1].append(ent)
        else:
            self.unsup(f"{ent.name} shares storage with the index data item {x.name}, whose bytes are "
                       "implementation-defined")

    def ix_group_move(self, src, dsts, shared):
        """A MOVE whose sender or receivers share bytes with index data items (`shared`: those
        items). IBM: an index data item "can be part of an alphanumeric group item that is
        referenced in a MOVE statement", with "no conversion of values". The bytes of an index data
        item reach only an index data item, so the result does not depend on their contents, when
        the sender and every receiver are groups of one length with index data items at the same
        offsets (and none overlaid through a REDEFINES); the items at each offset then exchange
        values. Any other such MOVE is unsupported."""
        ops = [src] + list(dsts)

        def layout(x):
            if x.kind != "ref" or x.rs is not None or not x.entry.is_group():
                return None
            e = x.entry
            if any(e not in i.ancestors() for i in self.dd.overlap_ix_all(e)):
                return None
            return item_size(e), sub_ix_offsets(e)
        lays = [layout(x) for x in ops]
        whole = {id(x.entry) for x in ops if x.kind == "ref"}

        def shape(l):
            return l[0], [o for o, _ in l[1]]
        if any(id(e) not in whole for e in shared) or None in lays or \
                any(shape(l) != shape(lays[0]) for l in lays):
            self.unsup(f"MOVE of a group with index data items whose bytes would reach other bytes "
                       f"({shared[0].name} and the index data item {self.dd.overlap_ix(shared[0]).name})")
            return
        for l in lays[1:]:
            for (_, a), (_, b) in zip(lays[0][1], l[1]):
                self.ix_union(a, b)

    def ix_ref(self, x):
        """The hidden child holding the value of the index data item x (an `ixd` operand)."""
        return {"item": x.entry.ixid, "subs": x.subs, "refStart": None, "refLen": None}

    def ix_len(self, idx_id):
        """Element length of the table of an index name (IBM: an index value is (occurrence - 1) x
        this length)."""
        ie = next(i for i in self.dd.indexes if i.id == idx_id)
        return item_size(ie.table)

    def ix_find(self, e):
        p = self.ix_parent.setdefault(e.id, e.id)
        if p != e.id:
            r = self.ix_find(self.ix_entries[p])
            self.ix_parent[e.id] = r
            return r
        return p

    def ix_union(self, a, b):
        """Index data items a and b exchange values (SET, comparison, group MOVE)."""
        self.ix_entries[a.id], self.ix_entries[b.id] = a, b
        ra, rb = self.ix_find(a), self.ix_find(b)
        if ra != rb:
            self.ix_parent[ra] = rb
            self.ix_lens.setdefault(rb, set()).update(self.ix_lens.pop(ra, set()))
        self.ix_touch(a)
        self.ix_touch(b)

    def ix_link(self, e, idx_id=None, length=None):
        """Index data item e exchanges values with an index name (or with the index of a table whose
        elements are `length` bytes long)."""
        self.ix_entries[e.id] = e
        n = self.ix_len(idx_id) if length is None else length
        self.ix_lens.setdefault(self.ix_find(e), set()).add(n)
        self.ix_touch(e)

    def ix_touch(self, e):
        if self.ix_frames:
            self.ix_frames[-1].append(e)

    def ix_finish(self):
        """IBM keeps an index value as a displacement, (occurrence - 1) x element length, and moves
        it between index names and index data items without conversion; GnuCOBOL keeps the
        occurrence number. The two agree, and so does the model (occurrence numbers), as long as
        each index data item exchanges values only with index names of tables with one element
        length. Statements touching index data items whose values meet several element lengths
        become unsupported."""
        mixed = {r: sorted(ls) for r, ls in self.ix_lens.items() if len(ls) > 1 and self.ix_find(self.ix_entries[r]) == r}
        for out, touched, t in self.ix_stmts:
            bad = sorted({e.name for e in touched if self.ix_find(e) in mixed})
            if not bad or id(out) in self.ix_done:
                continue
            self.ix_done.add(id(out))
            lens = sorted({n for e in touched if self.ix_find(e) in mixed for n in mixed[self.ix_find(e)]})
            what = (f"{t.val if t.kind == 'WORD' else 'EXEC'} (line {t.line}): index data item(s) "
                    f"{', '.join(bad)} take index values of tables with element lengths "
                    f"{', '.join(map(str, lens))} (IBM moves displacements, GnuCOBOL occurrence numbers)")
            self.unsupported.append((t.where(), what))
            first = True
            for d in out:
                if isinstance(d, dict):
                    d.clear()
                    if first:
                        d["unsupported"] = {"what": what}
                        first = False
                    else:
                        d["performInline"] = {"body": [], "loop": "once"}

    def special_register(self, name, tok):
        """Declare a special register on first use (IBM: RETURN-CODE is S9(4) BINARY, zero)."""
        e = Entry(self.fresh(), 1, name, None, tok, "working")
        e.pic, e.cat, e.usage_kw = {"num": {"digits": 4, "scale": 0, "signed": True}}, "num", "BINARY"
        e.value = ("num", 0, 0, 1)
        e.is_global = True
        self.dd.records.append(e)
        self.dd.by_name[name] = [e]

    def paren_has_colon(self):
        toks, i = self.ts.toks, self.ts.i
        depth = 0
        while i < len(toks):
            t = toks[i]
            if t.kind == "LPAR":
                depth += 1
            elif t.kind == "RPAR":
                depth -= 1
                if depth == 0:
                    return False
            elif t.kind == "COLON" and depth == 1:
                return True
            elif t.kind in ("PERIOD", "EOF"):
                return False
            i += 1
        return False

    def subscripts(self):
        ts = self.ts
        ts.expect_kind("LPAR")
        subs = []
        while ts.peek().kind != "RPAR":
            t = ts.peek()
            if t.kind in ("PERIOD", "EOF"):
                raise ParseError(t, "unclosed subscript")
            if t.is_word("ALL"):
                ts.next()
                self.unsup("subscript ALL")
                subs.append({"lit": {"n": 1}})
                continue
            subs.append(self.sub_of(self.sub_expr(), "subscript"))
        ts.expect_kind("RPAR")
        return subs

    def sub_expr(self):
        """One subscript: integer, or (data / index name) [+|- integer]."""
        ts = self.ts
        t = ts.peek()
        if t.kind == "NUM":
            ts.next()
            v, s, _ = lit_number(t)
            return X("num", t, v=v, scale=s, digits=0)
        x = self.identifier()
        n = ts.peek()
        if n.kind == "OP" and n.val in "+-" and not n.sep and ts.peek(1).kind == "NUM":
            ts.next()
            k = ts.next()
            v, s, _ = lit_number(k)
            return X("bin", n, op=n.val, a=x, b=X("num", k, v=v, scale=s, digits=0))
        # a signed literal after the name (`T(I -1)`) is the next subscript, as in GnuCOBOL
        return x

    def sub_of(self, x, what):
        """Surface `Sub` of a subscript / reference-modification expression."""
        def base(y, k):
            if y.kind == "idx":
                return {"idx": {"id": y.id, "k": k}}
            if y.kind == "ref" and not y.subs and y.rs is None and y.entry.numeric() \
                    and y.entry.pic["num"]["scale"] <= 0:
                return {"item": {"id": y.entry.id, "k": k}}
            return None
        def linear(y):
            """(name, k) for name + k, or (None, k) for the integer k: integer literals and at
            most one name (coefficient 1) under +, -, * and parentheses, evaluated exactly (IBM:
            reference modifiers are arithmetic expressions); None for any other expression."""
            if y.kind == "num":
                return (None, y.v) if y.scale == 0 else None
            if y.kind == "fig" and y.name == "ZERO":
                return (None, 0)
            if y.kind == "paren":
                return linear(y.a)
            if y.kind == "neg":
                a = linear(y.a)
                return (None, -a[1]) if a is not None and a[0] is None else None
            if y.kind == "bin" and y.op in "+-*":
                a, c = linear(y.a), linear(y.b)
                if a is None or c is None:
                    return None
                if y.op == "*":
                    return (None, a[1] * c[1]) if a[0] is None and c[0] is None else None
                if y.op == "-":
                    return (a[0], a[1] - c[1]) if c[0] is None else None
                if a[0] is not None and c[0] is not None:
                    return None
                return (a[0] if a[0] is not None else c[0], a[1] + c[1])
            return (y, 0) if base(y, 0) is not None else None
        lin = linear(x)
        if lin is not None:
            return {"lit": {"n": lin[1]}} if lin[0] is None else base(lin[0], lin[1])
        if x.kind == "ixd" or (x.kind == "bin" and x.a.kind == "ixd"):
            # IBM: "You cannot use index data items as subscripts or indexes."
            self.unsup(f"index data item as a {what}")
            return {"lit": {"n": 1}}
        self.unsup(f"{what} not of the form literal / name [+|- integer]")
        return {"lit": {"n": 1}}

    def primary(self):
        """Identifier, literal, figurative constant, ALL literal or intrinsic function."""
        ts = self.ts
        t = ts.peek()
        if t.kind == "NUM":
            ts.next()
            v, s, d = lit_number(t)
            return X("num", t, v=v, scale=s, digits=d)
        if t.kind == "STR":
            ts.next()
            return X("str", t, s=t.val)
        if t.kind == "HEX":
            ts.next()
            return X("hex", t, b=t.val)
        if t.kind in ("NSTR", "ZSTR"):
            ts.next()
            self.unsup(f"{t.kind} literal")
            return X("str", t, s="")
        if t.kind == "WORD":
            if t.val in FIGURATIVE:
                ts.next()
                if FIGURATIVE[t.val] == "NULL":
                    self.unsup("NULL")
                return X("fig", t, name=FIGURATIVE[t.val])
            if t.val == "ALL":
                ts.next()
                inner = self.primary()
                if inner.kind not in ("str", "fig", "hex"):
                    raise ParseError(t, "ALL must be followed by a literal")
                return X("all", t, lit=inner)
            if t.val == "FUNCTION":
                return self.function()
            if t.val == "LENGTH" and ts.peek(1).is_word("OF"):
                # the item's size in bytes, a compile-time constant
                ts.next(), ts.next()
                # a length reads no bytes, so items sharing storage with index data items qualify
                self.ix_allow.append([])
                try:
                    x = self.identifier()
                finally:
                    self.ix_allow.pop()
                if x.kind not in ("ref", "ixd") or x.entry is None:
                    self.unsup("LENGTH OF a non-data item")
                    return X("num", t, v=0, scale=0, digits=1)
                if self.odo_group(x.entry):
                    self.unsup("LENGTH OF a group containing an OCCURS DEPENDING ON table (its length varies)")
                n = item_size(x.entry)
                return X("num", t, v=n, scale=0, digits=len(str(n)))
            if t.val == "ADDRESS" and ts.peek(1).is_word("OF"):
                ts.next(), ts.next()
                self.identifier()
                self.unsup("ADDRESS OF")
                return X("num", t, v=0, scale=0, digits=1)
            if is_user_word(t):
                return self.identifier()
        raise ParseError(t, f"expected an operand, found {t.val!r}")

    def function(self):
        ts = self.ts
        t = ts.expect_word("FUNCTION")
        nt = ts.next()
        if nt.kind != "WORD":
            raise ParseError(nt, "expected a function name")
        name = nt.val
        args = []
        if ts.peek().kind == "LPAR" and not self.paren_has_colon():
            ts.next()
            while ts.peek().kind != "RPAR":
                if ts.peek().kind in ("PERIOD", "EOF"):
                    raise ParseError(nt, "unclosed function arguments")
                args.append(self.arith())
            ts.next()
        x = X("fn", t, name=name, args=args, refmod=None)
        if ts.peek().kind == "LPAR" and self.paren_has_colon():
            ts.next()
            s = self.arith()
            ts.expect_kind("COLON")
            n = None
            if ts.peek().kind != "RPAR":
                n = self.arith()
            ts.expect_kind("RPAR")
            x.refmod = (s, n)
            if name not in ("CURRENT-DATE", "WHEN-COMPILED"):
                self.unsup(f"reference modification of FUNCTION {name}")
        if name == "LENGTH":
            return self.fn_length(x)
        if name == "WHEN-COMPILED":
            return self.fn_when_compiled(x)
        if name not in FUNCTIONS and name not in AFUNCTIONS and name not in SEQ_FUNCTIONS and \
                name != "CURRENT-DATE":
            self.unsup(f"FUNCTION {name}")
        return x

    def static_len(self, a):
        """Length in bytes of an alphanumeric or hexadecimal literal, a data item without
        reference modification, or an alphanumeric function of one (which keeps its argument's
        length); None for anything else."""
        if a.kind == "paren":
            a = a.a
        if a.kind == "str":
            return len(a.s)
        if a.kind == "hex":
            return len(a.b)
        if a.kind == "ref" and a.entry is not None and a.rs is None:
            return None if self.odo_group(a.entry) else item_size(a.entry)
        if a.kind == "fn" and a.name in AFUNCTIONS and len(a.args) == 1 and a.refmod is None:
            return self.static_len(a.args[0])
        return None

    def fn_length(self, x):
        """`FUNCTION LENGTH (arg)`: the argument's length in bytes, a compile-time constant."""
        n = self.static_len(x.args[0]) if len(x.args) == 1 and x.refmod is None else None
        if n is None:
            self.unsup("FUNCTION LENGTH of this argument")
            n = 0
        return X("num", x.tok, v=n, scale=0, digits=len(str(n)))

    def fn_when_compiled(self, x):
        """`FUNCTION WHEN-COMPILED [(start:len)]`: the time of compilation, i.e. of this front
        end's run (or `--when-compiled`), as 21 characters YYYYMMDDhhmmsshh+hhmm."""
        if self.when_compiled is None:
            now = datetime.datetime.now(datetime.timezone.utc)
            self.when_compiled = now.strftime("%Y%m%d%H%M%S") + f"{now.microsecond // 10000:02d}+0000"
        s = self.when_compiled
        if x.args:
            self.unsup("FUNCTION WHEN-COMPILED with arguments")
        if x.refmod is not None:
            st, n = x.refmod
            if st.kind != "num" or st.scale != 0 or (n is not None and (n.kind != "num" or n.scale != 0)):
                self.unsup("FUNCTION WHEN-COMPILED with a variable reference modification")
            else:
                start = st.v
                length = n.v if n is not None else 21 - start + 1
                if not (1 <= start <= 21 and 1 <= length <= 21 - start + 1):
                    raise ParseError(x.tok, "reference modification outside FUNCTION WHEN-COMPILED")
                s = s[start - 1:start - 1 + length]
        return X("str", x.tok, s=s)

    # ------------------------------------------------------------------ arithmetic expressions
    def arith(self):
        ts = self.ts
        a = self.term()
        while True:
            t = ts.peek()
            if t.kind == "OP" and t.val in ("+", "-") and not t.sep:
                ts.next()
                a = X("bin", t, op=t.val, a=a, b=self.term())
            else:
                # also before a signed literal (`MAX(A -1)`) and before an operator that follows
                # a separator comma (`MAX(A, - 1)`): both start the next operand, as in GnuCOBOL
                return a

    def term(self):
        ts = self.ts
        a = self.power()
        while ts.peek().kind == "OP" and ts.peek().val in ("*", "/") and not ts.peek().sep:
            t = ts.next()
            a = X("bin", t, op=t.val, a=a, b=self.power())
        return a

    def power(self):
        ts = self.ts
        a = self.unary()
        while ts.peek().kind == "OP" and ts.peek().val == "**" and not ts.peek().sep:
            t = ts.next()
            a = X("pow", t, a=a, b=self.unary())
        return a

    def unary(self):
        ts = self.ts
        t = ts.peek()
        if t.kind == "OP" and t.val in ("+", "-"):
            ts.next()
            a = self.unary()
            return a if t.val == "+" else X("neg", t, a=a)
        if t.kind == "LPAR":
            ts.next()
            a = self.arith()
            ts.expect_kind("RPAR")
            return X("paren", t, a=a)
        return self.primary()

    # ------------------------------------------------------------------ JSON of operands
    def to_expr(self, x):
        k = x.kind
        if k == "paren":
            return self.to_expr(x.a)
        if k == "num":
            return {"lit": {"v": x.v, "scale": x.scale}}
        if k == "ref":
            if x.rs is not None:
                self.unsup("reference-modified operand in arithmetic")
            elif not x.entry.numeric():
                self.unsup(f"non-numeric item {x.entry.name} in arithmetic")
            return {"ref": {"r": self.ref_json(x)}}
        if k == "idx":
            return {"idx": {"id": x.id}}
        if k == "fig" and x.name == "ZERO":
            return {"lit": {"v": 0, "scale": 0}}
        if k == "neg":
            return {"neg": {"a": self.to_expr(x.a)}}
        if k == "bin":
            op = {"+": "add", "-": "sub", "*": "mul", "/": "div"}[x.op]
            j = {op: {"a": self.to_expr(x.a), "b": self.to_expr(x.b)}}
            if op == "div":
                j["div"]["scale"] = self.div_scale
            return j
        if k == "pow":
            b = x.b.a if x.b.kind == "paren" else x.b
            if b.kind == "num" and b.scale == 0 and 0 <= b.v <= 64:
                return {"pow": {"a": self.to_expr(x.a), "n": b.v}}
            if getattr(x, "int_exp", False):
                # an exponent that is an integral data item or expression (mark_int_exps)
                return {"powE": {"a": self.to_expr(x.a), "e": self.to_expr(x.b)}}
            self.unsup("exponent other than a small integer literal")
            return {"lit": {"v": 0, "scale": 0}}
        if k == "fn":
            if x.name in ("ORD", "ORD-MAX", "ORD-MIN"):
                return self.seq_fn_expr(x)
            if x.name in FUNCTIONS:
                return {"fn": {"name": x.name, "args": [self.to_expr(a) for a in x.args]}}
            self.unsup(f"FUNCTION {x.name} in arithmetic")
            return {"lit": {"v": 0, "scale": 0}}
        if k == "cond":
            self.unsup("condition name used as a value")
        elif k == "ixd":
            self.unsup(IX_DIRECT)
        else:
            self.unsup(f"non-numeric operand in arithmetic")
        return {"lit": {"v": 0, "scale": 0}}

    def to_operand(self, x):
        k = x.kind
        if k == "paren":
            return self.to_operand(x.a)
        if k == "ref":
            return {"ref": {"r": self.ref_json(x)}}
        if k == "num":
            return {"lit": {"l": {"num": {"v": x.v, "scale": x.scale, "digits": x.digits}}}}
        if k == "str":
            return {"lit": {"l": {"str": {"s": x.s}}}}
        if k == "hex":
            return {"lit": {"l": {"hex": {"h": x.b.hex().upper()}}}}
        if k == "fig":
            return {"lit": {"l": {"fig": {"name": x.name}}}}
        if k == "all":
            if x.lit.kind == "fig":
                return self.to_operand(x.lit)
            if x.lit.kind == "str":
                return {"lit": {"l": {"all": {"s": x.lit.s}}}}
            self.unsup("ALL with a hexadecimal literal")
        elif k == "fn":
            if x.name in AFUNCTIONS and x.refmod is None and len(x.args) == 1:
                a = x.args[0].a if x.args[0].kind == "paren" else x.args[0]
                if (a.kind == "ref" and a.entry is not None and not a.entry.numeric()) or \
                        a.kind in ("str", "hex") or (a.kind == "fn" and a.name in AFUNCTIONS):
                    return {"fn": {"name": x.name, "args": [self.to_operand(a)]}}
                self.unsup(f"FUNCTION {x.name} of a non-alphanumeric argument")
            elif self.seq_alnum_fn(x):
                return self.seq_fn_operand(x)
            else:
                self.unsup(f"FUNCTION {x.name} as an operand")
        elif k == "idx":
            self.unsup("index name as an operand")
        elif k == "ixd":
            self.unsup(IX_DIRECT)
        elif k == "cond":
            self.unsup("condition name as an operand")
        else:
            self.unsup("arithmetic expression where an operand is required")
        return {"lit": {"l": {"fig": {"name": "ZERO"}}}}

    # ------------------------------------------------------------------ integral exponents
    # IBM evaluates `op1 ** op2` in fixed point when op2 is an integral data-name or variable: the
    # power is held with dmax decimal places (Cobol.Expr.powInt). The front end takes that path for
    # an exponent that is not a literal, only where the resolver's dmax is IBM's: a COMPUTE without
    # ROUNDED into numeric items and without INTEGER or INTEGER-PART of an argument with decimal
    # places, or a relation or sign condition whose operands are all integers (dmax 0); and not
    # inside a function argument or under a literal exponent. Every other exponent keeps the old path.
    def int_exp_ok(self, b):
        """b is a non-constant integral exponent: numeric items without decimal places or
        reference modification, integer literals, unary minus, parentheses and + - *, with at
        least one item (decimal places, a division, a power or a function may make IBM's
        evaluation floating point)."""
        def walk(z):
            if z.kind in ("paren", "neg"):
                return walk(z.a)
            if z.kind == "bin" and z.op in ("+", "-", "*"):
                p, q = walk(z.a), walk(z.b)
                return None if p is None or q is None else p or q
            if z.kind == "num":
                return False if z.scale == 0 else None
            if z.kind == "ref" and z.entry is not None and z.entry.numeric() and z.rs is None and \
                    z.entry.pic["num"]["scale"] <= 0:
                return True
            return None
        return walk(b) is True

    def mark_int_exps(self, x, on):
        """Set int_exp on every power of x outside function arguments and literal-exponent
        bases: on, and its exponent is not a literal from 0 to 64 and is int_exp_ok."""
        if x.kind == "pow":
            b = x.b.a if x.b.kind == "paren" else x.b
            lit = b.kind == "num" and b.scale == 0 and 0 <= b.v <= 64
            x.int_exp = on and not lit and self.int_exp_ok(x.b)
            # under a literal exponent IBM takes such a power as a variable of 30 - dmax integer
            # places and so holds the outer power with dmax places too; the old path is exact
            self.mark_int_exps(x.a, on and not lit)
        elif x.kind in ("paren", "neg"):
            self.mark_int_exps(x.a, on)
        elif x.kind == "bin":
            self.mark_int_exps(x.a, on)
            self.mark_int_exps(x.b, on)

    def entry_by_id(self, iid):
        """The data item with id iid in this program's data division or a containing one's."""
        dd = self.dd
        while dd is not None:
            stack = list(dd.records)
            while stack:
                e = stack.pop()
                if e.id == iid:
                    return e
                stack += e.children
            dd = dd.outer
        return None

    def compute_int_exps(self, e, rcv):
        """COMPUTE: the integral-exponent path needs receivers that are numeric items (the
        resolver's dmax counts their decimal places, not a numeric-edited item's), no ROUNDED
        (IBM: one more decimal place "might be carried") and int_fn_ok."""
        def numeric(r):
            ent = self.entry_by_id(r["ref"]["item"])
            return ent is not None and ent.numeric() and r["ref"]["refStart"] is None
        self.mark_int_exps(e, all(r["rounded"] is None and numeric(r) for r in rcv) and self.int_fn_ok(e))

    def int_fn_ok(self, x):
        """No FUNCTION INTEGER or INTEGER-PART in x has an argument with decimal places (IBM gives
        an integer function no decimal places in dmax, the resolver counts its argument's)."""
        k = x.kind
        if k == "fn":
            if x.name in ("INTEGER", "INTEGER-PART") and not all(self.int_leaves(a) for a in x.args):
                return False
            return all(self.int_fn_ok(a) for a in x.args)
        if k in ("paren", "neg"):
            return self.int_fn_ok(x.a)
        if k in ("bin", "pow"):
            return self.int_fn_ok(x.a) and self.int_fn_ok(x.b)
        return True

    def int_leaves(self, x):
        """Every literal and data item of x, function arguments included, is an integer."""
        k = x.kind
        if k == "num":
            return x.scale <= 0
        if k == "ref":
            return x.entry is not None and x.entry.numeric() and x.rs is None and \
                x.entry.pic["num"]["scale"] <= 0
        if k in ("paren", "neg"):
            return self.int_leaves(x.a)
        if k in ("bin", "pow"):
            return self.int_leaves(x.a) and self.int_leaves(x.b)
        if k == "fn":
            return all(self.int_leaves(a) for a in x.args)
        return k in ("idx", "fig")

    def cond_int_exps(self, *xs):
        """A relation or sign condition: the integral-exponent path needs integer operands only
        (IBM's dmax for a comparison is that of both comparands' operands; the resolver uses 0)."""
        on = all(self.int_leaves(x) for x in xs)
        for x in xs:
            self.mark_int_exps(x, on)

    # ------------------------------------------------------------------ collating-sequence functions
    def arg_class(self, a):
        """Class of a function argument: "num", "alnum" (alphanumeric or alphabetic items,
        reference-modified items, alphanumeric literals, alphanumeric functions) or None."""
        if a.kind == "paren":
            return self.arg_class(a.a)
        if a.kind == "num":
            return "num"
        if a.kind in ("str", "hex"):
            return "alnum"
        if a.kind == "ref" and a.entry is not None:
            return "num" if a.entry.numeric() and a.rs is None else "alnum"
        if a.kind in ("neg", "bin", "pow", "idx"):
            return "num"
        if a.kind == "fn":
            if self.seq_alnum_fn(a) or (a.name in AFUNCTIONS and a.refmod is None):
                return "alnum"
            if a.name in FUNCTIONS or a.name in ("ORD", "ORD-MAX", "ORD-MIN"):
                return "num"
        return None

    def seq_alnum_fn(self, x):
        """CHAR, and MAX / MIN of alphanumeric arguments: alphanumeric operands."""
        if x.kind != "fn" or x.refmod is not None or not x.args:
            return False
        if x.name == "CHAR":
            return True
        return x.name in ("MAX", "MIN") and all(self.arg_class(a) == "alnum" for a in x.args)

    def seq_fn_operand(self, x):
        """CHAR (an integer item or literal) and alphanumeric MAX / MIN, as surface operands; MAX
        and MIN as nested pairs (MAX (MAX (a, b), c) is MAX (a, b, c): the leftmost greatest)."""
        args = [a.a if a.kind == "paren" else a for a in x.args]
        if x.name == "CHAR":
            a = args[0]
            if len(args) == 1 and (a.kind == "num" and a.scale == 0 or a.kind == "ref" and a.entry is not None
                                   and a.entry.numeric() and a.rs is None and a.entry.pic["num"]["scale"] == 0):
                return {"fn": {"name": "CHAR", "args": [self.to_operand(a)]}}
            self.unsup("FUNCTION CHAR of an argument that is not an integer item or literal")
            return {"lit": {"l": {"fig": {"name": "ZERO"}}}}
        ops = [self.to_operand(a) for a in args]
        acc = {"fn": {"name": x.name, "args": ops[:1]}} if len(ops) == 1 else ops[0]
        for o in ops[1:]:
            acc = {"fn": {"name": x.name, "args": [acc, o]}}
        return acc

    def seq_fn_expr(self, x):
        """ORD (one alphanumeric argument), ORD-MAX and ORD-MIN (alphanumeric or numeric
        arguments) as surface expressions."""
        args = [a.a if a.kind == "paren" else a for a in x.args]
        cls = [self.arg_class(a) for a in args]
        if x.name == "ORD":
            if len(args) == 1 and cls[0] == "alnum":
                return {"afn": {"name": "ORD", "args": [self.to_operand(args[0])]}}
            self.unsup("FUNCTION ORD of an argument that is not alphanumeric")
        elif args and all(c == "alnum" for c in cls):
            return {"afn": {"name": x.name, "args": [self.to_operand(a) for a in args]}}
        elif args and all(c == "num" for c in cls):
            return {"fn": {"name": x.name, "args": [self.to_expr(a) for a in args]}}
        else:
            self.unsup(f"FUNCTION {x.name} of arguments that are neither all numeric nor all alphanumeric")
        return {"lit": {"v": 0, "scale": 0}}

    def ref_json(self, x):
        return {"item": x.entry.id, "subs": x.subs, "refStart": x.rs, "refLen": x.rl}

    def ref_of(self, x, what="receiver"):
        if x.kind == "ref":
            return self.ref_json(x)
        self.unsup(IX_DIRECT if x.kind == "ixd" else f"{what} is not a data item")
        return {"item": 0, "subs": [], "refStart": None, "refLen": None}

    def receivers(self, rounded_ok=True):
        """`id [ROUNDED [MODE [IS] m]] ...`"""
        out = []
        while self.at_identifier():
            x = self.identifier()
            r = None
            if self.ts.accept_word("ROUNDED"):
                if not rounded_ok:
                    raise ParseError(x.tok, "ROUNDED not allowed here")
                r = "NEAREST-AWAY-FROM-ZERO"
                if self.ts.accept_word("MODE"):
                    self.ts.accept_word("IS")
                    m = self.ts.next()
                    if m.val not in ROUNDING_MODES:
                        raise ParseError(m, f"unknown rounding mode {m.val}")
                    r = m.val
            out.append({"ref": self.ref_of(x), "rounded": r})
        if not out:
            raise ParseError(self.ts.peek(), "expected a receiving item")
        return out

    def identifiers(self):
        out = []
        while self.at_identifier():
            out.append(self.identifier())
        return out

    # ------------------------------------------------------------------ conditions
    def cond(self):
        return self.cond_or({"subj": None, "op": None})

    def cond_or(self, st):
        a = self.cond_and(st)
        while self.ts.accept_word("OR"):
            a = {"or": {"a": a, "b": self.cond_and(st)}}
        return a

    def cond_and(self, st):
        a = self.cond_not(st)
        while self.ts.accept_word("AND"):
            a = {"and": {"a": a, "b": self.cond_not(st)}}
        return a

    def cond_not(self, st):
        ts = self.ts
        if ts.at_word("NOT") and not self.relop_at(1):
            ts.next()
            return {"not": {"c": self.cond_not(st)}}
        return self.cond_simple(st)

    def relop_at(self, k):
        save = self.ts.i
        self.ts.i += k
        try:
            return self.try_relop() is not None
        finally:
            self.ts.i = save

    def try_relop(self):
        ts = self.ts
        save = ts.i
        ts.accept_word("IS")
        neg = ts.accept_word("NOT") is not None
        t = ts.peek()
        op = None
        if t.kind == "OP" and t.val in ("=", "<", ">", "<=", ">=", "<>"):
            ts.next()
            op = t.val
        elif t.is_word("EQUAL"):
            ts.next()
            ts.accept_word("TO")
            op = "="
        elif t.is_word("GREATER", "LESS"):
            ts.next()
            ts.accept_word("THAN")
            op = ">" if t.val == "GREATER" else "<"
            if ts.at_word("OR") and ts.peek(1).is_word("EQUAL"):
                ts.next(), ts.next()
                ts.accept_word("TO")
                op += "="
        if op is None:
            ts.i = save
            return None
        return (neg, op)

    def rel_json(self, r, a, b):
        neg, op = r
        if neg:
            op = NEG_OP[op]
        if a.kind == "ixd" or b.kind == "ixd":
            # IBM: an index data item compared with an index name or another index data item:
            # "the actual values are compared without conversion"; any other comparison involving
            # an index data item is undefined
            if a.kind not in ("ixd", "idx") or b.kind not in ("ixd", "idx"):
                self.unsup("comparison of an index data item with an operand other than an index name or index data item")
                return {"const": {"b": False}}
            for x, y in ((a, b), (b, a)):
                if x.kind == "ixd" and y.kind == "idx":
                    self.ix_link(x.entry, y.id)
            if a.kind == "ixd" and b.kind == "ixd":
                self.ix_union(a.entry, b.entry)

            def val(x):
                return {"idx": {"id": x.id}} if x.kind == "idx" else {"ref": {"r": self.ix_ref(x)}}
            return {"relExpr": {"op": op, "a": val(a), "b": val(b)}}
        def simple(x):
            return x.kind in SIMPLE or (x.kind == "fn" and x.name in AFUNCTIONS) or self.seq_alnum_fn(x)
        if simple(a) and simple(b):
            return {"rel": {"op": op, "a": self.to_operand(a), "b": self.to_operand(b)}}
        self.cond_int_exps(a, b)
        return {"relExpr": {"op": op, "a": self.to_expr(a), "b": self.to_expr(b)}}

    def cond_simple(self, st):
        ts = self.ts
        t = ts.peek()
        if t.kind == "LPAR":
            save = (ts.i, dict(st), len(self.frames[-1]) if self.frames else 0)
            try:
                ts.next()
                c = self.cond_or(st)
                if ts.peek().kind == "RPAR":
                    ts.next()
                    n = ts.peek()
                    if not ((n.kind == "OP" and n.val in ("+", "-", "*", "/", "**")) or
                            self.relop_at(0) or self.class_or_sign_at()):
                        return c
            except ParseError:
                pass
            ts.i = save[0]
            st.clear()
            st.update(save[1])
            if self.frames:
                del self.frames[-1][save[2]:]
        r = self.try_relop()
        if r is not None:
            if st["subj"] is None:
                raise ParseError(t, "relational operator without a subject")
            obj = self.arith()
            st["op"] = r
            return self.rel_json(r, st["subj"], obj)
        e = self.arith()
        if e.kind == "cond":
            return {"cond88": {"id": e.id, "subs": e.subs}}
        cs = self.class_or_sign()
        if cs is not None:
            neg, kind, word = cs
            if kind == "uclass":
                c = self.uclass_cond(e, word)
            elif kind == "class":
                if e.kind != "ref":
                    self.unsup("class condition on a non-identifier")
                c = {"cls": {"test": word, "r": self.ref_of(e, "class condition subject")}}
            else:
                self.cond_int_exps(e)
                c = {"sign": {"test": word, "e": self.to_expr(e)}}
            return {"not": {"c": c}} if neg else c
        r = self.try_relop()
        if r is not None:
            obj = self.arith()
            st["subj"], st["op"] = e, r
            return self.rel_json(r, e, obj)
        if st["subj"] is None or st["op"] is None:
            raise ParseError(ts.peek(), f"expected a condition, found {ts.peek().val!r}")
        return self.rel_json(st["op"], st["subj"], e)

    def class_or_sign_at(self):
        save = self.ts.i
        try:
            return self.class_or_sign() is not None
        finally:
            self.ts.i = save

    def class_or_sign(self):
        """`[IS] [NOT] NUMERIC | ALPHABETIC... | class-name | POSITIVE | NEGATIVE | ZERO`."""
        ts = self.ts
        save = ts.i
        ts.accept_word("IS")
        neg = ts.accept_word("NOT") is not None
        t = ts.peek()
        if t.kind == "WORD" and t.val in CLASSES:
            ts.next()
            return (neg, "class", t.val)
        if t.kind == "WORD" and t.val in self.classes:
            ts.next()
            return (neg, "uclass", t.val)
        if t.kind == "WORD" and t.val in SIGNS:
            n = ts.peek(1)
            # `A = B OR ZERO` is an abbreviated relation: ZERO there follows OR / AND
            ts.next()
            return (neg, "sign", SIGNS[t.val])
        if t.kind == "WORD" and t.val in ("DBCS", "KANJI"):
            ts.next()
            self.unsup(f"class condition {t.val}")
            return (neg, "class", "NUMERIC")
        ts.i = save
        return None

    def uclass_cond(self, e, name):
        """`e IS class-name` (IBM: "identifier-1 consists entirely of the characters listed in
        the definition of class-name"): for each byte position i of e, the byte e(i:1) lies in
        one of the class's runs of consecutive byte values: `= X'lo'`, or `>= X'lo'` and `<= X'hi'`
        (a bound at X'00' or X'FF' left out); all positions ANDed, the runs ORed, both as balanced
        trees. These are comparisons of one byte with one byte: no padding, the native byte order,
        so exact. Unsupported: a program collating sequence given by literals (the comparisons
        would be collated), a subject that is not an identifier, an elementary item not DISPLAY
        (IBM: identifier-1 must be "DISPLAY when class-name is specified"), a group containing an
        OCCURS DEPENDING ON table (its length varies), a reference modification whose length is
        not a literal (nor the rest of the item from a literal start), and more than CLASS_CAP
        comparisons."""
        no = {"const": {"b": False}}
        # a contained program runs under its outermost program's sequence
        if self.collating is not None or self.outermost().collating is not None:
            self.unsup(f"class condition {name} in a program collating sequence given by literals")
            return no
        if e.kind != "ref":
            self.unsup("class condition on a non-identifier")
            return no
        ent = e.entry
        if ent.cat == "num" and ent.usage() != "display":
            self.unsup(f"class condition {name} on an item that is not USAGE DISPLAY")
            return no
        if self.odo_group(ent):
            self.unsup(f"class condition {name} on a group containing an OCCURS DEPENDING ON table")
            return no
        size = item_size(ent)
        start, n = e.rs, size
        if e.rs is not None:
            lit = e.rs.get("lit", {}).get("n")
            if e.rl is not None:
                n = e.rl.get("lit", {}).get("n")
            elif lit is not None:
                n = size - lit + 1
            else:
                n = None
            if n is None or n < 1:
                self.unsup(f"class condition {name} on a reference modification of variable length")
                return no

        def byte_at(i):
            """The subject's byte at position i (from 1): its reference modified by (i:1)."""
            if start is None:
                st = {"lit": {"n": i}}
            else:
                st = copy.deepcopy(start)
                body = next(iter(st.values()))
                body["n" if "lit" in st else "k"] = body.get("n" if "lit" in st else "k", 0) + i - 1
            return {"ref": {"r": dict(copy.deepcopy(self.ref_json(e)), refStart=st, refLen={"lit": {"n": 1}})}}

        def rel(op, a, b):
            return {"rel": {"op": op, "a": a, "b": {"lit": {"l": {"hex": {"h": f"{b:02X}"}}}}}}

        def tree(op, cs):
            if len(cs) == 1:
                return cs[0]
            k = len(cs) // 2
            return {op: {"a": tree(op, cs[:k]), "b": tree(op, cs[k:])}}
        runs = []
        for b in sorted(self.classes[name]):
            if runs and runs[-1][1] == b - 1:
                runs[-1][1] = b
            else:
                runs.append([b, b])
        per = sum(1 if lo == hi or lo == 0 or hi == 0xFF else 2 for lo, hi in runs)
        if per * n > CLASS_CAP:
            self.unsup(f"class condition {name} of {per * n} comparisons (more than {CLASS_CAP})")
            return no

        def at(i):
            alts = []
            for lo, hi in runs:
                if lo == hi:
                    alts.append(rel("=", byte_at(i), lo))
                elif lo == 0:
                    alts.append(rel("<=", byte_at(i), hi))
                elif hi == 0xFF:
                    alts.append(rel(">=", byte_at(i), lo))
                else:
                    alts.append({"and": {"a": rel(">=", byte_at(i), lo), "b": rel("<=", byte_at(i), hi)}})
            return tree("or", alts)
        return tree("and", [at(i) for i in range(1, n + 1)])

    # ------------------------------------------------------------------ phrases
    def size_phrases(self):
        ts = self.ts
        on, not_on = None, []
        while True:
            if ts.at_word("ON") and ts.peek(1).is_word("SIZE") or ts.at_word("SIZE"):
                ts.accept_word("ON")
                ts.expect_word("SIZE")
                ts.expect_word("ERROR")
                on = self.stmts()
            elif ts.at_word("NOT") and (ts.peek(1).is_word("SIZE") or
                                        ts.peek(1).is_word("ON") and ts.peek(2).is_word("SIZE")):
                ts.next()
                ts.accept_word("ON")
                ts.expect_word("SIZE")
                ts.expect_word("ERROR")
                not_on = self.stmts()
            else:
                return on, not_on

    def phrase(self, words, prefixes=("ON", "AT")):
        """Conditional phrase `[ON|AT] W1 [W2]` / `NOT [ON|AT] W1 [W2]`: returns
        (positive stmts or None, negative stmts or None)."""
        ts = self.ts
        pos = neg = None

        def at(k):
            # (`is_word()` with no arguments matches any word: only test real prefixes)
            if prefixes and ts.peek(k).is_word(*prefixes) and ts.peek(k + 1).is_word(words[0]):
                return k + 1
            if ts.peek(k).is_word(words[0]):
                return k
            return None

        while True:
            k = at(0)
            if k is not None:
                for _ in range(k):
                    ts.next()
                for w in words:
                    if w == words[0]:
                        ts.expect_word(w)
                    else:
                        ts.accept_word(w)
                pos = self.stmts()
                continue
            if ts.at_word("NOT"):
                k = at(1)
                if k is not None:
                    for _ in range(k):
                        ts.next()
                    for w in words:
                        if w == words[0]:
                            ts.expect_word(w)
                        else:
                            ts.accept_word(w)
                    neg = self.stmts()
                    continue
            return pos, neg

    def end(self, word):
        self.ts.accept_word(word)

    # ------------------------------------------------------------------ verbs
    def st_MOVE(self, t):
        ts = self.ts
        ts.next()
        if ts.accept_word("CORRESPONDING", "CORR"):
            return self.move_corr(t)
        self.ix_allow.append([])
        try:
            src = self.primary()
            ts.expect_word("TO")
            dsts = self.identifiers()
        finally:
            shared = self.ix_allow.pop()
        if shared:
            self.ix_group_move(src, dsts, shared)
        if not dsts:
            raise ParseError(ts.peek(), "MOVE without receiving items")
        if src.kind == "fn" and src.name == "CURRENT-DATE":
            # one clock reading (21 characters YYYYMMDDhhmmsshh+hhmm), optionally (start:len)
            start, length = 1, 21
            if src.refmod is not None:
                s, n = src.refmod
                if s.kind != "num" or s.scale != 0 or (n is not None and (n.kind != "num" or n.scale != 0)):
                    self.unsup("FUNCTION CURRENT-DATE with a variable reference modification")
                    return []
                start = s.v
                length = n.v if n is not None else 21 - start + 1
                if not (1 <= start <= 21 and 1 <= length <= 21 - start + 1):
                    raise ParseError(t, "reference modification outside FUNCTION CURRENT-DATE")
            if len(dsts) != 1:
                self.unsup("MOVE FUNCTION CURRENT-DATE to several items")
                return []
            if self.is_ae(dsts[0]):
                self.unsup("FUNCTION CURRENT-DATE moved to an alphanumeric-edited item")
                return []
            return [{"clock": {"dst": self.ref_of(dsts[0]), "start": start, "len": length}}]
        if any(self.is_ae(d) for d in dsts):
            return self.ae_move(t, src, dsts)
        return [{"move": {"src": self.to_operand(src), "dsts": [self.ref_of(d) for d in dsts]}}]

    def is_ae(self, x):
        """x is a whole alphanumeric-edited item (a reference-modified one is alphanumeric)."""
        return x.kind == "ref" and getattr(x.entry, "ae", None) is not None and x.rs is None

    def ae_move(self, t, src, dsts):
        """MOVE into alphanumeric-edited receivers (IBM Enterprise COBOL, GnuCOBOL): the sending
        data, aligned on the left, padded with spaces or truncated on the right, fills the data
        positions (A, X, 9) from the left, and B, 0 and / insert a space, a zero and a slash. A group
        item sends its bytes unedited (a group move). Each such receiver becomes: the MOVE into the
        first n positions of the hidden item %AE-TMP (n = data positions), the MOVE into it as an
        alphanumeric item (the checks of a direct MOVE; its result is overwritten), then each run
        of data positions taken from %AE-TMP and each run of insertion characters as a literal.
        The other receivers keep a MOVE of their own, in order. The sender is read again for each
        receiver; it reads the same as the one evaluation of a MOVE (Data.lean move) unless a
        receiver stored before overlaps it, which the MOVE checks reject, or changes one of its
        subscripts or reference-modification operands or the argument of a function sender (a
        function value has no area for the MOVE checks), which is excluded here."""
        if src.kind == "all" and src.lit.kind != "fig":
            # GnuCOBOL fills the whole item without editing; the standard edits the repeated string
            self.unsup("MOVE ALL literal to an alphanumeric-edited item")
            return []
        group = src.kind == "ref" and src.entry.is_group() and src.rs is None
        if not group and len(dsts) > 1 and (src.kind == "fn" or src.kind == "ref" and any(
                "item" in s for s in src.subs + [x for x in (src.rs, src.rl) if x is not None])):
            self.unsup("MOVE from a function or from an item with a data-name subscript or reference "
                       "modification to several receivers, one alphanumeric-edited")
            return []
        op = self.to_operand(src)
        out, run = [], []
        for d in dsts:
            if group or not self.is_ae(d):
                run.append(self.ref_of(d))
                continue
            if run:
                out.append({"move": {"src": copy.deepcopy(op), "dsts": run}})
                run = []
            out += self.ae_pieces(t, op, self.ref_of(d), d.entry.ae)
        if run:
            out.append({"move": {"src": copy.deepcopy(op), "dsts": run}})
        return out

    def ae_pieces(self, t, op, r, pat):
        """The statements of a MOVE of operand op into the alphanumeric-edited item r (pattern
        pat), as described at ae_move."""
        def tmp_ref(start, n):
            return {"item": self.dd.ae_tmp(t).id, "subs": [], "refStart": {"lit": {"n": start}},
                    "refLen": {"lit": {"n": n}}}
        out = [{"move": {"src": copy.deepcopy(op), "dsts": [tmp_ref(1, pat.count("d"))]}},
               {"move": {"src": copy.deepcopy(op), "dsts": [copy.deepcopy(r)]}}]
        if "ref" in op:
            # the MOVE checks let a sender occupy exactly the receiver's area (Data.lean
            # badOverlap), but an edited MOVE of an item onto itself is unpredictable (IBM: the
            # fields overlap); the MOVE into the receiver's first positions then faults
            out.append({"move": {"src": copy.deepcopy(op), "dsts": [
                dict(copy.deepcopy(r), refStart={"lit": {"n": 1}}, refLen={"lit": {"n": len(pat) - 1}})]}})
        i, q = 0, 1
        while i < len(pat):
            j = i
            while j < len(pat) and (pat[j] == "d") == (pat[i] == "d"):
                j += 1
            piece = dict(copy.deepcopy(r), refStart={"lit": {"n": i + 1}}, refLen={"lit": {"n": j - i}})
            if pat[i] == "d":
                out.append({"move": {"src": {"ref": {"r": tmp_ref(q, j - i)}}, "dsts": [piece]}})
                q += j - i
            else:
                out.append({"move": {"src": {"lit": {"l": {"str": {"s": "".join(pat[i:j])}}}},
                                     "dsts": [piece]}})
            i = j
        return out

    def ae_initialize(self, t, d):
        """INITIALIZE moves SPACE into an alphanumeric-edited item through the editing: after the
        resolver's MOVEs for identifier d (Resolve.lean initTargets: elementary items, not
        FILLER, neither with nor under a REDEFINES clause below d, every occurrence of the tables
        inside), the same items with a 0 or / insertion get the edited MOVE SPACE again. A
        reference-modified d is one elementary alphanumeric item (IBM), initialized unedited."""
        out = []
        if d.rs is not None:
            return out

        def walk(e, occs):
            if e.redefines is not None and e is not d.entry:
                return
            here = occs + ([e.occurs] if e.occurs is not None and e is not d.entry else [])
            if e.pic is not None:
                if e.name.upper() != "FILLER" and e.ae is not None and ("0" in e.ae or "/" in e.ae):
                    combos = [[]]
                    for n in here:
                        combos = [c + [{"lit": {"n": i + 1}}] for c in combos for i in range(n)]
                    for c in combos:
                        r = {"item": e.id, "subs": copy.deepcopy(d.subs) + c, "refStart": None, "refLen": None}
                        out.extend(self.ae_pieces(t, {"lit": {"l": {"fig": {"name": "SPACE"}}}}, r, e.ae))
                return
            for c in e.children:
                walk(c, here)
        walk(d.entry, [])
        return out

    # ------------------------------------------------------------------ CORRESPONDING
    def move_corr(self, t):
        """MOVE CORRESPONDING identifier-1 TO identifier-2: a MOVE for each corresponding pair
        (corr_pairs), in the order of identifier-1's items (IBM: "The results are the same as if
        each pair of CORRESPONDING identifiers were referenced in a separate MOVE statement.")."""
        x1, x2 = self.corr_identifiers("TO")
        out = []
        for a, b in self.corr_pairs(t, x1, x2, False):
            src = X("ref", t, entry=a, subs=copy.deepcopy(x1.subs), rs=None, rl=None)
            dst = X("ref", t, entry=b, subs=copy.deepcopy(x2.subs), rs=None, rl=None)
            if self.is_ae(dst):
                out += self.ae_move(t, src, [dst])
            else:
                out.append({"move": {"src": self.to_operand(src), "dsts": [self.ref_of(dst)]}})
        return out

    def arith_corr(self, t, verb):
        """ADD CORRESPONDING identifier-1 TO identifier-2 / SUBTRACT CORRESPONDING identifier-1
        FROM identifier-2 [ROUNDED] [SIZE ERROR phrases]: an ADD / SUBTRACT for each corresponding
        pair (corr_pairs), ROUNDED applying to each receiver. IBM: "If any of the individual
        operations in the ADD CORRESPONDING statement produces a size error condition,
        imperative-statement-1 in the ON SIZE ERROR phrase is not executed until all of the
        individual additions are completed." With SIZE ERROR phrases, the hidden item %CORR-COUNT
        counts the pairs without a size error (each pair's NOT ON SIZE ERROR phrase adds 1; with ON
        SIZE ERROR each pair has an empty ON SIZE ERROR phrase, so a receiver with a size error keeps
        its value), and the statement ends with IF %CORR-COUNT = the number of pairs THEN the NOT ON
        SIZE ERROR statements ELSE the ON SIZE ERROR statements."""
        ts = self.ts
        x1, x2 = self.corr_identifiers("TO" if verb == "add" else "FROM")
        rounded = None
        if ts.accept_word("ROUNDED"):
            rounded = "NEAREST-AWAY-FROM-ZERO"
            if ts.accept_word("MODE"):
                ts.accept_word("IS")
                m = ts.next()
                if m.val not in ROUNDING_MODES:
                    raise ParseError(m, f"unknown rounding mode {m.val}")
                rounded = m.val
        on, not_on = self.size_phrases()
        self.end("END-ADD" if verb == "add" else "END-SUBTRACT")
        pairs = self.corr_pairs(t, x1, x2, True)
        for a, b in pairs:
            # each pair is an ADD / SUBTRACT of its own
            self.composite30([self.entry_places(a), self.entry_places(b)], f" in the pair {a.name} / {b.name}")
        phrases = on is not None or bool(not_on)
        if not pairs:
            if phrases:
                self.unsup(f"{verb.upper()} CORRESPONDING with SIZE ERROR phrases and no corresponding items")
            return []
        cnt = None
        out = []
        if phrases:
            c = self.dd.hidden_num(t, "%CORR-COUNT", 9)
            cnt = {"item": c.id, "subs": [], "refStart": None, "refLen": None}
            out.append({"move": {"src": {"lit": {"l": {"num": {"v": 0, "scale": 0, "digits": 1}}}},
                                 "dsts": [copy.deepcopy(cnt)]}})
        for a, b in pairs:
            op = {"ref": {"r": {"item": a.id, "subs": copy.deepcopy(x1.subs), "refStart": None, "refLen": None}}}
            rcv = [{"ref": {"item": b.id, "subs": copy.deepcopy(x2.subs), "refStart": None, "refLen": None},
                    "rounded": rounded}]
            bump = [] if cnt is None else [
                {"add": {"ops": [{"lit": {"v": 1, "scale": 0}}], "rcv": [{"ref": copy.deepcopy(cnt), "rounded": None}],
                         "giving": False, "onSize": None, "notOnSize": []}}]
            trap = [] if on is not None else None
            if verb == "add":
                out.append({"add": {"ops": [op], "rcv": rcv, "giving": False, "onSize": trap, "notOnSize": bump}})
            else:
                out.append({"subtract": {"ops": [op], "rcv": rcv, "giving": None, "onSize": trap,
                                         "notOnSize": bump}})
        if cnt is not None:
            n = len(pairs)
            all_ok = {"rel": {"op": "=", "a": {"ref": {"r": copy.deepcopy(cnt)}},
                              "b": {"lit": {"l": {"num": {"v": n, "scale": 0, "digits": len(str(n))}}}}}}
            out.append({"ite": {"c": all_ok, "t": not_on, "e": on if on is not None else []}})
        return out

    def corr_identifiers(self, word):
        """identifier-1 TO / FROM identifier-2 of a CORRESPONDING phrase. IBM: "Both identifiers
        that follow the keyword CORRESPONDING must name group items"; neither is a level-66 item
        nor reference-modified. Index data items in them are checked per pair (corr_pairs)."""
        ts = self.ts
        self.ix_allow.append([])
        try:
            x1 = self.identifier()
            ts.expect_word(word)
            x2 = self.identifier()
        finally:
            self.ix_allow.pop()
        for x in (x1, x2):
            if x.kind != "ref" or not x.entry.is_group() or x.entry.rn is not None:
                raise ParseError(x.tok, f"{x.tok.val}: a CORRESPONDING operand must be a group item")
            if x.rs is not None:
                raise ParseError(x.tok, f"{x.tok.val}: a CORRESPONDING operand cannot be reference-modified")
        return x1, x2

    def corr_pairs(self, t, x1, x2, arith):
        """The corresponding pairs of identifier-1 and identifier-2 (IBM CORRESPONDING phrase), in
        the order of identifier-1's items: subordinate items with "the same name and the same
        qualifiers up to but not including identifier-1 and identifier-2", "not identified by the
        keyword FILLER", whose descriptions "do not include a REDEFINES, RENAMES, OCCURS, USAGE
        INDEX, USAGE POINTER" clause (the items below such an item are never reached; level-66
        items are not subordinate items here); "In a MOVE statement, at least one of the data items
        is an elementary item, and the move is permitted by the move rules"; "In an ADD or SUBTRACT
        statement, both of the data items are elementary numeric data items." The statement is
        unsupported for a pair whose elementary MOVE IBM's move table does not permit, a pair
        sharing storage with an index data item, operands that may share storage (IBM: overlapping
        operands give unpredictable results) unless they are the same item with the same
        subscripts, and a receiver that may share storage with a subscript of either operand."""
        def eligible(e):
            return e.name != "FILLER" and e.redefines is None and e.occurs is None and not e.index \
                and not e.pointer and e.usage_kw != "INDEX"
        pairs = []

        def walk(g1, g2):
            k1 = [c for c in g1.children if eligible(c)]
            k2 = [c for c in g2.children if eligible(c)]
            for c1 in k1:
                m = [c2 for c2 in k2 if c2.name == c1.name]
                if not m:
                    continue
                if len(m) > 1 or [c.name for c in k1].count(c1.name) > 1:
                    raise ParseError(t, f"CORRESPONDING: {c1.name} is not unique under {g1.name} and {g2.name}")
                c2 = m[0]
                if c1.is_group() and c2.is_group():
                    walk(c1, c2)
                elif not arith or (c1.numeric() and c2.numeric()):
                    pairs.append((c1, c2))
        walk(x1.entry, x2.entry)
        for a, b in pairs:
            why = None if arith else self.corr_move_bad(a, b)
            if why is not None:
                self.unsup(f"MOVE CORRESPONDING of {a.name}: IBM permits no elementary MOVE {why}")
            for e in (a, b):
                x = self.dd.overlap_ix(e)
                if x is not None:
                    self.unsup(f"CORRESPONDING item {e.name} shares storage with the index data item "
                               f"{x.name}, whose bytes are implementation-defined")
        if not (x1.entry is x2.entry and x1.subs == x2.subs) and self.corr_meet(x1, x2):
            self.unsup("CORRESPONDING operands that may share storage")
        ents = {}
        for s in x1.subs + x2.subs:
            if "item" in s:
                if not ents:
                    stack = list(self.dd.records)
                    while stack:
                        e = stack.pop()
                        ents[e.id] = e
                        stack += e.children
                sx = X("ref", t, entry=ents[s["item"]["id"]], subs=[])
                if any(self.corr_meet(X("ref", t, entry=b, subs=x2.subs), sx) for _, b in pairs):
                    self.unsup("a CORRESPONDING receiver that may share storage with a subscript")
        return pairs

    def corr_move_bad(self, a, b):
        """'from <category> to <category>' for an elementary MOVE from a to b that IBM's table of
        valid elementary moves does not permit, else None (a group move is always permitted)."""
        def cat(e):
            if e.is_group():
                return None
            if e.cat == "num":
                return "numeric" if e.pic["num"]["scale"] <= 0 else "non-integer numeric"
            if e.cat == "numEdited":
                return "numeric-edited"
            if e.ae is not None:
                return "alphanumeric-edited"
            return "alphabetic" if set(picmod.symbols(e.pic_text)) == {"A"} else "alphanumeric"
        ca, cb = cat(a), cat(b)
        if ca is None or cb is None:
            return None
        num = ("numeric", "non-integer numeric", "numeric-edited")
        bad = (ca in ("alphabetic", "alphanumeric-edited") and cb in num) or \
            (cb == "alphabetic" and ca in num) or \
            (ca == "non-integer numeric" and cb in ("alphanumeric", "alphanumeric-edited"))
        return f"from {ca} to {cb}" if bad else None

    def corr_meet(self, x, y):
        """Whether the operands x and y (items with subscripts) may share a byte: the same record
        storage and meeting byte ranges (the occurrence given by literal subscripts, else every
        occurrence)."""
        if rec_group(x.entry) is not rec_group(y.entry):
            return False

        def ranges(z):
            e = z.entry
            if z.subs and all("lit" in s for s in z.subs):
                dims = list(reversed(table_dims(e)))
                off = rec_offset(e) + sum((s["lit"]["n"] - 1) * st for s, (st, _) in zip(z.subs, dims))
                return [(off, off + item_size(e))]
            return occ_ranges(e)
        rx, ry = ranges(x), ranges(y)
        return rx is None or ry is None or ranges_meet(rx, ry)

    def st_COMPUTE(self, t):
        ts = self.ts
        ts.next()
        rcv = self.receivers()
        if not ts.accept_word("EQUAL"):
            o = ts.next()
            if not (o.kind == "OP" and o.val == "="):
                raise ParseError(o, "expected = in COMPUTE")
        e = self.arith()
        on, not_on = self.size_phrases()
        self.end("END-COMPUTE")
        self.compute_int_exps(e, rcv)
        return [{"compute": {"rcv": rcv, "e": self.to_expr(e), "onSize": on, "notOnSize": not_on}}]

    def arith_operands(self):
        """Operands of ADD / SUBTRACT (identifiers and numeric literals)."""
        out = []
        ts = self.ts
        while True:
            t = ts.peek()
            if t.kind == "NUM" or self.at_identifier() or t.is_word("ZERO", "ZEROS", "ZEROES"):
                out.append(self.primary())
            else:
                return out

    # IBM, Language Reference, "Arithmetic statement operands": "The composite of operands is a hypothetical data
    # item resulting from aligning the operands at the decimal point and then superimposing them on one another";
    # "If the ARITH(COMPAT) compiler option is in effect, the composite of operands can be a maximum of 30 digits" (the
    # model's ARITH option); it is made of, for ADD and SUBTRACT, "all operands in a given statement except those
    # following the word GIVING", for MULTIPLY "all receiving data items", for DIVIDE "all receiving data items except
    # the REMAINDER data item". A statement beyond it is unsupported (composite30).
    def entry_places(self, e):
        """(integer places, decimal places) of a numeric or numeric-edited data item: its PICTURE's digit positions
        (P positions included; a floating insertion string of n symbols holds n - 1), None for any other item."""
        if e is None or e.pic is None:
            return None
        if "num" in e.pic:
            n = e.pic["num"]
            return max(0, n["digits"] - n["scale"]), max(0, n["scale"])
        if "numEdited" in e.pic:
            syms = e.pic["numEdited"]["pic"]
            point = ("comma", "v") if self.dd.dpc else ("dot", "v")
            k = next((i for i, s in enumerate(syms) if s in point), len(syms))
            floating = set()
            for s in ("cs", "plus", "minus"):
                ix = [i for i, x in enumerate(syms) if x == s]
                if len(ix) > 1:
                    floating.update(ix[1:])

            def digits(lo, hi):
                return sum(1 for i in range(lo, hi) if syms[i] in ("nine", "z", "star", "p") or i in floating)
            return digits(0, k), digits(k + 1, len(syms))
        return None

    def operand_places(self, x):
        """(integer places, decimal places) of an operand as parsed: a numeric literal's digits as written, a data
        item's (entry_places), ZERO one integer place; None for anything else."""
        if x.kind == "paren":
            return self.operand_places(x.a)
        if x.kind == "num":
            return max(0, x.digits - x.scale), max(0, x.scale)
        if x.kind == "ref":
            return self.entry_places(x.entry)
        if x.kind == "fig" and x.name == "ZERO":
            return 1, 0
        return None

    def rcv_places(self, rcv):
        """The places of receivers (JSON, as receivers() gives them)."""
        return [self.entry_places(self.entry_by_id(r["ref"]["item"])) for r in rcv]

    def composite30(self, places, where=""):
        """Make the statement unsupported when the composite of operands (places: those of the operands that make
        it up) exceeds the 30 digits IBM allows."""
        ps = [p for p in places if p is not None]
        if not ps:
            return
        n = max(i for i, _ in ps) + max(d for _, d in ps)
        if n > 30:
            self.unsup(f"a composite of operands of {n} digits{where}, over the 30 digits IBM allows with ARITH(COMPAT) "
                       f"(Language Reference, 'Arithmetic statement operands')")

    def st_ADD(self, t):
        ts = self.ts
        ts.next()
        if ts.accept_word("CORRESPONDING", "CORR"):
            return self.arith_corr(t, "add")
        ops = self.arith_operands()
        giving = False
        if ts.accept_word("TO"):
            if ts.peek(len_ids := 0) and False:
                pass
            # `ADD a TO b GIVING c`: b is an operand
            save = ts.i
            more = self.arith_operands()
            if ts.at_word("GIVING"):
                ops += more
            else:
                ts.i = save
                rcv = self.receivers()
                on, not_on = self.size_phrases()
                self.end("END-ADD")
                self.composite30([self.operand_places(o) for o in ops] + self.rcv_places(rcv))
                return [{"add": {"ops": [self.to_expr(o) for o in ops], "rcv": rcv, "giving": False,
                                 "onSize": on, "notOnSize": not_on}}]
        ts.expect_word("GIVING")
        rcv = self.receivers()
        on, not_on = self.size_phrases()
        self.end("END-ADD")
        self.composite30([self.operand_places(o) for o in ops])
        return [{"add": {"ops": [self.to_expr(o) for o in ops], "rcv": rcv, "giving": True,
                         "onSize": on, "notOnSize": not_on}}]

    def st_SUBTRACT(self, t):
        ts = self.ts
        ts.next()
        if ts.accept_word("CORRESPONDING", "CORR"):
            return self.arith_corr(t, "subtract")
        ops = self.arith_operands()
        ts.expect_word("FROM")
        save = ts.i
        m = self.arith_operands()
        giving = None
        if ts.at_word("GIVING") and len(m) == 1:
            ts.next()
            giving = self.to_expr(m[0])
        else:
            ts.i = save
        rcv = self.receivers()
        on, not_on = self.size_phrases()
        self.end("END-SUBTRACT")
        self.composite30([self.operand_places(o) for o in ops] +
                         ([self.operand_places(m[0])] if giving is not None else self.rcv_places(rcv)))
        return [{"subtract": {"ops": [self.to_expr(o) for o in ops], "rcv": rcv, "giving": giving,
                              "onSize": on, "notOnSize": not_on}}]

    def st_MULTIPLY(self, t):
        ts = self.ts
        ts.next()
        a = self.primary()
        ts.expect_word("BY")
        save = ts.i
        b = self.primary()
        giving = None
        if ts.accept_word("GIVING"):
            giving = self.to_expr(b)
        else:
            ts.i = save
        rcv = self.receivers()
        on, not_on = self.size_phrases()
        self.end("END-MULTIPLY")
        self.composite30(self.rcv_places(rcv))
        return [{"multiply": {"a": self.to_expr(a), "rcv": rcv, "giving": giving,
                              "onSize": on, "notOnSize": not_on}}]

    def st_DIVIDE(self, t):
        ts = self.ts
        ts.next()
        a = self.primary()
        w = ts.expect_word("INTO", "BY")
        save = ts.i
        b = self.primary()
        rem = None
        if ts.accept_word("GIVING"):
            rcv = self.receivers()
            if ts.accept_word("REMAINDER"):
                rem = self.ref_of(self.identifier())
            dividend, divisor = (b, a) if w.val == "INTO" else (a, b)
            giving = True
        else:
            if w.val == "BY":
                raise ParseError(w, "DIVIDE ... BY needs GIVING")
            ts.i = save
            rcv = self.receivers()
            dividend, divisor = X("num", t, v=0, scale=0, digits=1), a
            giving = False
        on, not_on = self.size_phrases()
        self.end("END-DIVIDE")
        self.composite30(self.rcv_places(rcv))
        return [{"divide": {"dividend": self.to_expr(dividend), "divisor": self.to_expr(divisor),
                            "rcv": rcv, "giving": giving, "remainder": rem, "onSize": on,
                            "notOnSize": not_on}}]

    def st_IF(self, t):
        ts = self.ts
        ts.next()
        c = self.cond()
        ts.accept_word("THEN")
        then = self.stmts()
        els = []
        if ts.accept_word("ELSE"):
            els = self.stmts()
        self.end("END-IF")
        return [{"ite": {"c": c, "t": then, "e": els}}]

    def st_EVALUATE(self, t):
        ts = self.ts
        ts.next()
        subjects = [self.eval_subject()]
        while ts.accept_word("ALSO"):
            subjects.append(self.eval_subject())
        arms, other = [], []
        while ts.at_word("WHEN"):
            conds = []
            is_other = False
            while ts.accept_word("WHEN"):
                if ts.accept_word("OTHER"):
                    is_other = True
                    break
                objs = [self.eval_object(subjects[0])]
                k = 1
                while ts.accept_word("ALSO"):
                    if k >= len(subjects):
                        raise ParseError(ts.peek(), "more WHEN objects than EVALUATE subjects")
                    objs.append(self.eval_object(subjects[k]))
                    k += 1
                if k != len(subjects):
                    raise ParseError(ts.peek(), "fewer WHEN objects than EVALUATE subjects")
                c = objs[0]
                for o in objs[1:]:
                    c = {"and": {"a": c, "b": o}}
                conds.append(c)
            body = self.stmts()
            if is_other:
                other = body
                break
            c = conds[0]
            for o in conds[1:]:
                c = {"or": {"a": c, "b": o}}
            arms.append([c, body])
        self.end("END-EVALUATE")
        return [{"evaluate": {"arms": arms, "other": other}}]

    def eval_subject(self):
        ts = self.ts
        t = ts.peek()
        if t.is_word("TRUE", "FALSE"):
            ts.next()
            return ("bool", t.val == "TRUE")
        save = ts.i
        nfr = len(self.frames[-1])
        e = self.arith()
        if e.kind == "cond" or self.relop_at(0) or self.class_or_sign_at() or ts.at_word("AND", "OR"):
            ts.i = save
            del self.frames[-1][nfr:]
            return ("cond", self.cond())
        return ("expr", e)

    def eval_object(self, subj):
        ts = self.ts
        if ts.accept_word("ANY"):
            return {"const": {"b": True}}
        kind = subj[0]
        if ts.at_word("TRUE", "FALSE") and kind in ("cond", "bool"):
            b = ts.next().val == "TRUE"
            if kind == "bool":
                return {"const": {"b": b == subj[1]}}
            return subj[1] if b else {"not": {"c": subj[1]}}
        if kind == "bool":
            c = self.cond()
            return c if subj[1] else {"not": {"c": c}}
        if kind == "cond":
            raise ParseError(ts.peek(), "WHEN object for a condition subject must be TRUE, FALSE or ANY")
        e = subj[1]
        neg = ts.accept_word("NOT") is not None
        lo = self.arith()
        if ts.accept_word("THRU", "THROUGH"):
            hi = self.arith()
            c = {"and": {"a": eval_own(self.rel_json((False, ">="), e, lo)),
                         "b": eval_own(self.rel_json((False, "<="), e, hi))}}
        else:
            c = eval_own(self.rel_json((False, "="), e, lo))
        return {"not": {"c": c}} if neg else c

    def perform_loop(self):
        ts = self.ts
        test_after = False
        if ts.at_word("WITH") and ts.peek(1).is_word("TEST") or ts.at_word("TEST"):
            ts.accept_word("WITH")
            ts.expect_word("TEST")
            test_after = ts.expect_word("BEFORE", "AFTER").val == "AFTER"
            if not ts.at_word("UNTIL", "VARYING"):
                raise ParseError(ts.peek(), "WITH TEST needs UNTIL or VARYING")
        if ts.accept_word("UNTIL"):
            return {"until": {"testAfter": test_after, "c": self.cond()}}
        if ts.accept_word("VARYING"):
            var = self.identifier()
            ts.expect_word("FROM")
            f = self.arith()
            ts.expect_word("BY")
            b = self.arith()
            ts.expect_word("UNTIL")
            c = self.cond()
            levels = [(var, f, b, c)]
            while ts.accept_word("AFTER"):
                v2 = self.identifier()
                ts.expect_word("FROM")
                f2 = self.arith()
                ts.expect_word("BY")
                b2 = self.arith()
                ts.expect_word("UNTIL")
                levels.append((v2, f2, b2, self.cond()))
            lv = [self.varying_level(v, fe, be, cc) for v, fe, be, cc in levels]
            if any(x is None for x in lv):
                return "once"
            if len(levels) > 1:
                # the resolver gives the statements built in after_stmts the scale of a VARYING
                # (dmax 0) only when FROM and BY have no division
                if any(_has_key(x["fromE"], "div") or _has_key(x["byE"], "div") for x in lv):
                    self.unsup("PERFORM VARYING ... AFTER with a division in FROM or BY")
                    return "once"
                return {"after": {"testAfter": test_after, "levels": lv}}
            if "idx" in lv[0]:
                return {"varyingIdx": dict(testAfter=test_after, **lv[0])}
            return {"varying": dict(testAfter=test_after, **lv[0])}
        # `n TIMES`
        t = ts.peek()
        if t.kind == "NUM" or self.at_identifier():
            save = ts.i
            nfr = len(self.frames[-1])
            n = self.primary()
            if ts.accept_word("TIMES"):
                return {"times": {"n": self.to_expr(n)}}
            ts.i = save
            del self.frames[-1][nfr:]
        return "once"

    def varying_level(self, v, fe, be, cc):
        """One `VARYING / AFTER v FROM fe BY be UNTIL cc` phrase: {"var" | "idx", "fromE", "byE",
        "c"}, or None (unsupported). IBM, VARYING an index name: it "is initialized and incremented
        or decremented according to the rules under INDEX phrase" (SET); in the FROM phrase "an
        identifier must be described as an integer and have a positive value; a literal must be a
        positive integer" (or an index name, set as by SET), in the BY phrase "an identifier must be
        described as an integer; a literal must be a nonzero integer"."""
        def integer(x):
            x = x.a if x.kind == "paren" else x
            return (x.kind == "num" and x.scale == 0) or \
                (x.kind == "ref" and x.rs is None and x.entry.numeric() and x.entry.pic["num"]["scale"] <= 0)
        if v.kind == "ixd":
            # IBM: identifier-2 "Must name a numeric elementary item"
            self.unsup("PERFORM VARYING an index data item")
            return None
        if v.kind != "idx":
            return {"var": self.ref_of(v, "VARYING variable"), "fromE": self.to_expr(fe),
                    "byE": self.to_expr(be), "c": cc}
        b = be.a if be.kind == "paren" else be
        if not (fe.kind == "idx" or integer(fe)):
            self.unsup("PERFORM VARYING an index name FROM an operand other than an integer or an index name")
            return None
        if not integer(be) or (b.kind == "num" and b.v == 0):
            self.unsup("PERFORM VARYING an index name BY an operand other than an integer item or a nonzero integer")
            return None
        return {"idx": v.id, "fromE": self.to_expr(fe), "byE": self.to_expr(be), "c": cc}

    def st_PERFORM(self, t):
        ts = self.ts
        ts.next()
        if self.is_proc_name(ts.peek()) and not (ts.peek(1).is_word("TIMES")):
            first = self.proc_ref()
            last = None
            if ts.accept_word("THRU", "THROUGH"):
                last = self.proc_ref()
            loop = self.perform_loop()
            if isinstance(loop, dict) and "after" in loop:
                return self.after_stmts(loop["after"],
                                        [{"perform": {"first": first, "last": last, "loop": "once"}}])
            return [{"perform": {"first": first, "last": last, "loop": loop}}]
        loop = self.perform_loop()
        body = self.stmts()
        ts.expect_word("END-PERFORM")
        if isinstance(loop, dict) and "after" in loop:
            if _has_exit_perform(body):
                self.unsup("EXIT PERFORM inside PERFORM VARYING ... AFTER")
                return []
            return self.after_stmts(loop["after"], body)
        return [{"performInline": {"body": body, "loop": loop}}]

    def after_stmts(self, after, body):
        """`PERFORM ... VARYING v1 FROM f1 BY b1 UNTIL c1 AFTER v2 ... AFTER vn ...` as nested
        loops, following IBM Enterprise COBOL ("Varying two identifiers") and GnuCOBOL:
        * TEST BEFORE: v1 .. vn are set to their initial values, then c1 is tested; when level
          k + 1 ends (c(k+1) true), vk is augmented and v(k+1) .. vn are set to their initial
          values again, before ck is tested.  So: init v1 .. vn; UNTIL c1 [UNTIL c2 [... UNTIL cn
          [body; step vn] ...; step v1; init v2 .. vn].
        * TEST AFTER: the levels nest as single-level VARYING loops with TEST AFTER (an inner
          loop's initialization follows the outer augmentation).
        The initialization and augmentation are the COMPUTE v = f and ADD b TO v statements the
        resolver makes for a single VARYING, or, for an index name, SET v TO f and SET v UP BY b."""
        lv = after["levels"]

        def init(x):
            if "idx" in x:
                return {"setIdx": {"id": x["idx"], "e": copy.deepcopy(x["fromE"])}}
            return {"compute": {"rcv": [{"ref": copy.deepcopy(x["var"]), "rounded": None}],
                                "e": copy.deepcopy(x["fromE"]), "onSize": None, "notOnSize": []}}

        def step(x):
            if "idx" in x:
                return {"setIdxBy": {"id": x["idx"], "e": copy.deepcopy(x["byE"]), "down": False}}
            return {"add": {"ops": [copy.deepcopy(x["byE"])],
                            "rcv": [{"ref": copy.deepcopy(x["var"]), "rounded": None}],
                            "giving": False, "onSize": None, "notOnSize": []}}

        if after["testAfter"]:
            inner = body
            for x in reversed(lv):
                if "idx" in x:
                    loop = {"varyingIdx": {
                        "testAfter": True, "idx": x["idx"], "fromE": copy.deepcopy(x["fromE"]),
                        "byE": copy.deepcopy(x["byE"]), "c": copy.deepcopy(x["c"])}}
                else:
                    loop = {"varying": {
                        "testAfter": True, "var": copy.deepcopy(x["var"]), "fromE": copy.deepcopy(x["fromE"]),
                        "byE": copy.deepcopy(x["byE"]), "c": copy.deepcopy(x["c"])}}
                inner = [{"performInline": {"body": inner, "loop": loop}}]
            return inner
        n = len(lv)
        loop = [{"performInline": {"body": body + [step(lv[n - 1])],
                                   "loop": {"until": {"testAfter": False, "c": copy.deepcopy(lv[n - 1]["c"])}}}}]
        for k in range(n - 2, -1, -1):
            loop = [{"performInline": {"body": loop + [step(lv[k])] + [init(x) for x in lv[k + 1:]],
                                       "loop": {"until": {"testAfter": False, "c": copy.deepcopy(lv[k]["c"])}}}}]
        return [init(x) for x in lv] + loop

    def st_GO(self, t):
        ts = self.ts
        ts.next()
        ts.accept_word("TO")
        targets = []
        while self.is_proc_name(ts.peek()):
            targets.append(self.proc_ref())
        if not targets:
            self.unsup("GO TO without a target (ALTER)")
            return []
        if ts.accept_word("DEPENDING"):
            ts.accept_word("ON")
            e = self.arith()
            return [{"goToDep": {"targets": targets, "e": self.to_expr(e)}}]
        if len(targets) != 1:
            raise ParseError(t, "GO TO with several targets needs DEPENDING ON")
        p = getattr(self, "cur_para", None)
        if p in getattr(self, "alter", {}):
            # the paragraph's GO TO, as ALTER leaves it: its initial target is one more choice
            lst = self.alter[p]
            if targets[0] not in lst:
                lst.append(targets[0])
            e = self.alter_item[p]
            e.value = ("num", lst.index(targets[0]) + 1, 0)
            return [{"goToDep": {"targets": list(lst), "e": {"ref": {"r": {
                "item": e.id, "subs": [], "refStart": None, "refLen": None}}}}}]
        return [{"goTo": {"target": targets[0]}}]

    def st_ALTER(self, t):
        """`ALTER p TO [PROCEED TO] q ...`: set p's hidden item to q's position."""
        ts = self.ts
        ts.next()
        out = []
        while is_user_word(ts.peek()) and ts.peek(1).is_word("TO"):
            p = ts.next().val
            ts.next()
            if ts.accept_word("PROCEED"):
                ts.expect_word("TO")
            q = ts.next().val
            lst = self.alter.get(p)
            if lst is None or q not in lst:
                raise ParseError(t, f"ALTER {p}: not prescanned")
            out.append({"move": {"src": {"lit": {"l": {"num": {"v": lst.index(q) + 1, "scale": 0,
                                                              "digits": 4}}}},
                                 "dsts": [{"item": self.alter_item[p].id, "subs": [],
                                           "refStart": None, "refLen": None}]}})
        return out

    def st_EXIT(self, t):
        ts = self.ts
        ts.next()
        if ts.accept_word("PROGRAM"):
            return ["exitProgram"]
        if ts.accept_word("PERFORM"):
            if ts.accept_word("CYCLE"):
                return ["exitCycle"]
            return ["exitPerform"]
        if ts.accept_word("PARAGRAPH"):
            return ["exitPara"]
        if ts.accept_word("SECTION"):
            return ["exitSection"]
        if ts.at_word("METHOD", "FUNCTION"):
            self.unsup(f"EXIT {ts.next().val}")
            return []
        return ["cont"]

    def st_CONTINUE(self, t):
        self.ts.next()
        return ["cont"]

    def st_GOBACK(self, t):
        self.ts.next()
        if self.ts.accept_word("RETURNING"):
            self.primary()
            self.unsup("GOBACK RETURNING")
        return ["goback"]

    def st_STOP(self, t):
        ts = self.ts
        ts.next()
        if ts.accept_word("RUN"):
            return ["stopRun"]
        self.primary()
        self.unsup("STOP literal")
        return []

    def st_SET(self, t):
        ts = self.ts
        ts.next()
        if ts.peek().kind == "WORD" and ts.peek().val in self.switch_mnem:
            # `SET {mnemonic-name}... TO {ON | OFF} ...`: the switches' hidden items (make_switches)
            out = []
            while ts.peek().kind == "WORD" and ts.peek().val in self.switch_mnem:
                names = []
                while ts.peek().kind == "WORD" and ts.peek().val in self.switch_mnem:
                    names.append(ts.next().val)
                ts.expect_word("TO")
                v = "1" if ts.expect_word("ON", "OFF").val == "ON" else "0"
                out += [{"move": {"src": {"lit": {"l": {"str": {"s": v}}}},
                                  "dsts": [{"item": self.switch_mnem[n].id, "subs": [], "refStart": None,
                                            "refLen": None}]}} for n in names]
            return out
        if ts.at_word("ADDRESS"):
            # `SET ADDRESS OF item TO pointer`: the item is the storage at that address (a
            # LINKAGE item); modelled as a copy of the addressed bytes of the environment's
            # address space into the item (the programs only read such storage)
            ts.next()
            ts.expect_word("OF")
            x = self.identifier()
            ts.expect_word("TO")
            if ts.at_word("ADDRESS", "NULL", "NULLS"):
                self.unsup("SET ADDRESS OF ... TO ADDRESS OF / NULL")
                self.skip_statement()
                return []
            p = self.identifier()
            if p.kind != "ref" or not getattr(p.entry, "pointer", False):
                self.unsup("SET ADDRESS OF ... TO a non-pointer")
                return []
            return [{"setAddress": {"dst": self.ref_of(x), "ptr": self.ref_of(p)}}]
        targets = self.identifiers()
        if not targets:
            raise ParseError(ts.peek(), "SET without targets")
        if ts.accept_word("UP", "DOWN"):
            down = ts.peek(-1).val == "DOWN"
            ts.expect_word("BY")
            e = self.arith()
            out = []
            for x in targets:
                if x.kind == "ixd":
                    # IBM: "The receiving field is an index specified by index-name-3."
                    self.unsup("SET UP/DOWN of an index data item")
                    continue
                if x.kind != "idx":
                    self.unsup("SET UP/DOWN of a non-index item")
                    continue
                out.append({"setIdxBy": {"id": x.id, "e": self.to_expr(e), "down": down}})
            return out
        ts.expect_word("TO")
        if ts.at_word("TRUE", "FALSE"):
            val = ts.next().val == "TRUE"
            out = []
            for x in targets:
                if x.kind != "cond":
                    raise ParseError(x.tok, f"SET {x.tok.val} TO {'TRUE' if val else 'FALSE'}: not a condition name")
                if getattr(x.entry, "switch", False):
                    self.unsup("SET TO TRUE / FALSE of a switch-status condition name")
                    continue
                if val:
                    out.append({"setTrue": {"id": x.id, "subs": x.subs}})
                else:
                    c = x.entry
                    if c.false_value is None:
                        raise ParseError(x.tok, f"SET {c.name} TO FALSE without a FALSE value")
                    lit = self.lit_x(c.false_value, x.tok)
                    out.append({"move": {"src": self.to_operand(lit),
                                         "dsts": [{"item": c.parent.id, "subs": x.subs,
                                                   "refStart": None, "refLen": None}]}})
            return out
        if ts.at_word("ADDRESS", "NULL", "NULLS", "ENTRY"):
            self.unsup("SET pointer")
            self.skip_statement()
            return []
        src = self.arith()
        out = []
        for x in targets:
            if x.kind == "ref" and getattr(x.entry, "pointer", False):
                # pointer to pointer: the 4-byte address
                if src.kind != "ref" or not getattr(src.entry, "pointer", False):
                    self.unsup("SET pointer TO a non-pointer")
                    continue
                out.append({"move": {"src": self.to_operand(src), "dsts": [self.ref_json(x)]}})
            elif x.kind == "idx" and src.kind == "ixd":
                # no conversion: the index name takes the occurrence number the item holds
                out.append({"setIdx": {"id": x.id, "e": {"ref": {"r": self.ix_ref(src)}}}})
                self.ix_link(src.entry, x.id)
            elif x.kind == "idx":
                out.append({"setIdx": {"id": x.id, "e": self.to_expr(src)}})
            elif x.kind == "ixd" and src.kind in ("idx", "ixd"):
                # no conversion: the item takes the index name's or the other item's occurrence
                # number (7 digits; a larger one is beyond the representation)
                e = {"idx": {"id": src.id}} if src.kind == "idx" else {"ref": {"r": self.ix_ref(src)}}
                out.append({"compute": {"rcv": [{"ref": self.ix_ref(x), "rounded": None}], "e": e,
                                        "onSize": [{"unsupported": {"what": IX_RANGE}}], "notOnSize": []}})
                if src.kind == "idx":
                    self.ix_link(x.entry, src.id)
                else:
                    self.ix_union(x.entry, src.entry)
            elif x.kind == "ixd":
                self.unsup("SET of an index data item to a value other than an index name or index data item")
            elif x.kind == "ref" and src.kind == "ixd":
                self.unsup("SET of an integer item to an index data item")
            elif x.kind == "ref" and src.kind == "idx":
                out.append({"compute": {"rcv": [{"ref": self.ref_json(x), "rounded": None}],
                                        "e": self.to_expr(src), "onSize": None, "notOnSize": []}})
            else:
                self.unsup("SET of a data item")
        return out

    def lit_x(self, lit, tok):
        kind = lit[0]
        if kind == "num":
            return X("num", tok, v=lit[1], scale=lit[2], digits=lit[3])
        if kind == "str":
            return X("str", tok, s=lit[1])
        if kind == "hex":
            return X("hex", tok, b=lit[1])
        if kind == "fig":
            return X("fig", tok, name=lit[1])
        return X("all", tok, lit=self.lit_x(lit[1], tok))

    def st_DISPLAY(self, t):
        ts = self.ts
        ts.next()
        ops = []
        while True:
            p = ts.peek()
            if p.kind in ("NUM", "STR", "HEX", "NSTR", "ZSTR") or self.at_identifier() or \
                    (p.kind == "WORD" and (p.val in FIGURATIVE or p.val in ("ALL", "FUNCTION"))):
                ops.append(self.primary())
            else:
                break
        if any(o.kind == "num" and str(o.tok.val)[:1] in "+-" for o in ops):
            # IBM gives no form for the sign of a numeric literal shown by DISPLAY
            self.unsup("DISPLAY of a signed numeric literal")
        if self.dd.dpc and any(o.kind == "num" and o.scale > 0 for o in ops):
            # unchecked under the clause: the model writes the digits only (IBM: a literal's
            # decimal point is an assumed one; Exec.lean displayBytes), as GnuCOBOL 3.2 does
            self.unsup("DISPLAY of a numeric literal with decimal places under DECIMAL-POINT IS COMMA")
        if ts.accept_word("UPON"):
            u = ts.next()
            if u.val not in ("SYSOUT",):
                self.unsup(f"DISPLAY UPON {u.val}")
        if ts.at_word("WITH") or ts.at_word("NO"):
            ts.accept_word("WITH")
            ts.expect_word("NO")
            ts.expect_word("ADVANCING")
            self.unsup("DISPLAY WITH NO ADVANCING")
        self.end("END-DISPLAY")
        return [{"display": {"ops": [self.to_operand(o) for o in ops]}}]

    def st_INITIALIZE(self, t):
        ts = self.ts
        ts.next()
        # IBM: identifiers that are not valid MOVE receivers, such as index data items, are not
        # initialized; the resolver skips them (the hidden FILLER child), so a group containing
        # index data items may be initialized
        self.ix_allow.append([])
        try:
            dsts = self.identifiers()
        finally:
            shared = self.ix_allow.pop()
        for ent in shared:
            # only index data items inside the identifier are skipped (one overlaid through a
            # REDEFINES would be written)
            outside = [x for x in self.dd.overlap_ix_all(ent) if ent not in x.ancestors()]
            if outside or not any(d.kind == "ref" and d.entry is ent and d.rs is None for d in dsts):
                self.unsup(f"{ent.name} shares storage with the index data item "
                           f"{self.dd.overlap_ix(ent).name}, whose bytes are implementation-defined")
        if any(d.kind == "ref" and self.odo_group(d.entry) for d in dsts):
            # IBM: "you cannot use the INITIALIZE statement to initialize a variably-located item or
            # a variable-length item"
            self.unsup("INITIALIZE of a group containing an OCCURS DEPENDING ON table")
        if any(d.kind == "ref" and d.entry.rn is not None for d in dsts):
            self.unsup("INITIALIZE of a level-66 (RENAMES) item")
        if ts.at_word("REPLACING") or ts.at_word("THEN") and ts.peek(1).is_word("REPLACING"):
            ts.accept_word("THEN")
            ts.next()
            repl = {}
            while ts.at_word(*INIT_CATEGORIES):
                c = ts.next()
                cat = "DBCS" if c.val == "EGCS" else c.val
                if cat in repl:
                    raise ParseError(c, f"INITIALIZE ... REPLACING {c.val} twice")
                ts.accept_word("DATA")
                ts.expect_word("BY")
                repl[cat] = self.primary()
            if not repl:
                raise ParseError(ts.peek(), "REPLACING without a category")
            if ts.at_word("THEN", "TO", "DEFAULT"):
                self.unsup("INITIALIZE ... THEN TO DEFAULT")
                self.skip_init_phrases()
                return []
            return self.init_replacing(t, dsts, repl)
        if ts.at_word("WITH", "FILLER"):
            self.unsup("INITIALIZE WITH FILLER")
        elif ts.at_word("ALL", *INIT_CATEGORIES):
            self.unsup("INITIALIZE ... TO VALUE")
        elif ts.at_word("THEN", "TO", "DEFAULT"):
            self.unsup("INITIALIZE ... THEN TO DEFAULT")
        self.skip_init_phrases()
        if any(d.kind == "ref" and d.entry.pointer for d in dsts):
            self.unsup("INITIALIZE of a pointer")
            return []
        lowered = [d.kind == "ref" and d.rs is None and
                   any(e.pointer for e, _ in self.init_receivers(d.entry, pointers=True)) for d in dsts]
        if any(lowered):
            # IBM rule 1a: a pointer is no receiver, but the resolver cannot tell it from a 9-digit
            # COMP-5 item and would MOVE ZERO into it. An identifier with a pointer among its rule-1
            # candidates becomes its MOVEs here: those of REPLACING every category BY SPACE or ZERO
            # (rules 1c and 2), with no INITIALIZE for the resolver and no ae_initialize pieces.
            plain = {c: X("fig", t, name="ZERO" if c.startswith("NUMERIC") else "SPACE")
                     for c in ("ALPHABETIC", "ALPHANUMERIC", "ALPHANUMERIC-EDITED", "NUMERIC",
                               "NUMERIC-EDITED")}
            out = []
            for d, low in zip(dsts, lowered):
                if low:
                    out += self.init_moves(t, d, plain)
                    continue
                p = self.ae_initialize(t, d) if d.kind == "ref" else []
                if p and d.rs is not None:
                    self.unsup("INITIALIZE of a reference-modified item with an alphanumeric-edited item")
                    return []
                out += [{"initialize": {"dsts": [self.ref_of(d)]}}] + p
            return out
        refs = [self.ref_of(d) for d in dsts]
        pieces = [self.ae_initialize(t, d) if d.kind == "ref" else [] for d in dsts]
        if not any(pieces):
            return [{"initialize": {"dsts": refs}}]
        if any(p and d.rs is not None for d, p in zip(dsts, pieces)):
            # the resolver initializes the whole item of a reference-modified identifier
            self.unsup("INITIALIZE of a reference-modified item with an alphanumeric-edited item")
            return []
        # identifiers are initialized in turn (the resolver's MOVEs of INITIALIZE A B are those of
        # INITIALIZE A, then INITIALIZE B), each followed by its edited MOVEs
        out = []
        for r, p in zip(refs, pieces):
            out += [{"initialize": {"dsts": [r]}}] + p
        return out

    def skip_init_phrases(self):
        """The rest of an INITIALIZE statement whose phrases are unsupported."""
        ts = self.ts
        while ts.peek().kind == "WORD" and ts.peek().val not in VERBS and \
                not ts.peek().val.startswith("END-") and ts.peek().val not in ("ELSE", "WHEN") \
                or ts.peek().kind in ("NUM", "STR", "HEX"):
            if ts.at_word("NOT", "AT", "ON", "INVALID"):
                break
            ts.next()

    def init_receivers(self, root, pointers=False):
        """IBM's INITIALIZE rule 1 for identifier `root`: its elementary items (root itself when it
        is elementary) except FILLER items (no WITH FILLER phrase), items that are not MOVE
        receivers (pointers, index data items) and items inside root that have a REDEFINES clause
        or lie under one (root's own REDEFINES does not count), each with the OCCURS counts of the
        tables inside root that contain it (every occurrence is a receiver). Storage order. With
        `pointers`, the pointers among these candidates are kept."""
        out = []

        def walk(e, occs):
            if e is not root and e.redefines is not None or e.usage() == "index":
                return
            here = occs + ([e.occurs] if e.occurs is not None and e is not root else [])
            if e.pic is not None:
                if e.name.upper() != "FILLER" and (pointers or not e.pointer):
                    out.append((e, here))
                return
            for c in e.children:
                walk(c, here)
        walk(root, [])
        return out

    @staticmethod
    def init_category(e):
        """The category of an elementary item, as INITIALIZE ... REPLACING names it (IBM: an
        alphabetic PICTURE has only A; an alphanumeric-edited one is stored as alphanumeric)."""
        if e.cat == "num":
            return "NUMERIC"
        if e.cat == "numEdited":
            return "NUMERIC-EDITED"
        if e.ae is not None:
            return "ALPHANUMERIC-EDITED"
        return "ALPHABETIC" if set(picmod.symbols(e.pic_text)) == {"A"} else "ALPHANUMERIC"

    def init_replacing(self, t, dsts, repl):
        """`INITIALIZE identifier... REPLACING category [DATA] BY operand ...` as MOVEs (IBM: "as if
        a series of implicit MOVE statements"): for each identifier in turn, each receiver of rule 1
        (init_receivers) of a category named in the phrase gets a MOVE of that category's operand
        (through the editing for an alphanumeric-edited item, see ae_move); the others are not
        changed. The operand is read again for each MOVE, so an operand item that shares storage
        with an identifier, or that has a data-name subscript or reference modification, is
        unsupported, as is an identifier with a data-name subscript or reference modification."""
        def root(e):
            r = e.root()
            while r.redefines is not None:
                r = r.redefines
            return r
        for x in repl.values():
            if x.kind == "ref":
                if x.entry.is_group():
                    raise ParseError(x.tok, "INITIALIZE ... REPLACING BY a group item")
                if any("lit" not in s for s in x.subs) or x.rs is not None:
                    self.unsup("INITIALIZE ... REPLACING BY an item with a data-name subscript or "
                               "reference modification")
                    return []
                if any(d.kind == "ref" and root(d.entry) is root(x.entry) for d in dsts):
                    self.unsup("INITIALIZE ... REPLACING BY an item in the storage of an identifier")
                    return []
            elif x.kind not in ("num", "str", "hex", "fig", "all"):
                self.unsup("INITIALIZE ... REPLACING BY an operand other than an item or a literal")
                return []
        out = []
        for d in dsts:
            if d.kind == "ixd":
                self.unsup("INITIALIZE ... REPLACING of an index data item")
                return []
            if d.kind != "ref":
                self.unsup("INITIALIZE ... REPLACING of a condition name or an index name")
                return []
            if d.rs is not None or any("lit" not in s for s in d.subs):
                self.unsup("INITIALIZE ... REPLACING of an item with a data-name subscript or reference "
                           "modification")
                return []
            if d.entry.pointer or d.entry.usage() == "index":
                self.unsup("INITIALIZE ... REPLACING of a pointer or index data item")
                return []
            out += self.init_moves(t, d, repl)
        return out

    def init_moves(self, t, d, ops):
        """The MOVEs of INITIALIZE for identifier d (a data item, not reference-modified): each
        receiver of rule 1 (init_receivers) whose category has an operand in ops gets a MOVE of that
        operand, through the editing for an alphanumeric-edited item (ae_pieces), every occurrence
        of the tables inside d, in storage order; the others are not changed."""
        out = []
        r0 = self.ref_json(d)
        for e, occs in self.init_receivers(d.entry):
            x = ops.get(self.init_category(e))
            if x is None:
                continue
            if e.ae is not None and x.kind == "all" and x.lit.kind != "fig":
                self.unsup("INITIALIZE ... REPLACING BY ALL literal for an alphanumeric-edited item")
                return []
            combos = [[]]
            for n in occs:
                combos = [c + [{"lit": {"n": i + 1}}] for c in combos for i in range(n)]
            for c in combos:
                r = dict(copy.deepcopy(r0), item=e.id, subs=copy.deepcopy(d.subs) + c)
                if e.ae is not None:
                    out += self.ae_pieces(t, self.to_operand(x), r, e.ae)
                else:
                    out.append({"move": {"src": self.to_operand(x), "dsts": [r]}})
        return out

    def st_CALL(self, t):
        ts = self.ts
        ts.next()
        prog = target = None
        if ts.peek().kind == "STR":
            prog = ts.next().val
        elif self.at_identifier():
            # CALL identifier: the program named by the item's value (unit.py dispatches on it)
            target = self.identifier()
            if target.kind != "ref" or not (target.entry.is_group() or target.entry.cat == "alnum") or \
                    target.entry.ae is not None:
                self.unsup("CALL of a program named by an item that is not alphanumeric")
        else:
            ts.next()
            self.unsup("CALL of a program named by a data item")
        args = []
        pre = []      # BY CONTENT: the arguments' bytes are moved to hidden items, passed instead
        mode = "REFERENCE"
        if ts.accept_word("USING"):
            while True:
                if ts.accept_word("BY"):
                    mode = ts.expect_word("REFERENCE", "CONTENT", "VALUE").val
                elif ts.at_word("REFERENCE", "CONTENT", "VALUE"):
                    mode = ts.next().val
                if ts.accept_word("OMITTED"):
                    self.unsup("CALL ... OMITTED")
                    continue
                p = ts.peek()
                if not (self.at_identifier() or p.kind in ("NUM", "STR", "HEX") or
                        p.is_word("ADDRESS", "LENGTH")):
                    break
                x = self.primary()
                if mode == "CONTENT":
                    tmp = self.by_content(x)
                    if tmp is not None:
                        pre.append(tmp[0])
                        args.append(tmp[1])
                elif mode != "REFERENCE":
                    self.unsup(f"CALL ... BY {mode}")
                elif x.kind == "ixd":
                    self.unsup("CALL USING an index data item (the called program reads its bytes)")
                elif x.kind != "ref":
                    self.unsup("CALL BY REFERENCE of a literal")
                else:
                    args.append(self.ref_json(x))
        if ts.accept_word("RETURNING"):
            self.identifier()
            self.unsup("CALL ... RETURNING")
        exc, nexc = self.phrase(["EXCEPTION"], prefixes=("ON",))
        ovf, novf = self.phrase(["OVERFLOW"], prefixes=("ON",))
        if exc is not None and ovf is not None:
            self.unsup("CALL ... with both ON EXCEPTION and ON OVERFLOW")
        if novf is not None:
            self.unsup("CALL ... NOT ON OVERFLOW")
        self.end("END-CALL")
        if prog == "CEE3ABD":
            # Language Environment abend service: CEE3ABD(abend code, timing)
            # without arguments the code is unspecified: -1
            code = {"ref": {"r": args[0]}} if args else {"lit": {"v": -1, "scale": 0}}
            return pre + [{"abend": {"code": code}}]
        # resolved when the whole unit is parsed (tools/cobolfe/unit.py): a CALL of a program of the
        # unit becomes `callLocal`, of another program `call` as before
        self.calls.append({"prog": prog, "target": self.ref_json(target) if target is not None else None,
                           "args": args, "onExc": exc if exc is not None else ovf, "notOnExc": nexc,
                           "line": t.line})
        return pre + [{"%call": len(self.calls) - 1}]

    def by_content(self, x):
        """`BY CONTENT x`: (MOVE of x's bytes to a hidden item, reference to that item), or None after
        recording why it is unsupported. The hidden item has x's description (so its length), or is
        `PIC X(n)` for an alphanumeric literal of n characters (IBM: "For alphanumeric literals, the called
        subprogram should describe the parameter as PIC X(n)"). Placed after every other item."""
        def whole(r):
            return dict(r, refStart={"lit": {"n": 1}}, refLen=None) if r["refStart"] is None else r
        if x.kind in ("str", "hex"):
            n = len(x.s) if x.kind == "str" else len(x.b)
            e = Entry(self.fresh(), 1, f"%BY-CONTENT-{self.unit.next_id}", None, x.tok, "working")
            e.pic, e.cat = {"alnum": {"len": n}}, "alnum"
            self.dd.records.append(e)
            r = {"item": e.id, "subs": [], "refStart": None, "refLen": None}
            return {"move": {"src": self.to_operand(x), "dsts": [r]}}, r
        if x.kind != "ref":
            self.unsup("CALL ... BY CONTENT of a numeric literal, figurative constant or special register")
            return None
        src = self.ref_json(x)
        if x.rs is not None:
            if x.rl is None or "lit" not in x.rs or "lit" not in x.rl:
                self.unsup("CALL ... BY CONTENT of a reference modification without literal positions")
                return None
            e = Entry(self.fresh(), 1, f"%BY-CONTENT-{self.unit.next_id}", None, x.tok, "working")
            e.pic, e.cat = {"alnum": {"len": x.rl["lit"]["n"]}}, "alnum"
        else:
            def walk(e):
                yield e
                for c in e.children:
                    yield from walk(c)
            if x.entry.parent is not None and any(item_align(c) > 1 for c in walk(x.entry)):
                # SYNCHRONIZED items are aligned from their record: a copy at level 01 could differ
                self.unsup("CALL ... BY CONTENT of a subordinate item with SYNCHRONIZED items")
                return None
            e = self.clone_item(x.entry)
        self.dd.records.append(e)
        r = {"item": e.id, "subs": [], "refStart": None, "refLen": None}
        return {"move": {"src": {"ref": {"r": whole(src)}}, "dsts": [whole(r)]}}, r

    def st_CANCEL(self, t):
        """`CANCEL {literal | identifier}...`: resolved with the unit (tools/cobolfe/unit.py): a program of
        the unit is put back in its initial state; another one is left to link.py (`cancel`)."""
        ts = self.ts
        ts.next()
        out = []
        while ts.peek().kind == "STR" or self.at_identifier():
            if ts.peek().kind == "STR":
                prog, target = ts.next().val, None
            else:
                x = self.identifier()
                prog, target = None, x
                if x.kind != "ref" or not (x.entry.is_group() or x.entry.cat == "alnum") or x.entry.ae is not None:
                    self.unsup("CANCEL of a program named by an item that is not alphanumeric")
                    continue
            self.cancels.append({"prog": prog, "target": self.ref_json(target) if target is not None else None,
                                 "line": t.line})
            out.append({"%cancel": len(self.cancels) - 1})
        if not out and not self.frames[-1]:
            raise ParseError(ts.peek(), "CANCEL without a program name")
        return out

    def clone_item(self, e, parent=None, ids=None):
        """A copy of item e's description (as a level-01 record when `parent` is None): pictures,
        usage and signs as in effect for e, occurrences of its subordinate items, their REDEFINES; no
        VALUE, condition names or indexes."""
        ids = {} if ids is None else ids
        c = Entry(self.fresh(), 1 if parent is None else e.level, "%BY-CONTENT" if parent is None else e.name,
                  parent, e.tok, "working")
        ids[e.id] = c
        c.pic, c.cat, c.pic_text, c.ae, c.pointer = e.pic, e.cat, e.pic_text, e.ae, e.pointer
        c.just, c.bwz, c.sync = e.just, e.bwz, e.sync
        if parent is None:
            c.usage_kw = next((a.usage_kw for a in [e] + e.ancestors() if a.usage_kw is not None), None)
            c.sign = e.sign_clause()
        else:
            c.usage_kw, c.sign, c.occurs = e.usage_kw, e.sign, e.occurs
            if e.redefines is not None:
                c.redefines = ids[e.redefines.id]
        c.children = [self.clone_item(k, c, ids) for k in e.children]
        return c

    # ------------------------------------------------------------------ files
    def file_ref(self):
        t = self.ts.expect_user_word()
        f = self.file_named(t.val)
        if f is None:
            raise ParseError(t, f"unknown file {t.val}")
        return f

    def record_file(self, x):
        """The file whose record area contains item `x`."""
        if x.kind == "ref":
            root = x.entry.root()
            if root.file is not None:
                return root.file_obj   # also a global record of a containing program
        raise ParseError(x.tok, "not a record of a file")

    def record_ref(self, f):
        rec = f.records[0] if f.records else None
        if rec is None:
            raise ParseError(f.tok, f"file {f.name} has no record description")
        return {"item": rec.id, "subs": [], "refStart": None, "refLen": None}

    def st_OPEN(self, t):
        ts = self.ts
        ts.next()
        out = []
        if not ts.at_word("INPUT", "OUTPUT", "I-O", "EXTEND"):
            raise ParseError(ts.peek(), "OPEN needs INPUT, OUTPUT, I-O or EXTEND")
        while ts.at_word("INPUT", "OUTPUT", "I-O", "EXTEND"):
            mode = ts.next().val
            while is_user_word(ts.peek()) and self.file_named(ts.peek().val) is not None:
                f = self.file_ref()
                self.check_file(f)
                rev = ts.accept_word("REVERSED") is not None and self.open_reversed(f, mode)
                if ts.accept_word("WITH"):
                    ts.expect_word("NO")
                    ts.expect_word("REWIND")
                    self.unsup("OPEN ... WITH NO REWIND")
                if rev:
                    out.append({"fopenRev": {"file": f.id}})
                    continue
                out.append({"fopen": {"file": f.id, "mode": mode}})
        return out

    def open_reversed(self, f, mode):
        """OPEN ... REVERSED after file f: True when the IR can carry it (Cobol.Stmt.fopenRev, an OPEN INPUT of a
        sequential file), else the statement is unsupported, named (IBM: REVERSED is an INPUT phrase of format 1 and "not
        valid for VSAM files")."""
        if mode != "INPUT":
            self.unsup(f"OPEN {mode} ... REVERSED (IBM: REVERSED is a phrase of OPEN INPUT)")
        elif f.org == "INDEXED":
            self.unsup("OPEN ... REVERSED of an indexed file (IBM: not valid for VSAM files)")
        else:
            return True
        return False

    def st_CLOSE(self, t):
        ts = self.ts
        ts.next()
        out = []
        while is_user_word(ts.peek()) and self.file_named(ts.peek().val) is not None:
            f = self.file_ref()
            self.check_file(f)
            opt = self.close_reel(f)
            if opt is None:
                opt = self.close_lock(f)
            if opt is not None:
                out.append({"fcloseOpt": {"file": f.id, "opt": opt}})
                continue
            out.append({"fclose": {"file": f.id}})
        if not out:
            raise ParseError(ts.peek(), "CLOSE without a file")
        return out

    def close_reel(self, f):
        """The phrase `REEL` / `UNIT` [[FOR] REMOVAL | [WITH] NO REWIND] after a file of CLOSE (IBM format 1; REEL and
        UNIT are interchangeable) as the IR names it, or None when neither word follows. IBM: "The REEL, UNIT, and NO
        REWIND phrases are not valid for VSAM files"."""
        ts = self.ts
        if not ts.accept_word("REEL", "UNIT"):
            return None
        if ts.accept_word("FOR") or ts.at_word("REMOVAL"):
            ts.expect_word("REMOVAL")
            opt = "REEL-REMOVAL"
        elif ts.accept_word("WITH") or ts.at_word("NO"):
            ts.expect_word("NO")
            ts.expect_word("REWIND")
            opt = "REEL-NO-REWIND"
        else:
            opt = "REEL"
        if f.org == "INDEXED":
            self.unsup("CLOSE ... REEL / UNIT of an indexed file (IBM: not valid for VSAM files)")
        return opt

    def close_lock(self, f):
        """The phrase [WITH] NO REWIND or [WITH] LOCK after a file of CLOSE (IBM formats 1 and 2) as the IR names it, or
        None when none follows. IBM: NO REWIND is "not valid for VSAM files"; LOCK is a phrase of every file."""
        ts = self.ts
        w = ts.expect_word("LOCK", "NO") if ts.accept_word("WITH") else ts.accept_word("LOCK", "NO")
        if w is None:
            return None
        if w.val == "LOCK":
            return "LOCK"
        ts.expect_word("REWIND")
        if f.org == "INDEXED":
            self.unsup("CLOSE ... NO REWIND of an indexed file (IBM: not valid for VSAM files)")
        return "NO-REWIND"

    def check_file(self, f):
        """Record the constructs of a file the model does not cover."""
        if f.org not in ("SEQUENTIAL", "INDEXED"):
            self.unsup(f"{f.org} file {f.name}")

    def st_READ(self, t):
        ts = self.ts
        ts.next()
        f = self.file_ref()
        nxt = ts.accept_word("NEXT", "PREVIOUS")
        ts.accept_word("RECORD")
        into = None
        if ts.accept_word("INTO"):
            into = self.identifier()
            if self.is_ae(into):
                self.unsup("READ INTO an alphanumeric-edited item")
        key = None
        if ts.accept_word("KEY"):
            ts.accept_word("IS")
            key = self.identifier()
        if ts.accept_word("WITH"):
            ts.expect_word("NO")
            ts.expect_word("LOCK")
        at_end, not_at_end = self.phrase(["END"], prefixes=("AT",))
        inv, not_inv = self.phrase(["INVALID", "KEY"], prefixes=())
        self.end("END-READ")
        self.check_file(f)
        if nxt is not None and nxt.val == "PREVIOUS":
            self.unsup("READ PREVIOUS")
        keyed = f.org == "INDEXED" and (f.access == "RANDOM" or (f.access == "DYNAMIC" and nxt is None))
        if keyed:
            if at_end is not None or not_at_end is not None:
                raise ParseError(t, "AT END in a keyed READ")
            kid = self.key_item(f, key)
            trap, exc, noexc = inv is not None, inv or [], not_inv or []
        else:
            if key is not None:
                raise ParseError(t, "KEY IS in a sequential READ")
            if inv is not None or not_inv is not None:
                raise ParseError(t, "INVALID KEY in a sequential READ")
            kid = None
            trap, exc, noexc = at_end is not None, at_end or [], not_at_end or []
        return [{"fread": {"file": f.id, "key": kid,
                           "into": self.ref_json(into) if into is not None else None,
                           "trap": trap, "exc": exc, "noExc": noexc}}]

    def key_item(self, f, key):
        """Item id of the key of reference of a keyed READ (default: the record key)."""
        if key is None:
            if f.key is None:
                raise ParseError(f.tok, f"indexed file {f.name} without RECORD KEY")
            t, names = f.key
            return self.dd.lookup(t, names, files=self.files).id
        if key.kind != "ref":
            raise ParseError(key.tok, "KEY IS needs a data name")
        return key.entry.id

    def st_WRITE(self, t):
        ts = self.ts
        ts.next()
        rec = self.identifier()
        f = self.record_file(rec)
        src = None
        if ts.accept_word("FROM"):
            src = self.primary()
        if ts.at_word("AFTER", "BEFORE"):
            ts.next()
            ts.accept_word("ADVANCING")
            if ts.accept_word("PAGE"):
                pass
            else:
                self.primary()
                ts.accept_word("LINE", "LINES")
            self.unsup("WRITE ... ADVANCING")
        eop, neop = self.phrase(["END-OF-PAGE"], prefixes=("AT",))
        eop2, neop2 = self.phrase(["EOP"], prefixes=("AT",))
        inv, not_inv = self.phrase(["INVALID", "KEY"], prefixes=())
        self.end("END-WRITE")
        if any(p is not None for p in (eop, neop, eop2, neop2)):
            self.unsup("WRITE ... END-OF-PAGE")
        self.check_file(f)
        if f.org != "INDEXED" and (inv is not None or not_inv is not None):
            raise ParseError(t, "INVALID KEY in a WRITE to a sequential file")
        if src is not None and self.is_ae(rec):
            self.unsup("WRITE FROM into an alphanumeric-edited record")
        out = []
        r = self.ref_json(rec)
        if src is not None:
            out.append({"move": {"src": self.to_operand(src), "dsts": [r]}})
        out.append({"fwrite": {"file": f.id, "rec": r, "trap": inv is not None, "exc": inv or [],
                               "noExc": not_inv or []}})
        return out

    def st_REWRITE(self, t):
        ts = self.ts
        ts.next()
        rec = self.identifier()
        f = self.record_file(rec)
        src = None
        if ts.accept_word("FROM"):
            src = self.primary()
        inv, not_inv = self.phrase(["INVALID", "KEY"], prefixes=())
        self.end("END-REWRITE")
        self.check_file(f)
        if src is not None and self.is_ae(rec):
            self.unsup("REWRITE FROM into an alphanumeric-edited record")
        out = []
        r = self.ref_json(rec)
        if src is not None:
            out.append({"move": {"src": self.to_operand(src), "dsts": [r]}})
        out.append({"frewrite": {"file": f.id, "rec": r, "trap": inv is not None, "exc": inv or [],
                                 "noExc": not_inv or []}})
        return out

    def st_DELETE(self, t):
        ts = self.ts
        ts.next()
        f = self.file_ref()
        ts.accept_word("RECORD")
        inv, not_inv = self.phrase(["INVALID", "KEY"], prefixes=())
        self.end("END-DELETE")
        self.check_file(f)
        return [{"fdelete": {"file": f.id, "trap": inv is not None, "exc": inv or [],
                             "noExc": not_inv or []}}]

    def st_START(self, t):
        ts = self.ts
        ts.next()
        f = self.file_ref()
        op, key = "=", None
        if ts.accept_word("KEY"):
            r = self.try_relop()
            if r is None:
                raise ParseError(ts.peek(), "START KEY needs a relational operator")
            neg, o = r
            op = {(False, "="): "=", (False, ">"): ">", (False, ">="): ">=",
                  (True, "<"): ">="}.get((neg, o))
            x = self.identifier()
            key = x.entry.id if x.kind == "ref" else None
            if op is None:
                self.unsup(f"START KEY {'NOT ' if neg else ''}{o}")
        inv, not_inv = self.phrase(["INVALID", "KEY"], prefixes=())
        self.end("END-START")
        self.check_file(f)
        if f.org != "INDEXED":
            self.unsup(f"START of a sequential file ({f.name})")
            return []
        if f.access == "RANDOM":
            raise ParseError(t, f"START of {f.name}, which has ACCESS RANDOM")
        if op is None:
            return []
        return [{"fstart": {"file": f.id, "op": op, "key": key, "trap": inv is not None,
                            "exc": inv or [], "noExc": not_inv or []}}]

    # ------------------------------------------------------------------ string handling
    def st_STRING(self, t):
        """`STRING src... DELIMITED BY SIZE ... INTO r [ON OVERFLOW ...]`: with every source
        delimited by SIZE and no POINTER the positions are static, so it is lowered to
        reference-modified MOVEs of the sources' bytes (STRING never pads the receiver)."""
        ts = self.ts
        ts.next()
        groups = []
        cur = []
        static = True
        while not ts.at_word("INTO"):
            p = ts.peek()
            if p.is_word("DELIMITED"):
                ts.next()
                ts.accept_word("BY")
                if ts.accept_word("SIZE"):
                    d = "SIZE"
                else:
                    d = self.primary()
                    static = False
                groups.append((cur, d))
                cur = []
            elif p.kind in ("PERIOD", "EOF"):
                raise ParseError(p, "STRING without INTO")
            else:
                cur.append(self.primary())
        if cur:
            raise ParseError(ts.peek(), "STRING source without DELIMITED BY")
        ts.expect_word("INTO")
        into = self.identifier()
        ptr = None
        if ts.accept_word("WITH") or ts.at_word("POINTER"):
            ts.expect_word("POINTER")
            ptr = self.identifier()
            static = False
        ovf, novf = self.phrase(["OVERFLOW"], prefixes=("ON",))
        self.end("END-STRING")
        if any(x.kind == "ref" and x.rs is None and self.odo_group(x.entry)
               for x in [s for srcs, _ in groups for s in srcs] + [into]):
            # a group containing an OCCURS DEPENDING ON table has no static length
            static = False
        if not static:
            # dynamic positions: the STRING statement itself (Cobol/Sem/StringInto.lean)
            if into.kind != "ref" or into.entry.cat not in ("alnum", None) or self.is_ae(into):
                self.unsup("STRING INTO a non-alphanumeric item")
                return []
            gs = [{"srcs": [self.to_operand(x) for x in srcs],
                   "delim": None if d == "SIZE" else self.to_operand(d)} for srcs, d in groups]
            return [{"stringInto": {"groups": gs, "into": self.ref_of(into),
                                    "ptr": self.ref_of(ptr) if ptr is not None else None,
                                    "onOvf": ovf, "notOnOvf": novf or []}}]
        if into.kind != "ref" or into.rs is not None or into.entry.cat not in ("alnum", None) or self.is_ae(into):
            self.unsup("STRING INTO a non-alphanumeric or reference-modified item")
            return []
        rlen = item_size(into.entry)
        out = []
        pos = 1
        overflow = False
        for srcs, _ in groups:
            for s in srcs:
                if overflow:
                    break
                src, n = self.string_source(s)
                if n is None:
                    return []
                take = min(n, rlen - pos + 1)
                if take < n:
                    overflow = True
                if take <= 0:
                    break
                if src.get("ref") is not None and take < n:
                    src["ref"]["r"]["refLen"] = {"lit": {"n": take}}
                elif src.get("lit") is not None and take < n:
                    src = {"lit": {"l": {"str": {"s": src["lit"]["l"]["str"]["s"][:take]}}}}
                r = self.ref_json(into)
                r = dict(r, refStart={"lit": {"n": pos}}, refLen={"lit": {"n": take}})
                out.append({"move": {"src": src, "dsts": [r]}})
                pos += take
        if overflow:
            out += ovf or []
        else:
            out += novf or []
        return out

    def string_source(self, x):
        """A STRING source as an operand of its raw bytes, with its length."""
        if x.kind == "ref":
            if x.rs is not None:
                if x.rl is not None and "lit" in x.rl and "lit" in x.rs:
                    return {"ref": {"r": self.ref_json(x)}}, x.rl["lit"]["n"]
                self.unsup("STRING source with a variable reference modification")
                return None, None
            n = item_size(x.entry)
            r = dict(self.ref_json(x), refStart={"lit": {"n": 1}}, refLen={"lit": {"n": n}})
            return {"ref": {"r": r}}, n
        if x.kind == "str":
            return {"lit": {"l": {"str": {"s": x.s}}}}, len(x.s)
        if x.kind == "num" and x.v >= 0 and x.scale == 0 and not x.tok.val.startswith("+"):
            s = x.tok.val
            return {"lit": {"l": {"str": {"s": s}}}}, len(s)
        if x.kind == "fig" and x.name in ("SPACE", "ZERO", "QUOTE", "HIGH-VALUE", "LOW-VALUE"):
            return {"lit": {"l": {"fig": {"name": x.name}}}}, 1
        self.unsup("STRING source")
        return None, None

    def st_UNSTRING(self, t):
        ts = self.ts
        ts.next()
        src = self.ref_of(self.identifier(), "UNSTRING sending item")
        delims = []
        if ts.accept_word("DELIMITED"):
            ts.accept_word("BY")
            while True:
                al = bool(ts.accept_word("ALL"))
                delims.append({"all": al, "op": self.to_operand(self.primary())})
                if not ts.accept_word("OR"):
                    break
        ts.expect_word("INTO")
        into = []
        while self.at_identifier():
            x = self.identifier()
            if self.is_ae(x):
                self.unsup("UNSTRING INTO an alphanumeric-edited item")
            r = {"rcv": self.ref_of(x, "UNSTRING receiver"), "delim": None, "count": None}
            if ts.accept_word("DELIMITER"):
                ts.accept_word("IN")
                dl = self.identifier()
                if self.is_ae(dl):
                    self.unsup("UNSTRING DELIMITER IN an alphanumeric-edited item")
                r["delim"] = self.ref_of(dl, "DELIMITER IN item")
            if ts.accept_word("COUNT"):
                ts.accept_word("IN")
                r["count"] = self.ref_of(self.identifier(), "COUNT IN item")
            into.append(r)
        if not into:
            raise ParseError(ts.peek(), "UNSTRING without receivers")
        ptr = tally = None
        if ts.accept_word("WITH") or ts.at_word("POINTER"):
            ts.expect_word("POINTER")
            ptr = self.ref_of(self.identifier(), "POINTER item")
        if ts.accept_word("TALLYING"):
            ts.accept_word("IN")
            tally = self.ref_of(self.identifier(), "TALLYING item")
        on, not_on = self.phrase(["OVERFLOW"], prefixes=("ON",))
        self.end("END-UNSTRING")
        return [{"unstring": {"src": src, "delims": delims, "into": into, "ptr": ptr,
                              "tally": tally, "onOvf": on, "notOnOvf": not_on or []}}]

    def st_INSPECT(self, t):
        ts = self.ts
        ts.next()
        target = self.ref_of(self.identifier(), "INSPECT item")

        def at_operand():
            p = ts.peek()
            return p.kind in ("NUM", "STR", "HEX", "NSTR", "ZSTR") or self.at_identifier() or \
                (p.kind == "WORD" and p.val in FIGURATIVE)

        def operand():
            return self.to_operand(self.primary())

        def bounds():
            before = after = None
            while ts.at_word("BEFORE", "AFTER"):
                w = ts.next().val
                ts.accept_word("INITIAL")
                if w == "BEFORE":
                    before = operand()
                else:
                    after = operand()
            return before, after

        def counter_next():
            # an identifier followed by FOR starts the next counter of TALLYING
            if not self.at_identifier():
                return False
            i = ts.i
            self.identifier()
            r = ts.at_word("FOR")
            ts.i = i
            return r

        if ts.accept_word("CONVERTING"):
            src = operand()
            ts.expect_word("TO")
            dst = operand()
            before, after = bounds()
            return [{"convert": {"target": target, "src": src, "dst": dst,
                                 "before": before, "after": after}}]
        tally, repl = [], []
        if ts.accept_word("TALLYING"):
            while counter_next():
                ctr = self.ref_of(self.identifier(), "TALLYING counter")
                ts.expect_word("FOR")
                while True:
                    if ts.accept_word("CHARACTERS"):
                        before, after = bounds()
                        tally.append({"kind": "chars", "before": before, "after": after, "counter": ctr})
                    elif ts.at_word("ALL", "LEADING"):
                        kind = ts.next().val.lower()
                        while at_operand() and not counter_next():
                            pat = operand()
                            before, after = bounds()
                            tally.append({"kind": kind, "pat": pat, "before": before, "after": after,
                                          "counter": ctr})
                    else:
                        break
        if ts.accept_word("REPLACING"):
            while True:
                if ts.accept_word("CHARACTERS"):
                    ts.expect_word("BY")
                    rep = operand()
                    before, after = bounds()
                    repl.append({"kind": "chars", "rep": rep, "before": before, "after": after})
                elif ts.at_word("ALL", "LEADING", "FIRST"):
                    kind = ts.next().val.lower()
                    while at_operand():
                        pat = operand()
                        ts.expect_word("BY")
                        rep = operand()
                        before, after = bounds()
                        repl.append({"kind": kind, "pat": pat, "rep": rep, "before": before, "after": after})
                else:
                    break
        if not tally and not repl:
            raise ParseError(ts.peek(), "INSPECT needs TALLYING, REPLACING or CONVERTING")
        return [{"inspect": {"target": target, "tally": tally, "replace": repl}}]

    def st_SEARCH(self, t):
        """Serial `SEARCH table [VARYING x] [AT END ...] WHEN c ... [END-SEARCH]`: the table's
        first index (or the VARYING index when it is one of the table's) runs from its current
        value to the OCCURS count.  `SEARCH ALL` (binary search) is unsupported."""
        ts = self.ts
        ts.next()
        if ts.accept_word("ALL"):
            return self.search_all(t)
        tt = ts.expect_user_word()
        names = [tt.val]
        while ts.at_word("OF", "IN"):
            ts.next()
            names.append(ts.expect_user_word().val)
        tab = self.dd.lookup(tt, names, files=self.files)
        if isinstance(tab, IndexEntry) or getattr(tab, "occurs", None) is None:
            raise ParseError(tt, f"SEARCH {tt.val}: not a table (no OCCURS)")
        idxs = [ie for ie in self.dd.indexes if ie.table is tab]
        var_idx = var_ref = var_ix = None
        if ts.accept_word("VARYING"):
            v = self.identifier()
            if v.kind == "idx" and any(ie.id == v.id for ie in idxs):
                idxs = [ie for ie in idxs if ie.id == v.id]
            elif v.kind == "idx":
                var_idx = v.id
            elif v.kind == "ixd":
                var_ix = v
            else:
                var_ref = self.ref_of(v, "SEARCH VARYING item")
        if not idxs:
            raise ParseError(tt, f"SEARCH {tt.val}: the table has no INDEXED BY")
        if var_ix is not None:
            # IBM: the index data item "is simultaneously increased by the same amount" as the
            # search index, i.e. by one occurrence of the table. A hidden index name counts the
            # occurrences (no 7-digit limit); the item takes its value where the search ends, in
            # the WHEN phrase that runs or at the end, and WHEN conditions may not read the item
            if any("idx" in s and s["idx"]["id"] == idxs[0].id for s in var_ix.subs):
                self.unsup("SEARCH VARYING an index data item subscripted by the search index")
            var_idx = self.fresh()
            self.ix_link(var_ix.entry, idxs[0].id)
        at_end, _ = self.phrase(["END"], prefixes=("AT",))
        conds, bodies = [], []
        while ts.accept_word("WHEN"):
            watch, self.ix_watch = self.ix_watch, var_ix.entry if var_ix is not None else None
            try:
                conds.append(self.cond())
            finally:
                self.ix_watch = watch
            bodies.append(self.stmts())
        if not conds:
            raise ParseError(ts.peek(), "SEARCH without WHEN")
        self.end("END-SEARCH")
        pre = []
        if var_ix is not None:
            def upd():
                return {"compute": {"rcv": [{"ref": self.ix_ref(var_ix), "rounded": None}],
                                    "e": {"idx": {"id": var_idx}},
                                    "onSize": [{"unsupported": {"what": IX_RANGE}}], "notOnSize": []}}
            pre = [{"setIdx": {"id": var_idx, "e": {"ref": {"r": self.ix_ref(var_ix)}}}}]
            at_end = [upd()] + (at_end or [])
            bodies = [[upd()] + b for b in bodies]
        return pre + [{"search": {"idx": idxs[0].id, "occurs": tab.occurs, "varIdx": var_idx,
                                  "varRef": var_ref, "atEnd": at_end or [], "conds": conds,
                                  "bodies": bodies}}]

    def search_all(self, t):
        """`SEARCH ALL table [AT END ...] WHEN cond stmts [END-SEARCH]`: binary search of a table
        with OCCURS ... ASCENDING / DESCENDING KEY and INDEXED BY (the first index)."""
        ts = self.ts
        tt = ts.expect_user_word()
        names = [tt.val]
        while ts.at_word("OF", "IN"):
            ts.next()
            names.append(ts.expect_user_word().val)
        tab = self.dd.lookup(tt, names, files=self.files)
        if isinstance(tab, IndexEntry) or getattr(tab, "occurs", None) is None:
            raise ParseError(tt, f"SEARCH ALL {tt.val}: not a table (no OCCURS)")
        idxs = [ie for ie in self.dd.indexes if ie.table is tab]
        if not idxs:
            raise ParseError(tt, f"SEARCH ALL {tt.val}: the table has no INDEXED BY")
        if not tab.keys:
            raise ParseError(tt, f"SEARCH ALL {tt.val}: the table has no ASCENDING / DESCENDING KEY")
        keys = []
        for asc, kname in tab.keys:
            # IBM: a KEY names the table entry itself or an item subordinate to it
            ke = tab if kname == tab.name else self.dd.lookup(tt, [kname, tab.name], files=self.files)
            if getattr(ke, "index", False) or self.dd.overlap_ix(ke) is not None:
                self.unsup(f"SEARCH ALL: key {kname} is or shares storage with an index data item")
                return []
            if ke.dims() != 1:
                self.unsup(f"SEARCH ALL: key {kname} in a table of {ke.dims()} levels")
                return []
            keys.append({"asc": asc, "key": {"item": ke.id, "subs": [{"idx": {"id": idxs[0].id, "k": 0}}],
                                             "refStart": None, "refLen": None}})
        at_end, _ = self.phrase(["END"], prefixes=("AT",))
        ts.expect_word("WHEN")
        cond = self.cond()
        body = self.stmts()
        if ts.at_word("WHEN"):
            raise ParseError(ts.peek(), "SEARCH ALL has a single WHEN phrase")
        self.end("END-SEARCH")
        return [{"searchAll": {"idx": idxs[0].id, "occurs": tab.occurs, "keys": keys,
                               "atEnd": at_end or [], "c": cond, "body": body}}]

    def st_ACCEPT(self, t):
        """`ACCEPT x FROM DATE [YYYYMMDD] / TIME`: characters of a clock reading. `ACCEPT x [FROM
        SYSIN | SYSIPT | mnemonic-name]`: the system input device (accept_sysin)."""
        ts = self.ts
        ts.next()
        dst = self.identifier()
        src = None
        if ts.accept_word("FROM"):
            w = ts.next()
            src = w.val
            if ts.at_word("YYYYMMDD", "YYYYDDD"):
                src += " " + ts.next().val
        exc, nexc = self.phrase(["EXCEPTION"], prefixes=("ON",))
        self.end("END-ACCEPT")
        if exc is not None or nexc is not None:
            self.unsup("ACCEPT ... ON EXCEPTION")
        # IBM: "When the FROM phrase is omitted, the system input device is assumed"; a mnemonic name
        # takes precedence over the environment-name it spells
        if src is None or self.devices.get(src, src) in SYSIN_NAMES:
            return self.accept_sysin(dst)
        pos = {"DATE": (3, 6), "DATE YYYYMMDD": (1, 8), "TIME": (9, 8)}.get(src)
        if self.is_ae(dst):
            self.unsup("ACCEPT into an alphanumeric-edited item")
            return []
        if src in ("DAY", "DAY YYYYDDD", "DAY-OF-WEEK"):
            return self.accept_day(t, dst, src)
        if pos is None:
            self.unsup(f"ACCEPT FROM {src}" if src else "ACCEPT from the input stream")
            return []
        return [{"clock": {"dst": self.ref_of(dst), "start": pos[0], "len": pos[1]}}]

    def accept_sysin(self, dst):
        """IBM ACCEPT format 1 from the system input device: the next records of the input stream
        fill x unchanged ("There is no editing or error checking of the incoming data"; `accept`,
        Cobol/Sem/Exec.lean sysinRead). x is "An alphanumeric group item" or "An elementary data
        item of usage DISPLAY, DISPLAY-1, or NATIONAL" (the other usages: a compile error). A group
        with an OCCURS DEPENDING ON table is unsupported (IBM does not say which length the transfer
        fills)."""
        if dst.kind == "ref" and not dst.entry.is_group() and (dst.entry.usage() != "display" or dst.entry.pointer):
            raise ParseError(dst.tok, f"ACCEPT {dst.entry.name}: not a group or an item of usage DISPLAY")
        if dst.kind == "ref" and self.odo_group(dst.entry):
            self.unsup("ACCEPT from the input stream into a group with OCCURS DEPENDING ON")
            return []
        return [{"accept": {"dst": self.ref_of(dst, "the ACCEPT receiving item")}}]

    def accept_day(self, t, dst, src):
        """`ACCEPT x FROM DAY [YYYYDDD]` / `DAY-OF-WEEK` (IBM: YYDDD, PICTURE 9(5); YYYYDDD, 9(7); a
        digit, 1 = Monday to 7 = Sunday, PICTURE 9; moved as an unsigned integer): the YYYYMMDD of one
        clock reading into the hidden item %CLOCK-DATE, the value computed with INTEGER-OF-DATE (day
        1 = 1601-01-01, a Monday) into a hidden item with the implicit PICTURE, then MOVEd to x."""
        def ref(e):
            return {"item": e.id, "subs": [], "refStart": None, "refLen": None}

        def lit(v):
            return {"lit": {"v": v, "scale": 0}}

        def fn(name, *args):
            return {"fn": {"name": name, "args": list(args)}}
        d8 = self.dd.hidden_num(t, "%CLOCK-DATE", 8)
        date = {"ref": {"r": ref(d8)}}
        year = fn("INTEGER-PART", {"div": {"a": date, "b": lit(10000), "scale": None}})
        day1 = fn("INTEGER-OF-DATE", date)
        doy = {"add": {"a": {"sub": {"a": day1, "b": fn("INTEGER-OF-DATE", {"add": {"a": {"mul": {
            "a": year, "b": lit(10000)}}, "b": lit(101)}})}}, "b": lit(1)}}
        if src == "DAY":
            res, n, e = "%CLOCK-DAY", 5, {"add": {"a": {"mul": {"a": fn("MOD", year, lit(100)), "b": lit(1000)}},
                                                  "b": doy}}
        elif src == "DAY YYYYDDD":
            res, n, e = "%CLOCK-DAY-YYYYDDD", 7, {"add": {"a": {"mul": {"a": year, "b": lit(1000)}}, "b": doy}}
        else:
            res, n, e = "%CLOCK-DAY-OF-WEEK", 1, {"add": {"a": fn("MOD", {"sub": {"a": day1, "b": lit(1)}}, lit(7)),
                                                          "b": lit(1)}}
        r = self.dd.hidden_num(t, res, n)
        return [{"clock": {"dst": ref(d8), "start": 1, "len": 8}},
                {"compute": {"rcv": [{"ref": ref(r), "rounded": None}], "e": e, "onSize": None, "notOnSize": []}},
                {"move": {"src": {"ref": {"r": ref(r)}}, "dsts": [self.ref_of(dst)]}}]

    def st_EXEC(self, t):
        self.ts.next()
        self.unsup(f"EXEC {t.val.split()[0] if t.val else ''}".strip())
        return []

    def skip_statement(self):
        """Skip to the end of the current statement (next verb or separator)."""
        ts = self.ts
        while True:
            p = ts.peek()
            if p.kind in ("PERIOD", "EOF", "EXEC"):
                return
            if p.kind == "WORD" and (p.val in VERBS or p.val.startswith("END-") or p.val in ("ELSE", "WHEN")):
                return
            ts.next()

    def st_generic(self, t):
        """A verb without a parser: skip to its END-verb (or to the next verb / period)."""
        ts = self.ts
        ts.next()
        end = "END-" + t.val
        depth = 0
        while True:
            p = ts.peek()
            if p.kind in ("PERIOD", "EOF"):
                break
            if p.is_word(t.val):
                depth += 1
            if p.is_word(end):
                ts.next()
                if depth == 0:
                    break
                depth -= 1
                continue
            if p.kind == "WORD" and depth == 0 and (p.val in VERBS or p.val in ("ELSE", "WHEN")) \
                    and not self.has_end_ahead(end):
                break
            ts.next()
        self.unsup(t.val)
        return []

    def has_end_ahead(self, end):
        toks, i = self.ts.toks, self.ts.i
        while i < len(toks) and toks[i].kind != "PERIOD":
            if toks[i].is_word(end):
                return True
            i += 1
        return False

    # ================================================================== output
    def files_json(self):
        out = []
        for f in self.files.values():
            if not f.records:
                continue
            def item_id(q):
                t, names = q
                return self.dd.lookup(t, names, files=self.files).id
            # the records of an FD share one record area, as long as the largest of them (the
            # first largest names it); records of different lengths without a RECORD clause make
            # the file variable-length, from the shortest to the longest record (a WRITE writes
            # the named record's length)
            sizes = [item_size(r) for r in f.records]
            area = f.records[sizes.index(max(sizes))]
            mn, mx = f.min_len, f.max_len
            # a record with an OCCURS DEPENDING ON table is as short as its integer-1 occurrences
            # make it (IBM, RECORD clause format 3), and makes the file variable-length
            mins = [s - self.odo_slack(r) for s, r in zip(sizes, f.records)]
            if mn is None and mx is None and f.depending is None and (len(set(sizes)) > 1 or mins != sizes):
                mn, mx = min(mins), max(sizes)
            out.append({"id": f.id,
                        "org": "indexed" if f.org == "INDEXED" else "sequential",
                        "access": f.access.lower(),
                        "record": area.id,
                        "key": item_id(f.key) if f.key is not None else None,
                        "alt": [[item_id(k), d] for (k, d) in f.alt_keys],
                        "status": item_id(f.status) if f.status is not None else None,
                        "minLen": mn, "maxLen": mx,
                        "dependsOn": item_id(f.depending) if f.depending is not None else None,
                        **({"optional": True} if f.optional else {})})
        return out

    def json(self):
        is_main = self.is_main if self.is_main is not None else not self.using
        return {"name": self.name, "config": self.config, "dialect": {"divExtraForRounded": True},
                "data": self.dd.json(), "paras": self.paras, "isMain": is_main, "using": [e.id for e in self.using],
                "files": self.files_json(), **({"use": self.use} if getattr(self, "use", None) else {}),
                **({"collating": self.collating} if self.collating is not None else {}),
                **({"odo": self.dd.odo_json()} if self.dd.odo_tables else {}),
                # an INITIAL called program (for tools/cobolfe/link.py; the resolver ignores the key)
                **({"initial": True} if self.initial and self.parent is None else {})}


def parse_program(toks, **opts):
    """The unit's surface IR (its first program, with the others linked in: tools/cobolfe/unit.py)
    and the first program's parse state (`p.unit.programs`: all of them)."""
    from unit import link_unit
    p = Program(toks, **opts)
    p.parse()
    while p.ts.peek().kind != "EOF":
        # the next separately compiled program of a batch (the previous one ended with END PROGRAM)
        Program(None, is_main=False, unit=p.unit, ts=p.ts, **p.opts).parse()
    # the index data item check once more over the whole unit (a GLOBAL one is named in several programs)
    p.ix_finish()
    return link_unit(p.unit), p

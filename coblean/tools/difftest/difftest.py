#!/usr/bin/env python3
"""Differential testing of the Lean COBOL semantics against GnuCOBOL.

Each random test is generated twice: as a COBOL program (compiled with GnuCOBOL,
`-std=ibm`) and as surface-IR JSON (resolved and run by `cobolrun`, the Lean reference
interpreter, with `Config.gnucobol`).  Both dump the bytes of the working-storage record
`R` at the end; the dumps must be identical.  Every outcome phrase (IF / ELSE, ON SIZE ERROR,
NOT ON SIZE ERROR) writes its letter to FLAG and to its statement's own byte of OTRACE, so a
later statement cannot hide which phrase ran.

Status of a test whose dumps differ although every field decodes to the same value:
  ok-negzero    a signed field holds 0 with the opposite sign (packed D vs C, separate '-' vs
                '+', overpunch negative zero vs '0'), and nothing else differs;
  ok-packed-fc  a signed packed field holds the same value with sign nibble F vs C (GnuCOBOL
                keeps F after a MOVE from an unsigned item), and nothing else differs;
  mismatch-bytes  any other byte difference (a failure).

usage: difftest.py [--n N] [--seed S] [--out DIR] [--kinds k1,k2,...] [--keep]
"""
import argparse
import json
import os
import random
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
COBC = os.path.join(ROOT, "scripts", "cobc.sh")
COBOLRUN = os.path.join(ROOT, ".lake", "build", "bin", "cobolrun")
LIBDIR = os.path.join(ROOT, "third_party", "gnucobol", "usr", "lib", "x86_64-linux-gnu")

CONFIG = {"charset": "ascii", "zonedSign": "asciiMF", "trunc": "std", "numprocPfd": False,
          "binaryLE": False, "comp5LE": True, "binary1Byte": False, "sizeErrorTruncates": True}

# GnuCOBOL flags per TRUNC mode.  -std=ibm defaults to binary-truncate: no (TRUNC(BIN)) and
# arithmetic-osvs: yes (OS/VS intermediate precision); Enterprise COBOL has neither.
COBC_FLAGS = {"std": ["-std=ibm", "-fbinary-truncate", "-fno-arithmetic-osvs"],
              "bin": ["-std=ibm", "-fno-arithmetic-osvs"]}
TRUNC = "std"
BIN_SIZE_QUIRK = False
FRONTEND = False
COBOLFE = os.environ.get("COBOLFE", os.path.join(ROOT, "tools", "cobolfe", "cobolfe.py"))

MODES = ["NEAREST-AWAY-FROM-ZERO", "AWAY-FROM-ZERO", "NEAREST-EVEN", "NEAREST-TOWARD-ZERO",
         "TOWARD-GREATER", "TOWARD-LESSER", "TRUNCATION"]

EDIT_PICS = [
    ("ZZZ9.99", "z z z nine dot nine nine"),
    ("-ZZ9.99", "minus z z nine dot nine nine"),
    ("ZZ9.99-", "z z nine dot nine nine minus"),
    ("+999.99", "plus nine nine nine dot nine nine"),
    ("ZZ,ZZ9.99CR", "z z comma z z nine dot nine nine cr"),
    ("ZZZ9.99DB", "z z z nine dot nine nine db"),
    ("$$$,$$9.99", "cs cs cs comma cs cs nine dot nine nine"),
    ("***9.99", "star star star nine dot nine nine"),
    ("ZZZZ9", "z z z z nine"),
    ("----9.99", "minus minus minus minus nine dot nine nine"),
    ("++++9", "plus plus plus plus nine"),
    ("99/99/99", "nine nine slash nine nine slash nine nine"),
    ("9B999", "nine b nine nine nine"),
    ("ZZZ.ZZ", "z z z dot z z"),
    ("$ZZ9.99", "cs z z nine dot nine nine"),
]


def jbool(b):
    return bool(b)


# ---------------------------------------------------------------- surface-IR JSON helpers
def ref(item):
    return {"item": item, "subs": [], "refStart": None, "refLen": None}


def op_ref(item):
    return {"ref": {"r": ref(item)}}


def op_num(v, scale, digits=0):
    return {"lit": {"l": {"num": {"v": v, "scale": scale, "digits": digits}}}}


def op_str(s):
    return {"lit": {"l": {"str": {"s": s}}}}


def op_fig(n):
    return {"lit": {"l": {"fig": {"name": n}}}}


def e_lit(v, s):
    return {"lit": {"v": v, "scale": s}}


def e_ref(item):
    return {"ref": {"r": ref(item)}}


def e_bin(op, a, b):
    return {op: {"a": a, "b": b}}


def e_div(a, b):
    # GnuCOBOL divides with ~38 significant digits; pin the IR's intermediate scale wide so the
    # test exercises the core rounding semantics, not the IBM intermediate-precision estimate
    return {"div": {"a": a, "b": b, "scale": 30}}


def rcv(item, rounded):
    return {"ref": ref(item), "rounded": rounded}


def item_json(it):
    return {"id": it["id"], "level": it["level"], "name": it["name"], "pic": it["pic"],
            "usage": it.get("usage", "display"), "occurs": it.get("occurs", 1),
            "redefines": it.get("redefines"), "value": it.get("value"),
            "just": jbool(it.get("just")), "signSep": jbool(it.get("signSep")),
            "signLead": jbool(it.get("signLead")), "bwz": jbool(it.get("bwz")),
            "sync": False, "conds": [], "children": [item_json(c) for c in it.get("children", [])]}


# ---------------------------------------------------------------- random data
class Field:
    def __init__(self, fid, name, kind, digits=0, scale=0, signed=False, usage="display",
                 sign_lead=False, sign_sep=False, length=0, edit=None, just=False):
        self.id, self.name, self.kind = fid, name, kind
        self.digits, self.scale, self.signed, self.usage = digits, scale, signed, usage
        self.sign_lead, self.sign_sep, self.length, self.edit, self.just = \
            sign_lead, sign_sep, length, edit, just

    @property
    def numeric(self):
        return self.kind == "num"

    def pic_cobol(self):
        if self.kind == "alnum":
            return f"X({self.length})"
        if self.kind == "edit":
            return self.edit[0]
        i = self.digits - self.scale
        s = "S" if self.signed else ""
        if i > 0 and self.scale > 0:
            return f"{s}9({i})V9({self.scale})"
        if i > 0:
            return f"{s}9({i})"
        return f"{s}V9({self.scale})"

    def pic_json(self):
        if self.kind == "alnum":
            return {"alnum": {"len": self.length}}
        if self.kind == "edit":
            return {"numEdited": {"pic": self.edit[1].split()}}
        return {"num": {"digits": self.digits, "scale": self.scale, "signed": self.signed}}

    def clauses(self):
        out = []
        if self.kind == "num":
            if self.usage == "packed":
                out.append("COMP-3")
            elif self.usage == "binary":
                out.append("COMP")
            elif self.usage == "comp5":
                out.append("COMP-5")
            if self.signed and self.usage == "display" and (self.sign_lead or self.sign_sep):
                out.append("SIGN " + ("LEADING" if self.sign_lead else "TRAILING") +
                           (" SEPARATE" if self.sign_sep else ""))
        if self.just:
            out.append("JUSTIFIED RIGHT")
        return " ".join(out)


def rand_numeric(rng, fid):
    digits = rng.randint(1, 9)
    scale = rng.randint(0, min(digits, 4))
    signed = rng.random() < 0.7
    usage = rng.choice(["display", "display", "packed", "packed", "binary", "comp5"])
    if usage == "packed" and digits % 2 == 0:
        # GnuCOBOL leaves garbage in the pad nibble of even-digit COMP-3 after truncation
        digits = digits + 1 if digits < 9 else digits - 1
        scale = min(scale, digits)
    if usage == "comp5" and TRUNC == "std":
        # GnuCOBOL -fbinary-truncate also truncates COMP-5 to the PICTURE (IBM never does):
        # COMP-5 is tested under the TRUNC(BIN) profile only
        usage = "binary"
    if usage == "comp5" and digits < 3:
        # GnuCOBOL allocates 1 byte for COMP-5 of 1-2 digits even with -std=ibm (IBM: 2)
        digits = rng.randint(3, 9)
        scale = rng.randint(0, min(digits, 4))
    lead = sep = False
    if usage == "display" and signed and rng.random() < 0.3:
        lead = rng.random() < 0.5
        sep = rng.random() < 0.5
    return Field(fid, f"N{fid}", "num", digits, scale, signed, usage, lead, sep)


def rand_value(rng, f):
    """A random value that fits field f, as (scaled int, scale)."""
    if f.usage == "comp5":
        # stay within the PICTURE so both sides agree on VALUE handling
        pass
    m = rng.randint(0, 10 ** f.digits - 1)
    if f.signed and rng.random() < 0.5:
        m = -m
    return m, f.scale


def num_literal_cobol(v, scale):
    sign = "-" if v < 0 else ""
    a = abs(v)
    if scale <= 0:
        return f"{sign}{a * 10 ** (-scale)}"
    s = str(a).rjust(scale + 1, "0")
    return f"{sign}{s[:-scale]}.{s[-scale:]}"


ALNUM_CHARS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 "


class Gen:
    def __init__(self, rng, kinds):
        self.rng = rng
        self.kinds = kinds
        self.fields = []
        self.next_id = 2   # 1 = record R
        self.flag = None
        self.trace = None  # OTRACE, one byte per statement; joins `fields` after the statements
        self.cur = 0       # number of the statement being generated (1-based)

    def new_id(self):
        i = self.next_id
        self.next_id += 1
        return i

    def make_fields(self):
        rng = self.rng
        n = rng.randint(4, 8)
        for _ in range(n):
            fid = self.new_id()
            r = rng.random()
            if r < 0.65:
                f = rand_numeric(rng, fid)
            elif r < 0.85:
                f = Field(fid, f"A{fid}", "alnum", length=rng.randint(1, 8),
                          just=rng.random() < 0.2)
            else:
                ep = rng.choice(EDIT_PICS)
                f = Field(fid, f"E{fid}", "edit", edit=ep)
            self.fields.append(f)
        self.flag = Field(self.new_id(), "FLAG", "alnum", length=1)
        self.fields.append(self.flag)
        # OTRACE is not in `fields` yet, so that the statements never pick it (the random stream is the
        # one of the generator without it)
        self.trace = Field(self.new_id(), "OTRACE", "alnum", length=1)

    def outcome(self, ch):
        """(COBOL, statements) recording outcome `ch` of the current statement: in FLAG, as
        before, and in the statement's own byte of OTRACE."""
        j = self.cur
        tr = {"item": self.trace.id, "subs": [], "refStart": {"lit": {"n": j}}, "refLen": {"lit": {"n": 1}}}
        return (f"MOVE '{ch}' TO FLAG MOVE '{ch}' TO OTRACE({j}:1)",
                [{"move": {"src": op_str(ch), "dsts": [ref(self.flag.id)]}},
                 {"move": {"src": op_str(ch), "dsts": [tr]}}])

    def nums(self):
        return [f for f in self.fields if f.numeric]

    # --- statements: (cobol_lines, json_stmt)
    def st_move_num(self):
        rng = self.rng
        dst = rng.choice([f for f in self.fields if f.kind in ("num", "edit")] or self.fields)
        if rng.random() < 0.5 and self.nums():
            src = rng.choice(self.nums())
            return [f"MOVE {src.name} TO {dst.name}"], {"move": {"src": op_ref(src.id), "dsts": [ref(dst.id)]}}
        digits = rng.randint(1, 8)
        scale = rng.randint(0, min(3, digits))
        if dst.kind == "edit":
            # GnuCOBOL edits a literal before high-order truncation: keep it within the picture
            ndig = sum(1 for t in dst.edit[1].split() if t in ("nine", "z", "star")) + \
                max(0, sum(1 for t in dst.edit[1].split() if t in ("cs", "plus", "minus")) - 1)
            nfrac = 0
            toks = dst.edit[1].split()
            if "dot" in toks:
                nfrac = sum(1 for t in toks[toks.index("dot"):] if t in ("nine", "z", "star"))
            scale = min(scale, nfrac)
            digits = max(1, min(digits, ndig - nfrac + scale))
        v = rng.randint(0, 10 ** digits - 1) * (-1 if rng.random() < 0.4 else 1)
        return [f"MOVE {num_literal_cobol(v, scale)} TO {dst.name}"], \
            {"move": {"src": op_num(v, scale, digits), "dsts": [ref(dst.id)]}}

    def st_move_alnum(self):
        rng = self.rng
        dsts = [f for f in self.fields if f.kind == "alnum" and f is not self.flag]
        if not dsts:
            return self.st_move_num()
        dst = rng.choice(dsts)
        r = rng.random()
        if r < 0.4:
            s = "".join(rng.choice(ALNUM_CHARS) for _ in range(rng.randint(1, 10)))
            return [f"MOVE '{s}' TO {dst.name}"], {"move": {"src": op_str(s), "dsts": [ref(dst.id)]}}
        if r < 0.6:
            fig = rng.choice(["SPACES", "ZEROS", "HIGH-VALUES", "LOW-VALUES"])
            return [f"MOVE {fig} TO {dst.name}"], {"move": {"src": op_fig(fig), "dsts": [ref(dst.id)]}}
        srcs = [f for f in self.fields if f.kind == "alnum" and f is not dst] + \
               [f for f in self.nums() if f.scale == 0]
        if not srcs:
            return self.st_move_num()
        src = rng.choice(srcs)
        if dst.just and src.numeric and src.digits > dst.length:
            return self.st_move_num()
        return [f"MOVE {src.name} TO {dst.name}"], {"move": {"src": op_ref(src.id), "dsts": [ref(dst.id)]}}

    def rand_expr(self, depth):
        rng = self.rng
        if depth == 0 or rng.random() < 0.35:
            if self.nums() and rng.random() < 0.7:
                f = rng.choice(self.nums())
                return f.name, e_ref(f.id)
            digits = rng.randint(1, 4)
            scale = rng.randint(0, min(2, digits))
            v = rng.randint(1, 10 ** digits - 1)
            return num_literal_cobol(v, scale), e_lit(v, scale)
        op = rng.choice(["add", "sub", "mul"])
        a_c, a_j = self.rand_expr(depth - 1)
        b_c, b_j = self.rand_expr(depth - 1)
        sym = {"add": "+", "sub": "-", "mul": "*"}[op]
        return f"({a_c} {sym} {b_c})", e_bin(op, a_j, b_j)

    def size_phrase(self, receivers=()):
        """Optional ON SIZE ERROR phrase: (cobol, onSize json, notOnSize json)."""
        rng = self.rng
        r = rng.random()
        # GnuCOBOL checks SIZE ERROR of COMP items against the binary capacity, IBM TRUNC(STD)
        # against the PICTURE: no SIZE ERROR phrase with COMP receivers
        if TRUNC == "std" and BIN_SIZE_QUIRK and any(f.usage == "binary" for f in receivers):
            return "", None, []
        if r < 0.4:
            (ec, ej), (kc, kj) = self.outcome("E"), self.outcome("K")
            return f"ON SIZE ERROR {ec} NOT ON SIZE ERROR {kc}", ej, kj
        return "", None, []

    def rounded(self):
        rng = self.rng
        r = rng.random()
        if r < 0.4:
            return "", None
        if r < 0.7:
            return " ROUNDED", "NEAREST-AWAY-FROM-ZERO"
        m = rng.choice(MODES)
        return f" ROUNDED MODE {m}", m

    def st_compute(self):
        rng = self.rng
        recs = rng.sample(self.nums(), k=min(len(self.nums()), rng.randint(1, 2)))
        rc = []
        rj = []
        for r in recs:
            c, j = self.rounded()
            rc.append(r.name + c)
            rj.append(rcv(r.id, j))
        e_c, e_j = self.rand_expr(2)
        if rng.random() < 0.3:
            # a top-level division (agrees with the exact quotient on both sides)
            d = rng.choice([f for f in self.nums()] + [None])
            if d is None:
                dv = rng.randint(1, 99)
                d_c, d_j = str(dv), e_lit(dv, 0)
            else:
                d_c, d_j = d.name, e_ref(d.id)
            e_c, e_j = f"{e_c} / {d_c}", e_div(e_j, d_j)
        sp_c, on, non = self.size_phrase(recs)
        if "/" in e_c and BIN_SIZE_QUIRK and any(f.usage == "binary" for f in recs):
            return self.st_move_num()
        if on is None and "/" in e_c:
            # division by zero without SIZE ERROR aborts both sides differently: always trap
            ec, ej = self.outcome("E")
            sp_c, on, non = f"ON SIZE ERROR {ec}", ej, []
        cob = [f"COMPUTE {' '.join(rc)} = {e_c}"] + ([sp_c] if sp_c else []) + ["END-COMPUTE"]
        return cob, {"compute": {"rcv": rj, "e": e_j, "onSize": on, "notOnSize": non}}

    def st_addsub(self):
        rng = self.rng
        nums = self.nums()
        recs = rng.sample(nums, k=min(len(nums), rng.randint(1, 2)))
        rest = [f for f in nums if f not in recs]
        if not rest:
            return self.st_move_num()
        # GnuCOBOL re-reads an operand that is also a receiver after storing it (IBM: the sum
        # is computed once): operands disjoint from receivers
        ops = rng.sample(rest, k=min(len(rest), rng.randint(1, 2)))
        rc, rj = [], []
        for r in recs:
            c, j = self.rounded() if r.usage != "packed" else ("", None)
            rc.append(r.name + c)
            rj.append(rcv(r.id, j))
        sp_c, on, non = self.size_phrase(recs)
        verb = rng.choice(["ADD", "SUBTRACT"])
        prep = "TO" if verb == "ADD" else "FROM"
        cob = [f"{verb} {' '.join(o.name for o in ops)} {prep} {' '.join(rc)}"] + \
            ([sp_c] if sp_c else []) + [f"END-{verb}"]
        opsj = [e_ref(o.id) for o in ops]
        if verb == "ADD":
            j = {"add": {"ops": opsj, "rcv": rj, "giving": False, "onSize": on, "notOnSize": non}}
        else:
            j = {"subtract": {"ops": opsj, "rcv": rj, "giving": None, "onSize": on, "notOnSize": non}}
        return cob, j

    def st_multiply(self):
        rng = self.rng
        nums = self.nums()
        a = rng.choice(nums)
        r = rng.choice(nums)
        c, rj = self.rounded()
        sp_c, on, non = self.size_phrase([r])
        if rng.random() < 0.5:
            g = rng.choice(nums)
            cob = [f"MULTIPLY {a.name} BY {g.name} GIVING {r.name}{c}"] + ([sp_c] if sp_c else []) + ["END-MULTIPLY"]
            return cob, {"multiply": {"a": e_ref(a.id), "rcv": [rcv(r.id, rj)], "giving": e_ref(g.id),
                                      "onSize": on, "notOnSize": non}}
        cob = [f"MULTIPLY {a.name} BY {r.name}{c}"] + ([sp_c] if sp_c else []) + ["END-MULTIPLY"]
        return cob, {"multiply": {"a": e_ref(a.id), "rcv": [rcv(r.id, rj)], "giving": None,
                                  "onSize": on, "notOnSize": non}}

    def st_divide(self):
        rng = self.rng
        nums = self.nums()
        a = rng.choice(nums)
        b = rng.choice(nums)
        q = rng.choice([f for f in nums if not BIN_SIZE_QUIRK or f.usage != "binary"] or [None])
        if q is None:
            return self.st_move_num()
        c, rj = self.rounded()
        (ec, on), (kc, non) = self.outcome("E"), self.outcome("K")
        sp = f"ON SIZE ERROR {ec} NOT ON SIZE ERROR {kc}"
        if rng.random() < 0.3:
            rem = rng.choice([f for f in nums if f is not q and (not BIN_SIZE_QUIRK or f.usage != "binary")]
                             or [None])
            if rem is None:
                return self.st_move_num()
            # no ON SIZE ERROR: GnuCOBOL stores the remainder even after a quotient size error;
            # divisor must not be zero then (abend), so divide by a non-zero literal
            dv = rng.randint(1, 97)
            cob = [f"DIVIDE {a.name} BY {dv} GIVING {q.name}{c} REMAINDER {rem.name}", "END-DIVIDE"]
            return cob, {"divide": {"dividend": e_ref(a.id), "divisor": e_lit(dv, 0), "rcv": [rcv(q.id, rj)],
                                    "giving": True, "remainder": ref(rem.id), "onSize": None, "notOnSize": []}}
        if rng.random() < 0.5:
            cob = [f"DIVIDE {a.name} BY {b.name} GIVING {q.name}{c}", sp, "END-DIVIDE"]
            return cob, {"divide": {"dividend": e_ref(a.id), "divisor": e_ref(b.id), "rcv": [rcv(q.id, rj)],
                                    "giving": True, "remainder": None, "onSize": on, "notOnSize": non}}
        cob = [f"DIVIDE {b.name} INTO {q.name}{c}", sp, "END-DIVIDE"]
        return cob, {"divide": {"dividend": e_lit(0, 0), "divisor": e_ref(b.id), "rcv": [rcv(q.id, rj)],
                                "giving": False, "remainder": None, "onSize": on, "notOnSize": non}}

    def st_if(self):
        rng = self.rng
        nums = self.nums()
        a = rng.choice(nums)
        b = rng.choice(nums)
        op = rng.choice(["=", "<", ">", "<=", ">=", "<>"])
        (yc, yj), (nc, nj) = self.outcome("Y"), self.outcome("N")
        cob = [f"IF {a.name} {op} {b.name}", yc, "ELSE", nc, "END-IF"]
        j = {"ite": {"c": {"rel": {"op": op, "a": op_ref(a.id), "b": op_ref(b.id)}}, "t": yj, "e": nj}}
        return cob, j

    def st_if_alnum(self):
        rng = self.rng
        als = [f for f in self.fields if f.kind == "alnum"]
        a = rng.choice(als)
        b = rng.choice(als)
        op = rng.choice(["=", "<", ">", "<>"])
        (yc, yj), (nc, nj) = self.outcome("Y"), self.outcome("N")
        cob = [f"IF {a.name} {op} {b.name}", yc, "ELSE", nc, "END-IF"]
        j = {"ite": {"c": {"rel": {"op": op, "a": op_ref(a.id), "b": op_ref(b.id)}}, "t": yj, "e": nj}}
        return cob, j

    def statements(self, n):
        rng = self.rng
        table = {"movenum": self.st_move_num, "movealnum": self.st_move_alnum,
                 "compute": self.st_compute, "addsub": self.st_addsub,
                 "multiply": self.st_multiply, "divide": self.st_divide,
                 "if": self.st_if, "ifalnum": self.st_if_alnum}
        kinds = [k for k in self.kinds if k in table]
        out = []
        self.trace.length = n
        for _ in range(n):
            if not self.nums():
                break
            self.cur = len(out) + 1
            out.append(table[rng.choice(kinds)]())
        self.fields.append(self.trace)
        return out


def render(gen, stmts, name):
    fields = gen.fields
    rng = gen.rng
    # values
    values = {}
    for f in fields:
        if f.kind == "num":
            v, s = rand_value(rng, f)
            values[f.id] = ("num", v, s)
        elif f is gen.flag:
            values[f.id] = ("str", "N")
        elif f is gen.trace:
            values[f.id] = ("str", "." * f.length)   # a statement without outcome keeps '.'
        elif f.kind == "alnum":
            values[f.id] = ("str", "".join(rng.choice(ALNUM_CHARS) for _ in range(f.length)))
        else:
            values[f.id] = ("zero",)
    # COBOL
    lines = ["IDENTIFICATION DIVISION.", f"PROGRAM-ID. {name}.", "DATA DIVISION.",
             "WORKING-STORAGE SECTION.", "01 R."]
    for f in fields:
        val = values[f.id]
        if val[0] == "num":
            vtxt = num_literal_cobol(val[1], val[2])
        elif val[0] == "str":
            vtxt = "'" + val[1] + "'"
        else:
            vtxt = "ZERO"
        cl = f.clauses()
        lines.append(f"   05 {f.name} PIC {f.pic_cobol()}" + (f" {cl}" if cl else "") + f" VALUE {vtxt}.")
    total = record_size(fields)
    lines += ["01 RX REDEFINES R.", f"   05 BYTE PIC X OCCURS {total}.", "01 IDX PIC 9(4) COMP.",
              "PROCEDURE DIVISION.", "MAIN-PARA."]
    for cob, _ in stmts:
        for ln in cob:
            lines.append("    " + ln)
    lines += [f"    PERFORM VARYING IDX FROM 1 BY 1 UNTIL IDX > {total}",
              "       DISPLAY FUNCTION ORD(BYTE(IDX)) ' ' WITH NO ADVANCING",
              "    END-PERFORM", "    DISPLAY ' '", "    STOP RUN."]
    cobol = "\n".join(wrap_fixed(ln) for ln in lines) + "\n"
    # JSON
    children = []
    for f in fields:
        val = values[f.id]
        if val[0] == "num":
            vj = {"num": {"v": val[1], "scale": val[2]}}
        elif val[0] == "str":
            vj = {"alnum": {"bs": [ord(c) for c in val[1]]}}
        else:
            vj = {"fig": {"f": "zero"}}
        children.append({"id": f.id, "level": 5, "name": f.name, "pic": f.pic_json(),
                         "usage": f.usage if f.kind == "num" else "display", "value": vj,
                         "signLead": f.sign_lead, "signSep": f.sign_sep, "just": f.just})
    data = [item_json({"id": 1, "level": 1, "name": "R", "pic": None, "children": children})]
    prog = {"name": name, "config": dict(CONFIG, trunc=TRUNC), "dialect": {"divExtraForRounded": True}, "data": data,
            "paras": [{"name": "MAIN-PARA", "sect": None,
                       "sentences": [[j for _, j in stmts] + ["stopRun"]]}],
            "isMain": True}
    return cobol, prog, total


def record_size(fields):
    n = 0
    for f in fields:
        if f.kind == "alnum":
            n += f.length
        elif f.kind == "edit":
            n += sum(2 if t in ("cr", "db") else (0 if t in ("v", "p") else 1) for t in f.edit[1].split())
        elif f.usage == "display":
            n += f.digits + (1 if f.signed and f.sign_sep else 0)
        elif f.usage == "packed":
            n += f.digits // 2 + 1
        else:
            n += 2 if f.digits <= 4 else (4 if f.digits <= 9 else 8)
    return n


def wrap_fixed(line):
    """Fixed-format line(s): code in columns 8-72, continuation lines in Area B."""
    prefix = "       "
    out = []
    while len(prefix) + len(line) > 72:
        width = 72 - len(prefix)
        inq = False
        best = -1
        for i, ch in enumerate(line[:width]):
            if ch == "'":
                inq = not inq
            if ch == " " and not inq:
                best = i
        if best <= 0:
            raise ValueError("cannot wrap: " + line)
        out.append(prefix + line[:best])
        line = line[best:].lstrip()
        prefix = "           "
    out.append(prefix + line)
    return "\n".join(out)


def run_one(idx, rng, outdir, kinds, keep):
    gen = Gen(rng, kinds)
    gen.make_fields()
    stmts = gen.statements(rng.randint(3, 10))
    name = f"T{idx:05d}"
    cobol, prog, total = render(gen, stmts, name)
    base = os.path.join(outdir, name)
    with open(base + ".cob", "w") as fh:
        fh.write(cobol)
    with open(base + ".json", "w") as fh:
        json.dump(prog, fh)
    c = subprocess.run([COBC, "-x"] + COBC_FLAGS[TRUNC] + ["-o", base, base + ".cob"],
                       capture_output=True, text=True)
    if c.returncode != 0:
        return ("cobc-error", c.stderr[:2000])
    env = dict(os.environ, LD_LIBRARY_PATH=LIBDIR)
    r = subprocess.run([base], capture_output=True, text=True, env=env, timeout=20)
    if r.returncode != 0:
        return ("gnucobol-abend", r.stdout[-500:] + r.stderr[-500:])
    try:
        gbytes = [int(x) - 1 for x in r.stdout.split()]
    except ValueError:
        return ("gnucobol-output", r.stdout[:500])
    l = subprocess.run([COBOLRUN, base + ".json"], capture_output=True, text=True, timeout=60)
    if l.returncode != 0:
        return ("cobolrun-error", l.stderr[:2000])
    res = json.loads(l.stdout)
    lbytes = res["mem"][:total]
    if not res["signal"].startswith("stop:"):
        return ("lean-signal", res["signal"])
    if gbytes != lbytes:
        diffs = field_diffs(gen.fields, gbytes, lbytes)
        if diffs:
            return ("mismatch", {"fields": diffs})
        # every field decodes to the same value: classify the byte differences
        classes = byte_classes(gen.fields, gbytes, lbytes)
        if any(c == "bytes" for c, _ in classes):
            return ("mismatch-bytes", {"fields": [d for c, d in classes]})
        status = "ok-packed-fc" if any(c == "packed-fc" for c, _ in classes) else "ok-negzero"
    else:
        status = "ok"
    if FRONTEND:
        fe = run_frontend(base, total)
        if fe[0] != "ok":
            return fe
        if fe[1] != lbytes:
            return ("frontend-mismatch", {"fields": field_diffs(gen.fields, fe[1], lbytes)})
    if not keep:
        for ext in ("", ".cob", ".json", ".fe.json", ".c", ".c.h", ".c.l.h"):
            p = base + ext
            if os.path.exists(p):
                os.remove(p)
    return (status, None)


def run_frontend(base, total):
    """Extract the IR from the COBOL source with the front end and run it.  The dump epilogue
    (`DISPLAY FUNCTION ORD(...) WITH NO ADVANCING`) is outside the IR: execution faults there,
    after the statements under test, with storage final."""
    fe = subprocess.run([sys.executable, "-I", COBOLFE, base + ".cob", "--profile", "gnucobol",
                         "--trunc", TRUNC, "--div-scale", "30", "--main", "-o", base + ".fe.json"],
                        capture_output=True, text=True)
    if fe.returncode != 0:
        return ("frontend-error", fe.stderr[:2000])
    unsup = [ln for ln in fe.stderr.splitlines() if "unsupported" in ln]
    if any("DISPLAY" not in ln for ln in unsup):
        return ("frontend-unsupported", "\n".join(unsup)[:2000])
    l = subprocess.run([COBOLRUN, base + ".fe.json"], capture_output=True, text=True, timeout=60)
    if l.returncode != 0:
        return ("frontend-cobolrun-error", l.stderr[:2000])
    res = json.loads(l.stdout)
    if not ("unsupported" in res["signal"] and "DISPLAY" in res["signal"]):
        return ("frontend-signal", res["signal"])
    return ("ok", res["mem"][:total])


def field_len(f):
    return record_size([f])


def decode_field(f, bs):
    """Value of a numeric field (ASCII zoned / packed / binary), else the raw bytes."""
    if f.kind != "num":
        return bytes(bs)
    if f.usage == "packed":
        nib = []
        for b in bs:
            nib += [b >> 4, b & 15]
        digits, sign = nib[:-1], nib[-1]
        v = 0
        for d in digits:
            v = v * 10 + d
        return -v if sign in (0xB, 0xD) else v
    if f.usage in ("binary", "comp5"):
        data = list(bs) if f.usage == "binary" else list(reversed(bs))
        v = 0
        for b in data:
            v = v * 256 + b
        if f.signed and v >= 2 ** (8 * len(bs) - 1):
            v -= 2 ** (8 * len(bs))
        return v
    # zoned (ASCII, 0x70 negative overpunch)
    chars = list(bs)
    neg = False
    if f.sign_sep:
        sc = chars.pop(0) if f.sign_lead else chars.pop()
        neg = sc == 0x2D
    elif f.signed:
        i = 0 if f.sign_lead else len(chars) - 1
        if chars[i] >= 0x70:
            neg = True
            chars[i] -= 0x40
    v = 0
    for c in chars:
        v = v * 10 + (c - 0x30)
    return -v if neg else v


def field_diffs(fields, g, l):
    out = []
    off = 0
    for f in fields:
        n = field_len(f)
        gv, lv = decode_field(f, g[off:off + n]), decode_field(f, l[off:off + n])
        if gv != lv:
            out.append({"field": f.name, "pic": f.pic_cobol(), "usage": f.usage if f.numeric else f.kind,
                        "gnucobol": gv if isinstance(gv, int) else list(gv),
                        "lean": lv if isinstance(lv, int) else list(lv)})
        off += n
    return out


def byte_class(f, gb, lb):
    """Why the bytes `gb` (GnuCOBOL) and `lb` (model) of field `f` differ although they decode to
    the same value: "negzero" (a signed 0 with the opposite sign: packed D vs C, separate '-' vs
    '+', overpunch 'p' vs '0'), "packed-fc" (a signed packed field, sign nibble F vs C, same
    value), else "bytes"."""
    n = len(gb)
    diff = [i for i in range(n) if gb[i] != lb[i]]
    if f.kind != "num" or not f.signed:
        return "bytes"
    zero = decode_field(f, gb) == 0
    if f.usage == "packed":
        if diff == [n - 1] and gb[-1] >> 4 == lb[-1] >> 4:
            signs = {gb[-1] & 15, lb[-1] & 15}
            if signs == {0xC, 0xF}:
                return "packed-fc"
            if signs == {0xC, 0xD} and zero:
                return "negzero"
        return "bytes"
    if f.usage == "display" and zero:
        pos = 0 if f.sign_lead else n - 1
        pair = {0x2B, 0x2D} if f.sign_sep else {0x30, 0x70}
        if diff == [pos] and {gb[pos], lb[pos]} == pair:
            return "negzero"
    return "bytes"


def byte_classes(fields, g, l):
    """[(class, details)] for every field whose bytes differ (see `byte_class`)."""
    out = []
    off = 0
    for f in fields:
        n = field_len(f)
        gb, lb = g[off:off + n], l[off:off + n]
        if gb != lb:
            c = byte_class(f, gb, lb)
            out.append((c, {"field": f.name, "pic": f.pic_cobol(), "usage": f.usage if f.numeric else f.kind,
                            "class": c, "gnucobol": bytes(gb).hex(), "lean": bytes(lb).hex()}))
        off += n
    return out


def bump(tally, out, case, status):
    """Count one case and append it to OUT/results.jsonl (one JSON object per case)."""
    tally[status] = tally.get(status, 0) + 1
    with open(os.path.join(out, "results.jsonl"), "a") as fh:
        fh.write(json.dumps({"case": case, "status": status}) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=50)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--out", default=os.path.join(ROOT, "tools", "difftest", "out"))
    ap.add_argument("--kinds", default="movenum,movealnum,compute,addsub,multiply,divide,if,ifalnum")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--trunc", default="std", choices=["std", "bin"])
    ap.add_argument("--bin-size-quirk", action="store_true",
                    help="avoid SIZE ERROR on COMP receivers (GnuCOBOL capacity check)")
    ap.add_argument("--frontend", action="store_true",
                    help="also run the IR the COBOL front end (tools/cobolfe) extracts from the "
                         "same COBOL source; it must agree with GnuCOBOL and with the generated IR")
    args = ap.parse_args()
    global TRUNC, BIN_SIZE_QUIRK, FRONTEND
    TRUNC = args.trunc
    BIN_SIZE_QUIRK = args.bin_size_quirk
    FRONTEND = args.frontend
    os.makedirs(args.out, exist_ok=True)
    open(os.path.join(args.out, "results.jsonl"), "w").close()
    rng = random.Random(args.seed)
    kinds = args.kinds.split(",")
    tally = {}
    fails = []
    for i in range(args.n):
        status, info = run_one(i, random.Random(rng.random()), args.out, kinds, args.keep)
        bump(tally, args.out, i, status)
        if status != "ok":
            fails.append((i, status, info))
    print(json.dumps({"tally": tally}))
    for i, status, info in fails[:20]:
        print(f"--- T{i:05d} {status}")
        print(json.dumps(info)[:1500] if not isinstance(info, str) else info[:1500])
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())

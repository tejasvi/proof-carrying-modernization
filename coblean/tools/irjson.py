"""Helpers to write surface-IR JSON (the extraction contract, `Cobol/Frontend/Surface.lean`).

The Lean side derives its JSON decoders, which require every field to be present; these
helpers fill in the defaults.  An extractor emits the same shapes.
"""

IBM = {"charset": "ebcdic", "zonedSign": "ebcdic", "trunc": "std", "numprocPfd": False,
       "binaryLE": False, "comp5LE": False, "binary1Byte": False, "sizeErrorTruncates": True}
GNUCOBOL = dict(IBM, charset="ascii", zonedSign="asciiMF", comp5LE=True)


# ---------------------------------------------------------------- data division
def item(id, level, name, pic=None, usage="display", occurs=1, redefines=None, value=None,
         just=False, signSep=False, signLead=False, bwz=False, sync=False, conds=(), children=()):
    return {"id": id, "level": level, "name": name, "pic": pic, "usage": usage, "occurs": occurs,
            "redefines": redefines, "value": value, "just": just, "signSep": signSep,
            "signLead": signLead, "bwz": bwz, "sync": sync,
            "conds": [[cid, [cname, vals]] for (cid, cname, vals) in conds],
            "children": list(children)}


def pic_x(n):
    return {"alnum": {"len": n}}


def pic_9(digits, scale=0, signed=False):
    return {"num": {"digits": digits, "scale": scale, "signed": signed}}


def val_num(v, scale=0):
    return {"num": {"v": v, "scale": scale}}


def val_bytes(bs):
    return {"alnum": {"bs": list(bs)}}


def val_fig(f):
    return {"fig": {"f": f}}          # "zero" | "space" | "high" | "low" | "quote"


def cond_val(lo, hi=None):
    return {"lo": lo, "hi": hi}


# ---------------------------------------------------------------- references and operands
def ref(item_id, subs=(), start=None, length=None):
    return {"item": item_id, "subs": list(subs), "refStart": start, "refLen": length}


def sub_lit(n):
    return {"lit": {"n": n}}


def sub_item(i, k=0):
    return {"item": {"id": i, "k": k}}


def sub_idx(i, k=0):
    return {"idx": {"id": i, "k": k}}


def o_ref(item_id, **kw):
    return {"ref": {"r": ref(item_id, **kw)}}


def o_num(v, scale=0, digits=0):
    return {"lit": {"l": {"num": {"v": v, "scale": scale, "digits": digits}}}}


def o_str(s):
    return {"lit": {"l": {"str": {"s": s}}}}


def o_fig(name):
    return {"lit": {"l": {"fig": {"name": name}}}}


# ---------------------------------------------------------------- expressions
def e_lit(v, scale=0):
    return {"lit": {"v": v, "scale": scale}}


def e_ref(item_id, **kw):
    return {"ref": {"r": ref(item_id, **kw)}}


def e_add(a, b):
    return {"add": {"a": a, "b": b}}


def e_sub(a, b):
    return {"sub": {"a": a, "b": b}}


def e_mul(a, b):
    return {"mul": {"a": a, "b": b}}


def e_div(a, b, scale=None):
    return {"div": {"a": a, "b": b, "scale": scale}}


# ---------------------------------------------------------------- conditions
def c_rel(op, a, b):
    return {"rel": {"op": op, "a": a, "b": b}}


def c_and(a, b):
    return {"and": {"a": a, "b": b}}


def c_or(a, b):
    return {"or": {"a": a, "b": b}}


def c_not(a):
    return {"not": {"c": a}}


def c_88(cid, subs=()):
    return {"cond88": {"id": cid, "subs": list(subs)}}


# ---------------------------------------------------------------- statements
def rcv(item_id, rounded=None, **kw):
    return {"ref": ref(item_id, **kw), "rounded": rounded}


def move(src, *dsts):
    return {"move": {"src": src, "dsts": list(dsts)}}


def compute(rcvs, e, on_size=None, not_on_size=()):
    return {"compute": {"rcv": list(rcvs), "e": e, "onSize": on_size, "notOnSize": list(not_on_size)}}


def add(ops, rcvs, giving=False, on_size=None, not_on_size=()):
    return {"add": {"ops": list(ops), "rcv": list(rcvs), "giving": giving, "onSize": on_size,
                    "notOnSize": list(not_on_size)}}


def ite(c, t, e=()):
    return {"ite": {"c": c, "t": list(t), "e": list(e)}}


def perform(first, last=None, loop="once"):
    return {"perform": {"first": first, "last": last, "loop": loop}}


def loop_until(c, test_after=False):
    return {"until": {"testAfter": test_after, "c": c}}


def go_to(target):
    return {"goTo": {"target": target}}


def set_true(cid, subs=()):
    return {"setTrue": {"id": cid, "subs": list(subs)}}


def read(file, rec, into=None, at_end=(), not_at_end=()):
    return {"read": {"file": file, "rec": rec, "into": into, "atEnd": list(at_end),
                     "notAtEnd": list(not_at_end)}}


def write(file, rec):
    return {"write": {"file": file, "rec": rec}}


CONT = "cont"
GOBACK = "goback"
STOP_RUN = "stopRun"


def para(name, *sentences, sect=None):
    return {"name": name, "sect": sect, "sentences": [list(s) for s in sentences]}


def program(name, data, paras, config=IBM, is_main=True, div_extra_for_rounded=True):
    return {"name": name, "config": config, "dialect": {"divExtraForRounded": div_extra_for_rounded},
            "data": data, "paras": paras, "isMain": is_main}

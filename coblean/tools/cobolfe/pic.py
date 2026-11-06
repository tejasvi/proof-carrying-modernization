"""PICTURE strings: expansion and classification into the surface `Pic` (Layout.lean)."""


class PicError(Exception):
    pass


EDIT_SYM = {"9": "nine", "Z": "z", "*": "star", "$": "cs", "+": "plus", "-": "minus",
            ".": "dot", ",": "comma", "B": "b", "0": "zero", "/": "slash", "CR": "cr",
            "DB": "db", "V": "v", "P": "p"}


def symbols(pic):
    """`S9(3)V99CR` -> ['S', '9', '9', '9', 'V', '9', '9', 'CR'] (repetitions expanded)."""
    out = []
    s = pic.upper()
    i = 0
    while i < len(s):
        if s.startswith("CR", i) or s.startswith("DB", i):
            out.append(s[i:i + 2])
            i += 2
            continue
        c = s[i]
        if c == "(":
            j = s.find(")", i)
            if j < 0 or not out:
                raise PicError(f"bad repetition in PICTURE {pic}")
            try:
                n = int(s[i + 1:j])
            except ValueError:
                raise PicError(f"bad repetition count in PICTURE {pic}")
            if n < 1:
                raise PicError(f"bad repetition count in PICTURE {pic}")
            out.extend([out[-1]] * (n - 1))
            i = j + 1
            continue
        out.append(c)
        i += 1
    return out


def ae_pattern(pic):
    """An alphanumeric-edited PICTURE (A, X, 9 with at least one A or X and one of the simple
    insertion symbols B, 0, /), position by position: "d" for a data position, else the inserted
    character. None for any other PICTURE."""
    syms = symbols(pic)
    kinds = set(syms)
    if not (kinds & {"X", "A"}) or not (kinds & {"B", "0", "/"}) or not kinds <= {"X", "A", "9", "B", "0", "/"}:
        return None
    return ["d" if s in ("X", "A", "9") else {"B": " ", "0": "0", "/": "/"}[s] for s in syms]


def classify(pic):
    """Surface `Pic` JSON of a PICTURE string, and its category
    (`alnum`, `num`, `numEdited`, or `alnumEdited`: stored as an alphanumeric item, the parser
    makes MOVEs into it insert the editing characters)."""
    syms = symbols(pic)
    if not syms:
        raise PicError("empty PICTURE")
    kinds = set(syms)
    if kinds <= {"X", "A", "9"} and kinds & {"X", "A"}:
        return {"alnum": {"len": len(syms)}}, "alnum"
    if kinds <= {"S", "9", "V", "P"}:
        signed = syms[0] == "S"
        if "S" in syms[1:]:
            raise PicError(f"S must come first in PICTURE {pic}")
        body = syms[1:] if signed else syms
        if body.count("V") > 1:
            raise PicError(f"more than one V in PICTURE {pic}")
        digits = body.count("9")
        if digits == 0:
            raise PicError(f"numeric PICTURE without digits: {pic}")
        if "V" in body:
            point = body.index("V")
        elif body[0] == "P":
            point = 0                       # PPP999: all positions are decimal places
        else:
            point = len(body)               # 999PPP: scaling positions on the right
        left = [c for c in body[:point] if c != "V"]
        right = [c for c in body[point:] if c != "V"]
        scale = len(right) - left.count("P")
        if digits > 31:
            raise PicError(f"more than 31 digits in PICTURE {pic}")
        return {"num": {"digits": digits, "scale": scale, "signed": signed}}, "num"
    if kinds & {"X", "A"}:
        if ae_pattern(pic) is not None:
            return {"alnum": {"len": len(syms)}}, "alnumEdited"
        raise PicError(f"PICTURE {pic} mixes alphanumeric and numeric-editing symbols")
    try:
        es = [EDIT_SYM[c] for c in syms]
    except KeyError as e:
        raise PicError(f"unsupported symbol {e.args[0]!r} in PICTURE {pic}")
    return {"numEdited": {"pic": es}}, "numEdited"

"""Differences between the COBOL outcome and a translation's outcome, and their kinds.

`diff(expected, actual)` lists the differing parts of two canonical outcomes (INTERFACES.md): the end, each display
line, each written or rewritten record field, the return code. `kind(d, case, expected)` names the kind of one
difference mechanically, from the values alone:

* `sign`: the same magnitude with another sign, or a zoned overpunch character against a sign character;
* `truncation`: one number is the other with high-order digits lost (or one text a prefix of the other);
* `rounding`: numbers differing by at most one unit in the last place;
* `arithmetic`: other numeric differences;
* `padding`: texts equal up to trailing spaces or leading zeros;
* `numeric formatting`: a display line whose digit runs differ in layout (decimal point, zero suppression, sign
  position) but not in digits;
* `uninitialized storage`: the case is init-dependent and the COBOL program's own outcomes differ in this part;
* `file status`: a different end or output count after the COBOL program reported a file status or INVALID KEY;
* `end of file`: the outputs differ only after the last record of the driving file was read (the COBOL program
  processes the last record again, or stops earlier);
* `record order`: the same lines or records in another order (e.g. sorted by Unicode instead of EBCDIC
  collation);
* `control flow`: missing or extra outputs, another end, otherwise;
* `text`: other differences in a text field or display line.

The raw differences are kept with every kind, so a table can be re-labelled by hand.
"""
from __future__ import annotations

import json
import re


def _align(a: list, b: list):
    """Pairs (i, j) of an alignment of two sequences (difflib on their JSON): equal runs are skipped, a replaced
    run of the same length is paired element by element, the rest are (i, None) / (None, j). So one missing line or
    record is one difference, not a shift of everything after it."""
    import difflib
    ka = [json.dumps(x, sort_keys=True, ensure_ascii=False) for x in a]
    kb = [json.dumps(x, sort_keys=True, ensure_ascii=False) for x in b]
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, ka, kb, autojunk=False).get_opcodes():
        if tag == "equal":
            continue
        if tag == "replace" and i2 - i1 == j2 - j1:
            yield from zip(range(i1, i2), range(j1, j2))
            continue
        n = min(i2 - i1, j2 - j1) if tag == "replace" else 0
        yield from zip(range(i1, i1 + n), range(j1, j1 + n))
        yield from ((i, None) for i in range(i1 + n, i2))
        yield from ((None, j) for j in range(j1 + n, j2))


def diff(exp: dict, act: dict, limit: int = 40) -> list[dict]:
    out: list[dict] = []
    if exp.get("end") != act.get("end"):
        out.append({"where": "end", "expected": exp.get("end"), "actual": act.get("end")})
    if exp.get("return_code") != act.get("return_code"):
        out.append({"where": "return_code", "expected": exp.get("return_code"), "actual": act.get("return_code")})
    de, da = exp.get("displays", []) or [], act.get("displays", []) or []
    for i, j in _align(de, da):
        out.append({"where": "display", "index": i if i is not None else j,
                    "expected": de[i] if i is not None else None, "actual": da[j] if j is not None else None})
        if len(out) >= limit:
            return out
    for stream in ("writes", "rewrites", "files"):
        fe, fa = exp.get(stream, {}) or {}, act.get(stream, {}) or {}
        for fd in sorted(set(fe) | set(fa)):
            re_, ra = fe.get(fd) or [], fa.get(fd) or []
            for i, j in _align(re_, ra):
                x = re_[i] if i is not None else None
                y = ra[j] if j is not None else None
                idx = i if i is not None else j
                if x is None or y is None or not isinstance(x, dict) or not isinstance(y, dict):
                    out.append({"where": stream, "file": fd, "index": idx, "expected": x, "actual": y})
                    continue
                for k in x:
                    if x[k] != y.get(k):
                        out.append({"where": stream, "file": fd, "index": idx, "field": k,
                                    "expected": x[k], "actual": y.get(k)})
                if len(out) >= limit:
                    return out
    return out


_OVERPUNCH = set("{}ABCDEFGHIJKLMNOPQR")


def _num_kind(a: int, b: int) -> str:
    if a == -b:
        return "sign"
    sa, sb = str(abs(a)), str(abs(b))
    if (len(sa) < len(sb) and sb.endswith(sa)) or (len(sb) < len(sa) and sa.endswith(sb)):
        return "truncation"
    if abs(a - b) <= 1:
        return "rounding"
    return "arithmetic"


def _text_kind(a: str, b: str) -> str:
    if a.rstrip() == b.rstrip():
        return "padding"
    if a.lstrip("0 ") == b.lstrip("0 ") and a.strip() and b.strip():
        return "padding"
    if a.startswith(b.rstrip()) or b.startswith(a.rstrip()):
        return "truncation"
    return "text"


def _display_kind(a: str, b: str) -> str:
    if a.rstrip() == b.rstrip():
        return "padding"
    # first differing column and the tokens around it
    i = next((k for k, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
    seg_a, seg_b = a[i:i + 1], b[i:i + 1]
    if (seg_a in _OVERPUNCH and (seg_b.isdigit() or seg_b in "+-")) or (seg_b in _OVERPUNCH and (seg_a.isdigit() or seg_a in "+-")):
        return "sign"
    if "-" in a[max(0, i - 2):i + 2] or "-" in b[max(0, i - 2):i + 2]:
        return "sign"
    da, db = re.sub(r"\D", "", a), re.sub(r"\D", "", b)
    if da == db:
        return "numeric formatting"
    if da.lstrip("0") == db.lstrip("0"):
        return "padding"
    na, nb = re.findall(r"\d+", a[max(0, i - 20):]), re.findall(r"\d+", b[max(0, i - 20):])
    if na and nb:
        x, y = na[0], nb[0]
        if (len(x) != len(y)) and (x.endswith(y) or y.endswith(x)):
            return "truncation"
        if len(x) == len(y) and x[:-1] == y[:-1]:
            return "rounding"
    return "text"


def _cobol_varies(d: dict, exp: dict) -> bool:
    """True if the COBOL program's own outcomes (on other initial storages) differ in this part."""
    for alt in exp.get("init_alternatives", []):
        for d2 in diff(exp, alt, limit=200):
            if d2["where"] == d["where"] and d2.get("index") == d.get("index") and d2.get("field") == d.get("field") \
                    and d2.get("file") == d.get("file"):
                return True
    return False


def _file_status_context(exp: dict) -> bool:
    return any(re.search(r"STATUS|INVALID|NOT FOUND", x) for x in exp.get("displays", [])[-6:])


def kind(d: dict, case: dict, exp: dict) -> str:
    if exp.get("init_dependent") and _cobol_varies(d, exp):
        return "uninitialized storage"
    w = d["where"]
    if w == "end":
        return "file status" if _file_status_context(exp) else "control flow"
    if w == "return_code":
        return "control flow"
    a, b = d.get("expected"), d.get("actual")
    if a is None or b is None:
        # an output the COBOL program repeats (the last record processed again after end of file), or one the
        # translation repeats
        if w == "display" and (a if a is not None else b) in (exp.get("displays", [])[:d["index"]] if a is not None
                                                              else []):
            return "end of file"
        if w in ("writes", "rewrites", "files") and a is not None and \
                a in (exp.get(w, {}).get(d["file"], [])[:d["index"]]):
            return "end of file"
        if w == "display" and _file_status_context(exp):
            return "file status"
        return "control flow"
    if w == "display":
        return _display_kind(a, b)
    if isinstance(a, int) and isinstance(b, int):
        return _num_kind(a, b)
    if isinstance(a, str) and isinstance(b, str):
        return _text_kind(a, b)
    return "text"


def location(d: dict) -> str:
    """Where a difference is, independent of the case: the stream and field, or the display line's template."""
    if d["where"] == "display":
        t = d.get("expected") or d.get("actual") or ""
        return "display:" + re.sub(r"\d", "9", t.strip())[:40]
    if d["where"] in ("writes", "rewrites", "files"):
        return f"{d['where']}:{d['file']}:{d.get('field', '<record>')}"
    return d["where"]


def _same_multiset(a: list, b: list) -> bool:
    key = lambda x: json.dumps(x, sort_keys=True, ensure_ascii=False)
    return a != b and sorted(map(key, a)) == sorted(map(key, b))


def _reordered(d: dict, exp: dict, act: dict) -> bool:
    """The stream holds the same lines/records in another order (e.g. records sorted by a different collating
    sequence: EBCDIC orders letters before digits, Unicode the other way round)."""
    w = d["where"]
    if w == "display":
        return _same_multiset(exp.get("displays", []), act.get("displays", []))
    if w in ("writes", "rewrites", "files"):
        return _same_multiset((exp.get(w) or {}).get(d["file"]) or [], (act.get(w) or {}).get(d["file"]) or [])
    return False


def location_class(loc: str) -> str:
    """The unit discrepancies are counted in: one per kind and output stream (display lines together; records per
    file and field). A defect that garbles many display lines counts once."""
    if loc.startswith("display:"):
        return "display"
    return loc


def classify(case: dict, exp: dict, act: dict) -> list[dict]:
    """The differences of one case with their kinds and locations (first per location)."""
    out, seen = [], set()
    for d in diff(exp, act):
        loc = location(d)
        if loc in seen:
            continue
        seen.add(loc)
        k = "record order" if _reordered(d, exp, act) else kind(d, case, exp)
        out.append(dict(d, kind=k, location=loc))
    return out

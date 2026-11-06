"""COPY expansion on token streams; programs with REPLACE, or COPY with REPLACING, OF or IN, go to
textmanip.py (text words, IBM's rules)."""
import os

import lexer
import source


class CopyError(Exception):
    pass


EXTS = ["", ".cpy", ".CPY", ".cbl", ".CBL", ".cob", ".COB", ".copy", ".COPY"]


def find_copybook(name, dirs):
    for d in dirs:
        for cand in (name, name.upper(), name.lower()):
            for e in EXTS:
                p = os.path.join(d, cand + e)
                if os.path.isfile(p):
                    return p
    return None


def _operand(toks, j):
    """A REPLACING operand: `==pseudo text==` (token list) or a single token."""
    t = toks[j]
    if t.kind == "PSEUDO":
        k = j + 1
        while k < len(toks) and toks[k].kind != "PSEUDO":
            k += 1
        if k >= len(toks):
            raise CopyError(f"{t.where()}: unterminated pseudo-text")
        return toks[j + 1:k], k + 1
    return [t], j + 1


def _same(a, b):
    return a.kind == b.kind and a.val == b.val


def _replace(toks, pairs):
    if not pairs:
        return toks
    out = []
    i = 0
    while i < len(toks):
        for pat, rep in pairs:
            if pat and i + len(pat) <= len(toks) and all(_same(p, toks[i + k]) for k, p in enumerate(pat)):
                for r in rep:
                    out.append(lexer.Tok(r.kind, r.val, toks[i].file, toks[i].line, toks[i].col))
                i += len(pat)
                break
        else:
            out.append(toks[i])
            i += 1
    return out


def text_forms(toks, dirs, fmt="fixed", depth=0):
    """1 when the program text, read as expand() reads it (copybooks depth first), holds a REPLACE
    statement, or a COPY statement with OF, IN or REPLACING, before anything that expand() rejects
    (expand() then leaves the program to textmanip.py); -1 when expand() rejects something first;
    else 0."""
    if depth > 20:
        return -1
    i = 0
    while i < len(toks):
        t = toks[i]
        if t.is_word("REPLACE"):
            return 1
        if not t.is_word("COPY"):
            i += 1
            continue
        if i + 1 >= len(toks) or toks[i + 1].kind not in ("WORD", "STR"):
            return -1
        j = i + 2
        if j < len(toks) and toks[j].is_word("OF", "IN", "REPLACING"):
            return 1
        if j < len(toks) and toks[j].is_word("SUPPRESS"):
            j += 1
        if j < len(toks) and toks[j].is_word("REPLACING"):
            return 1
        if j >= len(toks) or toks[j].kind != "PERIOD":
            return -1
        path = find_copybook(toks[i + 1].val, dirs)
        if path is None:
            return -1
        try:
            with open(path, encoding="latin-1") as fh:
                ctoks = lexer.tokenize(source.read_lines(fh.read(), path, fmt))
        except (OSError, lexer.LexError, source.SourceError):
            return -1
        r = text_forms(ctoks, dirs, fmt, depth + 1)
        if r:
            return r
        i = j + 1
    return 0


def expand(toks, dirs, fmt="fixed", depth=0, used=None):
    """Replace every `COPY name [REPLACING a BY b ...].` by the copybook's tokens (`OF lib` /
    `IN lib` is rejected: the copybook is looked up in `dirs`, not in a library). A program for
    which text_forms() is 1 is read again on text words instead (textmanip.py: REPLACE, and COPY
    with REPLACING, OF or IN, as IBM processes them), so the REPLACING and OF / IN branches below
    are not reached from a call at depth 0."""
    if depth == 0 and toks and text_forms(toks, dirs, fmt) == 1:
        import textmanip
        return textmanip.expand_file(toks[0].file, dirs, fmt, used)
    if depth > 20:
        raise CopyError("COPY nesting too deep")
    if used is None:
        used = []
    out = []
    i = 0
    while i < len(toks):
        t = toks[i]
        if not t.is_word("COPY"):
            out.append(t)
            i += 1
            continue
        if i + 1 >= len(toks) or toks[i + 1].kind not in ("WORD", "STR"):
            raise CopyError(f"{t.where()}: COPY without a copybook name")
        name = toks[i + 1].val
        j = i + 2
        if j < len(toks) and toks[j].is_word("OF", "IN"):
            # copybooks come from the -I directories, so a library name cannot be honoured
            lib = toks[j + 1].val if j + 1 < len(toks) else ""
            raise CopyError(f"{toks[j].where()}: COPY {name} {toks[j].val} {lib}: library names are not supported")
        if j < len(toks) and toks[j].is_word("SUPPRESS"):
            j += 1
        pairs = []
        if j < len(toks) and toks[j].is_word("REPLACING"):
            j += 1
            while j < len(toks) and toks[j].kind != "PERIOD":
                if toks[j].is_word("LEADING", "TRAILING"):
                    raise CopyError(f"{toks[j].where()}: COPY REPLACING LEADING/TRAILING is not supported")
                a, j = _operand(toks, j)
                if j >= len(toks) or not toks[j].is_word("BY"):
                    raise CopyError(f"{t.where()}: REPLACING without BY")
                b, j = _operand(toks, j + 1)
                pairs.append((a, b))
        if j >= len(toks) or toks[j].kind != "PERIOD":
            raise CopyError(f"{t.where()}: COPY statement must end with a period")
        path = find_copybook(name, dirs)
        if path is None:
            raise CopyError(f"{t.where()}: copybook {name} not found in {dirs}")
        used.append(path)
        with open(path, encoding="latin-1") as fh:
            ctoks = lexer.tokenize(source.read_lines(fh.read(), path, fmt))
        ctoks = expand(ctoks, dirs, fmt, depth + 1, used)
        out.extend(_replace(ctoks, pairs))
        i = j + 1
    return out

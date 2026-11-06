"""COPY and REPLACE on text words, as IBM Enterprise COBOL 6.4 processes them.

copybook.expand reads a program on tokens. A program whose text, with the copybooks it copies, holds
a REPLACE statement or a COPY statement with REPLACING, OF or IN is read here instead, on the text
words of IBM's rules (Language Reference: COPY statement, Comparison and replacement rules, REPLACE
statement):

* Text words: a literal with its delimiters (and its X, N, Z or G prefix); each of `(` `)` `:` and a
  separator period (a period followed by a space or the end of the line); a separator comma or
  semicolon (followed by a space or the end of the line); the pseudo-text delimiter `==`; and any
  other run of characters up to one of these or a space. Lines come from source.read_lines with
  keep_debug: comment lines are gone, and the text words of debugging lines take part in matching
  and are dropped at the end (a program WITH DEBUGGING MODE is unsupported).
* COPY statements first, in source order; a copybook's own COPY statements are expanded before the
  REPLACING phrase of the COPY statement that copied it applies, so that phrase reaches the nested
  text. A chain of nested COPY statements may hold one REPLACING phrase (IBM: IGYLI0078-S), and a
  copybook may not copy itself. A library name is a literal naming a directory (a relative one is
  looked for under the source's directory, then under each -I directory); a library-name word, which
  IBM takes as an environment variable, is rejected.
* Then REPLACE statements: each is in effect from its end to the next REPLACE statement or the end
  of its separately compiled program (REPLACE OFF ends it), and is removed from the text. A batch
  program ends with the END PROGRAM marker that closes it; the programs it contains keep the
  REPLACE in effect.
* Matching (both): at each text word the operands are tried in order. Operand-1 matches when its text
  words equal the following ones, separator commas and semicolons skipped (they count as spaces),
  unless operand-1 is just one of them; words compare in upper case, literals character for
  character. LEADING / TRAILING compare characters at the start / end of one word (a word left empty
  is deleted). Replaced text is not compared again.
* Replacement text words go where the matched ones began, with spaces only where the text or
  pseudo-text-2 has them (IBM: "additional spaces are introduced only between text words where there
  already exists a space"), so ==:TAG:== BY ==PAY== turns :TAG:-WEEK into PAY-WEEK.

The result is laid out as source lines again (unchanged words on their own line and column) and
tokenized by lexer.tokenize.
"""
import os

import copybook
import lexer
import source
from copybook import CopyError


class TW:
    """A text word: `kind` is word, lit, sep (one of ( ) : .), comma (a separator comma or semicolon)
    or pseudo (==); `sp` tells a space (or a line start) before it; `dbg` a debugging line."""
    __slots__ = ("text", "kind", "sp", "file", "line", "col", "dbg")

    def __init__(self, text, kind, sp, file, line, col, dbg):
        self.text, self.kind, self.sp, self.dbg = text, kind, sp, dbg
        self.file, self.line, self.col = file, line, col

    def moved(self, **kw):
        t = TW(self.text, self.kind, self.sp, self.file, self.line, self.col, self.dbg)
        for k, v in kw.items():
            setattr(t, k, v)
        return t

    def key(self):
        return self.text if self.kind == "lit" else self.text.upper()

    def is_(self, kind, *texts):
        return self.kind == kind and (not texts or self.key() in texts)

    def where(self):
        return f"{self.file}:{self.line}:{self.col}"


def _sep_end(s, k):
    """A comma, semicolon or period ending at s[k] is a separator: a space, the end of the line or
    a pseudo-text delimiter follows (IBM: in ==,== the space after the comma can be omitted)."""
    return k == len(s) or s[k] == " " or s.startswith("==", k)


def scan(lines):
    out = []
    for ln in lines:
        s, n, i, sp = ln.text, len(ln.text), 0, True
        while i < n:
            c = s[i]
            if c == " ":
                sp, i = True, i + 1
                continue
            col = ln.col0 + i
            end = _sep_end(s, i + 1)
            if c in ",;" and end:
                kind, j = "comma", i + 1
            elif c == "." and end:
                kind, j = "sep", i + 1
            elif c in "():":
                kind, j = "sep", i + 1
            elif s.startswith("==", i):
                kind, j = "pseudo", i + 2
            elif c in "'\"" or (c in "XxNnZzGg" and s[i + 1:i + 2] in ("'", '"')):
                kind, j = "lit", (i + 1 if c in "'\"" else i + 2)
                q = s[j - 1]
                while True:
                    if j >= n:
                        raise lexer.LexError(f"{ln.file}:{ln.lineno}:{col}: unterminated literal")
                    if s[j] == q:
                        if s[j + 1:j + 2] == q:
                            j += 2
                            continue
                        break
                    j += 1
                j += 1
            else:
                kind, j = "word", i
                while j < n and s[j] not in " ():'\"" and not s.startswith("==", j) and \
                        not (s[j] in ",;." and _sep_end(s, j + 1)):
                    j += 1
            out.append(TW(s[i:j], kind, sp, ln.file, ln.lineno, col, ln.debug))
            sp, i = False, j
    return out


def _value(t):
    """The characters of an alphanumeric literal text word without a prefix, else None."""
    if t.kind != "lit" or t.text[0] not in "'\"":
        return None
    q = t.text[0]
    return t.text[1:-1].replace(q + q, q)


def _operand(ws, j, t0):
    """The REPLACING / REPLACE operand at ws[j] -> (text words, next index, is pseudo-text). Not
    pseudo-text: an identifier (qualified, subscripted, reference-modified), function-identifier,
    literal (also ALL literal) or word, matched as pseudo-text holding it."""
    if j >= len(ws):
        raise CopyError(f"{t0.where()}: {t0.key()} statement must end with a period")
    t = ws[j]
    if t.kind == "pseudo":
        k = j + 1
        while k < len(ws) and ws[k].kind != "pseudo":
            k += 1
        if k >= len(ws):
            raise CopyError(f"{t.where()}: unterminated pseudo-text")
        return ws[j + 1:k], k + 1, True
    if t.kind not in ("word", "lit") or t.is_("word", "BY"):
        raise CopyError(f"{t.where()}: {t.text!r} cannot begin a {t0.key()} operand")
    k = j + 1
    if t.is_("word", "ALL") and k < len(ws) and ws[k].kind == "lit":
        return ws[j:k + 1], k + 1, False
    if t.kind == "word":
        if t.is_("word", "FUNCTION") and k < len(ws) and ws[k].kind == "word":
            k += 1
        while k + 1 < len(ws) and ws[k].is_("word", "OF", "IN") and ws[k + 1].kind == "word":
            k += 2
        while k < len(ws) and ws[k].is_("sep", "("):
            depth = 0
            while True:
                if k >= len(ws) or ws[k].is_("sep", "."):
                    raise CopyError(f"{t.where()}: unbalanced parentheses in a {t0.key()} operand")
                if ws[k].is_("sep", "("):
                    depth += 1
                elif ws[k].is_("sep", ")"):
                    depth -= 1
                k += 1
                if depth == 0:
                    break
    return ws[j:k], k, False


def _prep(mode, a, b, t0):
    """A prepared operand pair: ("words", keys, words-2, None), ("comma", char, words-2, None) or
    ("partial", key, text-2, LEADING|TRAILING)."""
    aw = [x for x in a if x.kind != "comma"]
    if mode:
        bw = [x for x in b if x.kind != "comma"]
        if len(aw) != 1 or aw[0].kind != "word" or len(bw) > 1 or (bw and bw[0].kind != "word"):
            raise CopyError(f"{t0.where()}: {mode} needs one partial word BY zero or one, not literals")
        return ("partial", aw[0].key(), bw[0].text if bw else "", mode)
    if not aw:
        if len(a) == 1:
            return ("comma", a[0].text, b, None)
        raise CopyError(f"{t0.where()}: {t0.key()} operand-1 without a text word")
    return ("words", [x.key() for x in aw], b, None)


def _pairs(ws, j, t0, operands):
    """The operand pairs of a REPLACING phrase or REPLACE statement from ws[j] up to the separator
    period -> (pairs, index after the period). `operands`: identifiers, literals and words allowed
    besides pseudo-text (COPY REPLACING)."""
    pairs = []
    while True:
        if j >= len(ws):
            raise CopyError(f"{t0.where()}: {t0.key()} statement must end with a period")
        if ws[j].is_("sep", "."):
            if not pairs:
                raise CopyError(f"{t0.where()}: {t0.key()} without operands")
            return pairs, j + 1
        mode = None
        if ws[j].is_("word", "LEADING", "TRAILING") and j + 1 < len(ws) and ws[j + 1].kind == "pseudo":
            mode = ws[j].key()
            j += 1
        a, j, apt = _operand(ws, j, t0)
        if j >= len(ws) or not ws[j].is_("word", "BY"):
            raise CopyError(f"{t0.where()}: {'REPLACING' if operands else 'REPLACE'} without BY")
        b, j, bpt = _operand(ws, j + 1, t0)
        if not (apt and bpt) and (mode or not operands):
            raise CopyError(f"{t0.where()}: {mode or 'REPLACE'} operands must be pseudo-text")
        pairs.append(_prep(mode, a, b, t0))


def apply(ws, pairs):
    """The text words ws with every match of the prepared pairs replaced (one comparison cycle per
    text word, operands in order, replaced text not compared again)."""
    out, i, n = [], 0, len(ws)
    pend = False     # the space before a match replaced by nothing goes to the next text word
    while i < n:
        w = ws[i]
        hit = None
        for kind, a, b, mode in pairs:
            if kind == "comma":
                if w.kind == "comma" and w.text == a:
                    hit = (i + 1, b, None)
                    break
                continue
            if w.kind == "comma":
                continue
            if kind == "words":
                j = i
                for k, key in enumerate(a):
                    while k and j < n and ws[j].kind == "comma":
                        j += 1
                    if j >= n or ws[j].kind == "comma" or ws[j].key() != key:
                        break
                    j += 1
                else:
                    hit = (j, b, None)
                    break
            elif w.kind in ("word", "lit") and len(a) <= len(w.text):
                u = w.key()
                if mode == "LEADING" and u.startswith(a):
                    hit = (i + 1, None, b + w.text[len(a):])
                    break
                if mode == "TRAILING" and u.endswith(a):
                    hit = (i + 1, None, w.text[:len(w.text) - len(a)] + b)
                    break
        if hit is None:
            out.append(w.moved(sp=True) if pend and not w.sp else w)
            pend = False
            i += 1
            continue
        j, words, text = hit
        if words is None:
            words = [w.moved(text=text, sp=False)] if text else []
        for k, x in enumerate(words):
            out.append(x.moved(sp=(w.sp or pend) if k == 0 else x.sp, file=w.file, line=w.line,
                               col=w.col, dbg=w.dbg))
        pend = (w.sp or pend) and not words
        i = j
    return out


def _copy_stmt(ws, i):
    """The COPY statement at ws[i] -> (name, library or None, prepared pairs, index after it)."""
    t = ws[i]
    j = i + 1
    if j >= len(ws) or not (ws[j].kind == "word" or _value(ws[j]) is not None):
        raise CopyError(f"{t.where()}: COPY without a copybook name")
    name = ws[j].key() if ws[j].kind == "word" else _value(ws[j])
    j += 1
    lib = None
    if j < len(ws) and ws[j].is_("word", "OF", "IN"):
        kw = ws[j]
        lib = _value(ws[j + 1]) if j + 1 < len(ws) else None
        if lib is None:
            what = ws[j + 1].text if j + 1 < len(ws) else ""
            raise CopyError(f"{kw.where()}: COPY {name} {kw.key()} {what}: library names are not supported, "
                            "except a literal naming a directory")
        j += 2
    if j < len(ws) and ws[j].is_("word", "SUPPRESS"):
        j += 1
    if j < len(ws) and ws[j].is_("word", "REPLACING"):
        pairs, j = _pairs(ws, j + 1, t, True)
        return name, lib, pairs, j
    if j >= len(ws) or not ws[j].is_("sep", "."):
        raise CopyError(f"{t.where()}: COPY statement must end with a period")
    return name, lib, [], j + 1


def _find(name, lib, dirs, t):
    if lib is None:
        path = copybook.find_copybook(name, dirs)
        if path is None:
            raise CopyError(f"{t.where()}: copybook {name} not found in {dirs}")
        return path
    cands = [lib] if os.path.isabs(lib) else [os.path.join(d, lib) for d in dirs]
    path = copybook.find_copybook(name, [c for c in cands if os.path.isdir(c)])
    if path is None:
        raise CopyError(f"{t.where()}: copybook {name} not found in library {lib} ({cands})")
    return path


def copy_pass(ws, dirs, fmt, chain, used, replacing):
    """ws with every COPY statement replaced by its library text. `chain`: the copybooks being
    copied (no recursion); `replacing`: a COPY statement of the chain has a REPLACING phrase."""
    out, i, pseudo = [], 0, False
    while i < len(ws):
        w = ws[i]
        if w.kind == "pseudo":
            pseudo = not pseudo
        if not w.is_("word", "COPY"):
            out.append(w)
            i += 1
            continue
        if pseudo:
            raise CopyError(f"{w.where()}: COPY in pseudo-text")
        name, lib, pairs, i = _copy_stmt(ws, i)
        if pairs and replacing:
            raise CopyError(f"{w.where()}: a second COPY statement with REPLACING in a chain of nested COPY "
                            "statements (IBM IGYLI0078-S)")
        path = _find(name, lib, dirs, w)
        if os.path.abspath(path) in chain:
            raise CopyError(f"{w.where()}: COPY {name} inside its own text (a nested COPY cannot cause recursion)")
        used.append(path)
        with open(path, encoding="latin-1") as fh:
            text = scan(source.read_lines(fh.read(), path, fmt, keep_debug=True))
        text = copy_pass(text, dirs, fmt, chain + [os.path.abspath(path)], used, replacing or bool(pairs))
        if pairs:
            text = apply(text, pairs)
        out.extend(x.moved(sp=x.sp or k == 0, dbg=x.dbg or w.dbg) for k, x in enumerate(text))
    return out


def replace_pass(ws):
    """ws with the REPLACE statements applied and removed. A REPLACE statement is in effect up to the
    next one or the end of its separately compiled program (IBM): the END PROGRAM marker that closes
    the outermost program of a batch ends it, the programs it contains keep it. IDENTIFICATION (ID)
    DIVISION headers and END PROGRAM markers count only as words of the program text: not inside
    literals or pseudo-text (the operands of REPLACE statements are read by _pairs) and not on
    debugging lines (comment lines in the end)."""
    out, seg, pairs, i, depth, pseudo = [], [], None, 0, 0, False
    while i < len(ws):
        w = ws[i]
        if not w.is_("word", "REPLACE"):
            seg.append(w)
            i += 1
            if w.kind == "pseudo":
                pseudo = not pseudo
            elif pseudo or w.dbg:
                pass
            elif w.is_("word", "IDENTIFICATION", "ID") and i < len(ws) and not ws[i].dbg \
                    and ws[i].is_("word", "DIVISION"):
                depth += 1
            elif w.is_("word", "END") and i + 2 < len(ws) and not any(x.dbg for x in ws[i:i + 3]) \
                    and ws[i].is_("word", "PROGRAM") and ws[i + 2].is_("sep", "."):
                seg.extend(ws[i:i + 3])
                i += 3
                depth -= 1
                if depth <= 0:
                    out.extend(apply(seg, pairs) if pairs else seg)
                    seg, pairs, depth = [], None, 0
            continue
        out.extend(apply(seg, pairs) if pairs else seg)
        seg = []
        if i + 2 < len(ws) and ws[i + 1].is_("word", "OFF") and ws[i + 2].is_("sep", "."):
            pairs, i = None, i + 3
        else:
            pairs, i = _pairs(ws, i + 1, w, False)
    out.extend(apply(seg, pairs) if pairs else seg)
    return out


def layout(ws, col0):
    """Source lines holding the text words: a new line where a word with a space before it comes
    from another source line; words of the line's own source line at their column if there is room."""
    out = []
    cur = None
    for w in ws:
        own = cur is not None and (w.file, w.line) == (cur.file, cur.lineno)
        if cur is None or (w.sp and not own):
            cur = source.Line("", col0, w.file, w.line)
            out.append(cur)
            own = True
        gap = w.col - col0 - len(cur.text) if own else 1
        if w.sp and cur.text:
            cur.text += " " * max(1, gap)
        elif not cur.text and own:
            cur.text = " " * max(0, gap)
        cur.text += w.text
    return out


def expand_file(path, dirs, fmt="fixed", used=None):
    """The tokens of the program file `path` after COPY and REPLACE (read as cobolfe.front_end
    reads it)."""
    if used is None:
        used = []
    with open(path, encoding="latin-1") as fh:
        text = fh.read()
    ws = scan(source.strip_comment_entries(source.read_lines(text, path, fmt, keep_debug=True)))
    ws = replace_pass(copy_pass(ws, dirs, fmt, [os.path.abspath(path)], used, False))
    return lexer.tokenize(layout([w for w in ws if not w.dbg], 1 if fmt == "free" else 8))

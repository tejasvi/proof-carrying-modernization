"""Tokens of COBOL program text (after `source.read_lines`)."""
import re
from dataclasses import dataclass, field


@dataclass
class Tok:
    kind: str        # WORD NUM STR HEX NSTR ZSTR PIC PERIOD LPAR RPAR COLON OP PSEUDO EXEC
    val: object      # WORD: upper-case text; NUM: literal text; STR: str; HEX: bytes; PIC: str; OP: str;
                     # EXEC: text between EXEC and END-EXEC (blanks collapsed)
    file: str = ""
    line: int = 0
    col: int = 0     # source column (1-based)
    # a separator comma or semicolon stands between the previous token and this one
    sep: bool = field(default=False, compare=False)
    # that separator ("," or ";") when it is written directly before this token, on its line
    # (DECIMAL-POINT IS COMMA reads `1,5` and `,5` as literals, parser.dpc_literals)
    sepch: str = field(default="", compare=False)

    def is_word(self, *ws):
        return self.kind == "WORD" and (not ws or self.val in ws)

    def where(self):
        return f"{self.file}:{self.line}:{self.col}"

    def __repr__(self):
        return f"{self.kind}({self.val!r})@{self.line}:{self.col}"


class LexError(Exception):
    pass


_WORD = re.compile(r"[A-Za-z0-9](?:[A-Za-z0-9_-]*[A-Za-z0-9_])?")
_NUM = re.compile(r"[+-]?(?:\d+(?:\.\d+)?|\.\d+)(?:E[+-]?\d+)?")
_SEP_AFTER = set(" ,;.():=<>+-*/\"'") | {""}
_END_EXEC = re.compile(r"\bEND-EXEC\b", re.IGNORECASE)


def _at(s, i):
    return s[i] if i < len(s) else ""


def tokenize(lines):
    toks = []
    pending_sep = [False]
    pending_ch = [""]

    def emit(t):
        t.sep = pending_sep[0]
        t.sepch = pending_ch[0]
        pending_sep[0] = False
        pending_ch[0] = ""
        toks.append(t)
    pic_next = False
    exec_raw = None      # inside EXEC ... END-EXEC: [token, text pieces]
    for ln in lines:
        s = ln.text
        i = 0
        n = len(s)
        pending_ch[0] = ""
        while i < n:
            if exec_raw:
                m = _END_EXEC.search(s, i)
                if m is None:
                    exec_raw[1].append(s[i:])
                    break
                exec_raw[1].append(s[i:m.start()])
                exec_raw[0].val = " ".join(" ".join(exec_raw[1]).split())
                emit(exec_raw[0])
                exec_raw = None
                i = m.end()
                continue
            c = s[i]
            col = ln.col0 + i
            mk = lambda kind, val: Tok(kind, val, ln.file, ln.lineno, col)
            if c == " ":
                pending_ch[0] = ""
                i += 1
                continue
            if c in ",;" and not (pic_next and c == "," and _at(s, i + 1) not in (" ", "")):
                # separator comma / semicolon (also accepted without the following space);
                # the next token records it (`MAX(A, - 1)` has two arguments)
                # (not a comma right after PIC / PICTURE [IS] that a non-space follows: IBM's
                # separator comma is followed by a space, so that comma begins the character-string
                # read below, and `PIC ,ZZ9` has 4 positions)
                pending_sep[0] = True
                pending_ch[0] = c
                i += 1
                continue
            if pic_next:
                # a PICTURE character string: up to a space; a final '.', ',' or ';' that
                # is followed by a space ends the clause, not the picture
                j = i
                while j < n and s[j] != " ":
                    j += 1
                pic = s[i:j]
                trail = None
                while pic and pic[-1] in ".,;" and True:
                    trail = pic[-1]
                    pic = pic[:-1]
                    break
                emit(mk("PIC", pic.upper()))
                if trail == ".":
                    emit(Tok("PERIOD", ".", ln.file, ln.lineno, ln.col0 + j - 1))
                i = j
                pic_next = False
                continue
            if c == "." and _at(s, i + 1) in (" ", ""):
                emit(mk("PERIOD", "."))
                i += 1
                continue
            if c in "'\"" or (c in "XxNnZzGg" and _at(s, i + 1) in ("'", '"')):
                kind = "STR"
                if c not in "'\"":
                    kind = {"X": "HEX", "N": "NSTR", "Z": "ZSTR", "G": "NSTR"}[c.upper()]
                    i += 1
                q = s[i]
                j = i + 1
                buf = []
                while True:
                    if j >= n:
                        raise LexError(f"{ln.file}:{ln.lineno}:{col}: unterminated literal")
                    if s[j] == q:
                        if _at(s, j + 1) == q:
                            buf.append(q)
                            j += 2
                            continue
                        break
                    buf.append(s[j])
                    j += 1
                text = "".join(buf)
                if kind == "HEX":
                    try:
                        val = bytes.fromhex(text)
                    except ValueError:
                        raise LexError(f"{ln.file}:{ln.lineno}:{col}: bad hex literal {text!r}")
                    emit(mk("HEX", val))
                else:
                    emit(mk(kind, text))
                i = j + 1
                continue
            if c == "=" and _at(s, i + 1) == "=":
                emit(mk("PSEUDO", "=="))
                i += 2
                continue
            if c == "(":
                emit(mk("LPAR", "("))
                i += 1
                continue
            if c == ")":
                emit(mk("RPAR", ")"))
                i += 1
                continue
            if c == ":":
                emit(mk("COLON", ":"))
                i += 1
                continue
            # numeric literal; a sign written directly before the digits always belongs to it,
            # also after an operand (`A -1`, `(A)-1`), as in GnuCOBOL: no binary operator there
            m = _NUM.match(s, i)
            if m and _at(s, m.end()) in _SEP_AFTER and not (_at(s, m.end()) == "-" and
                                                            m.group(0)[-1:].isdigit() and
                                                            _WORD.match(s, i)):
                lit = m.group(0)
                # `1000-CALC`: digits followed by a hyphen and more word characters is a word
                w = _WORD.match(s, i) if c not in "+-." else None
                if w and len(w.group(0)) > len(lit):
                    pass
                else:
                    emit(mk("NUM", lit))
                    i = m.end()
                    continue
            w = _WORD.match(s, i)
            if w:
                word = w.group(0).upper()
                if word == "EXEC" and not exec_raw:
                    exec_raw = [mk("EXEC", None), []]
                    i = w.end()
                    continue
                emit(mk("WORD", word))
                i = w.end()
                if word in ("PIC", "PICTURE"):
                    # optional IS
                    k = i
                    while k < n and s[k] == " ":
                        k += 1
                    if s[k:k + 2].upper() == "IS" and _at(s, k + 2) in (" ", ""):
                        emit(Tok("WORD", "IS", ln.file, ln.lineno, ln.col0 + k))
                        i = k + 2
                    pic_next = True
                continue
            if s.startswith("**", i):
                emit(mk("OP", "**"))
                i += 2
                continue
            if s.startswith(">=", i) or s.startswith("<=", i) or s.startswith("<>", i):
                emit(mk("OP", s[i:i + 2]))
                i += 2
                continue
            if c in "+-*/=<>&":
                emit(mk("OP", c))
                i += 1
                continue
            if c == ".":
                # a period not followed by a space (e.g. at end of text after a literal)
                emit(mk("PERIOD", "."))
                i += 1
                continue
            raise LexError(f"{ln.file}:{ln.lineno}:{col}: unexpected character {c!r}")
    if exec_raw:
        raise LexError(f"{exec_raw[0].where()}: EXEC without END-EXEC")
    return toks

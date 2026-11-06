"""Token stream with look-ahead, and parse errors that point at the source."""
from lexer import Tok
from reserved import is_user_word

EOF = Tok("EOF", None)


class ParseError(Exception):
    def __init__(self, tok, msg):
        where = tok.where() if tok is not None and tok.kind != "EOF" else "end of input"
        super().__init__(f"{where}: {msg}")
        self.tok = tok


def lit_number(t):
    """`(v, scale, digits)` of a numeric literal token (`-12.50` -> (-1250, 2, 4))."""
    s = t.val
    if "E" in s.upper():
        raise ParseError(t, f"floating-point literal {s} is not supported")
    neg = s.startswith("-")
    s = s.lstrip("+-")
    if "." in s:
        ip, fp = s.split(".")
    else:
        ip, fp = s, ""
    digits = ip + fp
    v = int(digits) if digits else 0
    return (-v if neg else v, len(fp), len(digits))


class TS:
    def __init__(self, toks):
        self.toks = toks
        self.i = 0

    def peek(self, k=0):
        j = self.i + k
        return self.toks[j] if j < len(self.toks) else EOF

    def next(self):
        t = self.peek()
        self.i += 1
        return t

    def at_word(self, *ws):
        return self.peek().is_word(*ws)

    def accept_word(self, *ws):
        if self.peek().is_word(*ws):
            return self.next()
        return None

    def expect_word(self, *ws):
        t = self.peek()
        if not t.is_word(*ws):
            raise ParseError(t, f"expected {' or '.join(ws)}, found {t.val!r}")
        return self.next()

    def accept_kind(self, kind):
        if self.peek().kind == kind:
            return self.next()
        return None

    def expect_kind(self, kind):
        t = self.peek()
        if t.kind != kind:
            raise ParseError(t, f"expected {kind}, found {t.val!r}")
        return self.next()

    def expect_user_word(self):
        t = self.peek()
        if not is_user_word(t):
            raise ParseError(t, f"expected a name, found {t.val!r}")
        return self.next()

    def skip_to_period(self):
        while self.peek().kind not in ("PERIOD", "EOF"):
            self.next()
        self.accept_kind("PERIOD")

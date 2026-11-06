"""Reading COBOL source text: reference format and copybooks.

* Fixed (reference) format: columns 1-6 sequence area (ignored), column 7 indicator
  (`*` `/` comment, `D` debugging line = comment, `-` continuation; any other character is an
  error), columns 8-72 program text (area A = 8-11, area B = 12-72), columns 73- ignored.
  A `D` line is a comment; a program that declares WITH DEBUGGING MODE is unsupported (see
  the parser). COPY and REPLACE match the text words of `D` lines before they become
  comments (IBM), so `textmanip.py` reads them with `keep_debug`.
* Free format: the whole line is text, `*>` starts a comment (also accepted in fixed format).
* Continuation: an alphanumeric literal left open at column 72 continues after the first
  quote of the next continuation line, holding the spaces through column 72 of every
  continued line; any other word continues with the first non-blank character of the
  continuation line.

The result is a list of `Line(text, col0, file, lineno)`: `text` is the program text of a
logical line, `col0` the source column of its first character (to tell area A from area B).
"""
import re
from dataclasses import dataclass, field


@dataclass
class Line:
    text: str
    col0: int          # source column (1-based) of text[0]
    file: str
    lineno: int
    # a debugging line (`D` in column 7), kept only by read_lines(keep_debug=True)
    debug: bool = field(default=False, compare=False)


class SourceError(Exception):
    pass


def _strip_inline_comment(s):
    """Remove a `*>` comment that is not inside a literal."""
    q = None
    i = 0
    while i < len(s):
        c = s[i]
        if q:
            if c == q:
                q = None
        elif c in "'\"":
            q = c
        elif c == "*" and i + 1 < len(s) and s[i + 1] == ">":
            return s[:i]
        i += 1
    return s


def _open_quote(s):
    """The quote character of an alphanumeric literal left open at the end of `s`, if any."""
    q = None
    for c in s:
        if q:
            if c == q:
                q = None     # a doubled quote closes and reopens: net effect is fine
        elif c in "'\"":
            q = c
    return q


# Tab stops for source lines with tab characters (`--tab-width`).  Real fixed-format source has
# no tabs; files edited with tabs need the author's tab width, or text slides past column 72.
TAB_WIDTH = 8


def read_lines(text, path, fmt="fixed", keep_debug=False):
    """The logical lines of a source file. Debugging lines are dropped, or with `keep_debug` kept
    with `debug` set (COPY and REPLACE match their text words, textmanip.py). A literal continued
    over several lines holds the spaces through column 72 of every continued line (IBM)."""
    out = []
    end72 = 0          # length of out[-1].text through column 72 of its last source line
    raw = text.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    for n, line in enumerate(raw, 1):
        line = line.expandtabs(TAB_WIDTH)
        directive = line.strip().upper()
        if directive.startswith(">>SOURCE"):
            # `>>SOURCE [FORMAT] [IS] FREE|FIXED`: accepted only when it names the format the
            # file is read in (a switch in mid-file is not supported)
            words = directive[len(">>SOURCE"):].split()
            want = "free" if "FREE" in words else "fixed" if "FIXED" in words else None
            if want is not None and want != fmt:
                raise SourceError(f"{path}:{n}: >>SOURCE switches to {want} format, the file is read as {fmt}")
            continue
        if fmt == "free":
            if line.lstrip().startswith("*>"):
                continue
            body = _strip_inline_comment(line).rstrip()
            if line.lstrip()[:1] == "-" and out:  # free-format continuation is rare
                pass
            out.append(Line(body, 1, path, n))
            continue
        if len(line) < 7:
            continue
        ind = line[6]
        if ind in "*/":
            continue
        if ind in "Dd" and not keep_debug:
            continue
        area = line[7:72]
        if ind == "-":
            if not out:
                raise SourceError(f"{path}:{n}: continuation line without a preceding line")
            prev = out[-1]
            q = _open_quote(prev.text)
            if q:
                # the open literal extends to column 72
                padded = prev.text.ljust(end72)
                cont = area.lstrip()
                if not cont or cont[0] not in "'\"":
                    raise SourceError(f"{path}:{n}: literal continuation must start with a quote")
                end72 = len(padded) + 72 - (8 + len(area) - len(cont))
                prev.text = padded + _strip_inline_comment(cont[1:]).rstrip()
            else:
                head = prev.text.rstrip()
                end72 = len(head) + 73 - (8 + len(area) - len(area.lstrip()))
                prev.text = head + _strip_inline_comment(area.lstrip()).rstrip()
            continue
        if ind not in " Dd":
            raise SourceError(f"{path}:{n}: unknown indicator {ind!r} in column 7")
        body = _strip_inline_comment(area).rstrip()
        out.append(Line(body, 8, path, n, ind in "Dd"))
        end72 = 72 - 8 + 1
    return out


_COMMENT_PARA = re.compile(r"(AUTHOR|INSTALLATION|DATE-WRITTEN|DATE-COMPILED|SECURITY|REMARKS)\s*\.",
                           re.IGNORECASE)
_HEADER = re.compile(r"(AUTHOR|INSTALLATION|DATE-WRITTEN|DATE-COMPILED|SECURITY|REMARKS|PROGRAM-ID"
                     r"|(IDENTIFICATION|ID|ENVIRONMENT|DATA|PROCEDURE)\s+DIVISION)\b", re.IGNORECASE)
_DIVISION = re.compile(r"(ENVIRONMENT|DATA|PROCEDURE)\s+DIVISION\b", re.IGNORECASE)
_ID_DIVISION = re.compile(r"(IDENTIFICATION|ID)\s+DIVISION\b", re.IGNORECASE)


def strip_comment_entries(lines):
    """Drop the comment entries of the identification division (`AUTHOR. any text`, ...):
    free text up to the next entry that starts in area A (or the next header). Each program of
    the source (contained programs, a batch) has its own identification division."""
    out = []
    in_entry = False
    in_id = True
    for k, ln in enumerate(lines):
        st = ln.text.lstrip()
        lead = len(ln.text) - len(st)
        if not in_id:
            if _ID_DIVISION.match(st):
                in_id, in_entry = True, False
            out.append(ln)
            continue
        if _DIVISION.match(st):
            in_id = False
            out.append(ln)
            continue
        area_a = ln.col0 + lead <= 11
        if in_entry:
            if st and ((area_a and ln.col0 == 8) or _HEADER.match(st)):
                in_entry = False
            else:
                continue
        m = _COMMENT_PARA.match(st)
        if m:
            out.append(Line(ln.text[:lead + m.end()], ln.col0, ln.file, ln.lineno))
            in_entry = True
            continue
        out.append(ln)
    return out

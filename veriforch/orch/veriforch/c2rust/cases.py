"""Test inputs for tiny-regex-c (f2632c6): (pattern, text) byte strings, neither containing 0.

    python3 -m veriforch.c2rust.cases       # writes runs/c2rust/tiny-regex-c/cases/{round,heldout}.json

Sources (field `source`):
* test1: tests/test1.c's test_vector table (its commented-out block excluded); the project's expectation
  (match or not, length) is kept as `project_expect`;
* makefile: the patterns of the Makefile's random tests (scripts/regex_test.py, regex_test_neg.py) as the shell
  passes them, each with texts generated to match it and random texts (the scripts are not run);
* compile: tests/test_compile.c's two invalid patterns;
* edge: hand-written: anchors and quantifiers out of place, a trailing backslash, unclosed and empty classes, the
  class-buffer and object limits, bytes >= 0x80 and control characters, empty pattern and text, long texts;
* gen: random patterns over the supported syntax with texts for each (generated to match, mutated, random).

`round` (seed 1) is evaluated on every version of a translation; `heldout` (seed 2: other generated cases, other
texts for the Makefile patterns) once a version passes `round`. A case is {"id", "source", "pattern", "text"}
with both strings as hex.
"""
from __future__ import annotations

import json
import random
import re
import shlex
import subprocess
import sys
from pathlib import Path

VO_ROOT = Path(__file__).resolve().parents[3]
TARGET = VO_ROOT / "targets" / "tiny-regex-c"
PIN = "f2632c6"
OUT = VO_ROOT / "runs" / "c2rust" / "tiny-regex-c" / "cases"
MAX_OBJECTS = 30
MAX_CCL = 40


def git_show(path: str) -> str:
    return subprocess.run(["git", "-C", str(TARGET), "show", f"{PIN}:{path}"], check=True, capture_output=True,
                          text=True, encoding="latin-1").stdout


def c_unescape(s: str) -> bytes:
    """The bytes of a C string literal's contents (simple, octal and hex escapes)."""
    simple = {"n": 10, "t": 9, "r": 13, "f": 12, "v": 11, "a": 7, "b": 8, "\\": 92, '"': 34, "'": 39, "?": 63}
    out, i = bytearray(), 0
    while i < len(s):
        ch = s[i]
        if ch != "\\":
            out.append(ord(ch))
            i += 1
            continue
        nx = s[i + 1]
        if nx in simple:
            out.append(simple[nx])
            i += 2
        elif nx == "x":
            mo = re.match(r"[0-9a-fA-F]+", s[i + 2:])
            out.append(int(mo.group(0), 16) & 0xFF)
            i += 2 + len(mo.group(0))
        elif nx in "01234567":
            mo = re.match(r"[0-7]{1,3}", s[i + 1:])
            out.append(int(mo.group(0), 8) & 0xFF)
            i += 1 + len(mo.group(0))
        else:
            raise ValueError(f"unknown escape \\{nx}")
    return bytes(out)


def test1_vectors() -> list[dict]:
    src = re.sub(r"/\*.*?\*/", "", git_show("tests/test1.c"), flags=re.S)
    table = src[src.index("test_vector[][4]"):]
    table = table[:table.index("};")]
    lit = r'"((?:[^"\\]|\\.)*)"'
    out = []
    for mo in re.finditer(r"\{\s*(OK|NOK)\s*,\s*" + lit + r"\s*,\s*" + lit + r"\s*,\s*\(char\*\)\s*(\d+)\s*\}", table):
        out.append({"pattern": c_unescape(mo.group(2)), "text": c_unescape(mo.group(3)),
                    "project_expect": {"match": mo.group(1) == "OK", "length": int(mo.group(4))}})
    return out


def makefile_patterns() -> list[tuple[str, bytes]]:
    """(script, pattern) of the Makefile's random tests, after make (no variable in the patterns) and the shell
    (backslash removal; no file matches the patterns as globs)."""
    out = []
    for line in git_show("Makefile").splitlines():
        mo = re.match(r"\s*@python \./scripts/(regex_test(?:_neg)?\.py) (.*) \$\(NRAND_TESTS\)\s*$", line)
        if mo:
            (word,) = shlex.split(mo.group(2))
            out.append((mo.group(1), word.encode("latin-1")))
    return out


def compile_vectors() -> list[bytes]:
    src = git_show("tests/test_compile.c")
    return [c_unescape(m) for m in re.findall(r're_compile\("((?:[^"\\]|\\.)*)"\)', src)]


# -- a model of the pattern syntax, only to generate texts likely to match (never an oracle) ---------------------

DIGITS = b"0123456789"
ALNUM = bytes(range(48, 58)) + bytes(range(65, 91)) + bytes(range(97, 123)) + b"_"
SPACE = b" \t\n\r\x0b\x0c"
PRINTABLE = bytes(range(32, 127))
CONTROL = b"\t\n\r\x0b\x0c\x01\x1b\x7f"
HIGH = bytes(range(0x80, 0x100))


def _meta_set(c: int) -> bytes | None:
    """Members of \\d \\D \\w \\W \\s \\S over all nonzero bytes."""
    every = bytes(range(1, 256))
    sets = {ord("d"): DIGITS, ord("w"): ALNUM, ord("s"): SPACE}
    if c in sets:
        return sets[c]
    if chr(c).lower() in "dws" and chr(c).isupper():
        pos = sets[ord(chr(c).lower())]
        return bytes(b for b in every if b not in pos)
    return None


def _class_members(body: bytes) -> set[int]:
    members, i = set(), 0
    while i < len(body):
        c = body[i]
        if c == 92 and i + 1 < len(body):
            ms = _meta_set(body[i + 1])
            members |= set(ms) if ms is not None else {body[i + 1]}
            i += 2
        elif i + 2 < len(body) and body[i + 1] == 45:
            lo, hi = c, body[i + 2]
            members |= set(range(lo, hi + 1))
            i += 3
        else:
            members.add(c)
            i += 1
    return members


def tokens(pattern: bytes) -> list[tuple[str, object, str]]:
    """(kind, payload, quantifier) for each atom: kind any | set (payload: allowed bytes) | begin | end."""
    out, i = [], 0
    while i < len(pattern):
        c = pattern[i]
        if c in b"*+?":
            if out and out[-1][2] == "":
                out[-1] = (out[-1][0], out[-1][1], chr(c))
            i += 1
            continue
        if c == ord("^"):
            out.append(("begin", None, ""))
        elif c == ord("$"):
            out.append(("end", None, ""))
        elif c == ord("."):
            out.append(("any", None, ""))
        elif c == 92:
            if i + 1 >= len(pattern):
                break
            i += 1
            ms = _meta_set(pattern[i])
            out.append(("set", set(ms) if ms is not None else {pattern[i]}, ""))
        elif c == ord("["):
            j = pattern.find(b"]", i + 1)
            if j < 0:
                break
            body = pattern[i + 1:j]
            neg = body.startswith(b"^")
            mem = _class_members(body[1:] if neg else body)
            out.append(("set", set(range(1, 256)) - mem if neg else mem, ""))
            i = j
        else:
            out.append(("set", {c}, ""))
        i += 1
    return out


def text_for(pattern: bytes, rnd: random.Random, alphabet: bytes) -> bytes:
    """A text the pattern probably matches, with a random prefix and suffix unless anchored."""
    toks = tokens(pattern)
    body = bytearray()
    for kind, payload, q in toks:
        if kind in ("begin", "end"):
            continue
        n = {"": 1, "*": rnd.choice([0, 1, 2, 3]), "+": rnd.choice([1, 1, 2, 4]), "?": rnd.choice([0, 1])}[q]
        for _ in range(n):
            if kind == "any":
                body.append(rnd.choice(alphabet))
            else:
                choices = sorted(payload) if payload else [97]
                common = [b for b in choices if b in alphabet]
                body.append(rnd.choice(common if common and rnd.random() < 0.8 else choices))
    pre = bytes(rnd.choice(alphabet) for _ in range(rnd.choice([0, 0, 1, 3])))
    suf = bytes(rnd.choice(alphabet) for _ in range(rnd.choice([0, 0, 1, 3])))
    if toks and toks[0][0] == "begin":
        pre = b""
    if toks and toks[-1][0] == "end":
        suf = b""
    return pre + bytes(body) + suf


def mutate(text: bytes, rnd: random.Random, alphabet: bytes) -> bytes:
    t = bytearray(text)
    for _ in range(rnd.choice([1, 1, 2])):
        op = rnd.choice(["ins", "del", "sub"]) if t else "ins"
        k = rnd.randrange(len(t) + (op == "ins")) if t or op == "ins" else 0
        if op == "ins":
            t.insert(k, rnd.choice(alphabet))
        elif op == "del":
            del t[k]
        else:
            t[k] = rnd.choice(alphabet)
    return bytes(t)


def random_text(rnd: random.Random, alphabet: bytes, n: int) -> bytes:
    return bytes(rnd.choice(alphabet) for _ in range(n))


# -- random patterns ----------------------------------------------------------------------------------------------

LITERALS = b"abcxyz019AZ_- !,:;@#%&=~'\"/<>{}()|]"


def gen_class(rnd: random.Random) -> bytes:
    items = []
    for _ in range(rnd.choice([1, 1, 2, 2, 3, 4])):
        r = rnd.random()
        if r < 0.35:
            items.append(bytes([rnd.choice(LITERALS.replace(b"]", b""))]))
        elif r < 0.65:
            a, b = sorted(rnd.sample(b"0123456789abcdefghxyzABCHZ", 2))
            if rnd.random() < 0.08:
                a, b = b, a
            items.append(bytes([a, 45, b]))
        elif r < 0.85:
            items.append(b"\\" + bytes([rnd.choice(b"dDwWsS\\].-^")]))
        elif r < 0.92:
            items.append(bytes([rnd.choice(HIGH + CONTROL)]))
        else:
            items.append(b"-")
    body = b"".join(items)
    neg = b"^" if rnd.random() < 0.3 else b""
    close = b"" if rnd.random() < 0.03 else b"]"
    return b"[" + neg + body + close


def gen_atom(rnd: random.Random) -> bytes:
    r = rnd.random()
    if r < 0.33:
        return bytes([rnd.choice(LITERALS)])
    if r < 0.43:
        return b"."
    if r < 0.56:
        return b"\\" + bytes([rnd.choice(b"dDwWsS")])
    if r < 0.61:
        return b"\\" + bytes([rnd.choice(b".\\*+?[]^$an-")])
    if r < 0.79:
        return gen_class(rnd)
    if r < 0.81:
        return bytes([rnd.choice(HIGH)])
    if r < 0.83:
        return bytes([rnd.choice(CONTROL)])
    return bytes([rnd.choice(b"abc")])


def gen_pattern(rnd: random.Random) -> bytes:
    n = rnd.choice([1, 2, 2, 3, 3, 3, 4, 4, 5, 6, 8, 12])
    parts = []
    for _ in range(n):
        a = gen_atom(rnd)
        q = rnd.random()
        a += b"*" if q < 0.18 else b"+" if q < 0.33 else b"?" if q < 0.45 else b""
        if rnd.random() < 0.03:                     # a stray quantifier or anchor
            a += bytes([rnd.choice(b"*+?^$")])
        parts.append(a)
    p = b"".join(parts)
    if rnd.random() < 0.2:
        p = b"^" + p
    if rnd.random() < 0.2:
        p += b"$"
    if rnd.random() < 0.02:
        p += b"\\"
    return p


def alphabet_for(pattern: bytes, rnd: random.Random) -> bytes:
    base = bytes(b for b in pattern if b not in b"\\[]^$*+?") or b"a"
    extra = b"abc019 _-\t\n" + bytes(rnd.sample(PRINTABLE, 6))
    if rnd.random() < 0.15:
        extra += bytes(rnd.sample(HIGH, 3)) + bytes([rnd.choice(CONTROL)])
    return base + extra


def text_cap(pattern: bytes) -> int:
    """Texts stay short where backtracking is costly (the reference is an interpreter)."""
    q = sum(pattern.count(c) for c in b"*+")
    return 120 if q <= 2 else 40 if q == 3 else 16


def texts_for(pattern: bytes, rnd: random.Random, n_match: int, n_mut: int, n_rand: int) -> list[bytes]:
    alpha = alphabet_for(pattern, rnd)
    cap = text_cap(pattern)
    out = []
    for _ in range(n_match):
        out.append(text_for(pattern, rnd, alpha)[:cap])
    for _ in range(n_mut):
        out.append(mutate(text_for(pattern, rnd, alpha), rnd, alpha)[:cap])
    for _ in range(n_rand):
        out.append(random_text(rnd, alpha, rnd.choice([0, 1, 3, 6, 12]))[:cap])
    return out


# -- hand-written edge cases --------------------------------------------------------------------------------------

def edge_cases() -> list[tuple[bytes, bytes]]:
    e = []
    add = lambda p, *ts: e.extend((p, t) for t in ts)           # noqa: E731
    # anchors and quantifiers out of place; empty pattern / text; matches at the end of the text
    add(b"", b"", b"abc")
    add(b"^", b"", b"abc")
    add(b"$", b"", b"abc")
    add(b"^$", b"", b"a")
    add(b"$$", b"", b"a")
    add(b"^^a", b"a", b"^a")
    add(b"a^b", b"a^b", b"ab", b"xa^b")
    add(b"a$b", b"a$b", b"ab")
    add(b"*a", b"a", b"*a", b"ba")
    add(b"+a", b"a", b"+a")
    add(b"?a", b"a", b"?a")
    add(b"*", b"", b"*", b"a")
    add(b"+", b"+", b"a")
    add(b"?", b"", b"?", b"a")
    add(b"a**", b"aaa", b"a*", b"b")
    add(b"a*+", b"aa", b"a+")
    add(b"a+*", b"aa", b"a*")
    add(b"a??", b"", b"a", b"a?")
    add(b"a*?", b"aa", b"b")
    add(b"a?*", b"aa", b"")
    add(b"^*a", b"a", b"*a")
    add(b"^+", b"+", b"a")
    add(b"$*", b"abc", b"")
    add(b"a$*", b"a", b"ab")
    add(b"a$?", b"a", b"ab")
    add(b"a*", b"", b"b", b"aaa")
    add(b"b*", b"aaa", b"")
    add(b"a?", b"", b"b")
    add(b".*", b"", b"abc")
    add(b".+", b"", b"abc")
    add(b"a*$", b"Xaa", b"aa", b"X", b"")
    add(b"a*b", b"c", b"b", b"ab", b"cab")
    add(b"x*y*z", b"z", b"q", b"xyz")
    add(b".?a*b", b"c", b"ab")
    add(b"a+$", b"Xaa", b"aa", b"X")
    add(b"a|b", b"b", b"a|b")
    add(b"(a)", b"a", b"(a)")
    # a trailing backslash, escapes
    add(b"a\\", b"a", b"", b"ba")
    add(b"\\", b"", b"\\", b"a")
    add(b"ab\\", b"xab")
    add(b"a*\\", b"aa", b"")
    add(b"[a]\\", b"a")
    add(b"\\.", b"a.b", b"ab")
    add(b"\\\\", b"\\", b"a")
    add(b"\\*", b"*", b"a")
    add(b"\\x", b"x")
    add(b"\\n", b"n", b"\n")
    add(b"\\\xe9", b"\xe9", b"a\xe9")
    add(b"\\-", b"-")
    add(b"\\d\\d?:\\d", b"1:2", b"12:3", b"a:3")
    # classes
    add(b"[", b"[", b"a")
    add(b"[a", b"a")
    add(b"[^", b"a")
    add(b"[^]", b"a", b"]")
    add(b"[]", b"a", b"")
    add(b"[]]", b"]", b"a")
    add(b"[]a]", b"a", b"]")
    add(b"[\\]", b"\\")
    add(b"[\\]]", b"]", b"\\", b"\\]")
    add(b"[\\", b"a")
    add(b"[a-]", b"-", b"a", b"b")
    add(b"[-a]", b"-", b"a")
    add(b"[-]", b"-")
    add(b"[^-]", b"-", b"a")
    add(b"[\\-]", b"-", b"\\")
    add(b"[a-c-e]", b"d", b"-", b"b")
    add(b"[--z]", b"-", b"a")
    add(b"[z-a]", b"m", b"z", b"-")
    add(b"[a-a]", b"a", b"b")
    add(b"[\\d-z]", b"-", b"5", b"y")
    add(b"[\\w]+", b"a_1-")
    add(b"[^\\w]+", b"a_1-!")
    add(b"[.]", b".", b"a")
    add(b"[\\.]", b".", b"\\")
    add(b"[$^]", b"$", b"^")
    add(b"[*+?]+", b"*+?a")
    add(b"[\\s\\d]+", b" 1\t2x")
    add(b"[a-\xff]", b"\xe9", b"b")
    add(b"[\x80-\xff]+", b"\xe9\x80a")
    add(b"[\xe9]", b"\xe9", b"e")
    add(b"[^\xe9]", b"\xe9", b"e")
    add(b"[^a]", b"\xff", b"a")
    add(b"[\x01-\x1f]", b"\t", b" ")
    # class buffer limits (40 bytes, index 0 never used)
    for n in (36, 37, 38, 39, 40):
        add(b"[" + b"a" * n + b"]", b"a", b"b")
    add(b"[" + b"a" * 36 + b"\\d]", b"5", b"a")
    add(b"[" + b"a" * 37 + b"\\d]", b"5")
    add(b"[" + b"a" * 38 + b"\\d]", b"5")
    add(b"[" + b"a" * 18 + b"][" + b"b" * 18 + b"]", b"ab", b"ba")
    add(b"[" + b"a" * 19 + b"][" + b"b" * 19 + b"]", b"ab")
    add(b"[00000000000000000000000000000000000000][", b"0")
    # object limits (30 slots: at most 29 objects and the sentinel)
    for n in (27, 28, 29, 30, 31):
        add(b"a" * n, b"a" * n, b"a" * (n - 1), b"b" + b"a" * n)
    add(b"ab" * 15, b"ab" * 15)
    add(b"^" + b"a" * 28, b"a" * 28, b"a" * 29)
    add(b"x" * 28 + b"$", b"x" * 28, b"yx" * 2)
    add(b"a*" * 14 + b"b", b"aab", b"b")
    add(b"a?" * 14 + b"a", b"aa", b"")
    add(b"[a]" * 29, b"a" * 29)
    # bytes >= 0x80 and control characters
    add(b"\xe9", b"\xe9", b"a\xe9")
    add(b"a\xe9", b"a\xe9")
    add(b".", b"\xe9", b"\n", b"\r")
    add(b"\\w", b"\xe9")
    add(b"\\W", b"\xe9")
    add(b"\\d", b"\xb2")
    add(b"\\D", b"\xb2")
    add(b"\\s", b"\x0b", b"\x0c", b"\x1c", b"\xa0", b"\x85")
    add(b"\\S", b"\xa0")
    add(b"[\\s]", b"\x0c")
    add(b"\x01", b"\x01")
    add(b"\x7f", b"\x7f")
    add(b"a.c", b"a\nc")
    add(b"\\S+", b"\xff\xfe")
    add(b"\xff*", b"\xff\xff", b"a")
    add(b"\xff+", b"\xff")
    # longer texts
    add(b".*a", b"b" * 100 + b"a")
    add(b"a+b", b"a" * 100)
    add(b"[a-z]+[0-9]+", b"abc" * 30 + b"1")
    add(b"\\s*x$", b" " * 80 + b"x")
    add(b"b.\\s*\n", b"aa\r\nbb\r\ncc\r\n\r\n")
    return e


# -- assembling the sets ------------------------------------------------------------------------------------------

def _case(cid: str, source: str, pattern: bytes, text: bytes, **extra) -> dict:
    if 0 in pattern or 0 in text:
        raise ValueError(f"{cid}: a C string cannot hold a 0 byte")
    return {"id": cid, "source": source, "pattern": pattern.hex(), "text": text.hex(), **extra}


def build(seed: int, n_gen: int, with_fixed: bool) -> list[dict]:
    rnd = random.Random(seed)
    out, seen = [], set()

    def add(cid, source, p, t, **extra):
        if (p, t) in seen:
            return
        seen.add((p, t))
        out.append(_case(cid, source, p, t, **extra))

    if with_fixed:
        for k, v in enumerate(test1_vectors()):
            add(f"test1-{k + 1}", "test1", v["pattern"], v["text"], project_expect=v["project_expect"])
        for k, p in enumerate(compile_vectors()):
            for t in (b"", b"a", b"\x01[^\\\xff]"):
                add(f"compile-{k + 1}-{t.hex() or 'empty'}", "compile", p, t)
        for k, (p, t) in enumerate(edge_cases()):
            add(f"edge-{k + 1}", "edge", p, t)
    for k, (script, p) in enumerate(makefile_patterns()):
        for j, t in enumerate(texts_for(p, rnd, 3, 1, 2)):
            add(f"makefile-s{seed}-{k + 1}-{j + 1}", "makefile", p, t, script=script)
    k = 0
    while k < n_gen:
        p = gen_pattern(rnd)
        if 0 in p:
            continue
        k += 1
        for j, t in enumerate(texts_for(p, rnd, 1, 1, 1)):
            add(f"gen-s{seed}-{k}-{j + 1}", "gen", p, t)
    return out


def main(argv: list[str]) -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    sets = {"round": build(1, 800, True), "heldout": build(2, 900, False)}
    rkeys = {(c["pattern"], c["text"]) for c in sets["round"]}
    sets["heldout"] = [c for c in sets["heldout"] if (c["pattern"], c["text"]) not in rkeys]
    for name, cases in sets.items():
        (OUT / f"{name}.json").write_text(json.dumps(cases, indent=0))
        by = {}
        for c in cases:
            by[c["source"]] = by.get(c["source"], 0) + 1
        print(name, len(cases), by, len({c["pattern"] for c in cases}), "patterns")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

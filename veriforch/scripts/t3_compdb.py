#!/usr/bin/env python3
"""Pre-registration T, step T3 (PREREG_T_v1): the compile commands of Thrift's C and C++ libraries at any revision,
by the rules of T1's hand-made ones (scratch/thrift_cxx/tools/mk_compdb.py, w-thrift-cxx, at f0eb8b84).

T1 read the TU lists off lib/cpp/CMakeLists.txt and lib/c_glib/CMakeLists.txt (as data) for a Linux build with every
optional dependency found (OpenSSL, libevent, zlib), Qt absent, WIN32 files out and the default options. Here the
same reading is mechanical, so that every revision gets the TU list of its own CMakeLists.txt (files added and
removed in a range are handled):
* the revision's CMakeLists.txt is read with `git show REV:PATH` (data only; nothing of the tree runs);
* its set / list(APPEND|REMOVE_ITEM|REMOVE_DUPLICATES) / if-elseif-else-endif commands are evaluated under the fixed
  configuration TRUTH below (three-valued: a condition with any other variable, a TARGET test, a comparison... is
  unknown). A variable set under an unknown condition is unknown, and so is every variable computed from it; a
  library call under an unknown condition or over an unknown variable, an unknown command, or an executed
  add_subdirectory stops the generator (fail closed: a person decides and the rule is extended here);
* the TUs are the .c/.cc/.cpp/.cxx sources of the ADD_LIBRARY_THRIFT calls that run, for the libraries of LIBS
  (lib/cpp: thrift, thriftnb, thriftz; lib/c_glib: thrift_c_glib, thrift_c_glib_zlib), in CMake order, each once;
* flags, the notional build directory, the config dir (the hand-written thrift/config.h) and the system headers
  (deps/thrift_headers) are T1's, unchanged at every revision: "the pinned flags" of PREREG_T_v1 T3.
Paths in the entries are those of the clone at the pin (targets/thrift): `vo ci` re-roots them onto each
materialised revision (veriforch.ci.materialise, adapters/cir/compdb.py).

    t3_compdb.py gen REPO REV LIB OUT.json      LIB: cpp or c_glib; prints the TU count
    t3_compdb.py tus REPO REV LIB               the TU paths (relative to the repository root), one per line
    t3_compdb.py selftest REPO PIN T1_DIR       at the pin, the entries equal T1's files in T1_DIR: for cpp the four
                                                lib/cpp component files together, for c_glib thrift_c_glib (exit 1
                                                otherwise)
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

T = Path("/home/user/veriforch/targets/thrift")
H = Path("/home/user/veriforch/deps/thrift_headers")
CONF = Path("/home/user/veriforch/targets/thrift_cpp_config")
B = Path("/home/user/veriforch/scratch/thrift_cxx/build")
CXX = "/home/user/cirlean_work/toolchain/upstream-4955d32b/bin/clang++"
CC = "/home/user/cirlean_work/toolchain/upstream-4955d32b/bin/clang"
GLOBAL_DEFS = ["-D__STDC_FORMAT_MACROS", "-D__STDC_LIMIT_MACROS"]
SYS_CXX = ["-isystem", str(H / "boost/include"), "-isystem", str(H / "libevent/include"),
           "-isystem", str(H / "openssl/include"), "-isystem", str(H / "openssl/include_arch"),
           "-isystem", str(H / "zlib/include")]
SYS_C = ["-isystem", str(H / "glib-2.0/include/glib-2.0"), "-isystem", str(H / "glib-2.0/lib_include"),
         "-isystem", str(H / "openssl/include"), "-isystem", str(H / "openssl/include_arch"),
         "-isystem", str(H / "zlib/include")]
LIB_FLAGS = {
    "cpp": (["-std=c++11", "-g", "-Wall", "-Wextra", "-Wno-deprecated-register"] + GLOBAL_DEFS
            + ["-DTHRIFT_STATIC_DEFINE", f"-I{T / 'lib/cpp/src'}", f"-I{CONF}"] + SYS_CXX),
    "c_glib": ["-g", "-Wall", "-Wextra"] + GLOBAL_DEFS + [f"-I{T / 'lib/c_glib/src'}", f"-I{CONF}"] + SYS_C,
}
COMPILER = {"cpp": CXX, "c_glib": CC}
BUILDDIR = {"cpp": B / "lib/cpp", "c_glib": B / "lib/c_glib"}
LIBDIR = {"cpp": "lib/cpp", "c_glib": "lib/c_glib"}
LIBS = {"cpp": {"thrift", "thriftnb", "thriftz"}, "c_glib": {"thrift_c_glib", "thrift_c_glib_zlib"}}
T1_FILES = {"cpp": ["thrift_cpp_protocol", "thrift_cpp_transport", "thrift_cpp_server", "thrift_cpp_other"],
            "c_glib": ["thrift_c_glib"]}
SRC_EXT = (".c", ".cc", ".cpp", ".cxx")

# T1's configuration: Linux (UNIX, not WIN32/WINCE/MSVC/MINGW/CYGWIN/APPLE/ANDROID); OpenSSL, libevent and zlib found
# and their options on (their CMAKE_DEPENDENT_OPTION defaults when found); Qt4 and Qt5 absent; the thread library
# options at their defaults (WITH_BOOSTTHREADS and WITH_STDTHREADS OFF: build/cmake/DefineOptions.cmake, 2017-2019);
# static libraries (BUILD_SHARED_LIBS off: THRIFT_STATIC_DEFINE); no tests
TRUTH = {"UNIX": True, "WIN32": False, "WINCE": False, "MSVC": False, "MINGW": False, "CYGWIN": False,
         "APPLE": False, "ANDROID": False, "OPENSSL_FOUND": True, "WITH_OPENSSL": True, "Libevent_FOUND": True,
         "WITH_LIBEVENT": True, "ZLIB_FOUND": True, "WITH_ZLIB": True, "QT4_FOUND": False, "WITH_QT4": False,
         "Qt5_FOUND": False, "WITH_QT5": False, "WITH_BOOSTTHREADS": False, "WITH_STDTHREADS": False,
         "BUILD_SHARED_LIBS": False, "BUILD_TESTING": False}
# commands that do not change a TU list (flags, include paths and link lines are T1's, whatever these say)
NOOP = {"include_directories", "target_link_libraries", "install", "find_package", "include", "add_definitions",
        "add_pkgconfig_thrift", "target_link_libraries_thrift", "target_link_libraries_thrift_against_thrift_library",
        "link_against_thrift_library", "require_boost_headers", "message", "set_target_properties",
        "target_include_directories", "target_compile_definitions", "add_dependencies", "cmake_minimum_required"}
TRUE_CONST = {"ON", "YES", "TRUE", "Y", "1"}
FALSE_CONST = {"OFF", "NO", "FALSE", "N", "0", "IGNORE", "NOTFOUND", ""}


class Fail(Exception):
    """The rules do not decide this revision (fail closed)."""


def git_show(repo: Path, rev: str, path: str) -> str | None:
    p = subprocess.run(["git", "-C", str(repo), "show", f"{rev}:{path}"], capture_output=True)
    return p.stdout.decode("utf-8", "replace") if p.returncode == 0 else None


# ---------------------------------------------------------------------------------------------- CMake reading
def parse(text: str) -> list[tuple[str, list[tuple[str, bool]], int]]:
    """CMake commands: (lower-case name, [(argument, quoted)], line). Parentheses inside an argument list are
    arguments of their own (as in if conditions); comments and bracket comments are dropped."""
    out, i, n, line = [], 0, len(text), 1

    def skip_comment(i: int) -> int:
        m = re.match(r"#\[(=*)\[", text[i:])
        if m:
            end = text.find("]" + m.group(1) + "]", i)
            if end < 0:
                raise Fail("unterminated bracket comment")
            return end + len(m.group(1)) + 2
        j = text.find("\n", i)
        return n if j < 0 else j

    while i < n:
        c = text[i]
        if c == "\n":
            line += 1
            i += 1
            continue
        if c.isspace():
            i += 1
            continue
        if c == "#":
            j = skip_comment(i)
            line += text.count("\n", i, j)
            i = j
            continue
        m = re.match(r"[A-Za-z_][A-Za-z0-9_]*", text[i:])
        if not m:
            raise Fail(f"line {line}: unexpected text {text[i:i + 30]!r}")
        name, start_line = m.group(0), line
        i += len(name)
        while i < n and text[i] in " \t":
            i += 1
        if i >= n or text[i] != "(":
            raise Fail(f"line {line}: `{name}` without an argument list")
        i += 1
        depth, args = 1, []
        while True:
            if i >= n:
                raise Fail(f"line {start_line}: unterminated `{name}(`")
            c = text[i]
            if c == "\n":
                line += 1
                i += 1
            elif c.isspace():
                i += 1
            elif c == "#":
                j = skip_comment(i)
                line += text.count("\n", i, j)
                i = j
            elif c == "(":
                args.append(("(", False))
                depth += 1
                i += 1
            elif c == ")":
                depth -= 1
                i += 1
                if depth == 0:
                    break
                args.append((")", False))
            elif c == '"':
                j, buf = i + 1, []
                while j < n and text[j] != '"':
                    if text[j] == "\\" and j + 1 < n:
                        nxt = text[j + 1]
                        if nxt == "\n":             # line continuation
                            line += 1
                        else:
                            buf.append({"n": "\n", "t": "\t", "r": "\r", ";": "\\;"}.get(nxt, nxt))
                        j += 2
                        continue
                    if text[j] == "\n":
                        line += 1
                    buf.append(text[j])
                    j += 1
                if j >= n:
                    raise Fail(f"line {start_line}: unterminated quoted argument")
                args.append(("".join(buf), True))
                i = j + 1
            else:
                mb = re.match(r"\[(=*)\[", text[i:])
                if mb:
                    end = text.find("]" + mb.group(1) + "]", i)
                    if end < 0:
                        raise Fail(f"line {start_line}: unterminated bracket argument")
                    body = text[i + len(mb.group(0)):end]
                    line += body.count("\n")
                    args.append((body, True))
                    i = end + len(mb.group(1)) + 2
                    continue
                j = i
                while j < n and not text[j].isspace() and text[j] not in '()#"':
                    if text[j] == "\\" and j + 1 < n:
                        j += 2
                        continue
                    if text[j] == "$" and text[j + 1:j + 2] == "{":      # ${VAR} (no nesting in these files)
                        k = text.find("}", j)
                        if k < 0:
                            raise Fail(f"line {line}: unterminated variable reference")
                        j = k + 1
                        continue
                    j += 1
                args.append((text[i:j], False))
                i = j
        out.append((name.lower(), args, start_line))
    return out


def expand(args: list[tuple[str, bool]], env: dict[str, list[str]]) -> tuple[list[str], set[str]]:
    """Variable references: an unquoted argument that is exactly ${VAR} becomes the list's elements (none when
    empty or unset); anywhere else ${VAR} is replaced by the list joined with ';' (an unquoted result is split at
    ';'). An undefined variable is empty, as in CMake. Also returns the names referenced."""
    out, refs = [], set()
    for a, quoted in args:
        refs |= set(re.findall(r"\$\{([A-Za-z0-9_.+-]+)\}", a))
        m = re.fullmatch(r"\$\{([A-Za-z0-9_.+-]+)\}", a)
        if m and not quoted:
            out += list(env.get(m.group(1), []))
            continue
        s = re.sub(r"\$\{([A-Za-z0-9_.+-]+)\}", lambda mm: ";".join(env.get(mm.group(1), [])), a)
        if "${" in s or "$ENV{" in s or "$<" in s:
            raise Fail(f"unsupported reference in {a!r}")
        out += [s] if quoted else [x for x in s.split(";") if x != ""]
    return out, refs


def cond_value(tokens: list[str]):
    """Three-valued `if` condition (True, False, None = unknown) over TRUTH. Supported: NOT, AND, OR, parentheses,
    constants, variable names; anything else (TARGET, DEFINED, EXISTS, comparisons, ...) is unknown."""
    pos = 0

    def peek():
        return tokens[pos] if pos < len(tokens) else None

    def atom():
        nonlocal pos
        t = peek()
        if t is None:
            raise Fail("empty condition")
        if t == "(":
            pos += 1
            v = disj()
            if peek() != ")":
                raise Fail(f"unbalanced parentheses in {tokens}")
            pos += 1
            return v
        if t.upper() in ("TARGET", "DEFINED", "EXISTS", "COMMAND", "POLICY", "IS_DIRECTORY", "IS_ABSOLUTE"):
            pos += 2
            return None
        pos += 1
        nxt = peek()
        if nxt is not None and nxt.upper() in ("STREQUAL", "EQUAL", "LESS", "GREATER", "MATCHES", "VERSION_LESS",
                                               "VERSION_GREATER", "VERSION_EQUAL", "STRLESS", "STRGREATER",
                                               "LESS_EQUAL", "GREATER_EQUAL", "VERSION_LESS_EQUAL",
                                               "VERSION_GREATER_EQUAL", "IN_LIST"):
            pos += 2
            return None
        if t.upper() in TRUE_CONST:
            return True
        if t.upper() in FALSE_CONST or t.upper().endswith("-NOTFOUND"):
            return False
        return TRUTH.get(t)

    def neg():
        nonlocal pos
        if peek() is not None and peek().upper() == "NOT":
            pos += 1
            v = neg()
            return None if v is None else not v
        return atom()

    def conj():
        nonlocal pos
        vals = [neg()]
        while peek() is not None and peek().upper() == "AND":
            pos += 1
            vals.append(neg())
        return False if False in vals else (None if None in vals else True)

    def disj():
        nonlocal pos
        vals = [conj()]
        while peek() is not None and peek().upper() == "OR":
            pos += 1
            vals.append(conj())
        return True if True in vals else (None if None in vals else False)

    v = disj()
    if pos != len(tokens):
        raise Fail(f"cannot read condition {tokens}")
    return v


def libraries(text: str, libdir: str) -> list[tuple[str, list[str]]]:
    """The ADD_LIBRARY_THRIFT calls that run under TRUTH: (library, sources as written)."""
    env: dict[str, list[str]] = {}
    unknown: set[str] = set()               # variables whose value the T3 configuration does not decide
    frames: list[dict] = []                 # per open if: own branch state and whether a branch was taken
    libs = []

    def state() -> str:
        if any(f["state"] == "off" for f in frames):
            return "off"
        if any(f["state"] == "unknown" for f in frames):
            return "unknown"
        return "on"

    for name, args, line in parse(text):
        if name == "if":
            v = cond_value([a for a, _ in args] if args else [""])
            frames.append({"state": {True: "on", False: "off", None: "unknown"}[v], "taken": v, "line": line})
            continue
        if name in ("elseif", "else"):
            if not frames:
                raise Fail(f"line {line}: {name} outside if")
            f = frames[-1]
            if f["taken"] is True:
                f["state"] = "off"
            elif f["taken"] is None:
                f["state"] = "unknown"
            else:
                v = True if name == "else" else cond_value([a for a, _ in args])
                f["state"] = {True: "on", False: "off", None: "unknown"}[v]
                f["taken"] = v
            continue
        if name == "endif":
            if not frames:
                raise Fail(f"line {line}: endif outside if")
            frames.pop()
            continue
        st = state()
        if st == "off" or name in NOOP:
            continue
        if name not in ("set", "list", "add_library_thrift", "add_subdirectory"):
            raise Fail(f"{libdir}/CMakeLists.txt line {line}: command `{name}` is not in the T3 rules")
        vals, refs = expand(args, env)
        if st == "unknown" or refs & unknown:
            if name in ("set", "list") and vals[0:1] and (name == "set" or len(vals) > 1):
                unknown.add(vals[0] if name == "set" else vals[1])
                continue
            raise Fail(f"{libdir}/CMakeLists.txt line {line}: `{name}` "
                       + ("under a condition the T3 rules do not decide" if st == "unknown"
                          else f"over variables the T3 rules do not decide ({sorted(refs & unknown)})"))
        if name == "set":
            if not vals:
                raise Fail(f"line {line}: set() without a variable")
            var, rest = vals[0], vals[1:]
            if "CACHE" in rest:
                rest = rest[:rest.index("CACHE")]
            if rest[-1:] == ["PARENT_SCOPE"]:
                rest = rest[:-1]
            env[var] = rest
            unknown.discard(var)
        elif name == "list":
            op, var, rest = vals[0].upper(), vals[1], vals[2:]
            if op == "APPEND":
                env[var] = env.get(var, []) + rest
            elif op == "REMOVE_ITEM":
                env[var] = [x for x in env.get(var, []) if x not in rest]
            elif op == "REMOVE_DUPLICATES":
                seen: set[str] = set()
                env[var] = [x for x in env.get(var, []) if not (x in seen or seen.add(x))]
            else:
                raise Fail(f"line {line}: list({op}) is not in the T3 rules")
        elif name == "add_library_thrift":
            libs.append((vals[0], vals[1:]))
        else:
            raise Fail(f"{libdir}/CMakeLists.txt line {line}: add_subdirectory({' '.join(vals)}) runs under the T3 "
                       f"configuration")
    if frames:
        raise Fail(f"{libdir}/CMakeLists.txt: if at line {frames[-1]['line']} has no endif")
    return libs


def tus(repo: Path, rev: str, lib: str) -> list[str]:
    """The library's TUs at REV (paths relative to the repository root), in CMake order, each once."""
    libdir = LIBDIR[lib]
    text = git_show(repo, rev, f"{libdir}/CMakeLists.txt")
    if text is None:
        raise Fail(f"no {libdir}/CMakeLists.txt at {rev}")
    out: list[str] = []
    for libname, srcs in libraries(text, libdir):
        if libname not in LIBS[lib]:
            raise Fail(f"{libdir}/CMakeLists.txt builds library {libname!r} under the T3 configuration (not in the "
                       f"T3 rules: {sorted(LIBS[lib])})")
        for s in srcs:
            rel = f"{libdir}/{s}"
            if rel.endswith(SRC_EXT) and rel not in out:
                out.append(rel)
    if not out:
        raise Fail(f"{libdir}/CMakeLists.txt at {rev}: no TU")
    return out


def entries(rel_tus: list[str], lib: str) -> list[dict]:
    db = []
    for rel in rel_tus:
        src = T / rel
        db.append({"directory": str(BUILDDIR[lib]), "file": str(src),
                   "arguments": [COMPILER[lib], *LIB_FLAGS[lib], "-c", str(src), "-o", src.name + ".o"]})
    return db


def selftest(repo: Path, pin: str, t1_dir: Path) -> int:
    bad = 0
    for lib in ("cpp", "c_glib"):
        mine = entries(tus(repo, pin, lib), lib)
        t1 = []
        for f in T1_FILES[lib]:
            t1 += json.loads((t1_dir / f"{f}.compile_commands.json").read_text())
        key = lambda e: e["file"]
        same_set = sorted(mine, key=key) == sorted(t1, key=key)
        same_order = lib != "c_glib" or mine == t1          # c_glib is one file: the order must match as well
        print(f"{lib}: {len(mine)} TUs here, {len(t1)} in T1 ({', '.join(T1_FILES[lib])}): "
              f"{'identical entries' if same_set else 'DIFFERENT'}"
              + ("" if same_order else " (order differs)"))
        if not (same_set and same_order):
            bad += 1
            mf, tf = {e["file"] for e in mine}, {e["file"] for e in t1}
            for x in sorted(mf - tf):
                print(f"  only here: {x}")
            for x in sorted(tf - mf):
                print(f"  only in T1: {x}")
            for e in mine:
                o = next((x for x in t1 if x["file"] == e["file"]), None)
                if o is not None and o != e:
                    print(f"  entry differs: {e['file']}")
    return 1 if bad else 0


def main(argv: list[str]) -> int:
    if len(argv) >= 1 and argv[0] == "gen" and len(argv) == 5:
        repo, rev, lib, out = Path(argv[1]), argv[2], argv[3], Path(argv[4])
        db = entries(tus(repo, rev, lib), lib)
        out.write_text(json.dumps(db, indent=1) + "\n")
        print(f"{lib} at {rev}: {len(db)} TUs -> {out}")
        return 0
    if len(argv) >= 1 and argv[0] == "tus" and len(argv) == 4:
        print("\n".join(tus(Path(argv[1]), argv[2], argv[3])))
        return 0
    if len(argv) >= 1 and argv[0] == "selftest" and len(argv) == 4:
        return selftest(Path(argv[1]), argv[2], Path(argv[3]))
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except Fail as e:
        print(f"t3_compdb: {e}", file=sys.stderr)
        sys.exit(3)

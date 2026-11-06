"""C/C++ build: sources -> ClangIR (.cir) -> Lean (cir2lean) -> units and call graph."""
from __future__ import annotations

import json
import os
import re
import subprocess
from pathlib import Path

from ...lean import RUN1, VO_ROOT, LeanPackage, Requirement
from ...model import Target, Unit, Variant, sha256
from ..base import Build, _ident

# The pinned cirlean. Override with VO_CIRLEAN_DIR / VO_CIRLEAN_PIN (patch runs use the pin equiv-lean was
# built against: see CERT_CIRLEAN in patch.py).
CIRLEAN = Path(os.environ.get("VO_CIRLEAN_DIR", str(VO_ROOT / "deps" / "cirlean-59da897")))
CIRLEAN_PIN = os.environ.get("VO_CIRLEAN_PIN", "59da897")
TOOLCHAIN = Path("/home/user/cirlean_work/toolchain/upstream-4955d32b")
CLANG = TOOLCHAIN / "bin" / "clang"
CIR2LEAN = CIRLEAN / ".lake/build/bin/cir2lean"
CIRSCAN = CIRLEAN / ".lake/build/bin/cirscan"
CIRRUN = CIRLEAN / ".lake/build/bin/cirrun"

_FUNC_RE = re.compile(r"^\s*cir\.func\b(?P<attrs>[^@]*)@(?P<name>[\w.$]+)\(")
_CALL_RE = re.compile(r"cir\.(?:try_)?call @([\w.$]+)\(")
_LOCDEF_RE = re.compile(r'^#(loc\d+) = loc\("(?P<file>[^"]+)":(?P<line>\d+):(?P<col>\d+)\)')
_LOCREF_RE = re.compile(r"loc\((?:fused\[)?#(loc\d+)")
_LOCLIT_RE = re.compile(r'loc\("(?P<file>[^"]+)":(?P<line>\d+):(?P<col>\d+)\)')
_FUSED_RE = re.compile(r"^#(loc\d+) = loc\(fused\[#(loc\d+)")


VO_CIRRUN_SRC = VO_ROOT / "tools" / "vo_cirrun" / "VoCirRun.lean"


def vo_cirrun() -> Path:
    """veriforch's runner for linked programs (tools/vo_cirrun: cirlean's cirrun plus `cir2lean --link`'s linking),
    built once per cirlean pin under runs/_tools against the pinned cirlean (nothing is written into the pin)."""
    import fcntl
    src = VO_CIRRUN_SRC.read_text()
    tdir = VO_ROOT / "runs" / "_tools" / ("vo_cirrun_" + re.sub(r"\W", "_", CIRLEAN_PIN))
    exe = tdir / ".lake" / "build" / "bin" / "vo-cirrun"
    want = sha256(src + "\n" + str(CIRLEAN))[:16]
    stamp = tdir / ".vo_built"
    if exe.exists() and stamp.exists() and stamp.read_text() == want:
        return exe
    tdir.mkdir(parents=True, exist_ok=True)
    with open(tdir / ".lock", "w") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)              # one build per pin, also across processes
        if exe.exists() and stamp.exists() and stamp.read_text() == want:
            return exe
        (tdir / "VoCirRun.lean").write_text(src)
        (tdir / "lakefile.toml").write_text(f'name = "vo_cirrun"\n\n[[require]]\nname = "cirlean"\npath = "{CIRLEAN}"\n\n'
                                            '[[lean_exe]]\nname = "vo-cirrun"\nroot = "VoCirRun"\n')
        (tdir / "lean-toolchain").write_text("leanprover/lean4:v4.35.0\n")
        p = run_tool(["lake", "build", "vo-cirrun"], tdir, timeout=1800, core_h=0.7)
        if p.returncode != 0 or not exe.exists():
            raise RuntimeError(f"building vo-cirrun failed:\n{p.stdout[-3000:]}")
        stamp.write_text(want)
    return exe


def run_tool(cmd: list[str], cwd: Path, timeout: int = 600, core_h: float = 0.1) -> subprocess.CompletedProcess:
    from ...lean import _run
    full = [str(RUN1), "-t", str(timeout), "-c", str(core_h), "--", *cmd]
    return _run(full, cwd, timeout + 60)


def lean_package(run_dir: Path, revision: str | None = None) -> LeanPackage:
    req = Requirement("cirlean", str(CIRLEAN), CIRLEAN_PIN, ["CIR"])
    # a pin chosen by environment gets its own package directory: two runs of one target on different pins would
    # otherwise rewrite each other's lakefile and compiled Gen modules (compiled .oleans come back from the
    # content-addressed cache, whose keys include the bridge fingerprint)
    pkg_dir = run_dir / ("lean" if "VO_CIRLEAN_PIN" not in os.environ else f"lean_{_ident(CIRLEAN_PIN)}")
    if revision is not None:
        # modular builds name their modules without the revision (so an unchanged function has byte-identical
        # modules in every revision and its compiled proof is reused from the cache); each revision then needs
        # its own package directory (beside the non-modular package, not inside it)
        pkg_dir = pkg_dir.with_name(pkg_dir.name + "_rev") / _ident(revision)
    return LeanPackage(pkg_dir, "vo_" + _ident(run_dir.name), [req], ["Gen", "VO"], run_dir / "cache" / "olean")


def build(target: Target, variant: Variant, run_dir: Path) -> Build:
    """Compile the target's sources as one unity translation unit and translate it to Lean."""
    vdir = run_dir / target.version / variant.name
    vdir.mkdir(parents=True, exist_ok=True)
    root = Path(target.root)
    sources = variant.sources or target.sources
    if link_enabled(target, sources):
        return _build_linked(target, variant, run_dir, sources)
    is_cxx = any(s.endswith((".cpp", ".cc", ".cxx", ".hpp")) for s in sources)
    unity_text = "".join(f'#include "{(root / s).as_posix()}"\n' for s in sources) + target.extra.get("unity_suffix", "")
    # clang names the ClangIR module after its input's absolute path, and cir2lean copies that name into the generated
    # Lean text (part of the module's cache key): the unity file lives in the run directory's cache, resolved and under
    # a name derived from its text, so that worker slots (runs/<target>_w<k>, cache/ a symlink to the main run
    # directory's cache) compile the same path and share the compiled module
    udir = (run_dir / "cache" / "unity").resolve() / sha256(unity_text)[:16]
    udir.mkdir(parents=True, exist_ok=True)
    unity = udir / ("vo_unity.cpp" if is_cxx else "vo_unity.c")
    if not unity.exists() or unity.read_text() != unity_text:
        tmp = unity.with_name(f"{unity.name}.{os.getpid()}.tmp")
        tmp.write_text(unity_text)
        tmp.replace(unity)
    cir = vdir / "unit.cir"
    cmd = [str(CLANG if not is_cxx else TOOLCHAIN / "bin" / "clang++")]
    if is_cxx:
        cmd += ["-std=c++20"] + target.extra.get("cxxflags", [])
    cmd += [f"-I{root / i}" for i in target.include] + variant.flags + target.extra.get("cflags", [])
    cmd += ["-fclangir", "-emit-cir", "-Xclang", "-fno-clangir-call-conv-lowering", str(unity), "-o", cir.name]
    p = run_tool(cmd, vdir, timeout=300)
    if p.returncode != 0 or not cir.exists():
        raise RuntimeError(f"clang -fclangir failed for {target.name}/{variant.name}:\n{p.stdout[-3000:]}")
    modular = modular_enabled(target)
    pkg = lean_package(run_dir, target.version if modular else None)
    gen_mod = (f"Gen.{_ident(variant.name)}.Unit" if modular
               else f"Gen.{_ident(target.version)}_{_ident(variant.name)}.Unit")
    gen_path = pkg.src(gen_mod)
    gen_path.parent.mkdir(parents=True, exist_ok=True)
    info = {"cir": str(cir), "gen_module": gen_mod, "gen_ns": gen_mod, "unity": str(unity)}
    if modular:
        # one module per function (`cir2lean --modular`): a proof imports only its own function, so an edit
        # re-checks the edited function's proof and nothing else (callers see the callee's contract only).
        # The .cir path is passed relative (cwd = vdir): cir2lean writes it into each module's header comment.
        info["ns"] = f"VO.{_ident(variant.name)}"
        p = run_tool([str(CIR2LEAN), "--modular", cir.name, gen_mod, str(pkg.dir)], vdir, timeout=300)
        man_path = pkg.dir / Path(*gen_mod.split(".")) / "manifest.json"
        if p.returncode != 0 or not gen_path.exists() or not man_path.exists():
            raise RuntimeError(f"cir2lean --modular failed:\n{p.stdout[-3000:]}")
        man = json.loads(man_path.read_text())
        fmods = {f["sym"]: f["module"] for f in man["functions"]}
        gen_text = "\n".join(pkg.src(m).read_text() for m in fmods.values())
        info.update({"modular": fmods, "modular_proofs": True, "types_module": man["types"],
                     "modular_decl": {f["sym"]: f["lean"].rsplit(".", 1)[-1] for f in man["functions"]},
                     "modular_lib": [f["sym"] for f in man["functions"] if f["model"] or not f["body"]],
                     "gen_order": [man["types"], *fmods.values(), gen_mod]})
    else:
        # the .cir by name (cwd = vdir), as in the modular branch: cir2lean writes it into the module's header comment
        p = run_tool([str(CIR2LEAN), cir.name, gen_mod, str(gen_path)], vdir, timeout=300)
        if p.returncode != 0 or not gen_path.exists():
            raise RuntimeError(f"cir2lean failed:\n{p.stdout[-3000:]}")
        gen_text = gen_path.read_text()
    scan = run_tool([str(CIRSCAN), str(cir)], vdir, timeout=300)
    if scan.returncode != 0:          # fail closed: an unreadable scan must not leave every unit in scope
        raise RuntimeError(f"cirscan failed (exit {scan.returncode}):\n{scan.stdout[-2000:]}")
    info["scan"] = scan.stdout
    units = extract_units(cir.read_text(), scan.stdout, gen_text, target)
    return Build(target=target, variant=variant, dir=vdir, pkg=pkg, units=units, info=info)


def link_enabled(target: Target, sources: list[str]) -> bool:
    """Several translation units compiled separately and linked by `cir2lean --link` (target option
    `link_mode = "cir2lean"`, or VO_CIR_LINK=1/0 to override); otherwise they are included into one unity file."""
    env = os.environ.get("VO_CIR_LINK")
    on = env == "1" if env in ("0", "1") else target.extra.get("link_mode") == "cir2lean"
    return on and len(sources) > 1


def _build_linked(target: Target, variant: Variant, run_dir: Path, sources: list[str]) -> Build:
    """Each source is compiled to ClangIR with its own recorded flags, and `cir2lean --link` links the units into
    one program: an external symbol resolves to its definition (or a library model), and the internal (static)
    symbols of a unit become `<unit>$<sym>`. The result has the per-function layout of `--modular` (Types, one
    module per function, the top module with `module` and `ctx`, manifest.json). Units come from each unit's IR
    (locations, bodies, scope) under their linked names; callees come from the linked manifest, so calls across
    translation units are ordinary calls."""
    vdir = run_dir / target.version / variant.name
    vdir.mkdir(parents=True, exist_ok=True)
    root = Path(target.root)
    stems = [Path(s).stem for s in sources]
    if len(set(stems)) != len(stems):
        raise ValueError(f"linked sources need distinct file names: {sources}")
    per_file = target.extra.get("compdb_flags") or {}
    cirs = []
    for s, stem in zip(sources, stems):
        is_cxx = s.endswith((".cpp", ".cc", ".cxx"))
        cir = vdir / f"{stem}.cir"
        cmd = [str(CLANG if not is_cxx else TOOLCHAIN / "bin" / "clang++")]
        if is_cxx:
            cmd += ["-std=c++20"] + target.extra.get("cxxflags", [])
        cmd += [f"-I{root / i}" for i in target.include] + per_file.get(s, variant.flags) + target.extra.get("cflags", [])
        cmd += ["-fclangir", "-emit-cir", "-Xclang", "-fno-clangir-call-conv-lowering", str(root / s), "-o", str(cir)]
        p = run_tool(cmd, vdir, timeout=300)
        if p.returncode != 0 or not cir.exists():
            raise RuntimeError(f"clang -fclangir failed for {target.name}/{variant.name}/{s}:\n{p.stdout[-3000:]}")
        cirs.append(cir)
    modular = modular_enabled(target)
    pkg = lean_package(run_dir, target.version if modular else None)
    gen_mod = (f"Gen.{_ident(variant.name)}.Unit" if modular
               else f"Gen.{_ident(target.version)}_{_ident(variant.name)}.Unit")
    pkg.src(gen_mod).parent.mkdir(parents=True, exist_ok=True)
    p = run_tool([str(CIR2LEAN), "--link", gen_mod, str(pkg.dir), *[c.name for c in cirs]], vdir, timeout=600)
    man_path = pkg.dir / Path(*gen_mod.split(".")) / "manifest.json"
    if p.returncode != 0 or not man_path.exists():
        raise RuntimeError(f"cir2lean --link failed:\n{p.stdout[-3000:]}")
    man = json.loads(man_path.read_text())
    fmods = {f["sym"]: f["module"] for f in man["functions"]}
    by_sym = {f["sym"]: f for f in man["functions"]}
    info = {"cir": str(cirs[0]), "cirs": [str(c) for c in cirs], "gen_module": gen_mod, "gen_ns": gen_mod,
            "linked": True, "modular": fmods, "modular_proofs": modular, "types_module": man["types"],
            "modular_decl": {f["sym"]: f["lean"].rsplit(".", 1)[-1] for f in man["functions"]},
            "modular_lib": [f["sym"] for f in man["functions"] if f["model"] or not f["body"]],
            "gen_order": [man["types"], *fmods.values(), gen_mod]}
    if modular:
        info["ns"] = f"VO.{_ident(variant.name)}"
    gen_text = "\n".join(pkg.src(m).read_text() for m in fmods.values())
    units, scans = [], []
    for cir, stem in zip(cirs, stems):
        scan = run_tool([str(CIRSCAN), str(cir)], vdir, timeout=300)
        if scan.returncode != 0:      # fail closed, as in the unity branch
            raise RuntimeError(f"cirscan failed on {cir.name} (exit {scan.returncode}):\n{scan.stdout[-2000:]}")
        scans.append(scan.stdout)
        for u in extract_units(cir.read_text(), scan.stdout, gen_text, target):
            sym = f"{stem}${u.sym}" if f"{stem}${u.sym}" in by_sym else u.sym
            if sym not in by_sym or any(x.sym == sym for x in units):
                continue                   # not in the linked program, or a duplicate definition kept once
            if sym != u.sym:
                u.name = sym               # a renamed internal symbol: unique across the program
            u.sym = sym
            u.lean_decl = by_sym[sym]["lean"].rsplit(".", 1)[-1]
            units.append(u)
    # cirscan runs per unit: a call to a function defined in ANOTHER unit of the program is "external" there; after
    # linking it is an ordinary call, so such a unit is in scope when every external callee it named is resolved
    resolved = {s for s, f in by_sym.items() if f["body"] or f["model"]}
    ext_of: dict[tuple[str, str], list[str]] = {}
    for cir, stem, scan_text in zip(cirs, stems, scans):
        for line in scan_text.splitlines():
            cols = line.split("\t")
            if len(cols) >= 5 and cols[0].endswith(".cir") and cols[3] == "external":
                ext_of[(stem, cols[1])] = [c for c in cols[4].split(",") if c]
    for u, stem in [(u, s) for s in stems for u in units if u.loc and Path(u.loc.split(":")[0]).stem == s]:
        orig = u.sym.split("$", 1)[1] if "$" in u.sym else u.sym
        ext = ext_of.get((stem, orig))
        if u.scope.startswith("gap:external") and ext is not None:
            missing = [c for c in ext if c not in resolved]
            # in scope when the link resolves every external callee; otherwise named by the callees still missing
            u.scope = "in_scope" if not missing else "gap:external:" + ",".join(missing)
    names = {u.sym for u in units}
    for u in units:
        calls = by_sym[u.sym]["callees"]
        u.callees = [c for c in calls if c in names and c != u.sym] + ([u.sym] if u.sym in calls else [])
        sig = u.signature if isinstance(u.signature, dict) else {}
        sig["externals"] = [c for c in calls if c not in names]
        u.signature = sig
    info["scan"] = "\n".join(scans)
    return Build(target=target, variant=variant, dir=vdir, pkg=pkg, units=units, info=info)


def modular_enabled(target: Target) -> bool:
    """Per-function Gen modules: target option `modular = true`, or VO_CIR_MODULAR=1/0 to override."""
    env = os.environ.get("VO_CIR_MODULAR")
    return env == "1" if env in ("0", "1") else bool(target.extra.get("modular", False))


_STRDEF_RE = re.compile(r'^\s*cir\.global\b.*?(@"\.str(?:\.\d+)?"|@\.str(?:\.\d+)?)\s*=\s*(.*?)\s*(?:align\(|loc\(|$)')
_STRREF_RE = re.compile(r'@"\.str(?:\.\d+)?"|@\.str(?:\.\d+)?\b')


def _literal_names(cir_text: str) -> dict[str, str]:
    """String-literal globals (`@".str.23"`) are numbered in order of appearance in the translation unit, so adding
    a literal anywhere renumbers the others. Map each name to a name derived from its contents, for body hashes
    that change only when a function's own code or the literals it uses change."""
    out = {}
    for line in cir_text.splitlines():
        m = _STRDEF_RE.match(line)
        if m:
            out[m.group(1)] = "@str_" + sha256(m.group(2))[:12]
    return out


def extract_units(cir_text: str, scan_text: str, gen_text: str, target: Target) -> list[Unit]:
    locs: dict[str, tuple[str, int]] = {}
    fused: dict[str, str] = {}
    for line in cir_text.splitlines():
        m = _LOCDEF_RE.match(line)
        if m:
            locs[m.group(1)] = (m.group("file"), int(m.group("line")))
            continue
        m = _FUSED_RE.match(line)
        if m:
            fused[m.group(1)] = m.group(2)

    def resolve(ref: str, depth: int = 0):
        if ref in locs:
            return locs[ref]
        if ref in fused and depth < 8:
            return resolve(fused[ref], depth + 1)
        return None
    funcs: dict[str, dict] = {}
    cur = None
    for line in cir_text.splitlines():
        m = _FUNC_RE.match(line)
        if m:
            name = m.group("name")
            cur = {"name": name, "attrs": m.group("attrs"), "lines": [line], "calls": [],
                   "decl_only": line.rstrip().endswith(")") or "{" not in line}
            funcs[name] = cur
            lr = _LOCREF_RE.search(line[line.find("(") :])
            cur["loc"] = resolve(lr.group(1)) if lr else None
            if target.extra.get("loc_from_definition"):
                # an out-of-line C++ member's line carries its definition as an inline loc("file":line:col) literal;
                # the first loc(#ref) is the in-class declaration (D2 fix for the not-emitted family, 10-25)
                li = _LOCLIT_RE.search(line[line.find("(") :])
                if li:
                    cur["loc"] = (li.group("file"), int(li.group("line")))
            if cur["decl_only"]:
                cur = None
            continue
        if cur is not None:
            cur["lines"].append(line)
            for c in _CALL_RE.findall(line):
                if c not in cur["calls"]:
                    cur["calls"].append(c)
            if line.startswith("  }"):
                if cur.get("loc") is None:
                    lr = _LOCREF_RE.search(line)
                    cur["loc"] = resolve(lr.group(1)) if lr else None
                cur = None
    scope: dict[str, str] = {}
    for line in scan_text.splitlines():
        cols = line.split("\t")
        if len(cols) >= 6 and cols[0].endswith(".cir"):
            status, unknown = cols[3], cols[5]
            if status == "external" and not unknown:
                unknown = cols[4]          # the missing callees name the gap (prereg D defect (i))
            scope[cols[1]] = "in_scope" if status == "in_scope" else f"gap:{status}:{unknown}".rstrip(":")
    gen_decls = set(re.findall(r"^def (fn_\w+) : FuncDecl", gen_text, re.M))
    lits = _literal_names(cir_text)
    demangled = {m.group(2): m.group(3) for m in re.finditer(
        r'^def (fn_\w+) : FuncDecl where\n  sym := "([^"]*)"\n  demangled := "([^"]*)"', gen_text, re.M)}
    user = set(scope)
    units = []
    root = str(Path(target.root).resolve())
    library = target.extra.get("include_library", False)
    for name, f in funcs.items():
        if f["decl_only"]:
            continue
        floc = f.get("loc")
        if not library:
            if user and name not in user and demangled.get(name) not in user:
                continue    # not a user function per cirscan (library code instantiated into the TU)
            if floc and not str(Path(floc[0]).resolve()).startswith(root):
                continue    # defined outside the target tree
        decl = "fn_" + re.sub(r"\W", "_", name)
        if decl not in gen_decls:
            # cir2lean names functions after their demangled name; fall back to a search by symbol
            m = re.search(r'^def (fn_\w+) : FuncDecl where\n  sym := "' + re.escape(name) + '"', gen_text, re.M)
            decl = m.group(1) if m else decl
        body = "\n".join(_strip_locs(l) for l in f["lines"])
        body = _STRREF_RE.sub(lambda mm: lits.get(mm.group(0), mm.group(0)), body)
        loc = f.get("loc")
        static = "internal" in f["attrs"] or "private" in f["attrs"]
        kind = "internal" if static else "api"
        if target.entry:
            kind = "api" if name in target.entry else "internal"
        u = Unit(name=name, sym=name, lean_decl=decl, kind=kind,
                 callees=[c for c in f["calls"] if c in funcs and not funcs[c]["decl_only"]
                          and (library or ((not user or c in user or demangled.get(c) in user)
                               and (not funcs[c].get("loc")
                                    or str(Path(funcs[c]["loc"][0]).resolve()).startswith(root))))],
                 scope=scope.get(name, scope.get(demangled.get(name, ""), "in_scope")),
                 loc=f"{loc[0]}:{loc[1]}" if loc else "", body_hash=sha256(body)[:16])
        u.signature = {"externals": [c for c in f["calls"] if c not in funcs or funcs[c]["decl_only"]],
                       "demangled": demangled.get(name, name)}
        u.source = c_source(loc) if loc else ""
        if "TEST_IGNORE" in u.source:
            u.scope = "gap:ignored_test"   # a Unity test marked ignored bails out by design: no test theorem
        units.append(u)
    return units


def _strip_locs(line: str) -> str:
    return re.sub(r"\s*loc\([^)]*\)", "", line)


def c_source(loc: tuple[str, int], max_lines: int = 400) -> str:
    """The source text of the function starting at `loc` (signature line to the matching brace)."""
    path, line = loc
    p = Path(path)
    if not p.is_absolute():
        return ""
    try:
        lines = p.read_text(errors="replace").splitlines()
    except OSError:
        return ""
    start = line - 1
    # walk back to the start of the declaration (return type may be on the previous line)
    while start > 0 and lines[start - 1].strip() and not lines[start - 1].rstrip().endswith((";", "}", "*/")) \
            and not lines[start - 1].lstrip().startswith(("#", "//")):
        start -= 1
    depth, out, seen = 0, [], False
    for l in lines[start : start + max_lines]:
        out.append(l)
        depth += l.count("{") - l.count("}")
        seen = seen or "{" in l
        if seen and depth <= 0:
            break
    return "\n".join(out)

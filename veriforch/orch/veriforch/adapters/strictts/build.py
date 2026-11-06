"""TypeScript build: sources -> StrictTS subset check -> Lean IR (translator) -> units and call graph.

The translator translates a whole program or nothing, so files that fail the subset check are left out
and their functions become gap units (with the rule ids of the diagnostics inside them). The remaining
files are translated together, in one Lean module per build.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
from pathlib import Path

from ...lean import RUN1, VO_ROOT, LeanPackage, Requirement
from ...model import Target, Unit, Variant, sha256
from ..base import Build, _ident

# The pinned StrictTS. Override with VO_STRICTTS_DIR / VO_STRICTTS_PIN (a run with an override gets its own
# package directory, as for cirlean).
STRICTTS = Path(os.environ.get("VO_STRICTTS_DIR", str(VO_ROOT / "deps" / "strictts")))
STRICTTS_PIN = os.environ.get("VO_STRICTTS_PIN", "9870429")
CLI = STRICTTS / "frontend" / "dist" / "cli.js"
NODE_PATH = STRICTTS / "frontend" / "node_modules"
LIST_FUNCTIONS = Path(__file__).parent / "list_functions.js"
EXTRACT_TESTS = Path(__file__).parent / "extract_tests.js"
VO_EXPECT = Path(__file__).parent / "vo_expect.ts"
_SPEC_RE = re.compile(r"\.(spec|test)\.tsx?$")
# functions of vo_expect.ts: scaffolding of the test statements (their meaning is part of each test theorem,
# documented in extract_tests.js), so they are not units of their own
HELPER_FUNS = ("vo_check", "vo_is_num", "vo_eq_num_arr", "vo_close")

_DIAG_RE = re.compile(r"^(?P<file>[^:\s]+\.tsx?):(?P<line>\d+):(?P<col>\d+) \[(?P<rule>[\w-]+)\] (?P<msg>.*)$")
_REF_RE = re.compile(r'^def «?(?P<ref>\w+?Ref)»? : FunRef (?P<args>.*?) (?P<ret>\S+|\(.*\)) := ⟨(?P<idx>\d+), "(?P<name>[^"]+)"⟩', re.M)
_DEF_RE = re.compile(r"^def «?(?P<def>\w+?Def)»? : FunDef TT where\n(?P<body>(?:(?!^def |^theorem |^abbrev |^/--).*\n)*)", re.M)
_CALL_RE = re.compile(r"\.call «?(\w+?Ref)»?")


def run_tool(cmd: list[str], cwd: Path, timeout: int = 300, core_h: float = 0.1, mem: int = 16) -> subprocess.CompletedProcess:
    full = [str(RUN1), "-t", str(timeout), "-m", str(mem), "-c", str(core_h), "--", *cmd]
    env = dict(os.environ, VO_ROOT=str(VO_ROOT), NODE_PATH=str(NODE_PATH))
    return subprocess.run(full, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                          timeout=timeout + 60, env=env)


def lean_package(run_dir: Path) -> LeanPackage:
    req = Requirement("strictts", str(STRICTTS), STRICTTS_PIN, ["StrictTS"])
    # StrictTS's large import closure needs a big address-space cap or Lean cannot create threads
    pkg_dir = run_dir / ("lean" if "VO_STRICTTS_PIN" not in os.environ else f"lean_{_ident(STRICTTS_PIN)}")
    return LeanPackage(pkg_dir, "vo_" + _ident(run_dir.name), [req], ["Gen", "VO"],
                       run_dir / "cache" / "olean", mem_gib=128)


def list_functions(root: Path, files: list[str], cwd: Path) -> list[dict]:
    p = run_tool(["node", str(LIST_FUNCTIONS), *[str(root / f) for f in files]], cwd, timeout=120)
    if p.returncode != 0:
        raise RuntimeError(f"list_functions failed: {p.stderr[-2000:]}")
    funcs = json.loads(p.stdout)
    # overload signatures have no body; keep the implementation
    best: dict[tuple[str, str], dict] = {}
    for f in funcs:
        k = (f["file"], f["name"])
        if k not in best or (f["hasBody"] and not best[k]["hasBody"]):
            best[k] = f
    return list(best.values())


_MODE: list[str] = []


def _mode() -> list[str]:
    """The subset mode of the build in progress (set by `build`), for the generated test files' check."""
    return list(_MODE)


def check_file(root: Path, rel: str, cwd: Path, mode: list[str] | None = None) -> list[dict]:
    """Subset diagnostics of one file (with its imports): [] when it is in the subset. `mode` ["--strict"]: StrictTS's
    strict subset (unknown and any rejected, no dyn values) instead of the default checked-dynamic one."""
    p = run_tool(["node", str(CLI), *(mode or []), "--check", str(root / rel)], cwd, timeout=120)
    if p.returncode == 0:
        return []
    diags = []
    for line in (p.stderr + "\n" + p.stdout).splitlines():
        m = _DIAG_RE.match(line.strip())
        if m:
            diags.append({"file": m.group("file"), "line": int(m.group("line")), "rule": m.group("rule"),
                          "msg": m.group("msg")})
    if not diags:
        diags.append({"file": rel, "line": 0, "rule": f"exit{p.returncode}", "msg": (p.stderr or p.stdout)[-300:]})
    return diags


def test_cases(root: Path, specs: list[str], diags: dict[str, list[dict]], vdir: Path) -> tuple[Path, list[dict]]:
    """The vitest cases of `specs` as generated StrictTS-subset files (extract_tests.js: one file per case, the
    expectations rewritten into throwing checks), each subset-checked. A case is a gap when the rewrite does
    not cover it, when its own file is outside the subset, or when it imports a source file outside it."""
    tdir = vdir / "vo_tests"
    tdir.mkdir(parents=True, exist_ok=True)
    for old in tdir.glob("vo_test_*.ts"):
        old.unlink()
    p = run_tool(["node", str(EXTRACT_TESTS), str(tdir), *[str(root / s) for s in specs]], vdir, timeout=300)
    if p.returncode != 0:
        raise RuntimeError(f"extract_tests failed: {p.stderr[-2000:]}")
    cases = json.loads(p.stdout)
    (tdir / "vo_expect.ts").write_text(VO_EXPECT.read_text())
    for c in cases:
        if not c["gap"]:
            (tdir / f"{c['name']}.ts").write_text(c["text"])
    todo = [c for c in cases if not c["gap"]]
    bad_files: dict[str, set[str]] = {}
    if todo:
        # one subset check over all cases; diagnostics name their files (a case's own file or a source it imports)
        q = run_tool(["node", str(CLI), *_mode(), "--check", "vo_expect.ts", *[f"{c['name']}.ts" for c in todo]], tdir,
                     timeout=600, core_h=0.2)
        for line in (q.stderr + "\n" + q.stdout).splitlines():
            m = _DIAG_RE.match(line.strip())
            if m:
                bad_files.setdefault(str((tdir / m.group("file")).resolve()), set()).add(m.group("rule"))
        if q.returncode != 0 and not bad_files:
            raise RuntimeError(f"subset check of the generated tests failed: {(q.stderr or q.stdout)[-1500:]}")
    if str((tdir / "vo_expect.ts").resolve()) in bad_files:
        raise RuntimeError(f"vo_expect.ts is outside the StrictTS subset: {bad_files}")
    src_bad = {str((root / rel).resolve()): sorted({d["rule"] for d in ds}) for rel, ds in diags.items() if ds}
    for c in todo:
        own = bad_files.get(str((tdir / f"{c['name']}.ts").resolve()))
        imp = [Path(f).name for f in c.get("imports", []) if str(Path(f).resolve()) in src_bad
               or str(Path(f).resolve()) in bad_files]
        if own:
            c["gap"] = "subset:" + ",".join(sorted(own))
        elif imp:
            c["gap"] = "imports a file outside the subset: " + ", ".join(imp)
    (vdir / "test_cases.json").write_text(json.dumps([{k: v for k, v in c.items() if k != "text"} for c in cases],
                                                    indent=1))
    return tdir, cases


_PARAMS_RE = re.compile(r"\(([^()]*)\)")


def _param_names(sig: str) -> list[str]:
    """Parameter names of a signature `name(a: T, b?: U, ...rest: V[]): R` (the translator's doc line or a
    declaration's first line); type annotations with brackets or generics are skipped by depth counting."""
    i = sig.find("(")
    if i < 0:
        return []
    depth, cur, out = 0, "", []
    for ch in sig[i + 1:]:
        if ch in "([{<":
            depth += 1
        elif ch in ")]}>":
            if depth == 0:
                break
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    names = []
    for part in out:
        if re.match(r"\s*(?:\.\.\.)?\s*[{\[]", part):
            names.append(None)                  # a destructured parameter: the translator names it itself
            continue
        m = re.match(r"\s*(?:\.\.\.)?\s*(?:public |private |protected |readonly )*([A-Za-z_$][\w$]*)", part)
        if m and m.group(1) != "this":
            names.append(m.group(1))
    return names


def _same_params(src: list, doc: list) -> bool:
    return len(src) == len(doc) and all(a is None or b is None or a == b for a, b in zip(src, doc))


def build_coverage(target: Target, variant: Variant, run_dir: Path) -> Build:
    """Extraction by StrictTS's own coverage mode (`--coverage --emit-lean`, the tool behind StrictTS's public coverage
    rows): one unit per coverage row (file, line, name, kind). A covered row whose function the emitted module
    contains is in scope; a covered row the module does not contain (a generic function without an instance, or one
    the partial translation leaves out) is `gap:not-emitted`; a blocked row is `gap:subset:<rules>`.

    The emitted module names its functions but not their files. The translator registers the covered units in row
    order (generic ones register nothing) and numbers repeated names `f`, `f_2`, ... in that order
    (frontend/src/partial.ts, core.ts leanName), so the k-th registered covered row named `f` is `f_k`. Every such
    pairing is checked against the translator's signature line (the parameter names); a row that fails the check is
    `gap:unmapped` (none in the runs so far).

    Target options: `extraction = "coverage"`, `coverage_project` (StrictTS's tools/public/tsconfig/<name>.json is
    the tsconfig, written next to the project's tsconfig.json with typeRoots at the pinned StrictTS), `strict`."""
    vdir = run_dir / target.version / variant.name
    vdir.mkdir(parents=True, exist_ok=True)
    root = Path(target.root)
    mode = ["--strict"] if target.extra.get("strict") else []
    name = target.extra["coverage_project"]
    label = f"{name}_{'strict' if mode else 'dyn'}"
    tmpl = json.loads((STRICTTS / "tools" / "public" / "tsconfig" / f"{name}.json").read_text())
    tmpl.setdefault("compilerOptions", {})["typeRoots"] = [str(STRICTTS / "frontend" / "node_modules" / "@types")]
    cfg_text = json.dumps(tmpl, indent=2) + "\n"
    cfg = root / "tsconfig.strictts.json"
    if not cfg.exists() or cfg.read_text() != cfg_text:
        cfg.write_text(cfg_text)
    tree = sorted(q for q in root.rglob("*.ts") if "node_modules" not in q.parts)
    fe_key = sha256(json.dumps([STRICTTS_PIN, "coverage", mode, label, cfg_text,
                                [(str(q.relative_to(root)), sha256(q.read_text(errors="replace"))) for q in tree]]))
    fe_path = run_dir / "cache" / "frontend" / f"{fe_key}.json"
    if fe_path.exists():
        fe = json.loads(fe_path.read_text())
    else:
        rep, lean = vdir / f"{label}.coverage.json", vdir / f"Cov_{_ident(label)}.lean"
        p = run_tool(["node", str(CLI), "--coverage", *mode, "-p", str(cfg), "--report", str(rep), "--label", label,
                      "--emit-lean", str(lean)], root, timeout=int(target.extra.get("translate_timeout", 1800)),
                     core_h=0.6)
        if p.returncode != 0 or not rep.exists() or not lean.exists():
            raise RuntimeError(f"StrictTS coverage failed:\n{(p.stderr or p.stdout)[-3000:]}")
        rows = json.loads(rep.read_text())["rows"]
        files = sorted({r["file"] for r in rows})
        sts = vdir / f"Cov_{_ident(label)}.funs.json"   # StrictTS >= 44d6b9b: its own list of emitted functions
        fe = {"rows": rows, "lean": lean.read_text(), "funcs": list_functions(root, files, vdir),
              "stdout": p.stdout[-4000:], "sts_funs": json.loads(sts.read_text()) if sts.exists() else None}
        fe_path.parent.mkdir(parents=True, exist_ok=True)
        tmp = fe_path.with_name(fe_path.name + f".{os.getpid()}.tmp")
        tmp.write_text(json.dumps(fe))
        tmp.replace(fe_path)
    rows, lean_text, funcs = fe["rows"], fe["lean"], fe["funcs"]
    sts_funs = fe.get("sts_funs")
    if sts_funs is None and (vdir / f"Cov_{_ident(label)}.funs.json").exists():
        sts_funs = json.loads((vdir / f"Cov_{_ident(label)}.funs.json").read_text())
    # StrictTS's own record of what it emitted, by source position: the Lean name of each emitted function and, for a
    # generic one, `generic: true` with its type arguments `inst` (older pins write no such file)
    sts_by_src = {(f.get("file"), f.get("line")): f for f in (sts_funs or []) if isinstance(f, dict)}
    ns = re.search(r"^namespace (\S+)", lean_text, re.M).group(1)
    refs = {}
    for m in re.finditer(r'(?:^/-- `(?P<doc>[^`]*)` -/\n)?^def «?(?P<lean>\w+?)Ref»? : FunRef (?P<args>.*?) '
                         r'(?P<ret>\S+|\(.*\)) := ⟨(?P<idx>\d+), "(?P<js>[^"]*)"⟩', lean_text, re.M):
        refs[m.group("lean")] = m.groupdict()
    defs = {}
    for m in _DEF_RE.finditer(lean_text):
        defs[m.group("def")[:-3]] = m.group(0)
    by_src = {}
    for f in funcs:
        fp = Path(f["file"])                         # absolute in older StrictTS, relative to the project in >= 44d6b9b
        rel = str(fp.resolve().relative_to(root.resolve())) if fp.is_absolute() else str(fp)
        by_src[(rel, f["line"])] = f
    # the registration order of the covered units -> their Lean names
    used: set[str] = set()
    lean_of: dict[int, str] = {}
    unmapped: set[int] = set()
    generic_of: dict[int, object] = {}               # row index -> instantiation of an emitted generic

    def lean_name(base: str) -> str:
        b = re.sub(r"[^A-Za-z0-9_]", "_", base)
        if not re.match(r"[A-Za-z_]", b):
            b = "_" + b
        n, k = b, 2
        while n in used:
            n, k = f"{b}_{k}", k + 1
        used.add(n)
        return n
    for i, r in enumerate(rows):
        if r["status"] != "covered":
            continue
        src = by_src.get((r["file"], r["line"]))
        text = (src or {}).get("text", "")
        kind = r["kind"]
        # A StrictTS that emits generic functions at fixed type arguments marks them in its funs.json (generic: true,
        # `inst`: the type arguments, e.g. {"T": "number"}; StrictTS >= 44d6b9b); older pins emit nothing for a generic. An emitted instance is found by its JS name
        # among the registered references, in registration order.
        sf = sts_by_src.get((r["file"], r["line"])) or {}
        inst = (sf.get("inst") or sf.get("instantiation")) if sf.get("generic") else None
        if sf.get("generic"):
            generic_of[i] = inst
        if kind == "function":
            if re.match(r"(?:export\s+)?(?:default\s+)?(?:async\s+)?function\s*\*?\s*[\w$]*\s*<", text):
                if not sf.get("generic"):
                    continue                                 # generic, not emitted: registers nothing
            base = r["name"]
        elif kind in ("arrow", "handler"):
            if re.search(r"=\s*(?:async\s*)?<", text.split("=>")[0]):
                if not sf.get("generic"):
                    continue
            base = r["name"]
        elif kind == "constructor":
            base = r["name"].split(".")[0] + "_new"
        elif kind == "method":
            cls, m = r["name"].split(".", 1)
            base = f"{cls}_static_{m}" if re.search(r"\bstatic\s+" + re.escape(m) + r"\b", text) else f"{cls}_{m}"
        elif kind == "accessor":
            cls, rest = r["name"].split(".", 1)
            gs, m = rest.split(" ", 1)
            base = f"{cls}_{gs}_{m}"
        else:
            continue
        if sf.get("lean") in refs:
            # StrictTS >= 44d6b9b names each emitted function's Lean definition in funs.json (a generic instance:
            # `difference_number` for difference<number>): use it rather than the registration-order reconstruction
            ln = sf["lean"]
            used.add(ln)
        elif i in generic_of:
            continue                                 # a generic the funs.json does not name: not emitted
        else:
            ln = lean_name(base)
        if ln in refs:
            doc = refs[ln].get("doc") or ""
            src_names = _param_names(text) if text else None
            doc_names = _param_names(doc) if doc else None
            if src_names is not None and doc_names is not None and not _same_params(src_names, doc_names):
                unmapped.add(i)
            else:
                lean_of[i] = ln
    names = [r["name"] for r in rows]
    dup = {n for n in names if names.count(n) > 1}
    unit_of = {i: (r["name"] if r["name"] not in dup else f"{r['name']}@{r['file']}:{r['line']}") for i, r in enumerate(rows)}
    name_of_lean = {ln: unit_of[i] for i, ln in lean_of.items()}
    pkg = lean_package(run_dir)
    gen_mod = f"Gen.{_ident(target.version)}_{_ident(variant.name)}.Unit"
    gen_path = pkg.src(gen_mod)
    gen_path.parent.mkdir(parents=True, exist_ok=True)
    gen_path.write_text(add_helpers(lean_text))
    units: list[Unit] = []
    for i, r in enumerate(rows):
        src = by_src.get((r["file"], r["line"]))
        loc = f"{root / r['file']}:{r['line']}"
        uname = unit_of[i]
        if i in lean_of:
            ln = lean_of[i]
            dtext = defs.get(ln, "")
            callees = []
            for c in _CALL_RE.findall(dtext):
                cn = name_of_lean.get(c[:-3])
                if cn and cn != uname and cn not in callees:
                    callees.append(cn)
            u = Unit(name=uname, sym=ln + "Ref", lean_decl=ln + "Def", kind="api", callees=callees, scope="in_scope",
                     loc=loc, body_hash=sha256(dtext)[:16], source=(src or {}).get("text", ""))
            rf = refs[ln]
            u.signature = {"ref": ln + "Ref", "def": ln + "Def", "call": ln + "_call", "args": rf["args"],
                           "ret": rf["ret"], "index": int(rf["idx"]), "row": {k: r[k] for k in ("file", "line", "name",
                                                                                                 "kind")}}
            if i in generic_of:
                u.signature["instance"] = generic_of[i] if generic_of[i] is not None else "generic (instantiation "\
                                                                                          "not reported)"
        else:
            if r["status"] == "covered":
                scope = "gap:unmapped" if i in unmapped else "gap:not-emitted"
            elif r["status"] == "blocked":
                scope = "gap:subset:" + ",".join(sorted(r.get("rules", {})))
            else:
                scope = "gap:" + str(r["status"])
            u = Unit(name=uname, sym=_ident(uname) + "Ref", lean_decl=_ident(uname) + "Def", kind="api", callees=[],
                     scope=scope, loc=loc, body_hash=sha256(json.dumps(r, sort_keys=True))[:16],
                     source=(src or {}).get("text", ""))
            u.signature = {"row": {k: r[k] for k in ("file", "line", "name", "kind")}}
        units.append(u)
    (vdir / "coverage_mapping.json").write_text(json.dumps(
        {"emitted_units": len(lean_of), "unmapped": [unit_of[i] for i in sorted(unmapped)],
         "lean_of": {unit_of[i]: ln for i, ln in lean_of.items()}}, indent=1))
    helpers = [h for h in HELPER_FUNS if re.search(rf"^def «?{h}Def»? :", lean_text, re.M)]
    return Build(target=target, variant=variant, dir=vdir, pkg=pkg, units=units,
                 info={"gen_module": gen_mod, "gen_ns": ns, "extraction": "coverage", "coverage_label": label,
                       "test_cases": 0, "test_helpers": helpers})


def build(target: Target, variant: Variant, run_dir: Path) -> Build:
    if target.extra.get("extraction") == "coverage":
        return build_coverage(target, variant, run_dir)
    vdir = run_dir / target.version / variant.name
    vdir.mkdir(parents=True, exist_ok=True)
    root = Path(target.root)
    # a variant may list spec files among its sources, or take the target's `tests` with the flag "tests"
    # target option `strict = true`: StrictTS's strict subset (`--strict`: unknown/any rejected, no dyn values) for the
    # subset check and the translation; the default is the checked-dynamic subset
    mode = ["--strict"] if target.extra.get("strict") else []
    global _MODE
    _MODE = mode
    listed = list(variant.sources or target.sources)
    sources = [s for s in listed if not _SPEC_RE.search(s)]
    specs = [s for s in listed if _SPEC_RE.search(s)] or (list(target.tests) if "tests" in variant.flags else [])
    # front-end cache (no tests): the subset diagnostics, function list and translation are a function of the pin
    # and the library's sources, so a later build of the same tree (e.g. one `vo verify --only` per unit in a
    # pre-registered study) reuses them instead of re-running the per-file checks
    fe_key = fe_path = None
    if not specs:
        tree = sorted(q for q in root.rglob("*.ts") if "node_modules" not in q.parts)
        fe_key = sha256(json.dumps([STRICTTS_PIN, mode, target.version, variant.name, sources,
                                    [(str(q.relative_to(root)), sha256(q.read_text(errors="replace"))) for q in tree]]))
        fe_path = run_dir / "cache" / "frontend" / f"{fe_key}.json"
    fe = json.loads(fe_path.read_text()) if fe_path is not None and fe_path.exists() else None
    if fe is not None:
        funcs, diags = fe["funcs"], fe["diags"]
    else:
        funcs = list_functions(root, sources, vdir)
        diags = {rel: check_file(root, rel, vdir, mode) for rel in sources}
    ok_files = [rel for rel, d in diags.items() if not d]
    cases: list[dict] = []
    extra_files: list[Path] = []
    if specs:
        tdir, cases = test_cases(root, specs, diags, vdir)
        ok_cases = [c for c in cases if not c["gap"]]
        if ok_cases:
            extra_files = [tdir / "vo_expect.ts"] + [tdir / f"{c['name']}.ts" for c in ok_cases]
            funcs += list_functions(tdir, [f.name for f in extra_files], vdir)
    pkg = lean_package(run_dir)
    gen_mod = f"Gen.{_ident(target.version)}_{_ident(variant.name)}.Unit"
    gen_path = pkg.src(gen_mod)
    gen_path.parent.mkdir(parents=True, exist_ok=True)
    gen_text = ""
    if ok_files and fe is not None:
        gen_text = fe["gen"]
        gen_path.write_text(add_helpers(gen_text))
    elif ok_files:
        p = run_tool(["node", str(CLI), *mode, "--namespace", gen_mod, "-o", str(gen_path),
                      *[str(root / f) for f in ok_files], *[str(f) for f in extra_files]], vdir,
                     timeout=int(target.extra.get("translate_timeout", 300)))
        if p.returncode != 0 or not gen_path.exists():
            raise RuntimeError(f"StrictTS translation failed:\n{p.stderr[-3000:]}")
        gen_text = gen_path.read_text()
        gen_path.write_text(add_helpers(gen_text))
    if fe_path is not None and fe is None:
        fe_path.parent.mkdir(parents=True, exist_ok=True)
        tmp = fe_path.with_name(fe_path.name + f".{os.getpid()}.tmp")
        tmp.write_text(json.dumps({"funcs": funcs, "diags": diags, "gen": gen_text}))
        tmp.replace(fe_path)
    units = extract_units(gen_text, funcs, diags, target, root)
    if specs:
        units = test_units(units, cases, gen_text)
    (vdir / "subset_diagnostics.json").write_text(json.dumps(diags, indent=1))
    helpers = [h for h in HELPER_FUNS if re.search(rf"^def «?{h}Def»? :", gen_text, re.M)]
    return Build(target=target, variant=variant, dir=vdir, pkg=pkg, units=units,
                 info={"gen_module": gen_mod, "gen_ns": gen_mod, "translated": ok_files, "diagnostics": diags,
                       "test_cases": len(cases), "test_helpers": helpers})


def test_units(units: list[Unit], cases: list[dict], gen_text: str) -> list[Unit]:
    """Test cases become units of kind `test` (located at their `it(...)` line in the spec); the vo_expect
    helpers are dropped from the units and from the call graph (each test theorem includes their meaning)."""
    by_name = {c["name"]: c for c in cases}
    out = []
    for u in units:
        if u.name in HELPER_FUNS:
            continue
        u.callees = [c for c in u.callees if c not in HELPER_FUNS]
        c = by_name.get(u.name)
        if c is not None:
            u.kind = "test"
            u.loc = f"{c['spec']}:{c['line']}"
            u.source = c["text"]
            if isinstance(u.signature, dict):
                u.signature["test_title"] = c["title"]
        out.append(u)
    have = {u.name for u in out}
    for c in cases:
        if c["name"] not in have:
            out.append(Unit(name=c["name"], sym=c["name"] + "Ref", lean_decl=c["name"] + "Def", kind="test",
                            callees=[], scope="gap:test:" + (c["gap"] or "not emitted"),
                            loc=f"{c['spec']}:{c['line']}", body_hash=sha256(c["title"] + (c["gap"] or ""))[:16],
                            source=c.get("text") or c["title"]))
    return out


HELPERS = r"""
/-! verif-orchestrator proof helpers (appended by veriforch adapters/strictts/build.py; not translator output). -/
open Lean Elab Tactic Meta in
/-- Case-split on the condition of an `if-then-else` in the goal (a closed condition, so data-dependent
branches split even under the `match`es of the interpreter, where `split` picks the outer `match`). -/
elab "vo_split_ite" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let some e := goal.find? (fun e => e.isAppOfArity ``ite 5 && !(e.getArg! 1).hasLooseBVars && !(e.getArg! 1).hasMVar)
    | throwError "vo_split_ite: no closed if-then-else condition in the goal"
  let c ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| by_cases hvo : $c <;> simp only [hvo, ↓reduceIte] at ⊢))
"""


def add_helpers(gen_text: str) -> str:
    """Append the helper tactics; `import Lean` goes next to the translator's import."""
    if "vo_split_ite" in gen_text:
        return gen_text
    text = gen_text.replace("import StrictTS.Frontend.Prelude", "import StrictTS.Frontend.Prelude\nimport Lean", 1)
    return text.rstrip("\n") + "\n" + HELPERS


def extract_units(gen_text: str, funcs: list[dict], diags: dict[str, list[dict]], target: Target,
                  root: Path) -> list[Unit]:
    refs = {m.group("name"): m.groupdict() for m in _REF_RE.finditer(gen_text)}
    defs = {}
    for m in _DEF_RE.finditer(gen_text):
        nm = re.search(r'^\s*name := "([^"]+)"', m.group("body"), re.M)
        if nm:
            defs[nm.group(1)] = (m.group("def"), m.group(0))
    ref_to_name = {d["ref"]: n for n, d in refs.items()}
    by_src = {(Path(f["file"]).resolve(), f["name"]): f for f in funcs}
    units: list[Unit] = []
    for name, r in refs.items():
        dname, dtext = defs.get(name, (name + "Def", ""))
        callees = []
        for c in _CALL_RE.findall(dtext):
            cn = ref_to_name.get(c)
            if cn and cn != name and cn not in callees:
                callees.append(cn)
        src = next((f for (p, n), f in by_src.items() if n == name), None)
        exported = bool(src and src["exported"])
        kind = ("api" if name in target.entry else "internal") if target.entry else ("api" if exported else "internal")
        loc = f"{src['file']}:{src['line']}" if src else ""
        u = Unit(name=name, sym=r["ref"], lean_decl=dname, kind=kind, callees=callees, scope="in_scope",
                 loc=loc, body_hash=sha256(dtext)[:16], source=src["text"] if src else "")
        # the call lemma is named after the reference (a generic instance `f<T>` has `f_rec1Ref`, `f_rec1_call`)
        u.signature = {"ref": r["ref"], "def": dname, "call": r["ref"][:-3] + "_call", "args": r["args"], "ret": r["ret"],
                       "index": int(r["idx"])}
        units.append(u)
    done = {u.name for u in units}
    # functions of translated files that the translator did not emit (generic functions are specialised
    # at their call sites; a generic with no instantiation in the program has no definition)
    for rel, ds in diags.items():
        if ds:
            continue
        path = (root / rel).resolve()
        for (p, n), f in by_src.items():
            if p != path or n in done or not f["hasBody"]:
                continue
            generic = re.match(r"(export\s+)?function\s+\w+\s*<", f["text"]) is not None
            exported = f["exported"]
            kind = ("api" if n in target.entry else "internal") if target.entry else ("api" if exported else "internal")
            units.append(Unit(name=n, sym=n + "Ref", lean_decl=n + "Def", kind=kind, callees=[],
                              scope="gap:not-emitted" + (":generic-without-instance" if generic else ""),
                              loc=f"{f['file']}:{f['line']}", body_hash=sha256(f["text"])[:16], source=f["text"]))
            done.add(n)
    # functions of files outside the subset: gap units with the rules violated inside them
    for rel, ds in diags.items():
        if not ds:
            continue
        path = (root / rel).resolve()
        for (p, n), f in by_src.items():
            if p != path or n in done or not f["hasBody"]:
                continue
            inside = sorted({d["rule"] for d in ds if Path(d["file"]).name == path.name
                             and f["line"] - 3 <= d["line"] <= f["endLine"]}) or sorted({d["rule"] for d in ds})
            exported = f["exported"]
            kind = ("api" if n in target.entry else "internal") if target.entry else ("api" if exported else "internal")
            units.append(Unit(name=n, sym=n + "Ref", lean_decl=n + "Def", kind=kind, callees=[],
                              scope="gap:subset:" + ",".join(inside), loc=f"{f['file']}:{f['line']}",
                              body_hash=sha256(f["text"])[:16], source=f["text"]))
            done.add(n)
    return units

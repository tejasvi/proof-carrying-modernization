"""Java build: sources -> javac (--release 8) -> Soot 4.7.1 Jimple -> Lean (`jimple_import`) -> units."""
from __future__ import annotations

import os
import re
import subprocess
from collections import Counter
from pathlib import Path

from ...lean import RUN1, VO_ROOT, LeanPackage, Requirement
from ...model import Target, Unit, Variant, sha256
from ..base import Build, _ident

# snapshot 20261024T0553Z (default since 10-24 06:40Z): concrete test runs in one simp call, structural descToName,
# method-level facts for modular builds (`modular = true`: per-method `jimple_method` body modules + per-class
# `jimple_shape` modules, so a body edit re-checks only that method), jcontract_ok for virtual and static callees.
# Older pins: -0357Z (class-level modular), -0029Z (tests), deps/JimpleLean (20261023T2000Z).
JIMPLELEAN = Path(os.environ.get("VO_JIMPLE_DIR", str(VO_ROOT / "deps" / "JimpleLean-20261024T0553Z")))
JIMPLE_PIN = os.environ.get("VO_JIMPLE_PIN", "snapshot-20261024T0553Z")
SOOT = Path("/home/user/jimplelean_work/toolchain/soot-4.7.1-jar-with-dependencies.jar")
JDK = Path("/usr/lib/jvm/java-17-openjdk-amd64/bin")
JFLAGS = ["-XX:+UseSerialGC", "-XX:ActiveProcessorCount=1", "-XX:-UsePerfData", "-Xmx1g"]
JIMPLE_RUN = JIMPLELEAN / ".lake/build/bin/jimple-run"

# Soot prints an enum as "enum class X": the name is the word after the optional "class"
# Soot prints interfaces with TWO spaces ("public interface  X"): one or more spaces before the name; the
# lookahead keeps a class whose name holds a Soot-quoted keyword ('annotation') skipped rather than truncated
_CLASS_RE = re.compile(r"^(?:[\w ]*?)(?:class|interface|enum)(?: class)? +([\w.$]+)(?=\s)(?: extends ([\w.$]+))?", re.M)
_METHOD_RE = re.compile(r"^    (?P<mods>(?:[\w]+ )*)(?P<ret>[\w.$\[\]]+) (?P<name>[\w<>$]+)\((?P<params>[^)]*)\)"
                        r"(?: throws (?P<throws>[\w.$, ]+))?\s*$")
_INVOKE_RE = re.compile(r"(static|virtual|special|interface|dynamic)invoke [^<]*<(?P<cls>[\w.$]+): "
                        r"(?P<ret>[\w.$\[\]]+) (?P<name>[\w<>$]+)\((?P<params>[^)]*)\)>")
# a method declaration, with a body (next line `{`) or without one (abstract, native: the line ends with `;`)
_MDECL_RE = re.compile(r"^    (?P<mods>(?:[\w]+ )*)(?P<ret>[\w.$\[\]]+) (?P<name>[\w<>$]+)\((?P<params>[^)]*)\)"
                       r"(?: throws (?P<throws>[\w.$, ]+))?\s*;?\s*$")


def declared_keys(text: str) -> Counter:
    """`name(params)` of every method a class's Jimple declares, bodiless ones included, in the unit signature's
    format (`sig['params']` joined by commas). JimpleLean names a method `name(params):ret` when two declarations of
    its class share `name(params)` (e.g. a bridge next to an abstract covariant method), so method modules and
    class-level references count duplicates over all declarations, not only over the methods with bodies."""
    keys: Counter = Counter()
    for line in text.replace("'", "").splitlines():
        m = _MDECL_RE.match(line)
        if m:
            ps = [p.strip() for p in m.group("params").split(",") if p.strip()]
            keys[f"{m.group('name')}({','.join(ps)})"] += 1
    return keys


def run_tool(cmd: list[str], cwd: Path, timeout: int = 600, core_h: float = 0.1, mem: int = 32) -> subprocess.CompletedProcess:
    full = [str(RUN1), "-t", str(timeout), "-m", str(mem), "-c", str(core_h), "--", *cmd]
    return subprocess.run(full, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                          timeout=timeout + 60, env=dict(os.environ, VO_ROOT=str(VO_ROOT)))


def lean_package(run_dir: Path, revision: str | None = None) -> LeanPackage:
    req = Requirement("JimpleLean", str(JIMPLELEAN), JIMPLE_PIN, ["Jimple"])
    # a modular build names its modules without the revision (an unchanged class has byte-identical modules in
    # every revision, so its compiled proofs come back from the content-addressed cache): one package per revision;
    # a pin chosen by environment gets its own directory, as for cirlean
    base = run_dir / ("lean" if "VO_JIMPLE_PIN" not in os.environ else f"lean_{_ident(JIMPLE_PIN)}")
    pkg_dir = base if revision is None else base.with_name(base.name + "_mod") / _ident(revision)
    return LeanPackage(pkg_dir, "vo_" + _ident(run_dir.name), [req], ["Gen", "VO"], run_dir / "cache" / "olean")


def modular_enabled(target: Target) -> bool:
    """Per-class Gen modules: target option `modular = true`, or VO_JIMPLE_MODULAR=1/0 to override."""
    env = os.environ.get("VO_JIMPLE_MODULAR")
    return env == "1" if env in ("0", "1") else bool(target.extra.get("modular", False))


_VO_MREF = [
    "/-- The method of class `cls` with name `name` and parameter types `ps`. -/",
    "def vo_mref (P : Program) (cls name : String) (ps : List JType) : MethodRef :=",
    "  ⟨cls, ((P.classes.find? (·.name == cls)).bind fun d =>",
    "    d.methods.find? (fun m => m.name == name && m.params == ps)).get!⟩"]
# for a class that declares two methods differing only in the return type (a bridge next to its method or to an
# abstract covariant one; JimpleLean names both `name(params):ret`): `vo_mref` returns the first of them, so the
# statements of such methods select by the return type too (JimpleAdapter._mref); emitted only for builds with such
# classes, so other builds' generated text (and cache keys) stay as they were
_VO_MREF_RET = [
    "/-- The method of class `cls` with name `name`, parameter types `ps` and return type `r` (classes that declare",
    "two methods differing only in the return type). -/",
    "def vo_mref_ret (P : Program) (cls name : String) (ps : List JType) (r : JType) : MethodRef :=",
    "  ⟨cls, ((P.classes.find? (·.name == cls)).bind fun d =>",
    "    d.methods.find? (fun m => m.name == name && m.params == ps && m.ret == r)).get!⟩"]


def _erase_bodies(text: str) -> str:
    """The class's Jimple without method bodies (what `jimple_shape` keeps: header, fields, method signatures):
    lines at brace depth <= 1."""
    out, depth = [], 0
    for line in text.splitlines():
        s = line.strip()
        if s == "{":
            depth += 1
            if depth == 1:
                out.append(line)
            continue
        if s == "}":
            if depth == 1:
                out.append(line)
            depth -= 1
            continue
        if depth <= 1:
            out.append(line)
    return "\n".join(out)


def method_level_supported() -> bool:
    """JimpleLean with method-level facts (`jimple_method`, `jimple_shape`, `Shapes`): 20261024T0553Z or later."""
    src = " ".join(q.read_text(errors="replace") for q in (JIMPLELEAN / "Jimple").rglob("*.lean"))
    return "jimple_method" in src and "jimple_shape" in src and "def Shapes" in src


def method_modules(run_dir: Path, pkg: LeanPackage, files: list[Path], variant: Variant, units: list[Unit]) -> dict:
    """Method-level modules (JimpleLean 0553Z): per class a SHAPE module (`jimple_shape`: the class without bodies)
    and per method a METHOD module (`jimple_method`: one body). Each reads a stored copy of the class's Jimple whose
    file name is a hash of what the module keeps (the class without bodies; the class name and that one method), so
    an edit to one body leaves every other module's text, and so its cache key, unchanged. Returns build-info
    entries (empty when the pinned JimpleLean has no method-level facts)."""
    if not method_level_supported():
        return {}
    # resolved: the stored file's path is part of each module's text (and so of its cache key), and worker slots
    # (runs/<target>_w<k>, cache/ a symlink to the main run dir's cache) must name the same file
    store = (run_dir / "cache" / "jimple").resolve()
    store.mkdir(parents=True, exist_ok=True)
    text_of: dict[str, str] = {}
    for f in files:
        text = f.read_text()
        m = _CLASS_RE.search(text)
        if m:
            text_of[m.group(1)] = text

    def stored(prefix: str, key_text: str, full: str) -> Path:
        # several revisions may share a key (same shape, or same method) with other bodies elsewhere in the class:
        # the module reads only the part the key covers, so the first stored copy serves them all
        path = store / f"{prefix}_{sha256(key_text)[:24]}.jimple"
        if not path.exists():
            tmp = path.with_suffix(f".{os.getpid()}.tmp")
            tmp.write_text(full)
            tmp.replace(path)
        return path

    shape_mod, shape_const, meth_mod, meth_ref = {}, {}, {}, {}
    for cls, text in sorted(text_of.items()):
        mod = f"Gen.J.{_ident(variant.name)}.{_ident(cls)}.Shape"
        path = stored("s", _erase_bodies(text), text)
        src = pkg.src(mod)
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text("\n".join([f"/- Generated by veriforch (adapters/jimple, method level): the shape of {cls}. -/",
                                   "import Jimple", "", f'jimple_shape "{path}" as {mod}', ""]))
        shape_mod[cls], shape_const[cls] = mod, f"{mod}.«{cls}»"
    decl = {cls: declared_keys(text) for cls, text in text_of.items()}
    for u in units:
        sig = u.signature or {}
        cls = sig.get("cls")
        key = f"{sig.get('name')}({','.join(sig.get('params', []))})"
        if cls not in text_of or decl[cls][key] > 1:
            continue                        # declarations that differ only in the return type (a bridge next to
                                            # its method or to an abstract covariant one): class level only
        mod = f"Gen.J.{_ident(variant.name)}.{_ident(cls)}.M.{_component('m_' + _ident(sig.get('name', '') + '_' + '_'.join(sig.get('params', []))))}"
        path = stored("m", cls + "\n" + sig.get("jimple", ""), text_of[cls])
        src = pkg.src(mod)
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text("\n".join([f"/- Generated by veriforch (adapters/jimple, method level): {cls}.{key} alone. -/",
                                   "import Jimple", "", f'jimple_method "{path}" "{key}" as {mod}', ""]))
        meth_mod[u.name], meth_ref[u.name] = mod, f"{mod}.«{cls}».«{key}».ref"
    return {"jshape": shape_mod, "shape_const": shape_const, "jmethod": meth_mod, "method_ref": meth_ref}


def _component(name: str, limit: int = 160) -> str:
    """A module-name component short enough for a file name (the .olean/.ilean names must stay under 255 bytes):
    long ones keep a readable prefix and a hash of the full name. Short names are unchanged."""
    if len(name) <= limit:
        return name
    return name[:limit - 18] + "_" + sha256(name)[:16]


def modular_modules(run_dir: Path, pkg: LeanPackage, files: list[Path], variant: Variant) -> dict:
    """One module per class (`jimple_import` of a content-addressed copy of its .jimple file: the module's name
    depends on the variant and class, its text on the class's Jimple) and the whole program of the build
    (`jimple_program`, with `vo_mref` for statements that name methods through the program). Returns the build-info
    entries."""
    if "def BodyVC" not in (JIMPLELEAN / "Jimple" / "Verify.lean").read_text():
        raise RuntimeError(f"modular Java builds need a JimpleLean with BodyVC (20261024T0159Z or later); pinned: "
                           f"{JIMPLELEAN} (set VO_JIMPLE_DIR / VO_JIMPLE_PIN)")
    # resolved: the stored file's path is part of each module's text (and so of its cache key), and worker slots
    # (runs/<target>_w<k>, cache/ a symlink to the main run dir's cache) must name the same file
    store = (run_dir / "cache" / "jimple").resolve()
    store.mkdir(parents=True, exist_ok=True)
    cls_mod: dict[str, str] = {}
    dup_keys: dict[str, list[str]] = {}
    for f in files:
        text = f.read_text()
        m = _CLASS_RE.search(text)
        if not m:
            continue
        cls, digest = m.group(1), sha256(text)
        dup = sorted(k for k, n in declared_keys(text).items() if n > 1)
        if dup:
            dup_keys[cls] = dup         # JimpleLean names these `name(params):ret` (JimpleAdapter._ref)
        copy = store / f"{digest[:24]}.jimple"
        if not copy.exists():
            copy.write_text(text)
        # the name depends on the variant and the class only (not on the revision): an edit keeps every statement that
        # names the class unchanged, so callers' proof keys and contracts stay the same; the content is the class's
        # Jimple (content-addressed copy), so unchanged classes have byte-identical modules in every revision
        mod = f"Gen.J.{_ident(variant.name)}.{_ident(cls)}"
        src = pkg.src(mod)
        src.parent.mkdir(parents=True, exist_ok=True)
        src.write_text("\n".join([
            f"/- Generated by veriforch (adapters/jimple, modular): class {cls} alone (per-class import). -/",
            "import Jimple", "", f'jimple_import "{copy}" as {mod}', ""]))
        cls_mod[cls] = mod
    whole = f"Gen.{_ident(variant.name)}.Whole"
    wsrc = pkg.src(whole)
    wsrc.parent.mkdir(parents=True, exist_ok=True)
    mods = [cls_mod[c] for c in sorted(cls_mod)]
    wsrc.write_text("\n".join(
        ["/- Generated by veriforch (adapters/jimple, modular): the build's program, assembled from its classes. -/",
         "import Jimple"] + [f"import {m}" for m in mods]
        + ["", "open Jimple", "", f"jimple_program {' '.join(mods)} as {whole}", "", f"namespace {whole}", ""]
        + _VO_MREF + (["", *_VO_MREF_RET] if dup_keys else []) + ["", f"end {whole}", ""]))
    return {"gen_module": whole, "gen_ns": whole, "prog": f"{whole}.prog", "jmodular": cls_mod,
            "class_const": {c: f"{m}.«{c}»" for c, m in cls_mod.items()}, "gen_order": [*mods, whole],
            "ns": f"VO.{_ident(variant.name)}", "dup_keys": dup_keys}


def unit_name(cls: str, name: str, params: str) -> str:
    return f"{cls}.{name}({params.replace(' ', '')})"


def build(target: Target, variant: Variant, run_dir: Path) -> Build:
    vdir = run_dir / target.version / variant.name
    classes, jdir = vdir / "classes", vdir / "jimple"
    for d in (classes, jdir):
        d.mkdir(parents=True, exist_ok=True)
        for f in d.rglob("*"):
            if f.is_file():
                f.unlink()
    root = Path(target.root)
    rels = variant.sources or target.sources
    # library jars of the variant (e.g. the JUnit API of a `tests` variant) are on Soot's class path too, so
    # their classes resolve; only the target's own classes are converted (-process-dir)
    lib_cp = [x for i, x in enumerate(variant.flags) if i > 0 and variant.flags[i - 1] in ("-cp", "-classpath")]
    jar = target.extra.get("jar")
    if jar:
        # jar input: the published binary jar is the program (no sources compiled); its sha256 is checked
        jar_path = Path(jar) if Path(jar).is_absolute() else root / jar
        import hashlib
        got = hashlib.sha256(jar_path.read_bytes()).hexdigest()
        if target.extra.get("jar_sha256") and got != target.extra["jar_sha256"]:
            raise RuntimeError(f"jar sha256 {got} != pinned {target.extra['jar_sha256']}: {jar_path}")
        process = str(jar_path)
    else:
        srcs = [str(root / s) for s in rels]
        p = run_tool([str(JDK / "javac"), "-J" + JFLAGS[0], "-J" + JFLAGS[3], "-J-XX:-UsePerfData", "--release",
                      str(target.extra.get("release", 8)), "-proc:none", "-g", "-d", str(classes), *variant.flags,
                      *srcs], vdir, timeout=300)
        if p.returncode != 0:
            raise RuntimeError(f"javac failed:\n{p.stdout[-3000:]}")
        process = str(classes)
    p = run_tool([str(JDK / "java"), *JFLAGS, "-cp", str(SOOT), "soot.Main", "-pp", "-allow-phantom-refs",
                  "-keep-line-number", "-cp", ":".join([process, *lib_cp]), "-process-dir", process,
                  "-f", "J", "-d", str(jdir)],
                 vdir, timeout=600 if jar else 300)
    # a multi-release jar's META-INF/versions/*/module-info has no methods: not part of the program
    files = sorted(f for f in jdir.glob("*.jimple") if not f.name.startswith("META-INF."))
    if p.returncode != 0 or not files:
        raise RuntimeError(f"Soot failed:\n{p.stdout[-3000:]}")
    if modular_enabled(target):
        pkg = lean_package(run_dir, target.version)
        info = modular_modules(run_dir, pkg, files, variant)
        units = extract_units(files, target, rels)
        mm = method_modules(run_dir, pkg, files, variant, units)
        if mm:
            # shapes and methods are compiled before the whole program (they import only Jimple)
            info.update(mm)
            info["gen_order"] = (info["gen_order"][:-1] + sorted(mm["jshape"].values())
                                 + sorted(mm["jmethod"].values()) + info["gen_order"][-1:])
        tests = junit_tests(root, [s for s in rels if s in target.tests])
        info.update({"jimple_dir": str(jdir), "classes": str(classes), "junit_tests": sorted(tests)})
        return Build(target=target, variant=variant, dir=vdir, pkg=pkg, units=units, info=info)
    pkg = lean_package(run_dir)
    gen_mod = f"Gen.{_ident(target.version)}_{_ident(variant.name)}.Unit"
    dup_keys: dict[str, list[str]] = {}
    for f in files:
        text = f.read_text()
        cm = _CLASS_RE.search(text)
        dup = sorted(k for k, n in declared_keys(text).items() if n > 1) if cm else []
        if dup:
            dup_keys[cm.group(1)] = dup
    digest = sha256("".join(f.name + "\n" + f.read_text() for f in files))
    gen_src = "\n".join([
        "/- Generated by veriforch (adapters/jimple): the Jimple of the target, imported at elaboration time. -/",
        "import Jimple", "", "open Jimple", "",
        f"-- jimple sha256 {digest}",
        f'jimple_import "{jdir}" as {gen_mod}', "",
        f"namespace {gen_mod}", "",
        "/-- The method of class `cls` with name `name` and parameter types `ps`. -/",
        "def vo_mref (P : Program) (cls name : String) (ps : List JType) : MethodRef :=",
        "  ⟨cls, ((P.classes.find? (·.name == cls)).bind fun d =>",
        "    d.methods.find? (fun m => m.name == name && m.params == ps)).get!⟩", "",
        *(_VO_MREF_RET + [""] if dup_keys else []),
        f"end {gen_mod}", ""])
    gp = pkg.src(gen_mod)
    gp.parent.mkdir(parents=True, exist_ok=True)
    gp.write_text(gen_src)
    units = extract_units(files, target, rels)
    tests = junit_tests(root, [s for s in rels if s in target.tests])
    return Build(target=target, variant=variant, dir=vdir, pkg=pkg, units=units,
                 info={"gen_module": gen_mod, "gen_ns": gen_mod, "jimple_dir": str(jdir), "classes": str(classes),
                       "prog": f"{gen_mod}.prog", "junit_tests": sorted(tests), "dup_keys": dup_keys})


# docs/LIBRARY_MODELS.md sections whose `## ` header is not a list of fully qualified class names ("## Boxed primitives
# (Integer, Long, ...)", "## java.util.Map: HashMap, LinkedHashMap, TreeMap", ...): the classes their unprefixed rows
# hold for; the Iterator section's tables by their match function (`iterInst`, ...); rows that name their class
# (`Integer.valueOf(int)`, `new HashMap()`) go to that class (_MODEL_SHORT resolves the simple names the table uses)
_MODEL_SHORT = {**{k: "java.lang." + k for k in ("Integer", "Long", "Short", "Byte", "Boolean", "Double", "Float",
                                                 "Character", "String", "Math", "System", "Enum", "Object", "Record",
                                                 "StringBuilder", "StringBuffer", "CharSequence", "Class")},
                **{k: "java.util." + k for k in ("List", "Map", "Set", "Collections", "Arrays", "Objects", "ArrayList",
                                                 "LinkedList", "HashMap", "LinkedHashMap", "TreeMap", "HashSet",
                                                 "LinkedHashSet", "TreeSet", "StringJoiner", "Iterator")},
                "Stream": "java.util.stream.Stream", "BigDecimal": "java.math.BigDecimal",
                "BigInteger": "java.math.BigInteger", "RoundingMode": "java.math.RoundingMode",
                "MathContext": "java.math.MathContext"}
_MODEL_SECTIONS = {
    "Boxed primitives": ["java.lang." + k for k in ("Integer", "Long", "Short", "Byte", "Boolean", "Double", "Float")],
    "java.util.List:": ["java.util.List", "java.util.ArrayList", "java.util.LinkedList"],
    "java.util.Map:": ["java.util.Map", "java.util.HashMap", "java.util.LinkedHashMap", "java.util.TreeMap"],
    "java.util.Set:": ["java.util.Set", "java.util.HashSet", "java.util.LinkedHashSet", "java.util.TreeSet"],
    "java.io.PrintStream": ["java.io.PrintStream"],
    "java.lang.Object (any object)": ["java.lang.Object"],
    "java.lang.Record": ["java.lang.Record"]}
_MODEL_TABLES = {"iterInst": ["java.util.Iterator"], "entryInst": ["java.util.Map$Entry"],
                 "viewInst": ["java.util.Set", "java.util.Collection"]}
# `virtualinvoke r.<java.lang.Object: java.lang.Object clone()>()`: the table's "Method of arrays" row when r is an array
_ARRAY_CLONE_RE = re.compile(r"virtualinvoke (\$?\w+)\.<java\.lang\.Object: java\.lang\.Object clone\(\)>")
_ARRAY_LOCALS_RE = re.compile(r"^\s+[\w.$]+(?:\[\])+ ([\w$]+(?:, [\w$]+)*);$")


def _resolved_model_rows(text: str) -> set[tuple[str, str, int]]:
    """Rows of the model table under headers that are not lists of fully qualified class names (see _MODEL_SECTIONS),
    and rows that name their class. "Method of arrays" rows come back as ("<array>", name, n)."""
    out: set[tuple[str, str, int]] = set()
    clss: list[str] = []
    table: list[str] | None = None
    arrays = False
    for line in text.splitlines():
        if line.startswith("## "):
            h = line[3:].strip()
            clss = next((v for k, v in _MODEL_SECTIONS.items() if h.startswith(k)), None) or \
                [c.strip() for c in h.split(",") if c.strip()]
            table, arrays = None, False
            continue
        if line.startswith("| ") and "|---" not in line and not line.startswith("| `"):
            m = re.search(r"\(`(\w+)`\)", line)       # a table heading, e.g. "| Instance method (`iterInst`) |"
            table = _MODEL_TABLES.get(m.group(1)) if m else None
            arrays = line.startswith("| Method of arrays")
            continue
        for m in re.finditer(r"`(new )?([\w.$]+)\(([^)]*)\)`", line):
            n = 0 if not m.group(3).strip() else len(m.group(3).split(","))
            parts = m.group(2).split(".")
            if arrays:
                out.add(("<array>", parts[-1], n))
            elif m.group(1):
                c = _MODEL_SHORT.get(parts[-1]) or (m.group(2) if len(parts) > 1 else None)
                if c:
                    out.add((c, "<init>", n))
            elif len(parts) >= 2 and parts[-2] in _MODEL_SHORT:
                out.add((_MODEL_SHORT[parts[-2]], parts[-1], n))
            else:
                for c in table or clss:
                    out.add((c, parts[-1], n))
    return out


def modelled_library() -> set[tuple[str, str, int]]:
    """(class, method, #params) rows of JimpleLean's generated model table (docs/LIBRARY_MODELS.md).

    A section header may name several classes ("## java.lang.StringBuilder, java.lang.StringBuffer"): its rows
    hold for each of them. Prose lines of a section that name methods in backticks without a parameter list
    ("`length`, `charAt`") are read as any arity up to 4. (Before the prereg-D defect fix (ii), 10-24, a
    multi-class header matched no class and prose lines were skipped.) Headers that are not such lists (boxed
    primitives, List/Map/Set, Iterator/Map.Entry/views, PrintStream, Object with array `clone()`) are resolved by
    _resolved_model_rows (T1 thrift, 10-25: before, their rows matched no class and read as unmodelled). Rows are
    matched by name and arity, as before."""
    out: set[tuple[str, str, int]] = set()
    p = JIMPLELEAN / "docs" / "LIBRARY_MODELS.md"
    if not p.exists():
        return out
    clss: list[str] = []
    for line in p.read_text().splitlines():
        if line.startswith("## "):
            clss = [c.strip() for c in line[3:].split(",") if c.strip()]
            continue
        if not clss:
            continue
        for m in re.finditer(r"`(new )?([\w.$]+)\(([^)]*)\)`", line):
            name = "<init>" if m.group(1) else m.group(2).split(".")[-1]
            n = 0 if not m.group(3).strip() else len(m.group(3).split(","))
            for c in clss:
                out.add((c, name, n))
        if not line.startswith("|"):
            for m in re.finditer(r"`([A-Za-z_]\w*)`", line):
                for c in clss:
                    for n in range(0, 5):
                        out.add((c, m.group(1), n))
    return out | _resolved_model_rows(p.read_text())


_THROWABLE_METHODS = {"getMessage", "getLocalizedMessage", "getCause", "initCause", "printStackTrace",
                      "fillInStackTrace", "addSuppressed"}
_OBJECT_METHODS = {"getClass", "hashCode", "equals", "toString"}


def _generic_model(cls: str, name: str, n: int) -> bool:
    """Rows of the model table stated for whole families of classes: library exception classes
    (constructors with up to four arguments, Throwable's methods) and Object's methods on any object."""
    if cls == "java.lang.Object" and name == "<init>":
        return True
    if cls.endswith(("Exception", "Error", "Throwable")) and (name == "<init>" and n <= 4 or name in _THROWABLE_METHODS):
        return True
    return name in _OBJECT_METHODS


_J5_ARITY = {"assertTrue": 1, "assertFalse": 1, "assertNull": 1, "assertNotNull": 1, "assertSame": 2,
             "assertNotSame": 2, "assertEquals": 2, "assertThrows": 2}
_J4_ARITY = {"assertTrue": 1, "assertFalse": 1, "assertNull": 1, "assertNotNull": 1, "assertSame": 2,
             "assertNotSame": 2, "assertEquals": 2, "assertThrows": 2, "fail": 0}
_J5_MSG = ("java.lang.String", "java.util.function.Supplier")


def _junit_model(cls: str, name: str, params: str) -> bool:
    """The JUnit assertions JimpleLean models natively (Jimple/Native.lean `jupiterAssert`/`junit4Assert`,
    docs/LIBRARY_MODELS.md "JUnit 5"/"JUnit 4"): the core arguments plus an optional message (last for JUnit 5:
    String or Supplier; first for JUnit 4: String). Delta overloads, assertArrayEquals, assertAll, ... are not."""
    ps = [x.strip() for x in params.split(",") if x.strip()]
    if cls == "org.junit.jupiter.api.Assertions":
        if name == "fail":
            return len(ps) <= 2
        k = _J5_ARITY.get(name)
        return k is not None and (len(ps) == k or (len(ps) == k + 1 and ps[-1] in _J5_MSG))
    if cls == "org.junit.Assert":
        k = _J4_ARITY.get(name)
        core = ps[1:] if ps and ps[0] == "java.lang.String" and len(ps) > (k or 0) else ps
        return k is not None and len(core) == k
    return False


def extract_units(files: list[Path], target: Target, rels: list[str] | None = None) -> list[Unit]:
    app_classes: set[str] = set()
    parsed = []
    for f in files:
        text = f.read_text()
        m = _CLASS_RE.search(text)
        if not m:
            continue
        cls = m.group(1)
        app_classes.add(cls)
        parsed.append((cls, text))
    lib = modelled_library()
    units: list[Unit] = []
    for cls, text in parsed:
        lines = text.replace("'", "").splitlines()   # Soot quotes primitive type names
        i = 0
        while i < len(lines):
            m = _METHOD_RE.match(lines[i])
            if not m or (i + 1 < len(lines) and lines[i + 1].strip() != "{"):
                i += 1
                continue
            name, params, mods = m.group("name"), m.group("params"), m.group("mods")
            body, j = [], i + 2
            while j < len(lines) and lines[j] != "    }":
                body.append(lines[j])
                j += 1
            callees, gaps = [], []
            arrays = {x.strip() for b in body for mm in [_ARRAY_LOCALS_RE.match(b)] if mm for x in mm.group(1).split(",")}
            for b in body:
                for inv in _INVOKE_RE.finditer(b):
                    ccls, cname, cparams = inv.group("cls"), inv.group("name"), inv.group("params")
                    if ccls in app_classes:
                        cu = unit_name(ccls, cname, cparams)
                        if cu not in callees:
                            callees.append(cu)
                    else:
                        n = 0 if not cparams.strip() else len(cparams.split(","))
                        ac = _ARRAY_CLONE_RE.search(b) if (ccls, cname, n) == ("java.lang.Object", "clone", 0) else None
                        if ac and ac.group(1) in arrays and ("<array>", "clone", 0) in lib:
                            continue                # clone() of an array: the table's "Method of arrays" row
                        if (ccls, cname, n) not in lib and not _generic_model(ccls, cname, n) \
                                and not _junit_model(ccls, cname, cparams):
                            gaps.append(f"{ccls}.{cname}/{n}")
                if "dynamicinvoke" in b and not any(k in b for k in ("LambdaMetafactory", "StringConcatFactory")):
                    gaps.append("invokedynamic")
            u = Unit(name=unit_name(cls, name, params), sym=f"{cls}.{name}({params})",
                     lean_decl=f"«{cls}».«{name}({params.replace(' ', '')})»",
                     kind="api" if "public" in mods.split() and not name.startswith("<") else "internal",
                     # a self-call is not a scheduling edge: the method's own contract goes into its Γ
                     callees=[c for c in callees if c != unit_name(cls, name, params)],
                     scope="in_scope" if not gaps else "gap:unmodelled:" + ",".join(sorted(set(gaps))),
                     loc=f"{cls}", body_hash=sha256("\n".join(lines[i:j]))[:16])
            u.signature = {"cls": cls, "name": name, "params": [p.strip() for p in params.split(",") if p.strip()],
                           "ret": m.group("ret"), "static": "static" in mods.split(),
                           "bridge": "volatile" in mods.split(),     # Soot prints ACC_BRIDGE as `volatile`
                           "recursive": unit_name(cls, name, params) in callees,
                           "throws": [t.strip() for t in (m.group("throws") or "").split(",") if t.strip()],
                           "jimple": "\n".join(lines[i:j + 1]),
                           "listing": numbered_listing("\n".join(lines[i:j + 1]))}
            u.source = java_source(target, cls, name, rels=rels)
            units.append(u)
            i = j + 1
    # a method and its bridge share a unit name (they differ only in the return type), and the scheduler resolves a
    # name to the LAST unit with it (verify_build: `by = {u.name: u}`): bridges first, the method last, so that
    # `--only <name>` verifies the method (T1 thrift, 10-25: the bridge came last for all 11 such names)
    groups: dict[str, list[Unit]] = {}
    for u in units:
        groups.setdefault(u.name, []).append(u)
    ordered, seen = [], set()
    for u in units:
        g = groups[u.name]
        if len(g) == 1:
            ordered.append(u)
        elif u.name not in seen:
            seen.add(u.name)
            ordered.extend(sorted(g, key=lambda x: not (x.signature or {}).get("bridge")))
    return ordered


_DECL_RE = re.compile(r"^\s*[\w.$\[\]]+ [\w$]+(, [\w$]+)*;$")
_LABEL_RE = re.compile(r"^\s*(\w+):$")


def numbered_listing(method_text: str) -> str:
    """The method body as JimpleLean numbers it (Jimple/Parser.lean parseBody): locals in declaration
    order (`fr.get k`), statements in order from 0 with labels resolved to statement indices."""
    lines = [l for l in method_text.splitlines()[2:] if l.strip() and l.strip() != "}"]
    locals_, stmts, labels = [], [], {}
    in_decls = True
    for l in lines:
        s = l.strip()
        if in_decls and _DECL_RE.match(s) and "=" not in s and "(" not in s:
            ty, names = s[:-1].split(" ", 1)
            locals_ += [(n.strip(), ty) for n in names.split(",")]
            continue
        in_decls = False
        m = _LABEL_RE.match(s)
        if m:
            labels[m.group(1)] = len(stmts)
            continue
        if s.startswith("catch "):
            stmts.append(("catch", s))
            continue
        stmts.append(("stmt", s))
    out = ["locals (fr.get k): " + ", ".join(f"{k} = {n} : {t}" for k, (n, t) in enumerate(locals_))]
    k = 0
    for kind, s in stmts:
        if kind == "catch":
            out.append(f"     {s}")
            continue
        s2 = re.sub(r"\b(label\d+)\b", lambda m: f"{m.group(1)}=[{labels.get(m.group(1), '?')}]", s)
        out.append(f"[{k}] {s2}")
        k += 1
    return "\n".join(out)


def java_source(target: Target, cls: str, name: str, max_lines: int = 120, rels: list[str] | None = None) -> str:
    """Source text of the methods named `name` in class `cls` (all overloads), for prompts and reports."""
    simple = cls.split(".")[-1]
    for s in rels or target.sources:
        p = Path(target.root) / s
        if p.stem != simple or not p.exists():
            continue
        lines = p.read_text(errors="replace").splitlines()
        if name == "<init>":
            name = simple
        out = []
        for k, l in enumerate(lines):
            if re.search(r"\b" + re.escape(name) + r"\s*\(", l) and not l.strip().startswith(("//", "*", "return")) \
                    and ("{" in l or (k + 1 < len(lines) and "{" in lines[k + 1])) and "=" not in l.split("(")[0]:
                depth, seen = 0, False
                for l2 in lines[k:k + max_lines]:
                    out.append(l2)
                    depth += l2.count("{") - l2.count("}")
                    seen = seen or "{" in l2
                    if seen and depth <= 0:
                        break
                out.append("")
        return "\n".join(out)
    return ""


# JUnit test annotations (Jupiter and JUnit 4): a method carrying one is a test unit
_TEST_ANN = re.compile(r"@(?:org\.junit\.jupiter\.api\.|org\.junit\.)?(Test|RepeatedTest)\b(?!\w)")
_CLASS_DECL = re.compile(r"\b(?:class|interface|enum|record)\s+([A-Za-z_$][\w$]*)")
_METHOD_HEAD = re.compile(r"([A-Za-z_$][\w$]*)\s*\(([^()]*)\)\s*(?:throws\s+[\w.$,\s]+)?\{")


def _strip_java(text: str) -> str:
    """Comments and string/char literals blanked out (newlines kept), so braces and `@Test` are code only."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif text.startswith("/*", i):
            j = text.find("*/", i + 2)
            j = n if j < 0 else j + 2
            out.append("".join(ch if ch == "\n" else " " for ch in text[i:j])); i = j
        elif text.startswith('"""', i):
            j = text.find('"""', i + 3)
            j = n if j < 0 else j + 3
            out.append("".join(ch if ch == "\n" else " " for ch in text[i:j])); i = j
        elif c in "\"'":
            j = i + 1
            while j < n and text[j] != c and text[j] != "\n":
                j += 2 if text[j] == "\\" else 1
            out.append(" " * (min(j + 1, n) - i)); i = min(j + 1, n)
        else:
            out.append(c); i += 1
    return "".join(out)


def junit_tests(root: Path, test_files: list[str]) -> set[str]:
    """`cls.method/arity` of every method annotated `@Test` (or `@RepeatedTest`) in the given test sources, with
    the binary class name (package + `Outer$Inner` for nested test classes), read from the source text."""
    found: set[str] = set()
    for rel in test_files:
        p = root / rel
        if not p.exists():
            continue
        text = _strip_java(p.read_text(errors="replace"))
        pm = re.search(r"^\s*package\s+([\w.]+)\s*;", text, re.M)
        pkg = pm.group(1) + "." if pm else ""
        stack: list[tuple[str, int]] = []       # (binary class name, brace depth inside its body)
        depth, pending_cls, pending_test, i = 0, None, False, 0
        while i < len(text):
            c = text[i]
            if c == "@":
                m = _TEST_ANN.match(text, i)
                if m and stack and depth == stack[-1][1]:
                    pending_test = True
                i += 1
                continue
            m = _CLASS_DECL.match(text, i)
            if m and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_$.")):
                pending_cls = m.group(1)
                i = m.end()
                continue
            if c == "{":
                depth += 1
                if pending_cls is not None:
                    outer = stack[-1][0] + "$" if stack else pkg
                    stack.append((outer + pending_cls, depth))
                    pending_cls = None
                    pending_test = False
                i += 1
                continue
            if c == "}":
                if stack and depth == stack[-1][1]:
                    stack.pop()
                depth -= 1
                i += 1
                continue
            if pending_test and stack and depth == stack[-1][1] and (c.isalpha() or c in "_$"):
                m = _METHOD_HEAD.match(text, i)
                if m and m.group(1) not in ("if", "for", "while", "switch", "catch", "synchronized"):
                    params = [x for x in m.group(2).split(",") if x.strip()]
                    found.add(f"{stack[-1][0]}.{m.group(1)}/{len(params)}")
                    pending_test = False
                    i = m.end() - 1             # the body's `{` is counted by the loop
                    continue
            i += 1
    return found

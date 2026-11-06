#!/usr/bin/env python3
"""Pre-registration T, step T3 (frozen v1: ~/fv_paper/prereg/PREREG_T_v1.md §T3, SHA256SUMS_T_v1): CI verdicts over
Apache Thrift's history, C1's procedure (PREREG_C_v2) per commit. Adapted from the C1/C1b driver
(~/veriforch_frozen/C1b_20261025T033823Z/scripts/prereg_c.py): the same `vo ci` command, budget rule, verdict
extraction, kernel replay, outcome definitions, records, worker slots and resource gate.

    <frozen>/.venv/bin/python -B <frozen>/scripts/prereg_t3.py --frozen <frozen> --pins <pin file> [--workers N]
        [--resume] [--stop-at ISO] [--hard-stop ISO]
    ... --plan [--first K | --orders 1,2,3]       targets and commands of the selected commits; nothing runs
    ... --no-llm --out runs/t3_dryrun_<UTC> [--commits-file TSV] [--first K | --orders ...]   a dry run: no model call

Pin file (env syntax, as scripts/cert_pin.env; `$VO_ROOT` is the frozen copy): VO_CIRLEAN_DIR/PIN, VO_CERT_CIRLEAN_DIR/
PIN, VO_EQUIVLEAN_DIR/PIN (C and C++: the compared builds and the certificates), VO_JIMPLE_DIR/PIN (Java),
VO_AENEAS_DIR/PIN, VO_EQUIVLEAN_AENEAS_DIR/PIN, VO_AENEAS_LEAN_PACKAGES (Rust). Every `vo ci` gets it as
VO_CERT_PIN_ENV (scripts/vo sources it), the pre-passes get the same values; recorded in pins.json at start.

Commits: T/t3_commits.tsv of the frozen package (checked against SHA256SUMS_T_v1, whose own sha256 is fixed below), in
its order. Per commit c with first parent p and per touched supported language (the TSV's `languages`):

1. The library target at this commit (under <out>/targets/<tag>/):
   C++ (lib/cpp), C (lib/c_glib): a compile_commands target, one variant per TU, with T1's options
     (targets/thrift_cpp_transport.toml, thrift_c_glib.toml: cflags -w; C++ also loc_from_definition). Its compile
     commands come from scripts/t3_compdb.py: the TUs that the CMakeLists.txt of p and of c both compile, with T1's
     flags, config.h and system headers (the pinned flags);
   Java (lib/java): T1's target (targets/thrift_java.toml) without the jar input, so that the Jimple adapter compiles
     each revision's own sources: javac 17 --release 8 -proc:none -g -encoding UTF-8 against T1's jar set
     (deps/thrift_java_jars); sources = the .java files under the revision's main source root (lib/java/src/main/java,
     or lib/java/src before the Gradle layout) at p and at c, each revision compiling the files it has;
   Rust (lib/rs): T1's target (targets/thrift_rs.toml) as is (vendored dependencies, Charon in bubblewrap).
2. The front-end pre-pass (scripts/t3_prepass.py; materialise + build both revisions as `vo ci` does; no model, no
   Lean for C, C++ and Java) gives the changed functions (unit name @ defining file). C/C++: only the TUs whose
   include closure (clang -MM, the build's flags) holds a changed file are built; each changed function gets one home
   TU, the TU compiled from its defining file, else the first TU in compile-commands order where it changed.
   B = $0.50 x the number of distinct changed functions.
3. `vo ci <target> --base p --head c [--variant <TU>]... --attempts 0 --budget B --check-timeout 600` inside one
   outer run1.sh job with its own guard log (its last `metered` line: the core-seconds) and its own run directory
   (the content-addressed .olean caches shared per language through symlinks, as C1). C/C++ name the home TUs and
   the affected TUs that did not build in the pre-pass (vo ci then records those as blocked: build).
4. Per changed function: the verdict of its home TU (equivalent, changed_only_where_old_unsafe, behaviour_changed with
   its witness, unknown with the reason). Every claimed verdict theorem: its axioms (printed by the verdict module's
   `#print axioms`, recorded) and the kernel replay of its module in the package that built it
   (scripts/kernel_replay.sh, `lake env leanchecker <module>`; a package without a lakefile, the Rust pair package,
   runs the same leanchecker with that package's explicit LEAN_PATH). Only a replayed theorem is a kernel verdict.
5. Outcome per commit (PREREG_C_v2): `blocked: build` when an affected TU (C/C++) or the library (Java, Rust) does not
   build at p or c, with the error; otherwise C1's computation over the verdicts (certified conservative, certified
   equivalent, behaviour change shown, partly certified, unknown). A commit without a changed function is `unknown`
   with that reason. The record also gives `outcome_blocked_only_if_nothing_builds` (the other reading of
   blocked: build for libraries of several TUs: the blocked TUs count as unknown functions). A tool failure (no
   ci.json, a pre-pass or driver failure) is `crash`, never an outcome: --resume re-runs it after a crash fix.
Stop rules: model $ (usage.jsonl rows of the commits' run directories) plus the B of the language runs in flight
reaching $300, or the clock reaching --stop-at (Tue 2026-10-27 03:00Z): nothing starts after that, and a `vo ci` that
starts before has a wall ending by --hard-stop. The remaining commits are recorded as unattempted.
Resource gate (main's T3 rules; T2 has priority): no dispatch while the 1-minute load > 450 or MemAvailable < 150 GB;
at most 6 commits in flight, each running its steps one after another.
"""
from __future__ import annotations

import argparse
import calendar
import csv
import hashlib
import json
import os
import re
import socket
import subprocess
import sys
import threading
import time
import tomllib
from pathlib import Path

LIVE = Path(__file__).resolve().parents[1]          # the frozen copy when run from it (runs/, deps/: live symlinks)
VO_LIVE = Path("/home/user/veriforch")
PKG = Path.home() / "fv_paper" / "prereg"
T_SHA = "b167d544df490ac4d6ae5338ac19191cfb32fd1c381df21c4fb1f59357f21986"   # sha256 of SHA256SUMS_T_v1
COMMITS = PKG / "T" / "t3_commits.tsv"
THRIFT = VO_LIVE / "targets" / "thrift"
THRIFT_PIN = "f0eb8b84eb5654a949dda7c8ae444a11ca63e632"
OUT_REAL = LIVE / "runs" / "prereg" / "T3"
BUDGET = 300.0
PER_FUNCTION = 0.50
STOP_AT = "2026-10-27T03:00:00Z"
HARD_STOP = "2026-10-27T05:30:00Z"                   # the paper freeze is 06:00Z
LOAD_MAX = 450.0
MEM_MIN = 150e9
MAX_WORKERS = 12                                     # main's T3 rule: 6 (the launcher's default); 12 only on main's word
VO_CI_WALL = 6 * 3600                                # C1's outer job: -t 6 h, -m 128, -c 8 core-h
VO_CI_CORE_H = 8.0
PREPASS_WALL = 4 * 3600
LEAN_BIN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin"
CLANG = Path("/home/user/cirlean_work/toolchain/upstream-4955d32b/bin/clang")
JDK = Path("/usr/lib/jvm/java-17-openjdk-amd64/bin")
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
JAVA_FIRST_JOBS = 11
CHARON_INCLUDE_ADD = ["integer_encoding"]
# main 10-25: T3's Java stays on JimpleLean 0149Z (equiv-lean 751764f's Jimple bridge requires it), so JimpleLean
# 1728Z's fix of "(kernel) deep recursion" on branches over signed bitwise results does not reach T3
JAVA_DEEP_RECURSION = ("JimpleLean 0149Z limitation: \"(kernel) deep recursion\" on branches over signed bitwise "
                       "results, fixed in JimpleLean 1728Z, which T3 does not use (equiv-lean's Jimple bridge needs 0149Z)")
KNOWN_LIMITATIONS = [JAVA_DEEP_RECURSION,
                     "Rust: vendored sources are today's crates.io versions satisfying each revision's Cargo.toml, not "
                     "the versions of the commit's date (w-thrift-rsts)",
                     "Rust: the T3 prune file was triaged at the pin; an Aeneas abort it does not cover is blocked: build"]
VERDICTS = {"equivalent", "changed_only_where_old_unsafe", "behaviour_changed", "unknown"}   # PREREG_C_v2
# the reason of a changed function's `unknown` when the language's adapter has no old ≡ new step (main 10-25)
NO_EQUIV = {"Java": "no Java equivalence step in veriforch CI"}
SYNTHETIC_RE = re.compile(r"\blambda\$|\baccess\$|\$deserializeLambda\$")
# language -> library directory, T1 target the T3 target is made from, kind
LANGS = {
    "C++": {"key": "cpp", "libdir": "lib/cpp", "t1": "thrift_cpp_transport", "compdb": "cpp"},
    "C": {"key": "c", "libdir": "lib/c_glib", "t1": "thrift_c_glib", "compdb": "c_glib"},
    "Java": {"key": "java", "libdir": "lib/java", "t1": "thrift_java"},
    "Rust": {"key": "rust", "libdir": "lib/rs", "t1": "thrift_rs"},
}
# inputs outside the frozen copy that the targets read: sha256 at start (pins.json), re-checked before each use
RUST_PRUNE_T3 = VO_LIVE / "runs/prereg/T3_inputs/thrift_rs_t3.aeneas_prune.json"   # w-thrift-rsts 10-25, a6522cc5…
INPUTS = {"config.h": VO_LIVE / "targets/thrift_cpp_config/thrift/config.h",
          "thrift_rs_t3.aeneas_prune.json": RUST_PRUNE_T3,
          "thrift_headers/VERSIONS.txt": VO_LIVE / "deps/thrift_headers/VERSIONS.txt",
          "thrift_java_jars/SHA256SUMS": VO_LIVE / "deps/thrift_java_jars/SHA256SUMS",
          "thrift_rs.Cargo.lock": VO_LIVE / "targets/thrift_rs.Cargo.lock"}


def utc() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def epoch(iso: str) -> float:
    return calendar.timegm(time.strptime(iso, "%Y-%m-%dT%H:%M:%SZ"))


def sh(cmd: list[str], cwd: Path | None = None, timeout: int = 600, env: dict | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, env=env)


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def git(*a: str) -> str:
    p = sh(["git", "-C", str(THRIFT), *a], timeout=300)
    if p.returncode != 0:
        raise RuntimeError(f"git {' '.join(a)}: {p.stderr.strip()[:500]}")
    return p.stdout


def tree_hash(d: Path, pattern: str = "*") -> str:
    """sha256 over the sorted (relative path, sha256) of the files under d matching pattern."""
    h = hashlib.sha256()
    for f in sorted(x for x in d.rglob(pattern) if x.is_file()):
        h.update(f"{f.relative_to(d)}\0{sha256_file(f)}\n".encode())
    return h.hexdigest()


# ---------------------------------------------------------------------------------------------- package and pins
def check_package() -> str:
    got = sha256_file(PKG / "SHA256SUMS_T_v1")
    if got != T_SHA:
        raise SystemExit(f"SHA256SUMS_T_v1 sha256 {got} != frozen {T_SHA}")
    p = sh(["sha256sum", "--check", "--strict", "SHA256SUMS_T_v1"], cwd=PKG)
    if p.returncode != 0:
        raise SystemExit(f"SHA256SUMS_T_v1: files differ from the frozen package:\n{p.stdout[-2000:]}{p.stderr[-500:]}")
    return got


def pin_env(tree: Path, pin_file: Path) -> dict[str, str]:
    """The pin file's assignments, `$VO_ROOT` read as the frozen copy (as scripts/vo sources it)."""
    env = {}
    for line in pin_file.read_text().replace("$VO_ROOT", str(tree)).splitlines():
        m = re.match(r'^\s*([A-Z_]+)="?([^"#]*)"?\s*$', line)
        if m:
            env[m.group(1)] = m.group(2).strip()
    return env


def git_head(path: str) -> str | None:
    p = sh(["git", "-C", path, "rev-parse", "HEAD"])
    return p.stdout.strip() if p.returncode == 0 else None


def frozen_copy(arg: str | None, plan: bool) -> Path:
    if not arg:
        if plan:
            return LIVE
        raise SystemExit("--frozen DIR is required (scripts/freeze_copy.sh DIR makes one)")
    f = Path(arg).resolve()
    p = sh(["sha256sum", "--check", "--strict", "--quiet", "SHA256SUMS"], cwd=f)
    if p.returncode != 0:
        raise SystemExit(f"frozen copy {f} does not match its manifest:\n{p.stdout[-1500:]}")
    if f != LIVE:
        raise SystemExit(f"run the frozen copy's own driver ({f}/scripts/prereg_t3.py), not {LIVE}")
    return f


def pins(frozen: Path, pin_file: Path, package_sha: str, a) -> tuple[dict, list[str]]:
    env = pin_env(frozen, pin_file)
    problems = []
    need = ["VO_CIRLEAN_DIR", "VO_CIRLEAN_PIN", "VO_CERT_CIRLEAN_DIR", "VO_CERT_CIRLEAN_PIN", "VO_EQUIVLEAN_DIR",
            "VO_EQUIVLEAN_PIN", "VO_JIMPLE_DIR", "VO_JIMPLE_PIN", "VO_AENEAS_DIR", "VO_AENEAS_PIN"]
    problems += [f"pin file has no {k}" for k in need if not env.get(k)]
    cir, cert, eq = env.get("VO_CIRLEAN_DIR", ""), env.get("VO_CERT_CIRLEAN_DIR", ""), env.get("VO_EQUIVLEAN_DIR", "")
    if cir and cert and Path(cir).resolve() != Path(cert).resolve():
        problems.append(f"scheduler cirlean {cir} != certificate cirlean {cert}")
    lf = Path(eq) / "lakefile.toml"
    req = re.search(r'name\s*=\s*"cirlean"\s*\npath\s*=\s*"([^"]+)"', lf.read_text()) if lf.exists() else None
    if req is None or (Path(eq) / req.group(1)).resolve() != Path(cert).resolve():
        problems.append(f"equiv-lean {eq} is not built against {cert} (lakefile cirlean path: "
                        f"{req.group(1) if req else 'none'})")
    for k in ("VO_CIRLEAN_DIR", "VO_JIMPLE_DIR", "VO_AENEAS_DIR", "VO_EQUIVLEAN_DIR"):
        if env.get(k) and not Path(env[k]).is_dir():
            problems.append(f"{k} {env[k]} does not exist")
    head = git_head(str(THRIFT))
    if head != THRIFT_PIN:
        problems.append(f"the Thrift clone is at {head}, not the pin {THRIFT_PIN}")
    jars = sh(["sha256sum", "--check", "--strict", "--quiet", "SHA256SUMS"], cwd=VO_LIVE / "deps/thrift_java_jars")
    if jars.returncode != 0:
        problems.append(f"deps/thrift_java_jars differs from its SHA256SUMS: {jars.stdout[-300:]}")
    man = frozen / "SHA256SUMS"
    jdir = env.get("VO_JIMPLE_DIR", "")
    d = {
        "started": utc(), "host": socket.gethostname(), "study": "T3",
        "dry_run": bool(a.no_llm), "no_llm": bool(a.no_llm), "commits_file": str(a.commits_file or COMMITS),
        "commits_file_sha256": sha256_file(Path(a.commits_file) if a.commits_file else COMMITS),
        "prereg_package": {"dir": str(PKG), "SHA256SUMS_T_v1": package_sha,
                           "PREREG_C_v2.md": sha256_file(PKG / "PREREG_C_v2.md"),
                           "DEVIATIONS.md_at_start": sha256_file(PKG / "DEVIATIONS.md")},
        "pin_file": {"path": str(pin_file), "sha256": sha256_file(pin_file), "env": env},
        "veriforch": {"frozen_copy": str(frozen),
                      "manifest_sha256": sha256_file(man) if man.exists() else None},
        "cirlean": {"dir": cir, "pin": env.get("VO_CIRLEAN_PIN"), "commit": git_head(cir)},
        "cert_cirlean": {"dir": cert, "pin": env.get("VO_CERT_CIRLEAN_PIN"), "commit": git_head(cert)},
        "equivlean": {"dir": eq, "pin": env.get("VO_EQUIVLEAN_PIN"), "commit": git_head(eq),
                      "lakefile_cirlean_path": req.group(1) if req else None},
        "jimplelean": {"dir": jdir, "pin": env.get("VO_JIMPLE_PIN"),
                       "SHA256SUMS_sha256": sha256_file(Path(jdir) / "SHA256SUMS")
                       if jdir and (Path(jdir) / "SHA256SUMS").exists() else None, "commit": git_head(jdir)},
        "equivlean_jimple": {"dir": env.get("VO_EQUIVLEAN_JIMPLE_DIR"), "pin": env.get("VO_EQUIVLEAN_JIMPLE_PIN"),
                             "commit": git_head(env["VO_EQUIVLEAN_JIMPLE_DIR"]) if env.get("VO_EQUIVLEAN_JIMPLE_DIR") else None,
                             "jimplelean_dir": env.get("VO_EQUIVLEAN_JIMPLE_JIMPLELEAN_DIR"),
                             "jimplelean_pin": env.get("VO_EQUIVLEAN_JIMPLE_JIMPLELEAN_PIN")},
        "rust": {k: env.get(k) for k in ("VO_AENEAS_DIR", "VO_AENEAS_PIN", "VO_EQUIVLEAN_AENEAS_DIR",
                                         "VO_EQUIVLEAN_AENEAS_PIN", "VO_AENEAS_LEAN_PACKAGES")},
        "adapter_sources": {str(q.relative_to(frozen)): sha256_file(q) for q in sorted(
            list((frozen / "orch" / "veriforch").glob("*.py"))
            + list((frozen / "orch" / "veriforch" / "adapters").glob("*/*.py"))) if q.is_file()},
        "lean": sh([str(LEAN_BIN / "lean"), "--version"]).stdout.strip(),
        "clang": (sh([str(CLANG), "--version"]).stdout.splitlines() or [""])[0],
        "jdk": (sh([str(JDK / "javac"), "-version"]).stdout + sh([str(JDK / "javac"), "-version"]).stderr).strip(),
        "thrift": {"root": str(THRIFT), "head": head},
        "inputs": {k: sha256_file(p) if p.exists() else None for k, p in INPUTS.items()},
        "inputs_trees": {"deps/thrift_headers": tree_hash(VO_LIVE / "deps/thrift_headers", "*.h"),
                         "rust vendor_dir (.cargo-checksum.json)":
                         tree_hash(VO_LIVE / "scratch/thrift_rsts/rs/vendor", ".cargo-checksum.json")},
        "limits": {"workers": a.workers, "load_max": a.load_max, "mem_min_gb": MEM_MIN / 1e9,
                   "shared_caches": a.shared_caches, "front_end_only": a.front_end_only,
                   "blocked_verdicts": a.blocked_verdicts,
                   "stop_at": a.stop_at, "hard_stop": a.hard_stop, "budget": BUDGET, "per_function": PER_FUNCTION,
                   "vo_ci": {"wall_s": VO_CI_WALL, "mem_gib": 128, "core_h": VO_CI_CORE_H},
                   "prepass_wall_s": PREPASS_WALL},
        "known_limitations": KNOWN_LIMITATIONS,
        "problems": problems,
    }
    return d, problems


def check_inputs(d: dict) -> None:
    """The targets' inputs outside the frozen copy are unchanged since the start (a change is a crash)."""
    for k, p in INPUTS.items():
        if (sha256_file(p) if p.exists() else None) != d["inputs"][k]:
            raise RuntimeError(f"input {k} ({p}) changed since the run started")


# ---------------------------------------------------------------------------------------------- targets
def toml_value(v) -> str:
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        return str(v)
    if isinstance(v, str):
        return json.dumps(v)
    if isinstance(v, list):
        return "[" + ", ".join(toml_value(x) for x in v) + "]"
    if isinstance(v, dict):
        return "{ " + ", ".join(f"{k if re.fullmatch(r'[A-Za-z0-9_-]+', k) else json.dumps(k)} = {toml_value(x)}"
                                for k, x in v.items()) + " }"
    raise TypeError(f"no TOML for {v!r}")


def write_toml(path: Path, d: dict, header: list[str]) -> None:
    lines = [f"# {h}" for h in header]
    lines += [f"{k} = {toml_value(v)}" for k, v in d.items() if k != "variants"]
    for var in d.get("variants", []):
        lines += ["", "[[variants]]"] + [f"{k} = {toml_value(x)}" for k, x in var.items()]
    path.write_text("\n".join(lines) + "\n")
    # the target must read back as written
    if tomllib.loads(path.read_text()) != d:
        raise RuntimeError(f"{path}: TOML round trip differs")


class BlockedBuild(Exception):
    """A revision that the pinned build cannot build, found before `vo ci` runs: (side, revision, error)."""


def java_root(rev: str, side: str) -> str:
    for rel in ("lib/java/src/main/java", "lib/java/src"):
        if sh(["git", "-C", str(THRIFT), "cat-file", "-e", f"{rev}:{rel}/org/apache/thrift"]).returncode == 0:
            return rel
    raise BlockedBuild(side, rev, f"no Java main source root (lib/java/src/main/java or lib/java/src) at {rev}")


def read_jarsets(path: Path | None) -> dict[str, tuple[str, Path]]:
    """revision -> (jar set name, directory) from the Java jar-set table (language, revision, set, path, evidence)."""
    if path is None:
        return {}
    out = {}
    for r in csv.DictReader(open(path), delimiter="\t"):
        if r["language"] == "Java":
            out[r["revision"]] = (r["set"], Path(r["path"]))
    return out


def jar_set(inputs: dict, rev: str) -> tuple[str, Path, list[Path]]:
    """The jar set of a Java revision: (name, directory, jars in classpath order: sorted by name, as T1's compile.sh);
    the directory must match its SHA256SUMS."""
    if rev not in inputs.get("jarsets", {}):
        raise RuntimeError(f"Java revision {rev} is not in the jar-set table {inputs.get('jarsets_file')}")
    name, d = inputs["jarsets"][rev]
    chk = sh(["sha256sum", "--check", "--strict", "--quiet", "SHA256SUMS"], cwd=d)
    if chk.returncode != 0:
        raise RuntimeError(f"jar set {name} ({d}) does not match its SHA256SUMS: {chk.stdout[-300:]}{chk.stderr[-300:]}")
    jars = sorted(d.glob("*.jar"), key=lambda q: q.name)
    if not jars:
        raise RuntimeError(f"jar set {name} ({d}) has no jar")
    return name, d, jars


def rust_depset(inputs: dict, t1: dict, rev: str) -> dict:
    """The vendored dependency set of a Rust revision, by the sha256 of its lib/rs/Cargo.toml: the prepared set
    <rust depsets>/<sha256>/ (w-thrift-rsts's tools/thrift_rsts/t3_vendor_sets.py: Cargo.lock, vendor/, set.json with
    the cargo features to use), else, for the pin's Cargo.toml, T1's lock and vendor dir."""
    man = git("show", f"{rev}:lib/rs/Cargo.toml").encode()
    key = hashlib.sha256(man).hexdigest()
    root = Path(inputs.get("rust_depsets") or "/nonexistent")
    d = root / key if (root / key).is_dir() else root / key[:16]
    if (d / "Cargo.lock").exists():
        sj = json.loads((d / "set.json").read_text()) if (d / "set.json").exists() else {}
        feats = sj.get("cargo_features")
        if feats is None:
            feats = json.loads((d / "features.json").read_text()) if (d / "features.json").exists() else []
        lock, vendor, src = d / "Cargo.lock", d / "vendor", f"prepared set {d}"
        dep_features = sj.get("dep_features")
    elif key == inputs["pin_cargo_toml_sha256"]:
        lock = Path(t1["cargo_lock"]) if Path(t1["cargo_lock"]).is_absolute() else VO_LIVE / "targets" / t1["cargo_lock"]
        vendor, feats, src = Path(t1["vendor_dir"]), list(t1.get("cargo_features", [])), "T1 (the pin's Cargo.toml)"
        dep_features = t1.get("dep_features")
    else:
        raise RuntimeError(f"no vendored dependency set for lib/rs/Cargo.toml sha256 {key} at {rev} (expected {d})")
    return {"cargo_toml_sha256": key, "cargo_lock": str(lock), "cargo_lock_sha256": sha256_file(lock),
            "vendor_dir": str(vendor), "cargo_features": feats, "dep_features": dep_features, "source": src}


def adapter_has_vendor_sets(frozen: Path) -> bool:
    """Whether the frozen Rust adapter picks the dependency set per revision itself (target option `vendor_sets`,
    w-thrift-rsts's patch after T2's freeze): then p and c of one commit may use different locks."""
    f = frozen / "orch" / "veriforch" / "adapters" / "rust" / "build.py"
    return f.exists() and "vendor_sets" in f.read_text()


def make_target(frozen: Path, lang: str, p: str, c: str, tdir: Path, inputs: dict) -> tuple[Path, dict]:
    """The T3 library target of `lang` for the pair (p, c): (TOML path, facts for the record). BlockedBuild when a
    revision cannot be built with the pinned build (no Java source root; Java jar sets or Rust dependency sets that
    differ between p and c, which one target cannot hold)."""
    cfg = LANGS[lang]
    tdir.mkdir(parents=True, exist_ok=True)
    t1 = tomllib.loads((frozen / "targets" / f"{cfg['t1']}.toml").read_text())
    name = f"t3_thrift_{cfg['key']}"
    head = [f"PREREG_T_v1 T3: the {lang} library target of Thrift at {p[:12]}..{c[:12]}, made by scripts/prereg_t3.py",
            f"from targets/{cfg['t1']}.toml (T1). UNTRUSTED tree: nothing of it runs outside a sandbox."]
    info: dict = {"t1_target": f"targets/{cfg['t1']}.toml"}
    if "compdb" in cfg:
        if str(frozen / "scripts") not in sys.path:
            sys.path.insert(0, str(frozen / "scripts"))
        import t3_compdb as g                               # the frozen copy's generator
        tb, th = g.tus(THRIFT, p, cfg["compdb"]), g.tus(THRIFT, c, cfg["compdb"])
        both = [x for x in th if x in tb]
        db = g.entries(both, cfg["compdb"])
        cc = tdir / f"{cfg['key']}.compile_commands.json"
        cc.write_text(json.dumps(db, indent=1) + "\n")
        d = {k: v for k, v in t1.items() if k not in ("name", "compile_commands")}
        d = {"name": name, **{k: d[k] for k in ("lang", "root")}, "compile_commands": str(cc),
             **{k: v for k, v in d.items() if k not in ("lang", "root")}}
        info.update(tus_base=len(tb), tus_head=len(th), tus=len(both), compile_commands=str(cc),
                    compile_commands_sha256=sha256_file(cc),
                    tus_only_base=[x for x in tb if x not in th], tus_only_head=[x for x in th if x not in tb])
    elif lang == "Java":
        rb, rh = java_root(p, "base"), java_root(c, "head")
        if rb != rh:
            raise BlockedBuild("head", c, f"the Java source root moves in this commit ({rb} -> {rh}): one target "
                                          f"cannot hold both")
        (sb, db_, jb), (sc, dc, jc) = jar_set(inputs, p), jar_set(inputs, c)
        if (sb, db_) != (sc, dc):
            raise BlockedBuild("head", c, f"the jar sets differ between p ({sb}) and c ({sc}): one target holds one "
                                          f"class path")
        srcs = set()
        for rev in (p, c):
            for f in git("ls-tree", "-r", "--name-only", rev, "--", rb + "/").splitlines():
                if f.endswith(".java"):
                    srcs.add(f[len(rb) + 1:])
        cpath = ":".join(str(j) for j in jb)
        d = {k: v for k, v in t1.items() if k not in ("name", "jar", "jar_sha256", "variants", "sources", "root")}
        d = {"name": name, "lang": t1["lang"], "root": str(THRIFT / rb), "sources": sorted(srcs), **d,
             "sources_present_only": True,
             "variants": [{"name": "lib", "flags": ["-encoding", "UTF-8", "-cp", cpath]}]}
        if d["lang"] != "jimple" or d.get("release") != 8:
            raise RuntimeError(f"unexpected T1 Java target options: {d['lang']}, release {d.get('release')}")
        info.update(source_root=rb, sources=len(srcs), jar_set=sb, jar_dir=str(db_),
                    jars={j.name: sha256_file(j) for j in jb}, jar_set_sha256sums=sha256_file(db_ / "SHA256SUMS"))
    else:                                                   # Rust: T1's options; files beside it made absolute
        d = dict(t1)
        d["name"] = name
        for k in ("cargo_lock", "aeneas_prune_file"):
            if k in d and not Path(d[k]).is_absolute():
                src = (frozen / "targets" / d[k])
                d[k] = str(src if src.exists() else VO_LIVE / "targets" / d[k])
        # main 10-25: each revision's varint library gets its bodies extracted: varint_rs (from a0e43d07 on) and
        # integer_encoding (before); a pattern that matches no dependency extracts nothing
        d["charon_include"] = list(d.get("charon_include", [])) + [x for x in CHARON_INCLUDE_ADD
                                                                    if x not in d.get("charon_include", [])]
        rsb, rsc = rust_depset(inputs, d, p), rust_depset(inputs, d, c)
        info.update(rust_depset_base=rsb, rust_depset_head=rsc)
        if adapter_has_vendor_sets(frozen):
            # the adapter picks each revision's set (lock, vendor dir, features defined there, dep features of the
            # dependencies it has) from <dir>/<sha256 of that revision's Cargo.toml>/ (w-thrift-rsts's T3 patch); the
            # T3 prune file is T1's plus `"missing": "skip"` and the uuid rename matched by impl identity
            d.pop("cargo_lock", None)
            d.pop("vendor_dir", None)
            d["vendor_sets"] = str(Path(inputs["rust_depsets"]))
            d["aeneas_prune_file"] = str(RUST_PRUNE_T3)
            info["rust_mode"] = "vendor_sets (per revision, in the adapter)"
        else:
            # one target holds one Cargo.lock and one feature list: p and c must need the same ones (a Cargo.toml
            # change that leaves the lock as it is is fine)
            if (rsb["cargo_lock_sha256"], rsb["cargo_features"]) != (rsc["cargo_lock_sha256"], rsc["cargo_features"]):
                raise BlockedBuild("head", c, f"lib/rs/Cargo.toml changes in this commit and p and c need different "
                                              f"locks or features (lock {rsb['cargo_lock_sha256'][:12]} -> "
                                              f"{rsc['cargo_lock_sha256'][:12]}, features {rsb['cargo_features']} -> "
                                              f"{rsc['cargo_features']}): one target holds one Cargo.lock")
            d.update(cargo_lock=rsb["cargo_lock"], vendor_dir=rsb["vendor_dir"])
            if rsb["cargo_features"]:
                d["cargo_features"] = rsb["cargo_features"]
            else:
                d.pop("cargo_features", None)
            if rsb.get("dep_features") is not None:
                if rsb["dep_features"]:
                    d["dep_features"] = rsb["dep_features"]
                else:
                    d.pop("dep_features", None)
            info["rust_mode"] = "one set for both revisions"
        info.update({k: d.get(k) for k in ("cargo_lock", "vendor_dir", "vendor_sets", "cargo_features",
                                           "dep_features", "aeneas_prune_file", "charon_include")})
    path = tdir / f"{name}.toml"
    write_toml(path, d, head)
    info["toml"], info["toml_sha256"] = str(path), sha256_file(path)
    return path, info


def changed_files(lang: str, root: str, p: str, c: str) -> list[str]:
    """Files changed between p and c below the target root, relative to it."""
    rel = str(Path(root).relative_to(THRIFT))
    out = git("diff", "--name-only", "--no-renames", p, c, "--", rel + "/")
    return sorted(f[len(rel) + 1:] for f in out.splitlines() if f.startswith(rel + "/"))


# ---------------------------------------------------------------------------------------------- run helpers
def run_env(frozen: Path, pin_file: Path, extra: dict, no_llm: bool) -> dict:
    env = dict(os.environ)
    for k in ("VO_CIRLEAN_DIR", "VO_CIRLEAN_PIN", "VO_ROOT", "PYTHONPATH", "VO_CI_RUN_DIR", "VO_GUARD_LOG"):
        env.pop(k, None)            # scripts/vo sets them (pins from the pin file, VO_ROOT = the frozen copy)
    env["VO_CERT_PIN_ENV"] = str(pin_file)
    if no_llm:                      # belt and braces beside --budget 0: no client can be made
        for k in ("ANTHROPIC_VERTEX_PROJECT_ID", "ANTHROPIC_API_KEY", "CLOUD_ML_REGION"):
            env.pop(k, None)
    env.update(extra)
    return env


def core_seconds(guard_log: Path) -> float | None:
    if not guard_log.exists():
        return None
    vals = re.findall(r"metered ([0-9.]+) core-s", guard_log.read_text())
    return float(vals[-1]) if vals else None


def usage_rows(run_dir: Path) -> list[dict]:
    p = run_dir / "llm" / "usage.jsonl"
    if not p.exists():
        return []
    out = []
    for line in p.read_text().splitlines():
        try:
            out.append(json.loads(line))
        except ValueError:
            pass
    return out


def run_dir_for(base: Path, tag: str, lang_key: str, kind: str = "runs", share_proofs: bool = False) -> Path:
    """A run directory of the commit's own (an earlier attempt's is kept as <dir>.crash_<UTC>); the content-addressed
    .olean caches (atomic stores: lean.py) are shared per language through symlinks; proof, negative and by-body
    caches stay per commit (C1), unless share_proofs (--shared-caches all): then cache/proofs is shared per language
    too (atomic per-key stores, as T2's worker slots share it), so a unit whose proof key an earlier commit already
    settled is not attempted again. Neither cache enters an old ≡ new verdict (the verdict modules are checked anew)."""
    rd = base / kind / f"{tag}_{lang_key}"
    if rd.exists():
        rd.rename(rd.with_name(rd.name + f".crash_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}"))
    (rd / "cache").mkdir(parents=True)
    # olean_eqj / jimple_eqj: the Java equivalence package's compiled modules and its digest-named copies of each
    # revision's Jimple (adapters/jimple/equiv.py), content-addressed and stored atomically like the .olean caches
    for cdir in ("olean", "olean_cert", "olean_eqj", "jimple_eqj") + (("proofs",) if share_proofs else ()):
        shared = base / f"cache_{lang_key}" / cdir
        shared.mkdir(parents=True, exist_ok=True)
        (rd / "cache" / cdir).symlink_to(shared)
    return rd


def resource_wait(log, what: str) -> None:
    """Before every dispatch: wait while the 1-minute load > LOAD_MAX or MemAvailable < MEM_MIN (every wait is logged
    when it starts, every 5 minutes while it lasts, and when it ends)."""
    t0, last = time.time(), 0.0
    while True:
        load1 = float(Path("/proc/loadavg").read_text().split()[0])
        avail = next(int(x.split()[1]) for x in open("/proc/meminfo") if x.startswith("MemAvailable:")) * 1024
        if load1 <= LOAD_MAX and avail >= MEM_MIN:
            if last:
                log(f"resource wait for {what} over after {time.time() - t0:.0f} s (load {load1:.0f}, "
                    f"MemAvailable {avail / 1e9:.0f} GB)")
            return
        if time.time() - last >= 300:
            log(f"resource wait for {what}: load {load1:.0f} (dispatch at <= {LOAD_MAX:.0f}), MemAvailable "
                f"{avail / 1e9:.0f} GB (dispatch at >= {MEM_MIN / 1e9:.0f})")
            last = time.time()
        time.sleep(30)


def module_package(module: str, run_dir: Path) -> Path | None:
    """The package directory whose build holds the module's .olean (the newest when several do)."""
    rel = Path(".lake/build/lib/lean") / (module.replace(".", "/") + ".olean")
    cands = list(run_dir.glob("lean*/" + str(rel))) + list(run_dir.glob("lean*/*/" + str(rel)))
    if not cands:
        return None
    best = max(cands, key=lambda q: q.stat().st_mtime)
    return Path(str(best).split("/.lake/build/lib/lean/")[0])


def kernel_replay(ctx: dict, module: str, run_dir: Path, log_dir: Path, env: dict) -> tuple[bool, str]:
    """`lake env leanchecker <module>` in the package that built it (scripts/kernel_replay.sh); a package without a
    lakefile (the Rust pair package: lean with an explicit LEAN_PATH) runs the same leanchecker with that LEAN_PATH."""
    frozen = ctx["frozen"]
    pkg = module_package(module, run_dir)
    if pkg is None:
        return False, f"FAIL {module}: module not found in the run's packages"
    log_dir.mkdir(parents=True, exist_ok=True)
    if (pkg / "lakefile.toml").exists():
        cmd = [str(frozen / "scripts" / "kernel_replay.sh"), "--log-dir", str(log_dir)]
        # packages that put equiv-lean on LEAN_PATH without Lake: the C/C++ certificate package (adapters/cir/patch.py)
        # and the Java equivalence package (adapters/jimple/equiv.py, EqjPackage)
        extra = {"lean_cert": ctx["env"].get("VO_EQUIVLEAN_DIR"),
                 "lean_eqj": ctx["env"].get("VO_EQUIVLEAN_JIMPLE_DIR",
                                            str(frozen / "deps" / "equivlean-751764f-jimple-0149Z"))}.get(pkg.name)
        if extra:
            cmd += ["--extra-lean-path", f"{extra}/.lake/build/lib/lean"]
        kr = sh(cmd + [str(pkg), module], timeout=7200, env=env)
        line = next((x for x in kr.stdout.splitlines() if x.startswith(("PASS", "FAIL"))), kr.stdout.strip()[-300:])
        return kr.returncode == 0 and line.startswith("PASS"), line
    lean_path = ":".join([str(pkg / ".lake/build/lib/lean")] + ctx["rust_lean_dirs"]())
    logf = log_dir / f"{module}.log"
    t0 = time.time()
    with open(logf, "w") as lf:
        kr = subprocess.run([str(frozen / "scripts" / "run1.sh"), "-t", "1800", "-m", "64", "-c", "0.7", "--",
                             "env", f"LEAN_PATH={lean_path}", str(LEAN_BIN / "leanchecker"), module],
                            cwd=pkg, stdout=lf, stderr=subprocess.STDOUT, env=env, timeout=1900)
    out = [x for x in logf.read_text().splitlines() if x.strip()]
    dt = round(time.time() - t0, 1)
    if kr.returncode == 0 and not out:
        return True, f"PASS {module} ({dt} s; explicit LEAN_PATH)"
    return False, f"FAIL {module} ({dt} s, exit {kr.returncode}): {(out or ['no output'])[0][:300]}"


# ---------------------------------------------------------------------------------------------- outcomes
def commit_outcome(verdicts: list[dict], blocked: bool) -> str:
    """C1's driver (PREREG_C_v2 definitions), unchanged."""
    if blocked:
        return "blocked: build"
    kinds = [v.get("kernel_verdict") for v in verdicts]
    if not verdicts:
        return "unknown"
    if any(v.get("verdict") == "behaviour_changed" for v in verdicts):
        return "behaviour change shown"
    if all(k == "equivalent" for k in kinds):
        return "certified equivalent"
    if all(k in ("equivalent", "changed_only_where_old_unsafe") for k in kinds):
        return "certified conservative"
    if any(k for k in kinds):
        return "partly certified"
    return "unknown"


def functions_of(pre: dict, lang: str) -> tuple[list[dict], list[str], dict]:
    """From the pre-pass: the distinct changed functions with their home variant, the variants vo ci names, and the
    affected variants that did not build."""
    order = pre["order"]
    blocked = {vn: r["blocked"] for vn, r in pre["variants"].items() if r.get("affected") and r.get("blocked")}
    funcs: dict[tuple[str, str], dict] = {}
    for vn in order:
        r = pre["variants"].get(vn) or {}
        for name in r.get("changed", []):
            loc = (r.get("units_head", {}).get(name) or {}).get("loc", "")
            fil = loc.rpartition(":")[0] if loc else ""
            key = (name, fil)
            f = funcs.setdefault(key, {"language": lang, "unit": name, "file": fil, "loc": loc, "tus": []})
            f["tus"].append(vn)
    for f in funcs.values():
        # the TU compiled from the function's defining file, else the first TU (target order) where it changed
        own = [vn for vn in f["tus"] if f["file"] and pre["variants"][vn].get("source") == f["file"]]
        f["home"] = own[0] if own else f["tus"][0]
        f["key"] = f"{f['unit']}@{f['file']}" if f["file"] else f["unit"]
    homes = [vn for vn in order if any(f["home"] == vn for f in funcs.values())]
    names = homes + [vn for vn in order if vn in blocked and vn not in homes]
    return sorted(funcs.values(), key=lambda f: (order.index(f["home"]), f["key"])), names, blocked


# ---------------------------------------------------------------------------------------------- one commit
class Ctx(dict):
    pass


def run_language(ctx: Ctx, row: dict, lang: str, p: str, c: str, tag: str, log) -> dict:
    base, frozen = ctx["base"], ctx["frozen"]
    cfg = LANGS[lang]
    lrec: dict = {"language": lang, "started": utc()}
    if time.time() >= epoch(ctx["stop_at"]):
        lrec.update(status="unattempted", reason=f"stop time {ctx['stop_at']} reached before this language's run")
        return lrec
    check_inputs(ctx["pins"])
    try:
        toml, tinfo = make_target(frozen, lang, p, c, base / "targets" / tag, ctx["inputs"])
    except BlockedBuild as e:
        side, rev, err = e.args
        lrec.update(status="done", verdicts=[], changed_count=0, budget=0.0, variants=[],
                    blocked={"lib": {"revision": side, "rev": rev, "error": err}},
                    note="blocked before vo ci: the pinned build cannot take this revision pair")
        return lrec
    lrec["target"] = tinfo
    root = tomllib.loads(toml.read_text())["root"]
    files = changed_files(lang, root, p, c)
    lrec["changed_files"] = files
    # 2. front-end pre-pass
    prd = run_dir_for(base, tag, cfg["key"], "prepass")
    spec = prd / "spec.json"
    out = prd / "prepass.json"
    spec.write_text(json.dumps({"target": str(toml), "base": p, "head": c, "run_dir": str(prd),
                                "changed_files": files}, indent=1))
    glog_pre = base / "guard" / f"{tag}_{cfg['key']}.prepass.log"
    env_pre = run_env(frozen, ctx["pin_file"], {**ctx["env"], "VO_ROOT": str(frozen),
                                                "PYTHONPATH": str(frozen / "orch"), "VO_GUARD_LOG": str(glog_pre)},
                      ctx["no_llm"])
    t0 = time.time()
    with open(base / "logs" / f"{tag}_{cfg['key']}.prepass.log", "w") as lf:
        pp = subprocess.run([str(frozen / "scripts" / "run1.sh"), "-t", str(PREPASS_WALL), "-m", "128", "-c", "4",
                             "--", str(frozen / ".venv" / "bin" / "python"), "-B",
                             str(frozen / "scripts" / "t3_prepass.py"), str(spec), str(out)],
                            stdout=lf, stderr=subprocess.STDOUT, env=env_pre)
    lrec["prepass_seconds"] = round(time.time() - t0, 1)
    lrec["prepass_core_seconds"] = core_seconds(glog_pre)
    pre = json.loads(out.read_text()) if out.exists() else {"error": f"no pre-pass output (exit {pp.returncode})"}
    if pre.get("error"):
        lrec.update(status="crash", error=f"pre-pass: {pre['error']}"[-3000:])
        return lrec
    funcs, variants, blocked = functions_of(pre, lang)
    if ctx.get("front_end_only"):
        # main 10-25: list commits in a dry run get the front end only; no vo ci, no verdict
        lrec.update(status="front_end_only", changed_count=len(funcs), budget=round(PER_FUNCTION * len(funcs), 2),
                    variants=variants, blocked=blocked or None, verdicts=[],
                    prepass={"affected": [vn for vn in pre["order"] if (pre["variants"].get(vn) or {}).get("affected")],
                             "blocked": blocked, "variants_total": len(pre["order"]), "file": str(out)})
        return lrec
    lrec["prepass"] = {"affected": [vn for vn in pre["order"] if (pre["variants"].get(vn) or {}).get("affected")],
                       "why": {vn: r.get("why") for vn, r in pre["variants"].items() if r.get("affected")},
                       "blocked": blocked,
                       "changed_by_variant": {vn: r["changed"] for vn, r in pre["variants"].items() if r.get("changed")},
                       "variants_total": len(pre["order"]), "file": str(out)}
    lrec["changed_functions"] = funcs
    n = len(funcs)
    budget = round(PER_FUNCTION * n, 2)
    lrec.update(changed_count=n, budget=budget, variants=variants)
    if blocked and ctx.get("blocked_verdicts") == "skip" and "compdb" in cfg:
        # the strict rule already makes the commit blocked: build; vo ci names only the blocked TUs (it records the
        # block) and the verdict step of the TUs that built is not run (--blocked-verdicts skip)
        variants = [vn for vn in variants if vn in blocked]
        lrec.update(variants=variants, verdicts_skipped=f"blocked: build under the strict rule ({len(blocked)} "
                                                        f"affected TU(s) do not build); verdicts of the other TUs not run")
        funcs = []
        budget = 0.0
        lrec["budget"] = 0.0
    if not variants:
        lrec.update(status="done", verdicts=[], blocked=None,
                    note="no changed function: no affected TU" if "compdb" in cfg else "no changed function")
        return lrec
    # budget rule (C1's reservation): model $ spent + B of the language runs in flight + this B must stay below $300.
    # While other runs are in flight, a run that does not fit waits for them (their B is a cap, their spend is far
    # smaller); with nothing in flight, spent + B >= $300 is the budget's end: this and every later run are unattempted
    key = f"{tag}_{cfg['key']}"
    waited = 0.0
    while True:
        with ctx["lock"]:
            committed = ctx["spent"] + sum(ctx["inflight"].values())
            if ctx["stop"].is_set() or (committed + budget >= BUDGET and not ctx["inflight"]):
                ctx["stop"].set()
                lrec.update(status="unattempted", reason=f"T3 budget: spent ${ctx['spent']:.2f} + B ${budget:.2f} "
                                                         f">= ${BUDGET:.0f}")
                return lrec
            if committed + budget < BUDGET:
                ctx["inflight"][key] = budget
                break
        if waited % 1800 == 0:
            log(f"T3 {key}: B ${budget:.2f} waits for in-flight runs (spent ${ctx['spent']:.2f}, in-flight B "
                f"${committed - ctx['spent']:.2f})")
        time.sleep(60)
        waited += 60
    if waited:
        lrec["budget_wait_seconds"] = waited
    try:
        # C1's job limits (6 h, 8 core-h) hold for a few changed functions; each verdict may take ~10 min (its checks run
        # to the 590 s timeout), so the limits grow with the number of verdicts this run computes (15 min and 0.3
        # core-h each), and the wall always ends by the hard stop
        nv = len(funcs)
        wall = int(min(max(VO_CI_WALL, 900 * nv + 3600), epoch(ctx["hard_stop"]) - time.time()))
        core_cap = max(VO_CI_CORE_H, round(0.3 * nv + 2, 1))
        if wall < 1800:
            lrec.update(status="unattempted", reason=f"less than 30 min left before the hard stop {ctx['hard_stop']}")
            return lrec
        rd = run_dir_for(base, tag, cfg["key"], share_proofs=ctx.get("shared_caches") == "all")
        if lang == "Rust" and (prd / "rust_fe").is_dir():
            # the pre-pass's Charon/Aeneas outputs of these two revisions (keyed by the crate's content and the
            # front-end options; adapters/rust/build.py `_frontend`): vo ci reuses them instead of recomputing
            (rd / "rust_fe").symlink_to(prd / "rust_fe")
        glog = base / "guard" / f"{tag}_{cfg['key']}.log"
        for old in (glog, base / "logs" / f"{tag}_{cfg['key']}.log"):
            if old.exists():
                old.rename(old.with_name(old.name + f".crash_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}"))
        vargs = [x for vn in variants for x in ("--variant", vn)] if "compdb" in cfg else []
        b_arg = 0.0 if ctx["no_llm"] else budget
        jobs = []
        if lang == "Java":
            with ctx["lock"]:               # main 10-25: --jobs 11 for the first Java build (a cold .olean cache)
                if not ctx["java_jobs_used"]:
                    ctx["java_jobs_used"] = True
                    jobs = ["--jobs", str(JAVA_FIRST_JOBS)]
        cmd = [str(frozen / "scripts" / "run1.sh"), "-t", str(wall), "-m", "128", "-c",
               str(core_cap if not jobs else core_cap * 2), "--",
               str(frozen / "scripts" / "vo"), "ci", str(toml), "--base", p, "--head", c, *vargs,
               "--attempts", "0", "--budget", f"{b_arg:.2f}", "--check-timeout", "600", *jobs]
        lrec["command"] = " ".join(cmd)
        env = run_env(frozen, ctx["pin_file"], {"VO_CI_RUN_DIR": str(rd), "VO_GUARD_LOG": str(glog)}, ctx["no_llm"])
        t0 = time.time()
        with open(base / "logs" / f"{tag}_{cfg['key']}.log", "w") as lf:
            proc = subprocess.run(cmd, stdout=lf, stderr=subprocess.STDOUT, env=env)
        lrec.update(exit=proc.returncode, seconds=round(time.time() - t0, 1), core_seconds=core_seconds(glog),
                    wall=wall, run_dir=str(rd))
        rows = usage_rows(rd)
        lrec.update(model_calls=len(rows), model_dollars=round(sum(x.get("dollars", 0) for x in rows), 4))
        if ctx["no_llm"] and rows:
            lrec.update(status="crash", error=f"{len(rows)} model call(s) in a --no-llm run")
            return lrec
        ci = rd / "ci" / f"{p}..{c}" / "ci.json"
        if not ci.exists():
            at_wall = proc.returncode in (124, 137) or lrec["seconds"] >= wall - 120
            if at_wall and wall < max(VO_CI_WALL, 900 * nv + 3600):
                # the wall was shortened to end by the hard stop: the stop rule, not a tool failure
                lrec.update(status="unattempted", reason=f"vo ci stopped at its wall ({wall} s), which ends at the hard "
                                                         f"stop {ctx['hard_stop']} (T3 stop rule)")
            else:
                lrec.update(status="crash", error=("vo ci reached its wall of {} s (exit {}): no ci.json".format(
                    wall, proc.returncode) if at_wall else f"no ci.json (exit {proc.returncode}; see the log)"))
            return lrec
        lrec["ci_json"] = str(ci)
        rep = json.loads(ci.read_text())
        got: dict[tuple[str, str], dict] = {}
        vo_blocked = {}
        for vn, vr in rep["variants"].items():
            if vr.get("blocked"):
                vo_blocked[vn] = {"revision": vr["revision"], "rev": vr.get("rev"), "error": vr["error"][-2000:]}
            for u in vr.get("units", []):
                if u.get("changed"):
                    got[(vn, u["unit"])] = u.get("equivalence") or {
                        "verdict": "unknown",
                        "detail": NO_EQUIV.get(lang, "no verdict recorded")}
        lrec["vo_ci_blocked"] = vo_blocked
        lrec["vo_ci_changed_by_variant"] = {vn: vr.get("changed", []) for vn, vr in rep["variants"].items()}
        verdicts = []
        for f in funcs:
            v = dict(got.get((f["home"], f["unit"])) or
                     {"verdict": "unknown",
                      "detail": (f"its home TU {f['home']} is blocked in vo ci" if f["home"] in vo_blocked
                                 else f"vo ci's build of {f['home']} does not list it as changed (the pre-pass did)")})
            v.update(unit=f["unit"], function=f["key"], language=lang, tu=f["home"])
            if v.get("verdict") not in VERDICTS:
                # an adapter verdict outside PREREG_C_v2's four is an unknown with its reason, the adapter's word kept:
                # the Java hook's `unchanged` (byte-identical class file; Soot names locals differently) reads
                # "bytecode identical; no verdict theorem" (main 10-25)
                v["adapter_verdict"] = v.get("verdict")
                why = str(v.get("detail") or v.get("reason") or "")
                v["detail"] = ("bytecode identical; no verdict theorem" + (f" ({why})" if why else "")
                               if v.get("verdict") == "unchanged" else f"adapter verdict `{v.get('verdict')}`: {why}")
                v["verdict"] = "unknown"
            if lang == "Java" and SYNTHETIC_RE.search(f["unit"]):
                v["synthetic"] = True       # a compiler-made method (lambda body, accessor): reported apart
            if lang == "Java" and "(kernel) deep recursion" in json.dumps(v):
                v["known_limitation"] = JAVA_DEEP_RECURSION
            if v.get("verdict") in ("equivalent", "changed_only_where_old_unsafe") and v.get("module"):
                ok, line = kernel_replay(ctx, v["module"], rd, base / "replay" / f"{tag}_{cfg['key']}", env)
                v["kernel_replay"] = line
                v["axioms_standard"] = set(v.get("axioms") or ["(none recorded)"]) <= STD_AXIOMS
                v["kernel_verdict"] = v["verdict"] if ok and v["axioms_standard"] else None
            verdicts.append(v)
        lrec["verdicts"] = verdicts
        lrec["blocked"] = {**blocked, **vo_blocked} or None
        lrec["status"] = "done"
        return lrec
    finally:
        with ctx["lock"]:
            ctx["inflight"].pop(key, None)
            ctx["spent"] += lrec.get("model_dollars") or 0.0


def run_commit(ctx: Ctx, row: dict, worker: int, dispatched_at: str, log) -> dict:
    base = ctx["base"]
    c = row["commit"]
    p = git("rev-parse", c + "^1").strip()
    tag = f"{int(row['order']):03d}_{c[:12]}"
    langs = [x for x in row["languages"].split(",") if x]
    rec = {"order": int(row["order"]), "commit": c, "parent": p, "date": row.get("date"), "rules": row.get("rules"),
           "languages": langs, "subject": row.get("subject"), "started": utc(), "worker": worker,
           "dispatched_at": dispatched_at, "no_llm": ctx["no_llm"], "by_language": {}}
    for lang in langs:
        if lang not in LANGS:
            rec["by_language"][lang] = {"status": "crash", "error": f"no T3 target for language {lang}"}
            continue
        try:
            rec["by_language"][lang] = run_language(ctx, row, lang, p, c, tag, log)
        except Exception as e:                  # a driver failure is a crash of this commit: --resume re-runs it
            import traceback
            rec["by_language"][lang] = {"language": lang, "status": "crash",
                                        "error": f"driver: {type(e).__name__}: {e}"[-2000:],
                                        "traceback": traceback.format_exc()[-4000:]}
    L = rec["by_language"].values()
    rec["budget"] = round(sum(x.get("budget") or 0 for x in L), 2)
    rec["model_dollars"] = round(sum(x.get("model_dollars") or 0 for x in L), 4)
    rec["core_seconds"] = round(sum((x.get("core_seconds") or 0) + (x.get("prepass_core_seconds") or 0) for x in L), 1)
    rec["changed_count"] = sum(x.get("changed_count") or 0 for x in L)
    verdicts = [v for x in L for v in x.get("verdicts") or []]
    rec["verdicts"] = verdicts
    blocked = {f"{x['language']}:{vn}": b for x in L for vn, b in (x.get("blocked") or {}).items()}
    rec["blocked"] = blocked or None
    statuses = {x.get("status") for x in L}
    if "crash" in statuses:
        rec["outcome"] = "crash"
    elif "front_end_only" in statuses:
        rec["outcome"] = "front end only"       # a dry run's list commit: no verdict step ran
        rec["front_end_blocked"] = bool(blocked)
    elif "unattempted" in statuses and statuses <= {"unattempted"}:
        rec["outcome"] = "unattempted"
        rec["reason"] = "; ".join(x.get("reason", "") for x in L)
    elif "unattempted" in statuses:             # one language ran, a stop rule stopped another
        rec["outcome"] = "unattempted"
        rec["reason"] = "partly unattempted: " + "; ".join(x.get("reason", "") for x in L if x.get("reason"))
    else:
        rec["outcome"] = commit_outcome(verdicts, bool(blocked))
        alt = verdicts + [{"verdict": "unknown", "unit": f"<{k}>", "detail": "blocked: build"} for k in blocked]
        rec["outcome_blocked_only_if_nothing_builds"] = commit_outcome(alt, bool(blocked) and not verdicts)
        if not rec["changed_count"] and not blocked:
            rec["outcome_note"] = "no changed function in the built library"
    rec["finished"] = utc()
    (base / "records" / f"{tag}.json").write_text(json.dumps(rec, indent=1))
    return rec


# ---------------------------------------------------------------------------------------------- driver
def select_rows(a) -> list[dict]:
    src = Path(a.commits_file) if a.commits_file else COMMITS
    rows = list(csv.DictReader(open(src), delimiter="\t"))
    if a.orders:
        want = {int(x) for x in a.orders.split(",")}
        rows = [r for r in rows if int(r["order"]) in want]
    if a.first:
        rows = rows[:a.first]
    return rows


def main() -> int:
    global LOAD_MAX
    ap = argparse.ArgumentParser()
    ap.add_argument("--frozen", default=None, help="the frozen copy this driver belongs to (scripts/freeze_copy.sh)")
    ap.add_argument("--pins", default=None, help="pin file (env syntax, as scripts/cert_pin.env)")
    ap.add_argument("--workers", type=int, default=1, help=f"commits in flight (at most {MAX_WORKERS})")
    ap.add_argument("--resume", action="store_true", help="skip commits whose record has an outcome other than crash")
    ap.add_argument("--stop-at", default=STOP_AT)
    ap.add_argument("--hard-stop", default=HARD_STOP)
    ap.add_argument("--load-max", type=float, default=LOAD_MAX)
    ap.add_argument("--plan", action="store_true", help="targets and commands only; nothing runs")
    ap.add_argument("--no-llm", action="store_true", help="a dry run: vo ci --budget 0 and no model credentials")
    ap.add_argument("--front-end-only", action="store_true",
                    help="dry runs only: targets and front-end pre-passes (materialise, build both revisions); no vo ci, "
                         "so no verdict is computed (main 10-25: the rule for list commits in a dry run)")
    ap.add_argument("--out", default=None, help="output directory (dry runs: runs/t3_dryrun_<UTC>)")
    ap.add_argument("--commits-file", default=None, help="dry runs only: commits outside the frozen list (same TSV)")
    ap.add_argument("--java-jarsets", default=None,
                    help="the Java jar-set table (language, revision, set, path, evidence): every Java revision's jars")
    ap.add_argument("--rust-depsets", default=None,
                    help="directory of prepared Rust dependency sets, <sha256(lib/rs/Cargo.toml)[:16]>/{Cargo.lock,"
                         "vendor/,features.json}; the pin's Cargo.toml uses T1's lock and vendor")
    ap.add_argument("--shared-caches", choices=["olean", "all"], default="all",
                    help="all (main 10-25, the T3 setting): the .olean and proof caches (proofs, failures, by-body) "
                         "shared per language, i.e. per library target, across commits; olean: proof caches per commit")
    ap.add_argument("--blocked-verdicts", choices=["run", "skip"], default="skip",
                    help="C/C++: skip (default; main 10-25, the evidence-owner session: a blocked commit's outcome is blocked: build whatever "
                         "its other TUs give) or run the verdict step of the TUs that built when another affected TU "
                         "does not build")
    ap.add_argument("--first", type=int, default=None)
    ap.add_argument("--orders", default=None, help="comma-separated orders of the commits file")
    a = ap.parse_args()
    LOAD_MAX = a.load_max
    import resource
    soft = resource.getrlimit(resource.RLIMIT_AS)[0]
    if not a.plan and soft != resource.RLIM_INFINITY and soft < 130 * 2**30:
        # nested run1.sh jobs set their own address-space caps (vo ci 128 GiB, replays 64 GiB); under a lower limit
        # they cannot, and run1.sh's warning line would make every kernel replay a FAIL
        raise SystemExit(f"address-space limit {soft / 2**30:.0f} GiB < 130 GiB: run the driver under "
                         f"scripts/run1.sh -m 256")
    if not 1 <= a.workers <= MAX_WORKERS:
        raise SystemExit(f"--workers must be 1..{MAX_WORKERS} (main's T3 rule: 6 jobs; 12 only on main's word)")
    out = Path(a.out).resolve() if a.out else OUT_REAL
    real = out == OUT_REAL.resolve()
    if real and not a.plan and (a.no_llm or a.commits_file or a.first or a.orders or a.front_end_only):
        raise SystemExit("the real T3 directory takes the whole frozen list with the model: no --no-llm, "
                         "--commits-file, --first, --orders or --front-end-only there")
    if a.front_end_only and not a.no_llm:
        raise SystemExit("--front-end-only is for --no-llm dry runs")
    if not real and not a.plan and not (a.no_llm and re.fullmatch(r"t3_dryrun_[0-9TZ]+", out.name)
                                        and out.parent == (LIVE / "runs").resolve()):
        raise SystemExit("a run outside runs/prereg/T3 must be a --no-llm dry run in runs/t3_dryrun_<UTC>")
    if not a.pins:
        raise SystemExit("--pins FILE is required")
    pin_file = Path(a.pins).resolve()
    pkg_sha = check_package()
    frozen = frozen_copy(a.frozen, a.plan)
    d, problems = pins(frozen, pin_file, pkg_sha, a)
    rows = select_rows(a)
    inputs = {"jarsets": read_jarsets(Path(a.java_jarsets).resolve() if a.java_jarsets else None),
              "jarsets_file": str(Path(a.java_jarsets).resolve()) if a.java_jarsets else None,
              "rust_depsets": str(Path(a.rust_depsets).resolve()) if a.rust_depsets else None,
              "pin_cargo_toml_sha256": hashlib.sha256(git("show", f"{THRIFT_PIN}:lib/rs/Cargo.toml").encode()).hexdigest()}
    sets = {}
    for name, dd in sorted(set(inputs["jarsets"].values())):
        sums = dd / "SHA256SUMS"
        sets[name] = {"dir": str(dd), "SHA256SUMS_sha256": sha256_file(sums) if sums.exists() else None}
        if not sums.exists():
            problems.append(f"jar set {name}: no {sums}")
    d["java_jarsets"] = {"file": inputs["jarsets_file"], "revisions": len(inputs["jarsets"]),
                         "sha256": sha256_file(Path(inputs["jarsets_file"])) if inputs["jarsets_file"] else None,
                         "sets": sets}
    rsets = {}
    if inputs["rust_depsets"] and Path(inputs["rust_depsets"]).is_dir():
        for sd in sorted(Path(inputs["rust_depsets"]).iterdir()):
            if (sd / "Cargo.lock").exists():
                rsets[sd.name] = {"Cargo.lock_sha256": sha256_file(sd / "Cargo.lock"),
                                  "features": json.loads((sd / "features.json").read_text())
                                  if (sd / "features.json").exists() else None}
    d["rust_depsets"] = {"dir": inputs["rust_depsets"], "sets": rsets,
                         "pin_cargo_toml_sha256": inputs["pin_cargo_toml_sha256"]}
    if any("Java" in r["languages"].split(",") for r in rows) and not inputs["jarsets"]:
        problems.append("Java commits selected but no --java-jarsets table")

    def log(msg: str) -> None:
        print(f"{utc()} {msg}", flush=True)

    if a.plan:
        print(json.dumps({k: d[k] for k in ("pin_file", "cirlean", "equivlean", "jimplelean", "rust", "thrift",
                                             "inputs", "problems")}, indent=1))
        tdir = (LIVE / "scratch" / "thrift_t3" / "plan")
        for r in rows:
            c = r["commit"]
            p = git("rev-parse", c + "^1").strip()
            tag = f"{int(r['order']):03d}_{c[:12]}"
            for lang in [x for x in r["languages"].split(",") if x]:
                try:
                    toml, info = make_target(frozen, lang, p, c, tdir / tag, inputs)
                    files = changed_files(lang, tomllib.loads(toml.read_text())["root"], p, c)
                    print(f"\n# order {r['order']} {c[:12]} {lang}: target {toml} ({info.get('tus', info.get('sources', ''))}"
                          f" TUs/sources); changed files {files}")
                    print(f"VO_CI_RUN_DIR={out}/runs/{tag}_{LANGS[lang]['key']} VO_CERT_PIN_ENV={pin_file} "
                          f"{frozen}/scripts/run1.sh -t {VO_CI_WALL} -m 128 -c {VO_CI_CORE_H} -- {frozen}/scripts/vo ci "
                          f"{toml} --base {p} --head {c} [--variant <home TU>]... --attempts 0 --budget <0.50 x changed "
                          f"functions from the pre-pass> --check-timeout 600")
                except BlockedBuild as e:
                    print(f"\n# order {r['order']} {c[:12]} {lang}: blocked: build before vo ci: {e.args[2]}")
                except Exception as e:
                    print(f"\n# order {r['order']} {c[:12]} {lang}: TARGET FAILS: {type(e).__name__}: {e}")
        return 0
    if problems:
        raise SystemExit("refusing to start T3:\n  " + "\n  ".join(problems))
    out.mkdir(parents=True, exist_ok=True)
    pp = out / "pins.json"
    if pp.exists() and not a.resume:
        raise SystemExit(f"{pp} exists (a run already started; --resume, no re-pin during a run)")
    if a.resume:
        old = json.loads(pp.read_text())
        same = lambda k, f: (old.get(k) or {}).get(f) == (d.get(k) or {}).get(f)
        bad = [f"{k}.{f}" for k, f in (("cirlean", "commit"), ("cert_cirlean", "commit"), ("equivlean", "commit"),
                                       ("jimplelean", "SHA256SUMS_sha256"), ("prereg_package", "SHA256SUMS_T_v1"))
               if not same(k, f)]
        bad += [k for k in ("lean", "clang", "inputs", "rust") if old.get(k) != d.get(k)]
        if bad:
            raise SystemExit(f"--resume: pins differ from the recorded ones in {bad} (no re-pin during a run)")
        old.setdefault("resumed", []).append({"at": utc(), "frozen_copy": str(frozen),
                                              "manifest_sha256": d["veriforch"]["manifest_sha256"],
                                              "workers": a.workers})
        pp.write_text(json.dumps(old, indent=1))
        d = old
    else:
        pp.write_text(json.dumps(d, indent=1))
    for sub in ("records", "logs", "guard", "runs", "prepass", "targets", "replay"):
        (out / sub).mkdir(parents=True, exist_ok=True)
    sys.path.insert(0, str(frozen / "orch"))
    os.environ.update({k: v for k, v in d["pin_file"]["env"].items()})
    os.environ["VO_ROOT"] = str(frozen)

    def rust_lean_dirs() -> list[str]:
        from veriforch.adapters.rust import build as rb      # noqa: E402 (imported with the pins set)
        return rb.lean_dirs()

    ctx = Ctx(base=out, frozen=frozen, pin_file=pin_file, env=d["pin_file"]["env"], pins=d, no_llm=a.no_llm,
              front_end_only=a.front_end_only, shared_caches=a.shared_caches, blocked_verdicts=a.blocked_verdicts,
              stop_at=a.stop_at, hard_stop=a.hard_stop, lock=threading.Lock(), inflight={}, spent=0.0,
              stop=threading.Event(), rust_lean_dirs=rust_lean_dirs, inputs=inputs,
              java_jobs_used=any((json.loads(f.read_text()).get("by_language") or {}).get("Java", {}).get("command")
                                 for f in (out / "records").glob("*.json") if f.is_file()))
    summary = out / "t3_results.jsonl"
    ctx["spent"] = sum(json.loads(f.read_text()).get("model_dollars") or 0.0
                       for f in (out / "records").glob("*.json*") if f.is_file())
    plan = []
    for r in rows:
        tag = f"{int(r['order']):03d}_{r['commit'][:12]}"
        f = out / "records" / f"{tag}.json"
        if a.resume and f.exists() and json.loads(f.read_text()).get("outcome") != "crash":
            continue
        plan.append((r, tag))
    log(f"T3: {len(plan)} commits to dispatch with {a.workers} workers; spent so far ${ctx['spent']:.2f}; "
        f"out {out}; frozen {frozen}; no_llm {a.no_llm}")
    from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
    free = list(range(1, a.workers + 1))
    inflight: dict = {}

    def collect(futs) -> None:
        for fut in futs:
            tag, w = inflight.pop(fut)
            free.append(w)
            free.sort()
            try:
                rec = fut.result()
            except Exception as e:
                rec = {"order": int(tag.split("_")[0]), "commit": tag.split("_", 1)[1], "outcome": "crash",
                       "error": f"driver: {type(e).__name__}: {e}"[-2000:], "worker": w, "finished": utc()}
                (out / "records" / f"{tag}.json").write_text(json.dumps(rec, indent=1))
            with open(summary, "a") as fh:
                fh.write(json.dumps({k: rec.get(k) for k in ("order", "commit", "languages", "outcome", "budget",
                                                              "changed_count", "model_dollars", "core_seconds")}) + "\n")
            log(f"T3 {tag} (worker {w}): {rec.get('outcome')} (changed {rec.get('changed_count')}, "
                f"${rec.get('model_dollars')}, {rec.get('core_seconds')} core-s); spent ${ctx['spent']:.2f}")

    def unattempted(rest, why: str) -> None:
        for r2, tag2 in rest:
            rec = {"order": int(r2["order"]), "commit": r2["commit"], "languages": r2["languages"].split(","),
                   "subject": r2["subject"], "outcome": "unattempted", "reason": why, "finished": utc()}
            (out / "records" / f"{tag2}.json").write_text(json.dumps(rec, indent=1))
            with open(summary, "a") as fh:
                fh.write(json.dumps({k: rec.get(k) for k in ("order", "commit", "languages", "outcome")}) + "\n")

    with ThreadPoolExecutor(max_workers=a.workers) as ex:
        for k, (r, tag) in enumerate(plan):
            while len(inflight) >= a.workers:
                done, _ = wait(list(inflight), return_when=FIRST_COMPLETED)
                collect(done)
            resource_wait(log, tag)
            collect([f for f in list(inflight) if f.done()])
            if time.time() >= epoch(a.stop_at) or ctx["stop"].is_set():
                why = (f"stop time {a.stop_at} reached" if time.time() >= epoch(a.stop_at)
                       else "T3 budget reached (spent + in-flight B >= $300)")
                log(f"T3 stop: {why}: {len(plan) - k} commits unattempted")
                unattempted(plan[k:], why)
                break
            old = out / "records" / f"{tag}.json"
            if old.exists():                    # a crashed attempt (--resume): kept beside the new one
                old.rename(old.with_name(f"{tag}.json.crash_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}"))
            w = free.pop(0)
            fut = ex.submit(run_commit, ctx, r, w, utc(), log)
            inflight[fut] = (tag, w)
            log(f"T3 dispatch {tag} {r['languages']} -> worker {w} (in flight {len(inflight)})")
        while inflight:
            done, _ = wait(list(inflight), return_when=FIRST_COMPLETED)
            collect(done)
    log("T3 done")
    return 0


if __name__ == "__main__":
    sys.exit(main())

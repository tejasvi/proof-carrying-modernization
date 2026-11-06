#!/usr/bin/env python3
"""Pre-registration T, step T2 (frozen v1: ~/fv_paper/prereg/PREREG_T_v1.md, SHA256SUMS_T_v1): the driver.

    .venv/bin/python -B scripts/prereg_t2.py --sample T/<sample>.tsv [--addendum T/ADDENDUM_T2_sample.md]
        --cirlean SHA [--jimple-snapshot NAME] [--strictts SHA] [--aeneas PIN] --frozen DIR
        [--workers 16 --free-slots 12 --load-max 450 --mem-min-gb 150] [--resume] [--dry-run --first K] ...

Adapted from D2's driver (~/veriforch_frozen/D2_20261025T030336Z/scripts/prereg_d2.py): the same per-unit procedure,
outcome mapping (R6 of PREREG_D_v2, with the readings recorded in DEVIATIONS.md for D), ledger, worker slots and
disjoint-closure dispatch, extended to one sample that mixes languages and targets.

Sample: the frozen T2 sample (draw_t2.py's TSV: order, language, component, unit, path, N_s, n_s, weight), processed in
its `order` (one seeded permutation of the whole sample, so that every attempted prefix is a random subsample).

Targets (frozen copies; every vo run directory of the run is runs/<run prefix>_<name>, --run-prefix: `t2` for the real
run, `t2dry[_<tag>]` for dry runs, so that a dry run never shares a run directory, proof cache or usage log with the
real T2, and T1's runs/<name> stay as they are):
  C++  lib/cpp units: targets/thrift_cpp_{protocol,transport,server,other}.toml (all four have root lib/cpp/src);
       compiler/cpp units: targets/thrift_cpp_compiler.toml;
  C    targets/thrift_c_glib.toml;
  Java targets/thrift_java.toml;  Rust targets/thrift_rs.toml;  TS: none (the T2 frame has no TS unit).
  A C/C++ target is a compile_commands target: one build variant per translation unit (TU). Every C/C++ command of the
  run names the TU (`--variant`), so that one TU's front-end failure never stops another TU's unit.

Procedure (PREREG_T_v1 T2; D's R7):
 0. Pins recorded at start (pins.json): bridge directories and commits/snapshots, Lean, clang, Soot/JDK, the sample's
    and the addendum's sha256, the T1 unit lists' sha256, the frozen copy's manifest and veriforch's source manifest.
 1. Front end and extraction once per library before the first unit (C/C++: once per TU, the unit veriforch builds):
    `vo verify <target> [--variant <TU>] --only __vo_prepare_no_unit__ --no-llm --check-timeout 600` builds the units
    and compiles every generated module at its fixed 900 s timeout (R9). Cost per library in prepare/; a library (TU)
    that fails here is `blocked: front end/extraction: <error class>` for its units (R6).
 2. Per unit u, in sample order:
    a. `timeout 600 vo verify <target> [--variant <TU>] --only <u and every callee in its closure> --attempts 3
       --check-timeout 600 --budget 0.25` (the 10-minute wall per unit);
    b. if u ends `stuck` (or `budget`) and the bridge has an executable semantics (cirlean for C/C++, the Rust
       adapter), `vo cex <target> [--variant <TU>] --only u --budget <0.25 minus what 2a spent>` within the unit's
       remaining wall;
    c. the kernel replay (`scripts/kernel_replay.sh`: `lake env leanchecker <module>`) of every theorem claimed in this
       unit's run, in the package that built it (outside the wall).
    A callee proved for an earlier unit is reused at no cost (the target's shared proof cache).
 3. Outcomes (R6 of PREREG_D_v2 with D's readings, DEVIATIONS.md): proved_mechanical, proved_model_stated, native,
    conditional, partial, refuted, blocked (with the gap name), timeout, infrastructure_error. Readings applied:
    a negative-cache `stuck` (verify reuses a recorded failure and writes no unit record) is a timeout; a kill at the
    wall is a timeout whatever status was recorded; a tool crash is an infrastructure error (until its crash fix and
    re-run); a proof that checks but fails kernel replay is an infrastructure error "replay failed".

Matching a sample row to a front-end unit (fixed here, before the run):
  C/C++: the T1 key (notes/thrift/T1_cxx_units.tsv) is the symbol (`sym`), `sym@path` for an internal-linkage symbol,
    or `qualified-name@path:line` for a definition that no TU emitted at T1 (spaces %20-encoded). Candidates are the
    units of every prepared TU of the language's targets whose root holds the path: same symbol (and, for `sym@path`,
    defined in `path`); for a T1 not-emitted key, a unit defined at path:line with that unqualified name. Several
    candidates: an in-scope one first, then the fewest gap names in its scope, then target and TU order. No candidate:
    if a TU whose front end failed defines the symbol in its ClangIR, the unit is blocked by that TU's front end;
    otherwise it is blocked: not emitted by the front end.
  Java: `Class#method(descriptor)` -> the unit named `Class.method(<Java parameter types>)` (D2's jimple rule); when a
    real method and its bridge share that name, the one whose signature has the descriptor's return type (bridges are
    outside the frame). The record notes `name_shared`: veriforch keys units by name, so until its adapter fix
    `--only <name>` may reach the bridge.
  Rust: the key is the units.json name (one library, variant `default`).

Workers (--workers N): units start strictly in sample order, never skipping ahead. A unit starts only when its closure
(target, unit names) is disjoint from the closures of the running units of the same target. Worker k > 0 has its own
vo run directory per target (runs/<prefix>_<name>_w<k>, through a copy of the target file with that name) whose cache/ is a
symlink to the target's run directory's cache/: proofs, compiled modules and failures are shared, while each vo process
writes its own package, unit records, model ledger and verify.json. No unit starts while MemAvailable < --mem-min-gb
(150 GB); the first --free-slots units in flight run whatever the load, and above that a unit waits while the 1-minute
load > --load-max. The same guard holds for step 1. Every wait is logged.

Stop rules: model spend (runs/prereg/T2/ledger.json, the rows the units' commands add to each run directory's
llm/usage.jsonl) plus $0.25 per unit in flight reaching $500, or the clock reaching --stop-at (Tue 2026-10-27
03:00Z): no unit is dispatched after that; units in flight finish within their wall. Unattempted units are recorded
and left out of the denominators.

Analysis (summary.json, summary.md): per stratum (language x component) counts and proportions of every outcome with
Wilson 95% intervals; per language and overall the stratified estimate sum_s (N_s / N_frame) p_s over the strata with
attempted units, with a normal 95% interval from sum_s (N_s / N_frame)^2 p_s (1 - p_s) / n_s (n_s = attempted units of
the stratum), next to the unweighted proportions (Wilson). N_frame is the frame of the language (or of all languages),
as written; `renormalised` divides by the frame share of the strata with attempted units instead (equal when every
stratum has attempted units). Cost per unit (model $ and core-seconds: median, IQR, mean, total), gap names.

--dry-run: --no-llm and a $0 counterexample step (no model call is possible: veriforch's LLM refuses any call once its
run budget, here 0, is spent); run directories runs/t2dry[_<tag>]_<name> (never the real run's); records in
runs/prereg/T2_dryrun[_<tag>]; nothing in the T2 ledger;
the first --first units (default 5) of the --sample file, which for a dry run may be any TSV in the sample's format.
With --prepare-scope needed (the default for dry runs) only the TUs that may hold the selected C/C++ units are
prepared (from notes/thrift/T1_cxx.json's `tus`); a real run prepares every TU.

Launch (an orchestrator like D2's: its heavy steps run under scripts/run1.sh themselves, so wrap it with a large -m and
a core-hour cap for the whole run):
    scripts/run1.sh -t 172800 -m 256 -c <core-h> -l runs/prereg/T2.guard.log -- \\
        .venv/bin/python -B <frozen>/scripts/prereg_t2.py --frozen <frozen> --sample ... --cirlean ...
"""
from __future__ import annotations

import argparse
import calendar
import csv
import fcntl
import hashlib
import json
import math
import os
import re
import shutil
import statistics
import subprocess
import sys
import threading
import time
from pathlib import Path

VO = Path("/home/user/veriforch")
PREREG = Path("/home/user/fv_paper/prereg")
THRIFT = VO / "targets" / "thrift"
OUT = VO / "runs" / "prereg" / "T2"
T2_BUDGET = 500.0
UNIT_BUDGET = 0.25
UNIT_WALL = 600
STOP_AT = "2026-10-27T03:00:00Z"
PREPARE_WALL = 7200
PREPARE_UNIT = "__vo_prepare_no_unit__"

# per language: bridge, executable semantics (counterexample step), matching rule, targets (live file names; the run
# uses their frozen copies), and the files each target needs beside it (copied into the frozen copy)
LANGS = {
    "C++": {"bridge": "cirlean", "semantics": True, "match": "cir",
            "targets": ["thrift_cpp_protocol", "thrift_cpp_transport", "thrift_cpp_server", "thrift_cpp_other",
                        "thrift_cpp_compiler"]},
    "C": {"bridge": "cirlean", "semantics": True, "match": "cir", "targets": ["thrift_c_glib"]},
    "Java": {"bridge": "jimple", "semantics": False, "match": "jimple", "targets": ["thrift_java"]},
    # Rust (w-thrift-rsts, 10-25 15:51Z): the T1 key is the units.json name; one library (variant "default"); the
    # adapter has an executable semantics (run_semantic)
    "Rust": {"bridge": "rust", "semantics": True, "match": "name", "targets": ["thrift_rs"]},
    # TS: the T2 frame has no TS unit (all .ts files of the tree are under test directories; thrift.d.ts has no
    # bodies), so no TS target is configured; a TS row in the sample stops the run at start
    "TS": {"bridge": "strictts", "semantics": False, "match": "unconfigured", "targets": []},
}
TARGET_EXTRA = {
    "thrift_cpp_protocol": ["thrift_cpp_protocol.compile_commands.json"],
    "thrift_cpp_transport": ["thrift_cpp_transport.compile_commands.json"],
    "thrift_cpp_server": ["thrift_cpp_server.compile_commands.json"],
    "thrift_cpp_other": ["thrift_cpp_other.compile_commands.json"],
    "thrift_cpp_compiler": ["thrift_cpp_compiler.compile_commands.json"],
    "thrift_c_glib": ["thrift_c_glib.compile_commands.json"],
    "thrift_rs": ["thrift_rs.Cargo.lock", "thrift_rs.aeneas_prune.json"],
}
CONFIG_DIR = "thrift_cpp_config"            # the hand-written thrift/config.h of the C/C++ compile commands
T1_LISTS = "notes/thrift/T1_*_units.tsv"     # the T1 unit lists (their sha256 at start go into pins.json)

OUTCOMES = ["proved_mechanical", "proved_model_stated", "native", "conditional", "partial", "refuted", "blocked",
            "timeout", "infrastructure_error"]


# ------------------------------------------------------------------------------------------------ small helpers
def _out(cmd: list[str], cwd: Path | None = None) -> str:
    try:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=120).stdout.strip()
    except Exception as e:                      # a missing tool is recorded, not fatal
        return f"unavailable: {e}"


def _read(p: Path) -> str:
    try:
        return p.read_text(errors="replace")
    except OSError:
        return ""


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def utc_epoch(iso: str) -> float:
    return calendar.timegm(time.strptime(iso, "%Y-%m-%dT%H:%M:%SZ"))


def mem_available_gb() -> float:
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) / (1024 * 1024)
    return float("inf")


def usage_rows(rd: Path) -> list[dict]:
    p = rd / "llm" / "usage.jsonl"
    if not p.exists():
        return []
    out = []
    for line in p.read_text().splitlines():
        try:
            out.append(json.loads(line))
        except ValueError:
            pass
    return out


def guard_core_s(log: Path) -> float:
    """Core-seconds of the commands logged in a guard log (each command's total at its exit line)."""
    if not log.exists():
        return 0.0
    tot = 0.0
    for line in log.read_text().splitlines():
        m = re.search(r"command exited .*total ([0-9.]+) core-h", line)
        if m:
            tot += float(m.group(1)) * 3600
    return tot


def wilson(k: int, n: int, z: float = 1.959963984540054) -> tuple[float, float]:
    if n == 0:
        return (float("nan"), float("nan"))
    p = k / n
    den = 1 + z * z / n
    c = (p + z * z / (2 * n)) / den
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return (max(0.0, c - h), min(1.0, c + h))


def stats(xs: list[float]) -> dict | None:
    if not xs:
        return None
    q = statistics.quantiles(xs, n=4) if len(xs) >= 2 else [xs[0]] * 3
    return {"n": len(xs), "median": statistics.median(xs), "q1": q[0], "q3": q[2], "mean": statistics.mean(xs),
            "total": sum(xs)}


def closure(name: str, by: dict[str, dict], first: dict | None = None) -> list[str]:
    """The unit and every callee reachable from it (names); `first`: the matched unit itself, whose callees are used
    even when another unit of the library has the same name."""
    seen, todo = [], [name]
    while todo:
        n = todo.pop()
        if n in seen or (n not in by and not (first and n == name)):
            continue
        seen.append(n)
        todo += (first if first is not None and n == name else by[n]).get("callees", [])
    return seen


PRIM = {"Z": "boolean", "B": "byte", "C": "char", "S": "short", "I": "int", "J": "long", "F": "float", "D": "double",
        "V": "void"}


def jtypes(desc: str) -> str:
    ps, i, out = desc[1:desc.index(")")], 0, []
    while i < len(ps):
        dims = 0
        while ps[i] == "[":
            dims += 1
            i += 1
        if ps[i] == "L":
            j = ps.index(";", i)
            ty = ps[i + 1:j].replace("/", ".")
            i = j + 1
        else:
            ty = PRIM[ps[i]]
            i += 1
        out.append(ty + "[]" * dims)
    return ",".join(out)


def jret(desc: str) -> str:
    """The Java return type of a JVM method descriptor."""
    r = desc[desc.index(")") + 1:]
    dims = len(r) - len(r.lstrip("["))
    r = r[dims:]
    ty = r[1:-1].replace("/", ".") if r.startswith("L") else PRIM[r]
    return ty + "[]" * dims


def _split_top(s: str, sep: str) -> list[str]:
    out, depth, cur, i = [], 0, "", 0
    while i < len(s):
        c = s[i]
        if c in "<([{":
            depth += 1
        elif c in ">)]}":
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            out.append(cur)
            cur = ""
            i += len(sep)
            continue
        cur += c
        i += 1
    out.append(cur)
    return out


def cxx_base(d: str) -> str:
    """The unqualified function name of a demangled C++ signature (the T1 inventory's clang AST `name`)."""
    d = re.sub(r"\[abi:[^\]]*\]", "", d).replace("(anonymous namespace)", "{anon}")
    m = re.search(r"(?:^|[\s:~])(operator(?:\(\)|[^(]*))\(", d)
    if m:
        return m.group(1).strip()
    depth, head = 0, d
    for k, ch in enumerate(d):
        if ch in "<{":
            depth += 1
        elif ch in ">}":
            depth -= 1
        elif ch == "(" and depth == 0:
            head = d[:k]
            break
    last = _split_top(_split_top(head, "::")[-1], " ")[-1]
    return (last[:last.index("<")] if "<" in last else last).strip()


def rel_to_repo(p: str) -> str:
    try:
        return str(Path(p).resolve().relative_to(THRIFT.resolve()))
    except (ValueError, OSError):
        return ""


def gap_count(scope: str) -> int:
    if not scope or scope == "in_scope":
        return 0
    parts = scope.split(":", 2)
    return len([x for x in parts[2].split(",") if x]) if len(parts) == 3 else 1


_CIRFUNC_RE = re.compile(r"^\s*cir\.func\b[^@]*@([\w.$]+)\(")


def cir_defined_symbols(cir: Path) -> set[str]:
    """Symbols a ClangIR file defines (with a body), by the rule of veriforch's build.extract_units."""
    out = set()
    if not cir.exists():
        return out
    with open(cir, errors="replace") as f:
        for line in f:
            m = _CIRFUNC_RE.match(line)
            if m and "{" in line and not line.rstrip().endswith(")"):
                out.add(m.group(1))
    return out


def error_class(out: str, rc: int) -> str:
    """A one-line error class for a failed front-end/extraction command."""
    for pat, label in ((r"CIR parse error: (?:line \d+: )?(.*)", "cir2lean CIR parse error: {}"),
                       (r"(generated module \S+ does not check)", "{}"),
                       (r"ClangIR code gen Not Yet Implemented: (.*)", "clang ClangIR NYI: {}"),
                       (r"(clang -fclangir failed)", "{}"),
                       (r"(cir2lean failed)", "{}"),
                       (r"(cir2lean --link failed)", "{}")):
        m = re.findall(pat, out)
        if m:
            return label.format(m[-1].strip())[:300]
    if rc == 124:
        return "front end/extraction killed at its wall"
    m = re.findall(r"(RuntimeError|Error|error)[: ].*", out)
    return (m[-1] if m else (out.strip().splitlines() or [f"exit {rc}"])[-1])[:300]


# ------------------------------------------------------------------------------------------------ the frozen copy
def freeze(dest: Path) -> dict:
    """R10 (as D2's driver did it): veriforch as a frozen copy with a SHA256 manifest. The copy holds the code
    (orch/veriforch, scripts/, VerifOrch/, tools/) and the T2 target files in targets_prereg/ (the driver renames each
    run's copies with --run-prefix), the files they need beside them, the C/C++ compile commands rewritten to the
    copy's config dir; runs/, deps/, targets/, scratch/ and .venv are symlinks to the live tree (outputs stay in the
    live runs/). Every vo call of the run executes the copy (PYTHONPATH and VO_ROOT point at it). An existing copy is
    reused as is after its manifest is re-checked; a crash fix is a new copy. No file mode is changed."""
    man = dest / "SHA256SUMS"
    if not dest.exists():
        dest.mkdir(parents=True)
        ign = shutil.ignore_patterns("__pycache__", "*.pyc", ".lake", "*.new")
        shutil.copytree(VO / "orch" / "veriforch", dest / "orch" / "veriforch", ignore=ign, copy_function=shutil.copy)
        shutil.copytree(VO / "scripts", dest / "scripts", ignore=ign, copy_function=shutil.copy)
        for d in ("VerifOrch", "tools"):
            if (VO / d).exists():
                shutil.copytree(VO / d, dest / d, ignore=ign, copy_function=shutil.copy)
        tp = dest / "targets_prereg"
        tp.mkdir()
        shutil.copytree(VO / "targets" / CONFIG_DIR, tp / CONFIG_DIR, copy_function=shutil.copy)
        live_conf, frozen_conf = str(VO / "targets" / CONFIG_DIR), str(tp / CONFIG_DIR)
        for cfg in LANGS.values():
            for name in cfg["targets"]:
                src = VO / "targets" / f"{name}.toml"
                if not src.exists():
                    continue                    # a language without its target yet: refused at run start
                text = src.read_text()
                for extra in TARGET_EXTRA.get(name, []):
                    s = VO / "targets" / extra
                    if not s.exists():
                        continue
                    data = s.read_text()
                    if extra.endswith(".compile_commands.json"):
                        data = data.replace(live_conf, frozen_conf)
                        text = text.replace(str(s), str(tp / extra))
                    (tp / extra).write_text(data)
                (tp / f"{name}.toml").write_text(text)
        for link in ("runs", "deps", "targets", "scratch", ".venv"):
            (dest / link).symlink_to(VO / link)
        files = sorted(q for q in dest.rglob("*") if q.is_file() and not q.is_symlink()
                       and q.relative_to(dest).parts[0] not in ("runs", "deps", "targets", "scratch", ".venv")
                       and q.name != "SHA256SUMS")
        man.write_text("".join(f"{sha256_file(q)}  {q.relative_to(dest)}\n" for q in files))
    bad = []
    for line in man.read_text().splitlines():
        h, rel = line.split("  ", 1)
        if not (dest / rel).exists() or sha256_file(dest / rel) != h:
            bad.append(rel)
    if bad:
        raise SystemExit(f"frozen copy {dest} differs from its manifest: {bad[:5]}")
    return {"path": str(dest), "SHA256SUMS_sha256": sha256_file(man), "files": len(man.read_text().splitlines())}


def check_sample_manifest(a) -> dict | None:
    """The frozen sample's manifest (T/SHA256SUMS_T2_addendum): its own sha256 must be --manifest-sha, every file it
    lists must match, and the --sample and --addendum files must be among them. Any mismatch stops the run."""
    if not a.manifest:
        return None
    man = Path(a.manifest).resolve()
    got = sha256_file(man)
    if a.manifest_sha and got != a.manifest_sha:
        raise SystemExit(f"manifest {man}: sha256 {got}, expected {a.manifest_sha}")
    listed = {}
    for line in man.read_text().splitlines():
        if line.strip():
            h, rel = line.split(None, 1)
            p = (man.parent / rel.strip().lstrip("*")).resolve()
            if not p.exists() or sha256_file(p) != h:
                raise SystemExit(f"manifest {man}: {rel} does not match its sha256")
            listed[str(p)] = h
    for what, p in (("sample", a.sample), ("addendum", a.addendum)):
        if p and str(Path(p).resolve()) not in listed:
            raise SystemExit(f"the {what} {p} is not in the manifest {man}")
    return {"path": str(man), "sha256": got, "files": len(listed)}


def veriforch_manifest(root: Path) -> tuple[str, int]:
    """SHA256 manifest of the run's veriforch sources (orch/, scripts/)."""
    lines = []
    for sub in ("orch/veriforch", "scripts"):
        for p in sorted((root / sub).rglob("*")):
            if p.is_file() and "__pycache__" not in p.parts and p.suffix in (".py", ".md", ".sh", ".js", ".ts", ""):
                lines.append(f"{sha256_file(p)}  {p.relative_to(root)}")
    text = "\n".join(lines) + "\n"
    return hashlib.sha256(text.encode()).hexdigest(), len(lines)


# ------------------------------------------------------------------------------------------------ pins
def bridge_env(bridge: str, a) -> dict[str, str]:
    if bridge == "cirlean":
        return {"VO_CIRLEAN_DIR": str(VO / "deps" / f"cirlean-{a.cirlean}"), "VO_CIRLEAN_PIN": a.cirlean}
    if bridge == "jimple":
        return {"VO_JIMPLE_DIR": str(VO / "deps" / f"JimpleLean-{a.jimple_snapshot}"),
                "VO_JIMPLE_PIN": f"snapshot-{a.jimple_snapshot}"}
    if bridge == "strictts":
        return {"VO_STRICTTS_DIR": str(VO / "deps" / f"strictts-{a.strictts}"), "VO_STRICTTS_PIN": a.strictts}
    if bridge == "rust":
        env = {"VO_AENEAS_DIR": str(VO / "deps" / a.aeneas), "VO_AENEAS_PIN": a.aeneas}
        for kv in a.rust_env or []:
            k, _, v = kv.partition("=")
            env[k] = v
        return env
    raise ValueError(bridge)


def bridge_pin_given(bridge: str, a) -> bool:
    return bool({"cirlean": a.cirlean, "jimple": a.jimple_snapshot, "strictts": a.strictts,
                 "rust": a.aeneas}[bridge])


def record_pins(a, odir: Path, langs: list[str], root: Path) -> dict:
    pins = {"started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "study": "T2",
            "dry_run": bool(a.dry_run),
            "prereg": {"SHA256SUMS_T_v1": sha256_file(PREREG / "SHA256SUMS_T_v1"),
                       "PREREG_T_v1.md": sha256_file(PREREG / "PREREG_T_v1.md"),
                       "PREREG_D_v2.md": sha256_file(PREREG / "PREREG_D_v2.md"),
                       "DEVIATIONS.md_at_start": sha256_file(PREREG / "DEVIATIONS.md")},
            "sample": a.sample, "sample_sha256": sha256_file(Path(a.sample)),
            "addendum": a.addendum, "addendum_sha256": sha256_file(Path(a.addendum)) if a.addendum else None,
            "t1_lists": {str(p.relative_to(VO)): sha256_file(p) for p in sorted(VO.glob(T1_LISTS))},
            "languages": langs, "bridges": {}, "notes": list(a.pin_note or []),
            "targets": {}, "veriforch_frozen_copy": a.frozen_info,
            "lean": _out([str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"), "--version"])}
    for lang in langs:
        b = LANGS[lang]["bridge"]
        env = bridge_env(b, a)
        bdir = Path(next(iter(env.values())))
        pins["bridges"][b] = {"env": env,
                              "commit": _out(["git", "-C", str(bdir), "log", "-1", "--format=%H %s"])
                              if (bdir / ".git").exists() else None,
                              "snapshot_sha256sums": sha256_file(bdir / "SHA256SUMS")
                              if (bdir / "SHA256SUMS").exists() else None}
        for name in LANGS[lang]["targets"]:
            p = root / "targets_prereg" / f"{name}.toml"
            pins["targets"][name] = {"toml": str(p), "sha256": sha256_file(p) if p.exists() else None}
    if any(LANGS[x]["bridge"] == "cirlean" for x in langs):
        from veriforch.adapters.cir import build as cb          # noqa: E402 (imported with the env set)
        pins["clang"] = {"path": str(cb.CLANG), "version": _out([str(cb.CLANG), "--version"]).splitlines()[:1],
                         "sha256": sha256_file(Path(os.path.realpath(cb.CLANG)))}
    if "Java" in langs:
        from veriforch.adapters.jimple import build as jb      # noqa: E402 (imported with the env set)
        pins["soot_jar_sha256"] = sha256_file(jb.SOOT)
        pins["jdk"] = _out(["bash", "-lc", f"{jb.JDK}/java -version 2>&1"])
    if "Rust" in langs:
        from veriforch.adapters.rust import build as rb        # noqa: E402 (imported with the env set)
        pins["rust"] = {"aeneas_dir": str(rb.AENEAS), "aeneas_pin": rb.AENEAS_PIN,
                        "equivlean_aeneas_dir": str(rb.EQUIVLEAN), "equivlean_aeneas_pin": rb.EQUIVLEAN_PIN,
                        "lean_packages": str(rb.LEAN_PACKAGES), "frontend_version": rb.FRONTEND_VERSION,
                        "bridge_pin": rb.PIN}
    m, n = veriforch_manifest(root)
    pins["veriforch_manifest_sha256"], pins["veriforch_files"] = m, n
    pins["workers"], pins["free_slots"] = a.workers, a.free_slots
    pins["run_prefix"], pins["unit_jobs"], pins["prepare_workers"] = a.run_prefix, a.unit_jobs, a.prepare_workers
    pins["sample_manifest"] = a.sample_manifest
    # files named at launch (adapter fix diffs, front-end files): name -> path and sha256
    pins["pin_files"] = {}
    for kv in a.pin_file or []:
        k, _, p = kv.partition("=")
        pins["pin_files"][k] = {"path": p, "sha256": sha256_file(Path(p)) if Path(p).is_file() else "MISSING"}
    pins["frozen_code_sha256"] = {rel: sha256_file(root / rel) for rel in (
        "orch/veriforch/adapters/cir/build.py", "orch/veriforch/adapters/jimple/build.py",
        "orch/veriforch/adapters/jimple/adapter.py", "orch/veriforch/adapters/rust/build.py",
        "orch/veriforch/scheduler.py", "orch/veriforch/cex.py", "orch/veriforch/cli.py", "scripts/prereg_t2.py")
        if (root / rel).exists()}
    pins["run_dirs"] = sorted(str(VO / "runs" / f"{a.run_prefix}_{n}") + "[_w<k>]"
                              for x in langs for n in LANGS[x]["targets"])
    pins["load_max"], pins["mem_min_gb"], pins["stop_at"] = a.load_max, a.mem_min_gb, a.stop_at
    out = odir / "pins.json"
    if out.exists() and a.resume:
        out = odir / f"pins_resume_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}.json"
    out.write_text(json.dumps(pins, indent=1))
    return pins


# ------------------------------------------------------------------------------------------------ ledger
def ledger_update(delta_usd: float, delta_core_h: float, price: float, lang: str, dry: bool) -> dict:
    p = OUT / "ledger.json"
    OUT.mkdir(parents=True, exist_ok=True)
    with open(OUT / "ledger.lock", "a") as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        d = json.loads(p.read_text()) if p.exists() else {"model_usd": 0.0, "core_h": 0.0, "compute_usd": 0.0,
                                                          "units": {}, "price_core_h": price}
        if not dry:
            d["model_usd"] += delta_usd
            d["core_h"] += delta_core_h
            d["compute_usd"] += delta_core_h * price
            d["units"][lang] = d["units"].get(lang, 0) + 1
            p.write_text(json.dumps(d, indent=1))
        fcntl.flock(lk, fcntl.LOCK_UN)
    return d


def ledger_total() -> float:
    p = OUT / "ledger.json"
    return json.loads(p.read_text())["model_usd"] if p.exists() else 0.0     # T2's cap is model spend only


# ------------------------------------------------------------------------------------------------ outcome (R6)
def map_outcome(info: dict) -> tuple[str, str]:
    """(outcome, detail) from one unit's records: PREREG_D_v2's table with D's readings (DEVIATIONS.md)."""
    if info.get("library_error"):
        return "blocked", "front end/extraction: " + info["library_error"]
    if info.get("unit") is None:
        return "blocked", info.get("unmatched") or "not emitted by the front end"
    if info.get("scope", "in_scope") != "in_scope":
        return "blocked", info["scope"]
    if info.get("crash"):
        return "infrastructure_error", "tool crash: " + info["crash"]
    f = info.get("finding") or {}
    if f.get("verdict") in ("real_bug", "missing_precondition") and f.get("counterexample"):
        return "refuted", f["verdict"]
    if info.get("killed"):
        return "timeout", f"killed at the {UNIT_WALL // 60}-minute wall"
    o = info.get("outcome") or {}
    st = o.get("status")
    if st == "proved":
        if o.get("trust") == "native":
            return "native", "native_decide"
        if info.get("replay") != "PASS":
            cause = info.get("replay_cause") or "not_run"
            label = {"deep_recursion": "(kernel) deep recursion", "kernel_rejection": "kernel rejection",
                     "not_run": "replay could not run"}[cause]
            return "infrastructure_error", f"replay failed: {label}: {info.get('replay_message', '')}"[:400]
        return ("proved_mechanical" if o.get("statement_origin") == "mechanical" else "proved_model_stated"), \
            o.get("statement_origin") or "llm"
    if st == "conditional":
        return "conditional", ", ".join(o.get("assumes", [])) or o.get("detail", "")
    if st == "partial":
        return "partial", o.get("detail", "")[:200]
    if st == "gap":
        return "blocked", info.get("scope") or o.get("detail", "")
    if st in ("stuck", "budget"):
        if st == "stuck" and str(o.get("detail", "")).startswith("LLM:") and not o.get("history") \
                and not (o.get("result") or {}).get("messages"):
            return "infrastructure_error", o["detail"][:200]
        return "timeout", f"{st}: " + str(o.get("detail", ""))[:200]
    if st == "blocked":
        return "timeout", str(o.get("detail", ""))[:200]
    if st == "error":
        return "infrastructure_error", str(o.get("detail", ""))[:200]
    return "infrastructure_error", f"no outcome record (status {st!r})"


def verify_status(out: str, variant: str, name: str) -> str | None:
    """The unit's status in `vo verify`'s closing JSON summary ({variant: {unit: status}})."""
    i = out.rfind("\n{")
    while i >= 0:
        try:
            d = json.loads(out[i + 1:out.index("\n}", i) + 2])
            return (d.get(variant) or {}).get(name) if isinstance(d, dict) else None
        except (ValueError, AttributeError):
            i = out.rfind("\n{", 0, i)
    return None


# ------------------------------------------------------------------------------------------------ the run
class Driver:
    def __init__(self, a):
        self.a = a
        a.sample_manifest = check_sample_manifest(a)       # before anything else: the frozen sample is what it was
        self.root = Path(a.frozen).resolve() if a.frozen else VO
        a.frozen_info = freeze(self.root) if a.frozen else None
        self.tdir = self.root / "targets_prereg" if a.frozen else None
        rows = list(csv.DictReader(open(a.sample), delimiter="\t"))
        self.all_rows = rows
        want = set(a.languages.split(",")) if a.languages else None
        if want:
            rows = [r for r in rows if r["language"] in want]
        if a.first:
            rows = rows[:a.first]
        self.rows = rows
        self.langs = sorted({r["language"] for r in rows})
        for lang in self.langs:
            if lang not in LANGS:
                raise SystemExit(f"sample language {lang!r} has no configuration")
            if LANGS[lang]["match"] == "unconfigured":
                raise SystemExit(f"{lang}: target and matching rule not configured yet (see LANGS)")
            if not bridge_pin_given(LANGS[lang]["bridge"], a):
                raise SystemExit(f"T2 pins are explicit: give the {LANGS[lang]['bridge']} pin for {lang}")
        OUT.mkdir(parents=True, exist_ok=True)
        (OUT / "units").mkdir(exist_ok=True)
        self.env = dict(os.environ, VO_ROOT=str(self.root), PYTHONPATH=str(self.root / "orch"), OMP_NUM_THREADS="1",
                        OPENBLAS_NUM_THREADS="1", MKL_NUM_THREADS="1", RAYON_NUM_THREADS="1",
                        TMPDIR=str(VO / "scratch" / "tmp"))
        for lang in self.langs:
            os.environ.update(bridge_env(LANGS[lang]["bridge"], a))
        self.vo = ["nice", "-n", "10", str(VO / ".venv" / "bin" / "python"), "-B", "-m", "veriforch"]
        self.replay_sh = str(self.root / "scripts" / "kernel_replay.sh")
        sys.path.insert(0, str(self.root / "orch"))
        from veriforch.config import load_target
        self.load_target = load_target
        # unit records and findings are named by veriforch's own rule (long names hashed, scheduler._unit_file)
        from veriforch import scheduler as _sch
        self.unit_file = getattr(_sch, "_unit_file", None) or (lambda d, n: d / f"{n}.json")
        self.targets: dict[str, dict] = {}       # live name -> {lang, tpath, t, rd}
        for lang in self.langs:
            for name in LANGS[lang]["targets"]:
                src = (self.tdir / f"{name}.toml") if self.tdir else VO / "targets" / f"{name}.toml"
                if not src.exists():
                    raise SystemExit(f"{lang}: target file {src} is missing")
                text = src.read_text()
                # every run directory of this run: runs/<run prefix>_<name> (a copy frozen before this rule named its
                # files t2_<name>; that prefix is dropped first)
                text = re.sub(r'^name = "(?:t2_)?([^"]+)"', rf'name = "{a.run_prefix}_\1"', text, count=1, flags=re.M)
                tp = OUT / "targets" / f"{name}.toml"
                tp.parent.mkdir(parents=True, exist_ok=True)
                text = self._with_target_dir(text, src.parent)
                if not tp.exists() or tp.read_text() != text:
                    tp.write_text(text)
                t = load_target(tp)
                self.targets[name] = {"lang": lang, "tpath": tp, "t": t, "rd": VO / "runs" / t.name,
                                      "root": Path(t.root).resolve(), "src": src}
        self.slots: dict[tuple[str, int], dict] = {}
        self.slot_lock = threading.Lock()

    @staticmethod
    def _with_target_dir(text: str, d: Path) -> str:
        """Relative paths in a target file resolve against the frozen target directory (load_target keeps an
        explicit _target_dir), so that the run's copies of the target file may live elsewhere."""
        if re.search(r"^_target_dir = ", text, re.M):
            return text
        return re.sub(r'^(name = "[^"]+")$', lambda m: f'{m.group(1)}\n_target_dir = "{d}"', text, count=1,
                      flags=re.M)

    def log(self, msg: str) -> None:
        line = f"{time.strftime('%H:%M:%SZ', time.gmtime())} {msg}"
        print(line, flush=True)
        with open(OUT / "driver.log", "a") as f:
            f.write(line + "\n")

    def run_cmd(self, cmd: list[str], guard: Path, timeout: int, lang: str) -> tuple[int, str, float]:
        env = dict(self.env, VO_GUARD_LOG=str(guard), **bridge_env(LANGS[lang]["bridge"], self.a))
        t0 = time.time()
        try:
            p = subprocess.run(cmd, cwd=VO, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                               timeout=timeout + 300)
            return p.returncode, p.stdout, time.time() - t0
        except subprocess.TimeoutExpired as e:
            out = e.stdout.decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
            return 124, out, time.time() - t0

    # ---------------------------------------------------------------- worker slots
    def slot(self, tname: str, k: int) -> dict:
        """Worker k's target file and vo run directory for one target: worker 0 is the target's own; worker k > 0 has
        runs/<name>_w<k> (a copy of the target file under that name) whose cache/ links to the target's cache/."""
        with self.slot_lock:
            key = (tname, k)
            if key in self.slots:
                return self.slots[key]
            tg = self.targets[tname]
            t = tg["t"]
            if k == 0:
                s = {"k": 0, "tpath": tg["tpath"], "rd": tg["rd"], "name": t.name}
            else:
                name = f"{t.name}_w{k}"
                text = re.sub(r'^name = "([^"]+)"', f'name = "{name}"', tg["tpath"].read_text(), count=1, flags=re.M)
                tp = OUT / "targets" / f"{tname}_w{k}.toml"
                if not tp.exists() or tp.read_text() != text:
                    tp.write_text(text)
                rd = VO / "runs" / name
                rd.mkdir(parents=True, exist_ok=True)
                main_cache = tg["rd"] / "cache"
                main_cache.mkdir(parents=True, exist_ok=True)
                cache = rd / "cache"
                if not cache.exists() and not cache.is_symlink():
                    cache.symlink_to(main_cache)
                elif not (cache.is_symlink() and cache.resolve() == main_cache.resolve()):
                    raise SystemExit(f"{cache} exists and is not the link to {main_cache}")
                s = {"k": k, "tpath": tp, "rd": rd, "name": name}
            self.slots[key] = s
            return s

    def vdir(self, s: dict, tname: str, variant: str) -> Path:
        return s["rd"] / self.targets[tname]["t"].version / variant

    # ---------------------------------------------------------------- resource guard
    def wait_resources(self, running: int, what: str, last: list[float]) -> str | None:
        """The RAM guard always applies (no new dispatch while MemAvailable < --mem-min-gb, main 16:38Z); the load
        guard applies once --free-slots units are in flight."""
        load, mem = os.getloadavg()[0], mem_available_gb()
        if mem < self.a.mem_min_gb:
            return f"resource guard: MemAvailable {mem:.0f} GB below {self.a.mem_min_gb:.0f} GB"
        if running >= self.a.free_slots and load > self.a.load_max:
            return (f"resource guard: {running} in flight >= {self.a.free_slots} free slots and 1-min load {load:.0f} "
                    f"> {self.a.load_max:.0f}")
        return None

    # ---------------------------------------------------------------- step 1: front end and extraction
    def libraries(self) -> list[tuple[str, str]]:
        """(target, variant) of every library of the run's languages; C/C++: every TU."""
        libs = []
        for tname, tg in self.targets.items():
            for v in tg["t"].variants:
                libs.append((tname, v.name))
        return libs

    def needed_libraries(self) -> list[tuple[str, str]]:
        """Dry runs: only the C/C++ TUs that may hold the selected units (T1's `tus`), all other libraries."""
        t1 = json.loads((VO / "notes/thrift/T1_cxx.json").read_text())
        by_key = {u["unit"]: u for u in t1["units"]}
        want: set[tuple[str, str]] = set()
        for r in self.rows:
            if LANGS[r["language"]]["match"] != "cir":
                continue
            u = by_key.get(r["unit"])
            for v in (u or {}).get("tus", []):
                for tname, tg in self.targets.items():
                    if any(x.name == v for x in tg["t"].variants):
                        want.add((tname, v))
        out = []
        for tname, v in self.libraries():
            if LANGS[self.targets[tname]["lang"]]["match"] != "cir" or (tname, v) in want:
                out.append((tname, v))
        return out

    def prepare_one(self, tname: str, variant: str, k: int, jobs: int) -> dict:
        tg = self.targets[tname]
        s = self.slot(tname, k)
        d = OUT / "prepare" / tname
        d.mkdir(parents=True, exist_ok=True)
        guard = d / f"{variant}.guard.log"
        n0 = len(usage_rows(s["rd"]))
        cmd = ["timeout", str(PREPARE_WALL), *self.vo, "verify", str(s["tpath"])]
        if len(tg["t"].variants) > 1:
            cmd += ["--variant", variant]
        cmd += ["--only", PREPARE_UNIT, "--no-llm", "--check-timeout", "600", "--jobs", str(jobs)]
        rc, out, wall = self.run_cmd(cmd, guard, PREPARE_WALL, tg["lang"])
        (d / f"{variant}.log").write_text(" ".join(cmd) + "\n" + out)
        units_p = self.vdir(s, tname, variant) / "units.json"
        res = {"target": tname, "variant": variant, "rc": rc, "wall_s": round(wall, 1),
               "core_s": round(guard_core_s(guard), 1),
               "model_usd": round(sum(r.get("dollars", 0) for r in usage_rows(s["rd"])[n0:]), 4),
               "slot": s["name"], "units_json": str(units_p) if units_p.exists() and rc == 0 else None,
               "unit_cir": str(self.vdir(s, tname, variant) / "unit.cir"),
               "error": None if rc == 0 else error_class(out, rc),
               "finished": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        (d / f"{variant}.json").write_text(json.dumps(res, indent=1))
        return res

    def prepare(self) -> dict:
        libs = self.needed_libraries() if self.a.prepare_scope == "needed" else self.libraries()
        res: dict[tuple[str, str], dict] = {}
        todo = []
        for tname, v in libs:
            p = OUT / "prepare" / tname / f"{v}.json"
            if p.exists():                          # front end and extraction once per library
                res[(tname, v)] = json.loads(p.read_text())
            else:
                todo.append((tname, v))
        self.log(f"front end + extraction: {len(libs)} libraries, {len(todo)} to prepare "
                 f"({self.a.prepare_workers} at a time)")
        cond = threading.Condition()
        free = list(range(max(1, self.a.prepare_workers)))
        threads = []

        def work(tname, v, k, jobs):
            try:
                r = self.prepare_one(tname, v, k, jobs)
            except Exception as e:
                r = {"target": tname, "variant": v, "rc": -1, "error": f"driver error: {type(e).__name__}: {e}"[:300],
                     "units_json": None, "wall_s": 0.0, "core_s": 0.0, "model_usd": 0.0}
            with cond:
                res[(tname, v)] = r
                free.append(k)
                cond.notify_all()
            self.log(f"prepared {tname}/{v}: rc {r['rc']} {r.get('wall_s', 0)} s"
                     + (f", error {r['error']}" if r.get("error") else ""))

        # a library with many generated modules (Java, Rust: one module per method/function) runs alone, its modules
        # compiled --prepare-workers at a time; then the C/C++ TUs (one generated module each), --prepare-workers at
        # a time. Either way at most --prepare-workers Lean checks run at once.
        big = [(tn, v) for tn, v in todo if LANGS[self.targets[tn]["lang"]]["match"] != "cir"]
        for tname, v in big:
            self.log(f"preparing {tname}/{v} alone, {self.a.prepare_workers} modules at a time")
            work(tname, v, 0, max(1, self.a.prepare_workers))
        todo = [x for x in todo if x not in big]
        last = [0.0]
        for tname, v in todo:
            with cond:
                while True:
                    reason = None
                    if not free:
                        reason = "busy"
                    else:
                        reason = self.wait_resources(self.a.prepare_workers - len(free), "prepare", last)
                    if reason is None:
                        break
                    if reason != "busy" and time.time() - last[0] > 300:
                        self.log(f"wait before preparing {tname}/{v}: {reason}")
                        last[0] = time.time()
                    cond.wait(timeout=self.a.poll)
                k = free.pop(0)
            th = threading.Thread(target=work, args=(tname, v, k, 1))
            th.start()
            threads.append(th)
        for th in threads:
            th.join()
        summ = {"libraries": len(libs), "failed": sum(1 for r in res.values() if r["rc"] != 0),
                "core_s": round(sum(r.get("core_s", 0) for r in res.values()), 1),
                "model_usd": round(sum(r.get("model_usd", 0) for r in res.values()), 4),
                "by_target": {}}
        for (tname, v), r in res.items():
            b = summ["by_target"].setdefault(tname, {"libraries": 0, "failed": 0, "core_s": 0.0, "errors": {}})
            b["libraries"] += 1
            b["core_s"] = round(b["core_s"] + r.get("core_s", 0), 1)
            if r["rc"] != 0:
                b["failed"] += 1
                b["errors"][r["error"]] = b["errors"].get(r["error"], 0) + 1
        (OUT / "prepare.json").write_text(json.dumps(summ, indent=1))
        self.prepared = res
        return summ

    # ---------------------------------------------------------------- matching
    def build_index(self) -> None:
        """Units of every prepared library, indexed by name (C/C++: the symbol)."""
        self.index: dict[str, list[dict]] = {}      # name -> [{target, variant, unit}]
        self.lib_units: dict[tuple[str, str], dict[str, dict]] = {}
        self.failed_syms: dict[tuple[str, str], set[str]] = {}
        order = {tn: i for i, tn in enumerate(self.targets)}
        for (tname, v), r in sorted(self.prepared.items(),
                                    key=lambda kv: (order[kv[0][0]],
                                                    [x.name for x in self.targets[kv[0][0]]["t"].variants].index(kv[0][1]))):
            if r["rc"] == 0 and r.get("units_json"):
                units = json.loads(Path(r["units_json"]).read_text())
                self.lib_units[(tname, v)] = {u["name"]: u for u in units}
                for u in units:
                    self.index.setdefault(u["name"], []).append({"target": tname, "variant": v, "unit": u})
            elif LANGS[self.targets[tname]["lang"]]["match"] == "cir":
                self.failed_syms[(tname, v)] = cir_defined_symbols(Path(r.get("unit_cir") or "/nonexistent"))

    def match(self, row: dict) -> dict:
        """-> {target, variant, unit} or {unmatched: reason} or {library_error: error, target, variant}."""
        lang = row["language"]
        rule = LANGS[lang]["match"]
        if rule == "cir":
            return self._match_cir(row)
        if rule == "jimple":
            # `Class#method(descriptor)` -> the unit `Class.method(<parameter types>)`; when a real method and its bridge
            # share that name, the unit whose signature has the descriptor's return type (the frame excludes bridges)
            key = row["unit"]
            cls, _, rest = key.partition("#")
            meth, desc = rest[:rest.index("(")], rest[rest.index("("):]
            want = f"{cls}.{meth}({jtypes(desc)})"
            cands = [c for c in self.index.get(want, []) if self.targets[c["target"]]["lang"] == lang]
            if cands:
                ret = jret(desc)
                exact = [c for c in cands if (c["unit"].get("signature") or {}).get("ret") == ret]
                best = dict((exact or cands)[0])
                if len(cands) > 1:
                    # veriforch keys units by name (the last one wins): `vo verify --only <name>` may take the other
                    best["name_shared"] = len(cands)
                return best
            fails = [(tn, v) for (tn, v), r in self.prepared.items() if r["rc"] != 0 and self.targets[tn]["lang"] == lang]
            if fails:
                tn, v = fails[0]
                return {"library_error": self.prepared[(tn, v)]["error"], "target": tn, "variant": v}
            return {"unmatched": "not emitted by the front end"}
        if rule == "name":
            cands = [c for c in self.index.get(row["unit"], []) if self.targets[c["target"]]["lang"] == lang]
            if cands:
                return cands[0]
            fails = [(tn, v) for (tn, v), r in self.prepared.items() if r["rc"] != 0 and self.targets[tn]["lang"] == lang]
            if fails:
                tn, v = fails[0]
                return {"library_error": self.prepared[(tn, v)]["error"], "target": tn, "variant": v}
            return {"unmatched": "not emitted by the front end"}
        raise SystemExit(f"{lang}: no matching rule")

    def _match_cir(self, row: dict) -> dict:
        lang, key, path = row["language"], row["unit"], row["path"]
        apath = (THRIFT / path).resolve()
        tnames = [tn for tn in LANGS[lang]["targets"] if str(apath).startswith(str(self.targets[tn]["root"]) + os.sep)]
        line = None
        sym = key
        internal = False
        if "@" in key:
            head, tail = key.rsplit("@", 1)
            if tail == path:
                sym, internal = head, True
            elif tail.startswith(path + ":") and tail[len(path) + 1:].isdigit():
                sym, line = None, int(tail[len(path) + 1:])
                qual = head.replace("%20", " ").replace("%09", "\t").replace("%25", "%")
                base = qual.split("::")[-1]
        cands = []
        if sym is not None:
            for c in self.index.get(sym, []):
                if c["target"] not in tnames:
                    continue
                if internal and rel_to_repo((c["unit"].get("loc") or "").rpartition(":")[0]) != path:
                    continue
                cands.append(c)
        else:
            for (tn, v), units in self.lib_units.items():
                if tn not in tnames:
                    continue
                for u in units.values():
                    f, _, ln = (u.get("loc") or "").rpartition(":")
                    if rel_to_repo(f) != path or not ln.isdigit() or int(ln) != line:
                        continue
                    dem = (u.get("signature") or {}).get("demangled") or ""
                    if (u["name"] if lang == "C" else cxx_base(dem or u["name"])) == base:
                        cands.append({"target": tn, "variant": v, "unit": u})
        if cands:
            order = {tn: i for i, tn in enumerate(tnames)}
            return min(cands, key=lambda c: (c["unit"].get("scope") != "in_scope", gap_count(c["unit"].get("scope", "")),
                                             order[c["target"]],
                                             [x.name for x in self.targets[c["target"]]["t"].variants].index(c["variant"])))
        if sym is not None:
            for (tn, v), syms in self.failed_syms.items():
                if tn in tnames and sym in syms:
                    return {"library_error": self.prepared[(tn, v)]["error"], "target": tn, "variant": v}
        return {"unmatched": "not emitted by the front end"}

    # ---------------------------------------------------------------- step 2: one unit
    def unit_record(self, vdir: Path, name: str) -> dict | None:
        p = self.unit_file(vdir / "units", name)
        return json.loads(p.read_text()) if p.exists() else None

    def module_package(self, module: str, rd: Path) -> Path | None:
        rel = Path(".lake/build/lib/lean") / (module.replace(".", "/") + ".olean")
        cands = [p for p in rd.glob("lean*/" + str(rel))] + [p for p in rd.glob("lean*/*/" + str(rel))]
        if not cands:
            return None
        best = max(cands, key=lambda p: p.stat().st_mtime)
        return Path(str(best).split("/.lake/build/lib/lean/")[0])

    def replay(self, names: list[str], vdir: Path, rd: Path, guard: Path, lang: str):
        mods = []
        for n in names:
            r = self.unit_record(vdir, n)
            if r and r.get("status") == "proved" and (r.get("obligation") or {}).get("module"):
                mods.append((n, r["obligation"]["module"]))
        if not mods:
            return None, None, "", []
        lines, verdict, cause, msg = [], None, None, ""
        for n, mod in mods:
            pkg = self.module_package(mod, rd)
            if pkg is None:
                line, c = f"FAIL {mod}: module not found in the run's packages", "not_run"
            else:
                rc, out, _ = self.run_cmd([self.replay_sh, "--log-dir", str(OUT / "replay"), str(pkg), mod],
                                          guard, 3600, lang)
                line = next((l for l in out.splitlines() if l.startswith(("PASS", "FAIL"))), out.strip()[-300:])
                full = out + "\n" + _read(OUT / "replay" / f"{mod}.log")
                c = None if line.startswith("PASS") else ("deep_recursion" if "deep recursion" in full
                                                          else "kernel_rejection")
            lines.append(f"{n}: {line}")
            if n == names[0]:
                verdict = "PASS" if c is None else "FAIL"
                cause, msg = c, line[:400]
        return verdict, cause, msg, lines

    def run_unit(self, row: dict, m: dict, k: int) -> dict:
        order, key, lang = row["order"], row["unit"], row["language"]
        rec = {"order": order, "language": lang, "component": row["component"], "key": key, "path": row["path"],
               "unit": None, "target": m.get("target"), "variant": m.get("variant"), "model_usd": 0.0,
               "core_s": 0.0, "wall_s": 0.0, "model_proposals": 0, "attempts_record": None, "statement_origin": "",
               "trust": "", "replay": "", "closure": [], "scope": None}
        info = {"order": order, "unit": None, "library_error": m.get("library_error"), "unmatched": m.get("unmatched")}
        if m.get("library_error") or m.get("unmatched"):
            out, detail = map_outcome(info)
            rec.update(outcome=out, detail=detail)
            return rec
        u, tname, variant = m["unit"], m["target"], m["variant"]
        tg = self.targets[tname]
        by = self.lib_units[(tname, variant)]
        names = closure(u["name"], by, first=u)
        info.update(unit=u["name"], scope=u.get("scope", "in_scope"))
        rec.update(unit=u["name"], scope=info["scope"], closure=names)
        if m.get("name_shared"):
            rec["name_shared"] = m["name_shared"]
        s = self.slot(tname, k)
        vdir = self.vdir(s, tname, variant)
        guard = OUT / "units" / f"{int(order):04d}.guard.log"
        ulog = OUT / "units" / f"{int(order):04d}.log"
        n0 = len(usage_rows(s["rd"]))
        vflag = ["--variant", variant] if len(tg["t"].variants) > 1 else []
        cmd = ["timeout", str(UNIT_WALL), *self.vo, "verify", str(s["tpath"]), *vflag]
        for n in names:
            cmd += ["--only", n]
        cmd += ["--attempts", "3", "--check-timeout", "600", "--budget", f"{UNIT_BUDGET:.2f}"]
        if self.a.unit_jobs:
            cmd += ["--jobs", str(self.a.unit_jobs)]      # vo's default (no flag, as in D2): 2 components at once
        if self.a.dry_run:
            cmd.append("--no-llm")
        t_start = time.time()
        rc, out, wall = self.run_cmd(cmd, guard, UNIT_WALL, lang)
        ulog.write_text(" ".join(cmd) + "\n" + out)
        info["killed"] = rc == 124
        if rc not in (0, 124):
            info["crash"] = (out.strip().splitlines() or [f"exit {rc}"])[-1][:300]
        o = self.unit_record(vdir, u["name"])
        if o is not None and self.unit_file(vdir / "units", u["name"]).stat().st_mtime < t_start - 1:
            o = None                             # a record of an earlier run of this slot, not of this command
        st = verify_status(out, variant, u["name"])
        if o is None and st is not None:
            # D's reading: a negative-cache result writes no unit record; the run's own JSON summary has the status
            neg = re.search(rf"{re.escape(u['name'])}: stuck \(negative cache, (\d+) earlier attempts\)", out)
            o = {"status": st, "detail": ("reused failed outcome (negative cache, %s earlier attempts)" % neg.group(1))
                 if neg else "status from the verify summary (no unit record written)"}
            rec["status_source"] = "verify_summary"
        info["outcome"] = o
        spent = sum(r.get("dollars", 0) for r in usage_rows(s["rd"])[n0:])
        if o and o.get("status") in ("stuck", "budget") and LANGS[lang]["semantics"] and not info["killed"] \
                and info["scope"] == "in_scope":
            left_wall = UNIT_WALL - wall
            left_usd = 0.0 if self.a.dry_run else max(0.0, UNIT_BUDGET - spent)
            if left_wall > 60:
                c = ["timeout", str(int(left_wall)), *self.vo, "cex", str(s["tpath"]), *vflag, "--only", u["name"],
                     "--budget", f"{left_usd:.4f}"]
                t_cex = time.time()
                rc2, out2, w2 = self.run_cmd(c, guard, int(left_wall), lang)
                with open(ulog, "a") as f:
                    f.write("\n" + " ".join(c) + "\n" + out2)
                wall += w2
                if rc2 == 124:
                    info["killed"] = True
                elif rc2 != 0:
                    info["crash"] = "vo cex: " + ((out2.strip().splitlines() or [f"exit {rc2}"])[-1])[:280]
                fp = self.unit_file(vdir / "findings", u["name"])
                info["finding"] = json.loads(fp.read_text()) if fp.exists() and fp.stat().st_mtime >= t_cex - 1 \
                    else None
                rec["cex"] = {"rc": rc2, "wall_s": round(w2, 1), "budget": round(left_usd, 4),
                              "verdict": (info["finding"] or {}).get("verdict")}
        rows_u = usage_rows(s["rd"])[n0:]
        rec["model_usd"] = round(sum(r.get("dollars", 0) for r in rows_u), 4)
        rec["model_proposals"] = sum(1 for r in rows_u if str(r.get("task", "")).startswith(f"{variant}:{u['name']}:"))
        rguard = OUT / "units" / f"{int(order):04d}.replay.guard.log"
        verdict, cause, rmsg, lines = self.replay(names, vdir, s["rd"], rguard, lang)
        info["replay"], info["replay_cause"], info["replay_message"] = verdict, cause, rmsg
        rec.update(replay=verdict or "", replay_cause=cause or "", replay_message=rmsg, replay_lines=lines,
                   core_s=round(guard_core_s(guard), 1), replay_core_s=round(guard_core_s(rguard), 1),
                   wall_s=round(wall, 1), killed=bool(info.get("killed")), crash=info.get("crash"))
        if o:
            rec["attempts_record"] = o.get("attempts")
            rec["statement_origin"] = o.get("statement_origin", "")
            rec["trust"] = o.get("trust", "")
            rec["status"] = o.get("status")
        out_, detail = map_outcome(info)
        rec.update(outcome=out_, detail=detail)
        return rec

    # ---------------------------------------------------------------- dispatch
    def _finish(self, row, rec, k, t0, done, res_p):
        ledger_update(rec["model_usd"], (rec["core_s"] + rec.get("replay_core_s", 0)) / 3600, self.a.price_core_h,
                      row["language"], self.a.dry_run)
        rec["worker"] = k
        rec["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        with self.cond:
            done[row["order"]] = rec
            with open(res_p, "a") as f:
                f.write(json.dumps(rec) + "\n")
            self.running.pop(row["order"], None)
            self.free.append(k)
            self.cond.notify_all()
        self.log(f"unit {row['order']} [{row['language']} {row['component']}] {row['unit'][:60]}: {rec['outcome']} "
                 f"({rec['detail'][:80]}) ${rec['model_usd']:.2f} {rec['core_s']:.0f} core-s "
                 f"{time.time() - t0:.0f} s (worker {k})")

    def _work(self, row, m, k, done, res_p):
        t0 = time.time()
        try:
            rec = self.run_unit(row, m, k)
        except Exception as e:                  # a driver error must not leave the unit in flight forever
            rec = {"order": row["order"], "language": row["language"], "component": row["component"],
                   "key": row["unit"], "path": row["path"], "unit": None, "outcome": "infrastructure_error",
                   "detail": f"driver error: {type(e).__name__}: {e}"[:300], "model_usd": 0.0, "core_s": 0.0,
                   "wall_s": round(time.time() - t0, 1), "model_proposals": 0, "attempts_record": None}
        self._finish(row, rec, k, t0, done, res_p)

    def dispatch(self, rows, done, res_p):
        n = max(1, self.a.workers)
        self.cond = threading.Condition()
        self.running: dict[str, set] = {}
        self.free = list(range(n))
        threads = []
        stopped = None
        stop_epoch = utc_epoch(self.a.stop_at)
        for row in rows:
            if row["order"] in done:
                continue
            m = self.match(row)
            cl = {(m["target"], x) for x in closure(m["unit"]["name"], self.lib_units[(m["target"], m["variant"])],
                                                    first=m["unit"])} if m.get("unit") else set()
            logged: set = set()
            t_wait = None
            last_res = 0.0
            with self.cond:
                while True:
                    if not self.a.dry_run and ledger_total() + UNIT_BUDGET * len(self.running) >= T2_BUDGET:
                        stopped = {"at": row["order"], "rule": f"model ${ledger_total():.2f} + ${UNIT_BUDGET:.2f} x "
                                                               f"{len(self.running)} in flight >= ${T2_BUDGET:.0f}"}
                        break
                    if time.time() >= stop_epoch:
                        stopped = {"at": row["order"], "rule": f"clock reached {self.a.stop_at}"}
                        break
                    reason, key = None, None
                    if not self.free:
                        reason, key = f"all {n} workers busy (units {sorted(self.running, key=int)})", "busy"
                    else:
                        clash = sorted((o for o, c in self.running.items() if c & cl), key=int)
                        if clash:
                            shared = sorted(x for _, x in (set().union(*(self.running[o] for o in clash)) & cl))
                            reason, key = f"closure overlaps running unit(s) {clash} on {shared[:4]}", ("clash", tuple(clash))
                        elif n > 1 and m.get("unit"):
                            r = self.wait_resources(len(self.running), "unit", [last_res])
                            if r:
                                reason, key = r, "resources"
                    if reason is None:
                        break
                    t_wait = t_wait or time.time()
                    if key not in logged or (key == "resources" and time.time() - last_res > 300):
                        self.log(f"wait before unit {row['order']}: {reason}")
                        logged.add(key)
                        last_res = time.time() if key == "resources" else last_res
                    self.cond.wait(timeout=self.a.poll)
                if stopped is not None:
                    self.log(f"stop rule ({stopped['rule']}): no dispatch from unit {row['order']} on")
                    break
                k = self.free.pop(0)
                self.running[row["order"]] = cl
            if t_wait:
                self.log(f"dispatch unit {row['order']} to worker {k} after {time.time() - t_wait:.0f} s of waiting")
            elif n > 1:
                self.log(f"dispatch unit {row['order']} to worker {k} (closure {len(cl)} units)")
            if n == 1:
                self._work(row, m, k, done, res_p)
            else:
                th = threading.Thread(target=self._work, args=(row, m, k, done, res_p))
                th.start()
                threads.append(th)
        for th in threads:
            th.join()
        return stopped

    # ---------------------------------------------------------------- run + analysis
    def run(self) -> None:
        self.log(f"start T2 ({'dry run' if self.a.dry_run else 'RUN'}): {len(self.rows)} units of {self.a.sample}, "
                 f"languages {self.langs}, frozen copy {self.root}")
        if not self.a.dry_run and not self.a.resume:
            for tg in self.targets.values():
                if tg["rd"].exists() and any(tg["rd"].glob("*/*/units/*.json")):
                    raise SystemExit(f"{tg['rd']} holds unit records from an earlier run: the real run starts from "
                                     "empty run directories (or use --resume)")
        record_pins(self.a, OUT, self.langs, self.root)
        prep = self.prepare()
        self.log(f"front end + extraction: {prep['libraries']} libraries, {prep['failed']} failed, "
                 f"{prep['core_s']} core-s")
        if self.a.prepare_only:
            return
        self.build_index()
        done = {}
        res_p = OUT / "results.jsonl"
        if self.a.resume and res_p.exists():
            for line in res_p.read_text().splitlines():
                r = json.loads(line)
                done[r["order"]] = r
        stopped = self.dispatch(self.rows, done, res_p)
        self.write_outcomes(self.rows, done, stopped, prep)

    def write_outcomes(self, rows, done, stopped, prep) -> None:
        cols = ["order", "language", "component", "key", "path", "target", "variant", "unit", "outcome", "detail",
                "statement_origin", "trust", "replay", "replay_cause", "model_usd", "core_s", "replay_core_s", "wall_s",
                "model_proposals", "attempts_record", "status_source"]
        with open(OUT / "outcomes.tsv", "w") as f:
            f.write("\t".join(cols) + "\n")
            for row in rows:
                r = done.get(row["order"])
                if r is None:
                    f.write("\t".join([row["order"], row["language"], row["component"], row["unit"], row["path"], "",
                                       "", "", "unattempted"] + [""] * (len(cols) - 9)) + "\n")
                    continue
                f.write("\t".join(str(r.get(c, "") if r.get(c) is not None else "").replace("\t", " ").replace("\n", " ")
                                  for c in cols) + "\n")
        # strata: N_s from the sample file (the frame), n_s attempted
        strata: dict[tuple[str, str], dict] = {}
        for row in self.all_rows:
            s = strata.setdefault((row["language"], row["component"]), {"N_s": int(row["N_s"]),
                                                                       "n_sampled": int(row["n_s"]), "rows": []})
            s["rows"].append(row["order"])
        att = [done[r["order"]] for r in rows if r["order"] in done]

        def counts(rs):
            return {o: sum(1 for r in rs if r["outcome"] == o) for o in OUTCOMES}

        def props(rs):
            c, n = counts(rs), len(rs)
            return {o: {"k": k, "p": round(k / n, 4) if n else None,
                        "wilson95": [round(x, 4) for x in wilson(k, n)] if n else None} for o, k in c.items()}

        per_stratum = {}
        for (lang, comp), s in sorted(strata.items()):
            rs = [r for r in att if r["language"] == lang and r["component"] == comp]
            per_stratum[f"{lang}|{comp}"] = {"language": lang, "component": comp, "N_s": s["N_s"],
                                              "n_sampled": s["n_sampled"], "attempted": len(rs),
                                              "outcomes": props(rs)}

        def stratified(lang: str | None):
            sts = [v for v in per_stratum.values() if lang is None or v["language"] == lang]
            n_frame = sum(v["N_s"] for v in sts)
            used = [v for v in sts if v["attempted"] > 0]
            n_used = sum(v["N_s"] for v in used)
            out = {"N_frame": n_frame, "frame_share_with_attempted_units": round(n_used / n_frame, 4) if n_frame else None,
                   "strata_without_attempted_units": [f"{v['language']}|{v['component']}" for v in sts if not v["attempted"]],
                   "estimates": {}}
            rs = [r for r in att if lang is None or r["language"] == lang]
            for o in OUTCOMES:
                est = var = est_r = var_r = 0.0
                for v in used:
                    p = v["outcomes"][o]["k"] / v["attempted"]
                    w, wr = v["N_s"] / n_frame, v["N_s"] / n_used
                    est += w * p
                    var += w * w * p * (1 - p) / v["attempted"]
                    est_r += wr * p
                    var_r += wr * wr * p * (1 - p) / v["attempted"]
                k = sum(1 for r in rs if r["outcome"] == o)
                n = len(rs)
                h, hr = 1.959963984540054 * math.sqrt(var), 1.959963984540054 * math.sqrt(var_r)
                out["estimates"][o] = {
                    "stratified": round(est, 4), "ci95": [round(max(0.0, est - h), 4), round(min(1.0, est + h), 4)],
                    "renormalised": round(est_r, 4), "renormalised_ci95": [round(max(0.0, est_r - hr), 4),
                                                                          round(min(1.0, est_r + hr), 4)],
                    "unweighted": round(k / n, 4) if n else None,
                    "unweighted_wilson95": [round(x, 4) for x in wilson(k, n)] if n else None, "k": k, "n": n}
            return out

        gaps: dict[str, int] = {}
        for r in att:
            if r["outcome"] == "blocked":
                gaps[r["detail"]] = gaps.get(r["detail"], 0) + 1
        rf: dict[str, list[dict]] = {"deep_recursion": [], "kernel_rejection": [], "not_run": []}
        for r in att:
            if r["outcome"] == "infrastructure_error" and str(r.get("detail", "")).startswith("replay failed"):
                rf[r.get("replay_cause") or "not_run"].append({"order": r["order"], "unit": r["unit"],
                                                                "message": r.get("replay_message", "")})
        langs = sorted({r["language"] for r in rows})
        summ = {"study": "T2", "dry_run": bool(self.a.dry_run), "sample": self.a.sample, "selected": len(rows),
                "attempted": len(att), "unattempted": len(rows) - len(att), "stopped": stopped,
                "counts": counts(att), "per_stratum": per_stratum,
                "per_language": {lang: stratified(lang) for lang in langs}, "overall": stratified(None),
                "cost_model_usd": stats([r["model_usd"] for r in att]),
                "cost_core_s": stats([r["core_s"] + r.get("replay_core_s", 0) for r in att]),
                "cost_by_language": {lang: {"model_usd": stats([r["model_usd"] for r in att if r["language"] == lang]),
                                            "core_s": stats([r["core_s"] + r.get("replay_core_s", 0)
                                                             for r in att if r["language"] == lang])}
                                     for lang in langs},
                "gap_names": dict(sorted(gaps.items(), key=lambda kv: -kv[1])), "replay_failed": rf,
                "front_end": prep, "ledger": json.loads((OUT / "ledger.json").read_text())
                if (OUT / "ledger.json").exists() else None}
        (OUT / "summary.json").write_text(json.dumps(summ, indent=1))
        md = [f"# Prereg T, T2: {len(att)} of {len(rows)} units attempted"
              + (f"; stopped at unit {stopped['at']} ({stopped['rule']})" if stopped else ""), ""]
        for scope, d in [("overall", summ["overall"])] + [(lang, summ["per_language"][lang]) for lang in langs]:
            md += [f"## {scope} (N_frame {d['N_frame']}, frame share with attempted units "
                   f"{d['frame_share_with_attempted_units']})", "",
                   "| outcome | k / n | unweighted | Wilson 95% | stratified | 95% CI |", "|---|---|---|---|---|---|"]
            for o in OUTCOMES:
                e = d["estimates"][o]
                if e["n"]:
                    md.append(f"| {o} | {e['k']} / {e['n']} | {e['unweighted']:.3f} | [{e['unweighted_wilson95'][0]:.3f}, "
                              f"{e['unweighted_wilson95'][1]:.3f}] | {e['stratified']:.3f} | [{e['ci95'][0]:.3f}, "
                              f"{e['ci95'][1]:.3f}] |")
                else:
                    md.append(f"| {o} | 0 / 0 | | | | |")
            md.append("")
        md += ["## Per stratum", "", "| stratum | N_s | sampled | attempted | " + " | ".join(OUTCOMES) + " |",
               "|---|---|---|---|" + "---|" * len(OUTCOMES)]
        for v in per_stratum.values():
            md.append(f"| {v['language']} {v['component']} | {v['N_s']} | {v['n_sampled']} | {v['attempted']} | "
                      + " | ".join(str(v["outcomes"][o]["k"]) for o in OUTCOMES) + " |")
        md += ["", f"Model $ per unit: {summ['cost_model_usd']}", f"Core-s per unit: {summ['cost_core_s']}", "",
               "Gap names:"] + [f"- {k}: {v}" for k, v in summ["gap_names"].items()]
        md += ["", "Infrastructure error \"replay failed\":"]
        for cause, label in (("deep_recursion", "(kernel) deep recursion"), ("kernel_rejection", "other kernel rejection"),
                             ("not_run", "replay could not run")):
            us = rf[cause]
            md.append(f"- {label}: {len(us)}" + "".join(f"\n  - unit {x['order']} `{x['unit']}`: {x['message']}" for x in us))
        (OUT / "summary.md").write_text("\n".join(md) + "\n")
        self.log(f"outcomes: {summ['counts']}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sample", required=True, help="the frozen T2 sample TSV (draw_t2.py's columns)")
    ap.add_argument("--addendum", default=None, help="T/ADDENDUM_T2_sample.md (its sha256 goes into pins.json)")
    ap.add_argument("--manifest", default=None, help="T/SHA256SUMS_T2_addendum: checked at start (required for a real run)")
    ap.add_argument("--manifest-sha", default=None, help="the manifest's own sha256 (required for a real run)")
    ap.add_argument("--pin-file", action="append", help="NAME=PATH: a file whose sha256 goes into pins.json (fix diffs)")
    ap.add_argument("--languages", default=None, help="only these languages of the sample (dry runs), e.g. C++,C")
    ap.add_argument("--first", type=int, default=0, help="only the first K selected units (dry runs)")
    ap.add_argument("--dry-run", action="store_true", help="--no-llm and a $0 counterexample step; no ledger")
    ap.add_argument("--tag", default=None, help="dry runs: records in runs/prereg/T2_dryrun_<TAG> (default T2_dryrun)")
    ap.add_argument("--run-prefix", default=None,
                    help="vo run directories runs/<PREFIX>_<target> (default t2 for the real run, t2dry[_<tag>] for "
                         "dry runs; a dry run may never use t2)")
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--prepare-only", action="store_true", help="step 1 only (front end and extraction)")
    ap.add_argument("--prepare-scope", choices=["all", "needed"], default=None,
                    help="libraries to prepare (default: all; dry runs: needed)")
    ap.add_argument("--prepare-workers", type=int, default=12,
                    help="Lean checks at once in step 1: C/C++ TUs prepared at once; a Java/Rust library's modules")
    ap.add_argument("--price-core-h", type=float, default=0.04, help="compute $ per core-hour (list price)")
    ap.add_argument("--frozen", default=None, help="R10: run veriforch from this frozen copy (created if missing); "
                                                   "required for a real run")
    ap.add_argument("--freeze-only", action="store_true", help="create (or re-check) the --frozen copy and exit")
    ap.add_argument("--workers", type=int, default=16, help="units in flight at once")
    ap.add_argument("--unit-jobs", type=int, default=None,
                    help="vo verify --jobs per unit (default: vo's own, 2 independent components at once, as in D2)")
    ap.add_argument("--free-slots", type=int, default=12, help="units in flight whatever the load")
    ap.add_argument("--load-max", type=float, default=450.0, help="above the free slots: wait while the 1-min load is above")
    ap.add_argument("--mem-min-gb", type=float, default=150.0, help="always: no dispatch while MemAvailable is below")
    ap.add_argument("--poll", type=float, default=30.0, help="seconds between re-checks while waiting")
    ap.add_argument("--stop-at", default=STOP_AT, help="no dispatch from this UTC time on (prereg: 2026-10-27T03:00:00Z)")
    ap.add_argument("--pin-note", action="append", help="a note recorded in pins.json")
    ap.add_argument("--cirlean", default=None, help="cirlean pin (deps/cirlean-<sha>): C and C++")
    ap.add_argument("--jimple-snapshot", default=None, help="JimpleLean snapshot (deps/JimpleLean-<name>): Java")
    ap.add_argument("--strictts", default=None, help="StrictTS pin (deps/strictts-<sha>): TS")
    ap.add_argument("--aeneas", default=None, help="Aeneas pin directory name under deps/ (Rust)")
    ap.add_argument("--rust-env", action="append", help="extra VAR=VALUE for the Rust bridge (Charon, equiv-lean, ...)")
    a = ap.parse_args()
    if a.freeze_only:
        if not a.frozen:
            raise SystemExit("--freeze-only needs --frozen DIR")
        print(json.dumps(freeze(Path(a.frozen).resolve()), indent=1))
        return 0
    if a.dry_run and not a.first:
        a.first = 5
    if a.prepare_scope is None:
        a.prepare_scope = "needed" if a.dry_run else "all"
    if not a.dry_run and not a.frozen:
        raise SystemExit("a real run executes a frozen copy of veriforch (R10): give --frozen DIR, e.g. "
                         "~/veriforch_frozen/T2_<UTC>")
    if not a.dry_run and not (a.manifest and a.manifest_sha and a.addendum):
        raise SystemExit("a real run checks the frozen sample: give --addendum, --manifest and --manifest-sha")
    if not a.dry_run and a.prepare_scope != "all":
        raise SystemExit("a real run prepares every library (--prepare-scope all)")
    if a.tag and not a.dry_run:
        raise SystemExit("--tag is for dry runs only")
    if a.run_prefix is None:
        a.run_prefix = ("t2dry" + (f"_{a.tag}" if a.tag else "")) if a.dry_run else "t2"
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", a.run_prefix):
        raise SystemExit(f"--run-prefix {a.run_prefix!r}: letters, digits and _ only")
    if a.dry_run and a.run_prefix == "t2":
        raise SystemExit("a dry run never uses the real run's directories (--run-prefix t2)")
    if not a.dry_run and a.run_prefix.startswith("t2dry"):
        raise SystemExit("the real run does not use a dry run's directories")
    if a.dry_run:
        global OUT
        OUT = VO / "runs" / "prereg" / ("T2_dryrun" + (f"_{a.tag}" if a.tag else ""))
    Driver(a).run()
    return 0


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Pre-registration D2 (frozen v1: ~/fv_paper/prereg/PREREG_D2_v1.md, SHA256SUMS_D2_v1 161d1d6a…cdce): the driver.

    .venv/bin/python scripts/prereg_d2.py POP --sample rerun|heldout --cirlean SHA --jimple-snapshot NAME
                                           --strictts SHA [--workers N] [--first K] [--dry-run] [--resume] ...

POP is zlib | tinyxml2 | lang3 | estoolkit (CardDemo is not in D2). D2 is D's procedure (below, unchanged) run after
the fixers' changes, on two samples per population: `--sample rerun` = the frozen D sample (D/sample_<pop>.tsv),
`--sample heldout` = D2/heldout_<pop>.tsv; the re-run sample first (a held-out run refuses to start before the re-run
summary exists). Everything lands in runs/prereg/D2/<POP>/<SAMPLE>/; front end and extraction run once per
population (runs/prereg/D2/<POP>/prepare.json) and both samples use the population's vo run directory
(runs/prereg_d2_<pop>, never D's). D2's budget is MODEL spend only (the prereg: compute is reported, not capped):
runs/prereg/D2/ledger.json, $500 for all D2 populations and samples. The pins are given explicitly at launch (no
defaults) and recorded at start, with the change list since D's pins (git log / snapshot list) in pins.json.
For es-toolkit, a generic function the coverage mode emits at fixed type arguments is recorded with its
instantiation (`generic_instance`): every claim about it is about that instance.

The rest of this docstring is D's (PREREG_D_v2), which D2 follows unchanged:

Procedure (the prereg's "Procedure" with R6-R9):
 0. Tool pins are recorded at start (pins.json): bridge directories and commits/snapshots, Lean, clang, Soot, JDK,
    the frozen sample's sha256 and veriforch's own source manifest. No re-pin during a run.
 1. Front end and extraction once per library, before the first unit (`vo verify <target> --only <none> --no-llm`:
    build, units, every generated module compiled at its fixed 900 s timeout); cost in prepare.json.
 2. Per unit u in sample order:
    a. `timeout 1800 vo verify <target> --only <u and every callee in its closure> --attempts 3 --check-timeout 600
       --budget 0.80` (R7);
    b. if u ends `stuck` (or `budget`) and the bridge has an executable semantics (C/C++, COBOL), `vo cex <target>
       --only u --budget <0.80 minus what 2a spent>` within the unit's remaining 30-minute wall;
    c. the kernel replay (`scripts/kernel_replay.sh`, `lake env leanchecker <module>`) of every theorem claimed in
       this unit's run (u and its closure), in the package that built it.
    A callee proved for an earlier unit is reused at no cost (veriforch's proof cache); its cost stays with the
    earlier unit.
 3. Outcome mapping (R6) per unit -> outcomes.tsv; summary.json/summary.md: counts, proportions with Wilson 95%
    intervals (CardDemo, a census: counts only), cost per unit (median, IQR, mean, total), gap names.

Costs per unit: model $ = the rows the unit's commands add to runs/<target>/llm/usage.jsonl; core-seconds = the
guard log of the unit's commands (VO_GUARD_LOG, honoured by scripts/run1.sh, also for Lean checks); compute $ =
core-hours x --price-core-h. The D total (model + compute) is kept in runs/prereg/D/ledger.json, shared by the five
populations: when it reaches $500, every driver stops at its current position (unattempted units are reported and
left out of the denominators).

--workers N (default 1: one unit at a time, as before) runs up to N units of the population at once, dispatched
strictly in sample order. A unit starts only when its --only closure (the unit and its callees) is disjoint from
the closures of all running units; otherwise the dispatcher waits (it never skips ahead). Each worker k > 0 has its
own vo run directory (runs/<target>_w<k>, through a copy of the target file with that name) whose cache/ is a
symlink to the population's run directory's cache/, so proofs, compiled modules and failures are shared (a callee
proved for an earlier unit is reused) while each vo process writes its own package, unit records, model ledger and
verify.json: concurrent vo runs in ONE run directory would rewrite the same generated-module .olean files under
each other's imports (every vo verify restores them from the cache) and would mix their model costs in one
usage.jsonl. Before each dispatch: the stop rule (ledger total + $0.80 x units in flight >= $500: stop dispatching;
the attempted prefix is reported) and, with N > 1, the resource guard (wait while the 1-minute load > --load-max or
MemAvailable < --mem-min-gb). Every wait is logged. --resume skips units with a result and re-dispatches an
interrupted unit (no result).

--dry-run: the first K units (--first, default 2) with `--no-llm` and a $0 counterexample step; no model call is
made. Nothing in the ledger. A dry run works on a renamed copy of the target (its own vo run directory).
--simulate S (dry run, front end only): each matched unit sleeps S seconds instead of running its commands (a test
of the dispatcher on the population's real closures).

Launch (the driver is an orchestrator like `scripts/vo`: its heavy steps run under scripts/run1.sh themselves, with
memory caps up to 128 GiB, which an outer run1.sh can only lower, so wrap it with a large -m):
    scripts/run1.sh -t 172800 -m 256 -c 80 -l runs/prereg/D/<POP>.guard.log -- \
        .venv/bin/python -B scripts/prereg_d.py <POP>
"""
from __future__ import annotations

import argparse
import csv
import fcntl
import hashlib
import json
import math
import os
import re
import statistics
import subprocess
import sys
import threading
import time
from pathlib import Path

VO = Path("/home/user/veriforch")
PREREG = Path("/home/user/fv_paper/prereg")
OUT = VO / "runs" / "prereg" / "D2"
D_BUDGET = 500.0
UNIT_BUDGET = 0.80
UNIT_WALL = 1800

POPS = {
    "zlib": {"target": "targets/prereg_d2_zlib.toml", "sample": "sample_zlib.tsv", "heldout": "heldout_zlib.tsv",
             "match": "c", "semantics": True, "bridge": "cirlean"},
    "tinyxml2": {"target": "targets/prereg_d2_tinyxml2.toml", "sample": "sample_tinyxml2.tsv",
                 "heldout": "heldout_tinyxml2.tsv", "match": "c", "semantics": True, "bridge": "cirlean"},
    "lang3": {"target": "targets/prereg_d2_lang3.toml", "sample": "sample_lang3.tsv", "heldout": "heldout_lang3.tsv",
              "match": "jimple", "semantics": False, "bridge": "jimple"},
    "estoolkit": {"target": "targets/prereg_d2_estoolkit.toml", "sample": "sample_estoolkit.tsv",
                  "heldout": "heldout_estoolkit.tsv", "match": "ts", "semantics": False, "bridge": "strictts"},
}

D_PINS = {"cirlean": "88e6008", "jimple": "20261024T1029Z", "strictts": "ae0eee4"}


def sample_file(pop: str, sample: str) -> Path:
    return PREREG / "D" / POPS[pop]["sample"] if sample == "rerun" else PREREG / "D2" / POPS[pop]["heldout"]


def changes_since_d(pop: str, a) -> dict:
    """The change list between D's pin and this D2 pin, as the prereg asks (commit log or snapshot list)."""
    b = POPS[pop]["bridge"]
    if b == "cirlean":
        return {"from": D_PINS["cirlean"], "to": a.cirlean,
                "log": _out(["git", "-C", str(Path.home() / "cirlean"), "log", "--oneline",
                             f"{D_PINS['cirlean']}..{a.cirlean}"])}
    if b == "strictts":
        return {"from": D_PINS["strictts"], "to": a.strictts,
                "log": _out(["git", "-C", str(Path.home() / "strictts"), "log", "--oneline",
                             f"{D_PINS['strictts']}..{a.strictts}"])}
    snaps = sorted(p.name for p in (Path.home() / "jimplelean_work" / "snapshots").glob("JimpleLean-*"))
    lo, hi = f"JimpleLean-{D_PINS['jimple']}", f"JimpleLean-{a.jimple_snapshot}"
    return {"from": D_PINS["jimple"], "to": a.jimple_snapshot,
            "snapshots_between": [x for x in snaps if lo < x <= hi],
            "note": "JimpleLean ships snapshots, not commits: the list is every snapshot after D's pin up to the D2 pin; "
                    "their notes are in ~/jimplelean_work/HANDOFF_20261023.md and the snapshots' own files"}


OUTCOMES = ["proved_mechanical", "proved_model_stated", "native", "conditional", "partial", "refuted", "blocked",
            "timeout", "infrastructure_error"]


# ------------------------------------------------------------------------------------------------ pins
def bridge_env(pop: str, a) -> dict[str, str]:
    b = POPS[pop]["bridge"]
    if b == "cirlean":
        return {"VO_CIRLEAN_DIR": str(VO / "deps" / f"cirlean-{a.cirlean}"), "VO_CIRLEAN_PIN": a.cirlean}
    if b == "jimple":
        return {"VO_JIMPLE_DIR": str(VO / "deps" / f"JimpleLean-{a.jimple_snapshot}"),
                "VO_JIMPLE_PIN": f"snapshot-{a.jimple_snapshot}"}
    if b == "strictts":
        return {"VO_STRICTTS_DIR": str(VO / "deps" / f"strictts-{a.strictts}"), "VO_STRICTTS_PIN": a.strictts}
    return {"VO_COBLEAN_DIR": str(VO / "deps" / f"coblean-{a.coblean}"), "VO_COBLEAN_PIN": f"snapshot-{a.coblean}"}


def _out(cmd: list[str], cwd: Path | None = None) -> str:
    try:
        return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=120).stdout.strip()
    except Exception as e:                      # a missing tool is recorded, not fatal
        return f"unavailable: {e}"


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def veriforch_manifest() -> tuple[str, int]:
    """SHA256 manifest of veriforch's own sources (orch/, scripts/), the code of this run (R10)."""
    lines = []
    for root in ("orch/veriforch", "scripts"):
        for p in sorted((VO / root).rglob("*")):
            if p.is_file() and "__pycache__" not in p.parts and p.suffix in (".py", ".md", ".sh", ".js", ".ts", ""):
                lines.append(f"{sha256_file(p)}  {p.relative_to(VO)}")
    text = "\n".join(lines) + "\n"
    return hashlib.sha256(text.encode()).hexdigest(), len(lines)


def record_pins(pop: str, a, odir: Path) -> dict:
    env = bridge_env(pop, a)
    bdir = Path(next(iter(env.values())))
    pins = {
        "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "population": pop, "study": "D2", "sample_kind": a.sample,
        "prereg": {"SHA256SUMS_D2_v1": sha256_file(PREREG / "SHA256SUMS_D2_v1"),
                   "PREREG_D2_v1.md": sha256_file(PREREG / "PREREG_D2_v1.md"),
                   "PREREG_D_v2.md": sha256_file(PREREG / "PREREG_D_v2.md"),
                   "sample": str(sample_file(pop, a.sample).relative_to(PREREG)),
                   "sample_sha256": sha256_file(sample_file(pop, a.sample)),
                   "fix_targets_sha256": sha256_file(PREREG / "D2" / "fix_targets.tsv")},
        "changes_since_D_pins": changes_since_d(pop, a),
        "notes": list(getattr(a, "pin_note", None) or []),
        "bridge_env": env,
        "bridge_commit": _out(["git", "-C", str(bdir), "log", "-1", "--format=%H %s"]) if (bdir / ".git").exists()
        else None,
        "bridge_snapshot_sha256sums": sha256_file(bdir / "SHA256SUMS") if (bdir / "SHA256SUMS").exists() else None,
        "lean": _out([str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"), "--version"]),
        "target_toml": a.target_path, "target_toml_sha256": a.target_text_sha,
        "veriforch_frozen_copy": a.frozen_info,
    }
    if POPS[pop]["bridge"] == "cirlean":
        from veriforch.adapters.cir import build as cb          # noqa: E402 (imported with the env set)
        pins["clang"] = {"path": str(cb.CLANG), "version": _out([str(cb.CLANG), "--version"]).splitlines()[:1]}
    if POPS[pop]["bridge"] == "jimple":
        from veriforch.adapters.jimple import build as jb      # noqa: E402 (imported with the env set)
        pins["soot_jar_sha256"] = sha256_file(jb.SOOT)
        pins["jdk"] = _out([str(jb.JDK / "java"), "-version"]) or _out(["bash", "-lc", f"{jb.JDK}/java -version 2>&1"])
    m, n = veriforch_manifest()
    pins["veriforch_manifest_sha256"], pins["veriforch_files"] = m, n
    pins["workers"] = getattr(a, "workers", 1)
    # the run's start record stays; a resumed run adds its own record next to it
    out = odir / "pins.json"
    if out.exists() and getattr(a, "resume", False):
        out = odir / f"pins_resume_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}.json"
    out.write_text(json.dumps(pins, indent=1))
    return pins


def freeze(dest: Path) -> dict:
    """R10: veriforch as a frozen copy with a SHA256 manifest. The copy holds the code (orch/veriforch, scripts/,
    VerifOrch/ (its Lean support modules), tools/, the prereg target files) and symlinks to the real runs/, deps/, targets/ and .venv, so the run's records stay in the
    real tree; every vo call of the run executes the copy (PYTHONPATH and VO_ROOT point at it). An existing copy is
    reused as is (its manifest is re-checked); a crash fix is a new copy."""
    import shutil
    man = dest / "SHA256SUMS"
    if not dest.exists():
        dest.mkdir(parents=True)
        shutil.copytree(VO / "orch" / "veriforch", dest / "orch" / "veriforch",
                        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        shutil.copytree(VO / "scripts", dest / "scripts", ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        # veriforch's own Lean sources (support modules of mechanical statements) and tools (vo-cirrun)
        for d in ("VerifOrch", "tools"):
            if (VO / d).exists():
                shutil.copytree(VO / d, dest / d, ignore=shutil.ignore_patterns("__pycache__", "*.pyc", ".lake"))
        (dest / "targets_prereg").mkdir()
        for c in POPS.values():
            shutil.copy2(VO / c["target"], dest / "targets_prereg" / Path(c["target"]).name)
        for link in ("runs", "deps", "targets", ".venv"):
            (dest / link).symlink_to(VO / link)
        files = sorted(q for q in dest.rglob("*") if q.is_file() and not q.is_symlink()
                       and not any(part in ("runs", "deps", "targets", ".venv") for part in q.relative_to(dest).parts[:1])
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


# ------------------------------------------------------------------------------------------------ ledger
def ledger_update(delta_usd: float, delta_core_h: float, price: float, pop: str, dry: bool) -> dict:
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
            d["units"][pop] = d["units"].get(pop, 0) + (1 if (delta_usd or delta_core_h) else 0)
            p.write_text(json.dumps(d, indent=1))
        fcntl.flock(lk, fcntl.LOCK_UN)
    return d


def ledger_total() -> float:
    p = OUT / "ledger.json"
    if not p.exists():
        return 0.0
    d = json.loads(p.read_text())
    return d["model_usd"]                     # D2's cap is model spend only (compute is reported, not capped)


# ------------------------------------------------------------------------------------------------ records
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


def mem_available_gb() -> float:
    for line in open("/proc/meminfo"):
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) / (1024 * 1024)
    return float("inf")


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


def match_unit(kind: str, row: dict, units: list[dict]) -> dict | None:
    """The unit of a sample row (the matching rules of the feasibility pass)."""
    if kind == "c":
        f, line, name = row["file"], int(row["line"]), row["name"]

        def loc(u):
            if not u.get("loc") or ":" not in u["loc"]:
                return None, None
            fl, ln = u["loc"].rsplit(":", 1)
            return Path(fl).name, int(ln) if ln.isdigit() else None
        cand = [u for u in units if loc(u) == (f, line)]
        if not cand:
            def dem(u):
                sig = u.get("signature") if isinstance(u.get("signature"), dict) else {}
                return (sig.get("demangled") or "").split("(")[0].split("::")[-1]
            cand = [u for u in units if loc(u)[0] == f and (u["name"].split("$")[-1] == name or dem(u) == name)]
        if not cand:
            cand = [u for d in range(-3, 4) for u in units if loc(u) == (f, line + d)]
        return cand[0] if cand else None
    if kind == "jimple":
        want = f"{row['class']}.{row['method']}({jtypes(row['descriptor'])})"
        return next((u for u in units if u["name"] == want), None)
    if kind == "ts":
        f, line, name = row["file"], int(row["line"]), row["name"]
        for u in units:
            lf, _, ll = (u.get("loc") or "").rpartition(":")
            if lf.endswith(f) and ll.isdigit() and int(ll) == line:
                return u
        return next((u for u in units if u["name"] == name and (u.get("loc") or "").split(":")[0].endswith(f)), None)
    if kind == "cobol":
        return next((u for u in units if u.get("loc") == row["path"]), None)
    raise ValueError(kind)


def closure(name: str, by: dict[str, dict]) -> list[str]:
    seen, todo = [], [name]
    while todo:
        n = todo.pop()
        if n in seen or n not in by:
            continue
        seen.append(n)
        todo += by[n].get("callees", [])
    return seen


def wilson(k: int, n: int, z: float = 1.959963984540054) -> tuple[float, float]:
    if n == 0:
        return (float("nan"), float("nan"))
    p = k / n
    den = 1 + z * z / n
    c = (p + z * z / (2 * n)) / den
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return (max(0.0, c - h), min(1.0, c + h))


# ------------------------------------------------------------------------------------------------ outcome (R6)
def map_outcome(info: dict) -> tuple[str, str]:
    """(outcome, detail) from one unit's records, following PREREG_D_v2's table."""
    if info.get("library_error"):
        return "blocked", "front end/extraction: " + info["library_error"]
    if info.get("unit") is None:
        return "blocked", "not emitted by the front end"
    if info.get("scope", "in_scope") != "in_scope":
        return "blocked", info["scope"]
    if info.get("crash"):
        return "infrastructure_error", "tool crash: " + info["crash"]
    f = info.get("finding") or {}
    if f.get("verdict") in ("real_bug", "missing_precondition") and f.get("counterexample"):
        return "refuted", f["verdict"]
    if info.get("killed"):
        return "timeout", "killed at the 30-minute wall"
    o = info.get("outcome") or {}
    st = o.get("status")
    if st == "proved":
        if o.get("trust") == "native":
            return "native", "native_decide"
        if info.get("replay") != "PASS":
            # The evidence-owner session (DEVIATIONS): a proof that checks but fails kernel replay is not proved; infrastructure error
            # "replay failed", reported by cause with every unit named
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


# ------------------------------------------------------------------------------------------------ the run
class Driver:
    def __init__(self, pop: str, a):
        self.pop, self.a = pop, a
        self.cfg = POPS[pop]
        self.pdir = OUT / pop                      # per population: front end once, shared by both samples
        self.odir = self.pdir / a.sample
        (self.odir / "units").mkdir(parents=True, exist_ok=True)
        root = Path(a.frozen).resolve() if a.frozen else VO
        a.frozen_info = freeze(root) if a.frozen else None
        self.env = dict(os.environ, **bridge_env(pop, a), VO_ROOT=str(root),
                        PYTHONPATH=str(root / "orch"), OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1",
                        MKL_NUM_THREADS="1", RAYON_NUM_THREADS="1", TMPDIR=str(VO / "scratch" / "tmp"))
        # vo as scripts/vo runs it (nice 10, the venv's python), from the frozen copy when there is one
        self.vo = ["nice", "-n", "10", str(VO / ".venv" / "bin" / "python"), "-B", "-m", "veriforch"]
        self.replay_sh = str(root / "scripts" / "kernel_replay.sh")
        os.environ.update(bridge_env(pop, a))
        sys.path.insert(0, str(VO / "orch"))
        from veriforch.config import load_target
        self.tpath = (Path(a.frozen).resolve() / "targets_prereg" / Path(self.cfg["target"]).name) if a.frozen \
            else VO / self.cfg["target"]
        if a.dry_run:
            # a dry run works on a copy of the target under another name, so vo's run directory (proof, olean and
            # negative caches, unit records, the model ledger) is not the real run's
            text = self.tpath.read_text()
            text = re.sub(r'^name = "([^"]+)"', r'name = "\1_dryrun"', text, count=1, flags=re.M)
            self.tpath = self.pdir / "target_dryrun.toml"
            self.tpath.write_text(text)
        self.t = load_target(self.tpath)
        a.target_text_sha = sha256_file(self.tpath)
        a.target_path = str(self.tpath)
        self.rd = VO / "runs" / self.t.name
        self.vdir = self.rd / self.t.version / self.t.variants[0].name

    def log(self, msg: str) -> None:
        line = f"{time.strftime('%H:%M:%SZ', time.gmtime())} {msg}"
        print(line, flush=True)
        with open(self.odir / "driver.log", "a") as f:
            f.write(line + "\n")

    def run_cmd(self, cmd: list[str], guard: Path, timeout: int) -> tuple[int, str, float]:
        env = dict(self.env, VO_GUARD_LOG=str(guard))
        t0 = time.time()
        try:
            p = subprocess.run(cmd, cwd=VO, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                               timeout=timeout + 120)
            return p.returncode, p.stdout, time.time() - t0
        except subprocess.TimeoutExpired as e:
            return 124, (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or ""), time.time() - t0

    def prepare(self) -> dict:
        """Front end + extraction once (procedure step 1)."""
        pj = self.pdir / "prepare.json"
        if pj.exists() and (self.a.resume or self.a.sample == "heldout"):
            return json.loads(pj.read_text())        # front end and extraction once per population
        guard = self.pdir / "prepare.guard.log"
        n0 = len(usage_rows(self.rd))
        if self.a.fe_only:
            # dry run, front end only: build and units (`vo scan`), no generated-module compilation
            rc, out, wall = self.run_cmd(["timeout", "86400", *self.vo, "scan", str(self.tpath)], guard, 86400)
            (self.pdir / "prepare.log").write_text(out)
            res = {"rc": rc, "wall_s": round(wall, 1), "core_s": round(guard_core_s(guard), 1), "model_usd": 0.0,
                   "error": None if rc == 0 else (out.strip().splitlines() or [f"exit {rc}"])[-1][:300],
                   "fe_only": True}
            pj.write_text(json.dumps(res, indent=1))
            return res
        # generated modules compile as independent single-thread jobs (--jobs: how many at once; e.g. lang3's ~6,000
        # shape/method modules at ~10 s each)
        rc, out, wall = self.run_cmd(["timeout", "86400", *self.vo, "verify", str(self.tpath), "--only",
                                      "__vo_prepare_no_unit__", "--no-llm", "--check-timeout", "600",
                                      "--jobs", str(self.a.prepare_jobs)], guard, 86400)
        (self.pdir / "prepare.log").write_text(out)
        res = {"rc": rc, "wall_s": round(wall, 1), "core_s": round(guard_core_s(guard), 1),
               "model_usd": round(sum(r.get("dollars", 0) for r in usage_rows(self.rd)[n0:]), 4),
               "error": None}
        if rc != 0:
            m = re.findall(r"(RuntimeError|Error|error)[: ].*", out)
            res["error"] = (m[-1] if m else out.strip().splitlines()[-1] if out.strip() else f"exit {rc}")[:300]
        units_p = self.vdir / "units.json"
        res["units_json"] = str(units_p) if units_p.exists() else None
        pj.write_text(json.dumps(res, indent=1))
        return res

    def units(self) -> list[dict]:
        p = self.vdir / "units.json"
        return json.loads(p.read_text()) if p.exists() else []

    def slot(self, k: int) -> dict:
        """Worker k's target file and vo run directory: worker 0 is the population's own; worker k > 0 has
        runs/<target>_w<k> (a copy of the target file under that name) with cache/ linked to the population's cache."""
        if k == 0:
            return {"k": 0, "tpath": self.tpath, "rd": self.rd, "vdir": self.vdir}
        name = f"{self.t.name}_w{k}"
        text = re.sub(r'^name = "([^"]+)"', f'name = "{name}"', self.tpath.read_text(), count=1, flags=re.M)
        tp = self.odir / f"target_w{k}.toml"
        if not tp.exists() or tp.read_text() != text:
            tp.write_text(text)
        rd = VO / "runs" / name
        rd.mkdir(parents=True, exist_ok=True)
        main_cache = self.rd / "cache"
        main_cache.mkdir(parents=True, exist_ok=True)
        cache = rd / "cache"
        if not cache.exists() and not cache.is_symlink():
            cache.symlink_to(main_cache)
        elif not (cache.is_symlink() and cache.resolve() == main_cache.resolve()):
            raise SystemExit(f"{cache} exists and is not the link to {main_cache}")
        return {"k": k, "tpath": tp, "rd": rd, "vdir": rd / self.t.version / self.t.variants[0].name}

    def unit_record(self, name: str, vdir: Path | None = None) -> dict | None:
        p = (vdir or self.vdir) / "units" / f"{name}.json"
        return json.loads(p.read_text()) if p.exists() else None

    def module_package(self, module: str, rd: Path | None = None) -> Path | None:
        """The package that built a module: the newest `.lake/build/lib/lean/<module>.olean` under the run dir."""
        rd = rd or self.rd
        rel = Path(".lake/build/lib/lean") / (module.replace(".", "/") + ".olean")
        cands = [p for p in rd.glob("lean*/" + str(rel))] + [p for p in rd.glob("lean*/*/" + str(rel))]
        if not cands:
            return None
        best = max(cands, key=lambda p: p.stat().st_mtime)
        return Path(str(best).split("/.lake/build/lib/lean/")[0])

    def replay(self, names: list[str], guard: Path, s: dict | None = None) -> tuple[str | None, str | None, str, list[str]]:
        """Kernel replay of the theorems this unit's run claims (status proved): u's own module and its proved callees'.
        -> (u's verdict PASS/FAIL or None when u claims nothing, failure cause, failure message, one line per module).
        Causes: "deep_recursion" (the kernel's "(kernel) deep recursion"), "kernel_rejection" (any other rejection),
        "not_run" (the module is not in the run's packages)."""
        s = s or self.slot(0)
        mods = []
        for n in names:
            r = self.unit_record(n, s["vdir"])
            if r and r.get("status") == "proved" and (r.get("obligation") or {}).get("module"):
                mods.append((n, r["obligation"]["module"]))
        if not mods:
            return None, None, "", []
        lines, verdict, cause, msg = [], None, None, ""
        for n, mod in mods:
            pkg = self.module_package(mod, s["rd"])
            if pkg is None:
                line, c = f"FAIL {mod}: module not found in the run's packages", "not_run"
            else:
                rc, out, _ = self.run_cmd([self.replay_sh, "--log-dir", str(self.odir / "replay"), str(pkg), mod],
                                          guard, 3600)
                line = next((l for l in out.splitlines() if l.startswith(("PASS", "FAIL"))), out.strip()[-300:])
                full = out + "\n" + _read(self.odir / "replay" / f"{mod}.log")
                c = None if line.startswith("PASS") else ("deep_recursion" if "deep recursion" in full
                                                          else "kernel_rejection")
            lines.append(f"{n}: {line}")
            if n == names[0]:
                verdict = "PASS" if c is None else "FAIL"
                cause, msg = c, line[:400]
        # callees' replays are listed in the record (lines); the outcome uses the unit's own theorem
        return verdict, cause, msg, lines

    def run_unit(self, row: dict, units: list[dict], by: dict[str, dict], lib_error: str | None,
                 s: dict | None = None) -> dict:
        s = s or self.slot(0)
        order, key = row["order"], row["key"]
        u = match_unit(self.cfg["match"], row, units)
        info = {"order": order, "key": key, "unit": u["name"] if u else None,
                "scope": u["scope"] if u else None, "library_error": lib_error}
        rec = {"order": order, "key": key, "unit": info["unit"], "model_usd": 0.0, "core_s": 0.0, "wall_s": 0.0,
               "model_proposals": 0, "attempts_record": None, "statement_origin": "", "trust": "", "replay": "",
               "closure": []}
        inst = ((u or {}).get("signature") or {}).get("instance")
        if inst:
            rec["generic_instance"] = inst          # es-toolkit: a generic emitted at fixed type arguments
        if lib_error or u is None:
            out, detail = map_outcome(info)
            rec.update(outcome=out, detail=detail)
            return rec
        # a gap unit runs the same command (veriforch records the gap and makes its default intended-contract
        # call); its outcome is blocked whatever the command does, and its cost is recorded
        if self.a.fe_only:
            if self.a.simulate:
                time.sleep(self.a.simulate)
            out, detail = map_outcome(info) if u["scope"] != "in_scope" else ("not_run", "front-end-only dry run")
            rec.update(outcome=out, detail=detail, closure=closure(u["name"], by))
            return rec
        names = closure(u["name"], by)
        rec["closure"] = names
        guard = self.odir / "units" / f"{int(order):03d}.guard.log"
        ulog = self.odir / "units" / f"{int(order):03d}.log"
        n0 = len(usage_rows(s["rd"]))
        cmd = ["timeout", str(UNIT_WALL), *self.vo, "verify", str(s["tpath"])]
        for n in names:
            cmd += ["--only", n]
        cmd += ["--attempts", "3", "--check-timeout", "600", "--budget", f"{UNIT_BUDGET:.2f}"]
        if self.a.dry_run:
            cmd.append("--no-llm")
        rc, out, wall = self.run_cmd(cmd, guard, UNIT_WALL)
        ulog.write_text(" ".join(cmd) + "\n" + out)
        info["killed"] = rc == 124
        if rc not in (0, 124):
            info["crash"] = (out.strip().splitlines() or [f"exit {rc}"])[-1][:300]
        o = self.unit_record(u["name"], s["vdir"])
        info["outcome"] = o
        spent = sum(r.get("dollars", 0) for r in usage_rows(s["rd"])[n0:])
        # counterexample step (C/C++, COBOL) for a stuck unit, in the remaining wall and budget
        if o and o.get("status") in ("stuck", "budget") and self.cfg["semantics"] and not info["killed"]:
            left_wall = UNIT_WALL - wall
            left_usd = 0.0 if self.a.dry_run else max(0.0, UNIT_BUDGET - spent)
            if left_wall > 60:
                c = ["timeout", str(int(left_wall)), *self.vo, "cex", str(s["tpath"]), "--only", u["name"], "--budget",
                     f"{left_usd:.4f}"]
                t_cex = time.time()
                rc2, out2, w2 = self.run_cmd(c, guard, int(left_wall))
                with open(ulog, "a") as f:
                    f.write("\n" + " ".join(c) + "\n" + out2)
                wall += w2
                if rc2 == 124:
                    info["killed"] = True
                elif rc2 != 0:
                    info["crash"] = "vo cex: " + ((out2.strip().splitlines() or [f"exit {rc2}"])[-1])[:280]
                fp = s["vdir"] / "findings" / f"{u['name']}.json"
                # only a finding written by this step counts (an older file may come from another run)
                info["finding"] = json.loads(fp.read_text()) if fp.exists() and fp.stat().st_mtime >= t_cex - 1 \
                    else None
        rows_u = usage_rows(s["rd"])[n0:]
        rec["model_usd"] = round(sum(r.get("dollars", 0) for r in rows_u), 4)
        rec["model_proposals"] = sum(1 for r in rows_u if str(r.get("task", "")).startswith(
            f"{self.t.variants[0].name}:{u['name']}:"))
        # kernel replay of the claimed theorems (outside the unit's wall)
        rguard = self.odir / "units" / f"{int(order):03d}.replay.guard.log"
        verdict, cause, rmsg, lines = self.replay(names, rguard, s)
        info["replay"], info["replay_cause"], info["replay_message"] = verdict, cause, rmsg
        rec["replay"] = verdict or ""
        rec["replay_cause"] = cause or ""
        rec["replay_message"] = rmsg
        rec["replay_lines"] = lines
        rec["core_s"] = round(guard_core_s(guard), 1)
        rec["replay_core_s"] = round(guard_core_s(rguard), 1)
        rec["wall_s"] = round(wall, 1)
        if o:
            rec["attempts_record"] = o.get("attempts")
            rec["statement_origin"] = o.get("statement_origin", "")
            rec["trust"] = o.get("trust", "")
            rec["status"] = o.get("status")
        out, detail = map_outcome(info)
        rec.update(outcome=out, detail=detail)
        return rec

    def run(self) -> None:
        self.log(f"start {self.pop} ({'dry run' if self.a.dry_run else 'RUN'}), target {self.tpath}")
        if self.a.sample == "heldout" and not self.a.dry_run and not (self.pdir / "rerun" / "summary.json").exists():
            raise SystemExit("D2 order: the re-run sample of this population finishes first (no rerun/summary.json)")
        if self.a.sample == "rerun" and not self.a.dry_run and not self.a.resume and (self.vdir / "units").exists() \
                and any((self.vdir / "units").glob("*.json")):
            raise SystemExit(f"{self.vdir}/units holds unit records from an earlier run: the real run starts from "
                             "an empty run directory (or use --resume)")
        record_pins(self.pop, self.a, self.odir)
        if self.cfg["bridge"] == "jimple":
            snaps = sorted(p.name for p in (Path.home() / "jimplelean_work" / "snapshots").glob("JimpleLean-*"))
            if snaps and snaps[-1] != f"JimpleLean-{self.a.jimple_snapshot}":
                self.log(f"NOTE: a newer JimpleLean snapshot exists ({snaps[-1]}); the pin is the newest GREEN one at "
                         f"run start: copy it (with data/) into deps/ and pass --jimple-snapshot if it is green")
        prep = self.prepare()
        self.log(f"front end + extraction: rc {prep['rc']}, {prep['wall_s']} s wall, {prep['core_s']} core-s"
                 + (f", error {prep['error']}" if prep["error"] else ""))
        units = self.units()
        lib_error = prep["error"] if (prep["rc"] != 0 and not units) else None
        by = {u["name"]: u for u in units}
        rows = list(csv.DictReader(open(sample_file(self.pop, self.a.sample)), delimiter="\t"))
        if self.a.first:
            rows = rows[:self.a.first]
        done = {}
        res_p = self.odir / "results.jsonl"
        if self.a.resume and res_p.exists():
            for line in res_p.read_text().splitlines():
                r = json.loads(line)
                done[r["order"]] = r
        stopped_at = self.dispatch(rows, units, by, lib_error, done, res_p)
        self.write_outcomes(rows, done, stopped_at, prep)

    def _finish(self, row: dict, rec: dict, k: int, t0: float, done: dict, res_p: Path) -> None:
        ledger_update(rec["model_usd"], (rec["core_s"] + rec.get("replay_core_s", 0)) / 3600,
                      self.a.price_core_h, self.pop, self.a.dry_run)
        rec["worker"] = k
        with self.cond:
            done[row["order"]] = rec
            with open(res_p, "a") as f:
                f.write(json.dumps(rec) + "\n")
            self.running.pop(row["order"], None)
            self.free.append(k)
            self.cond.notify_all()
        self.log(f"unit {row['order']} {row['key'][:60]}: {rec['outcome']} ({rec['detail'][:80]}) "
                 f"${rec['model_usd']:.2f} {rec['core_s']:.0f} core-s {time.time() - t0:.0f} s (worker {k})")

    def _work(self, row: dict, units: list[dict], by: dict, lib_error, k: int, done: dict, res_p: Path) -> None:
        t0 = time.time()
        try:
            rec = self.run_unit(row, units, by, lib_error, self.slot(k))
        except Exception as e:                  # a driver error must not leave the unit in flight forever
            rec = {"order": row["order"], "key": row["key"], "unit": None, "outcome": "infrastructure_error",
                   "detail": f"driver error: {type(e).__name__}: {e}"[:300], "model_usd": 0.0, "core_s": 0.0,
                   "wall_s": round(time.time() - t0, 1), "model_proposals": 0, "attempts_record": None}
        self._finish(row, rec, k, t0, done, res_p)

    def dispatch(self, rows: list[dict], units: list[dict], by: dict, lib_error, done: dict, res_p: Path):
        """Dispatch the units in sample order on --workers workers (see the module doc): never skip ahead; wait while
        the next unit's closure overlaps a running unit's, while every worker is busy, or (N > 1) while the machine is
        loaded; stop dispatching when the ledger total plus $0.80 per unit in flight reaches $500."""
        n = max(1, self.a.workers)
        self.cond = threading.Condition()
        self.running: dict[str, set] = {}
        self.free = list(range(n))
        threads = []
        stopped_at = None
        for row in rows:
            if row["order"] in done:
                continue
            u = None if lib_error else match_unit(self.cfg["match"], row, units)
            cl = set(closure(u["name"], by)) if u else set()
            logged: set = set()
            t_wait = None
            last_res_log = 0.0
            with self.cond:
                while True:
                    if not self.a.dry_run and ledger_total() + UNIT_BUDGET * len(self.running) >= D_BUDGET:
                        stopped_at = row["order"]
                        break
                    reason, key = None, None
                    if not self.free:
                        reason, key = f"all {n} workers busy (units {sorted(self.running, key=int)})", "busy"
                    else:
                        clash = sorted((o for o, c in self.running.items() if c & cl), key=int)
                        if clash:
                            shared = sorted(set().union(*(self.running[o] for o in clash)) & cl)
                            reason = f"closure overlaps running unit(s) {clash} on {shared[:4]}"
                            key = ("clash", tuple(clash))
                        elif n > 1:
                            load, mem = os.getloadavg()[0], mem_available_gb()
                            # the first --free-slots units of this population run whatever the load (user via the coordinating session,
                            # 10-24 21:4xZ); the RAM guard always applies
                            over = load > self.a.load_max and len(self.running) >= self.a.free_slots
                            if over or mem < self.a.mem_min_gb:
                                reason = (f"resource guard: 1-min load {load:.0f} (max {self.a.load_max:.0f}), "
                                          f"MemAvailable {mem:.0f} GB (min {self.a.mem_min_gb:.0f})")
                                key = "resources"
                    if reason is None:
                        break
                    t_wait = t_wait or time.time()
                    if key not in logged or (key == "resources" and time.time() - last_res_log > 300):
                        self.log(f"wait before unit {row['order']}: {reason}")
                        logged.add(key)
                        last_res_log = time.time() if key == "resources" else last_res_log
                    self.cond.wait(timeout=self.a.poll)
                if stopped_at is not None:
                    self.log(f"stop rule: ledger ${ledger_total():.2f} + ${UNIT_BUDGET:.2f} x {len(self.running)} in "
                             f"flight >= ${D_BUDGET:.0f}: no dispatch from unit {row['order']} on")
                    break
                k = self.free.pop(0)
                self.running[row["order"]] = cl
            if t_wait:
                self.log(f"dispatch unit {row['order']} to worker {k} after {time.time() - t_wait:.0f} s of waiting")
            elif n > 1:
                self.log(f"dispatch unit {row['order']} to worker {k} (closure {len(cl)} units)")
            if n == 1:
                self._work(row, units, by, lib_error, k, done, res_p)       # one at a time, in this thread
            else:
                th = threading.Thread(target=self._work, args=(row, units, by, lib_error, k, done, res_p))
                th.start()
                threads.append(th)
        for th in threads:
            th.join()
        return stopped_at

    def write_outcomes(self, rows: list[dict], done: dict, stopped_at, prep: dict) -> None:
        cols = ["order", "key", "unit", "outcome", "detail", "statement_origin", "trust", "replay", "replay_cause",
                "model_usd", "core_s", "replay_core_s", "wall_s", "model_proposals", "attempts_record"]
        with open(self.odir / "outcomes.tsv", "w") as f:
            f.write("\t".join(cols) + "\n")
            for row in rows:
                r = done.get(row["order"])
                if r is None:
                    f.write("\t".join([row["order"], row["key"], "", "unattempted"] + [""] * (len(cols) - 4)) + "\n")
                    continue
                f.write("\t".join(str(r.get(c, "")).replace("\t", " ").replace("\n", " ") for c in cols) + "\n")
        att = [done[r["order"]] for r in rows if r["order"] in done]
        n = len(att)
        census = self.cfg.get("census", False)
        counts = {o: sum(1 for r in att if r["outcome"] == o) for o in OUTCOMES + (["not_run"] if self.a.fe_only else [])}
        summ = {"population": self.pop, "attempted": n, "unattempted": len(rows) - n, "stopped_at": stopped_at,
                "counts": counts, "front_end": prep}
        if not census:
            summ["wilson95"] = {o: [round(x, 4) for x in wilson(k, n)] + [round(k / n, 4) if n else None]
                                for o, k in counts.items()}

        def stats(xs):
            if not xs:
                return None
            q = statistics.quantiles(xs, n=4) if len(xs) >= 2 else [xs[0]] * 3
            return {"median": statistics.median(xs), "q1": q[0], "q3": q[2], "mean": statistics.mean(xs),
                    "total": sum(xs)}
        summ["cost_model_usd"] = stats([r["model_usd"] for r in att])
        summ["cost_core_s"] = stats([r["core_s"] for r in att])
        gaps: dict[str, int] = {}
        for r in att:
            if r["outcome"] == "blocked":
                gaps[r["detail"]] = gaps.get(r["detail"], 0) + 1
        summ["gap_names"] = dict(sorted(gaps.items(), key=lambda kv: -kv[1]))
        rf: dict[str, list[dict]] = {"deep_recursion": [], "kernel_rejection": [], "not_run": []}
        for r in att:
            if r["outcome"] == "infrastructure_error" and str(r.get("detail", "")).startswith("replay failed"):
                rf[r.get("replay_cause") or "not_run"].append({"order": r["order"], "unit": r["unit"],
                                                                "message": r.get("replay_message", "")})
        summ["replay_failed"] = rf
        (self.odir / "summary.json").write_text(json.dumps(summ, indent=1))
        md = [f"# Prereg D, {self.pop}: {n} attempted" + (f", stopped at {stopped_at}" if stopped_at else ""), "",
              "| outcome | count | proportion | Wilson 95% |", "|---|---|---|---|"]
        for o in OUTCOMES:
            k = counts[o]
            if census:
                md.append(f"| {o} | {k} | | |")
            else:
                lo, hi = wilson(k, n)
                md.append(f"| {o} | {k} | {k / n:.3f} | [{lo:.3f}, {hi:.3f}] |" if n else f"| {o} | 0 | | |")
        md += ["", f"Model $ per unit: {summ['cost_model_usd']}", f"Core-s per unit: {summ['cost_core_s']}", "",
               "Gap names:"] + [f"- {k}: {v}" for k, v in summ["gap_names"].items()]
        md += ["", "Infrastructure error \"replay failed\" (a proof that checks but fails kernel replay; not proved):"]
        for cause, label in (("deep_recursion", "(kernel) deep recursion"), ("kernel_rejection", "other kernel rejection"),
                             ("not_run", "replay could not run")):
            us = summ["replay_failed"][cause]
            md.append(f"- {label}: {len(us)}" + ("".join(f"\n  - unit {x['order']} `{x['unit']}`: {x['message']}"
                                                        for x in us)))
        (self.odir / "summary.md").write_text("\n".join(md) + "\n")
        self.log(f"outcomes: {counts}")


def _read(p: Path) -> str:
    try:
        return p.read_text(errors="replace")
    except OSError:
        return ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("pop", choices=sorted(POPS))
    ap.add_argument("--pin-note", action="append", help="a note recorded in pins.json (known issues of a pinned tool)")
    ap.add_argument("--sample", required=True, choices=["rerun", "heldout"],
                    help="rerun = the frozen D sample; heldout = D2/heldout_<pop>.tsv (after the re-run sample)")
    ap.add_argument("--first", type=int, default=0, help="only the first K sample units (dry runs)")
    ap.add_argument("--dry-run", action="store_true", help="--no-llm and a $0 counterexample step; no ledger")
    ap.add_argument("--resume", action="store_true")
    ap.add_argument("--price-core-h", type=float, default=0.04, help="compute $ per core-hour (list price)")
    ap.add_argument("--prepare-jobs", type=int, default=4, help="generated modules compiled at once (step 1)")
    ap.add_argument("--fe-only", action="store_true", help="dry run: front end, units and mapping only (no verify)")
    ap.add_argument("--frozen", default=None, help="R10: run veriforch from this frozen copy (created if missing); "
                                                   "required for a real run")
    ap.add_argument("--freeze-only", action="store_true", help="create (or re-check) the --frozen copy and exit")
    ap.add_argument("--workers", type=int, default=2, help="units in flight at once (D2 default 2)")
    ap.add_argument("--load-max", type=float, default=320.0, help="resource guard: wait while the 1-min load is above")
    ap.add_argument("--free-slots", type=int, default=0,
                    help="units of this population that may run whatever the load (the RAM guard still applies)")
    ap.add_argument("--mem-min-gb", type=float, default=150.0, help="resource guard: wait while MemAvailable is below")
    ap.add_argument("--poll", type=float, default=30.0, help="seconds between re-checks while waiting")
    ap.add_argument("--simulate", type=float, default=0.0,
                    help="dry run, front end only: each matched unit sleeps this long (dispatcher test)")
    ap.add_argument("--cirlean", default=None, help="cirlean pin with the D2 fixes (deps/cirlean-<sha>); required for "
                                                    "zlib/tinyxml2")
    ap.add_argument("--jimple-snapshot", default=None, help="JimpleLean snapshot with the D2 fixes (deps/JimpleLean-<name>,"
                                                            " copied with data/); required for lang3")
    ap.add_argument("--strictts", default=None, help="StrictTS pin with the D2 fixes (deps/strictts-<sha>); required for "
                                                     "estoolkit")
    a = ap.parse_args()
    a.coblean = None
    need = {"cirlean": "cirlean", "jimple": "jimple_snapshot", "strictts": "strictts"}[POPS[a.pop]["bridge"]]
    if not a.freeze_only and not getattr(a, need):
        raise SystemExit(f"D2 pins are explicit: give --{need.replace('_', '-')} for {a.pop}")
    if a.freeze_only:
        if not a.frozen:
            raise SystemExit("--freeze-only needs --frozen DIR")
        print(json.dumps(freeze(Path(a.frozen).resolve()), indent=1))
        return 0
    if a.simulate:
        a.fe_only = True
    if a.fe_only:
        a.dry_run = True
    if a.dry_run and not a.first:
        a.first = 2
    if not a.dry_run and not a.frozen:
        raise SystemExit("a real run executes a frozen copy of veriforch (R10): give --frozen DIR, e.g. "
                         f"~/veriforch_frozen/D2_<UTC>")
    if a.dry_run:
        global OUT
        OUT = VO / "runs" / "prereg" / ("D2_dryrun_fe" if a.fe_only else "D2_dryrun")
    Driver(a.pop, a).run()
    return 0


if __name__ == "__main__":
    sys.exit(main())

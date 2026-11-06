"""Pre-registration C, run exactly as frozen (PREREG_C_v2.md; package ~/fv_paper/prereg, SHA256SUMS_v2).

    scripts/prereg_c1.sh [--dry-run N] [--frozen DIR]      C1: one `vo ci` per selected fix commit, order_c1.tsv
    scripts/prereg_c2.sh [--dry-run N] [--frozen DIR]      C2: proof reuse along c2_seq_<lib>.txt

Both:
* check the frozen package (SHA256SUMS_v2 sha256 and every file of SHA256SUMS_v1/v2) before anything else;
* run veriforch from a frozen copy (R10; scripts/freeze_copy.sh, made at start unless --frozen names one) and
  record the pins at start in runs/prereg/C/pins.json (key c1 or c2): cirlean and equiv-lean with their commits,
  Lean, clang, the copy's manifest, the package's manifest. No re-pin during a run;
* refuse a real run unless the scheduler's cirlean has `--link` and equiv-lean is built against that same cirlean;
* give every `vo ci` run its own guard log (VO_GUARD_LOG): the run executes inside one outer run1.sh job, whose
  last `metered … core-s` line is the run's core-seconds (the outer guard meters the whole process tree);
* write one record per commit/step under runs/prereg/C/{c1,c2}/records/ and a JSON-lines summary.

C1 (procedure 1-3): for each commit c with first parent p, in order_c1.tsv order:
`vo ci <lib>_lib --base p --head c --attempts 0 --budget B --check-timeout 600`, with B = $0.50 × the number of
changed functions. The changed functions are counted before the run by a front-end pass (the same materialise +
build as `vo ci`, no Lean, no model). A revision that does not build is `blocked: build` (vo ci records it). Each
claimed verdict theorem is replayed with `lake env leanchecker` (scripts/kernel_replay.sh) in the certificate
package that built it. C1 stops when model $ + compute $ reach $350; the remaining commits are unattempted.

C2 (procedure 1-4): per library in the order jsmn, tiny-regex-c, cJSON: baseline `vo ci <lib>_lib --base S0
--head S0 --attempts 3 --no-equiv` (not counted), then `vo ci <lib>_lib --base S(k-1) --head S(k) --attempts 3
--no-equiv` for each consecutive pair, all in one run directory per library (each step uses the caches the previous
one left). Per step (R4): changed functions, head work (cached / rechecked / new:<origin>, split into without the
model (template, reuse, prev) and with it (llm)), regressions, model calls and $ (usage.jsonl rows added during the
step), core-seconds. C2 stops when model $ reach $150; the remaining steps are unattempted.

--dry-run N: check the package and the pins, then print the first N commands (C1: computing B with the front-end
pass for those commits; C2: the first N commands of each library). Nothing else runs and nothing is recorded.
"""
from __future__ import annotations

import argparse
import csv
import json
import os
import re
import socket
import subprocess
import sys
import time
from pathlib import Path

LIVE = Path(__file__).resolve().parents[1]
PKG = Path.home() / "fv_paper" / "prereg"
V2_SHA = "aaf302a17d6e21554832b6b151e47fc17c960f23d0a82dd22afd25b7ffed6b31"
C1B_SHA = "0a1ea0d5e0d14ed70d93e2f3bb4756036a62732087ac57882bb29aca0560ed93"   # SHA256SUMS_C1b_v1
# PREREG_C1b: the one recorded build fix, used only for the 7 commits blocked in pass 1 (runs/prereg/C1b/BUILDFIX.md)
C1B_BUILDFIX_ORDERS = {12, 14, 27, 46, 48, 53, 55}
C1B_BUILDFIX_TARGET = ("cjson_lib_c1b_buildfix", "targets/cjson_lib_c1b_buildfix.toml")
OUT = LIVE / "runs" / "prereg" / "C"
LIBS = {"cjson": ("cjson_lib", "targets/cjson_lib.toml"),
        "tiny-regex-c": ("tiny_regex_c_lib", "targets/tiny_regex_c_lib.toml"),
        "jsmn": ("jsmn_lib", "targets/jsmn_lib.toml")}
C2_ORDER = ["jsmn", "tiny-regex-c", "cjson"]
LEAN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"
CLANG = Path("/home/user/cirlean_work/toolchain/upstream-4955d32b/bin/clang")
COMPUTE_DOLLARS_PER_CORE_H = 0.04      # list price assumed in the feasibility note (<machine-type>/c3 rows, upper end)
STUDY = "c1"                            # c1, c2 or c1b (PREREG_C1b: pass 2 of C1's unknown and blocked commits)


def utc() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def sh(cmd: list[str], cwd: Path | None = None, timeout: int = 600, env: dict | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, env=env)


# ---------------------------------------------------------------------------------------------- package and pins
def check_package() -> str:
    got = sh(["sha256sum", str(PKG / "SHA256SUMS_v2")]).stdout.split()[0]
    if got != V2_SHA:
        raise SystemExit(f"SHA256SUMS_v2 sha256 {got} != frozen {V2_SHA}")
    mans = ["SHA256SUMS_v1", "SHA256SUMS_v2"]
    if STUDY == "c1b":
        g = sh(["sha256sum", str(PKG / "SHA256SUMS_C1b_v1")]).stdout.split()[0]
        if g != C1B_SHA:
            raise SystemExit(f"SHA256SUMS_C1b_v1 sha256 {g} != frozen {C1B_SHA}")
        mans.append("SHA256SUMS_C1b_v1")
    for man in mans:
        p = sh(["sha256sum", "--check", "--strict", man], cwd=PKG)
        if p.returncode != 0:
            raise SystemExit(f"{man}: files differ from the frozen package:\n{p.stdout[-2000:]}{p.stderr[-500:]}")
    return got


def cert_env(tree: Path) -> dict[str, str]:
    """The pins `vo ci` uses in a veriforch tree: its scripts/cert_pin.env, or the file VO_CERT_PIN_ENV names
    (as its scripts/vo sources them)."""
    f = Path(os.environ["VO_CERT_PIN_ENV"]) if os.environ.get("VO_CERT_PIN_ENV") else tree / "scripts" / "cert_pin.env"
    text = f.read_text().replace("$VO_ROOT", str(tree))
    env = {}
    for line in text.splitlines():
        m = re.match(r'^\s*([A-Z_]+)="?([^"#]*)"?\s*$', line)
        if m:
            env[m.group(1)] = m.group(2).strip()
    return env


def git_head(path: str) -> str | None:
    p = sh(["git", "-C", path, "rev-parse", "HEAD"])
    return p.stdout.strip() if p.returncode == 0 else None


def pins(frozen: Path, package_sha: str) -> tuple[dict, list[str]]:
    env = cert_env(frozen)
    problems = []
    cir, cert, eq = env.get("VO_CIRLEAN_DIR", ""), env.get("VO_CERT_CIRLEAN_DIR", ""), env.get("VO_EQUIVLEAN_DIR", "")
    c2l = Path(cir) / ".lake/build/bin/cir2lean"
    hp = sh([str(c2l)]) if c2l.exists() else None
    helptext = (hp.stderr + hp.stdout) if hp else ""
    if "--link" not in helptext:
        problems.append(f"the scheduler's cirlean {cir} has no `cir2lean --link` (C needs >= 88e6008)")
    if Path(cir).resolve() != Path(cert).resolve():
        problems.append(f"scheduler cirlean {cir} != certificate cirlean {cert}")
    lf = Path(eq) / "lakefile.toml"
    req = re.search(r'name\s*=\s*"cirlean"\s*\npath\s*=\s*"([^"]+)"', lf.read_text()) if lf.exists() else None
    if req is None or (Path(eq) / req.group(1)).resolve() != Path(cert).resolve():
        problems.append(f"equiv-lean {eq} is not built against {cert} (lakefile cirlean path: "
                        f"{req.group(1) if req else 'none'})")
    man = frozen / "SHA256SUMS"
    d = {
        "started": utc(), "host": socket.gethostname(),
        "prereg_package": {"dir": str(PKG), "SHA256SUMS_v2": package_sha},
        "pin_env": os.environ.get("VO_CERT_PIN_ENV") or str(frozen / "scripts" / "cert_pin.env"),
        "veriforch": {"frozen_copy": str(frozen),
                      "manifest_sha256": sh(["sha256sum", str(man)]).stdout.split()[0] if man.exists() else None},
        "cirlean": {"dir": cir, "pin": env.get("VO_CIRLEAN_PIN"), "commit": git_head(cir)},
        "cert_cirlean": {"dir": cert, "pin": env.get("VO_CERT_CIRLEAN_PIN"), "commit": git_head(cert)},
        "equivlean": {"dir": eq, "pin": env.get("VO_EQUIVLEAN_PIN"), "commit": git_head(eq),
                      "lakefile_cirlean_path": req.group(1) if req else None},
        "lean": sh([str(LEAN), "--version"]).stdout.strip(),
        "clang": (sh([str(CLANG), "--version"]).stdout.splitlines() or [""])[0],
        "repos": {lib: {"root": root, "head": git_head(root)} for lib, root in
                  (("cjson", "/home/user/veriforch/targets/cjson_src/cJSON"),
                   ("tiny-regex-c", "/home/user/veriforch/targets/tiny-regex-c"),
                   ("jsmn", "/home/user/veriforch/targets/jsmn"))},
        "problems": problems,
    }
    return d, problems


def record_pins(study: str, d: dict) -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    p = OUT / "pins.json"
    allp = json.loads(p.read_text()) if p.exists() else {}
    if study in allp:
        raise SystemExit(f"{p} already has pins for {study} (a run already started; no re-pin during a run)")
    allp[study] = d
    p.write_text(json.dumps(allp, indent=1))


def frozen_copy(arg: str | None, dry: bool) -> Path:
    if arg:
        f = Path(arg).resolve()
        p = sh(["sha256sum", "--check", "--strict", "--quiet", "SHA256SUMS"], cwd=f)
        if p.returncode != 0:
            raise SystemExit(f"frozen copy {f} does not match its manifest:\n{p.stdout[-1500:]}")
        return f
    if dry:
        return LIVE
    dest = Path.home() / "veriforch_frozen" / f"C_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}"
    p = sh([str(LIVE / "scripts" / "freeze_copy.sh"), str(dest)])
    if p.returncode != 0:
        raise SystemExit(f"freeze_copy failed: {p.stdout}{p.stderr}")
    print(p.stdout.strip(), flush=True)
    return dest


# ---------------------------------------------------------------------------------------------- shared run helpers
def vo_env(run_dir: Path, guard_log: Path) -> dict:
    env = dict(os.environ)
    env.update({"VO_CI_RUN_DIR": str(run_dir), "VO_GUARD_LOG": str(guard_log)})
    for k in ("VO_CIRLEAN_DIR", "VO_CIRLEAN_PIN", "VO_ROOT", "PYTHONPATH"):
        env.pop(k, None)            # scripts/vo sets them (pins from cert_pin.env, VO_ROOT = the frozen copy)
    return env


def vo_ci_cmd(frozen: Path, target: str, base: str, head: str, extra: list[str], core_h_cap: float,
              wall: int) -> list[str]:
    """`vo ci` inside one outer run1.sh job (the whole run's core-seconds in its guard log)."""
    return [str(frozen / "scripts" / "run1.sh"), "-t", str(wall), "-m", "128", "-c", str(core_h_cap), "--",
            str(frozen / "scripts" / "vo"), "ci", str(frozen / target), "--base", base, "--head", head, *extra]


def core_seconds(guard_log: Path) -> float | None:
    """The outer job's final metering: the last `metered X core-s` line of the run's own guard log."""
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


def rev(repo: str, r: str) -> str:
    p = sh(["git", "-C", repo, "rev-parse", r])
    if p.returncode != 0:
        raise SystemExit(f"git rev-parse {r} in {repo}: {p.stderr}")
    return p.stdout.strip()


# ---------------------------------------------------------------------------------------------- C1
def changed_functions(frozen: Path, target_path: str, base: str, head: str, scratch: Path) -> tuple[int | None, str]:
    """Front-end pass (materialise + build of both revisions, as `vo ci` does; no Lean, no model): the number of
    changed functions, or None with the error when a revision does not build."""
    code = f"""
import json, sys
from pathlib import Path
from veriforch.config import load_target
from veriforch.ci import materialise
from veriforch.adapters.cir.adapter import CirAdapter
t = load_target({str(frozen / target_path)!r}); rd = Path({str(scratch)!r}); ad = CirAdapter()
units = []
for r in ({base!r}, {head!r}):
    tr = materialise(t, r, rd)
    try:
        b = ad.build(tr, tr.variants[0], rd)
    except Exception as e:
        print(json.dumps({{"error": f"{{r}}: {{type(e).__name__}}: {{e}}"[-2000:]}})); sys.exit(0)
    units.append({{u.name: u.body_hash for u in b.units}})
ub, uh = units
print(json.dumps({{"changed": sorted(n for n in uh if n in ub and uh[n] != ub[n])}}))
"""
    env = vo_env(scratch, scratch / "prepass.guard.log")
    env.update({"VO_ROOT": str(frozen), "PYTHONPATH": str(frozen / "orch")})
    ce = cert_env(frozen)
    env.update({"VO_CIRLEAN_DIR": ce["VO_CIRLEAN_DIR"], "VO_CIRLEAN_PIN": ce["VO_CIRLEAN_PIN"]})
    p = sh([str(frozen / ".venv" / "bin" / "python"), "-B", "-c", code], timeout=3600, env=env)
    try:
        d = json.loads(p.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        return None, f"front-end pass failed: {p.stdout[-800:]}{p.stderr[-1500:]}"
    if "error" in d:
        return None, d["error"]
    return len(d["changed"]), ",".join(d["changed"])


def commit_outcome(verdicts: list[dict], blocked: bool) -> str:
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


LOAD_MAX = 320.0               # the coordinating session's main-VM rule: no dispatch while the 1-min load is above this
FREE_SLOTS = 0                 # C1b: commits that may run whatever the load (the coordinating session 10-24: 3 guaranteed for veriforch
                               # overall, held by C2 and D while they run); the RAM guard always applies
MEM_MIN = 150e9                # ... or while MemAvailable is below 150 GB


def resource_wait(log, in_flight: int = 0) -> None:
    """Before every dispatch: wait while the 1-minute load average > 320 or MemAvailable < 150 GB (every wait is
    logged when it starts, every 5 minutes while it lasts, and when it ends)."""
    t0, last = time.time(), 0.0
    while True:
        load1 = float(Path("/proc/loadavg").read_text().split()[0])
        avail = next(int(x.split()[1]) for x in open("/proc/meminfo") if x.startswith("MemAvailable:")) * 1024
        if (load1 <= LOAD_MAX or in_flight < FREE_SLOTS) and avail >= MEM_MIN:
            if last:
                log(f"resource wait over after {time.time() - t0:.0f} s (load {load1:.0f}, "
                    f"MemAvailable {avail / 1e9:.0f} GB)")
            return
        if time.time() - last >= 300:
            log(f"resource wait: load {load1:.0f} (dispatch at <= {LOAD_MAX:.0f}), MemAvailable {avail / 1e9:.0f} GB "
                f"(dispatch at >= {MEM_MIN / 1e9:.0f})")
            last = time.time()
        time.sleep(30)


def c1_rows(args) -> list[dict]:
    order = Path(args.order_file) if args.order_file else PKG / "C" / "order_c1.tsv"
    rows = list(csv.DictReader(open(order), delimiter="\t"))
    if STUDY == "c1b":
        # PREREG_C1b units (C1b/units_c1b.tsv), processed in C1's order (C/order_c1.tsv)
        units = {r["order"] for r in csv.DictReader(open(PKG / "C1b" / "units_c1b.tsv"), delimiter="\t")}
        rows = [r for r in rows if r["order"] in units]
        if len(rows) != len(units):
            raise SystemExit(f"C1b: {len(units)} units, {len(rows)} found in order_c1.tsv")
    return rows


def c1_libs(args) -> dict[str, tuple[str, str]]:
    """library -> (run name, target file relative to the veriforch tree); --target LIB=FILE adds or replaces one
    (tests on repositories outside the pre-registered sets)."""
    libs = dict(LIBS)
    for spec in args.target or []:
        lib, path = spec.split("=", 1)
        libs[lib] = (Path(path).stem, path)
    return libs


def repo_root(tree: Path, target: str) -> str:
    import tomllib
    return tomllib.loads((tree / target).read_text())["root"]


def run_dir_for_commit(base: Path, tag: str, name: str) -> Path:
    """A run directory of the commit's own (no two workers ever build in one). An earlier attempt's directory (a
    crash) is kept under <tag>.crash_<UTC>. The content-addressed .olean caches (atomic stores: lean.py) are
    shared per library through symlinks; proof, negative and by-body caches stay per commit."""
    rd = base / "runs" / tag
    if rd.exists():
        rd.rename(rd.with_name(f"{tag}.crash_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}"))
    (rd / "cache").mkdir(parents=True)
    for c in ("olean", "olean_cert"):
        shared = base / name / "cache" / c
        shared.mkdir(parents=True, exist_ok=True)
        (rd / "cache" / c).symlink_to(shared)
    return rd


def c1_commit(frozen: Path, d: dict, base: Path, r: dict, lib: str, name: str, target: str, p: str, c: str,
              prepass: dict, worker: int, dispatched_at: str) -> dict:
    """One commit's procedure after its pre-pass: vo ci in its own run directory, verdicts, kernel replay of every
    claimed verdict theorem, outcome, record (same format as the sequential driver, plus worker / dispatched_at)."""
    tag = f"{int(r['order']):02d}_{c[:12]}"
    rec = {"order": int(r["order"]), "library": lib, "commit": c, "parent": p, "subject": r["subject"],
           "started": utc(), "worker": worker, "dispatched_at": dispatched_at, **prepass}
    if STUDY == "c1b":
        rec.update(study="c1b", **{"pass": 2}, target=target)
    budget = rec["budget"]
    run_dir = run_dir_for_commit(base, tag, name)
    glog = base / "guard" / f"{tag}.log"
    for old in (glog, base / "logs" / f"{tag}.log"):
        if old.exists():                    # an earlier (crashed) attempt's log: kept beside the new one
            old.rename(old.with_name(old.name + f".crash_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}"))
    rows_before = len(usage_rows(run_dir))
    cmd = vo_ci_cmd(frozen, target, p, c, ["--attempts", "0", "--budget", f"{budget:.2f}",
                                           "--check-timeout", "600"], 8.0, 6 * 3600)
    rec["command"] = " ".join(cmd)
    t0 = time.time()
    with open(base / "logs" / f"{tag}.log", "w") as lf:
        proc = subprocess.run(cmd, stdout=lf, stderr=subprocess.STDOUT, env=vo_env(run_dir, glog))
    rec.update(exit=proc.returncode, seconds=round(time.time() - t0, 1), core_seconds=core_seconds(glog))
    new_rows = usage_rows(run_dir)[rows_before:]
    rec.update(model_calls=len(new_rows), model_dollars=round(sum(x.get("dollars", 0) for x in new_rows), 4))
    ci = run_dir / "ci" / f"{p}..{c}" / "ci.json"
    verdicts, blocked = [], False
    if ci.exists():
        rep = json.loads(ci.read_text())
        for vn, vr in rep["variants"].items():
            if vr.get("blocked"):
                blocked = True
                rec["blocked"] = {"revision": vr["revision"], "error": vr["error"][-2000:]}
            for u in vr.get("units", []):
                if not u.get("changed"):
                    continue
                v = dict(u.get("equivalence") or {"verdict": "unknown", "detail": "no verdict recorded"})
                v["unit"] = u["unit"]
                if v.get("verdict") in ("equivalent", "changed_only_where_old_unsafe") and v.get("module"):
                    eqdir = d["equivlean"]["dir"]
                    kr = sh([str(frozen / "scripts" / "kernel_replay.sh"), "--extra-lean-path",
                             f"{eqdir}/.lake/build/lib/lean", "--log-dir", str(base / "replay" / tag),
                             str(run_dir / "lean_cert"), v["module"]], timeout=7200,
                            env=vo_env(run_dir, glog))
                    v["kernel_replay"] = kr.stdout.strip()
                    v["kernel_verdict"] = v["verdict"] if kr.returncode == 0 else None
                verdicts.append(v)
    else:
        rec["error"] = "no ci.json (see the log)"
    rec["verdicts"] = verdicts
    # a run that ended without ci.json crashed: not a verdict; re-run after a crash fix (PREREG_C_v2 "Tool pins")
    rec["outcome"] = "crash" if "error" in rec else commit_outcome(verdicts, blocked)
    rec["finished"] = utc()
    (base / "records" / f"{tag}.json").write_text(json.dumps(rec, indent=1))
    return rec


def spend_of(rec: dict) -> float:
    if STUDY == "c1b":
        return rec.get("model_dollars") or 0.0
    return (rec.get("model_dollars") or 0.0) + (rec.get("core_seconds") or 0.0) / 3600 * COMPUTE_DOLLARS_PER_CORE_H


def resume_pins(d: dict, workers: int, write: bool = True) -> None:
    """--resume: the tool pins must be the ones recorded when C1 started (no re-pin during a run); the resumption
    (frozen copy, its manifest, workers) is appended to the c1 pins (not with write=False: dry runs)."""
    p = OUT / "pins.json"
    allp = json.loads(p.read_text()) if p.exists() else {}
    if STUDY not in allp:
        raise SystemExit(f"--resume: no {STUDY} pins in {p}")
    old = allp[STUDY]
    def same(k, f):
        return (old.get(k) or {}).get(f) == (d.get(k) or {}).get(f)
    bad = [f"{k}.{f}" for k, f in (("cirlean", "commit"), ("cert_cirlean", "commit"), ("equivlean", "commit"),
                                   ("prereg_package", "SHA256SUMS_v2")) if not same(k, f)]
    bad += [k for k in ("lean", "clang") if old.get(k) != d.get(k)]
    if bad:
        raise SystemExit(f"--resume: pins differ from the recorded c1 pins in {bad} (no re-pin during a run)")
    if not write:
        print("--resume: the tool pins equal the recorded c1 pins (cirlean, certificate cirlean, equiv-lean, "
              "package, Lean, clang)")
        return
    old.setdefault("resumed", []).append({"at": utc(), "frozen_copy": d["veriforch"]["frozen_copy"],
                                          "manifest_sha256": d["veriforch"]["manifest_sha256"], "workers": workers})
    p.write_text(json.dumps(allp, indent=1))


def run_c1(args) -> int:
    from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
    global OUT
    if args.out:
        OUT = Path(args.out).resolve()
    pkg_sha = check_package()
    frozen = frozen_copy(args.frozen, args.dry_run is not None)
    d, problems = pins(frozen, pkg_sha)
    rows = c1_rows(args)
    libs = c1_libs(args)
    base = OUT / STUDY
    workers = max(1, args.workers)

    def log(msg: str) -> None:
        print(f"{utc()} {msg}", flush=True)

    def existing(tag: str) -> dict | None:
        f = base / "records" / f"{tag}.json"
        return json.loads(f.read_text()) if f.exists() else None

    plan = []                       # (row, lib, name, target, p, c, tag) in the order of the order file
    for r in rows:
        lib = r["library"]
        name, target = libs[lib]
        if STUDY == "c1b" and int(r["order"]) in C1B_BUILDFIX_ORDERS:
            name, target = C1B_BUILDFIX_TARGET
        repo = repo_root(frozen, target)
        c = rev(repo, r["commit"])
        p = rev(repo, c + "^1")
        tag = f"{int(r['order']):02d}_{c[:12]}"
        old = existing(tag) if args.resume else None
        if old is not None and old.get("outcome") != "crash":
            continue                # done (or reported unattempted) in an earlier run
        plan.append((r, lib, name, target, p, c, tag))
    if args.dry_run is not None:
        print(json.dumps(d, indent=1))
        if problems:
            print("NOTE (a real run would refuse to start):\n  " + "\n  ".join(problems))
        if args.resume:
            resume_pins(d, workers, write=False)
        scratch = LIVE / "scratch" / "prereg" / "c1_dryrun"
        load1 = float(Path("/proc/loadavg").read_text().split()[0])
        avail = next(int(x.split()[1]) for x in open("/proc/meminfo") if x.startswith("MemAvailable:")) * 1024
        print(f"\n# {len(plan)} commits to dispatch, {workers} workers; resource gate now: load {load1:.0f} "
              f"(<= {LOAD_MAX:.0f}), MemAvailable {avail / 1e9:.0f} GB (>= {MEM_MIN / 1e9:.0f})")
        inflight = 0.0
        for k, (r, lib, name, target, p, c, tag) in enumerate(plan[:args.dry_run]):
            n, why = changed_functions(frozen, target, p, c, scratch / name)
            budget = 0.0 if n is None else 0.5 * n
            slot = k + 1 if k < workers else "next free"
            glog = base / "guard" / f"{tag}.log"
            cmd = vo_ci_cmd(frozen, target, p, c, ["--attempts", "0", "--budget", f"{budget:.2f}",
                                                   "--check-timeout", "600"], 8.0, 6 * 3600)
            print(f"\n# dispatch {k + 1}: order {r['order']} {lib} {c[:12]} -> worker {slot}; changed functions "
                  f"{n if n is not None else 'none (blocked: build)'} [{why[:160]}]; B ${budget:.2f}; "
                  f"in-flight B before it ${inflight:.2f}")
            print(f"VO_CI_RUN_DIR={base / 'runs' / tag} VO_GUARD_LOG={glog} " + " ".join(cmd))
            inflight += budget if k < workers else 0.0
        return 0
    if problems:
        raise SystemExit("refusing to start C1:\n  " + "\n  ".join(problems))
    if args.resume:
        resume_pins(d, workers)
    else:
        record_pins(STUDY, d)
    for sub in ("records", "logs", "guard", "runs"):
        (base / sub).mkdir(parents=True, exist_ok=True)
    summary = base / f"{STUDY}_results.jsonl"
    # spend so far: every record of this study, crashed attempts included (C1 total <= $350, compute included)
    spent = sum(spend_of(json.loads(f.read_text())) for f in (base / "records").glob("*.json*")
                if f.is_file() and not f.name.endswith(".tmp"))
    log(f"{STUDY.upper()}: {len(plan)} commits to dispatch with {workers} workers; spent so far ${spent:.2f}")
    free = list(range(1, workers + 1))
    inflight: dict = {}            # future -> (tag, B, worker)

    def collect(futs) -> None:
        nonlocal spent
        for fut in futs:
            tag, b, w = inflight.pop(fut)
            free.append(w)
            free.sort()
            try:
                rec = fut.result()
            except Exception as e:          # a driver failure is a crash of this commit: --resume re-runs it
                rec = {"order": int(tag.split("_")[0]), "library": "?", "commit": tag.split("_", 1)[1],
                       "outcome": "crash", "error": f"driver: {type(e).__name__}: {e}"[-2000:], "worker": w,
                       "finished": utc()}
                prev = base / "records" / f"{tag}.json"
                prev.write_text(json.dumps(rec, indent=1))
            spent += spend_of(rec)
            with open(summary, "a") as f:
                f.write(json.dumps({k: rec.get(k) for k in ("order", "library", "commit", "outcome", "budget",
                                                            "model_dollars", "core_seconds")}) + "\n")
            log(f"{STUDY.upper()} {tag} (worker {w}): {rec['outcome']} (${rec.get('model_dollars')}, {rec.get('core_seconds')} "
                f"core-s); spent ${spent:.2f}")

    with ThreadPoolExecutor(max_workers=workers) as ex:
        for k, (r, lib, name, target, p, c, tag) in enumerate(plan):
            while len(inflight) >= workers:
                done, _ = wait(list(inflight), return_when=FIRST_COMPLETED)
                collect(done)
            resource_wait(log, len(inflight))
            collect([f for f in list(inflight) if f.done()])
            committed = spent + sum(b for _, b, _ in inflight.values())
            if committed >= 350.0:
                log(f"{STUDY.upper()} budget: spent ${spent:.2f} + in-flight B ${committed - spent:.2f} >= $350: "
                    f"{len(plan) - k} commits unattempted")
                for (r2, lib2, name2, target2, p2, c2, tag2) in plan[k:]:
                    rec = {"order": int(r2["order"]), "library": lib2, "commit": c2, "parent": p2,
                           "subject": r2["subject"], "started": utc(), "outcome": "unattempted",
                           "reason": f"{STUDY.upper()} budget spent (${spent:.2f} + in-flight B ${committed - spent:.2f} of $350)"}
                    (base / "records" / f"{tag2}.json").write_text(json.dumps(rec, indent=1))
                    with open(summary, "a") as f:
                        f.write(json.dumps({k2: rec.get(k2) for k2 in ("order", "library", "commit", "outcome",
                                                                       "budget", "model_dollars", "core_seconds")})
                                + "\n")
                break
            old = base / "records" / f"{tag}.json"
            if old.exists():                # a crashed attempt (--resume): its record is kept beside the new one
                old.rename(old.with_name(f"{tag}.json.crash_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}"))
            # the dispatcher runs the pre-passes one at a time, in a directory of their own (not the sequential
            # driver's base/prepass, which may still be in use while the switch happens)
            n, why = changed_functions(frozen, target, p, c, base / "prepass_dispatch" / name)
            budget = 0.0 if n is None else 0.5 * n
            prepass = {"changed_count_before": n, "changed_before": why if n is not None else None,
                       "prepass_error": None if n is not None else why, "budget": budget}
            w = free.pop(0)
            fut = ex.submit(c1_commit, frozen, d, base, r, lib, name, target, p, c, prepass, w, utc())
            inflight[fut] = (tag, budget, w)
            log(f"{STUDY.upper()} dispatch {tag} -> worker {w} (B ${budget:.2f}; in flight {len(inflight)})")
        while inflight:
            done, _ = wait(list(inflight), return_when=FIRST_COMPLETED)
            collect(done)
    log(f"{STUDY.upper()} done")
    return 0


# ---------------------------------------------------------------------------------------------- C2
def head_work(rep: dict) -> dict:
    out = {"changed": 0, "cached": 0, "rechecked": 0, "new_without_model": 0, "new_with_model": 0,
           "new_by_origin": {}, "regressions": 0, "failed": 0}
    for vn, vr in rep["variants"].items():
        out["changed"] += len(vr.get("changed", []))
        for u in vr.get("units", []):
            w = u.get("head_work", "-")
            out["regressions"] += bool(u.get("regression"))
            if w == "cached":
                out["cached"] += 1
            elif w == "rechecked":
                out["rechecked"] += 1
            elif w.startswith("new:"):
                o = w.split(":", 1)[1]
                out["new_by_origin"][o] = out["new_by_origin"].get(o, 0) + 1
                out["new_with_model" if o == "llm" else "new_without_model"] += 1
            elif w == "failed":
                out["failed"] += 1
    return out


def run_c2(args) -> int:
    pkg_sha = check_package()
    frozen = frozen_copy(args.frozen, args.dry_run is not None)
    d, problems = pins(frozen, pkg_sha)
    # C2 runs with --no-equiv: equiv-lean is not used, so only the scheduler's cirlean must have --link
    problems = [x for x in problems if "--link" in x]
    seqs = {lib: [x.strip() for x in (PKG / "C" / f"c2_seq_{lib}.txt").read_text().split() if x.strip()]
            for lib in C2_ORDER}
    if args.dry_run is not None:
        print(json.dumps(d, indent=1))
        if problems:
            print("NOTE (a real run would refuse to start):\n  " + "\n  ".join(problems))
        for lib in C2_ORDER:
            name, target = LIBS[lib]
            s = seqs[lib]
            pairs = [(s[0], s[0])] + list(zip(s, s[1:]))
            for k, (b, h) in enumerate(pairs[:args.dry_run]):
                glog = OUT / "c2" / "guard" / f"{name}_{k:02d}.log"
                cmd = vo_ci_cmd(frozen, target, b, h, ["--attempts", "3", "--no-equiv", "--budget", "<remaining of $150>"],
                                12.0, 12 * 3600)
                print(f"\n# {lib} {'baseline' if k == 0 else f'step {k}'}: {b[:12]}..{h[:12]}")
                print(f"VO_CI_RUN_DIR={OUT / 'c2' / name} VO_GUARD_LOG={glog} " + " ".join(cmd))
        return 0
    if problems:
        raise SystemExit("refusing to start C2:\n  " + "\n  ".join(problems))
    record_pins("c2", d)
    base = OUT / "c2"
    for sub in ("records", "logs", "guard"):
        (base / sub).mkdir(parents=True, exist_ok=True)
    spent = 0.0
    summary = base / "c2_results.jsonl"
    for lib in C2_ORDER:
        name, target = LIBS[lib]
        run_dir = base / name
        s = seqs[lib]
        pairs = [(s[0], s[0])] + list(zip(s, s[1:]))
        for k, (b, h) in enumerate(pairs):
            tag = f"{name}_{k:02d}"
            rec = {"library": lib, "step": k, "baseline": k == 0, "base": b, "head": h, "started": utc()}
            remaining = 150.0 - spent
            if remaining <= 0:
                rec.update(outcome="unattempted", reason=f"C2 budget spent (${spent:.2f} of $150)")
            else:
                glog = base / "guard" / f"{tag}.log"
                rows_before = len(usage_rows(run_dir))
                cmd = vo_ci_cmd(frozen, target, b, h, ["--attempts", "3", "--no-equiv", "--budget",
                                                       f"{remaining:.2f}"], 12.0, 12 * 3600)
                rec["command"] = " ".join(cmd)
                t0 = time.time()
                with open(base / "logs" / f"{tag}.log", "w") as lf:
                    proc = subprocess.run(cmd, stdout=lf, stderr=subprocess.STDOUT, env=vo_env(run_dir, glog))
                rec.update(exit=proc.returncode, seconds=round(time.time() - t0, 1), core_seconds=core_seconds(glog))
                new_rows = usage_rows(run_dir)[rows_before:]
                rec.update(model_calls=len(new_rows),
                           model_dollars=round(sum(x.get("dollars", 0) for x in new_rows), 4))
                spent += rec["model_dollars"]
                ci = run_dir / "ci" / f"{b}..{h}" / "ci.json"
                if ci.exists():
                    rep = json.loads(ci.read_text())
                    rec.update(head_work(rep))
                    rec["blocked_build"] = rep.get("blocked_build", 0)
                    rec["ci_json"] = str(ci)
                else:
                    rec["error"] = "no ci.json (see the log)"
                    rec["outcome"] = "crash"     # re-run after a crash fix
            rec["finished"] = utc()
            (base / "records" / f"{tag}.json").write_text(json.dumps(rec, indent=1))
            with open(summary, "a") as f:
                f.write(json.dumps(rec) + "\n")
            print(f"{utc()} C2 {tag}: {rec.get('outcome', 'done')} ${rec.get('model_dollars', 0)} "
                  f"cached {rec.get('cached', '-')} rechecked {rec.get('rechecked', '-')}", flush=True)
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("study", choices=["c1", "c2", "c1b"])
    ap.add_argument("--dry-run", type=int, default=None, metavar="N")
    ap.add_argument("--frozen", default=None, help="an existing frozen copy (scripts/freeze_copy.sh)")
    ap.add_argument("--workers", type=int, default=1, help="C1: commits run concurrently (default 1: one at a time)")
    ap.add_argument("--resume", action="store_true",
                    help="C1: skip commits whose record has an outcome other than crash; re-dispatch the rest")
    # tests on repositories outside the pre-registered sets (never for the real run)
    ap.add_argument("--order-file", default=None, help=argparse.SUPPRESS)
    ap.add_argument("--target", action="append", help=argparse.SUPPRESS)
    ap.add_argument("--out", default=None, help=argparse.SUPPRESS)
    ap.add_argument("--load-max", type=float, default=None,
                    help="1-min load above which no commit is dispatched (C1/C2: 320; C1b: 450, the coordinating session 10-24)")
    ap.add_argument("--free-slots", type=int, default=0,
                    help="C1b: commits that may run whatever the load (the RAM guard still applies)")
    a = ap.parse_args()
    global STUDY, OUT, LOAD_MAX, FREE_SLOTS
    STUDY = a.study
    if a.study == "c1b":
        OUT = LIVE / "runs" / "prereg" / "C1b"
        LOAD_MAX = 450.0
    if a.load_max is not None:
        LOAD_MAX = a.load_max
    FREE_SLOTS = a.free_slots
    return run_c1(a) if a.study in ("c1", "c1b") else run_c2(a)


if __name__ == "__main__":
    sys.exit(main())

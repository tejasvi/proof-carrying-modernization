"""Lean checking with a content-addressed .olean cache.

A generated Lake package (`runs/<name>/lean/`) requires a pinned bridge. Bridge libraries are built once
with `lake build`; generated modules are checked by calling `lean` directly with the package's LEAN_PATH,
so concurrent checks never wait on Lake's lock and the cache is under our control: a module's key is
sha256(lean version, bridge pin, source, keys of the generated modules it imports).
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

from .model import LeanMessage, ObligationResult, read_json, sha256, write_json

VO_ROOT = Path(os.environ.get("VO_ROOT", "/home/user/veriforch"))
RUN1 = VO_ROOT / "scripts" / "run1.sh"
TOOLCHAIN = "leanprover/lean4:v4.35.0"
LEAN_BIN = Path.home() / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean"
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


@dataclass
class Requirement:
    name: str
    path: str          # absolute path of the pinned bridge package
    pin: str           # commit or snapshot label (part of every cache key)
    libs: list[str] = field(default_factory=list)   # libraries of the bridge to build (e.g. ["CIR"])


class LeanPackage:
    def __init__(self, pkg_dir: Path, name: str, requires: list[Requirement], libs: list[str],
                 cache_dir: Path, extra_lean_path: list[str] | None = None, mem_gib: int = 32):
        self.dir = Path(pkg_dir)
        self.name = name
        self.requires = requires
        self.libs = libs
        self.cache_dir = Path(cache_dir)
        self._lean_path: str | None = None
        self.extra_lean_path = list(extra_lean_path or [])   # e.g. equiv-lean's build dir for certificates
        self.mem_gib = mem_gib                                 # default address-space cap of checks (GiB)
        self.pin = ";".join(f"{r.name}@{r.pin}" for r in requires)

    # -- package setup -------------------------------------------------------------------------
    def ensure(self) -> None:
        """Write the lakefile and build the bridge libraries (once; Lake skips up-to-date work)."""
        self.dir.mkdir(parents=True, exist_ok=True)
        lines = [f'name = "{self.name}"', f'defaultTargets = {json.dumps(self.libs)}', "",
                 "[leanOptions]", "autoImplicit = false", ""]
        for r in self.requires:
            lines += ["[[require]]", f'name = "{r.name}"', f'path = "{r.path}"', ""]
        for lib in self.libs:
            lines += ["[[lean_lib]]", f'name = "{lib}"', ""]
        text = "\n".join(lines)
        lf = self.dir / "lakefile.toml"
        if not lf.exists() or lf.read_text() != text:
            lf.write_text(text)
            # Lake keeps resolved dependency paths in the manifest: a re-pinned bridge path is ignored
            # unless the manifest is regenerated
            man = self.dir / "lake-manifest.json"
            if man.exists():
                man.unlink()
            self._lean_path = None
        (self.dir / "lean-toolchain").write_text(TOOLCHAIN + "\n")
        stamp = self.dir / ".vo_bridges_built"
        want = self.pin
        if not stamp.exists() or stamp.read_text() != want:
            targets = [lib for r in self.requires for lib in r.libs]
            proc = _run([str(RUN1), "-t", "1800", "-c", "0.6", "--", "lake", "build", *targets],
                        cwd=self.dir, timeout=1900)
            if proc.returncode != 0:
                raise RuntimeError(f"lake build {targets} failed:\n{proc.stdout[-3000:]}")
            stamp.write_text(want)

    def lean_path(self) -> str:
        if self._lean_path is None:
            proc = _run(["lake", "env", "printenv", "LEAN_PATH"], cwd=self.dir, timeout=300)
            if proc.returncode != 0:
                raise RuntimeError(f"lake env failed: {proc.stdout[-2000:]}")
            lp = proc.stdout.strip().splitlines()[-1]
            # compare resolved paths: a frozen copy reaches deps/ through a symlink, lake reports the target
            entries = {str(Path(e).resolve()) for e in lp.split(":") if e}
            for r in self.requires:
                if str((Path(r.path) / ".lake/build/lib/lean").resolve()) not in entries:
                    raise RuntimeError(f"LEAN_PATH does not use the pinned {r.name} at {r.path}: {lp}")
            self._lean_path = ":".join([lp] + self.extra_lean_path)
        return self._lean_path

    # -- paths ---------------------------------------------------------------------------------
    def src(self, mod: str) -> Path:
        return self.dir / (mod.replace(".", "/") + ".lean")

    def olean(self, mod: str) -> Path:
        return self.dir / ".lake/build/lib/lean" / (mod.replace(".", "/") + ".olean")

    def ilean(self, mod: str) -> Path:
        return self.olean(mod).with_suffix(".ilean")

    # -- checking ------------------------------------------------------------------------------
    def bridge_fingerprint(self) -> str:
        """sha256 over the built root .olean of every required library: the cache key must follow the bridge
        that is actually on LEAN_PATH, not only the pin label (a stale manifest once made them differ)."""
        if getattr(self, "_fp", None) is None:
            h = []
            for r in self.requires:
                base = Path(r.path) / ".lake/build/lib/lean"
                for lib in r.libs:
                    root = base / (lib.replace(".", "/") + ".olean")
                    files = ([root] if root.exists() else []) + sorted((base / lib.replace(".", "/")).rglob("*.olean"))
                    h.append(sha256(b"".join(f.relative_to(base).as_posix().encode() + f.read_bytes() for f in files))
                             if files else f"missing:{root}")
            self._fp = sha256("|".join(h))
        return self._fp

    def key(self, source: str, import_keys: dict[str, str]) -> str:
        parts = [TOOLCHAIN, self.pin, self.bridge_fingerprint(), ";".join(self.extra_lean_path), source] + \
            [f"{m}={k}" for m, k in sorted(import_keys.items())]
        return sha256("\n".join(parts))

    def check(self, mod: str, source: str, import_keys: dict[str, str] | None = None, *,
              timeout: int = 600, mem_gib: int | None = None, core_h: float = 0.25,
              use_cache: bool = True) -> ObligationResult:
        """Check one module. On success its .olean is in place for importers and stored in the cache."""
        import_keys = import_keys or {}
        key = self.key(source, import_keys)
        cdir = self.cache_dir / key[:2] / key
        path = self.src(mod)
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_text() != source:
            path.write_text(source)
        if use_cache and (cdir / "result.json").exists() and (cdir / "m.olean").exists():
            res = ObligationResult.from_json(read_json(cdir / "result.json"))
            self.olean(mod).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(cdir / "m.olean", self.olean(mod))
            if (cdir / "m.ilean").exists():
                shutil.copyfile(cdir / "m.ilean", self.ilean(mod))
            res.status = "cached"
            res.cache_key = key
            return res
        self.olean(mod).parent.mkdir(parents=True, exist_ok=True)
        for p in (self.olean(mod), self.ilean(mod)):
            if p.exists():
                p.unlink()
        # one lean thread (-j 1): the wall clock bounds the check, so the core-hour cap must not stop it earlier
        # (a 0.25 core-h cap killed 3600 s concrete test runs at ~900 s)
        core_h = max(core_h, 1.25 * timeout / 3600)
        cmd = [str(RUN1), "-t", str(timeout), "-m", str(mem_gib or self.mem_gib), "-c", str(core_h),
               "-l", str(self.dir.parent / "guard.log"), "--",
               "env", f"LEAN_PATH={self.lean_path()}", str(LEAN_BIN), "-R", str(self.dir),
               "-o", str(self.olean(mod)), "-i", str(self.ilean(mod)), "--json", "-j", "1",
               "-DElab.async=false", str(path)]
        t0 = time.time()
        proc = _run(cmd, cwd=self.dir, timeout=timeout + 60)
        dt = time.time() - t0
        res = parse_messages(proc.stdout)
        res.seconds = round(dt, 2)
        res.cache_key = key
        if proc.returncode in (124, 137) or (proc.returncode != 0 and not res.messages):
            res.status = "timeout" if proc.returncode in (124, 137) else "error"
            if not res.errors:
                res.errors.append(f"lean exited {proc.returncode}: {proc.stdout[-1500:]}")
        # success needs lean's exit 0 AND the .olean: a run killed or crashed after printing only warnings (an
        # out-of-memory abort under ulimit -v) parses as "no errors" but proves nothing (seen 10-25 on a 1891 s check)
        if res.ok and proc.returncode != 0:
            res.status = "error"
            res.errors.append(f"lean exited {proc.returncode} without an error message (killed or crashed): "
                              f"{proc.stdout[-800:]}")
        if res.ok and not self.olean(mod).exists():
            res.status = "error"
            res.errors.append("lean reported no error but wrote no .olean")
        if res.ok:
            cdir.mkdir(parents=True, exist_ok=True)
            # atomic stores: another process may be reading this entry or storing the same one
            suffix = f".{os.getpid()}.{threading.get_ident()}.tmp"
            for src, dst in ((self.olean(mod), cdir / "m.olean"), (self.ilean(mod), cdir / "m.ilean")):
                if src.exists():
                    shutil.copyfile(src, dst.with_name(dst.name + suffix))
                    dst.with_name(dst.name + suffix).replace(dst)
            write_json(cdir / "result.json", res)
        return res


_AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms: \[(.*)\]", re.S)


def parse_messages(stdout: str) -> ObligationResult:
    """Turn `lean --json` output into a result: proved / stuck (unsolved goals) / error."""
    msgs: list[LeanMessage] = []
    goals: list[str] = []
    errors: list[str] = []
    axioms: list[str] = []
    sorry = False
    for line in stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        sev = d.get("severity", "")
        text = d.get("data", "")
        pos = d.get("pos") or {}
        msgs.append(LeanMessage(sev, pos.get("line", 0), pos.get("column", 0), text))
        if sev == "error":
            if text.startswith("unsolved goals"):
                goals.append(text[len("unsolved goals"):].strip())
            else:
                errors.append(f"{pos.get('line', 0)}:{pos.get('column', 0)}: {text}")
        elif sev == "warning" and "declaration uses 'sorry'" in text:
            sorry = True
        m = _AXIOMS_RE.search(text)
        if m:
            axioms += [a.strip() for a in m.group(2).split(",") if a.strip()]
    if errors:
        status = "error" if not goals else "stuck"
        # tactic failures that leave goals behind ("linarith failed", "omega could not prove") are stuck too
        if not goals and any(_is_tactic_failure(e) for e in errors):
            status = "stuck"
    elif goals:
        status = "stuck"
    elif sorry:
        status = "stuck"
        errors.append("proof uses sorry")
    else:
        status = "proved"
    if "sorryAx" in axioms:
        status = "stuck"
    return ObligationResult(status=status, goals=goals, errors=errors, axioms=sorted(set(axioms)),
                            messages=msgs)


def _is_tactic_failure(err: str) -> bool:
    keys = ("omega could not prove", "failed to prove", "grind failed", "linarith failed", "simp made no progress",
            "decide failed", "The rfl tactic failed", "unsolved goals", "failed to synthesize")
    return any(k in err for k in keys)


# native_decide (evaluation by Lean's compiler): allowed only for proofs marked native, and reported separately.
# Lean 4.35 records each use as an auxiliary axiom `<decl>._native.native_decide.ax_<n>`; older versions use
# Lean.ofReduceBool.
NATIVE_AXIOMS = {"Lean.ofReduceBool", "Lean.trustCompiler"}
_NATIVE_AUX = re.compile(r"\._native\.native_decide\.ax_\d+$")


def is_native_axiom(a: str) -> bool:
    return a in NATIVE_AXIOMS or bool(_NATIVE_AUX.search(a))


def nonstandard_axioms(axioms: list[str], native: bool = False) -> list[str]:
    return [a for a in axioms if a not in STD_AXIOMS and not (native and is_native_axiom(a))]


def _run(cmd: list[str], cwd: Path, timeout: int) -> subprocess.CompletedProcess:
    """Run a job in its own session; on timeout SIGKILL every process of that session. `timeout` and the
    core-hour guard create their own process groups, so killing the direct child is not enough."""
    env = dict(os.environ)
    env.setdefault("VO_ROOT", str(VO_ROOT))
    proc = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env,
                            start_new_session=True)
    try:
        out, _ = proc.communicate(timeout=timeout)
        return subprocess.CompletedProcess(cmd, proc.returncode, out, "")
    except subprocess.TimeoutExpired:
        kill_session(proc.pid)
        try:
            out, _ = proc.communicate(timeout=30)
        except subprocess.TimeoutExpired:
            out = ""
        return subprocess.CompletedProcess(cmd, 124, out or "", "")


def kill_session(sid: int) -> None:
    """SIGKILL every process whose session id is `sid` (explicit PIDs from /proc, never a name pattern)."""
    import signal
    pids = []
    for d in Path("/proc").iterdir():
        if not d.name.isdigit():
            continue
        try:
            stat = (d / "stat").read_text()
        except OSError:
            continue
        fields = stat[stat.rfind(")") + 2:].split()
        if len(fields) > 3 and fields[3] == str(sid):
            pids.append(int(d.name))
    for pid in pids:
        try:
            os.kill(pid, signal.SIGKILL)
        except OSError:
            pass

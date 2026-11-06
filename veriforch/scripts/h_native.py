"""Pre-registration H, part one: native x86-64 builds of a harness (plain, ubsan, asan, asan-ubsan) and sandboxed runs
of one input on them. Only the harness and library sources of the target are compiled (with the flags of its compile
database) plus veriforch's driver; no project build script runs.

    python3 -I -B h_native.py build TARGET_TOML OUT_DIR VARIANT [--cc CLANG]
    python3 -I -B h_native.py run BINARY INPUT OUT_JSON WORK_DIR [--timeout S]

build: OUT_DIR/<target>.<variant>, compiled with clang 20.1.8 (the official LLVM release, signature-verified:
scratch/theorem/toolchain/VERIFY.txt; Theorem's compiler version). Flags: Theorem's compile flags for all four builds
(docs/building.md, "Compiler and flags") without the RISC-V target flags, then the file's flags from the compile
database, then the sanitizer flags of the variant (docs/building.md, "The builds"): ubsan = -fsanitize=undefined
-fno-sanitize-recover=all -fsanitize-trap=all -fno-sanitize=function; asan = -fsanitize=address; asan-ubsan = both.
The driver (scripts/h_native/h_driver.c: reads the input file into a heap buffer of exactly its size and calls
LLVMFuzzerTestOneInput once) is compiled without sanitizer flags, as Theorem's driver is.

run: BINARY INPUT inside bubblewrap (all namespaces unshared, so no network; read-only /usr and /etc, the binary's
directory, the input and, for ASan, the symbolizer; a private tmpfs /tmp, so a harness's fixed /tmp path stays inside
the sandbox; writable only WORK_DIR), under scripts/run1.sh. ASan runs get ASAN_OPTIONS with the settings that
Theorem's sealed runtime fixes (detect_leaks=0, allocator_may_return_null=1, abort_on_error=1), reports printed and
symbolized, and a 32 TiB address-space limit (the shadow reservation).
OUT_JSON: {"binary", "variant", "input", "sha256", "rc", "signal", "seconds", "report" (sanitizer report kind or ""),
"stdout_tail", "stderr_tail", "env", "sandbox"}.
"""
from __future__ import annotations

import hashlib
import json
import resource
import os
import shlex
import subprocess
import sys
import time
import tomllib
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUN1 = HERE / "run1.sh"
SUPPORT = HERE / "h_native"
LLVM = Path("/home/user/veriforch/scratch/theorem/toolchain/LLVM-20.1.8-Linux-X64")
DEFAULT_CC = str(LLVM / "bin" / "clang")
SYMBOLIZER = LLVM / "bin" / "llvm-symbolizer"
BASE = ("-Os -g -ffunction-sections -fdata-sections -fno-stack-protector -fno-plt -Wdate-time "
        "-fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-reallocarray -fno-builtin-free "
        "-fno-builtin-aligned_alloc -fno-builtin-posix_memalign -fno-builtin-memalign -fno-builtin-valloc "
        "-fno-builtin-strdup -fno-builtin-strndup").split()
UBSAN = "-fsanitize=undefined -fno-sanitize-recover=all -fsanitize-trap=all -fno-sanitize=function".split()
ASAN = ["-fsanitize=address"]
SAN = {"plain": [], "ubsan": UBSAN, "asan": ASAN, "asan-ubsan": ASAN + UBSAN}
# Theorem's sealed runtime: detect_leaks=0, allocator_may_return_null=1, abort_on_error=1 (docs/building.md, "The
# AddressSanitizer runtime"); unlike it, reports are printed and symbolized here, so that a report can be read
ASAN_OPTIONS = "detect_leaks=0:allocator_may_return_null=1:abort_on_error=1:symbolize=1:handle_abort=0"


def run_job(cmd: list[str], cwd: Path, t: int, mem_gib: int) -> subprocess.CompletedProcess:
    full = [str(RUN1), "-t", str(t), "-m", str(mem_gib), "-c", f"{max(0.02, 1.2 * t / 3600):.3f}", "--", *cmd]
    return subprocess.run(full, cwd=str(cwd), capture_output=True, timeout=t + 300, check=False)


def compdb_flags(entry: dict) -> list[str]:
    out, skip = [], False
    for a in entry["arguments"][1:]:
        if skip:
            skip = False
            continue
        if a in ("-o", "-c"):
            skip = a == "-o"
            continue
        if a == entry["file"]:
            continue
        out.append(a)
    return out


def build(toml_path: Path, out_dir: Path, variant: str, cc: str) -> int:
    t = tomllib.loads(toml_path.read_text())
    name, group = t["name"], t["link_groups"]
    if len(group) != 1:
        raise SystemExit("one link group expected")
    root = Path(t["root"])
    db = {Path(e["file"]).resolve(): e for e in json.loads(Path(t["compile_commands"]).read_text())}
    odir = out_dir / f"{name}.{variant}.obj"
    odir.mkdir(parents=True, exist_ok=True)
    objs, log = [], []

    def step(cmd: list[str], cwd: Path) -> bool:
        p = run_job(cmd, cwd, 300, 32)
        log.append(" ".join(shlex.quote(c) for c in cmd) + f"\n  rc {p.returncode}\n" + p.stdout.decode()[-2000:]
                   + p.stderr.decode()[-2000:])
        return p.returncode == 0

    for src in group[0]:
        e = db[(root / src).resolve()]
        obj = odir / (Path(src).stem + ".o")
        if not step([cc, *BASE, *compdb_flags(e), *SAN[variant], "-c", str(root / src), "-o", str(obj)], root):
            (out_dir / f"{name}.{variant}.build.log").write_text("\n".join(log))
            print(f"compile failed: {src}", file=sys.stderr)
            return 1
        objs.append(str(obj))
    drv = odir / "h_driver.o"
    if not step([cc, *BASE, "-c", str(SUPPORT / "h_driver.c"), "-o", str(drv)], odir):
        (out_dir / f"{name}.{variant}.build.log").write_text("\n".join(log))
        return 1
    binary = out_dir / f"{name}.{variant}"
    ok = step([cc, *SAN[variant], "-o", str(binary), *objs, str(drv), "-lm"], odir)
    (out_dir / f"{name}.{variant}.build.log").write_text("\n".join(log))
    if not ok or not binary.exists():
        print("link failed", file=sys.stderr)
        return 1
    print(f"{binary}\t{hashlib.sha256(binary.read_bytes()).hexdigest()}")
    return 0


def signal_of(rc: int) -> int:
    """The signal that ended the program, from the exit status (0 if none): bwrap reports 128 + sig, the guard
    re-raises a signal as sys.exit(-sig) (256 - sig); 137 is SIGKILL (also the guard's cap kill)."""
    if rc < 0:
        return -rc
    if 224 < rc < 256:
        return 256 - rc
    if 128 < rc < 160:
        return rc - 128
    return 0


def report_kind(variant: str, rc: int, err: str) -> str:
    sig = signal_of(rc)
    if "ERROR: AddressSanitizer" in err:
        line = next(ln for ln in err.splitlines() if "ERROR: AddressSanitizer" in ln)
        return "asan: " + line.split("ERROR: AddressSanitizer", 1)[1].lstrip(": ").strip()[:200]
    if rc == 124:
        return "timeout"
    if sig == 4 and "ubsan" in variant:
        return "ubsan trap (SIGILL)"
    if sig == 6:
        return "abort (SIGABRT)"
    if sig:
        return f"signal {sig}"
    return ""


def sandbox(binary: Path, inp: Path, work: Path, env: dict) -> list[str]:
    """bubblewrap command line (the flags of the Rust worker's build-script sandbox, notes/thrift/T1_rsts.md)."""
    cmd = ["bwrap", "--unshare-all", "--die-with-parent", "--new-session",
           "--symlink", "usr/bin", "/bin", "--symlink", "usr/lib", "/lib", "--symlink", "usr/lib64", "/lib64",
           "--symlink", "usr/sbin", "/sbin", "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
           "--ro-bind", "/usr", "/usr", "--ro-bind", "/etc", "/etc",
           "--ro-bind", str(binary.parent), str(binary.parent), "--ro-bind", str(inp), str(inp)]
    if "ASAN_SYMBOLIZER_PATH" in env:
        cmd += ["--ro-bind", str(SYMBOLIZER.parent), str(SYMBOLIZER.parent)]
    cmd += ["--bind", str(work), str(work), "--chdir", str(work), "--clearenv",
            "--setenv", "PATH", "/usr/bin", "--setenv", "HOME", str(work), "--setenv", "TMPDIR", "/tmp"]
    for k, v in env.items():
        cmd += ["--setenv", k, v]
    return cmd + ["--", str(binary), str(inp)]


def run(binary: Path, inp: Path, out: Path, work: Path, timeout: int) -> int:
    variant = binary.name.rsplit(".", 1)[-1]
    env = {}
    if "asan" in variant:
        env = {"ASAN_OPTIONS": ASAN_OPTIONS, "ASAN_SYMBOLIZER_PATH": str(SYMBOLIZER)}
    work.mkdir(parents=True, exist_ok=True)
    cmd = sandbox(binary, inp, work, env)
    mem = 32768 if "asan" in variant else 32
    t0, r0 = time.monotonic(), resource.getrusage(resource.RUSAGE_CHILDREN)
    p = run_job(cmd, work, timeout, mem)
    secs, r1 = time.monotonic() - t0, resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (r1.ru_utime + r1.ru_stime) - (r0.ru_utime + r0.ru_stime)
    so, se = p.stdout.decode(errors="replace"), p.stderr.decode(errors="replace")
    rc = p.returncode
    res = {"binary": str(binary), "variant": variant, "input": str(inp),
           "sha256": hashlib.sha256(inp.read_bytes()).hexdigest(), "rc": rc, "signal": signal_of(rc),
           "seconds": round(secs, 2), "cpu_seconds": round(cpu, 2), "report": report_kind(variant, rc, se), "stdout_tail": so[-2000:],
           "stderr_tail": se[-6000:], "env": env, "sandbox": " ".join(shlex.quote(c) for c in cmd)}
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=1) + "\n")
    print(f"{binary.name}\t{inp.name}\trc {rc}\t{res['report'] or '-'}\t{res['seconds']}s")
    return 0


def main(argv: list[str]) -> int:
    if len(argv) >= 5 and argv[1] == "build":
        cc = argv[argv.index("--cc") + 1] if "--cc" in argv else DEFAULT_CC
        return build(Path(argv[2]).resolve(), Path(argv[3]).resolve(), argv[4], cc)
    if len(argv) >= 6 and argv[1] == "run":
        timeout = int(argv[argv.index("--timeout") + 1]) if "--timeout" in argv else 60
        return run(Path(argv[2]).resolve(), Path(argv[3]).resolve(), Path(argv[4]).resolve(),
                   Path(argv[5]).resolve(), timeout)
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))

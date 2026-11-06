"""Pre-registration H, part one inputs: generate cgif's seed corpora as OSS-Fuzz's `meson test` does (upstream
fuzz/meson.build at b1facf77: each tests/<name>.c of tests/meson.build's tests_index / tests_rgb, linked with
fuzz/cgif_create_fuzz_seed.c / fuzz/cgif_rgb_create_fuzz_seed.c and CGIF_OUTPATH="<name>.seed", is run to write
<name>.seed), without meson: veriforch's own gcc lines, each run sandboxed.

    python3 -I -B h_cgif_seeds.py CGIF_ROOT OUT_DIR [--cc CC]

CGIF_ROOT: the upstream tree (targets/theorem_src/cgif@b1facf77a226). OUT_DIR gets bin/ (the generators), index/ and
rgb/ (the seeds, each written by its generator as the only writable directory of the sandbox) and SEEDS.tsv (list,
name, generator exit status, seed bytes, sha256, the upstream fuzz/seeds.sha256 value or "-", check: match / MISMATCH /
unchecked / missing). Compile: CC (default gcc) -std=c99 -O0 -g -I inc (meson's defaults for the project: c_std=c99,
buildtype debug), one job per generator under scripts/run1.sh. Run: bubblewrap with all namespaces unshared (no
network), read-only /usr, /etc and the generator, a private tmpfs /tmp, writable only the list's seed directory,
under scripts/run1.sh (60 s). Nothing of the project runs outside the sandbox.
"""
from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUN1 = HERE / "run1.sh"
LISTS = {"tests_index": ("index", "fuzz/cgif_create_fuzz_seed.c"),
         "tests_rgb": ("rgb", "fuzz/cgif_rgb_create_fuzz_seed.c")}


def job(cmd: list[str], cwd: Path, t: int) -> subprocess.CompletedProcess:
    full = [str(RUN1), "-t", str(t), "-m", "16", "-c", f"{max(0.02, 1.2 * t / 3600):.3f}", "--", *cmd]
    return subprocess.run(full, cwd=str(cwd), capture_output=True, timeout=t + 300, check=False)


def names(root: Path, which: str) -> list[str]:
    t = (root / "tests" / "meson.build").read_text()
    m = re.search(rf"^{which} = \[\n(.*?)^\]", t, re.S | re.M)
    if m is None:
        raise SystemExit(f"tests/meson.build has no {which}")
    ns = re.findall(r"\{ 'name' : '([A-Za-z0-9_]+)',\s*'seed_should_fail' : (?:true|false)\s*\}", m.group(1))
    if len(ns) != len(m.group(1).strip().splitlines()):
        raise SystemExit(f"{which}: unparsed lines")
    return ns


def sandbox(gen: Path, out: Path) -> list[str]:
    return ["bwrap", "--unshare-all", "--die-with-parent", "--new-session",
            "--symlink", "usr/bin", "/bin", "--symlink", "usr/lib", "/lib", "--symlink", "usr/lib64", "/lib64",
            "--symlink", "usr/sbin", "/sbin", "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp",
            "--ro-bind", "/usr", "/usr", "--ro-bind", "/etc", "/etc", "--ro-bind", str(gen), str(gen),
            "--bind", str(out), str(out), "--chdir", str(out), "--clearenv", "--setenv", "PATH", "/usr/bin",
            "--setenv", "HOME", str(out), "--setenv", "TMPDIR", "/tmp", "--", str(gen)]


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    root, out = Path(argv[1]).resolve(), Path(argv[2]).resolve()
    cc = argv[argv.index("--cc") + 1] if "--cc" in argv else "gcc"
    sums = {}
    for ln in (root / "fuzz" / "seeds.sha256").read_text().splitlines():
        h, n = ln.split()
        sums[n] = h
    rows = ["list\tname\tgenerator_rc\tbytes\tsha256\tupstream_sha256\tcheck"]
    (out / "bin").mkdir(parents=True, exist_ok=True)
    for which, (sub, wrapper) in LISTS.items():
        sdir = out / sub
        sdir.mkdir(parents=True, exist_ok=True)
        if any(sdir.iterdir()):
            raise SystemExit(f"{sdir} is not empty; not overwritten")
        for n in names(root, which):
            gen = out / "bin" / f"{n}_genseed"
            cp = job([cc, "-std=c99", "-O0", "-g", f"-I{root / 'inc'}", f'-DCGIF_OUTPATH="{n}.seed"',
                      str(root / "tests" / f"{n}.c"), str(root / wrapper), "-o", str(gen), "-lm"], out / "bin", 300)
            if cp.returncode != 0:
                rows.append(f"{sub}\t{n}.seed\tcompile-failed\t-\t-\t{sums.get(n + '.seed', '-')}\tmissing")
                print(cp.stdout.decode()[-2000:] + cp.stderr.decode()[-2000:], file=sys.stderr)
                continue
            rp = job(sandbox(gen, sdir), sdir, 60)
            seed = sdir / f"{n}.seed"
            up = sums.get(seed.name, "-")
            if not seed.exists():
                rows.append(f"{sub}\t{seed.name}\t{rp.returncode}\t-\t-\t{up}\tmissing")
                continue
            data = seed.read_bytes()
            h = hashlib.sha256(data).hexdigest()
            check = "unchecked" if up == "-" else ("match" if h == up else "MISMATCH")
            rows.append(f"{sub}\t{seed.name}\t{rp.returncode}\t{len(data)}\t{h}\t{up}\t{check}")
        extra = sorted(p.name for p in sdir.iterdir() if not p.name.endswith(".seed"))
        if extra:
            rows.append(f"{sub}\t# other files written: {' '.join(extra)}\t-\t-\t-\t-\t-")
    (out / "SEEDS.tsv").write_text("\n".join(rows) + "\n")
    checks = [r.rsplit("\t", 1)[-1] for r in rows[1:]]
    print(f"{len(checks)} seeds: " + ", ".join(f"{c} {checks.count(c)}" for c in sorted(set(checks))))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

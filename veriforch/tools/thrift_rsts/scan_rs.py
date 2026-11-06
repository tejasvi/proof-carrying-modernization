"""Thrift T1, Rust: vendor the crates.io dependencies of a `rust_crate = "vendored"` target (its `vendor_dir` and
`cargo_lock`), once, before the first build.

`cargo vendor` (the pinned toolchain's cargo, on the host, with network) resolves the crate copy's dependencies (the
crate's own [dependencies] and [features], `dep_features` merged, as the Rust adapter writes the copy) and downloads
their sources with checksums; no build script and no code of any crate runs. The adapter then builds the crate
offline from these sources, with Charon inside bubblewrap (`rust_sandbox = "bwrap"`): orch/veriforch/adapters/rust/.
Reports which vendored crates have a build script (scratch/thrift_rsts/rs/vendor_<target>/vendor_report.json).

    tools/thrift_rsts/scan_rs.py prepare TARGET.toml
"""
from __future__ import annotations

import json
import os
import re
import shutil
import sys
import tomllib
from pathlib import Path

VO_ROOT = Path(os.environ.get("VO_ROOT", "/home/user/veriforch"))
sys.path.insert(0, str(VO_ROOT / "orch"))

from veriforch.adapters.rust import build as rb  # noqa: E402
from veriforch.config import load_target  # noqa: E402
from veriforch.model import sha256  # noqa: E402

TOOLCHAIN = "nightly-2026-09-17"        # deps/aeneas-fdebf20/bin/rust-toolchain


def _opt_path(target, key: str) -> Path:
    p = Path(target.extra[key])
    return p if p.is_absolute() else Path(target.extra["_target_dir"]) / p


def _toml(v) -> str:
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        return str(v)
    if isinstance(v, str):
        return json.dumps(v)
    if isinstance(v, list):
        return "[" + ", ".join(_toml(x) for x in v) + "]"
    if isinstance(v, dict):
        return "{ " + ", ".join(f"{k if re.fullmatch(r'[A-Za-z0-9_-]+', k) else json.dumps(k)} = {_toml(x)}"
                                for k, x in v.items()) + " }"
    raise TypeError(f"no TOML for {v!r}")


def manifest(target, pinned: bool = True) -> tuple[dict[str, bytes], str, str]:
    """The crate copy (relative path -> content), its crate name and library root. Same checks and layout as the
    adapter's crate mode, but the dependencies stay; `pinned`: with the Cargo.lock and the vendored-source config."""
    root = Path(target.root)
    man = tomllib.loads((root / "Cargo.toml").read_text())
    pkg = man.get("package", {})
    if (root / "build.rs").exists() or pkg.get("build"):
        raise ValueError("the crate has a build script (never run)")
    libsec = man.get("lib", {})
    if libsec.get("proc-macro"):
        raise ValueError("procedural macro crates are not supported")
    crate = (libsec.get("name") or pkg.get("name", root.name)).replace("-", "_")
    edition = str(pkg.get("edition", "2015"))
    lib = libsec.get("path", "src/lib.rs")
    files: dict[str, bytes] = {}
    for f in sorted((root / "src").rglob("*")):
        if f.is_file():
            files[f.relative_to(root).as_posix()] = f.read_bytes()
    if lib not in files:
        raise ValueError(f"no library root {lib}")
    deps = dict(man.get("dependencies", {}))
    for name, feats in (target.extra.get("dep_features") or {}).items():
        spec = deps[name]
        spec = {"version": spec} if isinstance(spec, str) else dict(spec)
        spec["features"] = sorted(set(spec.get("features", [])) | set(feats))
        deps[name] = spec
    head = f'[package]\nname = "{crate}"\nversion = "0.0.0"\nedition = "{edition}"\n'
    if pkg.get("rust-version"):
        head += f'rust-version = "{pkg["rust-version"]}"\n'      # the resolver picks versions for it (as upstream)
    toml = [head, f'[lib]\npath = "{lib}"\n', "[workspace]\n",
            "[dependencies]\n" + "".join(f"{k} = {_toml(v)}\n" for k, v in deps.items())]
    if man.get("features"):
        toml.append("[features]\n" + "".join(f"{k} = {json.dumps(v)}\n" for k, v in man["features"].items()))
    files["Cargo.toml"] = "\n".join(toml).encode()
    if pinned:
        files["Cargo.lock"] = _opt_path(target, "cargo_lock").read_bytes()
        vendor = _opt_path(target, "vendor_dir")
        files[".cargo/config.toml"] = (f'[source.crates-io]\nreplace-with = "vendored-sources"\n\n'
                                       f'[source.vendored-sources]\ndirectory = "{vendor}"\n\n'
                                       f'[net]\noffline = true\n').encode()
    return files, crate, lib


def build_scripts(vendor: Path) -> list[dict]:
    """Vendored crates with a build script (build.rs, or `package.build` in their Cargo.toml)."""
    out = []
    for d in sorted(p for p in vendor.iterdir() if p.is_dir()):
        man = tomllib.loads((d / "Cargo.toml").read_text())
        b = man.get("package", {}).get("build")
        if b is False:
            continue
        path = b if isinstance(b, str) else ("build.rs" if (d / "build.rs").exists() else None)
        if path:
            out.append({"crate": d.name, "build": path, "sha256": sha256((d / path).read_bytes())
                        if (d / path).is_file() else None})
    return out


def prepare(t) -> int:
    """`cargo vendor` for the crate copy (unpinned manifest): writes vendor_dir and cargo_lock. Downloads the sources
    and their checksums; no build script and no code of the crates runs."""
    work = VO_ROOT / "scratch" / "thrift_rsts" / "rs" / f"vendor_{t.name}"
    vendor = _opt_path(t, "vendor_dir")
    if vendor.exists():
        raise SystemExit(f"{vendor} exists: remove it by hand (after checking it) to vendor again")
    files, _, _ = manifest(t, pinned=False)
    cdir = work / "crate"
    rb._write_tree(cdir, files)
    (work / "cargo_home").mkdir(parents=True, exist_ok=True)
    p = rb._job(["cargo", f"+{TOOLCHAIN}", "vendor", str(vendor)], cdir, mem_gib=16,
                timeout=900, core_h=0.2, env={"CARGO_HOME": work / "cargo_home", "CARGO_TERM_COLOR": "never",
                                             "TMPDIR": VO_ROOT / "scratch" / "tmp"}, log=work / "vendor.log")
    print(rb._text(p.stdout)[-3000:])
    if p.returncode != 0 or not (cdir / "Cargo.lock").exists():
        return 1
    lock = _opt_path(t, "cargo_lock")
    shutil.copyfile(cdir / "Cargo.lock", lock)
    bs = build_scripts(vendor)
    rep = {"vendor_dir": str(vendor), "cargo_lock": str(lock), "cargo_lock_sha256": sha256(lock.read_bytes()),
           "crates": sorted(p.name for p in vendor.iterdir() if p.is_dir()), "build_scripts": bs}
    (work / "vendor_report.json").write_text(json.dumps(rep, indent=1))
    print(json.dumps(rep, indent=1))
    return 0


def main(argv: list[str]) -> int:
    if len(argv) != 2 or argv[0] != "prepare":
        print(__doc__, file=sys.stderr)
        return 2
    return prepare(load_target(argv[1]))


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

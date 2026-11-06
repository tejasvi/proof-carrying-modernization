"""Thrift T3, Rust: one vendored dependency set per distinct lib/rs/Cargo.toml among the T3 commits and their parents.

For every Rust commit of the frozen T3 list (~/fv_paper/prereg/T/t3_commits.tsv) and its first parent, the content
of lib/rs/Cargo.toml is read from the clone's git objects (git rev-parse / cat-file: data only). For each distinct
content (key: its sha256, which the T3 driver computes from the file at p and c), the crate manifest that the Rust
adapter writes for `rust_crate = "vendored"` is rendered (orch/veriforch/adapters/rust/build.py: [dependencies] and
[features] of that Cargo.toml, `dep_features` merged where the dependency exists), with a stub src/lib.rs, and
`cargo vendor` (the pinned toolchain's cargo, on the host) resolves and downloads the sources: nothing of any crate
runs. Output, per set: OUT/<first 16 hex of the sha256>/{Cargo.toml.orig, Cargo.lock, vendor/, features.json,
set.json}; OUT/sets.json maps every
commit's p and c to their set.

    tools/thrift_rsts/t3_vendor_sets.py OUT
"""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tomllib
from pathlib import Path

VO_ROOT = Path("/home/user/veriforch")
sys.path.insert(0, str(VO_ROOT / "orch"))
from veriforch.adapters.rust import build as rb  # noqa: E402

CLONE = VO_ROOT / "targets" / "thrift"
T3_LIST = Path("/home/user/fv_paper/prereg/T/t3_commits.tsv")
TOOLCHAIN = "nightly-2026-09-17"
DEP_FEATURES = {"uuid": ["v4"]}          # as targets/thrift_rs.toml (the promoted tests call Uuid::new_v4)
FEATURES = ["rustls"]                     # as targets/thrift_rs.toml, where the revision defines it


def git(*args: str) -> bytes:
    p = subprocess.run(["git", "-C", str(CLONE), "-c", "core.fsmonitor=", "-c", "core.hooksPath=/dev/null", *args],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    return p.stdout


def render(man: dict) -> tuple[str, str]:
    """The adapter's vendored manifest for this Cargo.toml (crate name, edition, rust-version, [lib], [workspace],
    [dependencies] with DEP_FEATURES merged where present, [features]), and the library path."""
    pkg = man.get("package", {})
    libsec = man.get("lib", {})
    crate = (libsec.get("name") or pkg["name"]).replace("-", "_")
    edition = str(pkg.get("edition", "2015"))
    lib = libsec.get("path", "src/lib.rs")
    deps = dict(man.get("dependencies", {}))
    for name, feats in DEP_FEATURES.items():
        if name in deps:
            spec = deps[name]
            spec = {"version": spec} if isinstance(spec, str) else dict(spec)
            spec["features"] = sorted(set(spec.get("features", [])) | set(feats))
            deps[name] = spec
    toml = [f'[package]\nname = "{crate}"\nversion = "0.0.0"\nedition = "{edition}"\n'
            + (f'rust-version = "{pkg["rust-version"]}"\n' if pkg.get("rust-version") else ""),
            f'[lib]\npath = "{lib}"\n', "[workspace]\n",
            "[dependencies]\n" + "".join(f"{k} = {rb._toml_value(v)}\n" for k, v in deps.items())]
    if man.get("features"):
        toml.append("[features]\n" + "".join(f"{k} = {json.dumps(v)}\n" for k, v in man["features"].items()))
    return "\n".join(toml), lib


def main(argv: list[str]) -> int:
    out = Path(argv[0])
    out.mkdir(parents=True, exist_ok=True)
    rows = [l.split("\t") for l in T3_LIST.read_text().splitlines()[1:] if l.strip()]
    commits = [(r[0], r[1], r[2]) for r in rows if "Rust" in r[4].split(",")]
    revs: dict[str, dict] = {}
    contents: dict[str, bytes] = {}
    for order, c, date in commits:
        p = git("rev-parse", f"{c}^1").decode().strip()
        entry = {"order": order, "commit": c, "date": date, "parent": p}
        for side, rev in (("p", p), ("c", c)):
            data = git("cat-file", "-p", f"{rev}:lib/rs/Cargo.toml")
            h = hashlib.sha256(data).hexdigest()
            contents[h] = data
            entry[f"{side}_cargo_toml_sha256"] = h
        revs[c] = entry
    sets = {}
    for h, data in sorted(contents.items()):
        d = out / h[:16]                     # the T3 driver's layout: first 16 hex digits of the sha256
        man = tomllib.loads(data.decode())
        manifest, lib = render(man)
        work = VO_ROOT / "scratch" / "thrift_rsts" / "t3" / f"vendor_{h[:16]}"
        (work / "crate" / Path(lib).parent).mkdir(parents=True, exist_ok=True)
        (work / "crate" / "Cargo.toml").write_text(manifest)
        (work / "crate" / lib).write_text("// stub: cargo vendor needs a library target, not its code\n")
        (work / "cargo_home").mkdir(parents=True, exist_ok=True)
        if (d / "vendor").exists():
            raise SystemExit(f"{d / 'vendor'} exists: remove it by hand (after checking it) to vendor again")
        d.mkdir(parents=True, exist_ok=True)
        (d / "Cargo.toml.orig").write_bytes(data)
        q = rb._job(["cargo", f"+{TOOLCHAIN}", "vendor", str(d / "vendor")], work / "crate", mem_gib=16, timeout=900,
                    core_h=0.2, env={"CARGO_HOME": work / "cargo_home", "CARGO_TERM_COLOR": "never",
                                     "TMPDIR": VO_ROOT / "scratch" / "tmp"}, log=work / "vendor.log")
        if q.returncode != 0 or not (work / "crate" / "Cargo.lock").exists():
            print(f"{h[:16]}: cargo vendor failed: {rb._text(q.stdout)[-1500:]}")
            return 1
        lock = (work / "crate" / "Cargo.lock").read_bytes()
        (d / "Cargo.lock").write_bytes(lock)
        bs = []
        for v in sorted(x for x in (d / "vendor").iterdir() if x.is_dir()):
            vm = tomllib.loads((v / "Cargo.toml").read_text())
            b = vm.get("package", {}).get("build")
            if b is not False and (isinstance(b, str) or (v / "build.rs").exists()):
                bs.append(v.name)
        defined = sorted((man.get("features") or {}).keys())
        info = {"cargo_toml_sha256": h, "cargo_lock_sha256": hashlib.sha256(lock).hexdigest(),
                "edition": man.get("package", {}).get("edition"), "rust_version": man.get("package", {}).get("rust-version"),
                "dependencies": sorted((man.get("dependencies") or {}).keys()), "features_defined": defined,
                "cargo_features": [f for f in FEATURES if f in defined],
                "dep_features": {k: v for k, v in DEP_FEATURES.items() if k in (man.get("dependencies") or {})},
                "vendored_crates": len([x for x in (d / "vendor").iterdir() if x.is_dir()]),
                "crates_with_build_script": bs, "generated_manifest": manifest,
                "revisions": sorted({f"{e['order']}:{side}" for e in revs.values() for side in ("p", "c")
                                     if e[f"{side}_cargo_toml_sha256"] == h}, key=lambda s: (int(s.split(':')[0]), s))}
        (d / "set.json").write_text(json.dumps(info, indent=1))
        (d / "features.json").write_text(json.dumps(info["cargo_features"]) + "\n")
        sets[h] = {k: info[k] for k in ("cargo_lock_sha256", "features_defined", "cargo_features", "dep_features",
                                        "dependencies", "edition", "rust_version", "crates_with_build_script")}
        sets[h]["dir"] = h[:16]
        print(f"{h[:16]}: lock {info['cargo_lock_sha256'][:16]}, {info['vendored_crates']} crates, features "
              f"{defined}, revisions {len(info['revisions'])}", flush=True)
    (out / "sets.json").write_text(json.dumps({"tool": "tools/thrift_rsts/t3_vendor_sets.py", "toolchain": TOOLCHAIN,
                                               "sets": sets, "commits": list(revs.values())}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

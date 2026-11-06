"""Pre-registration H, part one: veriforch targets for the selected harnesses (harness and library unmodified).

    python3 -I -B h_targets.py THEOREM_REPO OSSFUZZ_GIT UPSTREAMS_DIR SRC_DIR TARGETS_DIR

For each selected entry point: the upstream tree at the commit of Theorem's build record, extracted with `git archive`
into SRC_DIR/<project>@<commit12>/ (once; nothing of it is run), the OSS-Fuzz harness file (when the harness comes
from OSS-Fuzz) copied to <that tree>/_ossfuzz/, and, in TARGETS_DIR, h_<project>_<harness>.compile_commands.json and
h_<project>_<harness>.toml (a cir target, one link group: the harness and the library files that Theorem's build
links, per its build record's licence components). Every harness file is checked byte for byte against Theorem's copy
(projects/<project>/<harness>/source/).

Compile flags (no optimisation flags, host x86-64): the library's own configuration as Theorem's recipe built it, as far
as it changes the source that is compiled (defines, language standard, include directories):
- cgif: meson (default buildtype: no NDEBUG), c_std=c99 for the library; the harness with Theorem's harness flags
  (no -std); include inc/.
- yajl-ruby: the files compiled as C with -I ext/yajl (OSS-Fuzz build.sh:25-27; Theorem's blind recipe: no -std,
  no defines).
- cJSON: CMake Release with Theorem's options (pin: ENABLE_CUSTOM_COMPILER_FLAGS=OFF, ENABLE_CJSON_TEST=OFF,
  ENABLE_CJSON_UTILS=ON) and the defaults (ENABLE_PUBLIC_SYMBOLS, ENABLE_LOCALES): cJSON.c with -DNDEBUG
  -DCJSON_EXPORT_SYMBOLS -DCJSON_API_VISIBILITY -DENABLE_LOCALES -fvisibility=hidden; the harness with Theorem's
  harness flags (no defines).
- bzip2: the files with -I . (OSS-Fuzz build.sh:19-34; Theorem's blind recipe: no defines).
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path

GIT_ENV = dict(os.environ, GIT_TERMINAL_PROMPT="0", GIT_CONFIG_NOSYSTEM="1")
OSSFUZZ_COMMIT = "bd2ce21991a94a362b92fb1bf25f86d5a1a60842"

# project, harness, upstream repository dir name, commit, harness source (repo, path), library files, flags
HARNESSES = [
    {"project": "cgif", "harness": "cgif_file_fuzzer", "updir": "github.com_dloebl_cgif@b1facf77a226.git",
     "commit": "b1facf77a226e971fdd9c0f2fd616ab9b03562d9",
     "hsrc": ("upstream", "fuzz/cgif_file_fuzzer.c"), "theorem_copy": "source/cgif_file_fuzzer.c",
     "lib": ["src/cgif.c", "src/cgif_raw.c"],
     "lib_flags": ["-std=c99", "-I{root}/inc"], "h_flags": ["-I{root}/inc"]},
    {"project": "cgif", "harness": "cgif_rgb_fuzzer", "updir": "github.com_dloebl_cgif@b1facf77a226.git",
     "commit": "b1facf77a226e971fdd9c0f2fd616ab9b03562d9",
     "hsrc": ("upstream", "fuzz/cgif_rgb_fuzzer.c"), "theorem_copy": "source/cgif_rgb_fuzzer.c",
     "lib": ["src/cgif.c", "src/cgif_raw.c", "src/cgif_rgb.c"],
     "lib_flags": ["-std=c99", "-I{root}/inc"], "h_flags": ["-I{root}/inc"]},
    {"project": "yajl-ruby", "harness": "json_fuzzer", "updir": "github.com_brianmario_yajl-ruby@6501652d1135.git",
     "commit": "6501652d113557d976676134056aa983e7863020",
     "hsrc": ("oss-fuzz", "projects/yajl-ruby/json_fuzzer.c"), "theorem_copy": "source/json_fuzzer.c",
     "lib": ["ext/yajl/yajl.c", "ext/yajl/yajl_alloc.c", "ext/yajl/yajl_buf.c", "ext/yajl/yajl_encode.c",
             "ext/yajl/yajl_lex.c", "ext/yajl/yajl_parser.c"],
     "lib_flags": ["-I{root}/ext/yajl"], "h_flags": ["-I{root}/ext/yajl"]},
    {"project": "cjson", "harness": "cjson_read_fuzzer", "updir": "github.com_davegamble_cjson@acc76239bee0.git",
     "commit": "acc76239bee01d8e9c858ae2cab296704e52d916",
     "hsrc": ("upstream", "fuzzing/cjson_read_fuzzer.c"), "theorem_copy": "source/cjson_read_fuzzer.c",
     "lib": ["cJSON.c"],
     "lib_flags": ["-DNDEBUG", "-DCJSON_EXPORT_SYMBOLS", "-DCJSON_API_VISIBILITY", "-DENABLE_LOCALES",
                   "-fvisibility=hidden", "-I{root}"],
     "h_flags": ["-I{root}"]},
    {"project": "bzip2", "harness": "bzip2_compress_target", "updir": "sourceware.org_git_bzip2@f5dfc96063fe.git",
     "commit": "f5dfc96063fef2d9c5446d0733867d899ef9b942",
     "hsrc": ("oss-fuzz", "projects/bzip2/bzip2_compress_target.c"),
     "theorem_copy": "source/bzip2_compress_target.c",
     "lib": ["blocksort.c", "bzlib.c", "compress.c", "crctable.c", "decompress.c", "huffman.c", "randtable.c"],
     "lib_flags": ["-I{root}"], "h_flags": ["-I{root}"]},
]


def git_bytes(repo: Path, *args: str) -> bytes:
    p = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, env=GIT_ENV, timeout=600, check=False)
    if p.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} in {repo}: rc {p.returncode}: {p.stderr.decode(errors='replace')}")
    return p.stdout


def extract(repo: Path, commit: str, dest: Path) -> None:
    """The tree at `commit` in dest (git archive | tar), once: a stamp file records the commit."""
    stamp = dest / ".h_extracted"
    if stamp.exists():
        if stamp.read_text().strip() != commit:
            raise SystemExit(f"{dest} holds another commit")
        return
    if dest.exists() and any(dest.iterdir()):
        raise SystemExit(f"{dest} exists, is not empty and has no stamp; not touched")
    dest.mkdir(parents=True, exist_ok=True)
    tar = git_bytes(repo, "archive", "--format=tar", commit)
    subprocess.run(["tar", "-x", "--no-same-owner", "--no-same-permissions", "-C", str(dest)], input=tar,
                   check=True, timeout=600)
    links = [str(p.relative_to(dest)) for p in dest.rglob("*") if p.is_symlink()]
    if links:
        print(f"note: {dest} has symlinks: {links[:5]}", file=sys.stderr)
    stamp.write_text(commit + "\n")


def main(argv: list[str]) -> int:
    if len(argv) != 6:
        print(__doc__, file=sys.stderr)
        return 2
    theorem, ossfuzz, updir, srcdir, tdir = (Path(a).resolve() for a in argv[1:])
    out = []
    for h in HARNESSES:
        root = srcdir / f"{h['project']}@{h['commit'][:12]}"
        extract(updir / h["updir"], h["commit"], root)
        kind, path = h["hsrc"]
        if kind == "oss-fuzz":
            data = git_bytes(ossfuzz, "cat-file", "blob", f"{OSSFUZZ_COMMIT}:{path}")
            rel = "_ossfuzz/" + path.rsplit("/", 1)[-1]
            dst = root / rel
            if dst.exists() and dst.read_bytes() != data:
                raise SystemExit(f"{dst} differs from OSS-Fuzz's file; not overwritten")
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(data)
        else:
            rel = path
            data = (root / rel).read_bytes()
        tcopy = (theorem / "projects" / h["project"] / h["harness"] / h["theorem_copy"]).read_bytes()
        if tcopy != data:
            raise SystemExit(f"{h['project']}/{h['harness']}: harness differs from Theorem's copy")
        entries = []
        for f, flags in [(rel, h["h_flags"])] + [(x, h["lib_flags"]) for x in h["lib"]]:
            if not (root / f).is_file():
                raise SystemExit(f"{root / f} missing")
            entries.append({"directory": str(root), "file": str(root / f),
                            "arguments": ["cc", *[x.format(root=root) for x in flags], "-c", str(root / f),
                                          "-o", Path(f).name + ".o"]})
        name = f"h_{h['project'].replace('-', '_')}_{h['harness']}"
        cdb = tdir / f"{name}.compile_commands.json"
        cdb.write_text(json.dumps(entries, indent=1) + "\n")
        group = ", ".join(json.dumps(x) for x in [rel] + h["lib"])
        toml = (f"# Pre-registration H, part one: {h['project']}/{h['harness']} as Theorem built it (upstream"
                f" {h['commit'][:12]}; harness {kind}:{path}), harness and library unmodified. Written by"
                f" scripts/h_targets.py.\n"
                f'name = "{name}"\nlang = "cir"\nroot = "{root}"\ncompile_commands = "{cdb}"\n'
                f'link_mode = "cir2lean"\nlink_groups = [[{group}]]\n')
        (tdir / f"{name}.toml").write_text(toml)
        out.append(f"{name}\t{root}\t{hashlib.sha256(toml.encode()).hexdigest()[:16]}"
                   f"\t{hashlib.sha256(cdb.read_bytes()).hexdigest()[:16]}")
    print("\n".join(out))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

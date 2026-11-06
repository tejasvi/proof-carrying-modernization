"""Delete regenerable Lean build products under an explicit allowlist of finished run directories.

    python3 -I tools/prune_build_v3.py MANIFEST_DIR ROOT...      # dry run: lists what would go
    python3 -I tools/prune_build_v3.py --delete MANIFEST_DIR ROOT...

A file goes only if it lies below a `.lake/build` directory or below `cache/olean` / `cache/olean_cert`
(veriforch's per-run .olean caches). Lean sources, proof JSON, records, logs and transcripts stay. Each ROOT must
be an existing absolute directory directly under ~/veriforch/runs or runs/prereg/C or runs/prereg/C1b, given literally; a root that any of our
processes has a file open under, or that has a file modified in the last 60 minutes, is skipped whole. Every file
is listed in MANIFEST_DIR/manifest.tsv (path, bytes) before it is unlinked one by one; afterwards only directories
left empty inside the pruned subtrees are removed (rmdir). Never follows symlinks.
"""
from __future__ import annotations

import os
import sys
import time
from pathlib import Path

RUNS = Path("/home/user/veriforch/runs")
PARENTS = (RUNS, RUNS / "prereg" / "C", RUNS / "prereg" / "C1b")   # roots: under runs/, or C/C1b study dirs
RECENT_S = 3600


def open_paths() -> set[str]:
    """Targets of the file descriptors of this user's processes (fd links only)."""
    out, uid = set(), os.getuid()
    for pid in os.listdir("/proc"):
        if not pid.isdigit():
            continue
        try:
            if os.stat(f"/proc/{pid}").st_uid != uid:
                continue
            for fd in os.listdir(f"/proc/{pid}/fd"):
                try:
                    out.add(os.readlink(f"/proc/{pid}/fd/{fd}"))
                except OSError:
                    pass
            out.add(os.readlink(f"/proc/{pid}/cwd"))
        except OSError:
            pass
    return out


def prunable(rel_parts: tuple[str, ...]) -> bool:
    for i in range(len(rel_parts) - 1):
        if rel_parts[i] == ".lake" and rel_parts[i + 1] == "build":
            return True
        if rel_parts[i] == "cache" and rel_parts[i + 1] in ("olean", "olean_cert"):
            return True
    return False


def walk(root: Path):
    stack = [root]
    while stack:
        d = stack.pop()
        try:
            with os.scandir(d) as it:
                for e in it:
                    if e.is_symlink():
                        continue
                    if e.is_dir(follow_symlinks=False):
                        stack.append(Path(e.path))
                    elif e.is_file(follow_symlinks=False):
                        st = e.stat(follow_symlinks=False)
                        yield Path(e.path), st.st_size, st.st_mtime
        except OSError:
            continue


def main(argv: list[str]) -> int:
    delete = argv[:1] == ["--delete"]
    argv = argv[1:] if delete else argv
    if len(argv) < 2:
        print(__doc__)
        return 2
    mdir, roots = Path(argv[0]), [Path(a) for a in argv[1:]]
    for r in roots:
        if not r.is_absolute() or r.parent not in PARENTS or not r.is_dir() or r.is_symlink() or r.name in ("", ".", ".."):
            print(f"refused root {r}: must be an existing directory directly under one of {PARENTS}")
            return 2
    mdir.mkdir(parents=True, exist_ok=True)
    busy = open_paths()
    now = time.time()
    total = n_total = 0
    with open(mdir / "manifest.tsv", "a") as man:
        for r in roots:
            rs = str(r) + "/"
            if any(p == str(r) or p.startswith(rs) for p in busy):
                print(f"skip {r}: a process has a file open below it")
                continue
            files = list(walk(r))
            recent = [p for p, _, mt in files if now - mt < RECENT_S]
            if recent:
                print(f"skip {r}: {len(recent)} files modified in the last hour, e.g. {recent[0]}")
                continue
            sel = [(p, s) for p, s, _ in files if prunable(p.relative_to(r).parts)]
            size = sum(s for _, s in sel)
            print(f"{r}: {len(sel)} build files, {size / 2**30:.2f} GiB of {sum(s for _, s, _ in files) / 2**30:.2f}")
            if not delete:
                continue
            for p, s in sel:
                man.write(f"{p}\t{s}\n")
            man.flush()
            dirs = set()
            for p, s in sel:
                try:
                    os.unlink(p)
                    total += s
                    n_total += 1
                    dirs.add(p.parent)
                except OSError as e:
                    print(f"  could not unlink {p}: {e}")
            # remove directories left empty, deepest first, never above the pruned subtree roots
            for d in sorted(dirs, key=lambda x: len(x.parts), reverse=True):
                while d != r and str(d).startswith(rs) and prunable(d.relative_to(r).parts + ("x",)):
                    try:
                        os.rmdir(d)
                    except OSError:
                        break
                    d = d.parent
    print(f"deleted {n_total} files, {total / 2**30:.2f} GiB" if delete else "dry run done (nothing deleted)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

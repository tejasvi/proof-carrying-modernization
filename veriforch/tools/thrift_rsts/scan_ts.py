"""Thrift T1 coverage scan (no model calls), TypeScript: veriforch's StrictTS coverage build on a copy of the project.

The StrictTS adapter's coverage mode (orch/veriforch/adapters/strictts/build.py `build_coverage`, as for the D2
es-toolkit target) takes its tsconfig from StrictTS's tools/public/tsconfig/<coverage_project>.json and writes
tsconfig.strictts.json into the target root. Thrift is not one of StrictTS's public projects and its clone is shared,
so this driver (nothing in orch/ or deps/ is edited):

* `prepare`: copies the listed files (`copy`) from `source_root` (the clone, read only) to `root` (a scratch copy;
  their sha256 go to <root>/SOURCES.sha256);
* `scan`: runs `build_coverage` unchanged with the pinned StrictTS (VO_STRICTTS_DIR, set before the import) and the
  tsconfig template given inline by the target (`coverage_tsconfig`), presented to the adapter through an overlay
  directory that holds only that template and a link to the pinned StrictTS's @types (the adapter reads nothing
  else from STRICTTS in coverage mode; the CLI, node_modules and Lean library are the pinned tree's).

    tools/thrift_rsts/scan_ts.py prepare TARGET.toml
    tools/thrift_rsts/scan_ts.py scan TARGET.toml       # runs/<target>/<version>/<variant>/units.json + coverage
"""
from __future__ import annotations

import json
import os
import shutil
import sys
from pathlib import Path

VO_ROOT = Path(os.environ.get("VO_ROOT", "/home/user/veriforch"))
STRICTTS_PIN_DIR = VO_ROOT / "deps" / "strictts-44d6b9b"           # the D2 pin
os.environ.setdefault("VO_STRICTTS_DIR", str(STRICTTS_PIN_DIR))
os.environ.setdefault("VO_STRICTTS_PIN", "44d6b9b")
sys.path.insert(0, str(VO_ROOT / "orch"))

from veriforch.adapters.strictts import build as sb  # noqa: E402
from veriforch.config import load_target  # noqa: E402
from veriforch.model import sha256, write_json  # noqa: E402


def prepare(t) -> int:
    src, root = Path(t.extra["source_root"]), Path(t.root)
    lines = []
    for rel in t.extra["copy"]:
        data = (src / rel).read_bytes()
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)
        lines.append(f"{sha256(data)}  {rel}\n")
    (root / "SOURCES.sha256").write_text("".join(lines))
    print(f"{len(lines)} files copied to {root}")
    return 0


def overlay(t) -> Path:
    """A directory standing for STRICTTS in `build_coverage`: tools/public/tsconfig/<project>.json (the target's
    template) and frontend/node_modules/@types (a link to the pinned StrictTS's)."""
    name = t.extra["coverage_project"]
    ov = VO_ROOT / "scratch" / "thrift_rsts" / "ts" / f"overlay_{t.name}"
    (ov / "tools" / "public" / "tsconfig").mkdir(parents=True, exist_ok=True)
    (ov / "tools" / "public" / "tsconfig" / f"{name}.json").write_text(
        json.dumps(t.extra["coverage_tsconfig"], indent=2) + "\n")
    types = ov / "frontend" / "node_modules" / "@types"
    types.parent.mkdir(parents=True, exist_ok=True)
    if not types.is_symlink():
        types.symlink_to(Path(os.environ["VO_STRICTTS_DIR"]) / "frontend" / "node_modules" / "@types")
    return ov


def scan(t) -> int:
    from veriforch.cli import run_dir_for
    root = Path(t.root)
    for line in (root / "SOURCES.sha256").read_text().splitlines():      # the copy is what `prepare` wrote
        h, rel = line.split("  ", 1)
        if sha256((root / rel).read_bytes()) != h or sha256((Path(t.extra["source_root"]) / rel).read_bytes()) != h:
            raise SystemExit(f"{rel}: the copy or the clone changed since `prepare`")
    sb.STRICTTS = overlay(t)
    for v in t.variants:
        b = sb.build_coverage(t, v, run_dir_for(t))
        write_json(b.dir / "units.json", b.units)
        print(f"[{v.name}] {len(b.units)} units -> {b.dir / 'units.json'}", flush=True)
        for u in b.units:
            print(f"  {u.name:40} {u.scope}", flush=True)
    return 0


def main(argv: list[str]) -> int:
    if len(argv) != 2 or argv[0] not in ("prepare", "scan"):
        print(__doc__, file=sys.stderr)
        return 2
    t = load_target(argv[1])
    return prepare(t) if argv[0] == "prepare" else scan(t)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

"""Thrift T1, Rust: which functions are library code and which are #[cfg(test)] code (tests and their helpers).

The Rust adapter promotes tests (`#[cfg(test)]` removed, `#[test]` -> doc attribute), so its units include every
function of the test modules. PREREG_T's frame takes library code only (the evidence-owner session's clarification: no function of a
#[cfg(test)] module). This runs Charon (inside bubblewrap, the target's options, as the adapter does) on the crate
copy WITHOUT the promotion, where rustc itself drops the cfg(test) code, and writes the library functions
(path, file, line; the promotion keeps every line where it was) to OUT.json.

    tools/thrift_rsts/cfgtest_rs.py TARGET.toml OUT.json
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

VO_ROOT = Path("/home/user/veriforch")
sys.path.insert(0, str(VO_ROOT / "orch"))
from veriforch.adapters.rust import build as rb  # noqa: E402
from veriforch.config import load_target  # noqa: E402


def main(argv: list[str]) -> int:
    t = load_target(argv[0])
    # the prune file only shapes what Aeneas reads; its --opaque patterns name test functions, absent here
    t.extra.pop("aeneas_prune_file", None)
    work = VO_ROOT / "scratch" / "thrift_rsts" / "rs" / f"libonly_{t.name}"
    files, crate, _ = rb._cargo_manifest(t)
    cdir = work / "crate"
    rb._write_tree(cdir, files)
    llbc, out = rb._charon(work, cdir, crate, t)
    if llbc is None:
        print(f"Charon failed: {out[-2000:]}")
        return 1
    funs, info = rb.llbc_functions(llbc)
    lib = [{"path": f["path"], "file": f["file"], "line": f["line"]} for f in funs
           if f["has_body"] and not f["global"] and "{" not in f["path"].split("::")[-1]]
    Path(argv[1]).write_text(json.dumps({"charon_version": info.get("charon_version"), "llbc": str(llbc),
                                         "library_functions": lib}, indent=1))
    print(f"{len(lib)} library functions (no cfg(test) code) -> {argv[1]}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

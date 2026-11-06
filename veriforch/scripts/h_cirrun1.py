"""Pre-registration H, part one: run one input of a harness on cirlean's semantics (veriforch's vo-cirrun, the pinned
cirlean's cirrun with `cir2lean --link`'s linking) and record the outcome.

    python3 -I -B h_cirrun1.py VO_CIRRUN TARGET_TOML VARIANT_DIR INPUT OUT_JSON [--timeout S] [--run1 RUN1_SH]

TARGET_TOML: an h_*.toml target (one link group); VARIANT_DIR: the variant directory of its `vo scan`
(runs/<target>/v0/<variant>/), which holds <stem>.cir for each source of the link group (taken in link order). The harness entry point LLVMFuzzerTestOneInput(data, size) is called
with data = a fresh array holding exactly the input's bytes and size = its length (as libFuzzer calls it). The run goes
through scripts/run1.sh (wall clock S seconds, default 60, plus run1's 30 s kill grace).

OUT_JSON: {"input", "bytes", "sha256", "outcome", "message", "rc", "seconds", "stdout_tail", "stderr_tail", "cmd_cirs"}
with outcome one of: "normal end" (the harness returned a value), "ub" (cirlean's result `UB: <message>`; whether the
message names an unsupported construct is decided later, from the message, by the report script), "timeout", "error"
(anything else: the runner failed or printed something unexpected). stdout_sha256 is the sha256 of the whole stdout,
stdout_untagged_sha256 that of the stdout without the locator's location tags (the locator's differential check
compares the pinned run's stdout_sha256 with the locator run's stdout_untagged_sha256).
"""
from __future__ import annotations

import hashlib
import json
import resource
import re
import subprocess
import sys
import time
import tomllib
from pathlib import Path

ENTRY = "LLVMFuzzerTestOneInput"
# the locator's location tags (scripts/h_locator_gen.py); the pinned runner never prints them
TAG = re.compile(r"⟦(?:call \S+ \S+ @\d+:\d+|loop @\d+:\d+)⟧")


def cirs_of(toml: Path, vdir: Path) -> list[str]:
    """The .cir files of a linked build, in link order (the target's single link group)."""
    groups = tomllib.loads(toml.read_text())["link_groups"]
    if len(groups) != 1:
        raise SystemExit(f"{toml}: expected one link group")
    cirs = [str(vdir / (Path(s).stem + ".cir")) for s in groups[0]]
    missing = [c for c in cirs if not Path(c).is_file()]
    if missing:
        raise SystemExit(f"missing .cir files: {missing}")
    return cirs


def main(argv: list[str]) -> int:
    args, timeout, run1 = [], 60, str(Path(__file__).resolve().parent / "run1.sh")
    it = iter(argv[1:])
    for a in it:
        if a == "--timeout":
            timeout = int(next(it))
        elif a == "--run1":
            run1 = next(it)
        else:
            args.append(a)
    if len(args) != 5:
        print(__doc__, file=sys.stderr)
        return 2
    exe, toml, vdir, inp, out = (Path(a).resolve() for a in args)
    data = inp.read_bytes()
    cirs = cirs_of(toml, vdir)
    arr = "&[" + ",".join(str(b) for b in data) + "]"
    cmd = [run1, "-t", str(timeout), "-m", "32", "-c", f"{max(0.02, 1.2 * timeout / 3600):.3f}", "--",
           str(exe), *cirs, "--", ENTRY, arr, str(len(data))]
    t0, r0 = time.monotonic(), resource.getrusage(resource.RUSAGE_CHILDREN)
    p = subprocess.run(cmd, capture_output=True, cwd=str(vdir), timeout=timeout + 300, check=False)
    secs, r1 = time.monotonic() - t0, resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (r1.ru_utime + r1.ru_stime) - (r0.ru_utime + r0.ru_stime)
    so, se = p.stdout.decode(errors="replace"), p.stderr.decode(errors="replace")
    lines = [ln for ln in so.splitlines() if ln.strip()]
    first = lines[0].strip() if lines else ""
    if p.returncode == 124 or (p.returncode == 137 and secs >= timeout):
        outcome, msg = "timeout", ""
    elif p.returncode == 0 and re.fullmatch(r"-?\d+", first):
        outcome, msg = "normal end", first
    elif first.startswith("UB: "):
        outcome, msg = "ub", first[4:]
    else:
        outcome, msg = "error", (first or se.strip().splitlines()[-1:] or [""])[0]
    res = {"input": str(inp), "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(), "outcome": outcome,
           "message": msg, "rc": p.returncode, "seconds": round(secs, 2), "cpu_seconds": round(cpu, 2), "stdout_tail": so[-2000:],
           "stdout_sha256": hashlib.sha256(p.stdout).hexdigest(),
           "stdout_untagged_sha256": hashlib.sha256(TAG.sub("", so).encode()).hexdigest(),
           "stderr_tail": se[-2000:], "cmd_cirs": cirs, "timeout": timeout}
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=1) + "\n")
    print(f"{inp.name}\t{outcome}\t{msg}\t{res['seconds']}s")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

"""Native results of a crate with one process per job (post hoc, for reporting).

    python3 -m veriforch.c2rust.fresh <run dir> <version>...

The loop's runner calls the crate on every job inside ONE driver process. That is exact for a pure crate (every
crate the Aeneas extraction accepts: no global state), but not for a version that keeps C's static buffers as
global state (e.g. a thread_local): there one job sees what the previous jobs left. The C reference runs one call
per fresh process. This module measures such versions the same way: the driver is started once per job, inside one
run1.sh job, and the version's round cases are judged as the loop judges native results. Written to
v<k>/fresh_native.json; nothing is sent to a model.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

from . import cref, rustrun
from .loop import judge

_WORKER = r'''
import json, subprocess, sys
exe, jobs_path, out_path, limit_ms = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
jobs = open(jobs_path).read().splitlines()
one = jobs_path + ".one"
with open(out_path, "w") as out:
    for k, line in enumerate(jobs):
        open(one, "w").write(line + "\n")
        try:
            p = subprocess.run([exe, one, "0", limit_ms], capture_output=True, text=True, timeout=60)
            text, rc = p.stdout, p.returncode
        except subprocess.TimeoutExpired:
            text, rc = "", -9
        out.write(json.dumps({"k": k, "stdout": text[-20000:], "rc": rc}) + "\n")
'''


def fresh_native(src: Path, jobs: list[dict], case_seconds: int = rustrun.CASE_SECONDS) -> list[dict]:
    w = rustrun.workdir(src)
    err = rustrun._native_build(w, src) if not (w / "native_build.ok").exists() else None
    if err:
        raise RuntimeError(f"native build fails: {err}")
    b = w / "fresh"
    b.mkdir(exist_ok=True)
    (b / "jobs.txt").write_text(rustrun._job_lines(jobs))
    (b / "worker.py").write_text(_WORKER)
    exe = w / "target" / "debug" / "vo_driver"
    p = rustrun._job([sys.executable, "-I", "-B", b / "worker.py", exe, b / "jobs.txt", b / "out.jsonl",
                      case_seconds * 1000], b, mem_gib=32, timeout=600 + len(jobs) * 2)
    if p.returncode != 0 or not (b / "out.jsonl").exists():
        raise RuntimeError(f"fresh worker failed (exit {p.returncode}): {rustrun._text(p.stderr)[-800:]}")
    res = []
    for line in (b / "out.jsonl").read_text().splitlines():
        r = json.loads(line)
        got = None
        for ln in r["stdout"].splitlines():
            f = ln.split(" ")
            if f[0] == "VOCASE":
                got = {"m": [int(f[3]), int(f[4])]} if f[2] == "m" else {"c": rustrun._parse_dump(f[3:])}
            elif f[0] == "VOPANIC" and got is None:
                got = {"panic": json.loads(ln.split(" ", 2)[2])}
            elif f[0] == "VOTIMEOUT":
                got = {"timeout": True}
        res.append(got or {"crash": f"exit {r['rc']}"})
    return res


def measure(run_dir: Path, version: int) -> dict:
    src = run_dir / f"v{version}" / "rust"
    cases = json.loads((cref.CASES / "round.json").read_text())
    ref = cref.cached_reference(cases)
    jobs, index = [], {}
    for c in cases:
        for kind, key in (("m", cref.mkey(c["pattern"], c["text"])), ("c", cref.ckey(c["pattern"]))):
            if key not in index:
                index[key] = len(jobs)
                jobs.append({"kind": kind, "pattern": c["pattern"], "text": c["text"] if kind == "m" else ""})
    res = fresh_native(src, jobs)
    kinds, passed = {}, 0
    for c in cases:
        r = {"m": {"native": res[index[cref.mkey(c["pattern"], c["text"])]]},
             "c": {"native": res[index[cref.ckey(c["pattern"])]]}}
        d = judge(c, ref[c["id"]], r)
        passed += not d
        for kd in {x["kind"] for x in d}:
            kinds[kd] = kinds.get(kd, 0) + 1
    out = {"version": version, "n": len(cases), "pass": passed, "kinds": kinds,
           "method": "native, one driver process per job"}
    (run_dir / f"v{version}" / "fresh_native.json").write_text(json.dumps(out, indent=1))
    return out


def main(argv: list[str]) -> int:
    run_dir = Path(argv[0])
    for v in argv[1:]:
        print(json.dumps(measure(run_dir, int(v))))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

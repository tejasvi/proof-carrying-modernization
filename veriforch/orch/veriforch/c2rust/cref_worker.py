"""One shard of cirrun reference jobs (run by cref.py inside scripts/run1.sh; standard library only).

    python3 -I -B cref_worker.py JOBS.json OUT.jsonl CIRRUN LIB.cir HARNESS.cir SECONDS

JOBS.json: [{"key", "kind": "m" | "c" | "u", "pattern": hex, "text": hex}]. Each job is one cirrun process:
`re_match` in LIB.cir with --show (the length comes back through the pointer argument); `vo_compile` in HARNESS.cir
with CIR_TRACE set (the dump is the last loop head's vo_dump); or, for a case cirrun reports as UB, `re_match` with
CIR_TRACE set to find where the UB happens. One JSON line per job is appended to OUT.jsonl as soon
as it is known, so a killed shard keeps its finished jobs.
"""
import json
import os
import re
import subprocess
import sys


def arg(hexs: str) -> str:
    bs = bytes.fromhex(hexs)
    return "&[" + ",".join(str(b - 256 if b >= 128 else b) for b in bs + b"\0") + "]"


def run_match(cirrun, lib, job, seconds):
    p = subprocess.run([cirrun, "--show", lib, "re_match", arg(job["pattern"]), arg(job["text"]), "&0"],
                       capture_output=True, text=True, timeout=seconds)
    lines = p.stdout.splitlines()
    if p.returncode != 0 or not lines:
        return {"error": f"cirrun exit {p.returncode}: {(p.stderr or p.stdout)[-500:]}"}
    if lines[0].startswith("UB: "):
        return {"ub": lines[0][4:]}
    mo = re.fullmatch(r"(-?\d+)", lines[0].strip())
    mo2 = re.fullmatch(r"args \S+ \S+ (-?\d+)", lines[1].strip()) if len(lines) > 1 else None
    if not mo or not mo2:
        return {"error": "unexpected cirrun output: " + p.stdout[-500:]}
    return {"ret": int(mo.group(1)), "len": int(mo2.group(1))}


def run_compile(cirrun, harness, job, seconds):
    p = subprocess.run([cirrun, harness, "vo_compile", arg(job["pattern"])], capture_output=True, text=True,
                       timeout=seconds, env=dict(os.environ, CIR_TRACE="1"))
    lines = p.stdout.splitlines()
    if p.returncode != 0 or not lines:
        return {"error": f"cirrun exit {p.returncode}: {(p.stderr or p.stdout)[-500:]}"}
    if lines[0].startswith("UB: "):
        return {"ub": lines[0][4:]}
    dump = None
    for line in p.stderr.splitlines():
        if line.startswith("@LOOP") and " vo_end=" in line:
            mo = re.search(r"\bvo_dump=\[([-\d,]*)\]", line)
            if mo:
                dump = [int(x) for x in mo.group(1).split(",")]
    if lines[0].strip() not in ("0", "1") or dump is None or len(dump) != 130:
        return {"error": "unexpected cirrun output: " + p.stdout[-300:] + p.stderr[-300:]}
    return {"ok": lines[0].strip() == "1", "objs": [dump[3 * j:3 * j + 3] for j in range(30)], "ccl_buf": dump[90:]}


def run_ubkind(cirrun, lib, job, seconds):
    """Where re_match's UB happens: the last loop head before it (matchstar's backward loop has `prepoint`,
    matchpattern's do-while has `pre`)."""
    p = subprocess.run([cirrun, lib, "re_match", arg(job["pattern"]), arg(job["text"]), "&0"],
                       capture_output=True, text=True, timeout=seconds, env=dict(os.environ, CIR_TRACE="1"))
    if not p.stdout.startswith("UB: "):
        return {"error": "not UB on the traced run: " + p.stdout[-200:]}
    last = ([l for l in p.stderr.splitlines() if l.startswith("@LOOP")] or [""])[-1]
    names = set(re.findall(r"(\w+)=", last))
    kind = ("matchstar: text-- before the start of the text" if "prepoint" in names else
            "matchpattern: &pattern[2] past the end of re_compiled" if "pre" in names else "other")
    return {"ubkind": kind, "last_loop": last[:300]}


def main():
    jobs_path, out_path, cirrun, lib, harness, seconds = sys.argv[1:7]
    seconds = int(seconds)
    with open(jobs_path) as f:
        jobs = json.load(f)
    done = set()
    if os.path.exists(out_path):
        with open(out_path) as f:
            for line in f:
                try:
                    done.add(json.loads(line)["key"])
                except (ValueError, KeyError):
                    pass
    with open(out_path, "a") as out:
        for job in jobs:
            if job["key"] in done:
                continue
            try:
                r = (run_match(cirrun, lib, job, seconds) if job["kind"] == "m" else
                     run_ubkind(cirrun, lib, job, seconds) if job["kind"] == "u" else
                     run_compile(cirrun, harness, job, seconds))
            except subprocess.TimeoutExpired:
                r = {"error": f"timeout: cirrun ran longer than {seconds} s"}
            out.write(json.dumps({"key": job["key"], "result": r}) + "\n")
            out.flush()


if __name__ == "__main__":
    main()

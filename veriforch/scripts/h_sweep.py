"""Pre-registration H, part one: the source-level UB sweep of the selected entry points (PREREG_H_v1.md, "Part one").

    python3 -I -B h_sweep.py PLAN_JSON OUT_DIR [--jobs N]

PLAN_JSON: {"vo_cirrun": path, "locator": path, "deadline_utc": "2026-10-27T03:00:00Z", "core_h_cap": 60,
"entries": [{"entry_point", "project", "status": "sweep" | "no public corpus", "toml", "variant_dir", "corpus_dir",
"native_prefix"}, ...]} in processing order.

For each entry point with a corpus, every input of corpus_dir/MANIFEST.tsv runs on the pinned semantics
(h_cirrun1.py with vo-cirrun, 60 s wall) and on the locator (h_cirrun1.py with h-locate). The locator's result is
used only if, with its location tags removed, its outcome, message and whole stdout equal the pinned run's byte for
byte (h_locdiff.py's check, per input); otherwise the input is reported without a location ("locator failure").
Each pinned result gets a class from cirlean's message (CLASSES below): "ub" (a message that names undefined behaviour
in C), "unsupported" (a construct or library function the semantics does not model), "abort" (abort, a failed assert,
exit), "reading" (the message alone does not tell), besides "normal end", "timeout" and "error". These classes only
sort the findings; the triage classes of the report ((i) C UB: a sanitizer report or a reading citing the C clause;
(ii) model limit: the code reason and the C rule that makes the code defined; (iii) unconfirmed) are decided per
distinct finding afterwards, in TRIAGE.tsv. For each distinct (message, innermost function, site) of the classes ub,
reading, unsupported and abort, the first input reaching it (by name) runs natively on the plain, ubsan, asan and
asan-ubsan builds (h_native.py, bubblewrap).

Machine rules (main, 2026-10-25): at most N concurrent jobs (default and maximum 8), a job is dispatched only while
the 1-minute load is at most 450 and MemAvailable is at least 150 GB (H yields to Thrift T2/T3); run the driver under
`nice -n 19` (the jobs inherit it); no job starts after the deadline or once the sweep's guard log reaches the cap
minus 2 core-h. Every job runs under scripts/run1.sh with VO_GUARD_LOG = OUT_DIR/guard_partone.log.

OUT_DIR/<project>__<harness>/: cir/, loc/, native/ (one JSON per run), RESULTS.tsv (per input), DISTINCT.tsv (per
distinct finding, with the native outcomes), LOCDIFF.tsv (the locator's check per input); OUT_DIR/SUMMARY.tsv
(per entry point).
"""
from __future__ import annotations

import concurrent.futures as cf
import datetime as dt
import hashlib
import json
import os
import re
import subprocess
import sys
import threading
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PY = [sys.executable, "-I", "-B"]
VARIANTS = ["plain", "ubsan", "asan", "asan-ubsan"]
TAG = re.compile(r"⟦(call (\S+) (\S+) @(\d+):(\d+)|loop @(\d+):(\d+))⟧")

# cirlean ffab71e's messages (CIR/Semantics, CIR/Std/Models.lean) by class; the rest is "triage"
UB_EXACT = {
    "array index out of bounds", "invalid memory read", "invalid memory write", "integer overflow",
    "division by zero", "remainder by zero", "division overflow", "remainder overflow", "shift amount out of range",
    "left shift of a negative value", "left shift overflow", "float-to-integer conversion out of range",
    "float-to-integer conversion of an infinity or NaN", "abs of the minimum value", "comparison of an invalid pointer",
    "difference of unrelated pointers", "freeing a pointer not from the allocator", "member access through a null or "
    "function pointer", "unterminated C string", "cir.unreachable executed", "va_arg: argument of another type",
    "va_arg: no more variadic arguments", "va_arg: value out of range of the type", "clz/ctz of zero",
    "indirect call through a non-function pointer"}
ABORT_EXACT = {"abort() called", "assertion failure", "exit() called", "trap", "std::terminate called",
               "exception escaped a noexcept function"}
UNSUPPORTED_PREFIX = ("unsupported", "call to an unknown function", "call to an external function without a model")
UNSUPPORTED_SUB = ("not modelled", "outside the modelled subset")
UNSUPPORTED_EXACT = {"library model called with unexpected arguments", "strtod: unexpected arguments",
                     "not a simple operation", "realloc: element type without a size",
                     "realloc: size not a multiple of the element size", "access through an integer-valued pointer"}

_lock = threading.Lock()
_running = 0


def classify(outcome: str, msg: str) -> str:
    if outcome != "ub":
        return outcome
    if msg in UB_EXACT:
        return "ub"
    if msg in ABORT_EXACT:
        return "abort"
    if msg.startswith(UNSUPPORTED_PREFIX) or any(s in msg for s in UNSUPPORTED_SUB) or msg in UNSUPPORTED_EXACT:
        return "unsupported"
    return "reading"


def strip_tags(msg: str) -> str:
    return TAG.sub("", msg)


def locate(msg: str, units: dict[str, str], entry: str = "LLVMFuzzerTestOneInput") -> dict:
    """Innermost program function of a located message, the site in it (innermost loop or call of a model or external
    function), and the backtrace."""
    frames = [m.group(0) for m in TAG.finditer(msg)]
    fn, site = entry, "body"
    for m in TAG.finditer(msg):
        if m.group(2) == "fn":
            fn, site = m.group(3), "body"
        elif m.group(2) in ("model", "extern", "unknown"):
            site = f"call {m.group(3)} @{m.group(4)}:{m.group(5)}"
            break
        elif m.group(6):
            site = f"loop @{m.group(6)}:{m.group(7)}"
    floc = units.get(fn, "?")
    return {"function": fn, "file": floc.rsplit(":", 1)[0], "function_line": floc.rsplit(":", 1)[-1], "site": site,
            "backtrace": "".join(frames)}


def load_ok() -> tuple[float, float]:
    load1 = float(Path("/proc/loadavg").read_text().split()[0])
    mem = next(int(ln.split()[1]) for ln in Path("/proc/meminfo").read_text().splitlines()
               if ln.startswith("MemAvailable:")) / 1048576
    return load1, mem


def core_h(guard_log: Path) -> float:
    if not guard_log.exists():
        return 0.0
    tot = 0.0
    for ln in guard_log.read_text().splitlines():
        m = re.search(r"guard exits, total ([0-9.]+) core-h", ln)
        if m:
            tot += float(m.group(1))
    return tot


class Gate:
    def __init__(self, jobs: int, deadline: dt.datetime, cap: float, guard_log: Path):
        self.jobs, self.deadline, self.cap, self.guard_log = jobs, deadline, cap, guard_log
        self.stopped = ""

    def acquire(self) -> bool:
        global _running
        while True:
            if dt.datetime.now(dt.timezone.utc) >= self.deadline:
                self.stopped = "deadline"
                return False
            if core_h(self.guard_log) >= self.cap - 2:
                self.stopped = "core-h cap"
                return False
            load1, mem = load_ok()
            with _lock:
                if load1 <= 450 and mem >= 150 and _running < self.jobs:
                    _running += 1
                    return True
            time.sleep(15)

    def release(self) -> None:
        global _running
        with _lock:
            _running -= 1


def run_py(gate: Gate, args: list[str], env: dict) -> int:
    if not gate.acquire():
        return -1
    try:
        return subprocess.run(PY + args, env=env, capture_output=True, timeout=3600, check=False).returncode
    finally:
        gate.release()


def sweep_entry(e: dict, plan: dict, out: Path, gate: Gate, pool: cf.ThreadPoolExecutor, env: dict) -> dict:
    d = out / f"{e['project']}__{e['entry_point']}"
    for sub in ("cir", "loc", "native", "work"):
        (d / sub).mkdir(parents=True, exist_ok=True)
    man = [ln.split("\t") for ln in (Path(e["corpus_dir"]) / "MANIFEST.tsv").read_text().splitlines()[1:]]
    inputs = [(n, int(b), h) for n, b, h in man]
    units = {u["name"]: u["loc"] for u in json.loads((Path(e["variant_dir"]) / "units.json").read_text())}

    def cir(n: str, tool: str, sub: str) -> dict:
        res = d / sub / f"{n}.json"
        if not res.exists():
            run_py(gate, [str(HERE / "h_cirrun1.py"), plan[tool], e["toml"], e["variant_dir"],
                          str(Path(e["corpus_dir"]) / "inputs" / n), str(res), "--timeout", "60"], env)
        return json.loads(res.read_text()) if res.exists() else {"outcome": "not run", "message": gate.stopped}

    pinned = dict(zip([n for n, _, _ in inputs], pool.map(lambda x: cir(x[0], "vo_cirrun", "cir"), inputs)))
    located = dict(zip([n for n, _, _ in inputs], pool.map(lambda x: cir(x[0], "locator", "loc"), inputs)))
    rows, distinct, ldiff = [], {}, []
    for n, b, h in inputs:
        r, lr = pinned[n], located[n]
        cls = classify(r["outcome"], r.get("message", ""))
        why = [k for k, ok in (("outcome", r.get("outcome") == lr.get("outcome")),
                               ("message", r.get("message") == strip_tags(lr.get("message", ""))),
                               ("stdout", r.get("stdout_sha256") is not None
                                and r.get("stdout_sha256") == lr.get("stdout_untagged_sha256"))) if not ok]
        lstatus = "equal" if not why else "locator failure: " + ",".join(why) + " differ"
        ldiff.append([n, r.get("outcome", ""), r.get("message", ""), lr.get("outcome", ""),
                      strip_tags(lr.get("message", "")), lstatus])
        loc = {"function": "", "file": "", "function_line": "", "site": "", "backtrace": ""}
        if not why and r["outcome"] == "ub":
            loc = locate(lr["message"], units)
        rows.append([n, str(b), h, r["outcome"], cls, r.get("message", ""), loc["function"], loc["file"],
                     loc["site"], lstatus, str(r.get("seconds", "")), loc["backtrace"]])
        if cls in ("ub", "reading", "unsupported", "abort"):
            key = (r["message"], loc["function"], loc["site"])
            distinct.setdefault(key, []).append(n)
    # native re-runs: the first input (by name) of each distinct finding, the four builds
    jobs = []
    for key, ns in distinct.items():
        n = sorted(ns)[0]
        for v in VARIANTS:
            res = d / "native" / f"{n}.{v}.json"
            if not res.exists():
                jobs.append((n, v, res))
    list(pool.map(lambda j: run_py(gate, [str(HERE / "h_native.py"), "run", f"{e['native_prefix']}.{j[1]}",
                                          str(Path(e["corpus_dir"]) / "inputs" / j[0]), str(j[2]),
                                          str(d / "work" / f"{j[0]}.{j[1]}"), "--timeout", "60"], env), jobs))
    drows = []
    for (msg, fn, site), ns in sorted(distinct.items()):
        n = sorted(ns)[0]
        nat = []
        for v in VARIANTS:
            p = d / "native" / f"{n}.{v}.json"
            nat.append((json.loads(p.read_text())["report"] or "silent") if p.exists() else "not run")
        drows.append([msg, classify("ub", msg), fn, site, str(len(ns)), n, *nat])
    (d / "LOCDIFF.tsv").write_text("\n".join("\t".join(x) for x in [["input", "pin_outcome", "pin_message",
                                   "loc_outcome", "loc_message_untagged", "verdict"]] + ldiff) + "\n")
    hdr = ["input", "bytes", "sha256", "outcome", "class", "message", "function", "file", "site", "locator",
           "seconds", "backtrace"]
    (d / "RESULTS.tsv").write_text("\n".join("\t".join(x) for x in [hdr] + rows) + "\n")
    dh = ["message", "class", "function", "site", "inputs", "first_input", *[f"native_{v}" for v in VARIANTS]]
    (d / "DISTINCT.tsv").write_text("\n".join("\t".join(x) for x in [dh] + drows) + "\n")
    counts = {}
    for r in rows:
        counts[r[4]] = counts.get(r[4], 0) + 1
    cpu = sum(json.loads(f.read_text()).get("cpu_seconds", 0.0) for sub in ("cir", "loc", "native")
              for f in (d / sub).glob("*.json"))
    return {"entry_point": e["entry_point"], "project": e["project"], "inputs": len(rows), **counts,
            "distinct_findings": len(drows), "cpu_core_h": round(cpu / 3600, 4)}


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    plan = json.loads(Path(argv[1]).read_text())
    out = Path(argv[2]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    jobs = int(argv[argv.index("--jobs") + 1]) if "--jobs" in argv else 8
    guard = out / "guard_partone.log"
    env = dict(os.environ, VO_GUARD_LOG=str(guard))
    deadline = dt.datetime.fromisoformat(plan["deadline_utc"].replace("Z", "+00:00"))
    gate = Gate(min(jobs, 8), deadline, float(plan["core_h_cap"]), guard)
    summary = []
    with cf.ThreadPoolExecutor(max_workers=min(jobs, 8)) as pool:
        for e in plan["entries"]:
            if e["status"] != "sweep":
                summary.append({"entry_point": e["entry_point"], "project": e["project"], "inputs": 0,
                                "note": e["status"]})
                continue
            t0 = time.time()
            s = sweep_entry(e, plan, out, gate, pool, env)
            s["wall_s"] = round(time.time() - t0)
            summary.append(s)
            print(json.dumps(s), flush=True)
    keys = ["entry_point", "project", "inputs", "normal end", "ub", "reading", "unsupported", "abort", "timeout",
            "error", "not run", "distinct_findings", "cpu_core_h", "wall_s", "note"]
    lines = ["\t".join(keys)] + ["\t".join(str(s.get(k, "")) for k in keys) for s in summary]
    lines.append(f"# core-h (guard_partone.log): {core_h(guard):.3f}; stopped: {gate.stopped or 'no'}")
    (out / "SUMMARY.tsv").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))

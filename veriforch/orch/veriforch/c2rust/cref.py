"""The C reference for tiny-regex-c (f2632c6) on cirlean's semantics, and a native cross-check.

    python3 -m veriforch.c2rust.cref [round heldout ...]    # results for the case sets; writes REFERENCE.md/.json

* re_match: `cirrun --show re.cir re_match P T &0` once per case: the module's initial memory (zeroed statics),
  one call, the result and the final *matchlength, or `UB: <reason>`;
* re_compile: `vo_compile` of vo_harness.c (the library included, plus a dump of the two static arrays, read by
  CIR_TRACE at its last loop head), once per distinct pattern;
* native: the same jobs on a gcc build (-O0, UBSan) of vo_native.c, one forked child per job. Only a cross-check
  of cirrun: the reference is cirrun's result.

C strings are passed as char arrays: each byte as a signed char, then the terminator. Results are cached per cirlean
pin in runs/c2rust/tiny-regex-c/c/ref_<pin>.jsonl (append-only; a job is a pure function of its inputs).
Every cirrun, clang and gcc job runs under scripts/run1.sh.
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path

VO_ROOT = Path(__file__).resolve().parents[3]
RUN1 = VO_ROOT / "scripts" / "run1.sh"
TRX = VO_ROOT / "runs" / "c2rust" / "tiny-regex-c"
CDIR = TRX / "c"
CASES = TRX / "cases"
CIRLEAN_PIN = os.environ.get("VO_C2RUST_CIRLEAN", "739fb2c")
CIRRUN = VO_ROOT / "deps" / f"cirlean-{CIRLEAN_PIN}" / ".lake" / "build" / "bin" / "cirrun"
CLANG = Path("/home/user/cirlean_work/toolchain/upstream-4955d32b/bin/clang")
GUARD_LOG = TRX / "guard.log"
CASE_SECONDS = 60
RETRY_SECONDS = 1800          # a case cirrun did not finish in CASE_SECONDS is run once more with this limit


def _run1(cmd: list, *, t: int, m: int, c: float, cwd: Path = CDIR, env: dict | None = None,
          capture: bool = True) -> subprocess.CompletedProcess:
    full = [str(RUN1), "-t", str(t), "-m", str(m), "-c", f"{c:.2f}", "-l", str(GUARD_LOG), "--"]
    if env:
        full += ["env"] + [f"{k}={v}" for k, v in env.items()]
    return subprocess.run(full + [str(x) for x in cmd], cwd=cwd, stdin=subprocess.DEVNULL,
                          capture_output=capture, text=True)


def ensure_build() -> dict:
    """re.cir (the library alone), vo_harness.cir, and the native cross-check binary; rebuilt when a source
    changes. Returns the source hashes."""
    srcs = [CDIR / "src" / "re.c", CDIR / "src" / "re.h", CDIR / "vo_harness.c", CDIR / "vo_native.c"]
    h = hashlib.sha256(b"".join(p.read_bytes() for p in srcs) + CIRLEAN_PIN.encode()).hexdigest()[:16]
    stamp = CDIR / "build.stamp"
    if stamp.exists() and stamp.read_text().strip() == h:
        return {"build": h}
    steps = [
        [CLANG, f"-I{CDIR / 'src'}", "-fclangir", "-emit-cir", "-Xclang", "-fno-clangir-call-conv-lowering",
         CDIR / "src" / "re.c", "-o", CDIR / "re.cir"],
        [CLANG, f"-I{CDIR / 'src'}", "-fclangir", "-emit-cir", "-Xclang", "-fno-clangir-call-conv-lowering",
         CDIR / "vo_harness.c", "-o", CDIR / "vo_harness.cir"],
        ["/usr/bin/gcc", "-O0", "-g", "-std=c99", "-D_DEFAULT_SOURCE", "-fsanitize=undefined",
         "-fno-sanitize-recover=undefined", f"-I{CDIR}", CDIR / "vo_native.c", "-o", CDIR / "vo_native"],
    ]
    for cmd in steps:
        p = _run1(cmd, t=300, m=8, c=0.1)
        if p.returncode != 0:
            raise RuntimeError(f"build step failed: {' '.join(map(str, cmd))}\n{p.stdout[-2000:]}{p.stderr[-2000:]}")
    stamp.write_text(h + "\n")
    return {"build": h}


def mkey(pattern: str, text: str) -> str:
    return f"m:{pattern}:{text}"


def ckey(pattern: str) -> str:
    return f"c:{pattern}"


def ukey(pattern: str, text: str) -> str:
    return f"u:{pattern}:{text}"


def _cache_path() -> Path:
    return CDIR / f"ref_{CIRLEAN_PIN}.jsonl"


def load_cache() -> dict:
    out = {}
    p = _cache_path()
    if p.exists():
        for line in p.read_text().splitlines():
            if line.strip():
                r = json.loads(line)
                out[r["key"]] = r["result"]
    return out


def _shards_allowed(want: int) -> int:
    """3 jobs always; more only while the 1-minute load is <= 450 and MemAvailable >= 150 GB."""
    load = float(Path("/proc/loadavg").read_text().split()[0])
    avail = 0
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            avail = int(line.split()[1]) // (1 << 20)
    return want if load <= 450 and avail >= 150 else min(want, 3)


def run_jobs(jobs: list[dict], shards: int = 8, seconds: int = CASE_SECONDS, force: bool = False) -> None:
    """cirrun on the jobs that are not cached yet (all of them with `force`), in parallel shards; results appended
    to the cache (a later line replaces an earlier one)."""
    cache = load_cache()
    todo = [j for j in jobs if force or j["key"] not in cache]
    if not todo:
        return
    k = max(1, min(_shards_allowed(shards), (len(todo) + 199) // 200 if seconds == CASE_SECONDS else len(todo)))
    batch = CDIR / "batches" / time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    batch.mkdir(parents=True, exist_ok=True)
    procs = []
    for s in range(k):
        part = todo[s::k]
        (batch / f"jobs{s}.json").write_text(json.dumps(part))
        secs = 600 + len(part) * (4 if seconds == CASE_SECONDS else seconds + 30)
        cmd = [str(RUN1), "-t", str(secs), "-m", "16", "-c", f"{max(0.25, 1.3 * secs / 3600):.2f}", "-l",
               str(GUARD_LOG), "--", sys.executable, "-I", "-B", str(Path(__file__).with_name("cref_worker.py")),
               str(batch / f"jobs{s}.json"), str(batch / f"out{s}.jsonl"), str(CIRRUN), str(CDIR / "re.cir"),
               str(CDIR / "vo_harness.cir"), str(seconds)]
        log = open(batch / f"log{s}.txt", "w")
        procs.append((subprocess.Popen(cmd, cwd=CDIR, stdin=subprocess.DEVNULL, stdout=log, stderr=log), log))
    for p, log in procs:
        p.wait()
        log.close()
    with open(_cache_path(), "a") as out:
        for s in range(k):
            f = batch / f"out{s}.jsonl"
            if f.exists():
                for line in f.read_text().splitlines():
                    if line.strip():
                        out.write(line.rstrip() + "\n")


def jobs_for(cases: list[dict]) -> list[dict]:
    jobs, seen = [], set()
    for c in cases:
        for key, kind in ((mkey(c["pattern"], c["text"]), "m"), (ckey(c["pattern"]), "c")):
            if key not in seen:
                seen.add(key)
                jobs.append({"key": key, "kind": kind, "pattern": c["pattern"], "text": c["text"]})
    return jobs


def reference(cases: list[dict]) -> dict:
    """{case id: {"match": R, "compile": C}} (R: {"ret", "len"} | {"ub", "ubkind"} | {"error"}; C: {"ok", "objs",
    "ccl_buf"} | {"ub"} | {"error"}). A job that timed out at CASE_SECONDS runs once more with RETRY_SECONDS; for
    each UB case a traced run names where the UB happens (`ubkind`)."""
    ensure_build()
    jobs = jobs_for(cases)
    run_jobs(jobs)
    cache = load_cache()
    slow = [j for j in jobs if cache.get(j["key"], {}).get("error", "").startswith(
        f"timeout: cirrun ran longer than {CASE_SECONDS} s")]
    if slow:
        run_jobs(slow, seconds=RETRY_SECONDS, force=True)
        cache = load_cache()
    ub = [{"key": ukey(c["pattern"], c["text"]), "kind": "u", "pattern": c["pattern"], "text": c["text"]}
          for c in cases if "ub" in cache.get(mkey(c["pattern"], c["text"]), {})]
    run_jobs(list({j["key"]: j for j in ub}.values()))
    cache = load_cache()
    out = {}
    for c in cases:
        m = dict(cache.get(mkey(c["pattern"], c["text"]), {"error": "not run"}))
        if "ub" in m:
            m["ubkind"] = cache.get(ukey(c["pattern"], c["text"]), {}).get("ubkind", "unknown")
        out[c["id"]] = {"match": m, "compile": cache.get(ckey(c["pattern"]), {"error": "not run"})}
    return out


def cached_reference(cases: list[dict]) -> dict:
    """reference() from the cache only (nothing is run): a job not in the cache is {"error": "not run"}."""
    cache = load_cache()
    out = {}
    for c in cases:
        m = dict(cache.get(mkey(c["pattern"], c["text"]), {"error": "not run"}))
        if "ub" in m:
            m["ubkind"] = cache.get(ukey(c["pattern"], c["text"]), {}).get("ubkind", "unknown")
        out[c["id"]] = {"match": m, "compile": cache.get(ckey(c["pattern"]), {"error": "not run"})}
    return out


def status(r: dict) -> str:
    return "ub" if "ub" in r else "error" if "error" in r else "ok"


# -- native cross-check -------------------------------------------------------------------------------------------

def native(cases: list[dict]) -> dict:
    """The jobs on the native build: {key: {"ret", "len"} | {"ok", "objs", "ccl_buf"} | {"crash": sig} |
    {"exit": status}}."""
    ensure_build()
    jobs = jobs_for(cases)
    batch = CDIR / "batches" / ("native_" + time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()))
    batch.mkdir(parents=True, exist_ok=True)
    lines = [f"{i} {j['kind']} {j['pattern'] or '-'}" + (f" {j['text'] or '-'}" if j["kind"] == "m" else "")
             for i, j in enumerate(jobs)]
    (batch / "jobs.txt").write_text("\n".join(lines) + "\n")
    p = _run1([CDIR / "vo_native", batch / "jobs.txt"], t=1800, m=8, c=0.6,
              env={"UBSAN_OPTIONS": "exitcode=99:print_stacktrace=0:halt_on_error=1"})
    (batch / "out.txt").write_text(p.stdout)
    out = {}
    for line in p.stdout.splitlines():
        f = line.split()
        if len(f) < 3 or not f[0].isdigit():
            continue
        key = jobs[int(f[0])]["key"]
        if f[1] == "m":
            out[key] = {"ret": int(f[2]), "len": int(f[3])}
        elif f[1] == "c":
            d = [int(x) for x in f[3:]]
            out[key] = {"ok": f[2] == "1", "objs": [d[3 * j:3 * j + 3] for j in range(30)], "ccl_buf": d[90:]}
        elif f[1] in ("crash", "exit"):
            out[key] = {f[1]: int(f[2])}
    return out


def _same(ref: dict, nat: dict) -> bool:
    if "ret" in ref:
        return nat.get("ret") == ref["ret"] and nat.get("len") == ref["len"]
    if "ok" in ref:
        return nat.get("ok") == ref["ok"] and (not ref["ok"] or (nat.get("objs"), nat.get("ccl_buf")) ==
                                              (ref["objs"], ref["ccl_buf"]))
    return False


def summarize(sets: list[str]) -> dict:
    summary = {"cirlean": CIRLEAN_PIN, "sets": {}}
    md = [f"# tiny-regex-c f2632c6: C reference on cirlean {CIRLEAN_PIN} (cirrun, one call per case from the "
          "initial memory)", ""]
    for name in sets:
        cases = json.loads((CASES / f"{name}.json").read_text())
        ref = reference(cases)
        nat = native(cases)
        by_src: dict = {}
        ub_cases, disagree, errors = [], [], []
        for c in cases:
            r = ref[c["id"]]
            s = by_src.setdefault(c["source"], {"cases": 0, "ok": 0, "ub": 0, "error": 0})
            s["cases"] += 1
            st = status(r["match"])
            s[st] += 1
            if st == "ub":
                ub_cases.append({"id": c["id"], "pattern": c["pattern"], "text": c["text"], "ub": r["match"]["ub"],
                                 "ubkind": r["match"]["ubkind"], "native": nat.get(mkey(c["pattern"], c["text"]))})
            elif st == "error":
                errors.append({"id": c["id"], "error": r["match"]["error"][:300]})
            elif not _same(r["match"], nat.get(mkey(c["pattern"], c["text"]), {})):
                disagree.append({"id": c["id"], "kind": "match", "cirrun": r["match"],
                                 "native": nat.get(mkey(c["pattern"], c["text"]))})
            if status(r["compile"]) == "ok" and not _same(r["compile"], nat.get(ckey(c["pattern"]), {})):
                disagree.append({"id": c["id"], "kind": "compile", "cirrun": r["compile"],
                                 "native": nat.get(ckey(c["pattern"]))})
            if status(r["compile"]) != "ok":
                errors.append({"id": c["id"], "compile": r["compile"]})
        ub_kinds: dict = {}
        for u in ub_cases:
            ub_kinds[u["ubkind"]] = ub_kinds.get(u["ubkind"], 0) + 1
        expect_fail = []
        for c in cases:
            pe = c.get("project_expect")
            r = ref[c["id"]]["match"]
            if pe and status(r) == "ok":
                got_match = r["ret"] != -1
                if got_match != pe["match"] or (pe["match"] and r["len"] != pe["length"]):
                    expect_fail.append({"id": c["id"], "expect": pe, "cirrun": r})
        summary["sets"][name] = {"cases": len(cases), "by_source": by_src, "ub_kinds": ub_kinds, "ub": ub_cases,
                                 "errors": errors, "native_disagreements": disagree,
                                 "project_expectation_failures": expect_fail}
        md += [f"## {name}: {len(cases)} cases", "",
               "| source | cases | defined | UB | cirrun error/timeout |", "|---|---|---|---|---|"]
        md += [f"| {k} | {v['cases']} | {v['ok']} | {v['ub']} | {v['error']} |" for k, v in sorted(by_src.items())]
        md += ["", "UB (cirrun: pointer arithmetic out of bounds), by where it happens: "
               + (", ".join(f"{k} ({n})" for k, n in sorted(ub_kinds.items())) or "none"),
               f"Native build (gcc -O0, UBSan, fork per case) vs cirrun on the defined cases: {len(disagree)} "
               "disagreements", f"Project expectations (tests/test1.c) not met by the C itself on defined cases: "
               + (", ".join(e["id"] for e in expect_fail) or "none"), ""]
    (TRX / "c" / "REFERENCE.json").write_text(json.dumps(summary, indent=1))
    (TRX / "c" / "REFERENCE.md").write_text("\n".join(md) + "\n")
    return summary


def main(argv: list[str]) -> int:
    s = summarize(argv or ["round", "heldout"])
    for name, v in s["sets"].items():
        print(name, v["cases"], v["by_source"], v["ub_kinds"], "native disagreements:",
              len(v["native_disagreements"]), "errors:", len(v["errors"]))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

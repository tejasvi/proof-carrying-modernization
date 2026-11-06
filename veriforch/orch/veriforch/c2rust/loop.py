"""Translate tiny-regex-c (f2632c6) to Rust with a model and repair it from counterexamples only.

    python3 -m veriforch.c2rust.loop ARM [--budget D] [--attempts N] [--seed S]

ARM is `guided` (the C sources + equiv-lean's style guide, styleguide_rust_c_v1.1.md, verbatim) or `plain` (the C
sources + the agreed interface: the API block of that guide, and what its types mean). Both arms get the same
answer format.

Each attempt is one model call. Attempt 1 asks for the translation. Each later attempt sends back the current
translation and one of two things: the build's message (cargo, Charon, Aeneas, the interface check, Lean), or up
to three counterexamples. A counterexample is an input on which the translation's result differs from the C
function's result under cirlean's semantics (cirrun), with both results. Nothing else goes back: no hints about
causes, no human edits.

A version passes a set of cases when, natively and in its Aeneas extraction evaluated in Lean,
* re_match returns cirrun's (return value, *matchlength) on every case where the C has defined behaviour, and
  re_compile returns the C's two static arrays (None for NULL) for every pattern of those cases;
* re_match and re_compile return normally (no panic, no Aeneas failure, no time-out) on every case, including
  those where cirrun reports undefined behaviour (there the result itself is not compared).
Cases where cirrun gave no result (time-out) are left out. The set of record is `round` (cases.py, seed 1, plus
the counterexamples found later); a version that passes it is checked on `heldout`, and the run ends when a
version passes both, or when the attempts or the budget run out.

Records under runs/c2rust/tiny-regex-c/<arm>/ (seeds > 1: <arm>_s<N>/):
* v<k>/rust/src/lib.rs (and the model's Cargo.toml, unused), v<k>/attempt.json (feedback sent, build result,
  counts, discrepancies by kind, counterexamples chosen), v<k>/failing.jsonl;
* llm/: the ledger and full transcripts (system prompt once, every user prompt and answer);
* summary.json, log.txt.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
from collections import Counter
from pathlib import Path

from ..llm import LLM, BudgetExceeded, LLMError
from ..modernize.loop import files_text, parse_files
from . import cref, rustrun

TRX = cref.TRX
GUIDE = TRX / "guide" / "styleguide_rust_c_v1.1.md"
GUIDE_SHA256 = "def9ffcbb1012ba8bb730ad8334211cd222095269d5d02cf497ac4af8752641a"
EXPECTED = ["src/lib.rs"]
ANSWER_FORMAT = ("Answer with the complete crate. For each file write a line `FILE: <path>` followed by a fenced code "
                 "block holding the whole file. Files: `src/lib.rs` (a `Cargo.toml` is optional: the crate is built "
                 "with no dependencies).")


# ---------------------------------------------------------------------------------------------- prompts

def _guide_text() -> str:
    import hashlib
    text = GUIDE.read_text()
    if hashlib.sha256(text.encode()).hexdigest() != GUIDE_SHA256:
        raise RuntimeError(f"{GUIDE} is not the recorded v1.1 (sha256 differs)")
    return text


def _api_block() -> str:
    """The guide's API code block, verbatim (the plain arm gets the interface and nothing else from the guide)."""
    g = _guide_text()
    mo = re.search(r"For tiny-regex-c \(re\.h\) this gives.*?\n\n(```rust\n.*?\n```)", g, re.S)
    if not mo:
        raise RuntimeError("API block not found in the style guide")
    return mo.group(1)


def system_prompt(arm: str) -> str:
    if arm == "guided":
        return "\n\n".join(["You translate C libraries into Rust. Follow the style guide below exactly.",
                            _guide_text(), "# Answer format", ANSWER_FORMAT])
    return "\n\n".join(["You translate C libraries into Rust.", "# Answer format", ANSWER_FORMAT])


def c_sources() -> str:
    src = cref.CDIR / "src"
    return "\n\n".join(["# C library: tiny-regex-c", "## re.h", f"```c\n{(src / 're.h').read_text()}\n```",
                        "## re.c", f"```c\n{(src / 're.c').read_text()}\n```"])


def task_text(arm: str) -> str:
    if arm == "guided":
        return c_sources() + "\n\n# Task\n\nTranslate this C library into Rust, following the style guide."
    return "\n\n".join([
        c_sources(), "# Task",
        "Translate this C library into one safe Rust library crate (`src/lib.rs`) with the same observable behaviour "
        "as the C code on x86-64 Linux, and exactly this public interface:", _api_block(),
        "A C string argument is passed as a byte slice holding the bytes before its terminating NUL (the slice never "
        "contains 0). The `int*` out-parameter is returned instead: re_matchp and re_match return (the C function's "
        "return value, the final *matchlength). re_compile returns None where the C function returns NULL. "
        "The functions must return normally (no panic) on every input. re_print is not needed."])


# ---------------------------------------------------------------------------------------------- comparison

def bytes_lit(h: str) -> str:
    out = []
    for b in bytes.fromhex(h):
        c = chr(b)
        out.append({"\\": "\\\\", '"': '\\"', "\n": "\\n", "\t": "\\t", "\r": "\\r"}.get(c) or
                   (c if 0x20 <= b < 0x7F else f"\\x{b:02x}"))
    return 'b"' + "".join(out) + '"'


def _show_compile(r) -> str:
    if r is None:
        return "None (NULL)"
    objs = [f"{j}: kind {o[0]}, ch {o[1]}, ccl {o[2]}" for j, o in enumerate(r["objs"]) if any(o)]
    buf = r["ccl_buf"]
    last = max([i for i, b in enumerate(buf) if b] or [-1])
    return ("Some: objs [" + "; ".join(objs) + "] (the others all zero); ccl_buf "
            + (json.dumps(buf[:last + 1])[:-1] + ", then zeros]" if last >= 0 else "all zero"))


def _exec_problem(r: dict) -> str | None:
    """A result that is not a value: panic, Aeneas failure, time-out, divergence, crash."""
    for k in ("panic", "fail", "timeout", "div", "crash", "runner_error", "skipped"):
        if k in r:
            return k
    return None


def judge(case: dict, ref: dict, res: dict) -> list[dict]:
    """Discrepancies of one case's jobs: [{"kind", "job": "m" | "c", "exec": "native" | "aeneas", ...}]."""
    out = []
    m_ref, c_ref = ref["match"], ref["compile"]
    defined = cref.status(m_ref) == "ok"
    for job in ("m", "c"):
        r_ref = m_ref if job == "m" else c_ref
        if cref.status(r_ref) == "error" or (job == "c" and cref.status(r_ref) != "ok"):
            continue
        for ex in ("native", "aeneas"):
            got = res[job].get(ex)
            if got is None:
                continue
            prob = _exec_problem(got)
            if prob in ("runner_error", "skipped"):
                out.append({"kind": "harness", "job": job, "exec": ex, "got": got})
                continue
            if job == "m" and not defined:          # C UB: only "returns normally" is required
                if prob:
                    out.append({"kind": f"{prob} on a C-UB input", "job": job, "exec": ex, "got": got})
                continue
            if prob:
                out.append({"kind": prob, "job": job, "exec": ex, "got": got})
            elif job == "m":
                ret, ln = got["m"]
                if ret != m_ref["ret"]:
                    out.append({"kind": "match index", "job": job, "exec": ex, "got": got})
                elif ln != m_ref["len"]:
                    out.append({"kind": "match length" + (" (no match)" if ret == -1 else ""), "job": job,
                                "exec": ex, "got": got})
            else:
                want = {"objs": c_ref["objs"], "ccl_buf": c_ref["ccl_buf"]} if c_ref["ok"] else None
                g = got["c"]
                if (g is None) != (want is None):
                    out.append({"kind": "compile NULL" if want is None else "compile not NULL", "job": job,
                                "exec": ex, "got": got})
                elif want is not None and g["objs"] != want["objs"]:
                    out.append({"kind": "compile objects", "job": job, "exec": ex, "got": got})
                elif want is not None and g["ccl_buf"] != want["ccl_buf"]:
                    out.append({"kind": "compile class buffer", "job": job, "exec": ex, "got": got})
    return out


def counterexample_text(k: int, case: dict, ref: dict, res: dict, diffs: list[dict]) -> str:
    p, t = bytes_lit(case["pattern"]), bytes_lit(case["text"])
    jobs = sorted({d["job"] for d in diffs})
    parts = [f"## Input {k}"]
    for job in jobs:
        if job == "m":
            parts.append(f"re_match(pattern = {p}, text = {t})")
            m = ref["match"]
            parts.append("- C (cirlean's semantics): " + (f"undefined behaviour ({m['ub']})" if "ub" in m else
                                                          f"returns {m['ret']}, *matchlength = {m['len']}"))
        else:
            parts.append(f"re_compile(pattern = {p})")
            c = ref["compile"]
            parts.append("- C (cirlean's semantics): " + _show_compile(
                {"objs": c["objs"], "ccl_buf": c["ccl_buf"]} if c["ok"] else None))
        for ex, name in (("native", "your translation (cargo, debug build)"),
                         ("aeneas", "your translation's Aeneas extraction, evaluated in Lean")):
            got = res[job].get(ex)
            if got is None:
                continue
            prob = _exec_problem(got)
            if prob:
                what = {"panic": "panics", "fail": "fails (Aeneas: panic)", "timeout": "does not finish in the time "
                        "limit", "div": "diverges", "crash": "crashes"}.get(prob, prob)
                detail = got.get(prob)
                parts.append(f"- {name}: {what}" + (f": {detail}" if isinstance(detail, str) else ""))
            elif job == "m":
                parts.append(f"- {name}: returns ({got['m'][0]}, {got['m'][1]})")
            else:
                parts.append(f"- {name}: {_show_compile(got['c'])}")
    return "\n".join(parts)


# ---------------------------------------------------------------------------------------------- the loop

class Run:
    def __init__(self, arm: str, budget: float, attempts: int, seed: int = 1):
        self.arm, self.seed, self.attempts = arm, seed, attempts
        self.dir = TRX / (arm if seed == 1 else f"{arm}_s{seed}")
        self.dir.mkdir(parents=True, exist_ok=True)
        self.llm = LLM(self.dir, budget=budget)
        self.system = system_prompt(arm)
        self.task = task_text(arm)
        self.round = json.loads((cref.CASES / "round.json").read_text())
        self.heldout = json.loads((cref.CASES / "heldout.json").read_text())
        # the reference comes from cref's cache (computed by `python3 -m veriforch.c2rust.cref` beforehand); a case
        # without a cirrun result counts as no_reference
        self.ref = {**cref.cached_reference(self.round), **cref.cached_reference(self.heldout)}

    def log(self, msg: str) -> None:
        line = f"{time.strftime('%H:%M:%SZ', time.gmtime())} c2rust/{self.arm}/s{self.seed}: {msg}"
        print(line, flush=True)
        with open(self.dir / "log.txt", "a") as f:
            f.write(line + "\n")

    def evaluate(self, vdir: Path, cases: list[dict]) -> dict:
        jobs, index = [], {}
        for c in cases:
            for kind, key in (("m", cref.mkey(c["pattern"], c["text"])), ("c", cref.ckey(c["pattern"]))):
                if key not in index:
                    index[key] = len(jobs)
                    jobs.append({"kind": kind, "pattern": c["pattern"], "text": c["text"] if kind == "m" else ""})
        t0 = time.time()
        res = rustrun.run_batch(vdir / "rust", jobs)
        secs = round(time.time() - t0, 1)
        if len(res) == 1 and "status" in res[0]:
            if res[0]["status"] == "runner_error":
                raise RuntimeError(f"harness: {res[0]['stage']}: {res[0]['message']}")
            out = {"compile_error": res[0]["message"], "stage": res[0]["stage"], "seconds": secs}
            if "native" in res[0]:      # outside the verifier's language, but it runs: record how it runs
                nat = self._judge_all(cases, index, [{"native": r} for r in res[0]["native"]])
                out["native_only"] = {x: nat[x] for x in ("n", "pass", "kinds")}
            return out
        ev = self._judge_all(cases, index, res)
        ev["seconds"] = secs
        return ev

    def _judge_all(self, cases: list[dict], index: dict, res: list[dict]) -> dict:
        failing, kinds, n_defined, n_ub, n_skip = [], Counter(), 0, 0, 0
        for c in cases:
            ref = self.ref[c["id"]]
            st = cref.status(ref["match"])
            n_defined += st == "ok"
            n_ub += st == "ub"
            n_skip += st == "error"
            r = {"m": res[index[cref.mkey(c["pattern"], c["text"])]], "c": res[index[cref.ckey(c["pattern"])]]}
            diffs = judge(c, ref, r)
            if any(d["kind"] == "harness" for d in diffs):
                raise RuntimeError(f"harness: case {c['id']}: {diffs[0]['got']}")
            if diffs:
                failing.append((c, ref, r, diffs))
                for kd in {(d["kind"], d["job"]) for d in diffs}:
                    kinds[kd[0]] += 1
        disagree = sum(1 for r in res if "aeneas" in r and r["native"] != r["aeneas"])
        return {"n": len(cases), "defined": n_defined, "ub": n_ub, "no_reference": n_skip,
                "pass": len(cases) - len(failing), "failing": failing, "kinds": dict(kinds),
                "executions_disagree": disagree}

    @staticmethod
    def pick(failing: list) -> list:
        """Up to three failing cases with distinct first discrepancies, smallest inputs first."""
        chosen, seen = [], set()
        for item in sorted(failing, key=lambda it: (len(it[0]["pattern"]) + len(it[0]["text"]), it[0]["id"])):
            key = (item[3][0]["kind"], item[3][0]["job"])
            if key in seen:
                continue
            seen.add(key)
            chosen.append(item)
            if len(chosen) == 3:
                break
        return chosen

    @staticmethod
    def feedback_text(chosen: list) -> str:
        return ("# Result\n\nOn the inputs below, your translation's results differ from the C library's "
                "(byte strings are the C strings' bytes before the NUL).\n\n"
                + "\n\n".join(counterexample_text(j + 1, c, ref, r, d) for j, (c, ref, r, d) in enumerate(chosen)))

    @staticmethod
    def _failing_rows(failing: list) -> str:
        return "".join(json.dumps({"case": c, "reference": ref, "translation": r, "diffs": d}) + "\n"
                       for c, ref, r, d in failing)

    def run(self) -> dict:
        t_start = time.time()
        files: dict = {}
        feedback = ""
        regression: list[dict] = []
        history, status = [], "attempts exhausted"
        all_kinds: Counter = Counter()
        for k in range(1, self.attempts + 1):
            vdir = self.dir / f"v{k}"
            vdir.mkdir(exist_ok=True)
            user = self.task + ("" if not files else "\n\n# Your current translation\n\n" + files_text(files)
                                + "\n\n" + feedback + "\n\nGive the corrected complete translation.")
            try:
                answer = self.llm.ask_text(f"c2rust:{self.arm}:s{self.seed}:v{k}", self.system, user,
                                           effort="high", max_tokens=64000)
            except BudgetExceeded as e:
                status = f"budget: {e}"
                break
            except LLMError as e:
                self.log(f"v{k}: model call failed: {e}")
                history.append({"version": k, "model_error": str(e)})
                continue
            new = parse_files(answer)
            if "src/lib.rs" not in new:
                feedback = ("# Result\n\nThe answer lacks the file src/lib.rs in the required format (`FILE: <path>` "
                            "followed by a fenced code block).")
                history.append({"version": k, "format_error": ["src/lib.rs"]})
                self.log(f"v{k}: answer lacks src/lib.rs")
                continue
            files = new
            for p, text in files.items():
                q = vdir / "rust" / p
                q.parent.mkdir(parents=True, exist_ok=True)
                q.write_text(text)
            rec = {"version": k, "feedback_sent": feedback[:20000],
                   "model_lines": sum(1 for ln in files["src/lib.rs"].splitlines() if ln.strip())}
            try:
                ev = self.evaluate(vdir, self.round + regression)
            except RuntimeError as e:
                status = f"harness error: {e}"
                self.log(f"v{k}: {status}")
                history.append({**rec, "harness_error": str(e)[:2000]})
                break
            if "compile_error" in ev:
                rec.update({"compile_error": ev["compile_error"][:20000], "compile_stage": ev["stage"]})
                if "native_only" in ev:
                    rec["native_only"] = ev["native_only"]
                all_kinds[f"build: {ev['stage']}"] += 1
                feedback = "# Result\n\nThe translation does not build:\n```\n" + ev["compile_error"][:6000] + "\n```"
                self.log(f"v{k}: build fails at {ev['stage']}")
            else:
                rec["round"] = {x: ev[x] for x in ("n", "defined", "ub", "no_reference", "pass", "kinds",
                                                   "executions_disagree", "seconds")}
                (vdir / "failing.jsonl").write_text(self._failing_rows(ev["failing"]))
                all_kinds.update({kd: 1 for kd in ev["kinds"]})
                self.log(f"v{k}: round {ev['pass']}/{ev['n']} pass; kinds {ev['kinds']}")
                if not ev["failing"]:
                    self.ref.update(cref.cached_reference(self.heldout))
                    try:
                        final = self.evaluate(vdir, self.heldout)
                    except RuntimeError as e:
                        status = f"harness error: {e}"
                        self.log(f"v{k}: {status}")
                        history.append(rec)
                        break
                    rec["heldout"] = {x: final.get(x) for x in ("n", "defined", "ub", "no_reference", "pass",
                                                                 "kinds", "executions_disagree", "seconds",
                                                                 "compile_error")}
                    if final.get("compile_error") is None and not final["failing"]:
                        history.append(rec)
                        (vdir / "attempt.json").write_text(json.dumps(rec, indent=1))
                        status = "passed"
                        self.log(f"v{k}: passed round and heldout ({final['n']} cases)")
                        break
                    (vdir / "failing_heldout.jsonl").write_text(self._failing_rows(final.get("failing", [])))
                    all_kinds.update({kd: 1 for kd in final.get("kinds", {})})
                    self.log(f"v{k}: heldout {final['pass']}/{final['n']} pass; kinds {final['kinds']}")
                    ev = final
                chosen = self.pick(ev["failing"])
                regression += [c for c, _, _, _ in chosen if c not in self.round and c not in regression]
                feedback = self.feedback_text(chosen)
                rec["counterexamples"] = [c["id"] for c, _, _, _ in chosen]
            history.append(rec)
            (vdir / "attempt.json").write_text(json.dumps(rec, indent=1))
        dollars, calls = self.dollars()
        summary = {"target": "tiny-regex-c f2632c6", "arm": self.arm, "seed": self.seed, "status": status,
                   "c_lines": len((cref.CDIR / "src" / "re.c").read_text().splitlines()),
                   "attempts": len(history), "versions": [h["version"] for h in history],
                   "final_version": history[-1]["version"] if history and status == "passed" else None,
                   "model_lines": history[-1].get("model_lines") if history else None, "human_lines": 0,
                   "discrepancy_kinds": dict(all_kinds), "build_failures": sum(1 for h in history
                                                                              if "compile_error" in h),
                   "dollars": round(dollars, 4), "llm_calls": calls, "seconds": round(time.time() - t_start, 1),
                   "model": self.llm.model, "guide_sha256": GUIDE_SHA256 if self.arm == "guided" else None}
        (self.dir / "summary.json").write_text(json.dumps(summary, indent=1))
        if status == "passed" and self.arm == "guided" and self.seed == 1:
            self.deliver(summary["final_version"], history[-1])
        self.log(f"done: {status}; {summary['attempts']} attempts; ${summary['dollars']}")
        return summary

    def deliver(self, k: int, rec: dict) -> None:
        """The passing guided crate goes to runs/c2rust/tiny-regex-c/rust/ for equiv-lean's proof, with the inputs
        on which the C has undefined behaviour (Bad) and an interface note. Files are overwritten one by one."""
        dst = TRX / "rust"
        (dst / "src").mkdir(parents=True, exist_ok=True)
        (dst / "src" / "lib.rs").write_bytes((self.dir / f"v{k}" / "rust" / "src" / "lib.rs").read_bytes())
        (dst / "Cargo.toml").write_bytes((rustrun.workdir(self.dir / f"v{k}" / "rust") / "crate" /
                                          "Cargo.toml").read_bytes())
        bad = []
        for name, cases in (("round", self.round), ("heldout", self.heldout)):
            for c in cases:
                m = self.ref[c["id"]]["match"]
                if "ub" in m:
                    bad.append({"set": name, "id": c["id"], "pattern": c["pattern"], "text": c["text"],
                                "pattern_bytes": bytes_lit(c["pattern"]), "text_bytes": bytes_lit(c["text"]),
                                "cirrun": m["ub"], "where": m["ubkind"]})
        (TRX / "bad_inputs.json").write_text(json.dumps(bad, indent=1))
        kinds = Counter(b["where"] for b in bad)
        versions = {"final": f"guided/v{k}/rust", "all": [f"guided/{d.name}/rust" for d in sorted(
            self.dir.glob("v*"), key=lambda d: int(d.name[1:])) if (d / "rust" / "src" / "lib.rs").exists()],
            "style_guide": f"guide/styleguide_rust_c_v1.1.md (sha256 {GUIDE_SHA256})",
            "delivered": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        (TRX / "versions.json").write_text(json.dumps(versions, indent=1))
        rd, ho = rec.get("round", {}), rec.get("heldout", {})
        (TRX / "INTERFACE.md").write_text("\n".join([
            "# tiny-regex-c (f2632c6) → Rust: the delivered crate", "",
            f"Crate: `rust/` (src/lib.rs = guided/v{k}; Cargo.toml: crate `tiny_regex`, no dependencies, overflow "
            "checks on). Style guide: equiv-lean's styleguide_rust_c_v1.1.md (copy in guide/, sha256 "
            f"{GUIDE_SHA256}).", "", "## Interface (agreed with equiv-lean, 10-25)", "", _api_block(), "",
            "* A slice is the C string's bytes before its NUL (never 0); each byte is a C `char` read as `i8`.",
            "* re_match / re_matchp return (C return value, final *matchlength); both are compared always.",
            "* re_compile: None exactly when C returns NULL; Some = the two static arrays after one call from the "
            "module's initial memory (kind; ch except for the class kinds; ccl = u.ccl - ccl_buf; ccl_buf with 0 "
            "where the call wrote nothing).", "",
            "## How it was tested", "",
            "Reference: cirlean " + cref.CIRLEAN_PIN + "'s cirrun, one call per case from the module's initial "
            "memory: `re_match` with --show, and a harness (c/vo_harness.c) dumping re_compile's arrays. A native "
            "gcc build (UBSan, fork per case) agrees with cirrun on every case where the C is defined.",
            f"* round: {rd.get('n')} cases ({rd.get('defined')} defined, {rd.get('ub')} C-UB, "
            f"{rd.get('no_reference')} without a cirrun result): all pass natively and in the Aeneas extraction "
            "evaluated in Lean.",
            f"* heldout: {ho.get('n')} cases ({ho.get('defined')} defined, {ho.get('ub')} C-UB, "
            f"{ho.get('no_reference')} without a cirrun result): all pass.",
            "* On every C-UB case the crate returns normally (no panic natively, no failure in Lean).", "",
            "## Bad: the inputs on which the C has undefined behaviour (cirrun: pointer arithmetic out of bounds)",
            "", "`bad_inputs.json` lists every such case of both sets (" + ", ".join(
                f"{w}: {n}" for w, n in sorted(kinds.items())) + "). The two sites:",
            "* matchstar's `text--` when the star is tried at text index 0 and the loop reaches text == prepoint "
            "(the decrement happens before the last call, so the case is UB even when that call succeeds; test "
            "vector #32 \"a*$\" / \"Xaa\");",
            "* matchpattern forming `&pattern[2]` = `&re_compiled[31]` when the compiled pattern has 29 objects "
            "and matching reaches its sentinel.", ""]) + "\n")
        self.log(f"delivered v{k} to {dst}")

    def dollars(self) -> tuple[float, int]:
        p = self.dir / "llm" / "usage.jsonl"
        rows = [json.loads(x) for x in p.read_text().splitlines() if x.strip()] if p.exists() else []
        mine = [r for r in rows if r.get("task", "").startswith(f"c2rust:{self.arm}:s{self.seed}:")]
        return sum(r.get("dollars", 0.0) for r in mine), len(mine)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("arm", choices=["guided", "plain"])
    ap.add_argument("--budget", type=float, default=40.0)
    ap.add_argument("--attempts", type=int, default=12)
    ap.add_argument("--seed", type=int, default=1)
    a = ap.parse_args(argv)
    Run(a.arm, a.budget, a.attempts, a.seed).run()
    return 0


if __name__ == "__main__":
    sys.exit(main())

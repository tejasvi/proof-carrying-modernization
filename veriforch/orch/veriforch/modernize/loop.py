"""Translate a COBOL batch program with an LLM and repair it from counterexamples only (paper item A).

    python3 -m veriforch.modernize.loop PROG ARM LANG [--budget D] [--attempts N] [--cases N] [--final N]

ARM is `guided` (COBOL source + copybooks + the fixed style guide) or `naive` ("translate this COBOL program to
idiomatic Java/Rust" + the I/O contract needed to run it). LANG is `java` or `rust`.

Each attempt is one model call. Attempt 1 asks for the translation. Each later attempt sends back the current
translation and one of two things: the compiler's (or front end's) message, or up to three counterexamples. A
counterexample is a generated input on which an execution of the translation differs from the COBOL program
under coblean's semantics (cobolrun), with both outputs and the differences. Nothing else goes back: no hints
about causes, no human edits.

A version passes when every execution agrees with cobolrun on every case of the round (fresh cases plus all
earlier counterexamples). It is then checked on a larger fresh set. The run ends when a version passes that
set, or when the attempts or the budget run out.

Executions per language: Java on the JVM and in JimpleLean's interpreter (guided arm); Rust natively and through
its Aeneas extraction evaluated in Lean (guided arm). The naive arm runs natively, since idiomatic code with file
I/O is outside the verifiers' languages.

Records under `runs/modernize/<PROG>/<arm>/<lang>/`:
* `v<k>/`: the files, `attempt.json` (feedback sent, compile result, per-case results, discrepancies);
* `cases/`: the cases of each round;
* `llm/`: the ledger and full transcripts (the system prompt once, each user prompt and answer);
* `summary.json`: attempts, discrepancies by kind, model lines, cost, time, final status.
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
from . import compare
from .cobol import CobolProgram, comparable, encode_record
from .gen import Generator

VO = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
CARDDEMO = VO / "targets" / "carddemo_src" / "carddemo" / "app"
RUNS = VO / "runs" / "modernize"

LANG_NAME = {"java": "Java", "rust": "Rust"}


# ---------------------------------------------------------------------------------------------- inputs to the model
def copybooks(source: str, cpy_dir: Path) -> list[tuple[str, str]]:
    """COPY members the program uses, recursively, in first-use order."""
    out, seen = [], set()

    def scan(text):
        for ln in text.splitlines():
            if len(ln) > 6 and ln[6] in "*/":
                continue
            for name in re.findall(r"\bCOPY\s+([A-Z0-9@#$-]+)", ln[:72], re.I):
                name = name.upper()
                if name in seen:
                    continue
                seen.add(name)
                p = next((q for q in (cpy_dir / f"{name}.cpy", cpy_dir / f"{name}.CPY", cpy_dir / name) if q.exists()),
                         None)
                if p is None:
                    raise FileNotFoundError(f"copybook {name} not in {cpy_dir}")
                text2 = p.read_text(errors="replace")
                out.append((p.name, text2))
                scan(text2)
    scan(source)
    return out


def naive_contract(m: dict, lang: str) -> str:
    """INTERFACES.md's naive-arm contract for one language, without the harness-side notes."""
    t = (HERE / "INTERFACES.md").read_text()
    body = t[t.index("## Naive-arm I/O contract"):].split("\n", 1)[1].strip()
    bullets = ["* " + b.strip() for b in body.split("\n* ") if b.strip()]
    bullets[0] = (f"* A Java program whose main class is `{m['java_class']}`, in the default package." if lang == "java"
                  else f"* A binary crate named `{m['rust_crate']}`, no dependencies.")
    out = []
    for b in bullets:
        b = b.replace("* * ", "* ")
        b = b.split("  The runner passes")[0].split(" The runner passes")[0]
        out.append(b.rstrip())
    return "\n".join(out)


def guided(arm: str) -> bool:
    """`guided` (the v1 style guide) and `guided_v2` (v1 plus the structure rules for verification)."""
    return arm.startswith("guided")


def expected_files(m: dict, arm: str, lang: str) -> list[str]:
    if lang == "java":
        return [f"{m['java_class']}.java"]
    return ["Cargo.toml", "src/lib.rs"] if guided(arm) else ["Cargo.toml", "src/main.rs"]


def system_prompt(m: dict, arm: str, lang: str) -> str:
    L = LANG_NAME[lang]
    files = expected_files(m, arm, lang)
    fmt = ("Answer with the complete translation. For each file write a line `FILE: <path>` followed by a fenced code "
           f"block holding the whole file. Files: {', '.join('`' + f + '`' for f in files)}"
           + (" (more source files are allowed)" if arm == "naive" else "") + ".")
    if guided(arm):
        guide = HERE / (f"styleguide_{lang}_v2.md" if arm == "guided_v2" else f"styleguide_{lang}.md")
        return "\n\n".join([
            f"You translate COBOL batch programs into {L}. Follow the style guide below exactly.",
            guide.read_text(),
            "# Answer format", fmt])
    return "\n\n".join([
        f"Translate this COBOL program to idiomatic {L}.",
        "# How the program is run", naive_contract(m, lang),
        "# Answer format", fmt])


def called_sources(externals: list[str]) -> list[tuple[str, str]]:
    """Sources of the routines the program CALLs (CardDemo ships COBDATFT as assembler in app/asm)."""
    out = []
    for name in externals:
        for sub, ext in (("asm", ".asm"), ("cbl", ".cbl"), ("asm", ".ASM"), ("cbl", ".CBL")):
            q = CARDDEMO / sub / f"{name}{ext}"
            if q.exists():
                out.append((q.name, q.read_text(errors="replace")))
                break
        else:
            raise FileNotFoundError(f"no source for the called routine {name}")
    return out


def task_text(prog: str, source: str, cpys: list[tuple[str, str]], called: list[tuple[str, str]] = ()) -> str:
    parts = [f"# COBOL program {prog}", f"```cobol\n{source}\n```", "# Copybooks"]
    for name, text in cpys:
        parts += [f"## {name}", f"```cobol\n{text}\n```"]
    if called:
        parts.append("# Routines the program CALLs")
        for name, text in called:
            parts += [f"## {name}", f"```{'asm' if name.endswith('.asm') else 'cobol'}\n{text}\n```"]
    return "\n\n".join(parts)


def files_text(files: dict[str, str]) -> str:
    out = []
    for path, text in files.items():
        lang = "toml" if path.endswith(".toml") else ("java" if path.endswith(".java") else "rust")
        out.append(f"FILE: {path}\n```{lang}\n{text}\n```")
    return "\n\n".join(out)


def parse_files(answer: str) -> dict[str, str]:
    files = {}
    for m in re.finditer(r"FILE:\s*`?([\w./-]+)`?\s*\n```[\w+-]*\n(.*?)\n```", answer, re.S):
        files[m.group(1).strip()] = m.group(2)
    return files


# ---------------------------------------------------------------------------------------------- counterexamples
def _compact(obj, width: int = 4000) -> str:
    s = json.dumps(obj, ensure_ascii=False, indent=1)
    return s if len(s) <= width else s[:width] + "\n... (cut)"


def naive_files_view(cobol: CobolProgram, case: dict) -> str:
    """The input files as the naive program reads them (UTF-8 lines of the CP037-decoded record images)."""
    out = []
    for f in cobol.m["files"]:
        if not f["input"]:
            continue
        rec = cobol.m["records"][f["record"]]
        lines = [bytes(encode_record(cobol.L, rec, r)).decode("cp037")
                 for r in case["files"].get(f["fd"], {"records": []})["records"]]
        out.append(f"File {f['assign']} ({len(lines)} records):\n```\n" + "\n".join(lines) + "\n```")
    return "\n".join(out)


def counterexample_text(k: int, case: dict, exp: dict, results: dict, diffs: list[dict], arm: str,
                        cobol: CobolProgram) -> str:
    parts = [f"## Input {k}"]
    if arm == "naive":
        parts.append(naive_files_view(cobol, case))
        if case.get("clock"):
            parts.append(f"COBOL_CURRENT_DATE={case['clock']}")
        if case.get("linkage"):
            parts.append(f"Linkage (EXEC PARM): `{json.dumps(case['linkage'], ensure_ascii=False)}`")
    else:
        parts.append(f"```json\n{_compact(case, 6000)}\n```")
    parts.append("### Output of the COBOL program")
    parts.append(f"```json\n{_compact({k: v for k, v in exp.items() if k not in ('init_dependent', 'init_alternatives', 'detail', 'other_events')}, 5000)}\n```")
    for name, res in results.items():
        parts.append(f"### Output of the translation ({name})")
        if "outcome" in res:
            parts.append(f"```json\n{_compact(res['outcome'], 5000)}\n```")
        else:
            parts.append(f"{res.get('status', 'error')}:\n```\n{str(res.get('message', ''))[:3000]}\n```")
    if diffs:
        parts.append("### Differences (expected = COBOL program, actual = translation)")
        for d in diffs[:12]:
            where = d["location"] if d["where"] != "display" else f"display line {d['index'] + 1}"
            parts.append(f"- {where}: expected {json.dumps(d.get('expected'), ensure_ascii=False)}, "
                         f"actual {json.dumps(d.get('actual'), ensure_ascii=False)}")
    return "\n".join(parts)


# ---------------------------------------------------------------------------------------------- runners
def runner(arm: str, lang: str):
    """`run(trans_dir, cases, mapping) -> list[{"status", "message"?, "executions": {name: result}}]`, one per case;
    a result is {"outcome": ...} or {"status": "runtime_error", "message": ...}; status "compile_error" for the
    whole version is a list with one element."""
    if lang == "java":
        from . import javarun as r
    else:
        from . import rustrun as r
    return r.run_guided_batch if guided(arm) else r.run_naive_batch


# ---------------------------------------------------------------------------------------------- the loop
class HarnessError(RuntimeError):
    """The runner itself failed (a tool killed by a cap, an executor crash): stop instead of blaming the model."""


class Run:
    def __init__(self, prog: str, arm: str, lang: str, budget: float, attempts: int, n_cases: int, n_final: int,
                 seed: int = 1):
        self.prog, self.arm, self.lang = prog, arm, lang
        # seed 1 is the run of record (its passing guided versions go to equiv-lean); other seeds are repetitions
        # for the statistics, in their own directories, never delivered
        self.dir = RUNS / prog / arm / (lang if seed == 1 else f"{lang}_s{seed}")
        self.dir.mkdir(parents=True, exist_ok=True)
        (self.dir / "cases").mkdir(exist_ok=True)
        pdir = RUNS / prog
        self.m = json.loads((pdir / "mapping.json").read_text())
        ir_path = pdir / f"{prog.lower()}.ir.json"
        self.ir = json.loads(ir_path.read_text())
        self.cobol = CobolProgram(ir_path, self.m, VO / "scratch" / "modernize" / "work")
        src = next(q for q in (CARDDEMO / "cbl" / f"{prog}.cbl", CARDDEMO / "cbl" / f"{prog}.CBL") if q.exists())
        self.source = src.read_text(errors="replace")
        self.cpys = copybooks(self.source, CARDDEMO / "cpy")
        self.llm = LLM(self.dir, budget=budget)
        self.attempts, self.n_cases, self.n_final, self.seed = attempts, n_cases, n_final, seed
        import hashlib
        self.gen = Generator(self.m, self.ir, seed=int(hashlib.sha256(f"{prog}:{arm}:{lang}:{seed}".encode())
                                                           .hexdigest()[:8], 16))
        self.system = system_prompt(self.m, arm, lang)
        called = called_sources(sorted(set(self.m.get("externals", [])) | set(self.m.get("called", []))))
        self.cpys = copybooks("\n".join([self.source] + [t for _n, t in called if not _n.lower().endswith(".asm")]),
                              CARDDEMO / "cpy")
        self.task = task_text(prog, self.source, self.cpys, called)
        self.run_fn = runner(arm, lang)
        self._cobol_cache: dict[str, dict] = {}

    def log(self, msg: str) -> None:
        line = f"{time.strftime('%H:%M:%SZ', time.gmtime())} {self.prog}/{self.arm}/{self.lang}: {msg}"
        print(line, flush=True)
        with open(self.dir / "log.txt", "a") as f:
            f.write(line + "\n")

    def normalise(self, case: dict) -> dict:
        """Naive arm: the EXEC PARM is a command-line argument, so its length field is the text's length, and it
        cannot hold NUL (C strings end there): NULs in the text become spaces, for COBOL and translation alike."""
        if self.arm != "naive" or not case.get("linkage"):
            return case
        case = json.loads(json.dumps(case))
        for lk in self.m.get("linkage", []):
            if "record" not in lk:
                continue
            fields = self.m["records"][lk["record"]]["fields"]
            num = [f for f in fields if f["kind"] == "num" and f["usage"] in ("binary", "comp5")]
            text = [f for f in fields if f["kind"] == "alnum"]
            vals = case["linkage"][lk["name"]]
            for f in text:
                vals[f["cobol"]] = vals[f["cobol"]].replace("\x00", " ")
            if num and text:
                vals[num[0]["cobol"]] = sum(f["len"] for f in text)
        return case

    def naive_view(self, outcome: dict, case: dict, files_after: dict | None) -> dict:
        """Naive arm: line-sequential files keep no WRITE/REWRITE log, so both sides are compared on the final
        contents of each file the program writes or rewrites (indexed files in key order). COBOL's final contents
        are the input records plus its successful WRITEs, then its REWRITEs in order (by record key); the
        translation's are the files it leaves. The return code is not observable on abend (exit status 999)."""
        o = {k: outcome.get(k) for k in ("end", "displays", "return_code")}
        if o["end"] == "abend":
            o["return_code"] = None
        files = {}
        for f in self.m["files"]:
            if not (f.get("write_from") or f.get("rewrite_from")):
                continue
            rec = self.m["records"][f.get("rewrite_from") or f.get("write_from")]
            n = self.cobol.L.size(self.cobol.L.records[f["fd_record"]][1])

            def img(layout, r):
                return (encode_record(self.cobol.L, self.m["records"][layout], r) + [0x40] * n)[:n]
            if files_after is not None:
                if f["fd"] not in files_after:
                    files[f["fd"]] = []          # never created: as COBOL's OPEN OUTPUT of an empty file
                    continue
                imgs = [img(rec_name, r) for r in files_after[f["fd"]]
                        for rec_name in [f.get("rewrite_from") or f.get("write_from")]
                        if not any(isinstance(v, dict) for v in r.values())]
            else:
                imgs = [img(f["record"], r) for r in (case["files"].get(f["fd"], {"records": []})["records"]
                                                      if f["input"] else [])]
                ks = f.get("key_span")
                for r in outcome.get("writes", {}).get(f["fd"], []):
                    im = img(f["write_from"], r)
                    if f["org"] == "indexed" and ks:
                        imgs = [x for x in imgs if x[ks[0]:ks[0] + ks[1]] != im[ks[0]:ks[0] + ks[1]]]
                    imgs.append(im)
                for r in outcome.get("rewrites", {}).get(f["fd"], []):
                    im = img(f["rewrite_from"], r)
                    if f["org"] == "indexed" and ks:
                        imgs = [im if x[ks[0]:ks[0] + ks[1]] == im[ks[0]:ks[0] + ks[1]] else x for x in imgs]
            if f["org"] == "indexed" and f.get("key_span"):
                o_, l_ = f["key_span"]
                imgs.sort(key=lambda x: x[o_:o_ + l_])
            from .cobol import decode_record
            files[f["fd"]] = [decode_record(rec, x) for x in imgs]
        o["files"] = files
        return o

    def cobol_outcome(self, case: dict) -> dict:
        key = json.dumps(case, sort_keys=True)
        if key not in self._cobol_cache:
            self._cobol_cache[key] = self.cobol.run(case)
        return self._cobol_cache[key]

    def evaluate(self, vdir: Path, cases: list[dict]) -> dict:
        t0 = time.time()
        res = self.run_fn(vdir, cases, self.m)
        if len(res) == 1 and res[0].get("status") == "runner_error":
            raise HarnessError(f"{res[0].get('stage')}: {res[0].get('message')}"[:2000])
        bad = [er for r in res for er in (r.get("executions") or {}).values() if er.get("status") == "runner_error"]
        if bad:
            raise HarnessError(f"{len(bad)} executions failed in the runner: {str(bad[0].get('message'))[:1500]}")
        if len(res) == 1 and res[0].get("status") == "compile_error":
            return {"compile_error": res[0].get("message", ""), "stage": res[0].get("stage"),
                    "seconds": round(time.time() - t0, 1)}
        failing, per_case, disagree = [], [], 0
        skipped = 0
        for i, (case, r) in enumerate(zip(cases, res)):
            exp = self.cobol_outcome(case)
            if exp.get("unsupported"):
                skipped += 1             # outside coblean's model (e.g. COBDATFT's error path): no reference
                continue
            if self.arm == "naive":
                exp = dict(self.naive_view(exp, case, None), init_dependent=exp.get("init_dependent"),
                           init_alternatives=[self.naive_view(a, case, None) for a in exp.get("init_alternatives", [])])
            execs = r.get("executions") or {"run": r}
            ok, diffs_all = True, []
            outs = []
            for name, er in execs.items():
                if "outcome" not in er:
                    ok = False
                    diffs_all.append({"where": "end", "expected": exp["end"], "actual": er.get("status", "error"),
                                      "kind": "crash", "location": f"crash:{name}",
                                      "message": str(er.get("message", ""))[:500], "execution": name})
                    continue
                if self.arm == "naive":
                    er = dict(er, outcome=self.naive_view(er["outcome"], case, r.get("files_after") or {}))
                    execs[name] = er
                outs.append(json.dumps(comparable(er["outcome"]), sort_keys=True))
                ds = compare.classify(case, exp, er["outcome"])
                if ds:
                    ok = False
                    diffs_all += [dict(d, execution=name) for d in ds]
            if len(set(outs)) > 1:
                disagree += 1
            per_case.append({"case": i, "ok": ok, "diffs": diffs_all[:20], "init_dependent": bool(exp.get("init_dependent"))})
            if not ok:
                failing.append((i, case, exp, execs, diffs_all))
        kinds = Counter()
        locs = Counter()
        for _, _, _, _, ds in failing:
            for d in {(d["kind"], compare.location_class(d["location"])) for d in ds}:
                kinds[d[0]] += 1
                locs[d] += 1
        return {"n": len(cases) - skipped, "skipped_unsupported": skipped, "pass": len(cases) - skipped - len(failing),
                "failing": failing, "per_case": per_case,
                "kinds": dict(kinds), "discrepancies": [{"kind": k, "location": l, "cases": n} for (k, l), n in
                                                         locs.most_common()],
                "executions_disagree": disagree, "seconds": round(time.time() - t0, 1)}

    def pick(self, failing: list) -> list:
        """Up to three failing cases with distinct first discrepancies, smallest inputs first."""
        def size(c):
            return sum(len(f["records"]) for f in c["files"].values())
        chosen, seen = [], set()
        for item in sorted(failing, key=lambda it: size(it[1])):
            key = (item[4][0]["kind"], item[4][0]["location"]) if item[4] else None
            if key in seen:
                continue
            seen.add(key)
            chosen.append(item)
            if len(chosen) == 3:
                break
        return chosen

    def fresh(self, n: int, tag: str) -> list[dict]:
        cases = [self.normalise(self.gen.case()) for _ in range(n)]
        with open(self.dir / "cases" / f"{tag}.jsonl", "w") as f:
            for c in cases:
                f.write(json.dumps(c, ensure_ascii=False) + "\n")
        return cases

    def resume(self, cex_cases: list[dict]) -> dict | None:
        """Continue a finished run from its last version with counterexamples found elsewhere (e.g. by a failed
        proof). They join the regression set; if the last version passes them, nothing happens."""
        prev = json.loads((self.dir / "summary.json").read_text())
        last = max(prev["versions"])
        sub = "java" if self.lang == "java" else "rust"
        base = self.dir / f"v{last}" / sub
        files = {str(q.relative_to(base)): q.read_text() for q in sorted(base.rglob("*"))
                 if q.is_file() and q.suffix in (".java", ".rs", ".toml") and "javarun" not in q.parts}
        cex_cases = [self.normalise(c) for c in cex_cases]
        ev = self.evaluate(self.dir / f"v{last}", cex_cases)
        if "compile_error" in ev or not ev["failing"]:
            self.log(f"resume: v{last} passes the {len(cex_cases)} external counterexample(s); nothing to repair")
            return None
        chosen = self.pick(ev["failing"])
        feedback = self.feedback_text(chosen)
        self.log(f"resume: v{last} fails {len(ev['failing'])} external counterexample(s); repairing from v{last + 1}")
        return self.run(start_k=last + 1, files=files, feedback=feedback, regression=cex_cases,
                        prev_summary=prev)

    def feedback_text(self, chosen: list) -> str:
        return ("# Result\n\nOn the inputs below, the translation's output differs from the COBOL "
                "program's. Inputs and outputs are JSON: records by COBOL field name (groups flattened, "
                "FILLERs as FILLER#k); numeric values are integers scaled by 10^decimals.\n\n" +
                "\n\n".join(counterexample_text(j + 1, c, e, x, d, self.arm, self.cobol)
                            for j, (_, c, e, x, d) in enumerate(chosen)))

    def naive_not_applicable(self) -> str | None:
        """The naive arm's line-sequential text files cannot carry packed or binary fields or variable-length
        records."""
        if self.arm != "naive":
            return None
        for f in self.m["files"]:
            if f.get("varying"):
                return f"{f['fd']} has variable-length records"
            for rn in {f.get("record") if f["input"] else None, f.get("write_from"), f.get("rewrite_from")} - {None}:
                bad = [x for x in self.m["records"][rn]["fields"] if x["kind"] == "num" and x["usage"] != "display"]
                if bad:
                    return f"{rn} has a {bad[0]['usage']} field ({bad[0]['cobol']})"
        return None

    def run(self, start_k: int = 1, files: dict | None = None, feedback: str = "", regression: list | None = None,
            prev_summary: dict | None = None) -> dict:
        why = self.naive_not_applicable()
        if why:
            summary = {"program": self.prog, "arm": self.arm, "lang": self.lang,
                       "status": f"not applicable: {why}; the naive I/O contract is line-sequential text",
                       "cobol_lines": len(self.source.splitlines()), "attempts": 0, "versions": [],
                       "final_version": None, "model_lines": None, "human_lines": 0, "discrepancies": [],
                       "discrepancies_by_kind": {}, "compile_errors": 0, "dollars": 0.0, "llm_calls": 0,
                       "seconds": 0.0, "model": self.llm.model}
            (self.dir / "summary.json").write_text(json.dumps(summary, indent=1))
            self.log(summary["status"])
            return summary
        t_start = time.time()
        files = dict(files or {})
        regression = list(regression or [])
        history = []
        status = "attempts exhausted"
        all_disc: dict[tuple, dict] = {}
        if prev_summary:
            for d in prev_summary.get("discrepancies", []):
                all_disc[(d["kind"], d["location"])] = dict(d)
        for k in range(start_k, start_k + self.attempts):
            vdir = self.dir / f"v{k}"
            vdir.mkdir(exist_ok=True)
            user = self.task + ("\n\nTranslate the program." if not files else
                                "\n\n# Your current translation\n\n" + files_text(files) + "\n\n" + feedback +
                                "\n\nGive the corrected complete translation.")
            try:
                answer = self.llm.ask_text(f"{self.prog}:{self.arm}:{self.lang}:v{k}", self.system, user,
                                           effort="high", max_tokens=64000)
            except BudgetExceeded as e:
                status = f"budget: {e}"
                break
            except LLMError as e:
                self.log(f"v{k}: model call failed: {e}")
                history.append({"version": k, "model_error": str(e)})
                continue
            new = parse_files(answer)
            missing = [p for p in expected_files(self.m, self.arm, self.lang) if p not in new]
            if missing:
                feedback = (f"# Result\n\nThe answer lacks the file(s) {', '.join(missing)} in the required format "
                            "(`FILE: <path>` followed by a fenced code block).")
                history.append({"version": k, "format_error": missing})
                self.log(f"v{k}: answer lacks {missing}")
                if not files:
                    continue
                continue
            files = new
            for p, text in files.items():
                q = vdir / ("java" if self.lang == "java" else "rust") / p
                q.parent.mkdir(parents=True, exist_ok=True)
                q.write_text(text)
            cases = self.fresh(self.n_cases, f"v{k}") + regression
            try:
                ev = self.evaluate(vdir, cases)
            except HarnessError as e:
                status = f"harness error: {e}"
                self.log(f"v{k}: {status}")
                history.append({"version": k, "harness_error": str(e)})
                break
            rec = {"version": k, "feedback_sent": feedback[:20000], "model_lines": self.model_lines(files)}
            if ev.get("failing"):
                # full data of every failing case, so the kinds can be recomputed or re-labelled by hand later
                with open(vdir / "failing.jsonl", "w") as fh:
                    for i, c, e, x, d in ev["failing"]:
                        fh.write(json.dumps({"case_index": i, "case": c, "cobol": e, "translation": x, "diffs": d},
                                            ensure_ascii=False) + "\n")
            if "compile_error" in ev:
                rec["compile_error"] = ev["compile_error"][:20000]
                rec["compile_stage"] = ev.get("stage")
                feedback = "# Result\n\nThe translation does not build:\n```\n" + ev["compile_error"][:6000] + "\n```"
                self.log(f"v{k}: compile error")
            else:
                rec.update({x: ev[x] for x in ("n", "pass", "kinds", "discrepancies", "executions_disagree",
                                               "seconds", "per_case")})
                for d in ev["discrepancies"]:
                    all_disc.setdefault((d["kind"], d["location"]), {"kind": d["kind"], "location": d["location"],
                                                                     "first_version": k, "cases": 0})
                    all_disc[(d["kind"], d["location"])]["cases"] += d["cases"]
                self.log(f"v{k}: {ev['pass']}/{ev['n']} pass; kinds {ev['kinds']}; disagree "
                         f"{ev['executions_disagree']}")
                if not ev["failing"]:
                    try:
                        final = self.evaluate(vdir, self.fresh(self.n_final, f"final_v{k}"))
                    except HarnessError as e:
                        status = f"harness error: {e}"
                        self.log(f"v{k}: {status}")
                        history.append(rec)
                        break
                    rec["final"] = {x: final.get(x) for x in ("n", "pass", "kinds", "discrepancies",
                                                              "executions_disagree", "seconds", "compile_error")}
                    if final.get("compile_error") is None and not final["failing"]:
                        history.append(rec)
                        (vdir / "attempt.json").write_text(json.dumps(rec, indent=1, ensure_ascii=False))
                        status = "passed"
                        self.log(f"v{k}: passed {final['n']} fresh cases")
                        break
                    ev = final
                    if final.get("failing"):
                        with open(vdir / "failing_final.jsonl", "w") as fh:
                            for i, c, e, x, d in final["failing"]:
                                fh.write(json.dumps({"case_index": i, "case": c, "cobol": e, "translation": x,
                                                     "diffs": d}, ensure_ascii=False) + "\n")
                    for d in final.get("discrepancies", []):
                        all_disc.setdefault((d["kind"], d["location"]), {"kind": d["kind"], "location": d["location"],
                                                                         "first_version": k, "cases": 0})
                        all_disc[(d["kind"], d["location"])]["cases"] += d["cases"]
                chosen = self.pick(ev["failing"])
                regression += [c for _, c, _, _, _ in chosen]
                feedback = self.feedback_text(chosen)
                rec["counterexamples"] = [i for i, _, _, _, _ in chosen]
            history.append(rec)
            (vdir / "attempt.json").write_text(json.dumps(rec, indent=1, ensure_ascii=False))
        if prev_summary:
            history = [{"version": v} for v in prev_summary.get("versions", [])] + history
            t_start -= prev_summary.get("seconds", 0)
        summary = {
            "program": self.prog, "arm": self.arm, "lang": self.lang, "seed": self.seed, "status": status,
            "cobol_lines": len(self.source.splitlines()),
            "attempts": len(history), "versions": [h["version"] for h in history],
            "final_version": history[-1]["version"] if history and status == "passed" else None,
            "model_lines": history[-1].get("model_lines") if history else None,
            "human_lines": 0,
            "discrepancies": sorted(all_disc.values(), key=lambda d: (d["first_version"], d["kind"])),
            "discrepancies_by_kind": dict(Counter(d["kind"] for d in all_disc.values())),
            "compile_errors": sum(1 for h in history if "compile_error" in h) +
                              (prev_summary or {}).get("compile_errors", 0),
            "dollars": round(self.translation_dollars()[0], 4), "llm_calls": self.translation_dollars()[1],
            "seconds": round(time.time() - t_start, 1),
            "model": self.llm.model,
        }
        (self.dir / "summary.json").write_text(json.dumps(summary, indent=1, ensure_ascii=False))
        if status == "passed" and guided(self.arm) and self.seed == 1:
            self.deliver(summary["final_version"])
        self.log(f"done: {status}; {summary['attempts']} attempts; ${summary['dollars']}")
        return summary

    def translation_dollars(self) -> tuple[float, int]:
        """$ and calls of this run's translation and repair calls (the ledger also holds labelling calls)."""
        p = self.dir / "llm" / "usage.jsonl"
        rows = [json.loads(x) for x in p.read_text().splitlines() if x.strip()] if p.exists() else []
        mine = [r for r in rows if r.get("task", "").startswith(f"{self.prog}:{self.arm}:{self.lang}:")]
        return sum(r.get("dollars", 0.0) for r in mine), len(mine)

    def deliver(self, k: int) -> None:
        """The passing guided version goes to runs/modernize/<PROG>/<java|rust>/ for equiv-lean's proof."""
        import shutil
        sub = "java" if self.lang == "java" else "rust"
        key = sub + ("_v2" if self.arm == "guided_v2" else "")
        dst = RUNS / self.prog / key
        if dst.exists():
            shutil.rmtree(dst)
        shutil.copytree(self.dir / f"v{k}" / sub, dst)
        vj = RUNS / self.prog / "versions.json"
        versions = json.loads(vj.read_text()) if vj.exists() else {}
        versions[key] = {"final": f"{self.arm}/{self.lang}/v{k}/{sub}",
                         "all": [f"{self.arm}/{self.lang}/{d.name}/{sub}" for d in sorted(self.dir.glob("v*"),
                                 key=lambda d: int(d.name[1:])) if (d / sub).exists()],
                         "style_guide": f"styleguide_{self.lang}{'_v2' if self.arm == 'guided_v2' else ''}.md",
                         "delivered": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        vj.write_text(json.dumps(versions, indent=1))
        self.log(f"delivered v{k} to {dst}")

    @staticmethod
    def model_lines(files: dict[str, str]) -> int:
        return sum(1 for t in files.values() for ln in t.splitlines() if ln.strip())


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("prog")
    ap.add_argument("arm", choices=["guided", "guided_v2", "naive"])
    ap.add_argument("lang", choices=["java", "rust"])
    ap.add_argument("--budget", type=float, default=15.0)
    ap.add_argument("--attempts", type=int, default=10)
    ap.add_argument("--cases", type=int, default=60)
    ap.add_argument("--final", type=int, default=300)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--resume-with", help="JSONL of counterexample cases (e.g. from a failed proof): continue the "
                                          "finished run from its last version")
    a = ap.parse_args(argv)
    r = Run(a.prog, a.arm, a.lang, a.budget, a.attempts, a.cases, a.final, a.seed)
    if a.resume_with:
        cex = [json.loads(x) for x in Path(a.resume_with).read_text().splitlines() if x.strip()]
        r.resume(cex)
    else:
        r.run()
    return 0


if __name__ == "__main__":
    sys.exit(main())

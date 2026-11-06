"""Root causes of the discrepancies a run repaired, labelled after the run by one uniform model call per repair.

    python3 -m veriforch.modernize.rootcause PROG ARM LANG [--budget D]

compare.py names the SYMPTOM of each discrepancy from the outputs alone (e.g. a wrong reject reason is `text`).
The cause usually needs the code: an alphanumeric comparison done in Unicode instead of EBCDIC order shows up as a
wrong record or a wrong reason code. For every repair step v<k> -> v<k+1> after failing cases, the model sees the
COBOL program, version k, the diff to version k+1, and the counterexamples that were sent. It names each cause
that the diff fixed, using the fixed taxonomy below. The repair loop never sees these labels. The prompt is the
same for every program, arm and language. Build failures are labelled from their stage and message, without a
model call.
"""
from __future__ import annotations

import argparse
import difflib
import json
import re
import time
from pathlib import Path

from ..llm import LLM
from .loop import CARDDEMO, RUNS, copybooks, task_text

KINDS = {
    "rounding": "a result rounded where COBOL truncates, or the other way round",
    "truncation": "high-order digits lost (size overflow without ON SIZE ERROR, MOVE to a shorter numeric field)",
    "sign": "sign lost, added or placed differently (unsigned fields take the absolute value, overpunch)",
    "arithmetic precision": "intermediate results with too few digits or the wrong scale",
    "uninitialized storage": "storage without a VALUE clause read before it is written",
    "file status": "file status codes, INVALID KEY / AT END handling, abends on I/O errors",
    "end of file": "behaviour at end of file (e.g. the last record processed again)",
    "collating sequence": "alphanumeric comparison or ordering in EBCDIC vs Unicode order",
    "numeric formatting": "how a numeric item is DISPLAYed or edited (zero padding, decimal point, sign position)",
    "padding": "alphanumeric MOVE padding/truncation, justification, group moves",
    "data conversion": "alphanumeric<->numeric MOVEs, digit/character interpretation, encodings",
    "control flow": "conditions, PERFORM/GO TO/paragraph fall-through, loop structure, missing or extra steps",
    "interface": "the translation's entry point, record classes or field types differ from the style guide",
    "verifier language": "a construct the verifier's language (JimpleLean / Aeneas) does not accept",
    "other": "anything else (explain)",
}

SCHEMA = {
    "type": "object",
    "properties": {
        "causes": {"type": "array", "items": {
            "type": "object",
            "properties": {
                "kind": {"type": "string", "enum": list(KINDS)},
                "cobol": {"type": "string", "description": "the COBOL statement(s) or rule involved"},
                "explanation": {"type": "string", "description": "one sentence: what the translation did wrong"},
                "fixed": {"type": "boolean", "description": "true if the diff fixes it"},
            },
            "required": ["kind", "cobol", "explanation", "fixed"]}},
    },
    "required": ["causes"],
}


def _files(vdir: Path) -> dict[str, str]:
    out = {}
    for sub in ("java", "rust"):
        base = vdir / sub
        if base.exists():
            for p in sorted(base.rglob("*")):
                if p.is_file() and p.suffix in (".java", ".rs", ".toml") and "javarun" not in p.parts \
                        and "target" not in p.parts:
                    out[str(p.relative_to(base))] = p.read_text(errors="replace")
    return out


def _diff(a: dict[str, str], b: dict[str, str]) -> str:
    out = []
    for path in sorted(set(a) | set(b)):
        out += difflib.unified_diff((a.get(path) or "").splitlines(), (b.get(path) or "").splitlines(),
                                    f"v_k/{path}", f"v_k+1/{path}", lineterm="", n=3)
    return "\n".join(out)


def label(prog: str, arm: str, lang_dir: str, budget: float = 5.0) -> dict:
    rdir = RUNS / prog / arm / lang_dir
    lang = lang_dir.split("_s")[0]
    summary = json.loads((rdir / "summary.json").read_text())
    source = (CARDDEMO / "cbl" / f"{prog}.cbl").read_text(errors="replace")
    task = task_text(prog, source, copybooks(source, CARDDEMO / "cpy"))
    llm = LLM(rdir, budget=budget)
    system = ("You review repairs of COBOL-to-" + ("Java" if lang == "java" else "Rust") + " translations. "
              "Name the root cause of each discrepancy a repair fixed, from this taxonomy:\n" +
              "\n".join(f"- {k}: {v}" for k, v in KINDS.items()))
    steps = []
    versions = summary["versions"]
    for k, k2 in zip(versions, versions[1:]):
        att = json.loads((rdir / f"v{k}" / "attempt.json").read_text())
        att2 = json.loads((rdir / f"v{k2}" / "attempt.json").read_text())
        step = {"from": k, "to": k2}
        if "compile_error" in att:
            msg = att["compile_error"]
            stage = att.get("compile_stage") or ""
            verifier = stage in ("soot", "jimple-import", "charon", "aeneas", "lean") or \
                re.match(r"\s*(Aeneas|Charon|Soot|JimpleLean|the crate uses functions or types that Aeneas)", msg)
            step["causes"] = [{"kind": "interface" if stage == "driver" or "interface" in msg[:400] else
                               ("verifier language" if verifier else "build"),
                               "cobol": "", "explanation": f"build failed at stage {stage or '?'}: {msg[:300]}",
                               "fixed": "compile_error" not in att2}]
            steps.append(step)
            continue
        if att.get("pass") == att.get("n") and (att.get("final") or {}).get("pass") == (att.get("final") or {}).get("n"):
            continue
        a, b = _files(rdir / f"v{k}"), _files(rdir / f"v{k2}")
        user = "\n\n".join([
            task,
            "# Translation, version k", "\n\n".join(f"FILE: {p}\n```\n{t}\n```" for p, t in a.items()),
            "# Diff from version k to version k+1 (the repair)", f"```diff\n{_diff(a, b)[:60000]}\n```",
            "# Counterexamples sent with the repair request", att2.get("feedback_sent", "")[:30000],
            "# Mechanical symptom labels of version k's failing cases",
            json.dumps((att.get("final") or {}).get("discrepancies") or att.get("discrepancies"), ensure_ascii=False)[:4000],
            "List every distinct root cause behind the counterexamples, and say for each whether the diff fixes it.",
            'Answer as {"causes": [{"kind": <one taxonomy name>, "cobol": <the COBOL statement(s) or rule>, '
            '"explanation": <one sentence>, "fixed": <true|false>}, ...]}.'])
        try:
            ans = llm.ask_json(f"rootcause:{prog}:{arm}:{lang_dir}:v{k}", system, user, SCHEMA, effort="high",
                               max_tokens=16000)
            causes = []
            for c in ans["causes"] if isinstance(ans.get("causes"), list) else []:
                kind = c.get("kind") or c.get("category") or "other"
                fixed = c.get("fixed", c.get("fixed_by_diff", c.get("fixed_by_repair")))
                causes.append({"kind": kind if kind in KINDS else "other",
                               "kind_given": kind, "cobol": c.get("cobol", c.get("cobol_construct", "")),
                               "explanation": c.get("explanation") or c.get("description") or c.get("summary", ""),
                               "fixed": bool(fixed), "raw": c})
            step["causes"] = causes
        except Exception as e:                       # budget or API trouble: leave the step unlabelled
            step["error"] = str(e)[:500]
        steps.append(step)
    out = {"program": prog, "arm": arm, "lang": lang, "run": lang_dir, "steps": steps,
           "labelled": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "model": llm.model,
           "dollars": round(llm.usage.dollars - llm._start_dollars, 4)}
    (rdir / "rootcauses.json").write_text(json.dumps(out, indent=1, ensure_ascii=False))
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("prog")
    ap.add_argument("arm")
    ap.add_argument("lang")
    ap.add_argument("--budget", type=float, default=5.0)
    a = ap.parse_args()
    r = label(a.prog, a.arm, a.lang, a.budget)
    for s in r["steps"]:
        for c in s.get("causes", []):
            print(f"v{s['from']}->v{s['to']}: {c['kind']}: {c['explanation'][:150]} (fixed={c['fixed']})")

"""Per-program table for item A from the runs' records: summary.json, rootcauses.json, attempt.json files,
annotations.json (harness artifacts) and equiv-lean's proof_<lang>.json.

    python3 -m veriforch.modernize.report [PROG...]      # writes runs/modernize/REPORT.md and REPORT.json

Discrepancies are counted two ways:
* root causes (rootcauses.json): one model call per repair step after the run, fixed taxonomy, labels never shown to
  the repair loop; counted per run as distinct (kind) per repair step;
* symptoms (compare.py, mechanical): distinct (kind, output stream) over the run.
"""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

RUNS = Path(__file__).resolve().parents[3] / "runs" / "modernize"


def _json(p: Path):
    return json.loads(p.read_text()) if p.exists() else None


def run_row(prog: str, arm: str, lang: str) -> dict | None:
    d = RUNS / prog / arm / lang
    s = _json(d / "summary.json")
    if s is None:
        return None
    rc = _json(d / "rootcauses.json") or {"steps": []}
    causes = Counter()
    for step in rc["steps"]:
        for k in {c["kind"] for c in step.get("causes", []) if c.get("fixed", True)} - {"harness artifact"}:
            causes[k] += 1
    stages = Counter()
    init_dep = n_cases = 0
    for v in s.get("versions", []):
        a = _json(d / f"v{v}" / "attempt.json") or {}
        if "compile_error" in a:
            stages[a.get("compile_stage") or "build"] += 1
        for pc in a.get("per_case", []) if v == (s["versions"] or [None])[0] else []:
            n_cases += 1
            init_dep += bool(pc.get("init_dependent"))
    lang0 = lang.split("_s")[0]
    proof = (_json(RUNS / prog / f"proof_{lang0}.json") if arm == "guided" else
             _json(RUNS / prog / f"proof_{lang0}_v2.json") if arm == "guided_v2" else None)
    return {**{k: s.get(k) for k in ("program", "arm", "lang", "status", "cobol_lines", "attempts", "model_lines",
                                     "human_lines", "dollars", "seconds", "llm_calls")},
            "root_causes": dict(causes), "symptoms": s.get("discrepancies_by_kind", {}),
            "build_failures": dict(stages), "first_round_init_dependent": [init_dep, n_cases],
            "annotations": _json(d / "annotations.json"), "proof": (proof or {}).get("status")}


def table(rows: list[dict]) -> str:
    out = ["| program | arm | lang | COBOL lines | attempts | build failures | root causes (repairs) | symptoms "
           "(mechanical) | status | proof | human lines | model lines | $ | min |", "|" + "---|" * 14]
    for r in rows:
        rc = ", ".join(f"{k} {n}" for k, n in sorted(r["root_causes"].items())) or "-"
        sy = ", ".join(f"{k} {n}" for k, n in sorted(r["symptoms"].items())) or "-"
        bf = ", ".join(f"{k} {n}" for k, n in sorted(r["build_failures"].items())) or "-"
        st = r["status"] if len(r["status"]) < 40 else r["status"][:37] + "..."
        out.append(f"| {r['program']} | {r['arm']} | {r['lang']} | {r['cobol_lines']} | {r['attempts']} | {bf} | {rc} "
                   f"| {sy} | {st} | {r['proof'] or '-'} | {r['human_lines']} | {r['model_lines'] or '-'} | "
                   f"{(r['dollars'] or 0):.2f} | {(r['seconds'] or 0) / 60:.0f} |")
    tot_rc, tot_sy = Counter(), Counter()
    for r in rows:
        tot_rc.update(r["root_causes"])
        tot_sy.update(r["symptoms"])
    out += ["", "Root causes, all runs: " + (", ".join(f"{k} {n}" for k, n in tot_rc.most_common()) or "-"),
            "Symptoms, all runs: " + (", ".join(f"{k} {n}" for k, n in tot_sy.most_common()) or "-")]
    applicable = [r for r in rows if not r["status"].startswith("not applicable")]
    passed = [r for r in applicable if r["status"] == "passed"]
    out.append(f"Passed: {len(passed)} of {len(applicable)} applicable runs "
               f"({len(rows) - len(applicable)} not applicable); first attempt: "
               f"{sum(1 for r in passed if r['attempts'] == 1)}")
    out.append(f"Translation + repair cost of these runs: ${sum(r['dollars'] or 0 for r in rows):.2f}")
    allrows = [json.loads(x) for p in RUNS.rglob("usage.jsonl") for x in p.read_text().splitlines() if x.strip()]
    out.append(f"All item A model spend (incl. aborted runs and root-cause labelling): "
               f"${sum(r.get('dollars', 0) for r in allrows):.2f} over {len(allrows)} calls")
    notes = [(r["program"], r["arm"], r["lang"], r["annotations"]) for r in rows if r["annotations"]]
    if notes:
        out += ["", "Harness notes:"] + [f"- {p} {a} {l}: {json.dumps(n, ensure_ascii=False)}" for p, a, l, n in notes]
    return "\n".join(out)


def seeds_table(progs: list[str]) -> tuple[str, list[dict]]:
    """Repetitions: the same run with seeds 1-3 (fresh generated cases and model samples; seed 1 is the run of
    record)."""
    out = ["| program | arm | lang | attempts per seed | passed | first attempt | root causes (all seeds) | $ (all seeds) |",
           "|" + "---|" * 8]
    rows = []
    for prog in progs:
        for arm in ("guided", "naive"):
            for lang in ("java", "rust"):
                rs = [r for d in (lang, f"{lang}_s2", f"{lang}_s3") if (r := run_row(prog, arm, d))]
                rs = [r for r in rs if not r["status"].startswith("not applicable")]
                if not rs:
                    continue
                rc = Counter()
                for r in rs:
                    rc.update(r["root_causes"])
                row = {"program": prog, "arm": arm, "lang": lang, "attempts": [r["attempts"] for r in rs],
                       "passed": sum(r["status"] == "passed" for r in rs), "seeds": len(rs),
                       "first_attempt": sum(r["status"] == "passed" and r["attempts"] == 1 for r in rs),
                       "root_causes": dict(rc), "dollars": round(sum(r["dollars"] or 0 for r in rs), 4)}
                rows.append(row)
                out.append(f"| {prog} | {arm} | {lang} | {row['attempts']} | {row['passed']}/{row['seeds']} | "
                           f"{row['first_attempt']}/{row['seeds']} | "
                           f"{', '.join(f'{k} {n}' for k, n in sorted(rc.items())) or '-'} | {row['dollars']:.2f} |")
    tot = Counter()
    for r in rows:
        tot.update(r["root_causes"])
    n = sum(r["seeds"] for r in rows)
    out += ["", f"Repetitions: {sum(r['passed'] for r in rows)} of {n} runs passed; first attempt in "
            f"{sum(r['first_attempt'] for r in rows)}; root causes over all seeds: "
            + (", ".join(f"{k} {v}" for k, v in tot.most_common()) or "-")]
    return "\n".join(out), rows


def main(progs: list[str]) -> str:
    progs = progs or sorted(p.name for p in RUNS.iterdir() if p.is_dir() and not p.name.startswith("_"))
    rows = [r for prog in progs for arm in ("guided", "guided_v2", "naive") for lang in ("java", "rust")
            if (r := run_row(prog, arm, lang))]
    text = table(rows)
    stext, srows = seeds_table(progs)
    text += "\n\n## Repetitions (seeds 1-3)\n\n" + stext
    (RUNS / "REPORT_SEEDS.json").write_text(json.dumps(srows, indent=1, ensure_ascii=False))
    (RUNS / "REPORT.md").write_text(text + "\n")
    (RUNS / "REPORT.json").write_text(json.dumps(rows, indent=1, ensure_ascii=False))
    return text


if __name__ == "__main__":
    print(main(sys.argv[1:]))

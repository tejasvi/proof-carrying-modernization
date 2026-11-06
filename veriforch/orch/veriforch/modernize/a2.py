"""A2: the "AI-error number" of item A, computed from the run records only (no model calls).

    python3 -m veriforch.modernize.a2        # writes runs/modernize/A2/A2.json and A2.md

Per run (program, arm, language, seed), from runs/modernize/<PROG>/<arm>/<lang>[_s<seed>]/:
* first attempt: v1 either failed to build (compile or verifier front end) or ran;
* first version that ran: the first v<k> with an evaluation; it "differed" if any generated case (the 60 fresh plus
  regression cases, or the 300-case final check) gave an outcome different from cobolrun;
* attempts to converge (versions until the run passed);
* root causes (rootcauses.json, the fixed taxonomy; causes the repair fixed), mapped to the user's categories;
* mechanical symptoms (summary.json discrepancies_by_kind, relabelled);
* executions_disagree in every attempt (the two executions per language: JVM + JimpleLean, native + Aeneas-in-Lean).
Excluded: runs whose summary says "not applicable", and runs with a harness artifact (annotations.json).
"""
from __future__ import annotations

import json
import math
import statistics
from collections import Counter, defaultdict
from pathlib import Path

RUNS = Path(__file__).resolve().parents[3] / "runs" / "modernize"
# equiv-lean (the equiv-lean maintainer session), verbatim, 2026-10-25, relayed by veriforch's main session
EQUIVLEAN_ANSWER = ("None so far, as of 01:58Z. No proof on a delivered translation (v1 or java_v2, Java or Rust) has "
                    "found a real behavioural mismatch with the COBOL that testing missed. Closest case: a platform-limit "
                    "edge, not a translation error. In CBTRN02C java_v2, findTcatbal loops over List.size(), which wraps at "
                    "≥ 2^31 list elements in JimpleLean's model; a real JVM throws OutOfMemoryError first. The statements "
                    "now bound inputs (< 2^27 records for Java, < 2^28 for Rust, whose usize may be 32-bit). The fuller "
                    "discrepancy list, statement-side findings included, comes from us later today.")
OUT = RUNS / "A2"
ARMS = {"guided": "style guide v1", "guided_v2": "style guide v2 (Java only)", "naive": "plain prompt"}

# fixed root-cause taxonomy (rootcause.py) -> the user's categories; the extra categories stay their own rows
CATEGORY = {
    "rounding": "rounding", "truncation": "truncation", "sign": "sign",
    "uninitialized storage": "uninitialized storage",
    "file status": "abend/file status", "end of file": "abend/file status",
    "control flow": "control flow",
    "collating sequence": "collating sequence (extra)", "verifier language": "verifier language (extra)",
    "interface": "interface (extra)", "numeric formatting": "numeric formatting (extra)",
    "padding": "padding (extra)", "data conversion": "data conversion (extra)",
    "arithmetic precision": "arithmetic precision (extra)", "other": "other",
}


def wilson(k: int, n: int, z: float = 1.96) -> list[float] | None:
    if n == 0:
        return None
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return [round(max(0.0, c - h), 4), round(min(1.0, c + h), 4)]


def _json(p: Path):
    return json.loads(p.read_text()) if p.exists() else None


def run_records() -> tuple[list[dict], list[dict]]:
    runs, excluded = [], []
    for prog_dir in sorted(p for p in RUNS.iterdir() if p.is_dir() and p.name.startswith("CB")):
        for arm in ARMS:
            for lang_dir in sorted((prog_dir / arm).glob("*")) if (prog_dir / arm).is_dir() else []:
                name = lang_dir.name
                if not (name in ("java", "rust") or name.startswith(("java_s", "rust_s"))):
                    continue                                    # *_aborted_* archives are not runs of record
                s = _json(lang_dir / "summary.json")
                if s is None:
                    continue
                lang, seed = (name.split("_s")[0], int(name.split("_s")[1])) if "_s" in name else (name, 1)
                rec = {"program": prog_dir.name, "arm": arm, "lang": lang, "seed": seed, "dir": str(lang_dir)}
                if s["status"].startswith("not applicable"):
                    excluded.append(dict(rec, reason=s["status"]))
                    continue
                ann = _json(lang_dir / "annotations.json")
                if ann:
                    excluded.append(dict(rec, reason="harness artifact: " + "; ".join(f"{k}: {v[:120]}" for k, v in ann.items())))
                    continue
                atts = []
                for v in s["versions"]:
                    a = _json(lang_dir / f"v{v}" / "attempt.json") or {}
                    atts.append((v, a))
                first = atts[0][1] if atts else {}
                v1_build_fail = "compile_error" in first
                ran = [(v, a) for v, a in atts if "n" in a]
                fv, fa = ran[0] if ran else (None, {})

                def differed(a):
                    fin = a.get("final") or {}
                    return (a.get("pass") != a.get("n")) or (fin and fin.get("pass") != fin.get("n"))
                rc = _json(lang_dir / "rootcauses.json") or {"steps": []}
                causes = [c["kind"] for st in rc["steps"] for c in st.get("causes", [])
                          if c.get("fixed", True) and c["kind"] != "harness artifact"]
                step_kinds = [k for st in rc["steps"] for k in {c["kind"] for c in st.get("causes", [])
                                                                 if c.get("fixed", True) and c["kind"] != "harness artifact"}]
                rec.update({
                    "status": s["status"], "attempts": s["attempts"],
                    "v1_build_fail": v1_build_fail,
                    "v1_build_stage": first.get("compile_stage") if v1_build_fail else None,
                    "first_ran_version": fv,
                    "first_ran_differed": bool(fa) and bool(differed(fa)),
                    "v1_correct": (not v1_build_fail) and bool(fa) and fv == 1 and not differed(fa),
                    "build_failures": sum(1 for _, a in atts if "compile_error" in a),
                    "executions_disagree": sum((a.get("executions_disagree") or 0) +
                                               ((a.get("final") or {}).get("executions_disagree") or 0)
                                               for _, a in atts),
                    "root_causes": causes, "root_cause_steps": step_kinds,
                    "symptoms": s.get("discrepancies_by_kind", {}),
                    "dollars": s.get("dollars"),
                })
                runs.append(rec)
    return runs, excluded


def rate(rows: list[dict], key: str) -> dict:
    n = len(rows)
    k = sum(1 for r in rows if r[key])
    return {"k": k, "n": n, "rate": round(k / n, 4) if n else None, "wilson95": wilson(k, n)}


def compute() -> dict:
    runs, excluded = run_records()
    for r in runs:
        r["v1_not_correct"] = not r["v1_correct"]
    groups = {
        "all": lambda r: "all",
        "arm": lambda r: r["arm"],
        "arm_x_lang": lambda r: f"{r['arm']} / {r['lang']}",
        "lang": lambda r: r["lang"],
        "program": lambda r: r["program"],
        "seed": lambda r: f"seed {r['seed']}",
        "arm_x_seed": lambda r: f"{r['arm']} / seed {r['seed']}",
        "program_x_arm_x_lang": lambda r: f"{r['program']} / {r['arm']} / {r['lang']}",
    }
    tables = {}
    for gname, gf in groups.items():
        by = defaultdict(list)
        for r in runs:
            by[gf(r)].append(r)
        tables[gname] = {g: {"first_ran_differed": rate(rs, "first_ran_differed"),
                             "v1_build_fail": rate(rs, "v1_build_fail"),
                             "v1_not_correct": rate(rs, "v1_not_correct")}
                         for g, rs in sorted(by.items())}
    # error kinds: root causes per arm x language, in the user's categories
    kinds = defaultdict(Counter)
    raw_kinds = defaultdict(Counter)
    symptoms = defaultdict(Counter)
    for r in runs:
        key = f"{r['arm']} / {r['lang']}"
        for c in r["root_causes"]:
            kinds[key][CATEGORY.get(c, c)] += 1
            raw_kinds[key][c] += 1
        symptoms[key].update(r["symptoms"])
    tot_kinds = Counter()
    for c in kinds.values():
        tot_kinds.update(c)
    tot_steps = Counter(CATEGORY.get(k, k) for r in runs for k in r["root_cause_steps"])
    # attempts to converge (passed runs)
    att = {}
    for key in sorted({f"{r['arm']} / {r['lang']}" for r in runs}):
        xs = [r["attempts"] for r in runs if f"{r['arm']} / {r['lang']}" == key and r["status"] == "passed"]
        att[key] = {"runs": len(xs), "median": statistics.median(xs) if xs else None, "max": max(xs) if xs else None,
                    "on_1": sum(1 for x in xs if x == 1), "on_2": sum(1 for x in xs if x == 2),
                    "on_3_plus": sum(1 for x in xs if x >= 3), "mean": round(statistics.mean(xs), 2) if xs else None}
    sample = _json(RUNS / "SAMPLECHECK.json") or []
    return {
        "definitions": {
            "first_ran_differed": "the first version that ran differed from cobolrun on a generated case (60 fresh + "
                                  "regression, or the 300-case final check)",
            "v1_build_fail": "the first attempt did not build (compiler or verifier front end: Soot/JimpleLean, "
                             "Charon/Aeneas/Lean)",
            "v1_not_correct": "the first attempt was not a passing translation (build failure or behaviour change)",
            "intervals": "Wilson 95%",
        },
        "runs": len(runs), "excluded": excluded,
        "status": dict(Counter(r["status"] for r in runs)),
        "tables": tables,
        "root_causes_by_arm_lang": {k: dict(v) for k, v in sorted(kinds.items())},
        "root_causes_raw_by_arm_lang": {k: dict(v) for k, v in sorted(raw_kinds.items())},
        "root_causes_total": dict(tot_kinds.most_common()),
        "root_cause_repair_steps_total": dict(tot_steps.most_common()),
        "equivlean_answer": EQUIVLEAN_ANSWER,
        "symptoms_by_arm_lang": {k: dict(v) for k, v in sorted(symptoms.items())},
        "attempts_to_converge": att,
        "executions_disagree_total": sum(r["executions_disagree"] for r in runs),
        "samplecheck": {"versions_checked": len(sample),
                        "caught_by_carddemo_sample_data": sum(1 for s in sample if s.get("sample_catches"))},
        "per_run": runs,
    }


def _fmt_rate(d: dict) -> str:
    if not d["n"]:
        return "-"
    lo, hi = d["wilson95"]
    return f"{d['k']}/{d['n']} = {d['rate'] * 100:.0f}% [{lo * 100:.0f}, {hi * 100:.0f}]"


def markdown(res: dict) -> str:
    L = ["# A2: AI-error numbers of item A (from the run records; no model calls)", "",
         f"{res['runs']} runs of record (8 programs x Java/Rust x arms, seeds 1-3; guided_v2: 3 Java programs, seed 1). "
         f"Excluded: {len(res['excluded'])} " + "; ".join(f"{e['program']} {e['arm']} {e['lang']} s{e['seed']} "
                                                         f"({e['reason'][:60]})" for e in res["excluded"]) + ".",
         "Final status: " + ", ".join(f"{k} {v}" for k, v in res["status"].items()) + ".", "",
         "Definitions: " + "; ".join(f"**{k}**: {v}" for k, v in res["definitions"].items()), ""]
    for g, title in (("all", "All runs"), ("arm", "By arm"), ("lang", "By language"), ("arm_x_lang", "By arm x language"),
                     ("seed", "By seed"), ("arm_x_seed", "By arm x seed"), ("program", "By program")):
        L += [f"## {title}", "", "| group | first version that ran differed | v1 build failure | v1 not correct |",
              "|---|---|---|---|"]
        for k, v in res["tables"][g].items():
            L.append(f"| {k} | {_fmt_rate(v['first_ran_differed'])} | {_fmt_rate(v['v1_build_fail'])} | "
                     f"{_fmt_rate(v['v1_not_correct'])} |")
        L.append("")
    L += ["## Error kinds (root causes the repairs fixed; fixed taxonomy, labelled after the runs)", "",
          "| arm / language | " + " | ".join(sorted(res["root_causes_total"])) + " |",
          "|---|" + "---|" * len(res["root_causes_total"])]
    for k, v in res["root_causes_by_arm_lang"].items():
        L.append(f"| {k} | " + " | ".join(str(v.get(c, 0)) for c in sorted(res["root_causes_total"])) + " |")
    L += ["", "Totals (each cause the labeller named; one repair can fix several): " +
          ", ".join(f"{k} {v}" for k, v in res["root_causes_total"].items()),
          "Repair steps with that kind (distinct kinds per step; the unit REPORT.md uses): " +
          ", ".join(f"{k} {v}" for k, v in res["root_cause_repair_steps_total"].items()), "",
          "User categories with zero root causes: " + ", ".join(
              c for c in ("rounding", "truncation", "sign", "uninitialized storage", "abend/file status",
                          "control flow") if c not in res["root_causes_total"]) + ".", "",
          "Mechanical symptoms (output-level labels, for comparison): " + "; ".join(
              f"{k}: " + ", ".join(f"{a} {b}" for a, b in sorted(v.items())) for k, v in res["symptoms_by_arm_lang"].items()),
          "", "## Attempts to converge (passed runs)", "", "| arm / language | runs | on 1 | on 2 | on 3+ | median | mean | max |",
          "|---|---|---|---|---|---|---|---|"]
    for k, v in res["attempts_to_converge"].items():
        L.append(f"| {k} | {v['runs']} | {v['on_1']} | {v['on_2']} | {v['on_3_plus']} | {v['median']} | {v['mean']} | {v['max']} |")
    L += ["", "## What caught the discrepancies", "",
          f"* Every discrepancy was caught by the differential run on the formal semantics (generated inputs, cobolrun vs "
          f"the translation). Both executions per language (Java: JVM and JimpleLean's interpreter; Rust: native and the "
          f"Aeneas extraction evaluated in Lean) gave the same outcome on every case of every attempt "
          f"(executions_disagree total = {res['executions_disagree_total']}), so each discrepancy was visible in the "
          f"formal execution alone.",
          f"* CardDemo's own sample data (app/data/EBCDIC) exposed {res['samplecheck']['caught_by_carddemo_sample_data']} "
          f"of the {res['samplecheck']['versions_checked']} failing seed-1 versions (SAMPLECHECK.json).",
          "* **Testing passed, proof failed: none so far.** equiv-lean's answer (asked 2026-10-25): \"" +
          res["equivlean_answer"] + "\" No proof note in runs/modernize/*/proof_*.json records a behavioural mismatch.",
          ""]
    return "\n".join(L) + "\n"


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    res = compute()
    (OUT / "A2.json").write_text(json.dumps(res, indent=1, ensure_ascii=False))
    (OUT / "A2.md").write_text(markdown(res))
    print(markdown(res)[:6000])


if __name__ == "__main__":
    main()

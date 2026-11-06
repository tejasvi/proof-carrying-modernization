"""PREREG_C1b summary from the run's records: pass 1 -> pass 2 per unit, per function, transition table, new
witnesses and kernel verdicts, cost. Writes runs/prereg/C1b/SUMMARY.md and SUMMARY.json.

    python3 scripts/prereg_c1b_summary.py
"""
from __future__ import annotations

import csv
import glob
import json
import re
from collections import Counter
from pathlib import Path

VO = Path(__file__).resolve().parents[1]
C1B = VO / "runs" / "prereg" / "C1b"
UNITS = Path.home() / "fv_paper" / "prereg" / "C1b" / "units_c1b.tsv"


def main() -> None:
    units = {int(r["order"]): r for r in csv.DictReader(open(UNITS), delimiter="\t")}
    recs = {}
    for f in glob.glob(str(C1B / "c1b" / "records" / "*.json")):
        d = json.loads(Path(f).read_text())
        recs[int(d["order"])] = d
    rows, trans, fn2, reasons = [], Counter(), Counter(), Counter()
    new_witness, new_kernel = [], []
    model = core_s = 0.0
    for o in sorted(units):
        u = units[o]
        r = recs.get(o)
        p1 = u["pass1_outcome"]
        p2 = r["outcome"] if r else "not run"
        trans[(u["library"], p1, p2)] += 1
        model += (r or {}).get("model_dollars") or 0.0
        core_s += (r or {}).get("core_seconds") or 0.0
        p1f = dict(x.split("=", 1) for x in u["pass1_functions"].split(";") if "=" in x)
        p2f = {}
        for v in (r or {}).get("verdicts", []):
            name = v.get("unit") or v.get("function")
            kv = v.get("kernel_verdict")
            verdict = kv or v.get("verdict")
            p2f[name] = verdict
            fn2[verdict] += 1
            if verdict == "unknown":
                reasons[re.sub(r"\d+", "N", (v.get("reason") or v.get("detail") or ""))[:70]] += 1
            if v.get("verdict") == "behaviour_changed" and p1f.get(name) != "behaviour_changed":
                new_witness.append({"order": o, "function": name, "witness": v.get("witness") or v.get("detail")})
            if kv and p1f.get(name) not in ("equivalent", "changed_only_where_old_unsafe"):
                new_kernel.append({"order": o, "function": name, "verdict": kv, "theorem": v.get("theorem") or v.get("module"),
                                   "replay": v.get("kernel_replay")})
        rows.append({"order": o, "library": u["library"], "commit": u["commit"], "pass1": p1, "pass2": p2,
                     "pass1_functions": p1f, "pass2_functions": p2f, "error": (r or {}).get("error")})
    out = {"units": rows, "transitions": [{"library": k[0], "pass1": k[1], "pass2": k[2], "n": n}
                                          for k, n in sorted(trans.items())],
           "pass2_function_verdicts": dict(fn2), "unknown_reasons": dict(reasons.most_common()),
           "new_behaviour_changed": new_witness, "new_kernel_verdicts": new_kernel,
           "model_dollars": round(model, 4), "core_hours": round(core_s / 3600, 2)}
    (C1B / "SUMMARY.json").write_text(json.dumps(out, indent=1))
    lines = ["# PREREG_C1b summary (pass 2)", "",
             f"Units {len(rows)}; records {len(recs)}; model ${model:.2f}; {core_s / 3600:.1f} core-h.", "",
             "| library | pass 1 | pass 2 | n |", "|---|---|---|---|"]
    lines += [f"| {k[0]} | {k[1]} | {k[2]} | {n} |" for k, n in sorted(trans.items())]
    lines += ["", "Per-function verdicts (pass 2): " + ", ".join(f"{k} {n}" for k, n in fn2.most_common()),
              "Unknown reasons: " + "; ".join(f"{k} ({n})" for k, n in reasons.most_common()),
              "", f"New behaviour_changed witnesses: {len(new_witness)}"]
    lines += [f"- order {w['order']} {w['function']}" for w in new_witness]
    lines += ["", f"New kernel verdicts: {len(new_kernel)}"]
    lines += [f"- order {k['order']} {k['function']}: {k['verdict']} ({k['theorem']}; replay {k['replay']})"
              for k in new_kernel]
    (C1B / "SUMMARY.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()

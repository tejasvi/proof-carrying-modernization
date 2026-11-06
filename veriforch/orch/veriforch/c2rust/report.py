"""Per-arm numbers for the tiny-regex-c C → Rust runs.

    python3 -m veriforch.c2rust.report          # writes runs/c2rust/tiny-regex-c/REPORT.md and REPORT.json

For each run directory (<arm>, <arm>_s<N>): status, attempts, build failures by stage, mechanical discrepancy
kinds (versions in which each kind occurred), the last version's round and heldout counts, how its natively built
crate behaves on the C-UB cases (panics; agreement with the flat-memory result of the native gcc build), model
lines, cost and time. Versions outside the verifier's language (Charon/Aeneas/Lean rejected them) also report their
native counts (`native_only`).
"""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

from . import cref, rustrun

TRX = cref.TRX


def _json(p: Path):
    return json.loads(p.read_text()) if p.exists() else None


def ub_behaviour(run_dir: Path, version: int) -> dict | None:
    """The version on the round's C-UB cases (natively and in Lean): how many give no value (panic, Aeneas
    failure, time-out), and how many give the flat-memory result of the native gcc build. Runs the runner on those
    cases (cached per job list)."""
    ref = _json(TRX / "c" / "REFERENCE.json")
    src = run_dir / f"v{version}" / "rust"
    if ref is None or not (src / "src" / "lib.rs").exists():
        return None
    ub = ref["sets"]["round"]["ub"]
    res = rustrun.run_batch(src, [{"kind": "m", "pattern": u["pattern"], "text": u["text"]} for u in ub])
    if len(res) == 1 and "status" in res[0]:
        return None
    out = {"ub_cases": len(ub), "no_value_native": 0, "no_value_aeneas": 0, "flat_memory_result": 0}
    for u, r in zip(ub, res):
        nat, lean = r.get("native", {}), r.get("aeneas", {})
        out["no_value_native"] += "m" not in nat
        out["no_value_aeneas"] += "m" not in lean
        g = u.get("native") or {}
        out["flat_memory_result"] += "m" in nat and nat["m"] == [g.get("ret"), g.get("len")]
    return out


def run_row(d: Path) -> dict | None:
    s = _json(d / "summary.json")
    if s is None:
        return None
    stages, kinds, native_only = Counter(), Counter(), []
    last_eval = None
    for v in s["versions"]:
        a = _json(d / f"v{v}" / "attempt.json") or {}
        if "compile_error" in a:
            stages[a.get("compile_stage")] += 1
            fresh = _json(d / f"v{v}" / "fresh_native.json")
            if fresh:           # one process per job (fresh.py): exact also for a version with global state
                native_only.append({"version": v, "pass": fresh["pass"], "n": fresh["n"], "kinds": fresh["kinds"],
                                    "method": "fresh process per job"})
            elif a.get("native_only"):
                native_only.append({"version": v, **a["native_only"], "method": "one driver process"})
        for part in ("round", "heldout"):
            for k in (a.get(part) or {}).get("kinds", {}) or {}:
                kinds[k] += 1
        if "round" in a:
            last_eval = (v, a)
    row = {k: s.get(k) for k in ("arm", "seed", "status", "attempts", "model_lines", "dollars", "seconds",
                                 "llm_calls", "guide_sha256")}
    row.update({"build_failures": dict(stages), "kinds_versions": dict(kinds), "native_only": native_only})
    if last_eval:
        v, a = last_eval
        row["last_evaluated"] = {"version": v, "round": a.get("round"), "heldout": a.get("heldout")}
        row["ub_behaviour"] = ub_behaviour(d, v)
    return row


def main(argv: list[str]) -> int:
    rows = [r for d in sorted(TRX.iterdir()) if d.is_dir() and (d / "summary.json").exists()
            if (r := run_row(d))]
    ref = _json(TRX / "c" / "REFERENCE.json") or {"sets": {}}
    md = ["# tiny-regex-c (f2632c6) → Rust: translation runs", ""]
    for name, v in ref["sets"].items():
        md.append(f"- C reference, {name}: {v['cases']} cases; C-UB by site: "
                  + ", ".join(f"{k} {n}" for k, n in sorted(v["ub_kinds"].items()))
                  + f"; native gcc vs cirrun disagreements: {len(v['native_disagreements'])}")
    md += ["", "| arm | seed | status | attempts | build failures | discrepancy kinds (versions) | last round | "
           "heldout | C-UB: no value (native+Lean) / flat result | lines | $ | min |", "|" + "---|" * 12]
    for r in rows:
        le = r.get("last_evaluated") or {}
        rd, ho, ub = le.get("round") or {}, le.get("heldout") or {}, r.get("ub_behaviour") or {}
        md.append(f"| {r['arm']} | {r['seed']} | {r['status'][:40]} | {r['attempts']} | "
                  + (", ".join(f"{k} {n}" for k, n in sorted(r["build_failures"].items())) or "-") + " | "
                  + (", ".join(f"{k} {n}" for k, n in sorted(r["kinds_versions"].items())) or "-") + " | "
                  + (f"v{le['version']}: {rd.get('pass')}/{rd.get('n')}" if le else "-") + " | "
                  + (f"{ho.get('pass')}/{ho.get('n')}" if ho else "-") + " | "
                  + (f"{ub.get('no_value_native')}+{ub.get('no_value_aeneas')} / {ub.get('flat_memory_result')} of "
                     f"{ub.get('ub_cases')}" if ub else "-")
                  + f" | {r['model_lines']} | {r['dollars']:.2f} | {(r['seconds'] or 0) / 60:.0f} |")
    for r in rows:
        if r["native_only"]:
            md.append(f"- {r['arm']} s{r['seed']}: versions outside the verifier's language, natively: "
                      + "; ".join(f"v{x['version']} {x['pass']}/{x['n']} ({x['method']})" for x in r["native_only"]))
    proof = _json(TRX / "proof_rust.json")
    if proof:
        # equiv-lean's proof of the delivered crate (proof_rust.json, as item A's proof_<lang>.json)
        md += ["", f"## Proof (equiv-lean {proof.get('equivlean', '?')}): {proof.get('status')}", "",
               f"- `{proof.get('theorem')}`: {proof.get('statement')}",
               *[f"- {x}" for x in proof.get("also", [])],
               f"- crate: {proof.get('crate')}; C side: {proof.get('c_side')}; axioms: {', '.join(proof.get('axioms', []))}"]
    (TRX / "REPORT.md").write_text("\n".join(md) + "\n")
    (TRX / "REPORT.json").write_text(json.dumps(rows, indent=1))
    print("\n".join(md))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

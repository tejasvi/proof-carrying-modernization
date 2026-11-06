"""Counterexamples for stuck obligations, checked on the bridge's executable semantics.

For a unit whose contract did not prove, the model proposes argument values that satisfy the contract's
precondition and are likely to falsify its leftover goal. Each candidate is run on the formal semantics
(cirlean: `cirrun`, which evaluates the same Lean definitions the proofs reason about). The verdict:

* `refuted`: some candidate gives undefined behaviour (or violates the postcondition) on the semantics.
  The contract is false as stated; the finding says whether the input respects the calling convention
  (then the code needs a fix, or the API a documented precondition) or not (then the precondition is too
  weak).
* `not_refuted`: every candidate runs cleanly; the obligation is probably true and the proof is missing
  (automation gap or missing invariant).
* `tool_gap`: the semantics reports an unmodelled feature.
"""
from __future__ import annotations

import json
from pathlib import Path

from .llm import LLM, BudgetExceeded, LLMError
from .model import ConcreteInput, Finding, ReplayResult, read_json, write_json

CANDIDATES_SCHEMA = {
    "type": "object",
    "properties": {
        "candidates": {"type": "array", "items": {"type": "object"}},
        "notes": {"type": "string"},
    },
    "required": ["candidates", "notes"],
}

GAP_MARKERS = ("element access into a non-array", "unsupported operation", "call to an unknown function",
               "library model called with unexpected arguments", "not modelled", "unknown op",
               "external function without a model")


def check_unit(adapter, build, unit_name: str, llm: LLM, *, max_candidates: int = 8, log=print) -> Finding | None:
    from .scheduler import _unit_file
    path = _unit_file(build.dir / "units", unit_name)
    if not path.exists():
        return None
    oc = read_json(path)
    if oc["status"] in ("proved", "conditional", "gap", "blocked") or not oc.get("obligation"):
        return None
    unit = next(u for u in build.units if u.name == unit_name)
    ob = oc["obligation"]
    goals = (oc.get("result") or {}).get("goals", [])[:2]
    user = "\n\n".join([
        f"# Contract that did not prove: `{unit_name}`",
        f"```c\n{unit.source}\n```",
        f"```lean\ntheorem {ob['theorem']} {ob['contract']['binders']} :\n    {ob['contract']['statement']}\n```",
        "Leftover goals (truncated):\n" + "\n---\n".join(g[:3000] for g in goals),
        "Needs reported by the prover: " + json.dumps(oc.get("needs", [])),
        adapter.candidate_instructions(unit, build),
        f"Propose up to {max_candidates} candidates, most likely to falsify the leftover goal first. For each, say "
        "whether it satisfies the calling convention a caller of this function must respect "
        '("convention": true/false) and why. Give {"candidates": [...], "notes": "..."}.'])
    try:
        d = llm.ask_json(f"cex:{build.variant.name}:{unit_name}", adapter.prompt_pack(), user,
                         CANDIDATES_SCHEMA, effort="high")
    except (LLMError, BudgetExceeded) as e:
        log(f"  cex {unit_name}: no candidates ({e})")
        return None
    runs: list[ReplayResult] = []
    first_bad: ConcreteInput | None = None
    bad_convention = None
    gap = False
    for c in d.get("candidates", [])[:max_candidates]:
        args = c.get("args")
        if args is None:
            continue
        rr = adapter.run_semantic(unit, build, args)
        runs.append(rr)
        log(f"  cex {unit_name}: {json.dumps(args)[:100]} -> {rr.outcome} {rr.detail[:100]}")
        if rr.outcome == "ub":
            if any(m in rr.detail for m in GAP_MARKERS):
                gap = True
                continue
            if first_bad is None or (c.get("convention") and not bad_convention):
                first_bad = ConcreteInput(unit=unit_name, args=args, note=c.get("why", ""))
                bad_convention = bool(c.get("convention"))
    if first_bad is not None:
        verdict = "real_bug" if bad_convention else "missing_precondition"
        summary = (f"`{unit_name}` has undefined behaviour on the semantics for an input that "
                   + ("respects" if bad_convention else "violates") + " the calling convention")
    elif gap:
        verdict, summary = "tool_gap", f"`{unit_name}`: the semantics reached an unmodelled feature"
    else:
        verdict, summary = "unconfirmed", f"`{unit_name}`: no candidate refuted the contract (likely a proof gap)"
    f = Finding(unit=unit_name, variant=build.variant.name, summary=summary, goals=[g[:2000] for g in goals],
                counterexample=first_bad, replays=runs, verdict=verdict, explanation=d.get("notes", ""))
    write_json(_unit_file(build.dir / "findings", unit_name), f)
    return f

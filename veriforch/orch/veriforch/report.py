"""Run reports: one markdown file per target summarising every build, test promotion, patch and cost."""
from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path

from .model import read_json

STATUS_ORDER = ["proved", "conditional", "partial", "stuck", "blocked", "gap", "error", "budget"]
PROVED = ("proved", "conditional", "partial")


def statement_origin(o: dict) -> str:
    """mechanical: the statement came from the bridge (type-derived template, test unit); llm: the model chose
    the statement, so it is trusted only after review."""
    c = ((o.get("obligation") or {}).get("contract") or {})
    note = (c.get("note") or "").lower()
    # bridge templates mark their notes at the start ("template: ...", "generic no-unexpected-exception contract
    # (template)", "cirinv proved..."); a model proposal that merely mentions the word must not count
    if c.get("origin") in ("template", "mechanical") or note.startswith(("template", "generic no-unexpected", "cirinv")):
        return "mechanical"
    return o.get("statement_origin") or "llm"


def collect(run_dir: Path) -> dict:
    builds = []
    for vj in sorted(run_dir.glob("*/*/verify.json")):
        version, variant = vj.parent.parent.name, vj.parent.name
        outcomes = read_json(vj)
        tests = vj.parent / "tests" / "theorems.json"
        names = {}
        uj = vj.parent / "units.json"
        if uj.exists():
            for u in read_json(uj):
                sig = u.get("signature") or {}
                dem = sig.get("demangled") if isinstance(sig, dict) else ""
                if dem and dem != u["name"]:
                    names[u["name"]] = dem
        builds.append({"version": version, "variant": variant, "outcomes": outcomes, "names": names,
                       "tests": read_json(tests) if tests.exists() else []})
    usage = []
    up = run_dir / "llm" / "usage.jsonl"
    if up.exists():
        for line in up.read_text().splitlines():
            try:
                usage.append(json.loads(line))
            except ValueError:
                pass
    patches = []
    for cj in sorted(run_dir.glob("patches/*/certificate.json")):
        patches.append({"id": cj.parent.name, **read_json(cj)})
    return {"builds": builds, "usage": usage, "patches": patches}


def render(target_name: str, data: dict) -> str:
    L = [f"# verif-orchestrator report: {target_name}", ""]
    total = Counter()
    gaps = defaultdict(set)
    for b in data["builds"]:
        oc = b["outcomes"]
        c = Counter(o["status"] for o in oc.values())
        total.update(c)
        L += [f"## {b['version']} / {b['variant']}", "",
              "| unit | status | attempts | Lean+LLM s | assumes | needs | note |", "|---|---|---|---|---|---|---|"]
        for name, o in sorted(oc.items(), key=lambda kv: (STATUS_ORDER.index(kv[1]["status"])
                                                          if kv[1]["status"] in STATUS_ORDER else 99, kv[0])):
            if o["status"] == "gap":
                gaps[o.get("detail", "").split(";")[0]].add(name)
            shown = b.get("names", {}).get(name, name)
            shown = shown if len(shown) <= 90 else shown[:87] + "..."
            st = o["status"] + (" (review)" if o["status"] in PROVED and statement_origin(o) != "mechanical" else "")
            L.append(f"| `{shown}` | {st} | {o.get('attempts', 0)} | {o.get('seconds', 0)} | "
                     f"{', '.join(o.get('assumes', [])) or ''} | {'; '.join(o.get('needs', []))[:120]} | "
                     f"{o.get('detail', '')[:80]} |")
        L.append("")
        L.append("Summary: " + ", ".join(f"{k} {c[k]}" for k in STATUS_ORDER if c.get(k)))
        mech = sum(1 for o in oc.values() if o["status"] in PROVED and statement_origin(o) == "mechanical")
        review = sum(1 for o in oc.values() if o["status"] in PROVED and statement_origin(o) != "mechanical")
        L.append(f"Proved with a mechanical statement: {mech}; proved with a model-written statement "
                 f"(needs review, not a headline result): {review}.")
        if b["tests"]:
            t = b["tests"]
            L += ["", f"Model-proposed test generalisations (needs review, not headline): {len(t)} "
                  f"({sum(x['kind'] == 'concrete' for x in t)} concrete, {sum(x['kind'] == 'generalized' for x in t)} generalized); "
                  f"{sum(bool(x.get('elaborates')) for x in t)} elaborate, {sum(x.get('status') == 'proved' for x in t)} proved."]
        L.append("")
    tool_gaps = defaultdict(set)
    for b in data["builds"]:
        for name, o in b["outcomes"].items():
            for nd in o.get("needs", []):
                if nd.lower().startswith("tool_gap"):
                    tool_gaps[nd.split(":", 1)[1].strip()[:300]].add(f"{b['variant']}:{name}")
    if tool_gaps:
        L += ["## Proof-automation gaps diagnosed by the proposal loop", ""]
        for text, where in sorted(tool_gaps.items()):
            L.append(f"* {text} ({', '.join(sorted(where))})")
        L.append("")
    if gaps:
        L += ["## Bridge gaps (feature requests to the bridge owners)", ""]
        for reason, units in sorted(gaps.items()):
            L.append(f"* `{reason}`: {', '.join(sorted(units))}")
        L.append("")
    if data["patches"]:
        L += ["## Patches", "", "| id | unit | new_safe | conservative | changed inputs |", "|---|---|---|---|---|"]
        for p in data["patches"]:
            L.append(f"| {p['id']} | `{p.get('unit', '')}` | {p.get('new_safe_status', '')} | "
                     f"{p.get('conservative_status', '')} | {p.get('changed_set', '')[:100]} |")
        L.append("")
    u = data["usage"]
    if u:
        dollars = sum(x.get("dollars", 0) for x in u)
        by_kind = Counter()
        for x in u:
            by_kind[x["task"].split(":")[0] if ":" in x["task"] else x["task"]] += x.get("dollars", 0)
        L += ["## Cost", "", f"LLM: {len(u)} calls, ${dollars:.2f} at list price; "
              f"{sum(x.get('cache_read', 0) for x in u):,} cached input tokens.", ""]
    L += ["## Totals", "", ", ".join(f"{k} {total[k]}" for k in STATUS_ORDER if total.get(k)), ""]
    return "\n".join(L)


def write_report(run_dir: Path, target_name: str) -> Path:
    data = collect(run_dir)
    out = run_dir / "reports"
    out.mkdir(parents=True, exist_ok=True)
    p = out / "report.md"
    p.write_text(render(target_name, data))
    (out / "report.json").write_text(json.dumps({k: v for k, v in data.items() if k != "usage"}, indent=1))
    return p


def summary_all(runs_root: Path) -> str:
    """One table over every target under runs/: units per status, test theorems, patches, LLM dollars."""
    rows = []
    for rd in sorted(p for p in runs_root.iterdir() if p.is_dir() and not p.name.startswith(("patch_", "jsmn_"))):
        data = collect(rd)
        if not data["builds"] and not data["patches"]:
            continue
        c = Counter(o["status"] for b in data["builds"] for o in b["outcomes"].values())
        c["mech"] = sum(1 for b in data["builds"] for o in b["outcomes"].values()
                        if o["status"] in PROVED and statement_origin(o) == "mechanical")
        c["review"] = sum(1 for b in data["builds"] for o in b["outcomes"].values()
                          if o["status"] in PROVED and statement_origin(o) != "mechanical")
        tests = [t for b in data["builds"] for t in b["tests"]]
        dollars = sum(x.get("dollars", 0) for x in data["usage"])
        lean_s = sum(float(o.get("seconds", 0)) for b in data["builds"] for o in b["outcomes"].values())
        n_units = sum(len(b["outcomes"]) for b in data["builds"])
        rows.append((rd.name, len(data["builds"]), n_units, c, tests, len(data["patches"]), dollars, lean_s))
    L = ["| target | builds | units | proved, mechanical statement | proved, model-stated (review) | stuck | gap | blocked | model test generalisations, review (proved) | patches | LLM $ | unit time s |",
         "|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for name, nb, nu, c, tests, npatch, dollars, lean_s in rows:
        L.append(f"| {name} | {nb} | {nu} | {c.get('mech', 0)} | {c.get('review', 0)} | {c.get('stuck', 0)} | "
                 f"{c.get('gap', 0)} | {c.get('blocked', 0)} | {len(tests)} ({sum(t.get('status') == 'proved' for t in tests)}) | "
                 f"{npatch} | {dollars:.2f} | {lean_s:.0f} |")
    return "\n".join(L)


METRIC_DEFINITIONS = """Definitions (fixed; computed from the run directories, primary version v0 only; CI revisions counted in
the CI columns):
* units: functions/methods/programs extracted from the build artifacts (units.json of every v0 build).
* in scope: units the bridge models (scope = in_scope).
* proved (mechanical): proved/conditional/partial units whose theorem statement was written without the model
  (bridge template, test unit as written, entry point quantified by type).
  Test units whose compiled body makes no call (their checks compiled out under the build's flags) are shown
  separately as "+N trivial" and not counted. Proofs by native evaluation (native_decide, which also trusts Lean's
  compiler; axiom Lean.ofReduceBool) are shown separately as "+N native"; every counted proof uses only propext,
  Classical.choice and Quot.sound.
* proved (model-stated, review): proved units whose statement the model wrote; kernel-checked, needs human review.
* human proof lines: tactic lines written by a person (0 by construction: every script is generated).
* model proof lines: tactic lines of accepted proofs proposed by the model (LLM proposals, and cached/reused ones).
* tool proof lines: tactic lines of accepted proofs from bridge templates.
* LLM $/unit and s/unit: LLM list-price dollars of the target / units in scope; sum of per-unit scheduler wall time
  (Lean checks + LLM calls) / units in scope. Each Lean check's wall time includes the core-hour guard (about 1 s
  since 10-24 02:00Z; runs before then are quantised to its 5 s poll).
* certified fixes: distinct functions with an accepted patch certificate (new_safe and conservative proved,
  std axioms; a function patched twice counts once).
* CI verdicts: per changed unit of every `vo ci` run: equivalent / changed only where old unsafe / behaviour
  changed (with a witness) / unknown."""


def paper_metrics(runs_root: Path) -> tuple[str, list[dict]]:
    rows = []
    for rd in sorted(p for p in runs_root.iterdir() if p.is_dir() and not p.name.startswith(("patch_", "jsmn_"))):
        units = in_scope = mech = trivial = native = review = h_lines = m_lines = t_lines = 0
        secs = 0.0
        for vd in sorted((rd / "v0").glob("*")) if (rd / "v0").exists() else []:
            uj, vj = vd / "units.json", vd / "verify.json"
            if uj.exists():
                us = read_json(uj)
                units += len(us)
                in_scope += sum(1 for u in us if u.get("scope") == "in_scope")
            if vj.exists():
                for o in read_json(vj).values():
                    secs += float(o.get("seconds") or 0)
                    if o["status"] not in PROVED:
                        continue
                    if ((o.get("obligation") or {}).get("contract") or {}).get("strength") == "trivial":
                        trivial += 1            # a test with no call in its compiled body: not counted as proved
                        continue
                    if o.get("trust") == "native":
                        native += 1             # native_decide: also trusts Lean's compiler, counted apart
                        continue
                    if statement_origin(o) == "mechanical":
                        mech += 1
                    else:
                        review += 1
                    proof = (o.get("obligation") or {}).get("proof") or {}
                    note = (((o.get("obligation") or {}).get("contract") or {}).get("note") or "").lower()
                    n = len([l for l in (proof.get("tactics") or "").splitlines() if l.strip()])
                    # a template proof stays a tool proof when a later run takes it from the cache
                    if proof.get("origin") == "template" or note.startswith(("template", "generic no-unexpected",
                                                                             "cirinv")):
                        t_lines += n
                    else:
                        m_lines += n
        dollars = 0.0
        up = rd / "llm" / "usage.jsonl"
        if up.exists():
            for line in up.read_text().splitlines():
                try:
                    dollars += json.loads(line).get("dollars", 0.0)
                except ValueError:
                    pass
        fixed_units = set()
        for cj in rd.glob("patches/*/certificate.json"):
            c = read_json(cj)
            if c.get("new_safe_status") == "proved" and c.get("conservative_status") == "proved":
                fixed_units.add(c.get("unit"))
        fixes = len(fixed_units)          # distinct functions with an accepted certificate
        ci = Counter()
        for cj in rd.glob("ci/*/ci.json"):
            for v in read_json(cj).get("variants", {}).values():
                for u in v.get("units", []):
                    if u.get("equivalence"):
                        ci[u["equivalence"].get("verdict", "unknown")] += 1
        if not (units or fixes or sum(ci.values())):
            continue
        rows.append({"target": rd.name, "units": units, "in_scope": in_scope, "proved_mechanical": mech,
                     "trivial_tests": trivial, "native_proofs": native,
                     "proved_model_stated": review, "human_proof_lines": h_lines, "model_proof_lines": m_lines,
                     "tool_proof_lines": t_lines, "llm_dollars": round(dollars, 2),
                     "llm_dollars_per_unit": round(dollars / in_scope, 3) if in_scope else None,
                     "seconds_per_unit": round(secs / in_scope, 1) if in_scope else None,
                     "certified_fixes": fixes, "ci": dict(ci)})
    tot = {k: sum(r[k] for r in rows) for k in ("units", "in_scope", "proved_mechanical", "trivial_tests",
                                                "native_proofs",
                                                "proved_model_stated",
                                                "human_proof_lines", "model_proof_lines", "tool_proof_lines",
                                                "certified_fixes")}
    tot["llm_dollars"] = round(sum(r["llm_dollars"] for r in rows), 2)
    tci = Counter()
    for r in rows:
        tci.update(r["ci"])
    L = ["| target | units | in scope | proved (mechanical) | proved (model-stated, review) | human proof lines | "
         "model proof lines | tool proof lines | LLM $/unit | s/unit | certified fixes | CI: equiv / old-unsafe / changed / unknown |",
         "|---|---|---|---|---|---|---|---|---|---|---|---|"]

    def cis(c):
        return (f"{c.get('equivalent', 0)} / {c.get('changed_only_where_old_unsafe', 0)} / "
                f"{c.get('behaviour_changed', 0)} / {c.get('unknown', 0)}")
    for r in rows:
        triv = (f" (+{r['trivial_tests']} trivial)" if r["trivial_tests"] else "") + \
            (f" (+{r['native_proofs']} native)" if r["native_proofs"] else "")
        L.append(f"| {r['target']} | {r['units']} | {r['in_scope']} | {r['proved_mechanical']}{triv} | "
                 f"{r['proved_model_stated']} | {r['human_proof_lines']} | {r['model_proof_lines']} | "
                 f"{r['tool_proof_lines']} | {r['llm_dollars_per_unit'] if r['llm_dollars_per_unit'] is not None else '-'} | "
                 f"{r['seconds_per_unit'] if r['seconds_per_unit'] is not None else '-'} | {r['certified_fixes']} | {cis(r['ci'])} |")
    ttriv = (f" (+{tot['trivial_tests']} trivial)" if tot["trivial_tests"] else "") + \
        (f" (+{tot['native_proofs']} native)" if tot["native_proofs"] else "")
    L.append(f"| **total** | {tot['units']} | {tot['in_scope']} | {tot['proved_mechanical']}{ttriv} | {tot['proved_model_stated']} | "
             f"{tot['human_proof_lines']} | {tot['model_proof_lines']} | {tot['tool_proof_lines']} | "
             f"{round(tot['llm_dollars'] / tot['in_scope'], 3) if tot['in_scope'] else '-'} | - | {tot['certified_fixes']} | {cis(tci)} |")
    return "\n".join(L) + "\n\n" + METRIC_DEFINITIONS + "\n", rows

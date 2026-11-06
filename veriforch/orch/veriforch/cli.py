"""Command line: `python -m veriforch <command> TARGET.toml [options]`."""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

from .config import load_target
from .lean import VO_ROOT
from .model import write_json


def adapter_for(lang: str):
    if lang == "cir":
        from .adapters.cir.adapter import CirAdapter
        return CirAdapter()
    if lang == "strictts":
        from .adapters.strictts.adapter import StrictTSAdapter
        return StrictTSAdapter()
    if lang == "jimple":
        from .adapters.jimple.adapter import JimpleAdapter
        return JimpleAdapter()
    if lang == "cobol":
        from .adapters.cobol.adapter import CobolAdapter
        return CobolAdapter()
    if lang == "rust":
        from .adapters.rust.adapter import RustAdapter
        return RustAdapter()
    raise SystemExit(f"no adapter for language {lang!r} yet")


def run_dir_for(target) -> Path:
    return VO_ROOT / "runs" / target.name


def cmd_scan(args) -> int:
    t = load_target(args.target)
    ad = adapter_for(t.lang)
    builds = []
    for v in t.variants:
        if args.variant and v.name not in args.variant:
            continue
        b = ad.build(t, v, run_dir_for(t))
        builds.append(b)
        write_json(b.dir / "units.json", b.units)
        print(f"[{v.name}] {len(b.units)} units", flush=True)
        for u in b.units:
            print(f"  {u.name:28} {u.kind:8} {u.scope:40} callees={u.callees}", flush=True)
    _link(t, builds)
    return 0


def _link(t, builds) -> None:
    """Whole-program call graph across translation units (compile_commands.json targets)."""
    if t.lang == "cir" and t.extra.get("compile_commands") and builds:
        from .adapters.cir.compdb import link_callgraph
        g = link_callgraph(builds, run_dir_for(t) / t.version)
        print(f"call graph: {len(g['nodes'])} units, {len(g['edges'])} edges, {g['cross_tu_edges']} across TUs",
              flush=True)


def cmd_verify(args) -> int:
    from .llm import LLM
    from .scheduler import verify_build
    t = load_target(args.target)
    ad = adapter_for(t.lang)
    rd = run_dir_for(t)
    llm = None if args.no_llm else LLM(rd, budget=args.budget)
    summary = {}
    variants = [v for v in t.variants if not args.variant or v.name in args.variant]

    builds = []

    def one(v):
        b = ad.build(t, v, rd)
        builds.append(b)
        write_json(b.dir / "units.json", b.units)
        print(f"[{v.name}] verifying {len(b.units)} units", flush=True)
        lg = lambda s, n=v.name: print(f"[{n}] {s.strip()}", flush=True)
        given_hints = None
        if getattr(args, "hint_file", None):
            # a contract requirement for named units, e.g. from a bridge owner whose proof of a caller needs a
            # weaker precondition or a stronger postcondition: the unit is re-opened with it (cache bypassed)
            given_hints = json.loads(Path(args.hint_file).read_text())
            lg(f"re-opening {sorted(given_hints)} with requirements from {args.hint_file}")
        oc = verify_build(ad, b, llm, attempts=args.attempts, only=set(args.only) if args.only else None,
                          jobs=args.jobs, retry_stuck=args.retry_stuck, check_timeout=args.check_timeout,
                          hints=given_hints, log=lg)
        if args.refine and llm is not None:
            from .scheduler import refinement_hints
            hints = refinement_hints(b, oc)
            if hints:
                lg(f"refinement pass: re-opening {sorted(hints)} on their callers' request")
                # unaffected stuck units keep their negative cache; callers of re-opened callees get new keys
                oc = verify_build(ad, b, llm, attempts=args.attempts, jobs=args.jobs, hints=hints, log=lg)
        summary[v.name] = {n: o.status for n, o in oc.items()}
        # proofs by trust: kernel (checked by Lean's kernel) and native (compiled evaluation, Lean.ofReduceBool)
        tr = {}
        for o in oc.values():
            if o.status in ("proved", "conditional", "partial"):
                tr[o.trust or "?"] = tr.get(o.trust or "?", 0) + 1
        lg("proofs by trust: " + (", ".join(f"{k} {n}" for k, n in sorted(tr.items())) or "none"))

    if variants:
        ad.build(t, variants[0], rd).pkg.ensure()          # bridge libraries once, before any concurrency
    if args.variant_jobs > 1:
        from concurrent.futures import ThreadPoolExecutor, as_completed
        with ThreadPoolExecutor(max_workers=args.variant_jobs) as ex:
            futs = {ex.submit(one, v): v.name for v in variants}
            for f in as_completed(futs):        # report a failed variant as soon as it fails
                try:
                    f.result()
                except Exception as e:          # one broken file must not stop the others
                    print(f"variant {futs[f]} failed: {type(e).__name__}: {e}"[:2000], flush=True)
    else:
        for v in variants:
            one(v)
    _link(t, builds)
    print(json.dumps(summary, indent=1))
    if llm:
        print(f"LLM: {llm.usage.calls} calls, ${llm.usage.dollars:.2f}")
    return 0


def cmd_promote(args) -> int:
    from .llm import LLM
    from .testpromo import promote_tests
    t = load_target(args.target)
    ad = adapter_for(t.lang)
    rd = run_dir_for(t)
    llm = LLM(rd, budget=args.budget)
    for v in t.variants:
        if args.variant and v.name not in args.variant:
            continue
        b = ad.build(t, v, rd)
        b.pkg.ensure()
        g = b.info["gen_module"]
        b.gen_modules[g] = b.pkg.check(g, b.pkg.src(g).read_text(), timeout=900).cache_key
        ths = promote_tests(ad, b, llm, log=lambda s: print(s, flush=True))
        print(f"[{v.name}] {len(ths)} theorems, {sum(t.elaborates for t in ths)} elaborate")
    print(f"LLM: {llm.usage.calls} calls, ${llm.usage.dollars:.2f}")
    return 0


def cmd_report(args) -> int:
    from .report import write_report
    t = load_target(args.target)
    p = write_report(run_dir_for(t), t.name)
    print(p.read_text())
    return 0


def cmd_metrics(args) -> int:
    from .report import paper_metrics
    text, rows = paper_metrics(VO_ROOT / "runs")
    (VO_ROOT / "runs" / "metrics.md").write_text(text)
    write_json(VO_ROOT / "runs" / "metrics.json", rows)
    print(text)
    return 0


def cmd_summary(args) -> int:
    from .report import summary_all
    print(summary_all(VO_ROOT / "runs"))
    return 0


def cmd_ci(args) -> int:
    import os
    from .ci import run_ci
    from .llm import LLM
    t = load_target(args.target)
    # VO_CI_RUN_DIR: a run directory of its own (caches included), e.g. one per pre-registered study
    rd = Path(os.environ["VO_CI_RUN_DIR"]).resolve() if os.environ.get("VO_CI_RUN_DIR") else run_dir_for(t)
    return run_ci(adapter_for(t.lang), t, args.base, args.head, rd, LLM(rd, budget=args.budget),
                  variants=args.variant, attempts=args.attempts, equivalence=not args.no_equiv,
                  check_timeout=args.check_timeout, jobs=args.jobs, log=lambda s: print(s, flush=True))


def cmd_run(args) -> int:
    """End to end: build -> bottom-up verify -> promote tests -> prove tests -> counterexamples -> report."""
    from .cex import check_unit
    from .llm import LLM
    from .report import write_report
    from .scheduler import verify_build
    from .testpromo import promote_tests, prove_tests
    t = load_target(args.target)
    ad = adapter_for(t.lang)
    rd = run_dir_for(t)
    llm = LLM(rd, budget=args.budget)
    log = lambda s: print(s, flush=True)
    for v in t.variants:
        if args.variant and v.name not in args.variant:
            continue
        b = ad.build(t, v, rd)
        write_json(b.dir / "units.json", b.units)
        b.pkg.ensure()
        log(f"[{v.name}] {len(b.units)} units: verify")
        oc = verify_build(ad, b, llm, attempts=args.attempts, jobs=args.jobs, retry_stuck=args.retry_stuck, log=log)
        if t.tests and not args.skip_tests and hasattr(ad, "placeholder_tactic"):
            log(f"[{v.name}] promote tests")
            promote_tests(ad, b, llm, log=log)
            prove_tests(ad, b, llm, log=log)
        if hasattr(ad, "run_semantic"):
            for name, o in oc.items():
                if o.status in ("stuck",):
                    f = check_unit(ad, b, name, llm, log=log)
                    if f:
                        log(f"  finding {name}: {f.verdict}: {f.summary}")
                    if f and f.verdict == "real_bug" and args.patch:
                        from .loop import run_patch_loop
                        ob = o.obligation or {}
                        contract = {"binders": ob.get("contract", {}).get("binders", ""),
                                    "statement": ob.get("contract", {}).get("statement", ""),
                                    "tactics": ob.get("proof", {}).get("tactics", "")}
                        res = run_patch_loop(ad, t, v, f.to_json(), contract, llm, rd, revisions=1,
                                             reverify=True, log=log)
                        log(f"  patch for {name}: {'accepted' if res['accepted'] else 'not accepted'} ({res['id']})")
    p = write_report(rd, t.name)
    log(f"report: {p}; LLM {llm.usage.calls} calls ${llm.usage.dollars:.2f}")
    return 0


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="veriforch")
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("scan", help="build, translate, extract units and the call graph")
    s.add_argument("target")
    s.add_argument("--variant", action="append")
    s.set_defaults(fn=cmd_scan)
    s = sub.add_parser("verify", help="bottom-up contract verification")
    s.add_argument("target")
    s.add_argument("--variant", action="append")
    s.add_argument("--only", action="append", help="verify only these units (callees must already be cached)")
    s.add_argument("--attempts", type=int, default=4)
    s.add_argument("--budget", type=float, default=20.0, help="LLM dollar budget for this run")
    s.add_argument("--no-llm", action="store_true")
    s.add_argument("--jobs", type=int, default=2, help="independent call-graph components verified concurrently")
    s.add_argument("--variant-jobs", type=int, default=1, help="build variants (e.g. files) verified concurrently")
    s.add_argument("--retry-stuck", action="store_true", help="re-attempt units that failed before with the same inputs")
    s.add_argument("--check-timeout", type=int, default=300,
                   help="wall-clock seconds per Lean check (concrete test theorems over strings need ~3600)")
    s.add_argument("--refine", action="store_true", help="second pass: re-open callee contracts that stuck callers need")
    s.add_argument("--hint-file", help="JSON {unit: requirement text}: re-open these units with the requirement "
                                       "(e.g. a caller's proof needs a weaker precondition / stronger postcondition)")
    s.set_defaults(fn=cmd_verify)
    s = sub.add_parser("promote", help="model-proposed test generalisations (needs review; headline test theorems are mechanical, from verify)")
    s.add_argument("target")
    s.add_argument("--variant", action="append")
    s.add_argument("--budget", type=float, default=10.0)
    s.set_defaults(fn=cmd_promote)
    s = sub.add_parser("report", help="write runs/<target>/reports/report.md")
    s.add_argument("target")
    s.set_defaults(fn=cmd_report)
    s = sub.add_parser("metrics", help="the evaluation table with fixed definitions (runs/metrics.md, .json)")
    s.set_defaults(fn=cmd_metrics)
    s = sub.add_parser("summary", help="one table over every target under runs/")
    s.set_defaults(fn=cmd_summary)
    s = sub.add_parser("ci", help="incremental verification between two git revisions")
    s.add_argument("target")
    s.add_argument("--base", required=True)
    s.add_argument("--head", required=True)
    s.add_argument("--variant", action="append")
    s.add_argument("--attempts", type=int, default=3)
    s.add_argument("--budget", type=float, default=10.0)
    s.add_argument("--no-equiv", action="store_true",
                   help="skip the old ≡ new verdicts (e.g. to verify with a bridge pin equiv-lean is not built on)")
    s.add_argument("--check-timeout", type=int, default=300, help="wall-clock seconds per Lean check")
    s.add_argument("--jobs", type=int, default=1, help="independent call-graph components verified concurrently")
    s.set_defaults(fn=cmd_ci)
    s = sub.add_parser("patch", help="prove-or-patch: certified source patch for a confirmed finding")
    s.add_argument("target")
    s.add_argument("--finding", required=True, help="JSON: unit, variant, summary, goals, contract{binders,statement,tactics}")
    s.add_argument("--revisions", type=int, default=1)
    s.add_argument("--budget", type=float, default=8.0)
    s.add_argument("--proposal", action="append", help="diff file to try instead of asking the LLM (repeatable)")
    s.add_argument("--reverify", action="store_true", help="re-verify the patched unit and its callers")
    s.add_argument("--no-llm", action="store_true", help="only try the --proposal diffs")
    s.set_defaults(fn=cmd_patch)
    s = sub.add_parser("run", help="end to end: verify, tests, counterexamples, report")
    s.add_argument("target")
    s.add_argument("--variant", action="append")
    s.add_argument("--attempts", type=int, default=3)
    s.add_argument("--jobs", type=int, default=2)
    s.add_argument("--budget", type=float, default=20.0)
    s.add_argument("--skip-tests", action="store_true")
    s.add_argument("--patch", action="store_true", help="run the certified patch loop on confirmed defects")
    s.add_argument("--retry-stuck", action="store_true")
    s.set_defaults(fn=cmd_run)
    s = sub.add_parser("cex", help="counterexample step for chosen stuck units (outside `vo run`)")
    s.add_argument("target")
    s.add_argument("--only", action="append", required=True, help="units to check (repeatable)")
    s.add_argument("--variant", action="append")
    s.add_argument("--budget", type=float, default=2.0, help="LLM dollar budget for this run")
    s.add_argument("--max-candidates", type=int, default=8)
    s.set_defaults(fn=cmd_cex)
    args = p.parse_args(argv)
    return args.fn(args)


def cmd_cex(args) -> int:
    """The counterexample step of `vo run` for chosen units (prereg D, R7): for each unit whose stored verify outcome
    is stuck (or out of budget) with an obligation, the model proposes inputs and the bridge's executable semantics
    runs them; the verdict goes to findings/<unit>.json (cex.check_unit). Units without such an outcome are
    skipped and reported."""
    from .cex import check_unit
    from .llm import LLM
    from .scheduler import _unit_file
    t = load_target(args.target)
    ad = adapter_for(t.lang)
    if not hasattr(ad, "run_semantic"):
        print(json.dumps({"error": f"the {t.lang} bridge has no executable semantics"}))
        return 2
    rd = run_dir_for(t)
    llm = LLM(rd, budget=args.budget)
    res: dict[str, dict] = {}
    for v in t.variants:
        if args.variant and v.name not in args.variant:
            continue
        b = ad.build(t, v, rd)
        names = {u.name for u in b.units}
        for name in args.only:
            if name not in names:
                continue
            f = check_unit(ad, b, name, llm, max_candidates=args.max_candidates, log=lambda s: print(s, flush=True))
            res[name] = ({"variant": v.name, "verdict": f.verdict, "summary": f.summary,
                          "finding": str(_unit_file(b.dir / "findings", name))} if f else
                         {"variant": v.name, "verdict": None, "summary": "no stuck outcome with an obligation"})
    for name in args.only:
        res.setdefault(name, {"verdict": None, "summary": "not a unit of the target"})
    print(json.dumps(res, indent=1))
    print(f"LLM: {llm.usage.calls} calls, ${llm.usage.dollars - llm._start_dollars:.2f}")
    return 0


def cmd_patch(args) -> int:
    # scripts/vo sets VO_CIRLEAN_DIR/PIN to the cirlean equiv-lean was built against (deps/cirlean, 87a2905)
    from .llm import LLM
    from .loop import load_finding, run_patch_loop
    t = load_target(args.target)
    ad = adapter_for(t.lang)
    rd = run_dir_for(t)
    req = load_finding(Path(args.finding))
    finding = {k: v for k, v in req.items() if k != "contract"}
    variant = next((v for v in t.variants if v.name == finding.get("variant", "default")), t.variants[0])
    props = None
    if args.proposal:
        props = [{"diff": Path(f).read_text(), "rationale": f"given diff {Path(f).name}", "kind": "general"}
                 for f in args.proposal]
    llm = None if args.no_llm else LLM(rd, budget=args.budget)
    res = run_patch_loop(ad, t, variant, finding, req["contract"], llm, rd, revisions=args.revisions,
                         proposals=props, reverify=args.reverify, log=lambda s: print(s, flush=True))
    print(json.dumps({"id": res["id"], "accepted": res["accepted"],
                      "attempts": [a.get("status") for a in res["attempts"]]}, indent=1))
    if llm:
        print(f"LLM: {llm.usage.calls} calls, ${llm.usage.dollars:.2f}")
    return 0 if res["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())

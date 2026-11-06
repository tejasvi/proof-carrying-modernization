"""Incremental verification between two revisions (CI mode).

Both revisions are materialised from the target's git repository (`git archive`, never a checkout of the
target's own tree), built, and verified with the shared caches: a unit whose body and callee contracts are
unchanged reuses its proof script (no LLM call) and, when the Lean inputs are byte-identical, its .olean.
The delta report lists changed units, re-proved units, regressions (proved at base, not at head) and
contract drift (a unit's proved contract statement changed), and the exit status is non-zero on a
regression.
"""
from __future__ import annotations

import dataclasses
import subprocess
import time
from collections import Counter
from pathlib import Path

from .model import Target, read_json, write_json


def _eq(v: dict | None) -> str:
    if not v:
        return ""
    w = v.get("witness")
    return v["verdict"] + (f" (witness {w.get('args', w)})" if w else "")


def materialise(target: Target, rev: str, run_dir: Path) -> Target:
    dst = run_dir / "src" / rev
    if not dst.exists():
        dst.mkdir(parents=True)
        arch = subprocess.run(["git", "-C", target.root, "archive", rev], stdout=subprocess.PIPE, check=True)
        subprocess.run(["tar", "-x", "-C", str(dst)], input=arch.stdout, check=True)
    t = dataclasses.replace(target, root=str(dst), version=rev, extra=dict(target.extra))
    if t.extra.get("sources_present_only"):
        # a library target names its source files at the pinned head; an older revision builds the ones it has
        t.sources = [s for s in target.sources if (dst / s).exists()]
        t.variants = [dataclasses.replace(v, sources=[s for s in v.sources if (dst / s).exists()])
                      for v in target.variants]
    if t.lang == "cir" and t.extra.get("compile_commands"):
        from .adapters.cir.compdb import variants_from_compdb
        t.variants = variants_from_compdb(t)     # flags re-rooted onto this revision
    return t


def _variant_at(t: Target, v):
    """The variant as recorded at revision `t` (a compilation database re-roots its flags onto that revision), or
    None when one of its sources does not exist there (a test program added or removed in the range)."""
    vv = next((x for x in t.variants if x.name == v.name), v)
    srcs = vv.sources or t.sources
    if srcs and not all((Path(t.root) / s).exists() for s in srcs):
        return None
    return vv


def _work(o) -> str:
    """What verifying a unit cost at this revision: `cached` (the compiled proof was reused: no Lean run),
    `rechecked` (Lean re-ran a cached proof script), `new:<origin>` (a new proof), or `failed`."""
    if o.status not in ("proved", "conditional", "partial"):
        return "failed" if o.attempts else o.status
    if (o.result or {}).get("status") == "cached":
        return "cached"
    origin = ((o.obligation or {}).get("proof") or {}).get("origin", "")
    return "rechecked" if origin == "cache" else f"new:{origin or '?'}"


def run_ci(adapter, target: Target, base: str, head: str, run_dir: Path, llm, *, variants=None,
           attempts: int = 3, equivalence: bool = True, check_timeout: int = 300, jobs: int = 1, log=print) -> int:
    """Exit status: 0, 1 when a unit regressed, 2 when a revision does not build (the variant's record says
    `blocked: build` with the error)."""
    from .scheduler import verify_build
    t0 = time.time()
    tb, th = materialise(target, base, run_dir), materialise(target, head, run_dir)
    report = {"base": base, "head": head, "variants": {}, "attempts": attempts,
              "sources": {"base": tb.sources, "head": th.sources}}
    regressions = 0
    blocked = 0
    # with --attempts 0 the model takes no part in verification (no proposals, no intended contracts of gap
    # units); it is used only by the old ≡ new step, to propose distinguishing inputs
    llm_verify = llm if attempts > 0 else None
    for v in target.variants:
        if variants and v.name not in variants:
            continue
        vb, vh = _variant_at(tb, v), _variant_at(th, v)
        if vh is None:
            log(f"[{v.name}] sources absent at head {head}: skipped")
            report["variants"][v.name] = {"absent_at": "head", "changed": [], "added": [], "removed": [], "units": [],
                                          "seconds_base": 0, "seconds_head": 0}
            continue
        try:
            bb = adapter.build(tb, vb, run_dir) if vb else None     # None: the program was added in the range
        except Exception as e:
            bb, err = None, ("base", base, f"{type(e).__name__}: {e}")
        else:
            err = None
        if err is None:
            try:
                bh = adapter.build(th, vh, run_dir)
            except Exception as e:
                err = ("head", head, f"{type(e).__name__}: {e}")
        if err is not None:
            blocked += 1
            log(f"[{v.name}] blocked: build ({err[0]} {err[1]}): {err[2][:300]}")
            report["variants"][v.name] = {"blocked": "build", "revision": err[0], "rev": err[1],
                                          "error": err[2][-4000:], "changed": [], "added": [], "removed": [],
                                          "units": [], "seconds_base": 0, "seconds_head": 0}
            continue
        for b in (bb, bh):              # one package per revision when module names are revision-independent
            if b is not None:
                b.pkg.ensure()
        hb = {u.name: u.body_hash for u in bb.units} if bb else {}
        hh = {u.name: u.body_hash for u in bh.units}
        changed = sorted(n for n in hh if n in hb and hh[n] != hb[n])
        added = sorted(set(hh) - set(hb))
        removed = sorted(set(hb) - set(hh))
        log(f"[{v.name}] changed {changed} added {added} removed {removed}")
        tb0 = time.time()
        ob = verify_build(adapter, bb, llm_verify, attempts=attempts, check_timeout=check_timeout, jobs=jobs,
                          log=log) if bb else {}
        t_base = time.time() - tb0
        th0 = time.time()
        oh = verify_build(adapter, bh, llm_verify, attempts=attempts, check_timeout=check_timeout, jobs=jobs, log=log)
        t_head = time.time() - th0
        # old ≡ new for every changed unit (mechanical statement, equiv-lean), with a witness when it fails
        verdicts = {}
        if equivalence and hasattr(adapter, "equivalence_verdict"):
            ub, uh = {u.name: u for u in bb.units}, {u.name: u for u in bh.units}
            for n in changed:
                if hasattr(adapter, "is_test_unit") and adapter.is_test_unit(uh[n], bh):
                    # a test changes when its own code or, e.g., the __LINE__ numbers it passes to its assertion
                    # helpers change; what CI checks for a test is its theorem at both revisions (a regression is
                    # proved at base and not at head), not old ≡ new over arbitrary memories
                    verdicts[n] = {"verdict": "test", "detail": "test unit: checked by its test theorem"}
                    continue
                try:
                    import inspect
                    kw = {"llm": llm} if "llm" in inspect.signature(adapter.equivalence_verdict).parameters else {}
                    verdicts[n] = adapter.equivalence_verdict(ub[n], uh[n], bb, bh, run_dir, **kw)
                except Exception as e:      # a verdict failure must not hide the rest of the report
                    verdicts[n] = {"verdict": "unknown", "detail": f"{type(e).__name__}: {e}"[:300]}
                why = verdicts[n].get("detail") if verdicts[n].get("verdict") == "unknown" else ""
                log(f"  equivalence {n}: {verdicts[n].get('verdict')}" + (f" ({why[:300]})" if why else ""))
        rows = []
        for n in sorted(set(ob) | set(oh)):
            sb = ob[n].status if n in ob else "-"
            sh = oh[n].status if n in oh else "-"
            cb = (ob[n].obligation or {}).get("contract", {}).get("statement") if n in ob else None
            ch = (oh[n].obligation or {}).get("contract", {}).get("statement") if n in oh else None
            regress = sb in ("proved", "conditional", "partial") and sh not in ("proved", "conditional", "partial")
            drift = sb in ("proved", "conditional", "partial") and sh in ("proved", "conditional", "partial") and cb != ch
            regressions += regress
            rows.append({"unit": n, "base": sb, "head": sh, "changed": n in changed, "regression": regress,
                         "contract_drift": drift, "head_attempts": oh[n].attempts if n in oh else 0,
                         "head_work": _work(oh[n]) if n in oh else "-", "equivalence": verdicts.get(n),
                         # kernel (Lean's kernel checked the proof) or native (compiled evaluation trusted through
                         # Lean.ofReduceBool); reported apart
                         "base_trust": getattr(ob.get(n), "trust", "") if n in ob else "",
                         "head_trust": getattr(oh.get(n), "trust", "") if n in oh else ""})
        report["variants"][v.name] = {"changed": changed, "added": added, "removed": removed, "units": rows,
                                      **({} if bb else {"absent_at": "base"}),
                                      "seconds_base": round(t_base, 1), "seconds_head": round(t_head, 1)}
    report["seconds"] = round(time.time() - t0, 1)
    report["regressions"] = regressions
    report["blocked_build"] = blocked
    out = run_dir / "ci" / f"{base}..{head}"
    write_json(out / "ci.json", report)
    md = [f"# CI {base}..{head}", ""]
    for vn, r in report["variants"].items():
        if r.get("blocked"):
            md += [f"## {vn}: blocked: build ({r['revision']} {r['rev']})", "", "```", r["error"][-3000:], "```", ""]
            continue
        absent = f" (program absent at {r['absent_at']})" if r.get("absent_at") else ""
        work = Counter(x.get("head_work", "-").split(":")[0] for x in r["units"])
        trust = Counter(x.get("head_trust") or "?" for x in r["units"] if x["head"] in ("proved", "conditional", "partial"))
        md += [f"## {vn}: changed {len(r['changed'])}, base {r['seconds_base']} s, head {r['seconds_head']} s{absent}",
               "", f"Head verification work: {work.get('cached', 0)} cached (no Lean run), {work.get('rechecked', 0)} "
               f"re-checked with a cached script, {work.get('new', 0)} new proofs, {work.get('failed', 0)} failed.",
               "", "Head proofs by trust: " + (", ".join(f"{k} {v}" for k, v in sorted(trust.items())) or "none")
               + " (kernel: checked by Lean's kernel; native: compiled evaluation, trusted through Lean.ofReduceBool).", "",
               "| unit | base | head | head work | changed | old ≡ new | regression | contract drift |",
               "|---|---|---|---|---|---|---|---|"]
        md += [f"| `{x['unit']}` | {x['base']}{' (native)' if x.get('base_trust') == 'native' else ''} | "
               f"{x['head']}{' (native)' if x.get('head_trust') == 'native' else ''} | {x.get('head_work', '')} | "
               f"{'yes' if x['changed'] else ''} | "
               f"{_eq(x.get('equivalence'))} | {'**yes**' if x['regression'] else ''} | "
               f"{'yes' if x['contract_drift'] else ''} |" for x in r["units"]]
        md.append("")
    (out / "ci.md").write_text("\n".join(md))
    # every run is also kept under history/ (another run of the same range rewrites ci.md / ci.json)
    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    (out / "history").mkdir(exist_ok=True)
    write_json(out / "history" / f"{stamp}.json", report)
    (out / "history" / f"{stamp}.md").write_text("\n".join(md))
    log(f"CI report: {out / 'ci.md'} (copy: history/{stamp}.md); regressions: {regressions}; "
        f"blocked builds: {blocked}")
    return 1 if regressions else (2 if blocked else 0)

"""Prove-or-patch: from a confirmed finding to a certified source patch.

Input: a finding (unit, variant, verdict `real_bug`, the stuck goal, ...) and the unit's intended
contract (binders, statement, and a proof script for the patched version). For each attempt:

1. the LLM proposes a minimal unified diff (guards and type widening preferred);
2. the diff is applied to a NEW version tree (runs/<t>/src/vN; the target tree is never edited);
3. the new version is built through the adapter;
4. the certificate (new_safe, conservative, changed_iff_unsafe) is rendered and checked;
5. accepted iff all three theorems check with standard axioms only; otherwise the failure goes back
   to the LLM for a revision.

Outputs: runs/<t>/patches/<id>/{patch.diff, certificate.lean, certificate.json, report.md} and one
attempt_<k>/ directory per attempt. After acceptance the patched build can be re-verified with the
scheduler (callers reuse cached proof scripts).
"""
from __future__ import annotations

import json
import re
import time
from pathlib import Path
from typing import Any

from .lean import nonstandard_axioms
from .llm import LLM, BudgetExceeded, LLMError
from .model import Finding, Patch, PatchCertificate, Target, Variant, read_json, write_json

PATCH_SCHEMA = {
    "type": "object",
    "properties": {
        "diff": {"type": "string", "description": "unified diff, paths a/<file> b/<file> relative to the target root"},
        "rationale": {"type": "string"},
        "kind": {"type": "string", "enum": ["guard", "type_widen", "general"]},
        "new_safe_tactics": {"type": "string",
                             "description": "proof of new_safe for the patched function; empty = the contract's script"},
        "conservative_tactics": {"type": "string",
                                 "description": "proof of conservative; empty = the default (loop-free functions)"},
    },
    "required": ["diff", "rationale", "kind", "new_safe_tactics", "conservative_tactics"],
    "additionalProperties": False,
}

SYSTEM = """You repair defects in C/C++ functions so that a Lean proof can certify the repair.
Answer with JSON only.

The function has inputs on which it has undefined behaviour (or violates its contract). You write a
MINIMAL source patch as a unified diff. A Lean certificate then checks three theorems:

1. new_safe: the patched function satisfies the contract on every input of its precondition;
2. conservative: on every input where the ORIGINAL function is safe, the patched function returns
   exactly the same value and leaves the caller's memory exactly the same;
3. a corollary: the behaviour changed exactly on the inputs where the original was unsafe.

So the patch may only change what happens on inputs where the original had undefined behaviour.
Rules:
* Prefer a guard before the faulty operation that handles exactly the failing inputs, or widening
  an intermediate computation to a larger type. Never change behaviour on safe inputs (no early
  returns, saturations, or rewrites that alter results the original computed correctly).
* Keep the function's signature, name and all other functions unchanged. No new includes unless
  needed; no new helper functions; no macros. Use integer literals rather than <limits.h> macros
  (write INT_MIN as (-2147483647 - 1)).
* The value returned on a previously failing input is your choice, but it must satisfy the
  contract's postcondition, which is given to you.
* The diff must apply with `patch -p1` from the target root: headers `--- a/<file>` and
  `+++ b/<file>`, correct hunk line numbers and context lines copied exactly from the source.

`new_safe_tactics` is the Lean proof of new_safe (cirlean): it starts with `cir_start` and
`cir_vcg` (symbolic execution, closes linear goals with omega), followed by tactics for what is
left. Leave it empty to use the contract's script. Leftover goals are pure facts over the
function's values. `omega` cannot reason about division by a variable: for the range of an
`int` quotient use `VerifOrch.tdiv_in_i32 a b ha hb0 hov : -2147483648 ≤ a.tdiv b ∧ a.tdiv b ≤
2147483647` (hb0 : b ≠ 0, hov : ¬ (a = -2147483648 ∧ b = -1)), e.g.
`all_goals (have := VerifOrch.tdiv_in_i32 a b (by omega) (by omega) (by omega); omega)`.
If a previous attempt failed only in new_safe while `conservative` held, the patch is probably
right: keep the diff and fix `new_safe_tactics`.
`omega` treats a product of two variables as an opaque atom: give it the facts it needs before the call,
e.g. `have hxy : 0 ≤ x * y := Int.mul_nonneg (by omega) (by omega)` and an upper bound such as
`have hle : x * y ≤ 65535 * 65535 := Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)`; put such
`have`s at the start of `new_safe_tactics` or `conservative_tactics` (after `obtain`).

`conservative_tactics` proves `EquivOn Bad ctxNew fNew ctxOld fOld` (equiv-lean). Leave it empty for
functions without loops (the default script handles straight-line and branching code). For a function
with a loop, prove ONE simulation direction (patched = target, original = source) and get Equiv from the
original's safety (shape given by the equiv-lean owner):
  intro args m hbad
  simp only [VerifOrch.Cir.Bad, not_or, Classical.not_not, WT] at hbad
  obtain ⟨⟨A, B, rfl⟩, hsafe⟩ := hbad          -- the contract's argument names
  refine EquivLean.Equiv.of_sim_of_safe ?_ (fun _ => VerifOrch.Cir.safe_of_safeRet hsafe)
  equiv_cir using (fun A count A' count' => A = A' ∧ count = count')
The coupling's binders are the loop's C variable names, the patched version's first and the original's
primed (as `cir_loop` binders). Do not run `cir_hrun` before `equiv_cir`. A guard branch that fires only
where the original has undefined behaviour needs no special treatment: on the original's safe paths its
condition is refuted.
"""


def _numbered(text: str) -> str:
    return "\n".join(f"{i + 1:5d}  {l}" for i, l in enumerate(text.splitlines()))


def user_prompt(target: Target, finding: dict, contract: dict, src_file: str, history: list[dict]) -> str:
    src = (Path(target.root) / src_file).read_text()
    parts = [f"# Defect in `{finding['unit']}` (target {target.name}, variant {finding.get('variant', 'default')})",
             f"Summary: {finding.get('summary', '')}",
             f"## Source file `{src_file}` (line numbers added for reference; they are not part of the file)",
             f"```c\n{_numbered(src)}\n```",
             "## The unit's contract (Lean, cirlean vocabulary): binders and conclusion",
             f"```lean\n{contract['binders']}\n{contract['statement']}\n```"]
    if finding.get("goals"):
        parts.append("## Proof obligation the original version could not discharge")
        parts.append("```\n" + finding["goals"][0][:4000] + "\n```")
    if finding.get("counterexample"):
        parts.append("## Failing input\n```json\n" + json.dumps(finding["counterexample"], indent=1) + "\n```")
    for k, h in enumerate(history, start=1):
        parts.append(f"## Attempt {k} was rejected: {h['reason']}")
        parts.append("```diff\n" + h["diff"][:3000] + "\n```")
        if h.get("tactics"):
            parts.append("new_safe tactics used:\n```lean\n" + h["tactics"][:1500] + "\n```")
        if h.get("detail"):
            parts.append("Details:\n```\n" + h["detail"][:4000] + "\n```")
    parts.append("Give the JSON object: diff, rationale, kind, new_safe_tactics.")
    return "\n\n".join(parts)


def _next_version(run_dir: Path) -> str:
    """Reserve a fresh version label atomically (concurrent patch runs on one target must not collide)."""
    (run_dir / "src").mkdir(parents=True, exist_ok=True)
    n = 1
    while True:
        try:
            (run_dir / "src" / f".reserved_v{n}").mkdir()
        except FileExistsError:
            n += 1
            continue
        if (run_dir / "src" / f"v{n}").exists():
            n += 1
            continue
        return f"v{n}"


def run_patch_loop(adapter, target: Target, variant: Variant, finding: dict, contract: dict, llm: LLM | None,
                   run_dir: Path, *, src_file: str | None = None, revisions: int = 1,
                   proposals: list[dict] | None = None, reverify: bool = False, log=print) -> dict[str, Any]:
    """Run the loop for one finding. `proposals` (list of {diff, rationale, kind}) are tried first
    (tests, replays, human patches); later attempts ask the LLM, with the rejections as feedback.
    Returns the result record (also written to the patch directory)."""
    from .adapters.cir import patch as cp
    pid = f"{finding['unit']}_{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}"
    pdir = run_dir / "patches" / pid
    pdir.mkdir(parents=True, exist_ok=True)
    src_file = src_file or (variant.sources or target.sources)[0]
    b0 = adapter.build(target, variant, run_dir)
    pkg = cp.cert_package(run_dir)
    pkg.ensure()
    cp.ensure_equivlean()
    g0 = b0.info["gen_module"]
    r0 = pkg.check(g0, b0.pkg.src(g0).read_text(), mem_gib=64)      # Gen source lives in the build package
    if not r0.ok:
        raise RuntimeError(f"{g0} does not check: {r0.errors[:2]}")
    keys = {g0: r0.cache_key, **cp.ensure_verifOrch(pkg)}
    history: list[dict] = []
    result: dict[str, Any] = {"id": pid, "unit": finding["unit"], "variant": variant.name, "accepted": False,
                              "attempts": [], "finding": finding, "contract": contract}
    n_attempts = 1 + revisions
    for k in range(n_attempts):
        adir = pdir / f"attempt_{k + 1}"
        adir.mkdir(exist_ok=True)
        if proposals is not None and k < len(proposals):
            prop = proposals[k]
        else:
            if llm is None:
                break
            try:
                prop = llm.ask_json(f"patch:{finding['unit']}:{k}", SYSTEM,
                                    user_prompt(target, finding, contract, src_file, history), PATCH_SCHEMA,
                                    effort="high")
            except (BudgetExceeded, LLMError) as e:
                result["attempts"].append({"status": "llm_error", "detail": str(e)})
                break
        patch = Patch(unit=finding["unit"], diff=prop["diff"], rationale=prop.get("rationale", ""),
                      kind=prop.get("kind", "general"))
        (adir / "patch.diff").write_text(patch.diff)
        rec: dict[str, Any] = {"attempt": k + 1, "kind": patch.kind, "rationale": patch.rationale}
        version = _next_version(run_dir)
        try:
            t1 = cp.apply_patch(target, patch, run_dir, version)
        except ValueError as e:
            rec.update(status="does_not_apply", detail=str(e))
            history.append({"reason": "the diff does not apply", "diff": patch.diff, "detail": str(e)})
            result["attempts"].append(rec)
            log(f"  attempt {k + 1}: diff does not apply")
            continue
        try:
            b1 = adapter.build(t1, variant, run_dir)
        except RuntimeError as e:
            rec.update(status="build_failed", version=version, detail=str(e)[-3000:])
            history.append({"reason": "the patched source does not compile/translate", "diff": patch.diff,
                            "detail": str(e)[-3000:]})
            result["attempts"].append(rec)
            log(f"  attempt {k + 1}: build failed")
            continue
        g1 = b1.info["gen_module"]
        r1 = pkg.check(g1, b1.pkg.src(g1).read_text(), mem_gib=64)
        ikeys = {**keys, g1: r1.cache_key}
        cert_id = f"{pid}_{k + 1}"
        tactics = (prop.get("new_safe_tactics") or "").strip() or contract.get("tactics", "cir_start\ncir_vcg")
        rec["new_safe_tactics"] = tactics
        text = cp.render_certificate(cert_id, contract["binders"], contract["statement"], tactics, g0, g1,
                                     prop.get("conservative_tactics") or contract.get("conservative_tactics"))
        (adir / "certificate.lean").write_text(text)
        res, st = cp.check_certificate(pkg, cert_id, text, ikeys)
        bad_ax = nonstandard_axioms(res.axioms)
        accepted = res.ok and all(v == "proved" for v in st.values()) and not bad_ax
        rec.update(status="accepted" if accepted else "rejected", version=version, theorems=st,
                   seconds=res.seconds, axioms=res.axioms, errors=res.errors[:3])
        write_json(adir / "result.json", rec)
        result["attempts"].append(rec)
        log(f"  attempt {k + 1} ({version}): {rec['status']} {st} in {res.seconds:.1f}s")
        if accepted:
            cert = PatchCertificate(unit=finding["unit"], new_safe=f"VOCert.{cert_id}.new_safe", new_safe_status="proved",
                                    conservative=f"VOCert.{cert_id}.conservative", conservative_status="proved",
                                    changed_set=f"exactly the calls of the contract on which the original "
                                                f"`{finding['unit']}` is unsafe (VOCert.{cert_id}.changed_iff_unsafe)",
                                    corollary="VerifOrch.Cir.changed_iff_unsafe_at",
                                    notes=f"axioms: {', '.join(res.axioms)}; check {res.seconds:.1f}s")
            (pdir / "patch.diff").write_text(patch.diff)
            (pdir / "certificate.lean").write_text(text)
            write_json(pdir / "certificate.json", cert)
            result.update(accepted=True, version=version, certificate=cert.to_json())
            if reverify:
                result["reverify"] = _reverify(adapter, b1, llm, finding["unit"], log)
            break
        # failure detail for the revision: which theorem failed and Lean's first errors
        failed = [t for t, v in st.items() if v != "proved"]
        witness = None
        if "conservative" in failed:
            witness = _witness(cp, pkg, contract, g0, g1, ikeys)
            if witness:
                rec["witness"] = witness
                write_json(adir / "result.json", rec)
                log(f"    witness: {witness}")
        if "conservative" in failed and "new_safe" not in failed:
            reason = "it changes behaviour on inputs where the original is safe (conservative failed)"
            if witness and witness.get("args"):
                reason += (f"; e.g. on arguments {witness['args']} the original gives {witness['original']}"
                           f" but the patched version gives {witness['patched']}")
        elif failed == ["new_safe"]:
            reason = ("only the proof of new_safe failed (conservative holds, so the patch is probably right): "
                      "keep the diff and give new_safe_tactics that close the goals below")
        else:
            reason = f"theorem(s) {', '.join(failed)} failed"
        history.append({"reason": reason, "diff": patch.diff, "tactics": tactics,
                        "detail": "\n".join(res.errors[:2] + [g[:2500] for g in res.goals[:2]])})
    write_json(pdir / "result.json", result)
    (pdir / "report.md").write_text(report_md(result))
    return result


def _witness(cp, pkg, contract: dict, g0: str, g1: str, ikeys: dict) -> dict | None:
    """Disagreement witness for all-int signatures (evidence that a rejected patch changes safe behaviour)."""
    try:
        decl, args, _ = cp.split_call(contract["statement"])
    except ValueError:
        return None
    elems = [e.strip() for e in args.strip()[1:-1].split(",") if e.strip()]
    if not elems or not all(re.fullmatch(r"\.int\s+\w+", e) for e in elems):
        return None
    try:
        return cp.disagreement_witness(pkg, g0, g1, decl, len(elems), ikeys)
    except Exception as e:
        return {"error": str(e)[:300]}


def _reverify(adapter, build, llm, unit: str, log) -> dict[str, str]:
    """Re-verify the patched unit and its (transitive) callers in the new build."""
    from .graph import reachable
    from .scheduler import verify_build
    callers = {u.name for u in build.units if unit in reachable(build.units, [u.name])}
    try:
        oc = verify_build(adapter, build, llm, only=callers | {unit}, log=log)
        return {n: o.status for n, o in oc.items()}
    except Exception as e:  # report, do not fail the accepted certificate
        return {"error": str(e)[:500]}


def report_md(result: dict[str, Any]) -> str:
    lines = [f"# Patch {result['id']}", "",
             f"Unit `{result['unit']}`, variant `{result['variant']}`: "
             + ("**accepted**" if result["accepted"] else "**no certified patch**"), ""]
    if result.get("certificate"):
        c = result["certificate"]
        lines += ["Certificate (all checked by Lean's kernel):", "",
                  f"* `{c['new_safe']}`: the patched function meets the contract on every input of its precondition;",
                  f"* `{c['conservative']}`: wherever the original is safe (on well-typed calls), both versions have the same caller-visible outcome (equiv-lean `EquivOn`);",
                  f"* changed set: {c['changed_set']}.", "", f"{c['notes']}", ""]
    lines.append("## Attempts")
    for a in result["attempts"]:
        lines.append(f"* attempt {a.get('attempt', '?')}: {a.get('status')}"
                     + (f", theorems {a['theorems']}" if a.get("theorems") else "")
                     + (f" ({a['kind']}: {a['rationale']})" if a.get("rationale") else ""))
        if a.get("witness", {}).get("args"):
            w = a["witness"]
            lines.append(f"  * witness: on {w['args']} the original gives `{w['original']}`, the patch `{w['patched']}`")
    if result.get("reverify"):
        lines += ["", "## Re-verification of the patched build", "",
                  *[f"* `{n}`: {s}" for n, s in result["reverify"].items()]]
    return "\n".join(lines) + "\n"


def load_finding(path: Path) -> dict:
    """A finding JSON (model.Finding fields) plus the unit's intended `contract` under that key."""
    d = read_json(path)
    out = Finding.from_json(d).to_json() if "verdict" in d else dict(d)
    if "contract" in d:
        out["contract"] = d["contract"]
    return out

"""Rust adapter over Charon + Aeneas: statements, proof templates, prompts, and CI old ≡ new through equiv-lean.

Statements are Aeneas Hoare triples `f x ⦃ r => post ⦄` (`spec (f x) post`: `f x` returns `ok r` with `post r`; a
panic is `fail`, divergence `div`). Every proved contract is tagged `@[step]`, so in a caller's proof Aeneas's
`step` tactic replaces each call by the callee's contract (one line per call, the callee body is never unfolded).

* Mechanical no-panic statement of a function (`no_panic`): `f x ⦃ _ => True ⦄` over every input of its type, i.e.
  `∃ v, f x = ok v` (`VerifOrch.Rust.spec_true_iff`). It is the first candidate of every function; the model may
  propose a contract with a precondition when it does not hold.
* Mechanical statement of a test (`mechanical_contract`): `t ⦃ _ => True ⦄`, i.e. `t = ok ()`: the test runs to
  the end, no panic, every assertion holds; `∃ e, t = fail e` for a `#[should_panic]` test.
"""
from __future__ import annotations

import json
import re
import threading
from pathlib import Path

from ...model import Contract, Obligation, Target, Unit, Variant
from ..base import Adapter, Build
from . import build as rbuild
from . import evalrun

HERE = Path(__file__).parent
SUPPORT = rbuild.SUPPORT_LEAN
SUPPORT_MODULE = rbuild.SUPPORT_MODULE        # imported by every function module (build.py)
_SUPPORT_LOCK = threading.Lock()
_LOOP_RE = re.compile(r"_loop\d*(\.body)?$")


class RustAdapter(Adapter):
    lang = "rust"
    pin = rbuild.PIN

    def build(self, target: Target, variant: Variant, run_dir: Path) -> Build:
        return rbuild.build(target, variant, run_dir)

    def module(self, build: Build, unit: Unit) -> str:
        return f"{build.ns}.{_ident(unit.name)}"

    def theorem(self, unit: Unit) -> str:
        return f"{_ident(unit.name)}_spec"

    def attrs(self, unit: Unit) -> str:
        # a proved contract is a `step` lemma: callers' `step` uses it at every call
        return "" if unit.kind == "test" else "@[step]"

    def schema(self) -> dict:
        return PROPOSAL_SCHEMA

    def modular_options(self) -> list[str]:
        return []

    def unit_gen_module(self, unit: Unit, build: Build) -> str:
        """The unit's own function module (it imports its callees' modules): an obligation's Lean inputs change only
        when the unit or one of its callees changes."""
        return build.info.get("unit_module", {}).get(unit.name, build.info["gen_module"])

    def support_modules(self, build: Build) -> dict[str, str]:
        with _SUPPORT_LOCK:
            res = build.pkg.check(SUPPORT_MODULE, SUPPORT.read_text(), timeout=900)
        if not res.ok:
            raise RuntimeError(f"{SUPPORT_MODULE} does not check: {res.errors[:3]}")
        return {SUPPORT_MODULE: res.cache_key}

    def render(self, ob: Obligation, build: Build) -> str:
        base = ["Aeneas", build.info.get("unit_module", {}).get(ob.unit, build.info["gen_module"])]
        imports = base + [i for i in ob.imports if i not in base]
        c = ob.contract
        lines = [f"import {i}" for i in imports]
        lines += ["", "open Aeneas Aeneas.Std Result ControlFlow Error", "", "set_option maxHeartbeats 4000000", "",
                  f"namespace {build.ns}", ""]
        lines += [o.strip() for o in ob.proof.options if o.strip()]
        if c.attrs:
            lines.append(c.attrs)
        lines.append(f"theorem {ob.theorem} {c.binders.strip()} :".replace("  ", " "))
        lines.append(f"    {c.statement.strip()} := by")
        for t in ob.proof.tactics.strip("\n").splitlines():
            lines.append("  " + t if t.strip() else "")
        lines += ["", f"#print axioms {ob.theorem}", "", f"end {build.ns}", ""]
        return "\n".join(lines)

    # -- statements ------------------------------------------------------------------------------------------------
    def call(self, unit: Unit) -> tuple[str, str]:
        """(binders, application): the function applied to all its explicit arguments, every binder of its
        definition (type and trait parameters of a generic function too) as theorem binders."""
        sig = unit.signature or {}
        bs = sig.get("binders") or []
        args = [n for b in bs if b["explicit"] for n in b["names"]]
        return " ".join(b["text"] for b in bs), sig.get("lean", unit.lean_decl) + "".join(" " + a for a in args)

    def no_panic(self, unit: Unit) -> tuple[str, str]:
        binders, app = self.call(unit)
        return binders, f"{app} ⦃ _ => True ⦄"

    def is_test_unit(self, unit: Unit, build: Build) -> bool:
        return unit.kind == "test"

    def mechanical_contract(self, unit: Unit, build: Build) -> "Contract | None":
        if not self.is_test_unit(unit, build) or not unit.in_scope:
            return None
        sig = unit.signature or {}
        if any(b["explicit"] for b in sig.get("binders") or []):
            return None
        lean = sig.get("lean", unit.lean_decl)
        st = f"∃ e, {lean} = fail e" if sig.get("should_panic") else f"{lean} ⦃ _ => True ⦄"
        what = "panics (#[should_panic])" if sig.get("should_panic") else "runs without panic, every assertion holds"
        return Contract(unit=unit.name, binders="", statement=st, origin="mechanical", strength="noub", attrs="",
                        note=f"test, stated mechanically: {what} ({unit.loc})")

    # -- proof templates (tried before the model) -------------------------------------------------------------------
    def _closure(self, unit: Unit, build: Build) -> list[Unit]:
        by = {u.name: u for u in build.units}
        seen, todo = [], [unit.name]
        while todo:
            n = todo.pop()
            if n in [u.name for u in seen] or n not in by:
                continue
            seen.append(by[n])
            todo += by[n].callees
        return seen

    def template_candidates(self, unit: Unit, build: Build) -> list[dict]:
        if self.is_test_unit(unit, build):
            return self.test_template(unit, build)
        sig = unit.signature or {}
        defs = sig.get("defs") or [unit.lean_decl]
        binders, st = self.no_panic(unit)
        base = {"binders": binders, "statement": st, "options": [], "strength": "noub", "needs": [],
                "statement_origin": "mechanical"}
        if any(_LOOP_RE.search(d) for d in defs):
            return []                   # a loop needs an invariant and a measure (the model's)
        # the body only: calls go through the callees' `@[step]` contracts
        f = sig.get("lean", unit.lean_decl)
        return [dict(base, tactics=f"unfold {f}\nvo_bounds\nstep*", notes="template: no panic on any input (step*)"),
                dict(base, tactics=f"unfold {f}\nvo_bounds\nstep*\nall_goals (try simp_all) <;> scalar_tac +nonLin",
                     notes="template: no panic on any input (step*, scalar_tac)")]

    def test_template(self, unit: Unit, build: Build) -> list[dict]:
        """A test is run, not summarised: the test and every function it reaches are unfolded and executed
        symbolically by `step*` (kernel-checked; loop-free code), or the whole test is evaluated by compiled code
        (`native_decide`, reported with trust `native`), unless it reaches a function Aeneas does not model (whose
        compiled stand-in is not the real function)."""
        sig = unit.signature or {}
        clo = self._closure(unit, build)
        defs = [d for u in clo for d in (u.signature or {}).get("defs") or []]
        loops = any(_LOOP_RE.search(d) for d in defs)
        out = []
        if sig.get("should_panic"):
            if all(u.in_scope for u in clo):
                out.append({"binders": "", "statement": "", "tactics": "exact VerifOrch.Rust.fail_of_panics (by native_decide)",
                            "options": [], "strength": "noub", "needs": [], "native": True,
                            "notes": "template: compiled evaluation of the test (native_decide)"})
            return out
        if not loops:
            out.append({"binders": "", "statement": "", "tactics": f"simp only [{', '.join(defs)}]\nvo_bounds\nstep*",
                        "options": [], "strength": "noub", "needs": [],
                        "notes": "template: symbolic execution of the test and everything it calls (step*)"})
        if all(u.in_scope for u in clo):
            # kernel, with loops: equiv-lean's wp symbolic execution (`aeneas_wp`), each loop unrolled one iteration
            # at a time on the concrete state (`rw [loop]`); a small heartbeat budget, as it fails slowly
            bodies = [d for d in defs if d.endswith(".body")]
            outer = [d for d in defs if not d.endswith(".body")]
            out.append({"binders": "", "statement": "", "tactics": "\n".join([
                "rw [EquivLean.Aeneas.spec_iff_wp]", "vo_bounds", f"simp only [{', '.join(outer)}]",
                f"aeneas_wp [{', '.join(bodies)}]" if bodies else "aeneas_wp",
                f"repeat (rw [loop]; aeneas_wp [{', '.join(bodies)}])" if bodies else "skip",
                "all_goals (try simp_all)"]),
                        "options": ["set_option maxHeartbeats 800000 in"], "strength": "noub", "needs": [],
                        "extra_imports": ["EquivLean.Bridge.Aeneas.Tactic"],
                        "notes": "template: wp symbolic execution of the test with loop unrolling (aeneas_wp)"})
            out.append({"binders": "", "statement": "", "tactics": "exact VerifOrch.Rust.spec_of_reducesTo (e := ()) (by native_decide)",
                        "options": [], "strength": "noub", "needs": [], "native": True,
                        "notes": "template: compiled evaluation of the test (native_decide)"})
        return out

    # -- prompt material ------------------------------------------------------------------------------------------
    def gen_text(self, build: Build, unit: Unit, max_chars: int = 12000) -> str:
        """The Aeneas definitions of the unit (its function module without the header)."""
        m = build.info.get("unit_module", {}).get(unit.name)
        if not m or not build.pkg.src(m).exists():
            return ""
        text = build.pkg.src(m).read_text()
        i = text.find("\nnamespace ")
        out = text[i + 1:] if i >= 0 else text
        return out if len(out) <= max_chars else out[: max_chars // 2] + "\n... [truncated] ...\n" + out[-max_chars // 2:]

    def type_defs(self, build: Build, max_chars: int = 6000) -> str:
        m = build.info.get("types_module")
        if not m or not build.pkg.src(m).exists():
            return ""
        text = build.pkg.src(m).read_text()
        i = text.find("\nnamespace ")
        out = text[i + 1:] if i >= 0 else ""
        return out[:max_chars]

    def intended_prompt(self, unit: Unit, build: Build) -> str:
        return "\n\n".join([
            f"# Function `{unit.name}` (kind: {unit.kind}) cannot be verified: {unit.scope}.",
            "State the contract it is intended to satisfy, so that its callers can be verified assuming it. It will be "
            "used only as an explicit hypothesis of the callers' theorems and reported as an unverified assumption. "
            "Use the vocabulary of proved contracts: an Aeneas Hoare triple `f x ⦃ r => post ⦄` over the function's "
            "Lean name, with binders for its arguments and the preconditions it needs. If the function has no Lean "
            "definition, describe the contract in `notes` and give binders/statement as the empty string.",
            "## Rust source", f"```rust\n{unit.source or '(not found)'}\n```",
            "Give the JSON object: binders, statement, notes."])

    def user_prompt(self, unit: Unit, build: Build, callees, history, hypotheses=()) -> str:
        from ...scheduler import truncate
        sig = unit.signature or {}
        binders, st = self.no_panic(unit)
        parts = [f"# Function under verification: `{unit.name}` (kind: {unit.kind}; theorem name `{self.theorem(unit)}`)",
                 f"Rust path `{sig.get('rust')}`; Lean definition `{sig.get('lean')}` (with its loops: "
                 f"{', '.join('`' + d + '`' for d in sig.get('defs', []))}); return type `{sig.get('ret')}`.",
                 f"Target `{build.target.name}`.",
                 "## Rust source", f"```rust\n{unit.source or '(not found)'}\n```",
                 "## Aeneas translation (the definitions your theorem is about)", f"```lean\n{self.gen_text(build, unit)}\n```"]
        td = self.type_defs(build)
        if td.strip():
            parts += ["## Type definitions of the crate", f"```lean\n{td}\n```"]
        if not self.is_test_unit(unit, build):
            parts += ["## The mechanical statement (no panic on any input); prove it if it holds",
                      f"```lean\ntheorem {self.theorem(unit)} {binders} :\n    {st}\n```",
                      "If it does not hold (some input panics: overflow, division by zero, index out of bounds, a failed "
                      "assertion), state the contract with the weakest precondition under which the function returns "
                      "`ok`, and a postcondition describing the result, and give in `notes` an input that panics."]
        if callees:
            parts.append("## Contracts of its callees (proved, imported, tagged @[step]: `step` applies them at calls)")
            for ob, _ in callees:
                parts.append(f"```lean\ntheorem {ob.theorem} {ob.contract.binders} :\n    {ob.contract.statement}\n```")
        elif not hypotheses:
            parts.append("The function calls no other function of the crate.")
        if hypotheses:
            parts.append("## Assumed contracts (unverified callees), in scope as hypotheses of your theorem")
            parts.append("The orchestrator puts these binders in front of your binders. Do not repeat them. Use them "
                         "with `step with <name>` or by `have` + `WP.spec_bind`.")
            for uname, hname, c in hypotheses:
                parts.append(f"```lean\n({hname} : ∀ {c.binders}, {c.statement})\n```")
        if history:
            parts.append("## Previous attempts and Lean's verdicts (fix the problems; do not repeat a failing script)")
            for k, (ob, res, prop) in enumerate(history[-3:], start=max(1, len(history) - 2)):
                fb = ["error: " + truncate(e, 2500) for e in res.errors[:3]]
                fb += ["unsolved goal:\n" + truncate(g, 5000) for g in res.goals[:2]]
                parts.append(f"### Attempt {k}: {res.status}\n```json\n" + json.dumps(
                    {kk: prop.get(kk) for kk in ("binders", "statement", "tactics", "options", "needs")}, indent=1)
                    + "\n```\n" + "\n".join(fb))
        parts.append("Give the JSON object: binders, statement, tactics, options, strength, needs, notes.")
        return "\n\n".join(parts)

    def prompt_pack(self) -> str:
        return (HERE / "prompt_pack.md").read_text()

    # -- counterexamples (compiled evaluation of the translation) -----------------------------------------------------
    def refute(self, unit: Unit, build: Build) -> dict | None:
        """The mechanical no-panic statement against compiled evaluation on generated inputs (boundaries and small
        values of the argument types). A panicking input refutes it; the refutation is checked as a theorem
        `¬ ∀ args, f args ⦃ _ => True ⦄` (by `native_decide` on the evaluation, trust `native`). Not for tests,
        generic functions, or functions reaching an opaque stand-in for an unmodelled library function."""
        sig = unit.signature or {}
        if self.is_test_unit(unit, build) or not unit.in_scope or not sig.get("binders") \
                or any(not b["explicit"] for b in sig["binders"]) \
                or any(not u.in_scope for u in self._closure(unit, build)):
            return None
        params = [(n, b["type"]) for b in sig["binders"] for n in b["names"]]
        grid, err = evalrun.input_grid(params, unit.name)
        if err or not grid:
            return None
        um = self.unit_gen_module(unit, build)
        exprs = [(k, f"VOEval.outcome ({sig['lean']}{a})") for k, (a, _) in enumerate(grid)]
        res, timeouts, err = evalrun.evaluate(build.pkg, [um], exprs, f"VOCex.{_ident(build.variant.name)}.{_ident(unit.name)}",
                                              build.dir / "findings" / f"eval_{_ident(unit.name)}.txt")
        bad = [k for k in sorted(res) if res[k].startswith("panic")]
        binders, st = self.no_panic(unit)
        out = {"refuted": bool(bad), "statement": st, "inputs": len(res), "timeouts": timeouts,
               "panicking_inputs": len(bad)}
        if err:
            out["error"] = err
        if not bad:
            return out
        k = bad[0]
        a, shown = grid[k]
        thm = f"{_ident(unit.name)}_no_panic_refuted"
        mod = f"VOCex.{_ident(build.variant.name)}.{_ident(unit.name)}_refuted"
        src = "\n".join([f"import {um}", "", "open Aeneas Aeneas.Std Result ControlFlow Error", "",
                         f"namespace {build.ns}", "",
                         f"/-- `{unit.name}` panics on {json.dumps(shown)} ({res[k]}). -/",
                         f"theorem {thm} : ¬ (∀ {binders}, {st}) := by", "  intro h",
                         f"  obtain ⟨e, he⟩ := VerifOrch.Rust.fail_of_panics (m := {sig['lean']}{a}) (by native_decide)",
                         f"  have h0 := h{a}", "  rw [he] at h0", "  simp at h0", "", f"#print axioms {thm}", "",
                         f"end {build.ns}", ""])
        r = build.pkg.check(mod, src, {um: build.gen_modules[um]}, timeout=600)
        out.update({"input": shown, "outcome": res[k], "theorem": f"{build.ns}.{thm}", "module": mod,
                    "status": r.status, "trust": "native" if r.ok else "", "examples": [
                        {"input": grid[j][1], "outcome": res[j]} for j in bad[:5]]})
        return out

    def candidate_instructions(self, unit: Unit, build: Build) -> str:
        sig = unit.signature or {}
        ps = ", ".join(f"`{n}`: {b['type']}" for b in sig.get("binders", []) if b["explicit"] for n in b["names"])
        return ("Each candidate is a JSON object {\"args\": {<parameter>: <value>}, \"convention\": bool, \"why\": str}: "
                f"parameters {ps}. Integers are JSON numbers in the type's range; slices and vectors are JSON arrays. "
                "The function panics (the analogue of undefined behaviour here) on overflow, division by zero, an "
                "index out of bounds or a failed assertion.")

    def run_semantic(self, unit: Unit, build: Build, args) -> "ReplayResult":
        """One input on the translation by compiled evaluation (`vo cex`): ok, ub (a panic), timeout or error."""
        from ...model import ReplayResult
        sig = unit.signature or {}
        params = [(n, b["type"]) for b in sig.get("binders", []) if b["explicit"] for n in b["names"]]
        lits = [evalrun.literal(t, (args or {}).get(n)) for n, t in params] if isinstance(args, dict) else [None]
        if any(l is None for l in lits) or not unit.in_scope:
            return ReplayResult(mode="semantic", outcome="error", detail=f"arguments not representable: {args}")
        um = self.unit_gen_module(unit, build)
        res, timeouts, err = evalrun.evaluate(build.pkg, [um], [(0, f"VOEval.outcome ({sig['lean']}{''.join(' ' + l for l in lits)})")],
                                              f"VOCex.{_ident(build.variant.name)}.{_ident(unit.name)}_run",
                                              build.dir / "findings" / f"run_{_ident(unit.name)}.txt")
        if timeouts:
            return ReplayResult(mode="semantic", outcome="timeout", detail="evaluation time limit")
        if 0 not in res:
            return ReplayResult(mode="semantic", outcome="error", detail=err or "no result")
        r = res[0]
        return ReplayResult(mode="semantic", outcome="ub" if r.startswith("panic") else "ok", detail=r,
                            confirmed=r.startswith("panic"))

    # -- CI: old ≡ new through equiv-lean's Aeneas bridge ------------------------------------------------------------
    def equivalence_verdict(self, unit_old: Unit, unit_new: Unit, b_old: Build, b_new: Build, run_dir: Path,
                            llm=None) -> dict:
        from .equiv import verdict
        return verdict(self, unit_old, unit_new, b_old, b_new, run_dir, llm=llm)


PROPOSAL_SCHEMA = {
    "type": "object",
    "properties": {
        "binders": {"type": "string", "description": "Lean binders: the arguments and the preconditions"},
        "statement": {"type": "string", "description": "An Aeneas Hoare triple, e.g. crate.f x ⦃ r => r.val = x.val + 1 ⦄"},
        "tactics": {"type": "string", "description": "Proof script, one tactic per line, without `by`"},
        "options": {"type": "array", "items": {"type": "string"}},
        "strength": {"type": "string", "enum": ["noub", "functional"]},
        "needs": {"type": "array", "items": {"type": "string"}},
        "notes": {"type": "string"},
    },
    "required": ["binders", "statement", "tactics", "options", "strength", "needs", "notes"],
    "additionalProperties": False,
}


def _ident(s: str) -> str:
    out = "".join(c if c.isalnum() or c == "_" else "_" for c in s)
    return out if out[:1].isalpha() else "u" + out

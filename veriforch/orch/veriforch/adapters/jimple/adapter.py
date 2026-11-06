"""Java adapter over JimpleLean: one `MethodVC` obligation per method, callee contracts through the
contract environment Γ (contracts only, inlining depth 0), proved by `jverify`.

Contract convention (what the scheduler's generic Contract fields hold for Java):
* `binders`: `(fuel : Nat) (hfuel : fuel = N)`, the exploration budget of the symbolic execution;
* `statement`: `MethodVC P (Contracts.env [...]) 0 (vo_mref P "C" "m" [params]) (Spec.of ...) (invariants) fuel`,
  self-contained: every spec is written inline, so an unproved callee's contract can be passed to callers
  as an explicit hypothesis by the scheduler (assume-guarantee) and copied into their Γ.
A method's own contract is in its Γ when it calls itself (partial correctness makes that sound).
"""
from __future__ import annotations

import json
import re
from pathlib import Path

from ...model import Obligation, Target, Unit, Variant
from ..base import Adapter, Build
from . import build as jbuild

HERE = Path(__file__).parent
EXAMPLES = ["Examples/Basics.lean", "Examples/Exceptions.lean"]

PROPOSAL_SCHEMA = {
    "type": "object",
    "properties": {
        "binders": {"type": "string", "description": "(fuel : Nat) (hfuel : fuel = N)"},
        "statement": {"type": "string", "description": "MethodVC P (Contracts.env [...]) 0 (vo_mref ...) (Spec.of ...) inv fuel"},
        "tactics": {"type": "string", "description": "Proof script without `by`, e.g. subst hfuel\\njverify"},
        "options": {"type": "array", "items": {"type": "string"}},
        "strength": {"type": "string", "enum": ["noub", "functional"]},
        "needs": {"type": "array", "items": {"type": "string"}},
        "notes": {"type": "string"},
    },
    "required": ["binders", "statement", "tactics", "options", "strength", "needs", "notes"],
    "additionalProperties": False,
}


class JimpleAdapter(Adapter):
    lang = "jimple"
    pin = jbuild.JIMPLE_PIN
    cache_scope = "variant"          # proofs mention the whole program term, so they do not carry across variants
    callee_contracts_in_statement = True   # Γ (callee contracts) is part of MethodVC: conditional until linked

    def build(self, target: Target, variant: Variant, run_dir: Path) -> Build:
        return jbuild.build(target, variant, run_dir)

    def module(self, build: Build, unit: Unit) -> str:
        n = _ident(unit.name)
        if len(n.encode()) > 200:               # file names (.lean/.olean/.ilean) must stay under 255 bytes
            n = jbuild._component(n, 150)
        return f"{build.ns}.{n}"

    def theorem(self, unit: Unit) -> str:
        return f"{_ident(unit.name)}_vc"

    def attrs(self, unit: Unit) -> str:
        return ""

    def schema(self) -> dict:
        return PROPOSAL_SCHEMA

    def template_candidates(self, unit: Unit, build: Build) -> list[dict]:
        """A free, annotation-free proof attempt: JimpleLean's generic contract (typed arguments in a typed
        state; returns normally or throws only declared exceptions; never leaves the model), proved by
        `jverify_generic`. Offered only for methods without application callees, so the contract
        environment holds nothing but the method's own generic contract (for a self-recursive method),
        which partial correctness makes sound; callers get contracts through the LLM path. JUnit test methods get
        the test templates instead (their statement is fixed by `mechanical_contract`)."""
        if self.is_test_unit(unit, build):
            return self._test_templates(unit, build)
        if self.modular_module(unit, build) is not None:
            return []          # genericSpec names the program, a modular theorem holds for every program
        if unit.callees or _has_loop((unit.signature or {}).get("listing", "")):
            return []          # a loop needs an invariant: without one the generic proof can only unroll
        mref = self._mref(unit, build)
        P = build.info["prog"]
        own = f"(genericSpec {P} ({mref}))"
        gamma = (f"(Contracts.env [(({mref}).sig, {own})])" if (unit.signature or {}).get("recursive")
                 else "(Contracts.env [])")
        return [{"binders": "(fuel : Nat) (hfuel : fuel = 60)",
                 "statement": f"MethodVC {P} {gamma} 0 ({mref}) {own} [] fuel",
                 "tactics": "subst hfuel\njverify_generic", "options": [], "strength": "noub", "needs": [],
                 "notes": "generic no-unexpected-exception contract (template)"}]

    # inlining depth and exploration budget of the test template (a concrete run: every call is unfolded)
    TEST_DEPTH, TEST_FUEL = 8, 400

    def is_test_unit(self, unit: Unit, build: Build) -> bool:
        """A method annotated `@Test` (JUnit 5 or 4) in one of the target's test sources, found by scanning the
        sources of the build (build.info["junit_tests"]: `cls.method/arity`)."""
        sig = unit.signature or {}
        key = f"{sig.get('cls')}.{sig.get('name')}/{len(sig.get('params', []))}"
        return key in set(build.info.get("junit_tests", []))

    def mechanical_contract(self, unit: Unit, build: Build) -> "Contract | None":
        """The theorem of a JUnit test method, stated mechanically (no model): `Sat P m (genericSpec P m [])`.
        JimpleLean's `Sat` is partial correctness over every execution of the method; `genericSpec` with no allowed
        exception says: started in a typed state after class initialization with a typed receiver, the test returns
        normally, i.e. every JUnit assertion holds (a failure throws AssertionFailedError/AssertionError) and no
        other exception escapes, and it never leaves the model (`wrong`). The statement names no callee contract:
        the proof goes through `MethodVC.sat_of_allVC` with an empty contract environment, so every call is
        unfolded (the code under test is executed), and the theorem does not depend on any model-written
        contract. @Test methods with parameters are quantified over all typed arguments."""
        from ...model import Contract
        if not self.is_test_unit(unit, build):
            return None
        P, mref = build.info["prog"], self._mref(unit, build)
        return Contract(unit=unit.name, binders="",
                        statement=f"Sat {P} ({mref}) (genericSpec {P} ({mref}) [])",
                        origin="mechanical", strength="noub", attrs="",
                        note="JUnit test method, stated mechanically. Over-approximations (the theorem is stronger "
                             "than the JUnit run needs): the receiver is any test-class instance with typed fields "
                             "(JUnit's fresh instance and @BeforeEach are not modelled), states after class "
                             "initialization; partial correctness (a terminating run passes). No dependency on "
                             "callee contracts (empty Γ; the Contracts.valid link is not needed).")

    def _test_templates(self, unit: Unit, build: Build) -> list[dict]:
        """Two free proof attempts for a test theorem, both through `MethodVC.sat_of_allVC` with an empty contract
        environment (every call unfolded, inlining depth TEST_DEPTH). (a) plain `jverify_generic`; (b) for long
        concrete runs: jvc evaluates a run without symbolic branches in ONE simp call, which stops at simp's
        default step limit (100000), so `jverify_generic` is stopped at the first inlined call and the rest of the
        run is evaluated by one simp call with jvc's simp set and a large step limit, then `jvc` closes what is
        left."""
        extra = ["inlineFuel"] + (["Native.throwsK"] if "assertThrows" in (unit.signature or {}).get("jimple", "")
                                  else [])
        ex = ", ".join(extra)
        head = (f"refine MethodVC.sat_of_allVC (Γ := fun _ => none) (d := {self.TEST_DEPTH})\n"
                f"  (Ann := {{ inv := fun _ => [], fuel := fun _ => {self.TEST_FUEL} }})\n"
                "  (fun _ _ h => by cases h) ?_\n")
        common = {"binders": "", "statement": "", "options": [], "strength": "noub", "needs": []}
        return [
            dict(common, tactics=head + f"jverify_generic [{ex}]",
                 notes=f"template: test run unfolded (empty contract environment, inlining depth {self.TEST_DEPTH})"),
            dict(common, tactics=head + "jverify_generic\n"
                 "all_goals simp (config := { decide := true, failIfUnchanged := false, zetaDelta := true, "
                 "maxSteps := 20000000 })\n"
                 f"  (disch := jdisch) [jsimp, jground, jnative, jctor, jeval, jbodyWP, *, {ex}]\n"
                 f"all_goals jvc [{ex}]",
                 notes="template: test run unfolded with one large simp call (long concrete runs; empty contract "
                       f"environment, inlining depth {self.TEST_DEPTH})")]

    # ---- modular builds (target option `modular = true`): one module per class, BodyVC per method, link step ----

    BODY_LEMMAS = ["Contains", "Program.ClassDecl.findMethod", "Targets", "Program.selectSpecial"]
    # method level: `jverify_body` resolves lookups through the shape facts itself; unfolding the lookups by hand
    # (the class-level list) leaves the shaped calls unresolved, so these are removed from the model's list too
    SHAPE_BLOCK = {"Contains", "Program.ClassDecl.findMethod", "Targets", "Program.selectSpecial", "Program.findMethod",
                   "ClassDecl.findMethod", "ClassDecl.erase", "MethodDecl.erase", "Program.staticDecl"}

    def modular_module(self, unit: Unit, build: Build) -> str | None:
        """The unit's own module in a modular build (its METHOD module when the pinned JimpleLean has method-level
        facts, else its class module), else None. Test methods keep the whole program (their statement is about it),
        and so do self-recursive methods (their own contract in Γ needs Contracts.valid)."""
        mods = build.info.get("jmodular")
        sig = unit.signature or {}
        if not mods or self.is_test_unit(unit, build) or sig.get("recursive"):
            return None
        if build.info.get("jmethod"):
            return build.info["jmethod"].get(unit.name)
        return mods.get(sig.get("cls"))

    def _method_level(self, unit: Unit, build: Build) -> bool:
        return unit.name in (build.info.get("jmethod") or {})

    def _facts(self, unit: Unit, build: Build) -> str:
        """The facts F of a modular theorem: `Shapes` of the classes it touches (method level: no method body is
        named), or `Contains` of those classes (class level)."""
        ks = self._classes_of(unit, build)
        if self._method_level(unit, build):
            return "(Shapes · [" + ", ".join(build.info["shape_const"][k] for k in ks) + "])"
        return "(Contains · [" + ", ".join(build.info["class_const"][k] for k in ks) + "])"

    def _classes_of(self, unit: Unit, build: Build) -> list[str]:
        """The application classes a modular theorem's facts name: the unit's own class, its callees' classes (a
        static call's resolution needs them) and the classes its body refers to (fields, `new`, invokes)."""
        known = build.info.get("class_const") or {}
        by = {u.name: u for u in build.units}
        own = (unit.signature or {}).get("cls")
        out = [own]
        for c in unit.callees:
            k = (by[c].signature or {}).get("cls") if c in by else None
            if k and k not in out:
                out.append(k)
        body = (unit.signature or {}).get("jimple", "")
        for k in re.findall(r"<([\w.$]+): ", body) + re.findall(r"\bnew ([\w.$]+)", body):
            if k in known and k not in out:
                out.append(k)
        return [k for k in out if k in known]

    def modular_parts(self, unit: Unit, build: Build, callees: list[str], contracts: dict) -> tuple[str, list[str]]:
        """No hypotheses (callee contracts are data in Γ); imports: method level = the unit's own method module and
        the shapes of the classes it touches; class level = the class modules the theorem names."""
        if self._method_level(unit, build):
            return "", ([build.info["jmethod"][unit.name]]
                        + [build.info["jshape"][k] for k in self._classes_of(unit, build)])
        mods = build.info["jmodular"]
        return "", [mods[k] for k in self._classes_of(unit, build)]

    def modular_prompt(self, unit: Unit, build: Build) -> str:
        return ""          # the Java prompt explains the modular statement itself (user_prompt)

    def _ref(self, unit: Unit, build: Build) -> str:
        if self._method_level(unit, build):
            return build.info["method_ref"][unit.name]
        sig = unit.signature or {}
        cls = sig.get("cls")
        key = f"{sig.get('name')}({','.join(sig.get('params', []))})"
        dup = [u for u in build.units if (u.signature or {}).get("cls") == cls and
               f"{(u.signature or {}).get('name')}({','.join((u.signature or {}).get('params', []))})" == key]
        # JimpleLean adds `:ret` when two DECLARATIONS share name(params), bodiless ones included
        # (build.declared_keys, per class in build.info["dup_keys"])
        if len(dup) > 1 or key in (build.info.get("dup_keys") or {}).get(cls, ()):
            key += f":{sig.get('ret')}"
        return f"{build.info['class_const'][cls]}.«{key}».ref"

    def _sig_lit(self, unit: Unit) -> str:
        sig = unit.signature or {}
        ps = ", ".join(_jtype(p) for p in sig.get("params", []))
        return f'(⟨"{sig.get("cls")}", {_jtype(sig.get("ret", "void"))}, "{sig.get("name")}", [{ps}]⟩ : MethodSig)'

    def _gamma(self, unit: Unit, build: Build, contracts: dict) -> str:
        by = {u.name: u for u in build.units}
        entries = []
        for c in unit.callees:
            if c in contracts and c in by:
                spec = _spec_parts(contracts[c].statement)[0]
                entries.append(f"({self._sig_lit(by[c])}, {spec})")
        return f"(Contracts.env [{', '.join(entries)}])"

    def modular_proposal(self, unit: Unit, build: Build, prop: dict, contracts: dict) -> dict:
        """Rebuild the statement mechanically around the model's spec and invariants: `BodyVC (Contains · [classes])
        Γ 0 ref S A fuel`, with the facts F, the callee contracts Γ and the method reference fixed by veriforch
        (the model's own F/Γ/reference, in either the MethodVC or the BodyVC form, are ignored), and `jverify`
        replaced by `jverify_body`. Raises ValueError for a proposal that cannot be a modular theorem."""
        spec, inv, fuel = _spec_parts(prop.get("statement", ""))
        if ".prog" in spec or "vo_mref" in spec or "genericSpec" in spec:
            raise ValueError("the spec must not mention the program (`... .prog`, `vo_mref`, `genericSpec`): a modular "
                             "theorem holds in every program that contains the class")
        stmt = f"BodyVC {self._facts(unit, build)} {self._gamma(unit, build, contracts)} 0 {self._ref(unit, build)} " \
               f"{spec} {inv} {fuel}"
        if self._method_level(unit, build):
            return dict(prop, statement=stmt, tactics=_body_tactics(prop.get("tactics", ""), [], self.SHAPE_BLOCK))
        return dict(prop, statement=stmt, tactics=_body_tactics(prop.get("tactics", ""), self.BODY_LEMMAS))

    def _modular_section(self, unit: Unit, build: Build, callees, hypotheses) -> str:
        cons = {u: c for u, _h, c in hypotheses}
        cons.update({ob.unit: ob.contract for ob, _ in callees})
        by = {u.name: u for u in build.units}
        gam = []
        for c in unit.callees:
            if c in cons and c in by:
                gam.append(f"  ({self._sig_lit(by[c])}, {_spec_parts(cons[c].statement)[0]})")
        lines = [
            "## Modular proof (" + ("per-method modules: only this method's body and the shapes of the classes it "
            "touches are imported; other methods' bodies are unknown, so every call needs its contract in Γ"
            if self._method_level(unit, build) else "per-class modules") + "): the theorem is fixed around your spec",
            "Your `statement` may use the usual `MethodVC P Γ 0 (vo_mref ...) S A fuel` form; veriforch keeps only your "
            "spec `S` (5th argument) and invariants `A` (6th) and states, for EVERY program containing the classes:",
            f"```lean\nBodyVC {self._facts(unit, build)} Γ 0 {self._ref(unit, build)} S A fuel\n```",
            "with Γ (the callees' proved contracts, fixed):",
            ("```lean\n(Contracts.env [\n" + ",\n".join(gam) + "])\n```") if gam else "Γ = `(Contracts.env [])`.",
            "Rules: S must not mention the program (no `.prog`, `vo_mref`, `genericSpec`). A method that calls a "
            "static method of class C needs `σ.initOf \"C\" = .done` in its precondition (otherwise the call may "
            "throw NoClassDefFoundError), and a contract whose method leaves the state unchanged should say "
            "`σ' = σ` in its postcondition (callers need the class still initialized). Prove it with "
            "`subst hfuel` then `jverify_body [" + ("" if self._method_level(unit, build) else ", ".join(self.BODY_LEMMAS))
            + "]` (your `jverify` is replaced by that"
            + ("; do NOT unfold findMethod/Targets/Contains/erase yourself: jverify_body resolves the calls through "
               "the shape facts" if self._method_level(unit, build) else "")
            + ") and leaf tactics such as `all_goals (first | omega | bv_omega | (simp_all; done) | grind)`."]
        return "\n\n".join(lines)

    def assemble(self, build: Build, order: list[str], proved: dict, own: dict, hyp_order: dict,
                 modular_units: set, status: dict, log=print, n_lookups: dict | None = None) -> dict:
        """The link step: one module over the build's whole program (`jimple_program`) that turns each modular
        theorem into `Sat`, bottom-up: `<u>_sat := (<u>_vc _ rfl).sat hF hV`, with `hF : Contains prog classes` by
        evaluation (`Contains.of_check`) and `hV : Valid prog Γ` from `Contracts.valid_of_ok` and one
        `ContractOK prog sig S` per callee (from its own `_sat`: `jcontract_ok` for a virtual or interface method,
        an explicit script for a static one). Checked once; returns {unit: {ok, theorem | error}}."""
        by = {u.name: u for u in build.units}
        W = build.info["prog"]
        ns = f"{build.ns}.Link"
        linked: dict[str, str] = {}            # unit -> its `_sat` theorem in this module
        need_ok: set[str] = set()
        thms, imports = [], set()
        for n in order:
            if n not in modular_units or n not in proved:
                continue
            ob = proved[n][0]
            binders = ob.contract.binders.strip()
            if not re.fullmatch(r"\(\w+ : Nat\) \(\w+ : \w+ = \d+\)", binders):
                continue                        # a theorem with other binders is not linked automatically
            cs = hyp_order.get(n, [])
            if any(c not in linked for c in cs):
                continue
            try:
                spec = _spec_parts(ob.contract.statement)[0]
            except ValueError:
                continue
            k = len(self._classes_of(by[n], build))
            if self._method_level(by[n], build):
                # the program has the shapes the body proof assumed (by evaluation)
                hf = ("(Shapes.of_check (by decide) (by intro s hs; simp only [List.mem_cons, List.not_mem_nil, "
                      f"or_false] at hs; rcases hs with {' | '.join(['rfl'] * k)} <;> exact ⟨_, rfl, rfl⟩))")
            else:
                hf = ("(Contains.of_check (by decide) (by intro d hd; simp only [List.mem_cons, List.not_mem_nil, "
                      f"or_false] at hd; rcases hd with {' | '.join(['rfl'] * k)} <;> rfl))")
            if cs:
                alts = " | ".join(f"exact {_ident(c)}_ok" for c in cs)
                hv = ("(Contracts.valid_of_ok (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] "
                      f"at hp; rcases hp with {' | '.join(['rfl'] * len(cs))} <;> first | {alts}))")
                need_ok |= set(cs)
            else:
                hv = "(Contracts.valid_of_ok (fun _ h => by cases h))"
            tn = f"{_ident(n)}_sat"
            thms.append((n, tn, [f"theorem {tn} : Sat {W} {self._ref(by[n], build)} {spec} :=",
                                 f"  ({build.ns}.{self.theorem(by[n])} _ rfl).sat {hf} {hv}", ""], spec))
            imports.add(ob.module)
            linked[n] = tn
        if not thms:
            return {}
        body, start_of = [], {}
        head = (["import Jimple", f"import {build.info['gen_module']}"] + [f"import {m}" for m in sorted(imports)] +
                ["", "open Jimple", "", "set_option maxHeartbeats 4000000", "set_option maxRecDepth 8000", "",
                 f"namespace {ns}", ""])
        for n, tn, ls, spec in thms:
            start_of[n] = (len(head) + len(body) + 1, None)
            body += ls
            if n in need_ok:
                body += [f"theorem {_ident(n)}_ok : ContractOK {W} {self._sig_lit(by[n])} {spec} := by"]
                body += (_STATIC_OK(tn) if (by[n].signature or {}).get("static") else [f"  jcontract_ok [{tn}]"])
                body += [""]
            start_of[n] = (start_of[n][0], len(head) + len(body))
        tail = [f"#print axioms {tn}" for _, tn, _, _ in thms] + ["", f"end {ns}", ""]
        src = "\n".join(head + body + tail)
        ikeys = {build.info["gen_module"]: build.gen_modules[build.info["gen_module"]],
                 **{proved[n][0].module: proved[n][1] for n in linked}}
        res = build.pkg.check(ns, src, ikeys, timeout=900)
        std = {"propext", "Classical.choice", "Quot.sound"}
        out = {}
        failed_lines = [m.line for m in res.messages if m.severity == "error"]
        for n, tn, _, _ in thms:
            lo, hi = start_of[n]
            errs = [m.text for m in res.messages if m.severity == "error" and lo <= m.line <= hi]
            ax = None
            for m in res.messages:
                mm = re.search(r"'([^']+)' depends on axioms: \[(.*)\]", m.text, re.S)
                if mm and mm.group(1).endswith("." + tn):
                    ax = [a.strip() for a in mm.group(2).split(",") if a.strip()]
            if not errs and ax is not None and set(ax) <= std and res.status != "timeout":
                out[n] = {"ok": True, "theorem": f"{ns}.{tn}", "axioms": ax}
            else:
                out[n] = {"ok": False, "error": (errs[0] if errs else f"status {res.status}, axioms {ax}, "
                                                 f"errors at lines {failed_lines[:5]}")[:500]}
        log(f"  link: {sum(r['ok'] for r in out.values())}/{len(out)} modular Java proofs linked ({ns})")
        return out

    def equivalence_verdict(self, unit_old: Unit, unit_new: Unit, b_old: Build, b_new: Build, run_dir: Path) -> dict:
        """CI old ≡ new for a changed method: equiv-lean's `equiv_jimple` (adapters/jimple/equiv.py); `equivalent`,
        `behaviour_changed` with a sampled counterexample, or `unknown` with the reason."""
        from .equiv import verdict
        return verdict(self, unit_old, unit_new, b_old, b_new, run_dir)

    def placeholder_tactic(self) -> str:
        return "subst hfuel\njverify"

    def records(self, build: Build) -> str:
        """Application classes and their methods (for test-promotion prompts)."""
        by_cls: dict[str, list[str]] = {}
        for u in build.units:
            sig = u.signature or {}
            by_cls.setdefault(sig.get("cls", "?"), []).append(
                f"{'static ' if sig.get('static') else ''}{sig.get('ret', '?')} {sig.get('name')}({', '.join(sig.get('params', []))})")
        return "\n".join(f"class {c}: " + "; ".join(ms) for c, ms in sorted(by_cls.items()))

    def _mref(self, unit: Unit, build: Build) -> str:
        sig = unit.signature or {}
        ps = ", ".join(_jtype(p) for p in sig.get("params", []))
        key = f"{sig.get('name')}({','.join(sig.get('params', []))})"
        if key in (build.info.get("dup_keys") or {}).get(sig.get("cls"), ()):
            # two declarations of the class share name(params): select by the return type too (build._VO_MREF_RET)
            return (f'vo_mref_ret {build.info["prog"]} "{sig.get("cls")}" "{sig.get("name")}" [{ps}] '
                    f'{_jtype(sig.get("ret", "void"))}')
        return f'vo_mref {build.info["prog"]} "{sig.get("cls")}" "{sig.get("name")}" [{ps}]'

    def modular_options(self) -> list[str]:
        return []          # depth 0 in every statement: calls are answered by Γ only

    def render(self, ob: Obligation, build: Build) -> str:
        gen = build.info["gen_module"]
        if any(i.startswith("Gen.J.") for i in ob.imports):
            # a modular proof (BodyVC): only the class modules it names, never the whole program
            imports, opens = ["Jimple"] + ob.imports, "open Jimple"
        else:
            imports, opens = ["Jimple", gen] + [i for i in ob.imports if i not in ("Jimple", gen)], f"open Jimple {gen}"
        c = ob.contract
        lines = [f"import {i}" for i in imports]
        lines += ["", opens, "", "set_option maxHeartbeats 4000000", "set_option maxRecDepth 8000", "",
                  f"namespace {build.ns}", ""]
        lines += [o.strip() for o in ob.proof.options if o.strip()]
        lines.append(f"theorem {ob.theorem} {c.binders.strip()} :")
        lines.append(f"    {c.statement.strip()} := by")
        for t in ob.proof.tactics.strip("\n").splitlines():
            lines.append("  " + t if t.strip() else "")
        lines += ["", f"#print axioms {ob.theorem}", "", f"end {build.ns}", ""]
        return "\n".join(lines)

    def _head(self, unit: Unit, build: Build) -> list[str]:
        sig = unit.signature or {}
        mref = self._mref(unit, build)
        rec = (" It calls itself: put its own contract into Γ under its own signature "
               f"`({mref}).sig`." if sig.get("recursive") else "")
        return [f"# Method under verification: `{unit.name}` (kind: {unit.kind}; theorem name `{self.theorem(unit)}`)",
                f"Program term: `{build.info['prog']}`. Method reference: `{mref}`.{rec}",
                f"Declared throws: {sig.get('throws') or 'none'}. Static: {sig.get('static')}.",
                "## Java source", f"```java\n{unit.source or '(not found)'}\n```",
                "## Jimple body as JimpleLean numbers it (use these statement indices for loop-head invariants "
                "and these local numbers for `fr.get k`)",
                f"```\n{sig.get('listing') or sig.get('jimple', '')}\n```"]

    def user_prompt(self, unit: Unit, build: Build, callees, history, hypotheses=()) -> str:
        from ...scheduler import truncate
        parts = self._head(unit, build)
        if callees and not self.is_test_unit(unit, build):
            parts.append("## Contracts of its callees (proved). Put each callee's spec into Γ verbatim, keyed by "
                         "the callee's `(vo_mref ...).sig`:")
            for ob, _ in callees:
                parts.append(f"```lean\n-- {ob.unit}\n{ob.contract.statement}\n```")
        if hypotheses:
            parts.append("## Unproved callee contracts (passed to your theorem as hypotheses by the orchestrator; "
                         "use their specs in Γ the same way):")
            for u, h, c in hypotheses:
                parts.append(f"```lean\n-- {u} ({h})\n{c.statement}\n```")
        if self.modular_module(unit, build) is not None:
            parts.append(self._modular_section(unit, build, callees, hypotheses))
        if self.is_test_unit(unit, build):
            parts.append(
                "## This is a JUnit test method; its theorem statement is fixed (see below)\n"
                "`Sat P m (genericSpec P m [])`: every terminating run from a typed state returns normally (no "
                "assertion fails, no exception escapes). Prove it through `MethodVC.sat_of_allVC (Γ := Γ') (d := D) "
                "(Ann := ...) hAll ?_`: with `Γ' := fun _ => none` the `hAll` argument is `(fun _ _ h => by cases h)` "
                "and every call is unfolded up to depth D (the code under test is executed; inlined bodies are "
                "explored for `inlineFuel` statements, so pass `inlineFuel` to jverify/jvc/simp). You may instead put "
                "your own contracts into Γ' (any Γ' with a proof of `AllVC P Γ' D Ann`, e.g. by `Contracts.allVC`) and "
                "cut points into `Ann.inv` to split a long run; jvc evaluates a run without symbolic branches in one "
                "simp call (simp's default limit is 100000 steps; `simp (config := { maxSteps := N })` with "
                "`[jsimp, jground, jnative, jctor, jeval, jbodyWP, *, inlineFuel]` and `(disch := jdisch)` goes further).")
        elif not callees and not hypotheses:
            parts.append("It calls no other application method: Γ is `Contracts.env []` unless it calls itself.")
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

    def intended_prompt(self, unit: Unit, build: Build) -> str:
        parts = self._head(unit, build)
        parts.append(f"This method is outside the model ({unit.scope}), so it cannot be verified now. State the "
                     "contract its callers may rely on, in the same convention (binders "
                     "`(fuel : Nat) (hfuel : fuel = N)`, statement `MethodVC ...` with the spec inline). It will be "
                     "used only as an explicit hypothesis of its callers' theorems. Give JSON: binders, statement, notes.")
        return "\n\n".join(parts)

    def prompt_pack(self) -> str:
        guide = (HERE / "prompt_pack.md").read_text()
        ex = []
        for rel in EXAMPLES:
            p = jbuild.JIMPLELEAN / rel
            if p.exists():
                ex.append(f"## {rel}\n```lean\n{p.read_text()}\n```")
        return guide + "\n\n# Worked examples from JimpleLean (all check)\n\n" + "\n\n".join(ex)


_PRIM = {t: f"(.prim .{t})" for t in ("int", "long", "boolean", "char", "byte", "short", "float", "double")}


def _split_args(s: str) -> list[str]:
    """Top-level whitespace-separated terms of a Lean application (brackets, braces, ⟨⟩ and strings balanced)."""
    out, cur, depth, i, n = [], [], 0, 0, len(s)
    opening, closing = "([{⟨", ")]}⟩"
    while i < n:
        ch = s[i]
        if ch == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
            cur.append(s[i:j + 1])
            i = j + 1
            continue
        if ch in opening:
            depth += 1
        elif ch in closing:
            depth -= 1
        if ch.isspace() and depth == 0:
            if cur:
                out.append("".join(cur))
                cur = []
        else:
            cur.append(ch)
        i += 1
    if cur:
        out.append("".join(cur))
    return out


def _spec_parts(statement: str) -> tuple[str, str, str]:
    """(S, A, fuel) of `MethodVC P Γ d m S A fuel` or `BodyVC F Γ d m S A fuel`."""
    args = _split_args(statement.strip())
    if len(args) != 8 or args[0] not in ("MethodVC", "BodyVC", "Jimple.MethodVC", "Jimple.BodyVC"):
        raise ValueError("the statement must be `MethodVC P Γ 0 m S A fuel` (or `BodyVC F Γ 0 m S A fuel`) with each "
                         "argument parenthesized: S = `(Spec.of ...)`, A = `[...]`")
    return args[5], args[6], args[7]


def _body_tactics(tactics: str, lemmas: list[str], block: set[str] | None = None) -> str:
    """`jverify [xs]` -> `jverify_body [lemmas, xs]` (a BodyVC goal); `jverify_body [xs]` gets the lemmas too;
    names in `block` are dropped from the model's list."""
    def rep(m):
        extra = [x.strip() for x in (m.group(2) or "").split(",") if x.strip() and x.strip() not in (block or set())]
        return "jverify_body [" + ", ".join(dict.fromkeys(lemmas + extra)) + "]"
    return re.sub(r"\bjverify(?:_body)?\b(?!_)(\s*\[([^\]]*)\])?", rep, tactics)


def _STATIC_OK(sat: str) -> list[str]:
    """`ContractOK prog sig S` of a STATIC method from its `Sat` fact: the call targets are the method itself; the
    behavioural-subtyping part holds because virtual selection only sees instance methods, so no virtual call of the
    static signature can execute (`jcontract_ok` covers virtual and interface methods)."""
    return ["  refine ⟨?_, ?_⟩",
            "  · intro m ht",
            "    obtain ⟨hsel, hb⟩ := ht",
            "    rcases hsel with h | h | ⟨hs, _⟩",
            "    all_goals first",
            f"      | (simp (config := {{ decide := true }}) only [jground, Program.Target.jimple.injEq] at h; subst h; "
            f"exact {sat})",
            "      | exact absurd h (by simp (config := { decide := true }) only [jground, reduceCtorEq, not_false_eq_true])",
            "      | exact absurd hs (by simp (config := { decide := true }) [clinitSig])",
            "  · apply forall_progClass_of_mem",
            "    simp (config := { decide := true }) only [jground, List.forall_mem_cons, List.forall_mem_nil, and_true]",
            "    repeat' apply And.intro",
            "    all_goals first",
            "      | trivial",
            "      | (intro _ args σ o hpre hv; cases hv <;> simp_all (config := { decide := true }) [jground, Spec.of])",
            "      | (intro args σ o hpre hv; cases hv <;> simp_all (config := { decide := true }) [jground, Spec.of])"]


def _has_loop(listing: str) -> bool:
    """A backward branch in the numbered listing (`[i] ... goto labelN=[k]` with k <= i)."""
    for line in listing.splitlines():
        m = re.match(r"\[(\d+)\]", line)
        if not m:
            continue
        i = int(m.group(1))
        if any(int(k) <= i for k in re.findall(r"=\[(\d+)\]", line)):
            return True
    return False


def _jtype(t: str) -> str:
    """Jimple type text -> Lean `JType` term (see Jimple/Syntax.lean)."""
    t = t.strip()
    if t.endswith("[]"):
        return f"(.array {_jtype(t[:-2])})"
    if t in _PRIM:
        return _PRIM[t]
    if t == "void":
        return ".void"
    return f'(.cls "{t}")'


def _ident(s: str) -> str:
    out = re.sub(r"\W", "_", s)
    return out if out[:1].isalpha() else "u" + out

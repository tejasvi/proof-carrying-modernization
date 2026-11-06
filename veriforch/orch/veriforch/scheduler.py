"""Bottom-up verification of one build: callees first, one contract module per unit, proposals from the
LLM checked by Lean, proof scripts cached by (body, callee contracts, bridge pin).

Assume-guarantee: a callee that is out of the bridge's scope (gap) or whose proof failed (stuck) does not
block its callers. Its contract (the last proposal, or an "intended contract" asked for once) is passed to
every caller's theorem as an explicit hypothesis `h_<callee>`, and that hypothesis is propagated to the
callers' callers. Results that depend on such hypotheses are reported as `conditional`, with the list of
assumed contracts. No axioms are ever added.
"""
from __future__ import annotations

import json
import os
import re
import threading
import time
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from .graph import bottom_up
from .lean import is_native_axiom, nonstandard_axioms
from .llm import LLM, BudgetExceeded, LLMError
from .model import Contract, Obligation, ObligationResult, ProofScript, read_json, sha256, write_json

INTENDED_SCHEMA = {
    "type": "object",
    "properties": {
        "binders": {"type": "string"},
        "statement": {"type": "string"},
        "notes": {"type": "string"},
    },
    "required": ["binders", "statement", "notes"],
    "additionalProperties": False,
}


@dataclass
class UnitOutcome:
    unit: str
    status: str                     # proved | conditional | stuck | gap | blocked | error | budget
    attempts: int = 0
    seconds: float = 0.0
    needs: list[str] = field(default_factory=list)
    assumes: list[str] = field(default_factory=list)
    detail: str = ""
    obligation: dict[str, Any] | None = None
    result: dict[str, Any] | None = None
    cache_key: str = ""
    key: str = ""                   # proof key (body, callee contracts, pin, kind) the outcome was computed for
    statement_origin: str = ""      # mechanical (bridge template / type-derived) | llm (needs review) | ""
    trust: str = ""                 # kernel (standard axioms) | native (also trusts Lean's compiler: native_decide)

    def to_json(self):
        return self.__dict__.copy()


def proof_key(body_hash: str, callee_keys: list[str], pin: str, kind: str) -> str:
    return sha256("|".join([pin, kind, body_hash] + sorted(callee_keys)))


def infer_origin(prop: dict) -> str:
    """Statement origin of a stored proposal without the field (cache entries written before it existed):
    bridge templates and inference tools mark their notes."""
    notes = (prop.get("notes") or "").lower()
    return "mechanical" if notes.startswith(("template", "generic no-unexpected", "cirinv")) else "llm"


def hyp_name(unit: str) -> str:
    return "h_" + "".join(c if c.isalnum() or c == "_" else "_" for c in unit)


def hyp_binder(unit: str, c: Contract) -> str:
    b = c.binders.strip()
    return f"({hyp_name(unit)} : ∀ {b}, {c.statement.strip()})" if b else f"({hyp_name(unit)} : {c.statement.strip()})"


def verify_build(adapter, build, llm: LLM | None, *, attempts: int = 4, only: set[str] | None = None,
                 effort: str = "high", assume_gaps: bool = True, jobs: int = 1, check_timeout: int = 300,
                 retry_stuck: bool = False, hints: dict[str, str] | None = None,
                 log=print) -> dict[str, UnitOutcome]:
    run_dir = build.dir.parents[1]
    proof_cache = run_dir / "cache" / "proofs"
    by_body = proof_cache / "by_body"
    out_dir = build.dir / "units"
    out_dir.mkdir(parents=True, exist_ok=True)
    gen = build.info["gen_module"]
    types_mod = build.info.get("types_module")
    if hasattr(adapter, "support_modules"):
        # veriforch's own Lean definitions that mechanical statements use (entry-point calling conventions)
        build.gen_modules.update(adapter.support_modules(build))
    deps = build.info.get("gen_deps")        # generated modules that import each other (Rust: callees' modules)

    def _gen_check(gm: str) -> None:
        # import keys: the top module imports everything before it; a function module may import Types, or with
        # `gen_deps` the generated modules listed there
        gk = (dict(build.gen_modules) if gm == gen
              else {d: build.gen_modules[d] for d in deps[gm]} if deps is not None and gm in deps
              else {types_mod: build.gen_modules[types_mod]} if types_mod in build.gen_modules else {})
        res = build.pkg.check(gm, build.pkg.src(gm).read_text(), gk, timeout=900)
        if not res.ok:
            raise RuntimeError(f"generated module {gm} does not check: {res.errors[:3]}")
        build.gen_modules[gm] = res.cache_key

    order = build.info.get("gen_order", [gen])
    if deps is not None:
        # level by level (a module after every module it imports), each level in parallel
        left = list(order)
        while left:
            ready = [m for m in left if not set(deps.get(m, [])) & set(left)]
            if not ready:
                raise RuntimeError(f"generated modules import each other in a cycle: {left[:5]}")
            with ThreadPoolExecutor(max_workers=max(1, jobs)) as ex:
                for f in [ex.submit(_gen_check, gm) for gm in ready]:
                    f.result()
            left = [m for m in left if m not in ready]
    elif len(order) > 2:
        # Types, then the per-function modules (independent of each other) in parallel, then the top module
        _gen_check(order[0])
        with ThreadPoolExecutor(max_workers=max(1, jobs)) as ex:
            for f in [ex.submit(_gen_check, gm) for gm in order[1:-1]]:
                f.result()
        _gen_check(order[-1])
    else:
        for gm in order:
            _gen_check(gm)
    by = {u.name: u for u in build.units}
    proved: dict[str, tuple[Obligation, str]] = {}
    assumed: dict[str, Contract] = {}
    assumes: dict[str, list[str]] = {}
    own: dict[str, Contract] = {}            # proved units' own contracts (without hypotheses or context binders)
    modular_units: set[str] = set()          # proved over an abstract context (cir2lean --modular)
    hyp_order: dict[str, list[str]] = {}     # a modular unit's callee hypotheses, in binder order
    n_lookups: dict[str, int] = {}           # lookup-fact binders of a modular cycle member (default: own + libraries)
    syms = {u.lean_decl: u.sym for u in build.units}
    outcomes: dict[str, UnitOutcome] = {}
    given = _given_contracts(build)          # contracts a bridge owner states for units whose proof is pending
    given_specs = _given_specs(build)        # ... and their proof files, when the owner's proof is done
    if only is not None and assume_gaps:
        # an --only run composes its units against the given contracts of units it does not process (e.g. a top
        # level checked against its callees' agreed contracts before their proofs exist): those stay assumptions
        assumed.update({n: c for n, c in given.items() if n not in only and n in {u.name for u in build.units}})
    system = adapter.prompt_pack()
    lock = threading.Lock()
    scc_of = {n: set(c) for c in bottom_up(build.units) for n in c}

    def do_unit(name: str) -> None:
        u = by[name]
        if only is not None and name not in only:
            return
        t0 = time.time()
        mech = adapter.mechanical_contract(u, build) if hasattr(adapter, "mechanical_contract") else None
        # a concrete test (a run from the initial memory) is proved by executing the real code; an entry point over
        # arbitrary inputs (strength "inputs") needs its callees' contracts like any other unit
        concrete = mech is not None and mech.strength != "inputs"
        # a static "external call" gap does not stop a test unit: its concrete run decides (a check's failure
        # branch may call printf without the run ever reaching it); a run that reaches the call fails honestly
        if not u.in_scope and not (concrete and u.scope.startswith("gap:external")):
            oc = UnitOutcome(name, "gap", detail=u.scope)
            if assume_gaps and name in given:
                with lock:
                    assumed[name] = given[name]
                oc.detail += f"; given contract ({given[name].note}) recorded as an assumption for callers"
            elif assume_gaps and llm is not None and u.kind != "test":
                # (a test is never called: its intended contract would serve no caller)
                c = _intended_contract(adapter, build, u, llm, system, log)
                if c is not None:
                    with lock:
                        assumed[name] = c
                    oc.detail += "; intended contract recorded as an assumption for callers"
            with lock:
                outcomes[name] = oc
            log(f"  {name}: gap ({u.scope})")
            _write(out_dir, oc, [])
            return
        # callees in the unit's own SCC (recursion) never block it: their calls are handled inside the proof
        # (unfolded by concrete execution, or by the bridge's recursion support); a unit with a mechanical
        # statement (a test) is never blocked: it is proved by executing the real callee bodies
        missing = [c for c in u.callees if c not in proved and c not in assumed and c not in scc_of.get(name, ())]
        if missing and not concrete:
            oc = UnitOutcome(name, "blocked", detail="callees without contracts: " + ", ".join(missing))
            with lock:
                if assume_gaps and name in given:
                    # a bridge owner's statement of this unit: its callers can be composed against it now
                    assumed[name] = given[name]
                    oc.detail += f"; given contract assumed: {given[name].note}"
                outcomes[name] = oc
            log(f"  {name}: blocked by {missing}")
            _write(out_dir, oc, [])
            return
        callees = [proved[c] for c in u.callees if c in proved]
        # the generated module the unit's obligation imports: the top module, or the unit's own function module when
        # the adapter names one (Rust: then an edit elsewhere leaves the obligation's Lean inputs unchanged)
        ugen = adapter.unit_gen_module(u, build) if hasattr(adapter, "unit_gen_module") else gen
        fmod = adapter.modular_module(u, build) if hasattr(adapter, "modular_module") else None
        # modular proof: the unit's own function module only, over any context containing it, with every callee's
        # contract as a hypothesis (recursive units and tests keep the whole module)
        modular = fmod is not None and mech is None and len(scc_of.get(name, ())) <= 1 and name not in u.callees
        if modular:
            mh = [c for c in u.callees if c in proved or c in assumed]
            hyps = sorted({c for c in mh if c not in proved}
                          | set().union(*[set(assumes.get(c, [])) for c in mh if c in proved]))
            hcon = {c: own[c] if c in proved else assumed[c] for c in mh}
            if hasattr(adapter, "modular_parts"):
                # the adapter states the modular theorem itself (Java: callee contracts are data in Γ)
                hyp_text, imports = adapter.modular_parts(u, build, mh, hcon)
            else:
                hyp_text = " ".join([adapter.modular_prefix(u, build)]
                                    + [adapter.modular_hyp_text(hyp_binder(c, hcon[c]), syms) for c in mh])
                imports = ([fmod] + [build.info["modular"][s] for s in adapter.modular_libs(u, build)]
                           + ([types_mod] if types_mod else []))
            ikeys = {m: build.gen_modules[m] for m in imports}
            ckeys = [hcon[c].key() for c in mh] + ["modular"]
        else:
            mh, hcon = [], {}
            # a test unit with a mechanical statement is proved by executing the real callees, so it takes no
            # assumed-contract hypotheses (cir_vcg would prefer them to the bodies at call sites)
            hyps = [] if concrete else sorted(
                set().union(*[set(assumes.get(c, [])) for c in u.callees if c in proved])
                | {c for c in u.callees if c in assumed and c not in proved})
            hyp_text = " ".join(hyp_binder(h, assumed[h]) for h in hyps)
            # a mechanical test unit imports no callee proofs: its run executes the real callee bodies, and an
            # imported `@[cir_spec]` contract would replace a body at its call sites (a weak contract would stop it)
            if concrete:
                imports = list(mech.imports)
                ikeys = {ugen: build.gen_modules[ugen], **{m: build.gen_modules[m] for m in imports}}
            else:
                extra = list(mech.imports) if mech is not None else []
                imports = extra + [ob.module for ob, _ in callees]
                ikeys = {ugen: build.gen_modules[ugen], **{m: build.gen_modules[m] for m in extra},
                         **{ob.module: k for ob, k in callees}}
            ckeys = [ob.contract.key() for ob, _ in callees] + [assumed[h].key() for h in hyps]
        if getattr(adapter, "cache_scope", "body") == "variant":
            # a bridge whose proofs mention the whole program (JimpleLean: the program term P) cannot reuse a proof
            # of the same body from another build variant
            ckeys = ckeys + [f"variant:{build.variant.name}"]
        pkey = proof_key(u.body_hash, ckeys, adapter.pin, u.kind)
        history: list[tuple[Obligation, ObligationResult, dict]] = []
        oc = UnitOutcome(name, "stuck", assumes=hyps, key=pkey)
        prev = _unit_file(out_dir, name)
        neg = proof_cache / "negative" / f"{pkey}.json"     # failures shared across revisions and variants
        hint = (hints or {}).get(name)
        d = None
        # a proof stored for these inputs wins over a recorded failure (a later run may have found it)
        if not retry_stuck and not hint and not (proof_cache / f"{pkey}.json").exists():
            for f in (prev, neg):
                if f.exists():
                    d = read_json(f)
                    if d.get("key") == pkey:
                        break
                    d = None
        if d is not None:
            if d.get("key") == pkey and d.get("status") == "stuck" and d.get("attempts", 0) >= attempts \
                    and d.get("history"):
                # negative cache: same inputs already failed with this many attempts; reuse, no LLM call
                last = d["history"][-1]["proposal"]
                for k in ("status", "attempts", "needs", "detail", "obligation", "result", "cache_key"):
                    setattr(oc, k, d.get(k, getattr(oc, k)))
                oc.detail = (oc.detail + "; " if oc.detail else "") + "reused failed outcome (negative cache)"
                if assume_gaps:
                    with lock:
                        assumed[name] = Contract(unit=name, binders=last["binders"], statement=last["statement"],
                                                 origin="assumed", strength=last.get("strength", "noub"), attrs="")
                with lock:
                    outcomes[name] = oc
                log(f"  {name}: stuck (negative cache, {oc.attempts} earlier attempts)")
                return
        cached = proof_cache / f"{pkey}.json"
        candidates: list[tuple[str, dict]] = []
        if hint:
            pass                        # re-opened on a caller's request: fresh proposals only
        elif cached.exists():
            candidates.append(("cache", read_json(cached)))
        if not hint:
            candidates += [("reuse", p) for p in _body_candidates(by_body, u, adapter.pin)[:2]
                           if not candidates or p != candidates[0][1]]
        prev_prop = None if (hint or mech is not None) else _prev_unit(by_body, u, adapter.pin)
        if prev_prop and all(prev_prop != c for _, c in candidates):
            candidates.append(("prev", prev_prop))
        # free proofs first: the bridge's own template (e.g. the standard tactic script), no LLM call
        if not hint and hasattr(adapter, "template_candidates"):
            candidates += [("template", dict(p, statement_origin=p.get("statement_origin", "mechanical")))
                           for p in adapter.template_candidates(u, build) if all(p != c for _, c in candidates)]
        if not hint and name in given_specs:
            # a script written against assumed callee contracts (h_<callee> hypotheses) also runs where the callees
            # are proved: `callee_aliases` binds each h_<callee> to the callee's theorem (and its own assumptions)
            aliases = "\n".join(f"have {hyp_name(c)} := {adapter.theorem(by[c])}" +
                                "".join(" " + hyp_name(h) for h in assumes.get(c, []))
                                for c in u.callees if c in proved and c != name)
            gp = _given_proof_candidate(adapter, build, u, given_specs[name], ikeys, check_timeout, log,
                                        aliases=aliases)
            if gp is not None:
                candidates.insert(0, ("given", gp))
        n_llm = 0
        while True:
            if candidates:
                origin, prop = candidates.pop(0)
            else:
                if llm is None or n_llm >= attempts:
                    break
                n_llm += 1
                try:
                    prompt = adapter.user_prompt(u, build, callees, history,
                                                 hypotheses=([(c, hyp_name(c), hcon[c]) for c in mh] if modular
                                                             else [(h, hyp_name(h), assumed[h]) for h in hyps]))
                    if prev_prop:
                        prompt += ("\n\n## Previous contract (proved for the previous version of this function)\n"
                                   f"```lean\n{prev_prop.get('binders', '')} :\n    {prev_prop.get('statement', '')}\n```\n"
                                   "Callers' proofs depend on it: keep exactly these binders and this statement if "
                                   "the new code still satisfies them, and change only the tactics. Change the "
                                   "contract only if the code's behaviour changed.")
                    if modular and hasattr(adapter, "modular_prompt"):
                        prompt += adapter.modular_prompt(u, build)
                    elif modular:
                        prompt += ("\n\n## Modular proof (the function's own module only)\n"
                                   "The theorem is stated over ANY context `ctx` containing the function (binder "
                                   f"`hf : ctx.mod.findFunc? \"{u.sym}\" = some {u.lean_decl}`, added for you), and every "
                                   "callee is available only through its contract hypothesis `h_<callee>` (no callee "
                                   "body, no callee `fn_` declaration: refer to callees by their symbol string). "
                                   "Write `binders`/`statement` for the function itself as usual (`Returns ctx "
                                   f"{u.lean_decl}.sym ...`); `cir_start` uses `hf`, and `cir_vcg` applies the hypotheses "
                                   "at call sites.")
                    if mech is not None:
                        prompt += ("\n\n## The theorem statement is FIXED (stated mechanically from the test unit)\n"
                                   f"```lean\ntheorem {adapter.theorem(u)} {mech.binders} :\n    {mech.statement}\n```\n"
                                   "Give only `tactics` (and `options`); your `binders` and `statement` are ignored.")
                        defs = adapter.mechanical_defs(mech) if hasattr(adapter, "mechanical_defs") else ""
                        if defs:
                            prompt += ("\n\n## Definitions the fixed statement uses (veriforch's own Lean, in scope)\n"
                                       f"```lean\n{defs}\n```")
                    if hint:
                        prompt += ("\n\n## Requested by its callers\nThe previous contract of this function was "
                                   "too weak for its callers' proofs. They need:\n" + hint +
                                   "\nKeep the precondition as weak as before and strengthen the postcondition "
                                   "(return value, memory effects, Frame) accordingly.")
                        old = read_json(prev) if prev.exists() else {}
                        old_ob = old.get("obligation") or {}
                        if old.get("status") in ("proved", "conditional", "partial") and old_ob.get("proof"):
                            prompt += ("\n\n## Previous proof (of the previous contract, kernel-checked)\n"
                                       f"```lean\ntheorem {old_ob.get('theorem', '')} "
                                       f"{old_ob['contract'].get('binders', '')} :\n    "
                                       f"{old_ob['contract'].get('statement', '')} := by\n"
                                       f"{old_ob['proof'].get('tactics', '')}\n```\n"
                                       "Adapt this script to the requested contract rather than starting over.")
                    prop = llm.ask_json(f"{build.variant.name}:{name}:{len(history)}", system, prompt,
                                        adapter.schema(),
                                        effort="xhigh" if (attempts >= 3 and n_llm == attempts) else effort)
                except BudgetExceeded as e:
                    oc.status, oc.detail = "budget", str(e)
                    break
                except LLMError as e:
                    oc.detail = f"LLM: {e}"
                    continue
                origin = "llm"
                prop["statement_origin"] = "llm"
            if mech is not None:
                prop = dict(prop, binders=mech.binders, statement=mech.statement, statement_origin="mechanical",
                            strength=mech.strength)
            if modular and hasattr(adapter, "modular_proposal"):
                # the adapter rebuilds the statement around the proposal (e.g. Java: facts, Γ and the method
                # reference fixed, the model's spec and invariants kept); a proposal it cannot use is a failed attempt
                try:
                    prop = adapter.modular_proposal(u, build, prop, hcon)
                except ValueError as e:
                    history.append((Obligation(unit=name, module=adapter.module(build, u),
                                               contract=Contract(unit=name, binders=prop.get("binders", ""),
                                                                 statement=prop.get("statement", "")),
                                               proof=ProofScript(tactics=prop.get("tactics", ""))),
                                    ObligationResult(status="error", errors=[f"rejected: {e}"]), prop))
                    log(f"  {name}: proposal rejected ({e})")
                    continue
            vac = vacuous(prop["binders"])
            if vac:
                history.append((Obligation(unit=name, module=adapter.module(build, u),
                                           contract=Contract(unit=name, binders=prop["binders"],
                                                             statement=prop["statement"]),
                                           proof=ProofScript(tactics=prop["tactics"])),
                                ObligationResult(status="error", errors=[f"rejected: vacuous precondition ({vac})"]),
                                prop))
                log(f"  {name}: proposal rejected (vacuous precondition: {vac})")
                continue
            binders = (hyp_text + " " + prop["binders"]).strip()
            options = list(prop.get("options", []))
            # callers are always proved against callee contracts, never callee bodies; except test units with a
            # mechanical statement: a concrete test run is proved by executing the code under test (evaluation)
            if (hyps or callees or mh) and not concrete and not any(o in options for o in adapter.modular_options()):
                options = adapter.modular_options() + [o for o in options if "inline" not in o]
            ob = Obligation(unit=name, module=adapter.module(build, u),
                            contract=Contract(unit=name, binders=binders, statement=prop["statement"],
                                              origin=origin, strength=prop.get("strength", "noub"),
                                              attrs=adapter.attrs(u), note=prop.get("notes", "")),
                            proof=ProofScript(tactics=prop["tactics"], options=options, origin=origin),
                            imports=imports + [i for i in prop.get("extra_imports", []) if i not in imports],
                            theorem=adapter.theorem(u))
            src = adapter.render(ob, build)
            # a given proof script (an engineer's long symbolic run, e.g. an entry point splitting into 16 paths)
            # gets the owners' memory cap; model proposals keep the package default
            res = build.pkg.check(ob.module, src, {**ikeys, **prop.get("extra_import_keys", {})},
                                  timeout=check_timeout,
                                  mem_gib=max(build.pkg.mem_gib, 128) if origin == "given" else None)
            # VO_KERNEL_ONLY=1: accept only kernel-checked proofs (a cached native proof is then tried and rejected)
            native_ok = bool(prop.get("native")) and os.environ.get("VO_KERNEL_ONLY") != "1"
            bad_ax = nonstandard_axioms(res.axioms, native=native_ok)
            if res.ok and bad_ax:
                res.status, res.errors = "error", res.errors + [f"non-standard axioms: {bad_ax}"]
            history.append((ob, res, prop))
            oc.attempts = len(history)
            log(f"  {name}: attempt {len(history)} ({origin}) -> {res.status} in {res.seconds:.1f}s"
                + (f"; needs {prop.get('needs')}" if prop.get("needs") else "")
                + (f"; assumes {hyps}" if hyps else ""))
            if res.ok:
                # internal functions may assume anything their callers establish (checked at call sites);
                # for API functions an assumption beyond the calling convention limits what was proved
                assumptions = ([n for n in prop.get("needs", []) if not n.lower().startswith("tool_gap")]
                               if u.kind == "api" else [])
                # a proof that needed assumptions beyond the calling convention is reported as partial; a bridge
                # that puts callee contracts inside the statement (JimpleLean's Γ) proves only a conditional result
                # until the contracts are linked (modular builds link them in `assemble`)
                in_stmt = getattr(adapter, "callee_contracts_in_statement", False) and callees and not modular \
                    and mech is None
                oc.status = "partial" if assumptions else ("conditional" if (hyps or in_stmt) else "proved")
                oc.needs = list(prop.get("needs", []))
                oc.statement_origin = prop.get("statement_origin") or infer_origin(prop)
                oc.trust = "native" if any(is_native_axiom(a) for a in res.axioms or []) else "kernel"
                proof_cache.mkdir(parents=True, exist_ok=True)
                write_json(cached, prop)
                _remember_body(by_body, u, adapter.pin, prop)
                _remember_unit(by_body, u, adapter.pin, prop)
                if neg.exists():
                    neg.unlink()            # these inputs are proved now: drop the shared failure record
                with lock:
                    proved[name] = (ob, res.cache_key)
                    own[name] = Contract(unit=name, binders=prop["binders"], statement=prop["statement"],
                                         origin=origin, strength=prop.get("strength", "noub"), attrs="")
                    if modular:
                        modular_units.add(name)
                        hyp_order[name] = list(mh)
                with lock:
                    assumes[name] = hyps
                break
        if history:
            ob, res, prop = history[-1]
            oc.obligation, oc.result, oc.cache_key = ob.to_json(), res.to_json(), res.cache_key
            if oc.status not in ("proved", "conditional", "partial"):
                oc.needs = list(prop.get("needs", []))
                if assume_gaps and name in given:
                    # a bridge owner's statement of this unit (its proof pending) is what callers assume
                    assumed[name] = given[name]
                    oc.detail = (oc.detail + "; " if oc.detail else "") + f"given contract assumed: {given[name].note}"
                elif assume_gaps:
                    # the unproved contract becomes an assumption of every caller
                    assumed[name] = Contract(unit=name, binders=prop["binders"], statement=prop["statement"],
                                             origin="assumed", strength=prop.get("strength", "noub"), attrs="")
        if oc.status == "stuck" and mech is None and hasattr(adapter, "refute"):
            # a bridge with an executable translation tests a stuck mechanical statement on generated inputs: a
            # counterexample replaces the gap, and a refuted statement is not assumed by callers
            try:
                ref = adapter.refute(u, build)
            except Exception as e:              # a refutation failure must not hide the unit's outcome
                ref = {"error": f"{type(e).__name__}: {e}"[:300]}
            if ref:
                write_json(_unit_file(build.dir / "findings", f"{name}.refutation"), ref)
                if ref.get("refuted"):
                    oc.detail = (oc.detail + "; " if oc.detail else "") + \
                        f"statement refuted: panics on {ref.get('input')} ({ref.get('outcome')})"
                    with lock:
                        if name in assumed and assumed[name].statement == ref.get("statement"):
                            del assumed[name]
        oc.seconds = round(time.time() - t0, 1)
        with lock:
            outcomes[name] = oc
            # verify.json after every unit, merged with the previous file, so a stopped run keeps what it proved
            _checkpoint()
        _write(out_dir, oc, history)
        if oc.status == "stuck" and history:
            neg.parent.mkdir(parents=True, exist_ok=True)
            _write(neg.parent, oc, history, name=neg.stem)

    def do_group(comp: list[str]) -> bool:
        """A cycle of the call graph (mutual or self recursion) as ONE obligation: the model proposes every
        member's contract, a measure and per-member tactics; the adapter generates the strong-induction skeleton
        and one theorem per member. Returns False when the cycle is not handled as a group (then each member is
        processed alone, as before)."""
        us = [by[n] for n in comp]
        if not hasattr(adapter, "render_group") or (only is not None and not set(comp) & only):
            return False
        mod_cycle = bool(build.info.get("modular_proofs")) and hasattr(adapter, "modular_group_parts")
        if build.info.get("modular_proofs") and not mod_cycle:
            return False                        # the adapter cannot state a cycle over an abstract context
        if any(not u.in_scope for u in us):
            return False
        if hasattr(adapter, "mechanical_contract") and any(adapter.mechanical_contract(u, build) for u in us):
            return False
        if all(given_specs.get(n, {}).get("proof_file") for n in comp):
            return False                        # the bridge owner proved every member: each imports its theorem
        t0 = time.time()
        ext = sorted({c for u in us for c in u.callees if c not in comp})
        missing = [c for c in ext if c not in proved and c not in assumed]
        if missing:
            for n in comp:
                oc = UnitOutcome(n, "blocked", detail="callees without contracts: " + ", ".join(missing))
                with lock:
                    if assume_gaps and n in given:
                        assumed[n] = given[n]
                        oc.detail += f"; given contract assumed: {given[n].note}"
                    outcomes[n] = oc
                _write(out_dir, oc, [])
            log(f"  cycle {comp}: blocked by {missing}")
            return True
        callees = [proved[c] for c in ext if c in proved]
        hyps = sorted(set().union(*[set(assumes.get(c, [])) for c in ext if c in proved])
                      | {c for c in ext if c in assumed and c not in proved})
        if mod_cycle:
            # modular build: the cycle is stated over any context containing its members (and the library functions
            # they call), with every callee outside the cycle as a contract hypothesis, like a single modular unit
            hcon = {c: own[c] if c in proved else assumed[c] for c in ext}
            hyp_text, imports, n_look = adapter.modular_group_parts(us, build, ext, hcon, syms)
            ikeys = {m: build.gen_modules[m] for m in imports}
            ckeys = [hcon[c].key() for c in ext] + ["cycle", "modular"]
        else:
            hcon, n_look = {}, 0
            hyp_text = " ".join(hyp_binder(h, assumed[h]) for h in hyps)
            imports = [ob.module for ob, _ in callees]
            ugen = adapter.unit_gen_module(us[0], build) if hasattr(adapter, "unit_gen_module") else gen
            ikeys = {ugen: build.gen_modules[ugen], **{ob.module: k for ob, k in callees}}
            ckeys = [ob.contract.key() for ob, _ in callees] + [assumed[h].key() for h in hyps] + ["cycle"]
        module = adapter.group_module(build, comp)
        # a bridge owner's lemma for some members (e.g. one loop of the cycle, stated with the other members'
        # contracts as hypotheses, `lemma_file` in given_contracts): checked as a module of its own, imported by the
        # group module and named in the prompt; members whose specs also give `measure` and `tactics` keep them
        # A member's spec may instead name an ASSUMPTION (`assume`: a Prop defined in its lemma file, e.g. the step
        # lemma of one loop, stated in the induction's own shape): it becomes a hypothesis of the cycle theorem, so
        # the cycle and every caller are `conditional` on that named Prop until the owner's proof replaces it.
        given_members, lemma_mods, step_assumed, discharged = {}, {}, [], {}
        for n in sorted(comp):
            spec = given_specs.get(n, {})
            bundle = spec.get("lemma_bundle")
            if bundle and hasattr(adapter, "given_proof_text") and bundle["dir"] not in lemma_mods:
                # an owner's proof spread over many modules (its own tactic and lemma modules, then the main one):
                # each is checked here in the given order as `<prefix>.<module>`, its imports of the other bundle
                # modules rewritten to that prefix and its generated-module import pointed at this build's
                lemma_mods[bundle["dir"]] = None
                names = set(bundle["order"])
                ok_b = True
                for bm in bundle["order"]:
                    try:
                        text = adapter.given_proof_text(build, {**spec, "proof_file": f"{bundle['dir']}/{bm}.lean"},
                                                        require_gen=False)
                    except (OSError, ValueError) as e:
                        log(f"  cycle {comp}: bundle module {bm} not usable here ({e})")
                        ok_b = False
                        break
                    text = "\n".join(f"import {bundle['prefix']}.{ln.split()[1]}"
                                     if ln.startswith("import ") and ln.split()[1] in names else ln
                                     for ln in text.splitlines()) + "\n"
                    bmod = f"{bundle['prefix']}.{bm}"
                    res = build.pkg.check(bmod, text, ikeys, timeout=max(check_timeout, 1800),
                                          mem_gib=max(build.pkg.mem_gib, 128))
                    bad = nonstandard_axioms(res.axioms, native=False)
                    if not res.ok or bad:
                        log(f"  cycle {comp}: bundle module {bm} does not check: {(res.errors or [str(bad)])[0][:300]}")
                        ok_b = False
                        break
                    ikeys = {**ikeys, bmod: res.cache_key}
                    if bm == bundle["main"]:
                        imports, ckeys = imports + [bmod], ckeys + [res.cache_key]
                        log(f"  cycle {comp}: bridge owner's bundle {bundle['dir']} checks ({res.seconds:.0f}s main)")
                if ok_b:
                    lemma_mods[bundle["dir"]] = bundle["prefix"]
            if bundle and lemma_mods.get(bundle["dir"]) and spec.get("discharge"):
                discharged.update(spec["discharge"])      # {assumption Prop: owner's theorem proving it}
            if not spec.get("lemma_file") or not hasattr(adapter, "given_proof_text"):
                continue
            lf = spec["lemma_file"]
            if lf not in lemma_mods:               # one module per distinct file (members may share one)
                lm = f"{module}_given{len(lemma_mods)}"
                lemma_mods[lf] = None
                try:
                    text = adapter.given_proof_text(build, {**spec, "proof_file": lf})
                except (OSError, ValueError) as e:
                    log(f"  cycle {comp}: bridge owner's lemma file for {n} not usable here ({e})")
                    continue
                res = build.pkg.check(lm, text, ikeys, timeout=max(check_timeout, 1800),
                                      mem_gib=max(build.pkg.mem_gib, 128))   # owners' proofs are large
                bad = nonstandard_axioms(res.axioms, native=False)
                if not res.ok or bad:
                    log(f"  cycle {comp}: bridge owner's lemma file {lf} does not check: "
                        f"{(res.errors or [str(bad)])[0][:300]}")
                    continue
                log(f"  cycle {comp}: bridge owner's lemma file {lf} checks ({res.seconds:.0f}s)")
                lemma_mods[lf] = lm
                imports, ikeys, ckeys = imports + [lm], {**ikeys, lm: res.cache_key}, ckeys + [res.cache_key]
            if lemma_mods[lf] is None:
                continue
            given_members[n] = spec
            if spec.get("assume") and spec["assume"] not in discharged:
                step_assumed.append(spec["assume"])
        if step_assumed and not mod_cycle:
            with lock:
                for a in step_assumed:
                    assumed[a] = Contract(unit=a, binders="", statement=a, origin="assumed", attrs="",
                                          note="named step assumption of a cycle member (owner's proof pending)")
            hyps = sorted(set(hyps) | set(step_assumed))
            hyp_text = " ".join(hyp_binder(h, assumed[h]) for h in hyps)
            ckeys = ckeys + [f"assume:{a}" for a in sorted(set(step_assumed))]
        gkey = proof_key("+".join(sorted(u.body_hash for u in us)), ckeys, adapter.pin, "cycle")
        cached = proof_cache / f"{gkey}.json"
        neg_g = proof_cache / "negative" / f"{gkey}.json"
        hinted = any((hints or {}).get(n) for n in comp)
        if not retry_stuck and not hinted and neg_g.exists() and not cached.exists():   # a stored proof wins over a failure record
            d = read_json(neg_g)
            if d.get("attempts", 0) >= attempts:
                last = d.get("last") or {}
                for n in comp:
                    oc = UnitOutcome(n, "stuck", attempts=d["attempts"], key=gkey,
                                     detail="cycle: reused failed outcome (negative cache)")
                    m = last.get(n)
                    if assume_gaps and m:
                        with lock:
                            assumed[n] = Contract(unit=n, binders=m["binders"], statement=m["statement"],
                                                  origin="assumed", attrs="")
                    with lock:
                        outcomes[n] = oc
                log(f"  cycle {comp}: stuck (negative cache, {d['attempts']} earlier attempts)")
                return True
        log(f"  cycle {comp}: one obligation (strong induction on a measure)")
        candidates = [("cache", read_json(cached))] if cached.exists() else []
        if set(given_members) == set(comp) and all(s.get("measure") and s.get("tactics")
                                                   for s in given_members.values()):
            from .adapters.cir.patch import binder_groups

            def _subst(s: dict) -> str:
                # {names}: the member's binder names; {assume:P}: the hypothesis naming assumption P;
                # {thm:<unit>}: that unit's proved theorem in this build
                t = s["tactics"].replace("{names}", " ".join(x for g, _, _ in binder_groups(s["binders"]) for x in g))
                # an assumption discharged by an owner's theorem is that theorem; otherwise the hypothesis
                t = re.sub(r"\{assume:([^}]+)\}", lambda mm: discharged.get(mm.group(1)) or hyp_name(mm.group(1)), t)
                # a callee proved here is its theorem; an assumed callee is the cycle theorem's hypothesis
                return re.sub(r"\{thm:([^}]+)\}", lambda mm: adapter.theorem(by[mm.group(1)]) if mm.group(1) in proved
                              else hyp_name(mm.group(1)), t)
            candidates.insert(0, ("given", {"members": [{"unit": n, "binders": s["binders"], "statement": s["statement"],
                                                         "measure": s["measure"], "tactics": _subst(s)}
                                                        for n, s in given_members.items()],
                                            "options": [o for s in given_members.values() for o in s.get("options", [])],
                                            "strength": "noub", "statement_origin": "given",
                                            "notes": "bridge owner's lemmas" + ("; assumed: " + ", ".join(step_assumed)
                                                                                if step_assumed else "")}))
        history: list[tuple[dict, ObligationResult, dict]] = []
        n_llm, done, last_members = 0, None, {}
        while True:
            if candidates:
                origin, prop = candidates.pop(0)
            else:
                if llm is None or n_llm >= attempts:
                    break
                n_llm += 1
                try:
                    prompt = adapter.group_prompt(us, build, callees, history,
                                                  hypotheses=[(h, hyp_name(h), assumed[h]) for h in hyps])
                    asked = [(n, (hints or {})[n]) for n in sorted(comp) if (hints or {}).get(n)]
                    if asked:
                        prompt += ("\n\n## Requested contract forms (from the callers and callees of this cycle)\n"
                                   + "\n".join(f"### `{n}`\n{text}" for n, text in asked))
                    for n, s in given_members.items():
                        prompt += (f"\n\n## Bridge owner's lemma for `{n}` (imported, kernel-checked)\n"
                                   "Keep this member's binders, statement and measure exactly as below; its tactics "
                                   "can be the lemma applied to `k`, the induction hypotheses `h_<member>` it takes, the "
                                   "member's binder names and `hk`" + (f", e.g. `{s['tactics']}`" if s.get("tactics")
                                                                     else "") + ".\n"
                                   f"binders: {s['binders']}\nstatement: {s['statement']}\n"
                                   f"measure: {s.get('measure', '?')}\nlemma: {s.get('lemma_statement', '(see file)')}")
                    # one answer carries every member's contract and tactics: allow a long answer, and keep the
                    # effort at the run's level (xhigh thinking on a cycle tends to exhaust the token limit)
                    prop = llm.ask_json(f"{build.variant.name}:cycle:{sorted(comp)[0]}:{len(history)}", system,
                                        prompt, adapter.group_schema(), effort=effort, max_tokens=128000)
                except BudgetExceeded:
                    break
                except LLMError as e:
                    log(f"  cycle {comp}: LLM error {e}")
                    continue
                origin = "llm"
            members = {m.get("unit"): m for m in prop.get("members", [])}
            if set(members) != set(comp):
                history.append(({}, ObligationResult(status="error", errors=[
                    f"members must be exactly {sorted(comp)}; got {sorted(k for k in members if k)}"]), prop))
                continue
            last_members = members
            vac = [vacuous(m["binders"]) for m in members.values() if vacuous(m["binders"])]
            if vac:
                history.append((members, ObligationResult(status="error",
                                                          errors=[f"rejected: vacuous precondition ({vac[0]})"]), prop))
                continue
            options = list(prop.get("options", []))
            if (callees or hyps) and not any(o in options for o in adapter.modular_options()):
                options = adapter.modular_options() + [o for o in options if "inline" not in o]
            try:
                src = adapter.render_group(build, us, members, hyp_text, imports, options)
            except ValueError as e:
                history.append((members, ObligationResult(status="error", errors=[str(e)]), prop))
                continue
            res = build.pkg.check(module, src, ikeys, timeout=check_timeout)
            bad_ax = nonstandard_axioms(res.axioms)
            if res.ok and bad_ax:
                res.status, res.errors = "error", res.errors + [f"non-standard axioms: {bad_ax}"]
            history.append((members, res, prop))
            log(f"  cycle {comp}: attempt {len(history)} ({origin}) -> {res.status} in {res.seconds:.1f}s")
            if res.ok:
                done = (origin, prop, res)
                break
        secs = round(time.time() - t0, 1)
        if done:
            origin, prop, res = done
            proof_cache.mkdir(parents=True, exist_ok=True)
            write_json(cached, prop)
            if neg_g.exists():
                neg_g.unlink()                  # these inputs are proved now: drop the shared failure record
            for u in us:
                m = members[u.name]
                needs = [x for x in m.get("needs", []) if not x.lower().startswith("tool_gap")]
                ob = Obligation(unit=u.name, module=module,
                                contract=Contract(unit=u.name, binders=(hyp_text + " " + m["binders"]).strip(),
                                                  statement=m["statement"], origin=origin,
                                                  strength=prop.get("strength", "noub"), attrs=adapter.attrs(u),
                                                  note=f"cycle {sorted(comp)}: " + (prop.get("notes") or "")),
                                proof=ProofScript(tactics=m["tactics"], options=list(prop.get("options", [])),
                                                  origin=origin),
                                imports=imports, theorem=adapter.theorem(u))
                status = "partial" if (needs and u.kind == "api") else ("conditional" if hyps else "proved")
                oc = UnitOutcome(u.name, status, attempts=len(history), seconds=secs, needs=list(m.get("needs", [])),
                                 assumes=hyps, obligation=ob.to_json(), result=res.to_json(),
                                 cache_key=res.cache_key, key=gkey,
                                 statement_origin=prop.get("statement_origin") or "llm", trust="kernel",
                                 detail=f"cycle {sorted(comp)} proved together ({module})")
                with lock:
                    proved[u.name] = (ob, res.cache_key)
                    own[u.name] = Contract(unit=u.name, binders=m["binders"], statement=m["statement"],
                                           origin=origin, attrs="")
                    assumes[u.name] = hyps
                    outcomes[u.name] = oc
                    if mod_cycle:
                        modular_units.add(u.name)
                        hyp_order[u.name] = list(ext)
                        n_lookups[u.name] = n_look
                _write(out_dir, oc, [])
        else:
            for u in us:
                oc = UnitOutcome(u.name, "stuck", attempts=len(history), seconds=secs, key=gkey,
                                 detail=f"cycle {sorted(comp)}: no proof")
                m = last_members.get(u.name)
                if assume_gaps and m:
                    with lock:
                        assumed[u.name] = Contract(unit=u.name, binders=m["binders"], statement=m["statement"],
                                                   origin="assumed", attrs="")
                with lock:
                    outcomes[u.name] = oc
                _write(out_dir, oc, [(None, r, p) for _, r, p in history])
            if history:
                neg_g.parent.mkdir(parents=True, exist_ok=True)
                write_json(neg_g, {"attempts": len(history), "last": last_members,
                                   "errors": [r.errors[:2] for _, r, _ in history]})
        with lock:
            _checkpoint()
        return True

    def _checkpoint() -> None:
        # a full run's file holds this run's units only (a stopped run keeps what it proved); an --only run merges
        vj = build.dir / "verify.json"
        prev = read_json(vj) if (only is not None and vj.exists()) else {}
        write_json(vj, {**prev, **{n: o.to_json() for n, o in outcomes.items()}})

    comps = bottom_up(build.units)
    comp_of = {n: i for i, c in enumerate(comps) for n in c}
    deps = {i: {comp_of[c] for n in comp for c in by[n].callees if c in comp_of and comp_of[c] != i}
            for i, comp in enumerate(comps)}
    # units with a mechanical statement (tests) need no callee results: they start at once, ahead of the rest
    def _concrete(u) -> bool:
        mc = adapter.mechanical_contract(u, build)
        return mc is not None and mc.strength != "inputs"
    mech_names = ({u.name for u in build.units if (only is None or u.name in only) and _concrete(u)}
                  if hasattr(adapter, "mechanical_contract") else set())
    mech_comp = {i for i, comp in enumerate(comps) if all(n in mech_names for n in comp)}
    for i in mech_comp:
        deps[i] = set()
    order = sorted(range(len(comps)), key=lambda i: (i not in mech_comp, i))

    def run_comp(comp: list[str]) -> None:
        recursive = len(comp) > 1 or comp[0] in by[comp[0]].callees
        if recursive and do_group(comp):
            return
        if len(comp) > 1:
            log(f"  recursion: SCC {comp} (each contract is checked on its own; recursive calls need a measure)")
        for name in comp:
            do_unit(name)

    done: set[int] = set()
    running: dict[int, Future] = {}
    with ThreadPoolExecutor(max_workers=max(1, jobs)) as ex:
        while len(done) < len(comps):
            for i in order:
                if i not in done and i not in running and deps[i] <= done:
                    running[i] = ex.submit(run_comp, comps[i])
            finished, _ = wait(list(running.values()), return_when=FIRST_COMPLETED)
            for i, f in list(running.items()):
                if f in finished:
                    f.result()
                    done.add(i)
                    del running[i]
    if modular_units and hasattr(adapter, "assemble"):
        # instantiate the modular proofs with the concrete module: each callee hypothesis becomes the callee's own
        # (assembled) theorem; a unit whose chain reaches an unproved callee stays conditional
        order = [n for comp in comps for n in comp]
        asm = adapter.assemble(build, order, {n: proved[n] for n in proved}, own, hyp_order, modular_units,
                               {n: o.status for n, o in outcomes.items()}, log=log, n_lookups=n_lookups)
        for n in modular_units:
            o = outcomes.get(n)
            if o is None or o.status not in ("proved", "conditional", "partial"):
                continue
            r = asm.get(n)
            if r and r.get("ok"):
                o.detail = (o.detail + "; " if o.detail else "") + f"modular; assembled: {r['theorem']}"
            elif not o.assumes:
                o.status = "conditional"
                o.detail = (o.detail + "; " if o.detail else "") + "modular; assembly failed: " + \
                    (r or {}).get("error", "not attempted")[:300]
        write_json(build.dir / "assembly.json", asm)
    vj = build.dir / "verify.json"
    # an --only run updates its units and keeps the others' outcomes; a full run replaces the file
    keep = read_json(vj) if (only is not None and vj.exists()) else {}
    write_json(vj, {**keep, **{n: o.to_json() for n, o in outcomes.items()}})
    write_json(build.dir / "assumed.json", {n: c.to_json() for n, c in assumed.items()})
    return outcomes


def _given_contracts(build) -> dict[str, Contract]:
    """Target option `given_contracts` (a JSON file next to the target, or absolute): {unit: {binders, statement,
    imports?, source}}. Such a contract is never treated as proved: when the unit itself ends unproved, callers
    assume it (they become `conditional` on the unit, as with any assumed contract), so they upgrade once the
    unit's proof lands. No axiom is added."""
    path = build.target.extra.get("given_contracts")
    if not path:
        return {}
    p = Path(path)
    if not p.is_absolute():
        p = Path(build.target.extra.get("_target_dir", ".")) / p
    data = json.loads(p.read_text())
    return {u: Contract(unit=u, binders=c["binders"], statement=c["statement"], origin="given", attrs="",
                        strength=c.get("strength", "functional"), note=c.get("source", "given"),
                        imports=list(c.get("imports", [])))
            for u, c in data.items()}


def _given_specs(build) -> dict[str, dict]:
    path = build.target.extra.get("given_contracts")
    if not path:
        return {}
    p = Path(path)
    if not p.is_absolute():
        p = Path(build.target.extra.get("_target_dir", ".")) / p
    return json.loads(p.read_text())


def _given_proof_candidate(adapter, build, u, spec: dict, ikeys: dict, timeout: int, log,
                           aliases: str = "") -> dict | None:
    """A bridge owner's proof of this unit (`proof_file` + `theorem` in given_contracts): its file is checked in
    this build's package as a module of its own (the adapter swaps its generated-module import for this build's),
    then offered as the first candidate, `exact <theorem> <binders>`. It is checked like any other proof: kernel,
    axioms, cache. Returns None when the file does not check here."""
    if spec.get("tactics_file") and not spec.get("proof_file"):
        # a proof script for this unit's own obligation as veriforch renders it (callee contracts in scope, given
        # contracts of unproved callees as hypotheses), e.g. written by a proof engineer iterating with
        # `vo verify --only <unit> --no-llm`: offered as the first candidate, checked like any other
        try:
            tactics = Path(spec["tactics_file"]).read_text()
            if spec.get("callee_aliases") and aliases:
                tactics = aliases + "\n" + tactics
        except OSError as e:
            log(f"  {u.name}: given proof script not readable ({e})")
            return None
        log(f"  {u.name}: given proof script {spec['tactics_file']}")
        return {"binders": spec["binders"], "statement": spec["statement"], "tactics": tactics,
                "options": list(spec.get("options", [])), "statement_origin": "given",
                "strength": spec.get("strength", "functional"), "notes": spec.get("source", "given proof script")}
    if not spec.get("proof_file") or not hasattr(adapter, "given_proof_text"):
        return None
    gm = adapter.module(build, u) + "_given"
    try:
        text = adapter.given_proof_text(build, spec)
    except (OSError, ValueError) as e:
        log(f"  {u.name}: bridge owner's proof not usable here ({e})")
        return None
    res = build.pkg.check(gm, text, ikeys, timeout=max(timeout, 1800),
                          mem_gib=max(build.pkg.mem_gib, 128))   # owners' proofs are large (32 GiB aborted one)
    bad = nonstandard_axioms(res.axioms, native=False)
    if not res.ok or bad:
        log(f"  {u.name}: bridge owner's proof does not check in this build: "
            f"{(res.errors or [str(bad)])[0][:300]}")
        return None
    from .adapters.cir.patch import binder_groups      # Lean binder syntax (the same for every Lean bridge)
    names = " ".join(x for g, _, _ in binder_groups(spec["binders"]) for x in g)
    log(f"  {u.name}: bridge owner's proof checks in this build ({spec['theorem']}, {res.seconds:.0f}s)")
    tactics = f"exact {spec['theorem']} {names}"
    if spec.get("tactics"):
        # the owner's theorem takes a callee's contract as an argument (e.g. `(hutf : Utf16Spec)`): the spec names
        # the term, with `{names}` for the binder names and `{thm:<unit>}` for that callee's proved theorem here
        by_name = {x.name: x for x in build.units}
        tactics = re.sub(r"\{thm:([^}]+)\}", lambda mm: adapter.theorem(by_name[mm.group(1)]),
                         spec["tactics"].replace("{names}", names))
    return {"binders": spec["binders"], "statement": spec["statement"],
            "tactics": tactics, "extra_imports": [gm], "extra_import_keys": {gm: res.cache_key},
            "statement_origin": "given", "strength": spec.get("strength", "functional"),
            "notes": spec.get("source", "bridge owner's proof")}


def refinement_hints(build, outcomes: dict[str, UnitOutcome]) -> dict[str, str]:
    """Callees named in a stuck caller's `needs` (by symbol or short name): the caller's needs become a hint for
    re-opening the callee's contract in a second pass."""
    by = {u.name: u for u in build.units}
    hints: dict[str, list[str]] = {}
    for name, oc in outcomes.items():
        if oc.status != "stuck" or not oc.needs:
            continue
        text = " ".join(oc.needs)
        for c in by[name].callees:
            cu = by.get(c)
            if cu is None or outcomes.get(c) is None or outcomes[c].status not in ("proved", "conditional", "partial"):
                continue
            dem = (cu.signature or {}).get("demangled") if isinstance(cu.signature, dict) else ""
            short = (dem or c).split("(")[0].split("::")[-1].split("<")[0]
            if c in text or (len(short) > 2 and re.search(r"\b" + re.escape(short) + r"\b", text)):
                hints.setdefault(c, []).append(f"[{name}] " + text[:1500])
    return {c: "\n".join(v) for c, v in hints.items()}


def _intended_contract(adapter, build, u, llm: LLM, system: str, log) -> Contract | None:
    """Ask once for the contract a gap unit is meant to satisfy; it is used only as a hypothesis."""
    cache = build.dir.parents[1] / "cache" / "intended" / f"{adapter.pin}_{u.body_hash}_{u.kind}.json"
    if cache.exists():
        d = read_json(cache)
    else:
        try:
            d = llm.ask_json(f"{build.variant.name}:{u.name}:intended", system,
                             adapter.intended_prompt(u, build), INTENDED_SCHEMA, effort="low")
        except (LLMError, BudgetExceeded) as e:
            log(f"  {u.name}: no intended contract ({e})")
            return None
        write_json(cache, d)
    return Contract(unit=u.name, binders=d["binders"], statement=d["statement"], origin="assumed",
                    strength="functional", attrs="", note=d.get("notes", ""))


def _body_candidates(by_body: Path, u, pin: str) -> list[dict]:
    p = by_body / f"{pin}_{u.body_hash}_{u.kind}.jsonl"
    if not p.exists():
        return []
    out = []
    for line in reversed(p.read_text().splitlines()):
        try:
            out.append(json.loads(line))
        except ValueError:
            pass
    return out


def _remember_body(by_body: Path, u, pin: str, prop: dict) -> None:
    by_body.mkdir(parents=True, exist_ok=True)
    with open(by_body / f"{pin}_{u.body_hash}_{u.kind}.jsonl", "a") as f:
        f.write(json.dumps(prop, sort_keys=True) + "\n")


def _prev_unit(by_body: Path, u, pin: str) -> dict | None:
    """The last accepted proposal for a unit of this name (any body): after an edit, its contract is tried first,
    so a behaviour-preserving edit keeps the contract and its callers' proofs stay cached."""
    p = by_body.parent / "by_unit" / f"{pin}_{_safe(u.name)}_{u.kind}.json"
    if p.exists():
        return read_json(p)
    # a new bridge pin: the unit's latest accepted proposal on any earlier pin, so a re-pin keeps the contracts
    # (callers' proofs depend on them) and the model is asked only if the old proof no longer checks
    others = sorted((by_body.parent / "by_unit").glob(f"*_{_safe(u.name)}_{u.kind}.json"),
                    key=lambda f: f.stat().st_mtime) if (by_body.parent / "by_unit").is_dir() else []
    return read_json(others[-1]) if others else None


def _remember_unit(by_body: Path, u, pin: str, prop: dict) -> None:
    d = by_body.parent / "by_unit"
    d.mkdir(parents=True, exist_ok=True)
    write_json(d / f"{pin}_{_safe(u.name)}_{u.kind}.json", prop)


def _safe(name: str) -> str:
    return "".join(c if c.isalnum() or c in "_-" else "_" for c in name)[:180]


def _unit_file(out_dir: Path, name: str) -> Path:
    """`<out_dir>/<name>.json`: a unit's record (units/, the negative cache), or a finding (`<unit>.refutation`). A name
    over 220 bytes (UTF-8) is too long for a file name (Java units with long parameter lists: thrift's
    NonblockingSaslHandler.<init>(...) is 384 bytes) once write_json adds `.json` and its temporary suffix
    `.<pid>.<thread id>.tmp` (up to 28 bytes; 255 is the limit): its first 200 bytes, cut at a character boundary, `_`
    and 16 hex digits of the whole name's sha256 (at most 250 bytes with both suffixes). Every read and write of these
    paths goes through here."""
    b = name.encode()
    if len(b) <= 220:
        return out_dir / f"{name}.json"
    return out_dir / f"{b[:200].decode('utf-8', 'ignore')}_{sha256(b)[:16]}.json"


def _write(out_dir: Path, oc: UnitOutcome, history, name: str | None = None) -> None:
    write_json(_unit_file(out_dir, name or oc.unit), {**oc.to_json(),
                                              "history": [{"proposal": p, "status": r.status,
                                                           "errors": r.errors[:3],
                                                           # the conclusion is at the end of a goal: keep both ends
                                                           "goals": [g if len(g) <= 4000 else
                                                                     g[:1200] + "\n…\n" + g[-2800:]
                                                                     for g in r.goals[:2]]}
                                                          for _, r, p in history]})


_VACUOUS = [re.compile(p) for p in (r":\s*False\s*\)", r":\s*0\s*<\s*0\s*\)", r":\s*1\s*=\s*0\s*\)",
                                    r":\s*\(?\s*(\w+)\s*<\s*\1\s*\)?\s*\)")]


_FUNC_BINDER = re.compile(r"\(\s*((?:[A-Za-z_][\w']*\s+)*[A-Za-z_][\w']*)\s*:\s*([^():]*→[^():]*)\)")


def vacuous(binders: str) -> str:
    """A syntactic guard against proposals that make the theorem vacuous (hypothesis `False`, `x < x`, ...)
    or that assume the computation itself: a function-typed ghost variable (e.g. `(s : Int → Int)` constrained
    to be the loop's trace) is a precondition no caller can establish. Hypotheses (names starting with `h`)
    may contain `→`. Semantic non-vacuity comes from the concrete test theorems."""
    for r in _VACUOUS:
        m = r.search(binders)
        if m:
            return m.group(0).strip()
    for m in _FUNC_BINDER.finditer(binders):
        names = m.group(1).split()
        if not all(n.startswith("h") for n in names):
            return f"function-typed ghost variable {m.group(0).strip()}: state preconditions over the inputs only"
    return ""


def truncate(s: str, n: int) -> str:
    return s if len(s) <= n else s[: n * 2 // 3] + "\n…[truncated]…\n" + s[-n // 3 :]

"""Model-proposed test generalisations (DESIGN.md step 2, "needs review" part), language independent.

Headline test theorems are stated MECHANICALLY by the adapter from the compiled test units
(`Adapter.mechanical_contract`, proved by the scheduler with the statement fixed). This module adds what a
model can contribute on top, and everything it states is labelled origin "llm" and reported separately as
"needs review": the statement was chosen by the model, so it is trusted only after a human reads it.

1. Extraction: the model reads the target's test files and lists the test cases as JSON: the API function
   exercised, the literal inputs, the checks on the result. Each case is validated against the source
   (cited line in range, literal values present in the file), so a hallucinated case is dropped.
2. Statements: per API function, the model states, in the bridge's vocabulary (adapter prompt pack):
   * a concrete theorem per case: the test as written, i.e. on this input the call has no undefined
     behaviour / panic and the checked values come out;
   * a generalized theorem covering the cases: the literal inputs become universally quantified variables
     under the calling-convention precondition; input-specific expected values are dropped; the
     input-independent checks (ranges, relations between outputs and inputs, the memory-safety facts the
     test's own checking code relies on) become the postcondition.
3. Elaboration: each statement is checked by Lean with a placeholder proof; statements that do not
   elaborate are sent back once with the error.
4. Proof: `prove_tests` runs the proposal loop on each theorem, importing the API functions' contract
   modules, so a test proof uses one-line summaries of the code under test.
"""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

from .llm import LLM, BudgetExceeded, LLMError
from .model import Contract, Obligation, ObligationResult, ProofScript, read_json, write_json

EXTRACT_SCHEMA = {
    "type": "object",
    "properties": {
        "cases": {"type": "array", "items": {"type": "object"}},
        "notes": {"type": "string"},
    },
    "required": ["cases", "notes"],
}

STATEMENTS_SCHEMA = {
    "type": "object",
    "properties": {
        "theorems": {"type": "array", "items": {"type": "object"}},
        "notes": {"type": "string"},
    },
    "required": ["theorems", "notes"],
}

EXTRACT_INSTRUCTIONS = """You extract unit-test cases from a test file so that each can be turned into a theorem.
A test case is one call (or a short sequence of calls) of the library's API with fixed inputs, plus the
checks the test applies to the results. Helper functions defined in the test sources (wrappers that call
the API and compare results) count as part of the case: report the API function they reach.

For each case give an object with keys:
  "name": "<test function>#<k>" (k numbers the cases inside that test function),
  "line": line number of the case in the file (1-based, as shown in the listing),
  "api": the API function under test (one of the listed API functions),
  "inputs": list of {"param": parameter name or role, "value": the literal value exactly as written in
            the source (string literals with their C escapes, numbers as written), "type": source type},
  "expected": list of the input-specific expected values the test compares against (as source text),
  "relational": list of checks that do not depend on the particular input (e.g. "return value is at
            least -3", "every token's start <= end <= length"), including facts the test's own checking
            code relies on to be well defined (e.g. it reads s[start..end) so 0 <= start <= end <= len),
  "conditional": compile-time condition under which the case exists (e.g. "JSMN_STRICT") or "".
Only report cases that really appear in the file."""

STATEMENTS_INSTRUCTIONS = """You turn unit-test cases into Lean theorem statements for the bridge described in
the system prompt. For the API function below you are given its contract as proved (or assumed) by the
orchestrator, and the test cases that exercise it. Produce:

* For each case, one "concrete" theorem: the call on exactly the test's inputs, with memory hypotheses
  describing the input objects (concrete contents), stating that the call has no undefined behaviour and
  that the results the test checks come out as expected. Use the same argument/memory conventions as the
  contract.
* One or more "generalized" theorems covering several cases: replace the literal inputs by universally
  quantified variables constrained only by the calling convention (as in the contract's precondition, no
  extra numeric restrictions), drop the input-specific expected values, and state as postcondition the
  relational checks of the cases (input-independent properties). Each generalized theorem lists the case
  names it covers.

Each theorem object: {"name": Lean identifier (unique, starts with "test_"), "kind": "concrete" or
"generalized", "covers": [case names], "binders": Lean binders and hypotheses, "statement": the
conclusion (a Returns ... judgement or the bridge's equivalent), "notes": short}. Do not include proofs."""


@dataclass
class TestTheorem:
    name: str
    kind: str
    api: str
    covers: list[str]
    binders: str
    statement: str
    notes: str = ""
    elaborates: bool = False
    elab_error: str = ""
    status: str = "unproved"         # unproved | proved | stuck
    seconds: float = 0.0
    origin: str = "llm"              # the model wrote this statement: reported as "needs review", not headline

    def to_json(self):
        return self.__dict__.copy()


def numbered(text: str) -> str:
    return "\n".join(f"{i:4d}| {l}" for i, l in enumerate(text.splitlines(), start=1))


def extract_cases(target, test_file: Path, api: list[str], llm: LLM, helpers: str = "") -> list[dict]:
    text = test_file.read_text(errors="replace")
    user = "\n\n".join([
        EXTRACT_INSTRUCTIONS,
        f"API functions: {', '.join(api)}",
        f"## Test file {test_file.name} (line-numbered)\n```\n{numbered(text)}\n```",
        f"## Test helper sources\n```\n{helpers}\n```" if helpers else "",
        'Give the JSON object {"cases": [...], "notes": "..."}.'])
    d = llm.ask_json(f"extract:{test_file.name}", "You read test code precisely and answer with JSON only.",
                     user, EXTRACT_SCHEMA, effort="medium")
    lines = text.splitlines()
    good = []
    for c in d.get("cases", []):
        try:
            ln = int(c.get("line", 0))
        except (TypeError, ValueError):
            continue
        if not (1 <= ln <= len(lines)) or c.get("api") not in api:
            continue
        # every string/number input must occur in the file as written
        if all(str(i.get("value", "")) in text for i in c.get("inputs", []) if i.get("value") not in (None, "")):
            good.append(c)
    return good


def promote_tests(adapter, build, llm: LLM, *, log=print) -> list[TestTheorem]:
    """Extract cases from the target's tests and state their theorems; checks elaboration."""
    target = build.target
    out = build.dir / "tests"
    out.mkdir(parents=True, exist_ok=True)
    api = [u.name for u in build.units if u.kind == "api"]
    root = Path(target.root)
    helpers = "\n\n".join((root / h).read_text(errors="replace") for h in target.extra.get("test_helpers", [])
                          if (root / h).exists())
    cases: list[dict] = []
    cache = out / "cases.json"
    if cache.exists():
        cases = read_json(cache)
    else:
        for tf in target.tests:
            cs = extract_cases(target, root / tf, api, llm, helpers)
            for c in cs:
                c["file"] = tf
            cases += cs
            log(f"  tests: {tf}: {len(cs)} cases")
        cases = [c for c in cases if _active(c.get("conditional", ""), build.variant.flags)]
        write_json(cache, cases)
    verify = read_json(build.dir / "verify.json") if (build.dir / "verify.json").exists() else {}
    assumed = read_json(build.dir / "assumed.json") if (build.dir / "assumed.json").exists() else {}
    theorems: list[TestTheorem] = []
    by_api: dict[str, list[dict]] = {}
    for c in cases:
        by_api.setdefault(c["api"], []).append(c)
    for api_fn, cs in by_api.items():
        unit = next(u for u in build.units if u.name == api_fn)
        contract = _contract_text(verify.get(api_fn), assumed.get(api_fn))
        user = "\n\n".join([
            STATEMENTS_INSTRUCTIONS,
            f"## API function `{api_fn}` (Lean decl `{unit.lean_decl}`)\n```c\n{unit.source}\n```",
            f"## Its contract\n```lean\n{contract or '(none yet: follow the conventions of the system prompt)'}\n```",
            f"## Records\n```lean\n{adapter.records(build) if hasattr(adapter, 'records') else ''}\n```",
            "## Test cases\n```json\n" + json.dumps(cs, indent=1) + "\n```",
            'Give the JSON object {"theorems": [...], "notes": "..."}.'])
        try:
            d = llm.ask_json(f"tests:{build.variant.name}:{api_fn}", adapter.prompt_pack(), user,
                             STATEMENTS_SCHEMA, effort="high")
        except (LLMError, BudgetExceeded) as e:
            log(f"  tests: {api_fn}: no statements ({e})")
            continue
        batch = []
        for t in d.get("theorems", []):
            if not all(k in t for k in ("name", "kind", "binders", "statement")):
                continue
            th = TestTheorem(name=_ident(t["name"]), kind=t["kind"], api=api_fn, covers=list(t.get("covers", [])),
                             binders=t["binders"], statement=t["statement"], notes=t.get("notes", ""))
            _elaborate(adapter, build, th)
            batch.append(th)
            log(f"  tests: {th.name} ({th.kind}, covers {len(th.covers)}): "
                + ("elaborates" if th.elaborates else f"does not elaborate: {th.elab_error[:120]}"))
        bad = [t for t in batch if not t.elaborates]
        if bad:
            # one repair round: send the statements back with Lean's errors
            fix_user = "\n\n".join([
                "These theorem statements do not elaborate in Lean. Fix each one (keep its name, kind and "
                "covers; change only what the error requires).",
                "```json\n" + json.dumps([{"name": t.name, "kind": t.kind, "covers": t.covers, "binders": t.binders,
                                            "statement": t.statement, "error": t.elab_error[:1500]} for t in bad],
                                          indent=1) + "\n```",
                f"## Records\n```lean\n{adapter.records(build) if hasattr(adapter, 'records') else ''}\n```",
                'Give the JSON object {"theorems": [...], "notes": "..."}.'])
            try:
                d2 = llm.ask_json(f"tests-fix:{build.variant.name}:{api_fn}", adapter.prompt_pack(), fix_user,
                                  STATEMENTS_SCHEMA, effort="high")
                fixed = {t.get("name"): t for t in d2.get("theorems", []) if "binders" in t and "statement" in t}
                for th in bad:
                    t = fixed.get(th.name)
                    if t:
                        th.binders, th.statement = t["binders"], t["statement"]
                        _elaborate(adapter, build, th)
                        log(f"  tests: {th.name} after repair: "
                            + ("elaborates" if th.elaborates else f"still fails: {th.elab_error[:120]}"))
            except (LLMError, BudgetExceeded) as e:
                log(f"  tests: repair round failed ({e})")
        theorems += batch
    write_json(out / "theorems.json", [t.to_json() for t in theorems])
    return theorems


def _elaborate(adapter, build, th: TestTheorem) -> None:
    """A statement elaborates if the only errors are about the (placeholder) proof."""
    ob = Obligation(unit=th.api, module=f"{build.ns}.tests.{th.name}",
                    contract=Contract(unit=th.api, binders=th.binders, statement=th.statement, attrs=""),
                    proof=ProofScript(tactics=adapter.placeholder_tactic()), theorem=th.name)
    res = build.pkg.check(ob.module, adapter.render(ob, build),
                          {build.info["gen_module"]: build.gen_modules.get(build.info["gen_module"], "")},
                          use_cache=False, timeout=300)
    statement_errors = [e for e in res.errors if not _proof_error(e)]
    th.elaborates = not statement_errors and res.status != "timeout"
    th.elab_error = "; ".join(statement_errors)[:2000]


def _proof_error(e: str) -> bool:
    keys = ("unsolved goals", "failed", "could not prove", "maximum recursion", "heartbeats", "timeout",
            "made no progress", "linarith", "omega")
    return any(k in e for k in keys)


def _contract_text(oc: dict | None, assumed: dict | None) -> str:
    if oc and oc.get("obligation"):
        c = oc["obligation"]["contract"]
        tag = "proved" if oc.get("status") in ("proved", "conditional", "partial") else "proposed, not proved"
        return f"-- {tag}\ntheorem {oc['obligation']['theorem']} {c['binders']} :\n    {c['statement']}"
    if assumed:
        return f"-- intended contract (unverified)\n∀ {assumed['binders']}, {assumed['statement']}"
    return ""


def _active(cond: str, flags: list[str]) -> bool:
    if not cond:
        return True
    neg = cond.startswith("!")
    name = cond.lstrip("!").strip()
    on = any(f.startswith(f"-D{name}") for f in flags)
    return on != neg


def _ident(s: str) -> str:
    s = re.sub(r"\W", "_", s)
    return s if s[:1].isalpha() else "t_" + s


TACTICS_SCHEMA = {
    "type": "object",
    "properties": {
        "tactics": {"type": "string"},
        "options": {"type": "array", "items": {"type": "string"}},
        "notes": {"type": "string"},
    },
    "required": ["tactics", "options", "notes"],
}


def prove_tests(adapter, build, llm: LLM, *, attempts: int = 3, log=print) -> list[TestTheorem]:
    """Prove the elaborated test theorems against the API contracts (imported or assumed)."""
    from .scheduler import hyp_binder, hyp_name, truncate
    out = build.dir / "tests"
    theorems = [TestTheorem(**t) for t in read_json(out / "theorems.json")]
    verify = read_json(build.dir / "verify.json") if (build.dir / "verify.json").exists() else {}
    assumed = read_json(build.dir / "assumed.json") if (build.dir / "assumed.json").exists() else {}
    gen = build.info["gen_module"]
    gkey = build.gen_modules.get(gen) or build.pkg.check(gen, build.pkg.src(gen).read_text(), timeout=900).cache_key
    imports, ikeys, hyps = [], {gen: gkey}, []
    for name, oc in verify.items():
        if oc["status"] in ("proved", "conditional", "partial") and oc.get("obligation"):
            imports.append(oc["obligation"]["module"])
            ikeys[oc["obligation"]["module"]] = oc.get("cache_key", "")
            hyps += oc.get("assumes", [])
    api_assumed = [n for n, oc in verify.items() if oc["status"] not in ("proved", "conditional", "partial") and n in assumed]
    hyps = sorted(set(hyps) | set(api_assumed))
    hyp_text = " ".join(hyp_binder(h, Contract(**{k: v for k, v in assumed[h].items()
                                                   if k in Contract.__dataclass_fields__})) for h in hyps if h in assumed)
    for th in theorems:
        if not th.elaborates or th.status == "proved":
            continue
        history = []
        for k in range(attempts):
            user = "\n\n".join([
                f"# Prove the test theorem `{th.name}` ({th.kind}) about `{th.api}`.",
                f"```lean\ntheorem {th.name} {hyp_text} {th.binders} :\n    {th.statement}\n```",
                "The contracts of the proved functions are imported and tagged; the hypotheses `h_*` are "
                "unverified contracts of functions that could not be proved, use them for calls of those "
                "functions (`set_option cir.inline false in` is added when they are present).",
                *(f"Attempt {i + 1} failed:\n```\n{truncate(e, 4000)}\n```" for i, e in enumerate(history[-2:])),
                'Give {"tactics": "...", "options": [...], "notes": "..."}.'])
            try:
                d = llm.ask_json(f"testproof:{build.variant.name}:{th.name}:{k}", adapter.prompt_pack(), user,
                                 TACTICS_SCHEMA, effort="high")
            except (LLMError, BudgetExceeded) as e:
                log(f"  {th.name}: {e}")
                break
            options = list(d.get("options", []))
            if hyps and not any("inline" in o for o in options):
                options = adapter.modular_options() + options
            ob = Obligation(unit=th.api, module=f"{build.ns}.tests.{th.name}",
                            contract=Contract(unit=th.api, binders=(hyp_text + " " + th.binders).strip(),
                                              statement=th.statement, attrs=""),
                            proof=ProofScript(tactics=d["tactics"], options=options), imports=imports,
                            theorem=th.name)
            res = build.pkg.check(ob.module, adapter.render(ob, build), ikeys, timeout=600)
            th.seconds += res.seconds
            log(f"  {th.name}: attempt {k + 1} -> {res.status} in {res.seconds:.1f}s")
            if res.ok and not [a for a in res.axioms if a not in ("propext", "Classical.choice", "Quot.sound")]:
                th.status = "proved" if not hyps else "conditional"
                break
            th.status = "stuck"
            history.append("\n".join(res.errors[:2] + [g[:3000] for g in res.goals[:1]]))
    write_json(out / "theorems.json", [t.to_json() for t in theorems])
    return theorems

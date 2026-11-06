"""TypeScript adapter over StrictTS: rendering contract modules, prompts, and proof templates."""
from __future__ import annotations

import json
import re
from pathlib import Path

from ...model import Contract, Obligation, Target, Unit, Variant
from ..base import Adapter, Build
from . import build as sbuild

HERE = Path(__file__).parent
EXAMPLES = ["examples/Summarize/AutoProofs.lean", "examples/Refactor/SumProof.lean", "examples/Hash/FnvProof.lean"]


class StrictTSAdapter(Adapter):
    lang = "strictts"
    pin = sbuild.STRICTTS_PIN

    def build(self, target: Target, variant: Variant, run_dir: Path) -> Build:
        return sbuild.build(target, variant, run_dir)

    def module(self, build: Build, unit: Unit) -> str:
        return f"{build.ns}.{_ident(unit.name)}"

    def theorem(self, unit: Unit) -> str:
        return f"{_ident(unit.name)}_spec"

    def attrs(self, unit: Unit) -> str:
        return ""

    def schema(self) -> dict:
        return PROPOSAL_SCHEMA

    def modular_options(self) -> list[str]:
        # Symbolic execution stops at `callFun I P gRef`; a hypothesis about that call closes it.
        return []

    def render(self, ob: Obligation, build: Build) -> str:
        gen = build.info["gen_module"]
        # Auto: `ts_auto`; Testing: `initWorld` (the world after module initialisation) in test statements
        base = ["StrictTS.Proof.Summarize", "StrictTS.Proof.Contract", "StrictTS.Proof.Auto", "StrictTS.Testing", gen]
        if self._has_eval():
            base.insert(-1, "StrictTS.Proof.Eval")            # `ts_eval`: concrete execution of test cases
        imports = base + [i for i in ob.imports if i not in base]
        c = ob.contract
        lines = [f"import {i}" for i in imports]
        lines += ["", f"open StrictTS StrictTS.JS {build.info['gen_ns']}", "", "set_option maxHeartbeats 4000000", "",
                  f"namespace {build.ns}", ""]
        lines += [o.strip() for o in ob.proof.options if o.strip()]
        if c.attrs:
            lines.append(c.attrs)
        lines.append(f"theorem {ob.theorem} {c.binders.strip()} :")
        lines.append(f"    {c.statement.strip()} := by")
        for t in ob.proof.tactics.strip("\n").splitlines():
            lines.append("  " + t if t.strip() else "")
        lines += ["", f"#print axioms {ob.theorem}", "", f"end {build.ns}", ""]
        return "\n".join(lines)

    # -- prompt material -----------------------------------------------------------------------
    def gen_decl(self, build: Build, unit: Unit, max_chars: int = 12000) -> str:
        p = build.pkg.src(build.info["gen_module"])
        if not p.exists():
            return ""
        text = p.read_text()
        sig = unit.signature or {}
        parts = []
        for pat in (r"^def «?" + re.escape(sig.get("ref", unit.sym)) + r"»? :.*\n",
                    r"^def «?" + re.escape(sig.get("def", unit.lean_decl)) + r"»? : FunDef TT where\n(?:(?!^def |^theorem |^abbrev |^/--).*\n)*",
                    r"^theorem «?" + re.escape(sig.get("call", unit.name + "_call")) + r"»? .*\n(?:  .*\n)*"):
            m = re.search(pat, text, re.M)
            if m:
                parts.append(m.group(0))
        out = "\n".join(parts)
        if len(out) > max_chars:
            out = out[: max_chars // 2] + "\n... [truncated] ...\n" + out[-max_chars // 2:]
        return out

    def type_table(self, build: Build) -> str:
        p = build.pkg.src(build.info["gen_module"])
        if not p.exists():
            return ""
        m = re.search(r"^abbrev TT : TypeTable where\n(?:  .*\n)+", p.read_text(), re.M)
        return m.group(0) if m else ""

    def template(self, unit: Unit, build: Build) -> dict | None:
        """The standard invariant-free script with type-derived binders (tried before the LLM)."""
        sig = unit.signature or {}
        args = _split_tys(sig.get("args", ""))
        if args is None:
            return None
        binders, vals = ["(I : Impl)"], []
        hyps = []
        for i, t in enumerate(args):
            m = re.fullmatch(r"\(?\.arr (\.\w+)\)?", t)
            if m:
                binders.append(f"(a{i} : Nat) (xs{i} : Array (Val TT {m.group(1)}))")
                hyps.append(f"(hw{i} : w.heap.get? (.arr {m.group(1)}, a{i}) = some xs{i})")
                vals.append(f".arr a{i}")
            elif t in SCALARS:
                lean_ty, ctor = SCALARS[t]
                binders.append(f"(x{i} : {lean_ty})")
                vals.append(f"{ctor} x{i}")
            else:
                binders.append(f"(v{i} : Val TT {t if t.startswith('.') else '(' + t + ')'})")
                vals.append(f"v{i}")
        argv = ".nil"
        for v in reversed(vals):
            argv = f"(.cons {'(' + v + ')' if ' ' in v else v} {argv})"
        binders.append("(w : World TT)")
        ref, dname, call = sig.get("ref", unit.sym), sig.get("def", unit.lean_decl), sig.get("call", unit.name + "_call")
        return {"binders": " ".join(binders + hyps),
                "statement": f"JS.Returns (callFun I program {ref} {argv}) w",
                "tactics": f"unfold JS.Returns\nrw [{call}]\nsimp only [{dname}, ts_sym]\ntry ts_summarize\ntry ts_callbacks\nsimp [ts_sym]\nrepeat' (vo_split_ite <;> try simp [ts_sym])",
                "options": [], "strength": "noub", "needs": [], "notes": "template: invariant-free script"}

    # -- test cases (vitest `it(...)` rewritten by extract_tests.js) ---------------------------------
    def is_test_unit(self, unit: Unit, build: Build) -> bool:
        return unit.kind == "test"

    def mechanical_contract(self, unit: Unit, build: Build) -> "Contract | None":
        """The theorem of a test case, stated mechanically (no model): for every implementation choice `I`,
        the generated test function, run from the world after module initialisation, returns normally. A
        failed expectation throws (vo_expect.ts), so this says: no panic, no uncaught exception, and every
        expectation of the case holds."""
        if not self.is_test_unit(unit, build) or not unit.in_scope:
            return None
        sig = unit.signature or {}
        if _split_tys(sig.get("args", "")) != []:
            return None
        ref = sig.get("ref", unit.sym)
        return Contract(unit=unit.name, binders="(I : Impl)",
                        statement=f"JS.Returns (callFun I program «{ref}» .nil) (StrictTS.Testing.initWorld I program)",
                        origin="mechanical", strength="noub", attrs="",
                        note=f"test case, stated mechanically: {sig.get('test_title', '')} ({unit.loc})")

    def _has_eval(self) -> bool:
        return (sbuild.STRICTTS / "StrictTS" / "Proof" / "Eval.lean").exists()

    def test_template(self, unit: Unit, build: Build) -> list[dict]:
        """Concrete execution of a test case: rewrite the initial world (programs whose initialisation
        allocates nothing), then symbolic execution with every called function unfolded and decidable facts
        about literals decided, loops unrolled one iteration at a time, and the final outcome read off."""
        by = {u.name: u for u in build.units}
        seen, todo = [], [unit.name]
        while todo:
            n = todo.pop()
            if n in seen or n not in by or not by[n].in_scope:
                continue
            seen.append(n)
            todo += by[n].callees
        lemmas = ["JS.Returns", "ts_sym"]
        for n in seen:
            sig = by[n].signature or {}
            lemmas += [f"«{sig.get('call', n + '_call')}»", f"«{sig.get('def', n + 'Def')}»"]
        for h in build.info.get("test_helpers", []):
            lemmas += [f"«{h}_call»", f"«{h}Def»"]
        ls = ", ".join(lemmas)
        out = []
        if self._has_eval():
            # first: StrictTS's own concrete execution (unfolding, F64 literal evaluation, loops, sorts, callbacks)
            out.append({"binders": "", "statement": "", "tactics": "ts_eval",
                        "options": ["set_option maxRecDepth 20000 in"], "strength": "noub", "needs": [],
                        "notes": "template: concrete test execution (ts_eval)"})
        # then veriforch's scripts: the full simp set (literal arithmetic, array literals, F64 facts of
        # StrictTS.Proof.Numbers), only the execution lemmas (when the full set loops or rewrites into forms ts_sym
        # does not know), and array methods with a callback through `ts_callbacks`, interleaved with the steps
        for only, callbacks in ((False, False), (True, False), (False, True)):
            run = f"simp (config := {{ decide := true }}){' only' if only else ''} [{ls}]"
            steps = [f"(rw [evalLoop.eq_1]; {run})", f"(rw [evalForOf.eq_1]; {run})", f"(rw [evalDo.eq_1]; {run})"]
            if callbacks:
                steps.append(f"(ts_callbacks; {run})")
            tactics = "\n".join([
                "have hw : StrictTS.Testing.initWorld I program = World.init TT := by",
                "  (simp [StrictTS.Testing.initWorld, program, mainBlock, ts_sym]) <;> rfl",
                "rw [hw]",
                run,
                f"repeat (first | {' | '.join(steps)})",
                "all_goals exact ⟨_, _, rfl⟩"])
            out.append({"binders": "", "statement": "", "tactics": tactics,
                        "options": ["set_option maxRecDepth 20000 in"], "strength": "noub", "needs": [],
                        "notes": "template: concrete test execution" + (" (execution lemmas only)" if only else "")
                                 + (" (with array-callback summaries)" if callbacks else "")})
        return out

    def template_candidates(self, unit: Unit, build: Build) -> list[dict]:
        if self.is_test_unit(unit, build):
            return self.test_template(unit, build)
        t = self.template(unit, build)
        if not t:
            return []
        # StrictTS's one-call proof attempt first (unfold, summarize loops/callbacks, simp), then the script
        auto = dict(t, tactics="unfold JS.Returns\nts_auto", notes="template: ts_auto")
        return [auto, t]

    _diff_cache: dict = {}

    def equivalence_verdict(self, unit_old: Unit, unit_new: Unit, b_old: Build, b_new: Build, run_dir: Path) -> dict:
        """old ≡ new through StrictTS's own semantic diff (strictts-diff, tools/difftool in the StrictTS repo,
        used read-only): PROVED -> equivalent (Lean theorem), REFUTED -> behaviour_changed (Node-confirmed
        input), UNKNOWN -> unknown with its reason. One run per revision pair, shared by all changed units."""
        import json as _json
        import subprocess
        from ...lean import RUN1, VO_ROOT
        key = (b_old.target.root, b_new.target.root)
        if key not in self._diff_cache:
            out = run_dir / "ci" / f"strictts-diff_{b_old.target.version}..{b_new.target.version}.json"
            out.parent.mkdir(parents=True, exist_ok=True)
            src = [s for s in (b_old.variant.sources or b_old.target.sources)]
            old_p = str(Path(b_old.target.root) / src[0]) if len(src) == 1 else b_old.target.root
            new_p = str(Path(b_new.target.root) / src[0]) if len(src) == 1 else b_new.target.root
            strictts_repo = Path("/home/user/strictts")
            cmd = [str(RUN1), "-t", "1800", "-m", "128", "-c", "0.6", "--", "node",
                   str(strictts_repo / "tools/difftool/dist/cli.js"), "diff", old_p, new_p, "--json", str(out)]
            p = subprocess.run(cmd, cwd=strictts_repo, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                               timeout=1900, env=dict(__import__("os").environ, VO_ROOT=str(VO_ROOT)))
            try:
                self._diff_cache[key] = _json.loads(out.read_text())
            except (OSError, ValueError):
                self._diff_cache[key] = {"error": p.stdout[-1500:]}
        data = self._diff_cache[key]
        if isinstance(data, dict) and "error" in data:
            return {"verdict": "unknown", "detail": "strictts-diff failed: " + data["error"][:300]}
        # strictts-diff/v1 (tools/difftool/schema/strictts-diff-v1.schema.json, frozen at ~/strictts 60cbe4f)
        rows = data.get("functions", []) if isinstance(data, dict) else []
        for r in rows:
            key = r.get("key", "")
            if r.get("name") != unit_new.name and key.split("::")[-1] != unit_new.name:
                continue
            v = r.get("verdict") or "UNKNOWN"
            proof = r.get("proof") or {}
            if v == "PROVED":
                return {"verdict": "equivalent", "tool": "strictts-diff", "key": key, "proof": proof}
            if v in ("REFUTED", "REFUTED*"):
                ce = r.get("counterexample") or {}
                return {"verdict": "behaviour_changed", "tool": "strictts-diff", "key": key,
                        "witness": {"args": ce.get("call"), "old": ce.get("old"), "new": ce.get("new"),
                                    "lean_confirmed": bool(ce.get("leanConfirmed"))}}
            return {"verdict": "unknown", "tool": "strictts-diff", "key": key,
                    "detail": "; ".join(r.get("reasonCodes") or []) or r.get("reasons")}
        return {"verdict": "unknown", "detail": "function not in strictts-diff output"}

    def intended_prompt(self, unit: Unit, build: Build) -> str:
        return "\n\n".join([
            f"# Function `{unit.name}` (kind: {unit.kind}) cannot be verified yet: it is outside the StrictTS "
            f"subset or was not emitted by the translator ({unit.scope}).",
            "State the contract it is intended to satisfy, so that its callers can be verified assuming it. "
            "It will be used only as an explicit hypothesis of the callers' theorems and reported as an "
            "unverified assumption. Use the vocabulary of proved contracts: JS.NoFault / JS.Returns / an "
            "equation about `exec (callFun I program fRef args) w`, with binders for I, the arguments and w. "
            "If the function has no Lean definition (no fRef), describe the contract in `notes` and give "
            "binders/statement as the empty string.",
            "## TypeScript source", f"```ts\n{unit.source or '(not found)'}\n```",
            "Give the JSON object: binders, statement, notes."])

    def user_prompt(self, unit: Unit, build: Build, callees, history, hypotheses=()) -> str:
        from ...scheduler import truncate
        sig = unit.signature or {}
        parts = [f"# Function under verification: `{unit.name}` (kind: {unit.kind}; theorem name `{self.theorem(unit)}`)",
                 f"Lean names: reference `{sig.get('ref')}`, definition `{sig.get('def')}`, call lemma "
                 f"`{sig.get('call')}`; argument types `{sig.get('args')}`, return type `{sig.get('ret')}`.",
                 f"Target `{build.target.name}`.",
                 "## TypeScript source", f"```ts\n{unit.source or '(not found)'}\n```",
                 "## Generated IR (StrictTS)", f"```lean\n{self.gen_decl(build, unit)}\n```"]
        tt = self.type_table(build)
        if tt:
            parts += ["## Type table of the program", f"```lean\n{tt}\n```"]
        if self.is_test_unit(unit, build):
            t = self.test_template(unit, build)[0]
            parts += ["## Standard script for test cases (concrete execution; try or adapt it)",
                      f"```lean\n{t['tactics']}\n```"]
        else:
            t = self.template(unit, build)
            if t:
                parts += ["## Standard script for this signature (try or adapt it)",
                          "```json\n" + json.dumps({k: t[k] for k in ("binders", "statement", "tactics")}, indent=1)
                          + "\n```"]
        if callees:
            parts.append("## Contracts of its callees (proved, imported; use them by name)")
            for ob, _ in callees:
                parts.append(f"```lean\ntheorem {ob.theorem} {ob.contract.binders} :\n    {ob.contract.statement}\n```")
        elif not hypotheses:
            parts.append("The function calls no other user function.")
        if hypotheses:
            parts.append("## Assumed contracts (unverified callees), in scope as hypotheses of your theorem")
            parts.append("The orchestrator puts these binders in front of your binders. Do not repeat them.")
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
        guide = (HERE / "prompt_pack.md").read_text()
        ex = []
        for rel in EXAMPLES:
            p = sbuild.STRICTTS / rel
            if p.exists():
                ex.append(f"## {rel}\n```lean\n{p.read_text()}\n```")
        return guide + "\n\n# Worked examples (all check)\n\n" + "\n\n".join(ex)


SCALARS = {".num": ("F64", ".num"), ".str": ("JSStr", ".str"), ".bool": ("Bool", ".bool")}

PROPOSAL_SCHEMA = {
    "type": "object",
    "properties": {
        "binders": {"type": "string", "description": "Lean binders and hypotheses"},
        "statement": {"type": "string", "description": "The conclusion, e.g. JS.NoFault (callFun I program fRef args) w"},
        "tactics": {"type": "string", "description": "Proof script, one tactic per line, without `by`"},
        "options": {"type": "array", "items": {"type": "string"}},
        "strength": {"type": "string", "enum": ["noub", "functional"]},
        "needs": {"type": "array", "items": {"type": "string"}},
        "notes": {"type": "string"},
    },
    "required": ["binders", "statement", "tactics", "options", "strength", "needs", "notes"],
    "additionalProperties": False,
}


def _split_tys(s: str) -> list[str] | None:
    """`tys[(.arr .num), .num]` -> ['(.arr .num)', '.num'] (top-level commas only)."""
    m = re.fullmatch(r"\s*tys\[(.*)\]\s*", s or "")
    if not m:
        return None
    inner, out, depth, cur = m.group(1), [], 0, ""
    for ch in inner:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def _ident(s: str) -> str:
    out = "".join(c if c.isalnum() or c == "_" else "_" for c in s)
    return out if out[:1].isalpha() else "u" + out

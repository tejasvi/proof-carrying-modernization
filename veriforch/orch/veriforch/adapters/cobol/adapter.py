"""COBOL adapter over coblean: rendering program-contract modules and the bridge's prompt pack."""
from __future__ import annotations

import json
import re
from pathlib import Path

from ...model import Contract, Obligation, ProofScript, Target, Unit, Variant
from ..base import Adapter, Build
from . import build as cbuild

HERE = Path(__file__).parent
EXAMPLES = ["Cobol/Spec.lean", "Examples/AcctInt.lean", "Examples/Binary.lean", "Examples/RecSum.lean",
            "Examples/Cbact02c.lean"]

PROPOSAL_SCHEMA = {
    "type": "object",
    "properties": {
        "binders": {"type": "string", "description": "Lean binders and hypotheses"},
        "statement": {"type": "string", "description": "The conclusion about the program run"},
        "tactics": {"type": "string", "description": "Proof script, one tactic per line, without `by`"},
        "options": {"type": "array", "items": {"type": "string"}},
        "strength": {"type": "string", "enum": ["noub", "functional"]},
        "needs": {"type": "array", "items": {"type": "string"}},
        "notes": {"type": "string"},
    },
    "required": ["binders", "statement", "tactics", "options", "strength", "needs", "notes"],
    "additionalProperties": False,
}


class CobolAdapter(Adapter):
    lang = "cobol"
    pin = cbuild.COBLEAN_PIN

    def build(self, target: Target, variant: Variant, run_dir: Path) -> Build:
        return cbuild.build(target, variant, run_dir)

    # -- names ---------------------------------------------------------------------------------
    def module(self, build: Build, unit: Unit) -> str:
        return f"{build.ns}.{_ident(unit.name)}"

    def theorem(self, unit: Unit) -> str:
        return f"{_ident(unit.name)}_ends"

    def attrs(self, unit: Unit) -> str:
        return ""

    def schema(self) -> dict:
        return PROPOSAL_SCHEMA

    def modular_options(self) -> list[str]:
        # coblean has no inlining switch: a CALLed program is an `Env.call` entry, so a caller's proof is
        # modular by construction once the hypothesis about `env.call` is in scope.
        return []

    def placeholder_tactic(self) -> str:
        return "skip"

    # -- executable semantics (cobolrun evaluates the same Lean definitions) --------------------------
    def candidate_instructions(self, unit: Unit, build: Build) -> str:
        p = self._prog(build, unit)
        return ("Each candidate is {\"args\": {\"mem\": HEX, \"inputs\": [[fileId, [[byte, ...], ...]], ...], "
                "\"fuel\": N}, \"convention\": bool, \"why\": str}: `mem` is the whole initial storage as "
                "hex (2 digits per byte, length = the program's memSize), with the input fields encoded in "
                "their PICTURE/USAGE format (EBCDIC zoned digits F0-F9 with the sign in the last zone nibble "
                "C/D, COMP-3 packed with sign nibble C/D, COMP/COMP-5 big-endian two's complement unless the "
                "config says otherwise); `inputs` gives the records of input files. Program files: "
                + json.dumps(p["files"]))

    def run_semantic(self, unit: Unit, build: Build, args) -> "ReplayResult":
        from ...model import ReplayResult
        from ..cir.build import run_tool
        p = self._prog(build, unit)
        gdir = Path(build.info["gen_dir"])
        cmd = [str(cbuild.COBLEAN / ".lake/build/bin/cobolrun"), p["json"], "--fuel", str(args.get("fuel", 10000))]
        if args.get("mem"):
            cmd += ["--mem", str(args["mem"])]
        if args.get("inputs"):
            ip = build.dir / "cex_inputs.json"
            ip.write_text(json.dumps(args["inputs"]))
            cmd += ["--inputs", str(ip)]
        r = run_tool(cmd, gdir, timeout=60, core_h=0.05)
        line = next((l for l in reversed(r.stdout.splitlines()) if l.startswith("{")), "")
        try:
            sig = json.loads(line).get("signal", "")
        except ValueError:
            return ReplayResult("semantic", "error", r.stdout[-400:])
        if sig.startswith("stop"):
            return ReplayResult("semantic", "ok", sig)
        if sig.startswith("fault"):
            return ReplayResult("semantic", "ub", sig, True)
        return ReplayResult("semantic", "timeout" if "Fuel" in sig else "error", sig)

    # -- rendering -----------------------------------------------------------------------------
    def render(self, ob: Obligation, build: Build) -> str:
        gen = build.info["gen_module"]
        imports = ["Cobol", gen] + [i for i in ob.imports if i not in ("Cobol", gen)]
        c = ob.contract
        lines = [f"import {i}" for i in imports]
        lines += ["", f"open Cobol {build.info['gen_ns']}", "", "set_option maxHeartbeats 4000000", "",
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

    # -- prompt context ------------------------------------------------------------------------
    def _prog(self, build: Build, unit: Unit) -> dict:
        return next(p for p in build.info["programs"] if p["name"] == unit.name)

    def records(self, build: Build) -> str:
        """Data division of every program, with the Lean field descriptors `P.NAME` that exist."""
        out = []
        for p in build.info["programs"]:
            pid = cbuild.prog_ident(p["name"])
            uniq = cbuild.unique_names(p["data"])
            out.append(f"-- program {p['name']}: Lean constant `{pid}`; field descriptors `{pid}.NAME` "
                       f"(and `{pid}.NAME.fmt` for numeric items) exist for: "
                       + ", ".join(sorted(n.replace('-', '_') for n in uniq))[:3000])
            out.append("\n".join(cbuild.data_table(p["data"]))[:6000])
            if p["files"]:
                out.append("-- files: " + json.dumps(p["files"]))
        return "\n".join(out)

    def program_text(self, build: Build, unit: Unit, max_chars: int = 14000) -> str:
        p = self._prog(build, unit)
        d = json.loads((Path(build.info["gen_dir"]) / p["json"]).read_text())
        paras = []
        for para in d.get("paras", []):
            paras.append(f"{para.get('name') or '(unnamed)'}" + (f" [section {para['sect']}]" if para.get("sect") else ""))
            for s in para.get("sentences", []):
                paras.append("    " + json.dumps(s, separators=(",", ":")))
        text = "\n".join(paras)
        if len(text) > max_chars:
            text = text[: max_chars * 2 // 3] + "\n... [truncated] ...\n" + text[-max_chars // 3 :]
        return text

    def user_prompt(self, unit: Unit, build: Build, callees, history, hypotheses=()) -> str:
        from ...scheduler import truncate
        pid = cbuild.prog_ident(unit.name)
        p = self._prog(build, unit)
        parts = [f"# Program under verification: `{unit.name}` (Lean constant `{pid}`, theorem name "
                 f"`{self.theorem(unit)}`)",
                 f"Target `{build.target.name}`, build variant `{build.variant.name}` "
                 f"(compiler options: {' '.join(build.variant.flags) or 'as in the IR config'}).",
                 "Goal: normal termination for every valid input: for all initial storage whose input "
                 "fields hold valid data (and, if the program reads files, for all input files of "
                 "records of the right length), the run ends with `.stop _` (no abend, no undefined "
                 "behaviour, no unsupported construct), given enough fuel. State the fuel as a function of "
                 "the input size. Use `Program.EndsNormally` or the equivalent `(P.run env fuel st).1 = "
                 ".stop k` form; a stronger functional postcondition is welcome if the proof stays easy.",
                 "## COBOL source" if unit.source else "## COBOL source not available",
                 f"```cobol\n{unit.source}\n```" if unit.source else "",
                 "## Data division (from the IR) and Lean field descriptors",
                 f"```\n{self.records_of(build, unit)}\n```",
                 "## Procedure division (surface IR, one JSON statement list per sentence)",
                 f"```\n{self.program_text(build, unit)}\n```"]
        if callees:
            parts.append("## Contracts of CALLed programs (proved)")
            for ob, _ in callees:
                parts.append(f"```lean\ntheorem {ob.theorem} {ob.contract.binders} :\n    {ob.contract.statement}\n```")
        if hypotheses:
            parts.append("## Assumed contracts of CALLed programs that are not verified (hypotheses in scope)")
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
        return "\n\n".join(x for x in parts if x)

    def records_of(self, build: Build, unit: Unit) -> str:
        p = self._prog(build, unit)
        pid = cbuild.prog_ident(p["name"])
        uniq = sorted(n.replace("-", "_") for n in cbuild.unique_names(p["data"]))
        head = (f"Lean field descriptors (reducible): {', '.join(f'{pid}.{n}' for n in uniq)}"[:4000])
        files = ("\nFiles: " + json.dumps(p["files"])) if p["files"] else ""
        return head + "\n" + "\n".join(cbuild.data_table(p["data"]))[:8000] + files

    def intended_prompt(self, unit: Unit, build: Build) -> str:
        return "\n\n".join([
            f"# Program `{unit.name}` cannot be verified yet: the model does not cover a construct it uses "
            f"({unit.scope}).",
            "State the contract it is intended to satisfy (as a CALLed program: a statement about "
            "`env.call` results, or about its own run), so that callers can be verified assuming it. It is "
            "used only as an explicit hypothesis of the callers' theorems.",
            "## COBOL source", f"```cobol\n{unit.source}\n```" if unit.source else "(not available)",
            "## Data division", f"```\n{self.records_of(build, unit)}\n```",
            "Give the JSON object: binders, statement, notes."])

    def prompt_pack(self) -> str:
        guide = (HERE / "prompt_pack.md").read_text()
        ex = []
        for rel in EXAMPLES:
            p = cbuild.COBLEAN / rel
            if p.exists():
                ex.append(f"## {rel}\n```lean\n{p.read_text()}\n```")
        return guide + "\n\n# Worked examples (all check)\n\n" + "\n\n".join(ex)


def _ident(s: str) -> str:
    out = re.sub(r"\W", "_", s)
    return out if out[:1].isalpha() else "u" + out

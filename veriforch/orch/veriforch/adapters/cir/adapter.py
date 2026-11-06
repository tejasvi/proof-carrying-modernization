"""C/C++ adapter over cirlean: rendering contract modules and the bridge's prompt pack."""
from __future__ import annotations

import json
import re
import threading
from pathlib import Path

from ...model import Contract, Obligation, ProofScript, Target, Unit, Variant
from ..base import Adapter, Build
from . import build as cbuild

HERE = Path(__file__).parent
EXAMPLES = ["Examples/Calls.lean", "Examples/Basics.lean", "Examples/Vectors.lean", "Examples/Classes.lean",
            "Examples/Carray.lean", "Examples/Cstruct.lean"]


class CirAdapter(Adapter):
    lang = "cir"
    pin = cbuild.CIRLEAN_PIN

    def build(self, target: Target, variant: Variant, run_dir: Path) -> Build:
        return cbuild.build(target, variant, run_dir)

    def module(self, build: Build, unit: Unit) -> str:
        return f"{build.ns}.{_ident(unit.name)}"

    def theorem(self, unit: Unit) -> str:
        return f"{_ident(unit.name)}_spec"

    def given_proof_text(self, build: Build, spec: dict, require_gen: bool = True) -> str:
        """A bridge owner's proof file for this build: its import of the generated module it was written against
        (and that module's name in `open` lines) become this build's (`gen_prefix`, default "Gen."). Nothing else
        changes."""
        from pathlib import Path
        text = Path(spec["proof_file"]).read_text()
        pre = spec.get("gen_prefix", "Gen.")
        gen, ns = build.info["gen_module"], build.info["gen_ns"]
        out, swapped = [], False
        for ln in text.splitlines():
            if ln.startswith("import ") and ln.split()[1].startswith(pre):
                out.append(f"import {gen}")
                swapped = True
            elif ln.startswith("open ") and pre in ln:
                out.append(" ".join(ns if w.startswith(pre) else w for w in ln.split()))
            else:
                out.append(ln)
        if not swapped and require_gen:      # a bundle's tactic modules need not import the generated module
            raise ValueError(f"no `import {pre}...` line to point at this build's generated module")
        return "\n".join(out) + "\n"

    def render(self, ob: Obligation, build: Build) -> str:
        gen = build.info["gen_module"]
        if any(i.startswith(gen + ".F.") for i in ob.imports):
            imports = ["CIR"] + ob.imports          # a modular proof: its own function's module only
        else:
            imports = ["CIR", gen] + [i for i in ob.imports if i not in ("CIR", gen)]
        c = ob.contract
        lines = [f"import {i}" for i in imports]
        lines += ["", f"open CIR {build.info['gen_ns']}", "", "set_option maxHeartbeats 4000000", "",
                  f"namespace {build.ns}", ""]
        # the model sometimes answers options as nested lists (D1 zlib order 99 crashed here): flatten, strings only
        lines += [o.strip() for x in ob.proof.options for o in (x if isinstance(x, list) else [x])
                  if isinstance(o, str) and o.strip()]
        if c.attrs:
            lines.append(c.attrs)
        lines.append(f"theorem {ob.theorem} {c.binders.strip()} :")
        lines.append(f"    {c.statement.strip()} := by")
        for t in ob.proof.tactics.strip("\n").splitlines():
            lines.append("  " + t if t.strip() else "")
        lines += ["", f"#print axioms {ob.theorem}", "", f"end {build.ns}", ""]
        return "\n".join(lines)

    def gen_decl(self, build: Build, unit: Unit, max_chars: int = 12000) -> str:
        """The unit's FuncDecl text from the Gen module (helper `abbrev ..._ops` defs included)."""
        fm = (build.info.get("modular") or {}).get(unit.sym)
        text = build.pkg.src(fm or build.info["gen_module"]).read_text()
        parts = []
        for m in re.finditer(r"^(abbrev|def) (" + re.escape(unit.lean_decl) + r"(_ops\d+)?) .*?(?=^\S)", text, re.M | re.S):
            parts.append(m.group(0))
        out = "\n".join(parts)
        if len(out) > max_chars:
            out = out[: max_chars // 2] + "\n... [truncated] ...\n" + out[-max_chars // 2 :]
        return out

    def records(self, build: Build) -> str:
        text = build.pkg.src(build.info.get("types_module") or build.info["gen_module"]).read_text()
        return "\n".join(m.group(0) for m in re.finditer(r"^def rec_\w+ : RecordDecl where\n(?:  .*\n)+", text, re.M))

    def attrs(self, unit: Unit) -> str:
        return "@[cir_spec]"

    def schema(self) -> dict:
        return PROPOSAL_SCHEMA

    def candidate_instructions(self, unit: Unit, build: Build) -> str:
        return ("Each candidate is {\"args\": [...], \"convention\": bool, \"why\": str}. `args` lists one "
                "command-line token per C parameter for the cirlean interpreter: an integer or bool parameter is "
                "a decimal integer (\"5\"); a pointer to an integer is \"&5\"; a pointer to the first element "
                "of an integer or char array is \"&[1,2,3]\" (chars as their integer codes, include a 0 "
                "terminator if the code expects one); a pointer to a struct whose members are integers is "
                "\"{1,2,3}\" (members in declaration order). Parameters of other shapes cannot be given: "
                "skip candidates that need them.")

    def run_semantic(self, unit: Unit, build: Build, args) -> "ReplayResult":
        """Run the unit on cirlean's semantics with concrete arguments (cirrun's argument syntax). A linked build
        runs in the linked program (all its translation units, `vo-cirrun`), so calls into other units resolve."""
        from ...model import ReplayResult
        if build.info.get("linked") and build.info.get("cirs"):
            cmd = [str(cbuild.vo_cirrun()), *build.info["cirs"], "--", unit.sym]
        else:
            cmd = [str(cbuild.CIRRUN), build.info["cir"], unit.sym]
        p = cbuild.run_tool(cmd + [str(a) for a in args], build.dir, timeout=60, core_h=0.05)
        out = p.stdout.strip().splitlines()
        last = out[-1] if out else ""
        if p.returncode == 124:
            return ReplayResult("semantic", "timeout", "no result within 60 s (possible non-termination)")
        if "UB:" in p.stdout:
            line = next(l for l in out if "UB:" in l)
            return ReplayResult("semantic", "ub", line.split("UB:", 1)[1].strip(), True)
        if p.returncode != 0:
            return ReplayResult("semantic", "error", p.stdout[-400:])
        return ReplayResult("semantic", "ok", last)

    _TEST_NAME = re.compile(r"^(test|tests|test_\w+|\w+_test|TEST_\w+)$", re.I)

    def modular_module(self, unit: Unit, build: Build) -> str | None:
        """The unit's own function module when proofs are modular (target `modular = true`), else None. A linked
        build has the per-function layout too, but proves over the concrete program unless modular is asked for."""
        if not build.info.get("modular_proofs"):
            return None
        return (build.info.get("modular") or {}).get(unit.sym)

    def modular_libs(self, unit: Unit, build: Build) -> list[str]:
        """Library functions (declared without a body, or with a cirlean model) that a modular unit calls: the
        context must contain them too, so each gets a lookup hypothesis and its module is imported."""
        libs = set(build.info.get("modular_lib") or [])
        ext = (unit.signature or {}).get("externals", []) if isinstance(unit.signature, dict) else []
        return [s for s in dict.fromkeys(ext) if s in libs]

    def modular_prefix(self, unit: Unit, build: Build) -> str:
        """Binders of a modular theorem: any context that contains the function (cirlean Examples/Modular*)
        and the library functions it calls."""
        decl = build.info.get("modular_decl") or {}
        libs = "".join(f' (hf_{_ident(s)} : ctx.mod.findFunc? "{s}" = some {decl[s]})'
                       for s in self.modular_libs(unit, build))
        return f'(ctx : Ctx) (hf : ctx.mod.findFunc? "{unit.sym}" = some {unit.lean_decl}){libs}'

    def modular_group_parts(self, units: list[Unit], build: Build, ext: list[str], hcon: dict,
                            syms: dict[str, str]) -> tuple[str, list[str], int]:
        """Binders, imports and number of lookup facts of a cycle stated over any context containing it: a lookup
        fact for every member and every library function the members call, then the contracts of the callees
        outside the cycle as hypotheses (callee symbols as literals)."""
        from ...scheduler import hyp_binder
        decl = build.info.get("modular_decl") or {}
        libs = list(dict.fromkeys(s for u in units for s in self.modular_libs(u, build)))
        look = [f'(hf_{_ident(u.sym)} : ctx.mod.findFunc? "{u.sym}" = some {u.lean_decl})' for u in units]
        look += [f'(hf_{_ident(s)} : ctx.mod.findFunc? "{s}" = some {decl[s]})' for s in libs]
        hyps = [self.modular_hyp_text(hyp_binder(c, hcon[c]), syms) for c in ext]
        types = build.info.get("types_module")
        imports = ([build.info["modular"][u.sym] for u in units] + [build.info["modular"][s] for s in libs]
                   + ([types] if types else []))
        return " ".join(["(ctx : Ctx)"] + look + hyps), imports, len(look)

    def modular_hyp_text(self, text: str, syms: dict[str, str]) -> str:
        """A callee contract as a hypothesis of a modular proof: the callee's module is not imported, so its
        `fn_g.sym` becomes the symbol literal."""
        return re.sub(r"(?<![\w.])(fn_\w+)\.sym\b", lambda m: f'"{syms[m.group(1)]}"' if m.group(1) in syms
                      else m.group(0), text)

    def assemble(self, build: Build, order: list[str], proved: dict, own: dict, hyp_order: dict,
                 modular_units: set, status: dict, log=print, n_lookups: dict | None = None) -> dict:
        """Instantiate the modular proofs with the concrete module (cirlean Examples/Modular.lean): for each
        modular unit, in bottom-up order, `<unit>_in_module : ∀ <binders>, <statement>` is its proof applied to the
        module's `ctx`, `cir_lookup` for the lookup fact, and each callee's own theorem for the callee hypothesis.
        One module, checked once; returns {unit: {ok, theorem | error}}."""
        gen = build.info["gen_module"]
        by = {u.name: u for u in build.units}
        ns = f"{build.ns}.Assembly"
        avail: dict[str, str] = {}               # unit -> a theorem of its own contract over the concrete module
        for n in order:
            if n in proved and n not in modular_units and status.get(n) == "proved":
                avail[n] = f"{build.ns}.{self.theorem(by[n])}"      # whole-module proof without hypotheses
        thms, lines_of, imports = [], {}, set()
        for n in order:
            if n not in modular_units or n not in proved:
                continue
            args = []
            for c in hyp_order.get(n, []):
                if c not in avail:
                    break
                args.append(avail[c])
            else:
                c = own[n]
                b = c.binders.strip()
                ty = f"∀ {b}, {c.statement.strip()}" if b else c.statement.strip()
                tn = f"{_ident(n)}_in_module"
                k = (n_lookups or {}).get(n) or (1 + len(self.modular_libs(by[n], build)))
                lookups = " (by cir_lookup)" * k
                thms.append((n, tn, [f"theorem {tn} : {ty} :=",
                                     f"  {build.ns}.{self.theorem(by[n])} ctx{lookups}"
                                     + "".join(f" {a}" for a in args), ""]))
                imports.add(proved[n][0].module)
                imports |= {proved[c][0].module for c in hyp_order.get(n, []) if c in proved}
                avail[n] = tn
        if not thms:
            return {}
        head = ["import CIR", f"import {gen}"] + [f"import {m}" for m in sorted(imports)] + [
            "", f"open CIR {build.info['gen_ns']}", "", "set_option maxHeartbeats 4000000", "", f"namespace {ns}", ""]
        body, start = [], len(head) + 1
        for n, tn, ls in thms:
            lines_of[n] = (start + len(body), start + len(body) + len(ls) - 1)
            body += ls
        tail = [f"#print axioms {tn}" for _, tn, _ in thms] + ["", f"end {ns}", ""]
        src = "\n".join(head + body + tail)
        ikeys = {gen: build.gen_modules[gen], **{proved[n][0].module: proved[n][1] for n in proved
                                                 if proved[n][0].module in imports}}
        res = build.pkg.check(ns, src, ikeys, timeout=900)
        std = {"propext", "Classical.choice", "Quot.sound"}
        out = {}
        for n, tn, _ in thms:
            lo, hi = lines_of[n]
            errs = [m.text for m in res.messages if m.severity == "error" and lo <= m.line <= hi]
            ax = None
            for m in res.messages:
                mm = re.search(r"'([^']+)' depends on axioms: \[(.*)\]", m.text, re.S)
                if mm and mm.group(1).endswith("." + tn):
                    ax = [a.strip() for a in mm.group(2).split(",") if a.strip()]
            if not errs and ax is not None and set(ax) <= std and res.status != "timeout":
                out[n] = {"ok": True, "theorem": f"{ns}.{tn}", "axioms": ax}
            else:
                out[n] = {"ok": False, "error": (errs[0] if errs else f"status {res.status}, axioms {ax}")[:500]}
        log(f"  assembly: {sum(r['ok'] for r in out.values())}/{len(out)} modular proofs instantiated ({ns})")
        return out

    def is_test_unit(self, unit: Unit, build: Build) -> bool:
        dem = (unit.signature or {}).get("demangled") if isinstance(unit.signature, dict) else ""
        base = (dem or unit.name).split("(")[0].split("::")[-1]
        in_test_file = any(unit.loc.startswith(str(Path(build.target.root) / t)) for t in build.target.tests)
        # a function in a listed test file is a test unit; its `main` too (a test program: exit code 0 = pass)
        return bool(self._TEST_NAME.match(base)) or in_test_file or base == "LLVMFuzzerTestOneInput"

    _ENTRY_LEAN = cbuild.VO_ROOT / "VerifOrch" / "Cir" / "Entry.lean"
    _TESTEVAL_LEAN = cbuild.VO_ROOT / "VerifOrch" / "Cir" / "TestEval.lean"

    def mechanical_defs(self, contract) -> str:
        """The calling-convention definitions an entry point's fixed statement names (InitExt, ReadableBuf, ...),
        so the model can unfold them: VerifOrch/Cir/Entry.lean without its header comment."""
        if "VerifOrch.Cir.Entry" not in (contract.imports or []):
            return ""
        text = self._ENTRY_LEAN.read_text()
        return text[text.find("namespace VerifOrch.Cir"):] if "namespace VerifOrch.Cir" in text else text

    def support_modules(self, build: Build) -> dict[str, str]:
        """Check veriforch's own Lean definitions into the build's package: the entry-point calling conventions
        (VerifOrch/Cir/Entry.lean) and, when the pinned cirlean evaluates calls (`callReturnsK`), the
        "returns normally" test lemmas (VerifOrch/Cir/TestEval.lean). Returns module -> cache key."""
        mods = [("VerifOrch.Cir.Entry", self._ENTRY_LEAN)]
        if self._has_tactic("cir_kernel"):
            mods.append(("VerifOrch.Cir.TestEval", self._TESTEVAL_LEAN))
        keys = {}
        # build variants verified concurrently share the package: one check of these modules at a time
        with _SUPPORT_LOCK:
            for mod, path in mods:
                res = build.pkg.check(mod, path.read_text(), timeout=600)
                if not res.ok:
                    raise RuntimeError(f"{mod} does not check: {res.errors[:3]}")
                keys[mod] = res.cache_key
        return keys

    def _entry_contract(self, unit: Unit, params: list[str]) -> "Contract | None":
        """Test entry points that take arbitrary input, quantified over every input their C calling convention
        allows, in any memory extending the module's initial memory: `int main(int argc, char **argv)` and
        `int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size)`. The claim is no undefined behaviour (a
        failing assert is undefined behaviour); the exit code is not constrained (such programs report a
        non-match or a usage error with a non-zero code)."""
        from ...model import Contract
        base = unit.name.split("(")[0]
        pre = "(m : Mem) (hm : VerifOrch.Cir.InitExt module m)"
        if base == "main" and len(params) == 2 and re.fullmatch(r"\(\.int true 32\)", params[0]) \
                and re.fullmatch(r"\(\.ptr \(\.ptr \(\.int (true|false) 8\)\)\)", params[1]):
            binders = (f"(argc : Int) (argv : Ptr) {pre} (hargc : -2147483648 ≤ argc ∧ argc ≤ 2147483647) "
                       "(hargs : VerifOrch.Cir.MainArgs module.initMem.next m argc argv)")
            args = "[.int argc, .ptr argv]"
        elif base == "LLVMFuzzerTestOneInput" and len(params) == 2 \
                and re.fullmatch(r"\(\.ptr \(\.int (true|false) 8\)\)", params[0]) \
                and re.fullmatch(r"\(\.int false 64\)", params[1]):
            binders = (f"(data : Ptr) (size : Int) {pre} (hsize : 0 ≤ size ∧ size ≤ 18446744073709551615) "
                       "(hbuf : VerifOrch.Cir.ReadableBuf module.initMem.next m data size)")
            args = "[.ptr data, .int size]"
        else:
            return None
        return Contract(unit=unit.name, binders=binders,
                        statement=f"Returns ctx {unit.lean_decl}.sym {args} m (fun _ _ => True)",
                        origin="mechanical", strength="inputs", attrs="", imports=["VerifOrch.Cir.Entry"],
                        note="test entry point over every input its calling convention allows, stated mechanically")

    def mechanical_contract(self, unit: Unit, build: Build) -> "Contract | None":
        """The theorem of a test unit, stated mechanically (no model): the test function as written, run from
        the module's initial memory, terminates without undefined behaviour (every assert holds) and, for
        int-returning tests under the target's `test_pass = "zero"` convention, returns 0. Tests with
        parameters are quantified over their integer arguments within the C types' ranges."""
        from ...model import Contract
        if not self.is_test_unit(unit, build):
            return None
        decl = self.gen_decl(build, unit, max_chars=10**9)
        mp = re.search(r"params := \[(.*?)\]\n", decl)
        mr = re.search(r"\n  ret := (.*?)\n", decl)
        if mp is None or mr is None:
            return None
        params = [x.strip() for x in re.split(r",\s*(?=\()", mp.group(1).strip())] if mp.group(1).strip() else []
        entry = self._entry_contract(unit, params)
        if entry is not None:
            return entry
        binders, args = [], []
        for i, ty in enumerate(params):
            mi = re.fullmatch(r"\(\.int (true|false) (\d+)\)", ty)
            if not mi:
                return None                      # other pointer/record parameters: no calling convention yet
            signed, w = mi.group(1) == "true", int(mi.group(2))
            lo, hi = (-(2 ** (w - 1)), 2 ** (w - 1) - 1) if signed else (0, 2 ** w - 1)
            binders.append(f"(x{i} : Int) (hx{i} : {lo} ≤ x{i} ∧ x{i} ≤ {hi})")
            args.append(f".int x{i}")
        ret = mr.group(1).strip()
        zero = build.target.extra.get("test_pass") == "zero" and ret.startswith("(.int")
        post = "(fun r _ => r = some (.int 0))" if zero else "(fun _ _ => True)"
        # a test whose compiled body makes no call (its checks compiled out under these flags, e.g. jsmn's
        # strict-only tests in the default program) proves nothing about the code under test: strength "trivial"
        trivial = ".call " not in decl
        return Contract(unit=unit.name, binders=" ".join(binders),
                        statement=f"Returns ctx {unit.lean_decl}.sym [{', '.join(args)}] module.initMem {post}",
                        origin="mechanical", strength="trivial" if trivial else "noub", attrs="",
                        imports=["VerifOrch.Cir.TestEval"] if self._has_tactic("cir_kernel") else [],
                        note="test unit, stated mechanically" + ("; trivial: its compiled body makes no call"
                                                                 if trivial else ""))

    def template_candidates(self, unit: Unit, build: Build) -> list[dict]:
        """Free proofs from the bridge's own invariant inference (cirlean's cirinv: traces + Houdini), for
        functions with loops; no LLM call. Cached per (pin, body hash). Opt-in: VO_CIRINV=1 (1-8 min per function)."""
        import os
        tool = cbuild.CIRLEAN / "tools" / "cirinv_v5.py"
        mc = self.mechanical_contract(unit, build) if self.is_test_unit(unit, build) else None
        # concrete execution only for a run from the module's initial memory (not for entry points over inputs)
        if mc is not None and "module.initMem (fun" in mc.statement and self._has_tactic("cir_eval") \
                and self._has_tactic("cir_init_mem"):
            # concrete test: evaluation alone (cirlean's cir_eval unrolls loops whose condition is a literal)
            # no heartbeat limit (a run over a string takes millions); the scheduler's check_timeout bounds it.
            # Kernel-checked evaluation first; then cirlean's `cir_native` (native_decide on a Boolean test of the
            # run, sound by `returns_of_callReturnsB`), which also trusts Lean's compiler and is reported so.
            out = [{"binders": "", "statement": "", "tactics": "cir_start\ncir_init_mem\ncir_eval",
                    "options": ["set_option maxHeartbeats 0 in"], "strength": mc.strength, "needs": [],
                    "notes": "template: concrete execution"}]
            void = mc.statement.endswith("module.initMem (fun _ _ => True)")
            if self._has_tactic("cir_kernel") and void and "VerifOrch.Cir.TestEval" in mc.imports:
                # "returns normally" (void tests): the same kernel evaluation through veriforch's lemma
                out = [{"binders": "", "statement": "", "options": ["set_option maxHeartbeats 0 in"],
                        "tactics": "exact VerifOrch.Cir.returns_true_of_callReturnsK (n := 1000000000) (by decide +kernel)",
                        "strength": mc.strength, "needs": [], "notes": "template: kernel evaluation"}]
            if self._has_tactic("cir_kernel") and "fun r _ => r = some (.int" in mc.statement:
                # cirlean's kernel evaluation of the interpreter's fixpoint approximations (`decide +kernel`):
                # standard axioms only, and much faster than symbolic execution of a concrete run
                # (it covers what symbolic execution of the concrete run would prove, so that one is dropped)
                out = [{"binders": "", "statement": "", "tactics": "cir_kernel",
                        "options": ["set_option maxHeartbeats 0 in"], "strength": mc.strength, "needs": [],
                        "notes": "template: kernel evaluation"}]
            import os
            mode = os.environ.get("VO_NATIVE_TESTS") or build.target.extra.get("native_tests", "fallback")
            native_tac = ("cir_native" if "fun r _ => r = some (.int" in mc.statement else
                          "exact VerifOrch.Cir.returns_true_of_callReturnsB (by native_decide)"
                          if void and "VerifOrch.Cir.TestEval" in mc.imports else None)
            if self._has_tactic("cir_native") and native_tac and mode != "off":
                nat = {"binders": "", "statement": "", "tactics": native_tac, "options": [],
                       "strength": mc.strength, "needs": [], "native": True,
                       "notes": "template: native evaluation (native_decide)"}
                out = [nat] + out if mode == "first" else out + [nat]
            return out
        if os.environ.get("VO_CIRINV", "0") != "1" or not tool.exists():
            return []
        if not re.search(r"\.(forOp|whileOp|doWhileOp)\b", self.gen_decl(build, unit, max_chars=10**9)):
            return []
        cache = build.dir.parents[1] / "cache" / "cirinv" / f"{self.pin}_{unit.body_hash}.json"
        if cache.exists():
            props = json.loads(cache.read_text())
            return props
        out = build.dir / "cirinv" / unit.body_hash
        out.mkdir(parents=True, exist_ok=True)
        env_core = os.environ.get("VO_CIRINV_CORE", "101")
        cmd = ["env", f"CIRLEAN={cbuild.CIRLEAN}", f"CIRINV_CORE={env_core}", str(cbuild.VO_ROOT / ".venv/bin/python"),
               "-I", str(tool), "--cir", build.info["cir"], "--sym", unit.sym, "--out", str(out),
               "--json", str(out / "cand.json")]
        p = cbuild.run_tool(cmd, build.dir, timeout=int(os.environ.get("VO_CIRINV_TIMEOUT", "480")), core_h=0.2)
        props: list[dict] = []
        try:
            d = json.loads((out / "cand.json").read_text())
        except (OSError, ValueError):
            d = {}
        if d.get("status") in ("proved", "proved_under") and d.get("proof") and Path(d["proof"]).exists():
            m = re.search(r"^theorem \w+ (?P<sig>.*?) :\n    (?P<stmt>Returns .*?) := by\n(?P<tac>(?:  .*\n?)*)",
                          Path(d["proof"]).read_text(), re.M | re.S)
            if m:
                pre = list(d.get("precondition") or [])
                props.append({"binders": m.group("sig"), "statement": m.group("stmt"),
                              "tactics": "\n".join(l[2:] for l in m.group("tac").splitlines()),
                              "options": [], "strength": "noub",
                              "needs": [f"precondition inferred by cirinv: {f}" for f in pre]
                                       if d["status"] == "proved_under" else [],
                              "notes": f"cirinv {d['status']}" + (f"; UB outside it: {d.get('ub_inputs')}"
                                                                  if d.get("ub_inputs") else "")})
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_text(json.dumps(props))
        return props

    def equivalence_verdict(self, unit_old: Unit, unit_new: Unit, b_old: Build, b_new: Build, run_dir: Path,
                            llm=None) -> dict:
        from .equiv import verdict
        return verdict(self, unit_old, unit_new, b_old, b_new, run_dir, llm=llm)

    def _has_tactic(self, name: str) -> bool:
        """Whether the pinned cirlean defines a tactic (grep of its tactic sources, cached)."""
        cache = getattr(self, "_tactics", None)
        if cache is None:
            cache = self._tactics = {}
        if name not in cache:
            src = " ".join(q.read_text(errors="replace") for q in (cbuild.CIRLEAN / "CIR").rglob("*.lean"))
            cache[name] = f'"{name}"' in src or f"syntax \"{name}\"" in src
        return cache[name]

    def placeholder_tactic(self) -> str:
        return "cir_start"

    def call_sites(self, unit: Unit, build: Build, max_chars: int = 3000) -> str:
        """Source lines of the unit's callers that call it, with one line of context."""
        out = []
        dem = (unit.signature or {}).get("demangled") if isinstance(unit.signature, dict) else ""
        short = (dem or unit.name).split("(")[0].split("::")[-1].split("<")[0] or unit.name
        for c in build.units:
            if unit.name not in c.callees or not c.source:
                continue
            lines = c.source.splitlines()
            for i, l in enumerate(lines):
                if re.search(r"\b" + re.escape(short) + r"\s*\(", l):
                    out.append(f"// in {c.name}:\n" + "\n".join(lines[max(0, i - 1): i + 2]))
        text = "\n".join(out)
        return text[:max_chars]

    def modular_options(self) -> list[str]:
        return ["set_option cir.inline false in"]

    def intended_prompt(self, unit: Unit, build: Build) -> str:
        return "\n\n".join([
            f"# Function `{unit.name}` (kind: {unit.kind}; Lean decl `{unit.lean_decl}`) cannot be verified yet: "
            f"the bridge does not model a construct it uses ({unit.scope}).",
            "State the contract it is intended to satisfy, so that its callers can be verified assuming it. "
            "It will be used only as an explicit hypothesis of the callers' theorems and reported as an "
            "unverified assumption. Make it the strongest contract the C code plainly satisfies on the inputs "
            "its callers pass, in the same vocabulary as proved contracts (Returns ctx fn_f.sym [args] m post).",
            "## C source", f"```c\n{unit.source or '(not found)'}\n```",
            "## Records of the module", f"```lean\n{self.records(build)}\n```",
            "## Generated IR of the function", f"```lean\n{self.gen_decl(build, unit)}\n```",
            "Give the JSON object: binders, statement, notes."])

    # -- mutual recursion: one obligation for a call-graph cycle (cirlean Examples/Recursion.lean) -------------

    def group_schema(self) -> dict:
        return GROUP_SCHEMA

    def group_module(self, build: Build, comp: list[str]) -> str:
        return f"{build.ns}.scc_{_ident(sorted(comp)[0])}"

    def render_group(self, build: Build, units: list[Unit], members: dict, hyp_text: str, imports: list[str],
                     options: list[str]) -> str:
        """One module for a cycle of the call graph: the members' contracts proved together by strong induction
        on a measure (`<f>_scc_ind`), each recursive call discharged by the induction hypothesis restated as a
        local contract `h_<g>` (with `measure < k` as a premise), then one `@[cir_spec]` theorem per member, of
        the same name and shape as for a function outside a cycle. The skeleton is generated here; the model
        writes the contracts, the measures and each member's tactics."""
        from .patch import binder_groups
        gen = build.info["gen_module"]
        if hyp_text.lstrip().startswith("(ctx : Ctx)"):
            lines = [f"import {i}" for i in ["CIR"] + imports]     # a modular cycle: its own function modules only
        else:
            lines = [f"import {i}" for i in ["CIR", gen] + [i for i in imports if i not in ("CIR", gen)]]
        lines += ["", f"open CIR {build.info['gen_ns']}", "", "set_option maxHeartbeats 4000000", "",
                  f"namespace {build.ns}", ""]
        n = len(units)
        ind = f"{_ident(sorted(u.name for u in units)[0])}_scc_ind"
        hyp_names = " ".join(ns for g, _, br in binder_groups(hyp_text) if br == "(" for ns in g)

        def names(m):
            gs = binder_groups(m["binders"])
            if any(br != "(" for _, _, br in gs):
                raise ValueError("cycle contracts must use explicit binders only")
            return " ".join(x for g, _, _ in gs for x in g)

        def proj(term: str, i: int) -> str:
            return term if n == 1 else term + ".2" * i + (".1" if i < n - 1 else "")

        # the model sometimes answers a field as a list of lines: join it
        ms = [{k: ("\n".join(map(str, v)) if isinstance(v, list) else v) for k, v in members[u.name].items()}
              for u in units]
        options = [o for x in options for o in (x if isinstance(x, list) else [x]) if isinstance(o, str)]
        conj = [f"(∀ {m['binders'].strip()}, {m['measure'].strip()} = k → {m['statement'].strip()})" for m in ms]
        lines += [o.strip() for o in options if o.strip()]
        lines.append(" ".join(x for x in ["theorem", ind, hyp_text.strip(), ": ∀ (k : Nat),"] if x))
        lines.append("    " + " ∧\n    ".join(conj) + " := by")
        lines += ["  intro k", "  induction k using Nat.strongRecOn with", "  | _ k ih =>"]
        for i, (u, m) in enumerate(zip(units, ms)):
            lines.append(f"  have h_{_ident(u.name)} : ∀ {m['binders'].strip()}, {m['measure'].strip()} < k → "
                         f"{m['statement'].strip()} :=")
            lines.append(f"    fun {names(m)} hlt => {proj('(ih _ hlt)', i)} {names(m)} rfl")
        if n > 1:
            lines.append("  refine ⟨" + ", ".join(["?_"] * n) + "⟩")
        for u, m in zip(units, ms):
            lead, ind_t = ("  · ", "    ") if n > 1 else ("  ", "  ")
            lines.append(f"{lead}intro {names(m)} hk")
            lines += [ind_t + x for x in m["tactics"].strip("\n").splitlines() if x.strip()]
        lines.append("")
        for i, (u, m) in enumerate(zip(units, ms)):
            head = " ".join(x for x in ["@[cir_spec] theorem", self.theorem(u), hyp_text.strip(),
                                        m["binders"].strip(), ":"] if x)
            inst = " ".join(x for x in [ind, hyp_names, "(" + m["measure"].strip() + ")"] if x)
            lines += [head, f"    {m['statement'].strip()} :=", f"  {proj('(' + inst + ')', i)} {names(m)} rfl"]
        lines += [f"#print axioms {ind}"] + [f"#print axioms {self.theorem(u)}" for u in units]
        lines += ["", f"end {build.ns}", ""]
        return "\n".join(lines)

    def group_prompt(self, units: list[Unit], build: Build, callees, history, hypotheses=()) -> str:
        from ...scheduler import truncate
        names = ", ".join(f"`{u.name}`" for u in units)
        parts = [f"# A cycle of the call graph: {names} (recursion)",
                 f"Target `{build.target.name}`, build variant `{build.variant.name}`.",
                 "These functions call each other (or themselves), so their contracts are proved TOGETHER by strong "
                 "induction on a measure. The orchestrator writes the skeleton below; you give, for EACH member, its "
                 "contract (`binders` with explicit binders only, `statement`), a Nat-valued `measure` over its "
                 "binders that decreases at every call inside the cycle, and the `tactics` of its conjunct.",
                 "```lean\n"
                 "theorem f_scc_ind : ∀ (k : Nat), (∀ <binders_f>, <measure_f> = k → <statement_f>) ∧ ... := by\n"
                 "  intro k\n"
                 "  induction k using Nat.strongRecOn with\n"
                 "  | _ k ih =>\n"
                 "  have h_f : ∀ <binders_f>, <measure_f> < k → <statement_f> := ...   -- one per member\n"
                 "  refine ⟨?_, ...⟩\n"
                 "  · intro <binder names of f> hk\n"
                 "    <your tactics for f>   -- usually cir_start; cir_vcg; ...\n"
                 "```",
                 "Inside a member's tactics, `cir_vcg` uses the local hypotheses `h_<member>` as the contracts of "
                 "the recursive calls: their premises, including `<measure> < k`, become goals (close them, e.g. "
                 "with omega, using `hk : <measure> = k`). Calls to functions outside the cycle use their contracts "
                 "below. cirlean's worked example: sum_down (measure n.toNat) and is_even/is_odd (mutual)."]
        for u in units:
            parts += [f"## Member `{u.name}` (Lean decl `{u.lean_decl}`, theorem `{self.theorem(u)}`)",
                      "```c\n" + (u.source or "(not found)") + "\n```",
                      "```lean\n" + self.gen_decl(build, u) + "\n```"]
        parts += ["## Records of the module (field order = `.agg` order)", "```lean\n" + self.records(build) + "\n```"]
        if callees:
            parts.append("## Contracts of callees outside the cycle (proved, @[cir_spec], in scope)")
            for ob, _ in callees:
                parts.append(f"```lean\ntheorem {ob.theorem} {ob.contract.binders} :\n    {ob.contract.statement}\n```")
        if hypotheses:
            parts.append("## Assumed contracts (unverified callees outside the cycle), hypotheses in scope")
            for uname, hname, c in hypotheses:
                parts.append(f"```lean\n({hname} : ∀ {c.binders}, {c.statement})\n```")
        if history:
            parts.append("## Previous attempts and Lean's verdicts (fix the problems; do not repeat a failing script)")
            for k, (_, res, prop) in enumerate(history[-2:], start=max(1, len(history) - 1)):
                fb = ["error: " + truncate(e, 2500) for e in res.errors[:3]]
                fb += ["unsolved goal:\n" + truncate(g, 5000) for g in res.goals[:2]]
                parts.append(f"### Attempt {k}: {res.status}\n```json\n" + json.dumps(prop, indent=1)[:6000]
                             + "\n```\n" + "\n".join(fb))
        parts.append("Give the JSON object: members (one per function above, `unit` exactly as named), options, "
                     "strength, notes.")
        return "\n\n".join(parts)

    def user_prompt(self, unit: Unit, build: Build, callees, history, hypotheses=()) -> str:
        from ...scheduler import truncate
        parts = [f"# Function under verification: `{unit.name}` (kind: {unit.kind}; Lean decl `{unit.lean_decl}`,"
                 f" theorem name `{self.theorem(unit)}`)",
                 f"Target `{build.target.name}`, build variant `{build.variant.name}` "
                 f"(compiler flags: {' '.join(build.variant.flags) or 'none'}).",
                 "## C source", f"```c\n{unit.source or '(not found)'}\n```",
                 "## Records of the module (field order = `.agg` order)", f"```lean\n{self.records(build)}\n```",
                 "## Generated IR of the function (for parameter types and symbol)",
                 f"```lean\n{self.gen_decl(build, unit)}\n```"]
        sites = self.call_sites(unit, build)
        if sites:
            parts.append("## How its callers call it (choose argument and memory shapes that fit these call "
                         "sites, e.g. a pointer into an array element rather than a standalone object)")
            parts.append("```c\n" + sites + "\n```")
        if callees:
            parts.append("## Contracts of its callees (proved, tagged @[cir_spec], in scope)")
            for ob, _ in callees:
                parts.append(f"```lean\ntheorem {ob.theorem} {ob.contract.binders} :\n    {ob.contract.statement}\n```")
        elif not hypotheses:
            parts.append("The function calls no other user function.")
        if hypotheses:
            parts.append("## Assumed contracts (unverified callees), in scope as hypotheses of your theorem")
            parts.append("The orchestrator puts these binders in front of your binders, and adds "
                         "`set_option cir.inline false in`, so calls to these functions must be discharged with "
                         "the hypotheses. Do not repeat them in your binders.")
            for uname, hname, c in hypotheses:
                parts.append(f"```lean\n({hname} : ∀ {c.binders}, {c.statement})\n```")
        if history:
            parts.append("## Previous attempts and Lean's verdicts (fix the problems; do not repeat a failing script)")
            for k, (ob, res, prop) in enumerate(history[-3:], start=max(1, len(history) - 2)):
                fb = []
                for e in res.errors[:3]:
                    fb.append("error: " + truncate(e, 2500))
                for g in res.goals[:2]:
                    fb.append("unsolved goal:\n" + truncate(g, 5000))
                parts.append(f"### Attempt {k}: {res.status}\n```json\n" + json.dumps(
                    {kk: prop.get(kk) for kk in ("binders", "statement", "tactics", "options", "needs")}, indent=1)
                    + "\n```\n" + "\n".join(fb))
        parts.append("Give the JSON object: binders, statement, tactics, options, strength, needs, notes.")
        return "\n\n".join(parts)

    def prompt_pack(self) -> str:
        guide = (HERE / "prompt_pack.md").read_text()
        ex = []
        # every worked example of the pinned bridge (they are small and the system prompt is cached);
        # the core examples first, then the rest in name order
        rels = EXAMPLES + sorted(f"Examples/{q.name}" for q in (cbuild.CIRLEAN / "Examples").glob("*.lean")
                                 if f"Examples/{q.name}" not in EXAMPLES)
        for rel in rels:
            p = cbuild.CIRLEAN / rel
            if p.exists():
                ex.append(f"## {rel}\n```lean\n{p.read_text()}\n```")
        return guide + "\n\n# Worked examples (all check)\n\n" + "\n\n".join(ex)


_SUPPORT_LOCK = threading.Lock()


GROUP_SCHEMA = {
    "type": "object",
    "properties": {
        "members": {"type": "array", "items": {
            "type": "object",
            "properties": {
                "unit": {"type": "string", "description": "The function's unit name, exactly as given"},
                "binders": {"type": "string", "description": "Explicit Lean binders and hypotheses, e.g. (n : Int) (m : Mem) (h0 : 0 ≤ n)"},
                "statement": {"type": "string", "description": "Returns ctx fn_f.sym [args] m (fun r m' => post)"},
                "measure": {"type": "string", "description": "A Nat-valued term over the binders that every call inside the cycle decreases, e.g. n.toNat"},
                "tactics": {"type": "string", "description": "Proof of this member's conjunct, one tactic per line (binders and hk : measure = k are already introduced)"},
                "needs": {"type": "array", "items": {"type": "string"}},
            },
            "required": ["unit", "binders", "statement", "measure", "tactics", "needs"],
            "additionalProperties": False}},
        "options": {"type": "array", "items": {"type": "string"},
                    "description": "Lines placed before the induction theorem, e.g. `set_option cir.inline false in`"},
        "strength": {"type": "string", "enum": ["noub", "functional"]},
        "notes": {"type": "string"},
    },
    "required": ["members", "options", "strength", "notes"],
    "additionalProperties": False,
}


PROPOSAL_SCHEMA = {
    "type": "object",
    "properties": {
        "binders": {"type": "string", "description": "Lean binders and hypotheses, e.g. (x : Int) (m : Mem) (hx : ...)"},
        "statement": {"type": "string", "description": "The conclusion: Returns ctx fn_f.sym [args] m (fun r m' => post)"},
        "tactics": {"type": "string", "description": "Proof script, one tactic per line, without `by`"},
        "options": {"type": "array", "items": {"type": "string"},
                    "description": "Lines placed before the theorem, e.g. `set_option cir.inline false in`"},
        "strength": {"type": "string", "enum": ["noub", "functional"]},
        "needs": {"type": "array", "items": {"type": "string"},
                  "description": "Assumptions beyond the calling convention (hneed_ hypotheses) or tool gaps"},
        "notes": {"type": "string"},
    },
    "required": ["binders", "statement", "tactics", "options", "strength", "needs", "notes"],
    "additionalProperties": False,
}


def _ident(s: str) -> str:
    out = "".join(c if c.isalnum() or c == "_" else "_" for c in s)
    return out if out[:1].isalpha() else "u" + out

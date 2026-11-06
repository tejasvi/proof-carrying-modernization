"""CI equivalence verdicts for a changed C/C++ function (old ≡ new, or exactly which inputs changed).

The statement is mechanical (no model). The input domain is read from the parameter types in the generated IR:
* an integer parameter ranges over its C type's range;
* a pointer parameter ranges over every pointer a caller can pass: null, function and vtable pointers, and
  pointers into blocks that exist at the call (`∀ b p, x = .loc b p → b < m.next`). A pointer into a block the
  callee has not allocated yet would alias the callee's own locals, which old and new allocate differently;
* a `float`/`double` parameter ranges over every floating-point value;
* the memory is arbitrary. `ObsEq m` compares the exit and every block that existed before the call, which is
  everything the caller can see through its pointers.

Three verdicts, tried in order, each a kernel-checked theorem in the certificate package (equiv-lean):
* `equivalent`: `Equiv (ObsEq m) (new args) (old args)` on every input of the domain;
* `changed_only_where_old_unsafe`: `EquivOn (Bad := ill-typed call ∨ old unsafe) new old`, where a well-typed
  call is one in the domain above. Wherever the old version was defined, both agree;
* `behaviour_changed`: a distinguishing input on which the old version is safe and the outcomes differ
  (both versions run on the semantics), or `unknown` when neither a proof nor a witness was found.

Parameters of other types get `unknown (domain not mechanical)`. This includes records passed by value: their
pointer fields would need the same condition as pointer parameters.
"""
from __future__ import annotations

import re
from pathlib import Path

from ..base import _ident
from . import patch as cp


def int_domain(adapter, build, unit) -> tuple[str, str, int, list[str]] | None:
    """(binders, args list, arity, conditions) from the parameter types, else None (a type without a mechanical
    domain). Argument i is bound to `x{i}`: `.int x{i}` for an integer, `.ptr x{i}` for a pointer, `.bool x{i}`.
    `conditions` are the domain's constraints on the arguments and `m`. The binders state them as hypotheses
    (after `(m : Mem)`), and the well-typed-call predicate of the EquivOn verdict requires them."""
    decl = adapter.gen_decl(build, unit, max_chars=10**9)
    mp = re.search(r"params := \[(.*?)\]\n", decl)
    if mp is None:
        return None
    params = [x.strip() for x in re.split(r",\s*(?=\()", mp.group(1).strip())] if mp.group(1).strip() else []
    binders, after_m, args, conds = [], [], [], []
    for i, ty in enumerate(params):
        mi = re.fullmatch(r"\(\.int (true|false) (\d+)\)", ty)
        if mi:
            signed, w = mi.group(1) == "true", int(mi.group(2))
            lo, hi = (-(2 ** (w - 1)), 2 ** (w - 1) - 1) if signed else (0, 2 ** w - 1)
            c = f"({lo} ≤ x{i} ∧ x{i} ≤ {hi})"
            binders.append(f"(x{i} : Int) (hx{i} : {c})")
            args.append(f".int x{i}")
            conds.append(c)
        elif ty.startswith("(.ptr "):
            c = f"(∀ b p, x{i} = Ptr.loc b p → b < m.next)"
            binders.append(f"(x{i} : Ptr)")
            after_m.append(f"(hx{i} : {c})")
            args.append(f".ptr x{i}")
            conds.append(c)
        elif ty == "(.bool)" or ty == ".bool":
            binders.append(f"(x{i} : Bool)")
            args.append(f".bool x{i}")
        elif ty in ("(.float .double)", "(.float .float)"):
            binders.append(f"(x{i} : Float)")      # every value of the C type, NaNs and infinities included
            args.append(f".float x{i}")
        else:
            return None
    return " ".join(binders + ["(m : Mem)"] + after_m), "[" + ", ".join(args) + "]", len(params), conds


def render(eid: str, binders: str, args: str, arity: int, gen_old: str, gen_new: str, decl: str,
           conds: list[str] | None = None, only: str | None = None) -> str:
    """The verdict module: both theorems, or `only` one of them (`equivalent` / `changed_only_where_old_unsafe`)."""
    text = _render(eid, binders, args, arity, gen_old, gen_new, decl, conds)
    if only is None:
        return text
    lines = text.splitlines()
    a = next(i for i, l in enumerate(lines) if l.startswith("/-- old ≡ new"))
    b = next(i for i, l in enumerate(lines) if l.startswith("def WT"))
    c = next(i for i, l in enumerate(lines) if l.startswith("#print axioms"))
    keep = lines[:a] + (lines[a:b] if only == "equivalent" else lines[b:c]) + [f"#print axioms {only}", ""] + lines[c + 2:]
    return "\n".join(keep)


def _render(eid: str, binders: str, args: str, arity: int, gen_old: str, gen_new: str, decl: str,
            conds: list[str] | None = None) -> str:
    conds = conds or []
    vars_ = " ".join(f"x{i}" for i in range(arity))
    body = " ∧ ".join([f"args = {args}"] + conds)
    wt = f"fun args m => ∃ {vars_}, {body}" if arity else f"fun args _ => {body}"
    names = [f"x{i}" for i in range(arity)] + ["rfl"] + [f"hwt{k}" for k in range(len(conds))]
    obtain = ("⟨" + ", ".join(names) + "⟩") if arity else "rfl"
    return "\n".join([
        "import CIR", f"import {gen_old}", f"import {gen_new}", "import EquivLean.Core.Facts",
        "import EquivLean.Bridge.Cir.Tactic", "import EquivLean.Bridge.Cir.AutoCouple",   # same-shape loops: no `using`
        "import EquivLean.Bridge.Cir.PtrArgs",          # pointer arguments over an arbitrary memory
        "import VerifOrch.Cir.Patch", "",
        "open CIR EquivLean EquivLean.Cir", "", "set_option maxHeartbeats 4000000", "",
        f"namespace VOEquiv.{eid}", "",
        "/-- old ≡ new on every input of the (mechanical) domain. -/",
        f"theorem equivalent {binders} :",
        f"    Equiv (ObsEq m) (evalCall {gen_new}.ctx {gen_new}.{decl}.sym {args} m)",
        f"      (evalCall {gen_old}.ctx {gen_old}.{decl}.sym {args} m) := by",
        "  equiv_cir", "",
        f"def WT : List Val → Mem → Prop := {wt}", "",
        "/-- Wherever the old version is defined, the versions agree. -/",
        f"theorem changed_only_where_old_unsafe : EquivOn (VerifOrch.Cir.Bad WT {gen_old}.ctx {gen_old}.{decl}.sym)",
        f"    {gen_new}.ctx {gen_new}.{decl}.sym {gen_old}.ctx {gen_old}.{decl}.sym := by",
        "  intro args m hbad",
        "  simp only [VerifOrch.Cir.Bad, not_or, Classical.not_not, WT] at hbad",
        f"  obtain ⟨{obtain}, hsafe⟩ := hbad",
        "  first",
        "    | (refine EquivLean.Equiv.of_sim_of_safe ?_ (fun _ => VerifOrch.Cir.safe_of_safeRet hsafe); equiv_cir)",
        "    | (have hs0 := VerifOrch.Cir.safe_of_safeRet hsafe; rw [safe_res_iff_holds] at hs0; cir_hrun hs0;",
        "       all_goals equiv_cir)", "",
        "#print axioms equivalent", "#print axioms changed_only_where_old_unsafe", "",
        f"end VOEquiv.{eid}", ""])


def cert_modules(pkg, b, ikeys: dict[str, str]) -> str:
    """Check build `b`'s generated modules in the certificate package; returns the name of its top module there.

    A unity build has one generated module. Linked (`cir2lean --link`) and modular builds have one module per
    function: `gen_order` lists the types module, the function modules and the top module, which imports them,
    and all of them are checked in that order. Modular builds name their modules without the revision
    (`Gen.<variant>.Unit...`), so the two revisions of a CI range would collide in one package: their copies get
    the revision in the name (`Gen.<rev>_<variant>.Unit...`), the naming of non-modular builds."""
    top = b.info["gen_module"]
    order = b.info.get("gen_order") or [top]
    prefix = top.rsplit(".", 1)[0]                          # Gen.<variant> or Gen.<rev>_<variant>
    if b.info.get("modular_proofs") or not prefix.startswith(f"Gen.{_ident(b.target.version)}_"):
        new = f"Gen.{_ident(b.target.version)}_{prefix.split('.', 1)[1]}"
        pat = re.compile(r"(?<![\w.])" + re.escape(prefix) + r"(?=[.\s]|$)", re.M)

        def ren(text: str) -> str:
            return pat.sub(new, text)
    else:
        def ren(text: str) -> str:
            return text
    for gm in order:
        src = ren(b.pkg.src(gm).read_text())
        name = ren(gm)
        imports = re.findall(r"^import\s+(\S+)", src, re.M)
        r = pkg.check(name, src, {m: ikeys[m] for m in imports if m in ikeys}, timeout=900, mem_gib=64)
        if not r.ok:
            raise RuntimeError(f"generated module {name} does not check in the certificate package: "
                               f"{r.errors[:2]}")
        ikeys[name] = r.cache_key
    return ren(top)


def verdict(adapter, unit_old, unit_new, b_old, b_new, run_dir: Path, llm=None) -> dict:
    dom = int_domain(adapter, b_new, unit_new)
    if dom is None:
        return {"verdict": "unknown", "detail": "domain not mechanical (parameter type without a domain)"}
    binders, args, arity, conds = dom
    pkg = cp.cert_package(run_dir)
    pkg.ensure()
    cp.ensure_equivlean()
    ikeys = cp.ensure_verifOrch(pkg)
    gen_old, gen_new = cert_modules(pkg, b_old, ikeys), cert_modules(pkg, b_new, ikeys)
    if gen_old == gen_new:
        raise RuntimeError(f"both revisions map to the module {gen_old}: refusing a vacuous comparison")
    eid = re.sub(r"\W", "_", f"{unit_new.name}_{b_old.target.version}_{b_new.target.version}")
    text = render(eid, binders, args, arity, gen_old, gen_new, unit_new.lean_decl, conds)
    res = pkg.check(f"VOEquiv.{eid}", text, ikeys, timeout=590, mem_gib=128, core_h=0.3)
    lines = text.splitlines()
    start2 = next(i + 1 for i, l in enumerate(lines) if l.startswith("def WT"))
    err1 = [m for m in res.messages if m.severity == "error" and m.line < start2]
    err2 = [m for m in res.messages if m.severity == "error" and m.line >= start2]
    out = {"module": f"VOEquiv.{eid}", "seconds": res.seconds}

    def axioms_of(thm: str) -> list[str] | None:
        for m in res.messages:
            mm = re.search(r"'([^']+)' depends on axioms: \[(.*)\]", m.text, re.S)
            if mm and mm.group(1).endswith(thm):
                return [a.strip() for a in mm.group(2).split(",") if a.strip()]
        return None

    std = {"propext", "Classical.choice", "Quot.sound"}
    ax1, ax2 = axioms_of("equivalent"), axioms_of("changed_only_where_old_unsafe")

    def replayable(kind: str) -> dict:
        """When the other theorem failed, the module has an error and Lean writes no .olean, so the accepted
        theorem could not be replayed by the kernel checker: it is checked again alone in a module of its own."""
        if res.ok:
            return {}
        mod = f"VOEquiv.{eid}_{'equiv' if kind == 'equivalent' else 'conservative'}"
        r1 = pkg.check(mod, render(eid, binders, args, arity, gen_old, gen_new, unit_new.lean_decl, conds, only=kind),
                       ikeys, timeout=590, mem_gib=128, core_h=0.3)
        return ({"module": mod, "theorem": f"VOEquiv.{eid}.{kind}", "module_with_both": out["module"]} if r1.ok
                else {"replay_module_error": "; ".join(r1.errors[:2])[:300]})
    if not err1 and res.status != "timeout" and ax1 is not None and set(ax1) <= std:
        return {**out, "verdict": "equivalent", "theorem": f"VOEquiv.{eid}.equivalent", "axioms": ax1,
                **replayable("equivalent")}
    if not err2 and res.status != "timeout" and ax2 is not None and set(ax2) <= std:
        return {**out, "verdict": "changed_only_where_old_unsafe",
                "theorem": f"VOEquiv.{eid}.changed_only_where_old_unsafe", "axioms": ax2,
                **replayable("changed_only_where_old_unsafe")}
    w = None
    all_int = all(a.startswith(".int") for a in args.strip("[]").split(", ") if a)
    if not all_int:
        # pointer domains: the model proposes a concrete memory and arguments, both versions are evaluated on it
        if llm is None:
            return {**out, "verdict": "unknown", "detail": "; ".join(m.text[:200] for m in (err1 + err2)[:2])}
        from . import witness
        decl_text = adapter.gen_decl(b_new, unit_new, max_chars=10**9)
        mp = re.search(r"params := \[(.*?)\]\n", decl_text)
        pw = witness.search(pkg, llm, gen_old, gen_new, unit_new.lean_decl,
                            unit_old.source or "", unit_new.source or "", adapter.records(b_new),
                            mp.group(0) if mp else "", ikeys)
        if pw:
            return {**out, "verdict": "behaviour_changed", "witness": pw}
        return {**out, "verdict": "unknown", "detail": "; ".join(m.text[:200] for m in (err1 + err2)[:2])
                + "; no distinguishing input found"}
    try:
        if not all_int:      # (unreachable: pointer domains are handled above)
            raise ValueError("witness search covers integer parameters only")
        w = cp.disagreement_witness(pkg, gen_old, gen_new, unit_new.lean_decl, arity, ikeys)
    except Exception as e:      # the witness search is evidence only; a failure leaves the verdict unknown
        out["witness_error"] = str(e)[:300]
    if w and not w.get("error"):
        return {**out, "verdict": "behaviour_changed", "witness": w}
    return {**out, "verdict": "unknown", "detail": "; ".join(m.text[:200] for m in (err1 + err2)[:2])}

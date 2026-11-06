"""CI old ≡ new for a changed Rust function, through equiv-lean's Aeneas bridge (EquivLean.Bridge.Aeneas.AutoCouple).

The old revision's LLBC is translated again by Aeneas into the namespace `<crate>_vo_old` (`-namespace`, modules
`Old.<variant>.<crate>.*`), so both versions live in one Lean environment (the pair package: the new revision's
checked modules, byte-identical to its own package, and the old ones). One module per changed function states

    theorem <f>_equiv <args> : Equiv (· = ·) (<crate>.f args) (<crate>_vo_old.f args)

(equiv-lean's `Behaves` instance for `Result`: a panic is an outcome, so this is the same result and the same panic on
every input; only divergence is excluded). Candidates: `equiv_aeneas_straight` (loop-free) and `equiv_aeneas` without
`using` (AutoCouple: the coupling of one lockstep loop per function is generated), with the function's definitions and
those of every function it calls (both versions; calls are inlined, so callees must be loop-free) unfolded.

Without a proof, both versions run by compiled evaluation (`#eval` of the Aeneas definitions, a time limit per input)
on boundary and small inputs of the argument types: an input with different outcomes is a behaviour change, reported
with both outcomes; when none differs, the verdict is `unknown` (equiv-lean covers one lockstep loop per function,
generated couplings only; relations between variables and functional invariants need a hand-written coupling).
"""
from __future__ import annotations

import json
import re
import threading
from pathlib import Path

from ...model import Unit
from ..base import Build, _ident
from . import build as rbuild
from . import evalrun

OLD_SUFFIX = "_vo_old"
_PAIRS: dict = {}
_LOCK = threading.Lock()
_LOOP_RE = re.compile(r"_loop\d*(\.body)?$")
BOUND_LEMMAS = [f"VerifOrch.Rust.{t}_{w}_eq" for t in ("U8", "U16", "U32", "U64", "U128", "I8", "I16", "I32", "I64",
                                                        "I128") for w in ("MAX", "MIN")]


def _pair(b_old: Build, b_new: Build, run_dir: Path) -> dict:
    """The pair package of two revisions (once per revision pair and variant)."""
    key = (b_old.info["llbc"], b_new.info["llbc"], b_new.variant.name)
    with _LOCK:
        if key in _PAIRS:
            return _PAIRS[key]
        work = Path(b_old.info["frontend"])
        old_ns = b_old.info["crate_ns"] + OLD_SUFFIX
        old_prefix = "Old." + b_old.info["prefix"].split(".", 1)[1]
        gdir, _ = rbuild._aeneas(work, Path(b_old.info["llbc"]), old_prefix.replace(".", "/"), namespace=old_ns,
                                 log_name=f"aeneas_{_ident(old_prefix)}")
        osp = rbuild.split_modules(gdir, old_prefix)
        pkg = rbuild.RustLeanPackage(run_dir / "lean_rust_pair" / f"{_ident(b_old.target.version)}__"
                                     f"{_ident(b_new.target.version)}", "vo_" + _ident(run_dir.name),
                                     run_dir / "cache" / "olean")
        pkg.ensure()
        mods, order, deps = {}, [], {}
        for m in b_new.info["gen_order"]:
            if m != b_new.info["gen_module"]:
                mods[m], deps[m] = b_new.pkg.src(m).read_text(), list(b_new.info["gen_deps"][m])
                order.append(m)
        # Aeneas declares the library items it does not model (opaque) under their own names, the same in both
        # revisions: the old modules import the new revision's declarations instead of declaring them again
        new_prefix = b_new.info["prefix"]
        rename = {}
        for kind in ("TypesExternal", "FunsExternal"):
            om_, nm_ = f"{old_prefix}.{kind}", f"{new_prefix}.{kind}"
            if om_ not in osp["modules"]:
                continue
            old_names = set(rbuild._DEF_RE.findall(osp["modules"][om_]))
            new_names = set(rbuild._DEF_RE.findall(mods[nm_])) if nm_ in mods else set()
            if not old_names <= new_names:
                res = {"error": f"{kind}: the old revision uses unmodelled library items the new one does not: "
                                f"{sorted(old_names - new_names)[:5]}"}
                _PAIRS[key] = res
                return res
            rename[om_] = nm_
        for m in osp["order"]:
            if m in mods or m in rename:
                continue
            text = osp["modules"][m]
            for a, b in rename.items():
                text = text.replace(f"public import {a}\n", f"public import {b}\n")
            mods[m], deps[m] = text, [rename.get(d, d) for d in osp["deps"][m]]
            order.append(m)
        for m, text in mods.items():
            p = pkg.src(m)
            p.parent.mkdir(parents=True, exist_ok=True)
            if not p.exists() or p.read_text() != text:
                p.write_text(text)
        keys, failed = rbuild._check_generated(pkg, {"modules": mods, "order": order, "deps": deps}, 3)
        res = {"pkg": pkg, "keys": keys, "failed": failed, "old_ns": old_ns, "old_prefix": old_prefix,
               "old_module": {n["main"]: n["module"] for n in osp["nodes"] if n["main"]},
               "old_defs": {n["main"]: [f"{old_ns}.{d}" for d in n["defs"]] for n in osp["nodes"] if n["main"]},
               "verdicts": {}, "dir": run_dir / "ci" / f"rust_equiv_{_ident(b_old.target.version)}__"
                                                       f"{_ident(b_new.target.version)}"}
        res["dir"].mkdir(parents=True, exist_ok=True)
        _PAIRS[key] = res
        return res


def _closure(u: Unit, by: dict) -> list[Unit]:
    seen, todo = [], list(u.callees)
    while todo:
        n = todo.pop()
        if n in [x.name for x in seen] or n not in by:
            continue
        seen.append(by[n])
        todo += by[n].callees
    return seen


def verdict(adapter, u_old: Unit, u_new: Unit, b_old: Build, b_new: Build, run_dir: Path, llm=None) -> dict:
    if not (u_old.in_scope and u_new.in_scope):
        return {"verdict": "unknown", "detail": f"not translated: old {u_old.scope}, new {u_new.scope}"}
    so, sn = u_old.signature or {}, u_new.signature or {}
    to, tn = [b["type"] for b in so.get("binders", [])], [b["type"] for b in sn.get("binders", [])]
    if to != tn or so.get("ret") != sn.get("ret"):
        return {"verdict": "unknown", "detail": f"signature changed: ({', '.join(to)}) -> {so.get('ret')} became "
                                                f"({', '.join(tn)}) -> {sn.get('ret')}; old ≡ new is not stated"}
    P = _pair(b_old, b_new, run_dir)
    if "error" in P:
        return {"verdict": "unknown", "detail": P["error"]}
    if u_new.name in P["verdicts"]:
        return P["verdicts"][u_new.name]
    om, nm = P["old_module"].get(u_new.name), b_new.info.get("unit_module", {}).get(u_new.name)
    if om is None or om not in P["keys"] or nm not in P["keys"]:
        return {"verdict": "unknown", "detail": f"modules do not check in the pair package: "
                                                f"{P['failed'].get(om) or P['failed'].get(nm) or 'missing'}"}
    by_new = {u.name: u for u in b_new.units}
    clo = _closure(u_new, by_new)
    old_ns, new_ns = P["old_ns"], b_new.info["crate_ns"]
    defs_new = list(sn.get("defs", [])) + [d for c in clo for d in (c.signature or {}).get("defs", [])]
    defs_old = P["old_defs"].get(u_new.name, []) + [d for c in clo for d in P["old_defs"].get(c.name, [])]
    looped_callees = [c.name for c in clo if any(_LOOP_RE.search(d) for d in (c.signature or {}).get("defs", []))]
    binders = " ".join(b["text"] for b in sn.get("binders", []))
    args = "".join(" " + a for b in sn.get("binders", []) if b["explicit"] for a in b["names"])
    new_app, old_app = f"{sn['lean']}{args}", f"{old_ns}.{u_new.name}{args}"
    thm = f"{_ident(u_new.name)}_equiv"
    mod = f"VOEq.{_ident(b_new.variant.name)}.{_ident(u_new.name)}"
    statement = f"Equiv (· = ·) ({new_app}) ({old_app})"
    defs = ", ".join(defs_new + defs_old)
    extra = ", ".join(BOUND_LEMMAS)
    candidates = [("equiv_aeneas_straight", f"equiv_aeneas_straight [{defs}] with [{extra}]")]
    if not looped_callees:
        candidates.append(("equiv_aeneas (generated coupling)", f"equiv_aeneas [{defs}] with [{extra}]"))
    tried = []
    for name, tac in candidates:
        src = "\n".join([
            "import EquivLean.Bridge.Aeneas.AutoCouple", f"import {nm}", f"import {om}", "",
            "open Aeneas Aeneas.Std Result ControlFlow Error EquivLean EquivLean.Aeneas", "",
            "set_option maxHeartbeats 4000000", "", f"namespace VOEq.{_ident(b_new.variant.name)}", "",
            f"theorem {thm} {binders} :", f"    {statement} := by", f"  {tac}", "", f"#print axioms {thm}", "",
            f"end VOEq.{_ident(b_new.variant.name)}", ""])
        res = P["pkg"].check(mod, src, {nm: P["keys"][nm], om: P["keys"][om]}, timeout=900)
        bad = [a for a in res.axioms if a not in ("propext", "Classical.choice", "Quot.sound")]
        tried.append({"tactic": name, "status": res.status, "errors": (res.errors or res.goals)[:1]})
        if res.ok and not bad:
            v = {"verdict": "equivalent", "tool": f"equiv-lean {name}", "theorem": f"VOEq.{_ident(b_new.variant.name)}.{thm}",
                 "statement": statement, "module": mod, "key": res.cache_key, "axioms": res.axioms,
                 "seconds": res.seconds}
            P["verdicts"][u_new.name] = v
            return v
    w = _witness(P, b_new, u_new, nm, om, new_app, old_app)
    if w.get("differs"):
        v = {"verdict": "behaviour_changed", "tool": "compiled evaluation of both Aeneas translations",
             "witness": w["differs"][0], "differing_inputs": w["differs"][:10], "inputs_evaluated": w["n"],
             "inputs_timed_out": w["timeouts"], "proof_attempts": tried}
        if llm is not None:
            try:
                v["changed_set"] = _changed_set(P, b_old, b_new, u_new, nm, om, w, llm)
            except Exception as e:          # the verdict stands without the characterisation
                v["changed_set"] = {"status": "error", "detail": f"{type(e).__name__}: {e}"[:300]}
    else:
        why = (f"callees with loops are not inlined: {looped_callees}; " if looped_callees else "")
        v = {"verdict": "unknown", "detail": why + f"no proof ({', '.join(t['tactic'] for t in tried)}) and no "
                                                   f"distinguishing input among {w['n']} evaluated"
                                                   + (f" ({w['timeouts']} timed out)" if w["timeouts"] else "")
                                                   + (f"; {w['error']}" if w.get("error") else ""),
             "proof_attempts": tried}
    P["verdicts"][u_new.name] = v
    return v


def _witness(P: dict, b_new: Build, u: Unit, nm: str, om: str, new_app: str, old_app: str) -> dict:
    """Both versions on the same generated inputs; the inputs whose outcomes differ."""
    sig = u.signature or {}
    if any(not b["explicit"] for b in sig.get("binders", [])):
        return {"n": 0, "timeouts": 0, "error": "generic function: no inputs generated"}
    params = [(n, b["type"]) for b in sig.get("binders", []) for n in b["names"]]
    grid, err = evalrun.input_grid(params, u.name)
    if err:
        return {"n": 0, "timeouts": 0, "error": err}
    fn_new, fn_old = sig["lean"], P["old_ns"] + "." + u.name
    exprs = [(k, f"VOEval.outcome ({fn_old}{a}) ++ \" || \" ++ VOEval.outcome ({fn_new}{a})")
             for k, (a, _) in enumerate(grid)]
    results, timeouts, err = evalrun.evaluate(P["pkg"], [nm, om], exprs,
                                              f"VOEq.Eval.{_ident(b_new.variant.name)}.{_ident(u.name)}",
                                              P["dir"] / f"eval_{_ident(u.name)}.txt")
    differs = []
    for k, (_, shown) in enumerate(grid):
        r = results.get(k)
        if r is not None and " || " in r:
            ro, rn = r.split(" || ", 1)
            if ro != rn:
                differs.append({"args": shown, "old": ro, "new": rn})
    out = {"n": len(results), "timeouts": timeouts, "differs": differs,
           "evaluated": [grid[k][1] for k in sorted(results) if k < len(grid)]}
    if err:
        out["error"] = err
    return out


# -- the changed input set (EquivOn) ---------------------------------------------------------------------------------

EQUIV_ON_GUIDE = r"""You write Lean 4 proofs about Rust functions translated by Charon + Aeneas, with equiv-lean's Aeneas bridge.
A change to a function is known to alter its behaviour on some inputs (found by evaluation). The theorem, which is
FIXED, says the new and the old version agree on every other input: same result and same panic
(`Equiv (· = ·) t s`; `equiv_eq_iff : Equiv (· = ·) t s ↔ t = s`). Give only the tactic proof. Answer with JSON only.

Tools: `equiv_eq_iff`, `equiv_of_wp` (goal `wp s (fun os => wp t (fun ot => R ot os))`), `aeneas_wp [defs]` (symbolic
execution of Aeneas code under `wp`, unfolding `defs`), `aeneas_leaves` (closes the leaves), `equiv_aeneas_straight
[defs]`, `equiv_aeneas [defs]` (two loops in lockstep, coupling generated) / `equiv_aeneas [defs] using I`, `rw [loop]`
(unfold a loop ONE iteration; never put `loop` in a simp set: it unfolds forever), `by_cases`, `simp only [...]`,
`subst`, `split_ifs`, `scalar_tac`, `omega`, `simp_all`. Lemmas `<name>_same : @new.f = @old.f` (by `rfl`) are given
for every definition whose text is the same in both versions: rewrite with them so both sides call the same
function, then the two sides often become syntactically equal (`simp only [...]` closes `t = t`).

Worked example (equiv-lean, Demo/Aeneas/SumPR.lean `v3_equivOn_v1`, checks): a PR replaced `s = s + v[i]` by
`s = s.saturating_add(v[i])` in a summing loop; the versions differ exactly on the inputs where the old one overflows
(`Bad v := 4294967295 < total v`, `total v` the mathematical sum). `EquivOn Bad R f g` unfolds to
`∀ x, ¬ Bad x → Equiv R (f x) (g x)`, the form of your theorem.

```lean
def total (v : Slice U32) : Nat := (v.val.map UScalar.val).sum
def Bad (v : Slice U32) : Prop := 4294967295 < total v

theorem sum_drop_succ (l : List Nat) (i : Nat) (h : i < l.length) :
    (l.drop i).sum = l[i] + (l.drop (i + 1)).sum := by
  rw [List.drop_eq_getElem_cons h, List.sum_cons]

theorem v3_equivOn_v1 : EquivOn Bad (· = ·) sumpr.v3.sum sumpr.v1.sum := by
  intro v hbad
  simp only [Bad, Nat.not_lt] at hbad
  equiv_aeneas [sumpr.v3.sum, sumpr.v1.sum, sumpr.v3.sum_loop, sumpr.v1.sum_loop,
      sumpr.v3.sum_loop.body, sumpr.v1.sum_loop.body]
    using fun p q => p = q ∧ p.2.val ≤ v.val.length ∧
      p.1.val + ((v.val.map UScalar.val).drop p.2.val).sum = total v
    with [sum_drop_succ, total]
```

JSON object: `tactics` (the proof after `:= by`, one tactic per line), `notes` (one sentence)."""

EQUIV_ON_SCHEMA = {"type": "object", "properties": {"tactics": {"type": "string"}, "notes": {"type": "string"}},
                   "required": ["tactics", "notes"], "additionalProperties": False}


def _bad_predicate(params: list[tuple[str, str]], w: dict) -> str | None:
    """A predicate on the arguments that holds exactly on the inputs whose outcomes differed, among those evaluated:
    one argument at one value (every evaluated input with it differed, no other did), or the differing inputs
    themselves (at most four)."""
    rows = w.get("evaluated") or []
    diff = [d["args"] for d in w["differs"]]
    dkeys = {json.dumps(a, sort_keys=True) for a in diff}
    for n, t in params:
        for v in sorted({a[n] for a in diff}):
            same = {json.dumps(a, sort_keys=True) for a in rows if a.get(n) == v}
            lit = evalrun.literal(t, json.loads(v) if re.fullmatch(r"-?\d+|true|false", v) else None)
            if same and same == dkeys and lit is not None:
                return f"{n} = {lit}"
    if len(diff) > 4:
        return None
    alts = []
    for a in diff:
        conj = []
        for n, t in params:
            lit = evalrun.literal(t, json.loads(a[n]) if re.fullmatch(r"-?\d+|true|false", a[n]) else None)
            if lit is None:
                return None
            conj.append(f"{n} = {lit}")
        alts.append("(" + " ∧ ".join(conj) + ")")
    return " ∨ ".join(alts) if alts else None


def _changed_set(P: dict, b_old: Build, b_new: Build, u: Unit, nm: str, om: str, w: dict, llm) -> dict:
    """`∀ args, ¬ Bad args → Equiv (· = ·) (new.f args) (old.f args)` for the predicate `Bad` read off the evaluated
    inputs: with the witnesses (where the versions differ), the exact input set the change alters. The statement is
    fixed; the model writes the proof (two attempts)."""
    sig = u.signature or {}
    params = [(n, b["type"]) for b in sig.get("binders", []) if b["explicit"] for n in b["names"]]
    bad = _bad_predicate(params, w)
    if bad is None:
        return {"status": "skipped", "detail": "no simple predicate fits the differing inputs"}
    old_ns, new_ns = P["old_ns"], b_new.info["crate_ns"]
    by_new = {x.name: x for x in b_new.units}
    names = [u.name] + [c.name for c in _closure(u, by_new)]
    # definitions with the same text in both versions: `rfl` lemmas the proof can rewrite with
    same = []
    new_text = b_new.pkg.src(nm).read_text()
    old_text = P["pkg"].src(om).read_text()
    for n in names:
        for d in (by_new[n].signature or {}).get("defs", []) if n in by_new else []:
            short = d[len(new_ns) + 1:]
            blk_n = _def_block(new_text, short)
            blk_o = _def_block(old_text, short)
            if blk_n and blk_n == blk_o:
                same.append((f"{_ident(short)}_same", d, f"{old_ns}.{short}"))
    binders = " ".join(b["text"] for b in sig.get("binders", []))
    args = "".join(" " + a for a, _ in params)
    thm = f"{_ident(u.name)}_equivOn"
    statement = f"∀ {binders}, ¬ ({bad}) → Equiv (· = ·) ({sig['lean']}{args}) ({old_ns}.{u.name}{args})"
    mod = f"VOEq.{_ident(b_new.variant.name)}.{_ident(u.name)}_on"
    head = ["import EquivLean.Bridge.Aeneas.AutoCouple", f"import {nm}", f"import {om}", "",
            "open Aeneas Aeneas.Std Result ControlFlow Error EquivLean EquivLean.Aeneas", "",
            "set_option maxHeartbeats 4000000", "", f"namespace VOEq.{_ident(b_new.variant.name)}", ""]
    head += [f"theorem {n} : @{a} = @{b} := rfl" for n, a, b in same] + [""]
    user = "\n\n".join([
        f"# Changed function `{u.name}`; inputs where the versions differ (evaluated): "
        + json.dumps(w["differs"][:5]),
        "## New version (namespace " + new_ns + ")", f"```lean\n{_body(new_text)}\n```",
        "## Old version (namespace " + old_ns + ")", f"```lean\n{_body(old_text)}\n```",
        "## Lemmas in scope", "```lean\n" + "\n".join(f"theorem {n} : @{a} = @{b}" for n, a, b in same) + "\n```",
        "## The theorem to prove (fixed)", f"```lean\ntheorem {thm} : {statement}\n```"])
    history = []
    for k in range(2):
        prompt = user + ("" if not history else "\n\n## Previous attempts\n" + "\n".join(
            f"```lean\n{h['tactics']}\n```\nLean: {h['feedback'][:2500]}" for h in history))
        try:
            ans = llm.ask_json(f"equivOn:{u.name}:{k}", EQUIV_ON_GUIDE, prompt, EQUIV_ON_SCHEMA, effort="high")
        except Exception as e:
            return {"status": "error", "predicate": bad, "detail": f"model: {e}"[:300]}
        tac = ans.get("tactics", "")
        src = "\n".join(head + [f"theorem {thm} : {statement} := by"] + ["  " + l for l in tac.splitlines()]
                         + ["", f"#print axioms {thm}", "", f"end VOEq.{_ident(b_new.variant.name)}", ""])
        res = P["pkg"].check(mod, src, {nm: P["keys"][nm], om: P["keys"][om]}, timeout=900)
        bad_ax = [a for a in res.axioms if a not in ("propext", "Classical.choice", "Quot.sound")]
        if res.ok and not bad_ax:
            return {"status": "proved", "predicate": bad, "statement": statement,
                    "theorem": f"VOEq.{_ident(b_new.variant.name)}.{thm}", "module": mod, "tactics": tac,
                    "axioms": res.axioms}
        history.append({"tactics": tac, "feedback": "; ".join((res.errors or [])[:2] + (res.goals or [])[:1])})
    return {"status": "unproved", "predicate": bad, "statement": statement, "attempts": len(history)}


def _def_block(text: str, short: str) -> str | None:
    """The text of `def <short>` in a split module (up to the next doc comment or `end`), without the namespace."""
    m = re.search(rf"^(?:@\[[^\n]*\]\n)?def {re.escape(short)}(?=[\s(:])(?:.*\n)*?(?=^/--|^end |^@\[|\Z)", text, re.M)
    return m.group(0) if m else None


def _body(text: str) -> str:
    i = text.find("\nnamespace ")
    return text[i + 1:] if i >= 0 else text

"""Distinguishing inputs for CI verdicts over pointer domains.

When neither `equivalent` nor `changed_only_where_old_unsafe` is proved for a function with pointer parameters,
the model proposes a concrete input: a small memory (blocks with typed values, e.g. linked records) and the
argument values. veriforch evaluates both versions on it with cirlean's interpreter (`#eval evalCall`) and
accepts the input as a witness only if all of the following hold:
* it is in the CI domain (every pointer argument points into a block of the memory);
* the old version runs without undefined behaviour;
* the two outcomes differ: the exit, or the contents of a block that existed before the call.

The model's terms are only evaluated, never trusted as proofs: the verdict stays `behaviour_changed` evidence from
running both versions, like the integer witness search.
"""
from __future__ import annotations

import json
import re

WITNESS_SCHEMA = {
    "type": "object",
    "properties": {
        "blocks": {"type": "array", "items": {
            "type": "object",
            "properties": {
                "kind": {"type": "string", "enum": ["heap", "stack", "global", "readonly"]},
                "ty": {"type": "string", "description": "Lean `Ty` term of the block, e.g. (.record \"cJSON\")"},
                "val": {"type": "string", "description": "Lean `Val` term, e.g. .agg [.ptr .null, .ptr (.loc 1 []), .int 0]"},
            },
            "required": ["kind", "ty", "val"], "additionalProperties": False}},
        "args": {"type": "array", "items": {"type": "string"},
                 "description": "One Lean `Val` term per parameter, e.g. .ptr (.loc 0 [])"},
        "why": {"type": "string"},
    },
    "required": ["blocks", "args", "why"],
    "additionalProperties": False,
}

_ALLOWED = re.compile(r"^[\s\w.\[\](),:\"'+\-*/<>=!&|⟨⟩]*$")


def _clean(term: str) -> str:
    """Model-written Lean terms are spliced into an `#eval` module: refuse anything beyond plain value syntax."""
    if not _ALLOWED.match(term) or any(k in term for k in ("#", "import", "open", "macro", "elab", "syntax",
                                                             "set_option", "unsafe", "IO", "run_cmd")):
        raise ValueError(f"term rejected: {term[:120]}")
    return term


def render(gen_old: str, gen_new: str, decl: str, cand: dict) -> str:
    blocks = cand.get("blocks") or []
    if not isinstance(blocks, list) or any(not isinstance(b, dict) or "ty" not in b or "val" not in b for b in blocks):
        raise ValueError("every block needs `ty` and `val`")
    kinds = [b.get("kind", "heap") for b in blocks]
    if any(k not in ("heap", "stack", "global", "readonly") for k in kinds):
        raise ValueError(f"block kind must be heap, stack, global or readonly: {kinds}")
    cases = "\n".join(f"  | {i} => some ⟨.{k}, true, {_clean(str(b['ty']))}, {_clean(str(b['val']))}⟩"
                      for i, (k, b) in enumerate(zip(kinds, blocks)))
    args = ", ".join(_clean(str(a)) for a in cand.get("args") or [])
    n = len(blocks)
    return f"""import CIR
import {gen_old}
import {gen_new}
open CIR

deriving instance Repr for CIR.Exit

/-- Each version runs on its OWN module's initial memory (its globals and statics initialized as in that
program; a commit may add, drop or reorder globals), followed by the candidate's blocks, numbered `voBase + i`
after the globals of both modules, so a pointer argument names the same block in both runs. -/
def voInitOld : Mem := Module.initMem {gen_old}.module
def voInitNew : Mem := Module.initMem {gen_new}.module
def voBase : Nat := max voInitOld.next voInitNew.next

def voExtra : Nat → Option MemBlock
{cases}
  | _ => none

def voMemOf (init : Mem) : Mem :=
  {{ blocks := fun b => if b < init.next then init.blocks b else if b < voBase then none else voExtra (b - voBase),
     next := voBase + {n} }}

def voArgs : List Val := [{args}]

/-- In the CI domain: every pointer argument points into an existing block (or is null/fn/vtable). -/
def voInDomain : Bool := voArgs.all fun v => match v with
  | .ptr (.loc b _) => decide (b < voBase + {n})
  | _ => true

/-- The outcome: the exit and the candidate's blocks after the call (the globals' layouts may differ between
the versions, so they are not compared). -/
def voObs (r : Res (Exit × Mem)) : String :=
  match r with
  | .ok (e, m) => s!"ok {{reprStr e}} " ++ String.intercalate ";" ((List.range {n}).map fun i =>
      match m.blocks (voBase + i) with | some blk => reprStr blk.val | none => "none")
  | .ub msg => s!"ub {{msg}}"
  | .div => "div"

#eval
  let o := voObs (evalCall {gen_old}.ctx {gen_old}.{decl}.sym voArgs (voMemOf voInitOld))
  let w := voObs (evalCall {gen_new}.ctx {gen_new}.{decl}.sym voArgs (voMemOf voInitNew))
  if !voInDomain then "VOW OUT_OF_DOMAIN"
  else if !o.startsWith "ok" then s!"VOW OLD_UNSAFE {{o}}"
  else if o == w then "VOW SAME"
  else s!"VOW DIFF ||| {{o}} ||| {{w}}"
"""


def search(pkg, llm, gen_old: str, gen_new: str, decl: str, src_old: str, src_new: str, records: str,
           params: str, import_keys: dict, tries: int = 2, log=print) -> dict | None:
    """Ask the model for candidate inputs and keep the first that distinguishes the versions (see module doc)."""
    history = []
    for k in range(tries):
        prompt = "\n\n".join([
            "# Find an input on which two versions of a C function behave differently",
            "The old version must run WITHOUT undefined behaviour on the input; the outcomes (return value or the "
            "contents of a block that existed before the call) must differ. The memory is the program's initial "
            "memory (globals and statics in place) followed by the blocks you provide: your block i is "
            "`.loc (voBase + i) []`, an element of an array block `.loc (voBase + i) [.idx j]`, a field of a record "
            "block `.loc (voBase + i) [.idx f]`. Write every pointer to your blocks in that form, with `voBase`.",
            "## Old version", f"```c\n{src_old}\n```", "## New version", f"```c\n{src_new}\n```",
            "## Parameter types (IR)", f"```lean\n{params}\n```",
            "## Records (field order = `.agg` order)", f"```lean\n{records}\n```",
            "Values: `.int n`, `.ptr .null`, `.ptr (.loc b path)`, `.agg [fields]`, `.arr [elems]`; record type "
            "`(.record \"name\")`, array type `(Ty.array elemTy n)`, int type `(.int true 32)`, pointer `(.ptr ty)`.",
        ] + ([f"## Earlier candidates and results\n```json\n{json.dumps(history, indent=1)[:5000]}\n```"] if history else []) +
            ["Give the JSON object: blocks, args, why."])
        try:
            cand = llm.ask_json(f"witness:{decl}:{k}", "You construct concrete test inputs for C code given in "
                                "cirlean's Lean value syntax.", prompt, WITNESS_SCHEMA, effort="high")
        except Exception as e:                      # budget or API trouble: no witness
            log(f"  witness search stopped: {e}")
            return None
        try:
            src = render(gen_old, gen_new, decl, cand)
        except (ValueError, KeyError, TypeError) as e:
            history.append({"candidate": cand, "result": str(e)})
            continue
        mod = f"VOCert.PWitness_{re.sub(r'[^A-Za-z0-9_]', '_', gen_new)}_{decl}_{k}"
        res = pkg.check(mod, src, import_keys, mem_gib=64, use_cache=False, timeout=600)
        out = " ".join(m.text for m in res.messages if "VOW" in m.text)
        history.append({"candidate": cand, "result": out[:1500] or "; ".join(res.errors[:2])[:1500]})
        log(f"  witness candidate {k}: {(out or '; '.join(res.errors[:1]))[:200]}")
        if "VOW DIFF" in out:
            old, new = [s.strip() for s in out.split("|||")[1:3]]
            return {"args": cand["args"], "blocks": cand["blocks"], "why": cand.get("why", ""),
                    "old": old[:600], "new": new[:600], "evaluated": True}
    return None

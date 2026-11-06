"""Compiled evaluation of Aeneas translations on concrete inputs (`#eval` of the Lean definitions the proofs are about,
one thread and a time limit per input), shared by the CI witness search (equiv.py), the refutation of no-panic
statements and `vo cex` (adapter.py: refute, run_semantic).

Inputs per argument type: boundaries and small values of scalars, booleans, and short slices / vectors of them
(`values`); a JSON value given for one argument (e.g. by the model in `vo cex`) is turned into a literal by `literal`.
"""
from __future__ import annotations

import itertools
import json
import random
import re
from pathlib import Path

from ...lean import LEAN_BIN, parse_messages
from ...model import sha256
from ..base import _ident
from . import build as rbuild

CASE_MS = 5000                      # per-input limit
BATCH = 60                          # inputs per Lean run
MAX_CASES = 240

_EVAL_PRELUDE = r'''
open Aeneas Aeneas.Std Result

namespace VOEval

class VoShow (α : Type) where
  str : α → String

instance : VoShow Bool := ⟨fun b => toString b⟩
instance : VoShow Unit := ⟨fun _ => "()"⟩
instance {ty : UScalarTy} : VoShow (UScalar ty) := ⟨fun x => toString x.val⟩
instance {ty : IScalarTy} : VoShow (IScalar ty) := ⟨fun x => toString x.val⟩
instance {α β : Type} [VoShow α] [VoShow β] : VoShow (α × β) :=
  ⟨fun p => "(" ++ VoShow.str p.1 ++ ", " ++ VoShow.str p.2 ++ ")"⟩
instance {α : Type} [VoShow α] : VoShow (List α) := ⟨fun l => "[" ++ ", ".intercalate (l.map VoShow.str) ++ "]"⟩
instance {α : Type} [VoShow α] : VoShow (alloc.vec.Vec α) := ⟨fun v => VoShow.str v.val⟩
instance {α : Type} [VoShow α] : VoShow (Slice α) := ⟨fun v => VoShow.str v.val⟩
instance {α : Type} {n : Usize} [VoShow α] : VoShow (Std.Array α n) := ⟨fun v => VoShow.str v.val⟩
instance {α : Type} [VoShow α] : VoShow (Option α) :=
  ⟨fun o => match o with | none => "None" | some a => "Some " ++ VoShow.str a⟩

def outcome {α : Type} [VoShow α] (r : Result α) : String :=
  match r.match with
  | .ok a => "ok " ++ VoShow.str a
  | .div => "div"
  | .vis (.fail e) _ => "panic " ++ toString (repr e)

def slice {α : Type} (l : List α) : Slice α :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

def vec {α : Type} (l : List α) : alloc.vec.Vec α :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], by simp⟩

partial def waitTask (t : Task String) (start limit : Nat) : IO (Option String) := do
  if ← IO.hasFinished t then return some t.get
  if (← IO.monoMsNow) - start > limit then return none
  IO.sleep 5
  waitTask t start limit

def emit (path line : String) : IO Unit := do
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn line
  h.flush

/-- One input on its own thread; past the limit the process ends (the runner resumes after this input). -/
def evalCase (path : String) (k limit : Nat) (f : Unit → String) : IO Unit := do
  emit path s!"VOSTART {k}"
  let start ← IO.monoMsNow
  match ← waitTask (Task.spawn f .dedicated) start limit with
  | some s => emit path s!"VOCASE {k} {s}"
  | none => emit path s!"VOTIMEOUT {k}"; IO.Process.exit 3
'''

_UNSIGNED = {"Std.U8": 8, "Std.U16": 16, "Std.U32": 32, "Std.U64": 64, "Std.U128": 128, "Std.Usize": 64,
             "U8": 8, "U16": 16, "U32": 32, "U64": 64, "U128": 128, "Usize": 64}
_SIGNED = {"Std.I8": 8, "Std.I16": 16, "Std.I32": 32, "Std.I64": 64, "Std.I128": 128, "Std.Isize": 64,
           "I8": 8, "I16": 16, "I32": 32, "I64": 64, "I128": 128, "Isize": 64}


def values(ty: str) -> list[tuple[str, str]] | None:
    """(Lean term, shown value) for inputs of one argument type: boundaries and small values."""
    ty = ty.strip()
    if ty in ("Bool", "_root_.Bool"):
        return [("false", "false"), ("true", "true")]
    if ty in _UNSIGNED:
        n = _UNSIGNED[ty]
        mx = 2 ** n - 1
        suf = ty.split(".")[-1].lower()
        vs = sorted(v for v in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 16, 25, 27, 28, 100, 255, 1000, mx // 2, mx - 1, mx}
                    if 0 <= v <= mx)
        return [(f"{v}#{suf}", str(v)) for v in vs]
    if ty in _SIGNED:
        n = _SIGNED[ty]
        mx, mn = 2 ** (n - 1) - 1, -(2 ** (n - 1))
        suf = ty.split(".")[-1].lower()
        vs = sorted({0, 1, -1, 2, -2, 3, -3, 5, 7, 10, -10, 13, 100, -100, mn, mn + 1, mx - 1, mx})
        return [(f"({v})#{suf}", str(v)) for v in vs]
    m = re.fullmatch(r"(Slice|alloc\.vec\.Vec)\s+(\S+)", ty) or re.fullmatch(r"(Slice|alloc\.vec\.Vec)\s+\((.+)\)", ty)
    if m:
        el = values(m.group(2))
        if not el:
            return None
        mk = "VOEval.slice" if m.group(1) == "Slice" else "VOEval.vec"
        small = el[:6] + el[-2:]
        lists = [[], [small[0]], [small[1]], small[:3], small[1:4][::-1], [small[-1]], [small[-1], small[-1]],
                 small[:6]]
        out = []
        for l in lists:
            out.append((f"({mk} [{', '.join(t for t, _ in l)}])", "[" + ", ".join(s for _, s in l) + "]"))
        return out
    return None


def literal(ty: str, v) -> str | None:
    """The Lean literal of a JSON value for an argument of type `ty` (None when the type or value is not supported)."""
    ty = ty.strip()
    if ty in ("Bool", "_root_.Bool") and isinstance(v, bool):
        return "true" if v else "false"
    if (ty in _UNSIGNED or ty in _SIGNED) and isinstance(v, int) and not isinstance(v, bool):
        n = (_UNSIGNED.get(ty) or _SIGNED.get(ty))
        lo, hi = (0, 2 ** n - 1) if ty in _UNSIGNED else (-(2 ** (n - 1)), 2 ** (n - 1) - 1)
        if not lo <= v <= hi:
            return None
        suf = ty.split(".")[-1].lower()
        return f"{v}#{suf}" if ty in _UNSIGNED else f"({v})#{suf}"
    m = re.fullmatch(r"(Slice|alloc\.vec\.Vec)\s+\(?([^()]+?)\)?", ty)
    if m and isinstance(v, list):
        el = [literal(m.group(2), x) for x in v]
        if any(e is None for e in el):
            return None
        mk = "VOEval.slice" if m.group(1) == "Slice" else "VOEval.vec"
        return f"({mk} [{', '.join(el)}])"
    return None


def input_grid(params: list[tuple[str, str]], seed: str) -> tuple[list[tuple[str, dict]], str | None]:
    """Argument lists for the parameters [(name, type)]: [(Lean argument text, {name: shown value})], or an error."""
    vals = [values(t) for _, t in params]
    if any(v is None for v in vals):
        return [], "argument types without generated inputs: " + ", ".join(t for (_, t), v in zip(params, vals) if v is None)
    combos = list(itertools.product(*vals)) if vals else [()]
    if len(combos) > MAX_CASES:
        rnd = random.Random(sha256(seed)[:8])
        head = [tuple(v[min(i, len(v) - 1)] for v in vals) for i in range(max(len(v) for v in vals))]
        combos = head + rnd.sample(combos, MAX_CASES - len(head))
    return [("".join(f" {t}" for t, _ in c), {n: s for (n, _), (_, s) in zip(params, c)}) for c in combos], None


def evaluate(pkg, imports: list[str], exprs: list[tuple[int, str]], mod: str, out_file: Path,
             case_ms: int = CASE_MS) -> tuple[dict[int, str], int, str | None]:
    """Evaluate String-valued Lean expressions (built from `VOEval.outcome`) in `pkg`, importing `imports`: one
    top-level `#eval` per expression (each elaborated on its own), at most BATCH per Lean run; an expression past its
    time limit ends the run, which resumes after it. Returns ({k: value}, number timed out, error)."""
    results: dict[int, str] = {}
    timeouts, start = 0, 0
    path = pkg.src(mod)
    path.parent.mkdir(parents=True, exist_ok=True)
    out_file.parent.mkdir(parents=True, exist_ok=True)
    head = "".join(f"import {i}\n" for i in imports) + _EVAL_PRELUDE + "\nend VOEval\n\n"
    while start < len(exprs):
        batch = exprs[start: start + BATCH]
        if out_file.exists():
            out_file.unlink()
        path.write_text(head + "\n".join(f"#eval VOEval.evalCase {json.dumps(str(out_file))} {k} {case_ms} (fun _ => {e})"
                                         for k, e in batch) + "\n")
        p = rbuild._job(["env", f"LEAN_PATH={pkg.lean_path()}", LEAN_BIN, "-R", pkg.dir, "--json", "-j", "1",
                         "-DElab.async=false", f"--tstack={4 << 20}", path], pkg.dir, mem_gib=32,
                        timeout=len(batch) * case_ms // 1000 + 240, core_h=0.25)
        lines = out_file.read_text().splitlines() if out_file.exists() else []
        started, timed_out = False, None
        for l in lines:
            m = re.match(r"VOCASE (\d+) (.*)$", l)
            if m:
                results[int(m.group(1))] = m.group(2)
            elif l.startswith("VOSTART"):
                started = True
            elif l.startswith("VOTIMEOUT"):
                timed_out = int(l.split()[1])
        if not started:
            res = parse_messages(rbuild._text(p.stdout))
            return results, timeouts, "evaluation failed: " + "; ".join(res.errors[:2])[:400]
        if timed_out is not None:
            timeouts += 1
            start = next((i for i, (k, _) in enumerate(exprs) if k == timed_out), len(exprs)) + 1
        else:
            start += len(batch)
    return results, timeouts, None

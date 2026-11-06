import CIR
import EquivLean.Bridge.Cir.ValSwap

/-!
# Caller pointers: lemmas for symbolic execution

Facts used by `equiv_cir` for pointer arguments (see `EquivLean.Bridge.Cir.PtrArgs`):

* `ptrValid`, reads and writes through `null`, function, vtable and integer (`addr`) pointers
  compute;
* `IsCaller b` tags a block of the caller (a split pointer argument);
* a typed `int` load of a caller integer, in the range of the type or read through its
  signed/unsigned counterpart, is one path with the value `wrap s w x` (`load_int_merge_s`/`_u`);
* `Val.set?` at two leaf positions commutes (`Val.set?_swap`, `EquivLean.Bridge.Cir.ValSwap`), for
  programs that write the same locations in another order.
-/

namespace EquivLean.Cir

open CIR

theorem ptrValid_loc (m : Mem) (b : Nat) (p : List PathElem) :
    ptrValid m (.loc b p) = (m.live? b).isSome := rfl
theorem ptrValid_null (m : Mem) : ptrValid m .null = true := rfl
theorem ptrValid_fn (m : Mem) (s : String) : ptrValid m (.fn s) = true := rfl
theorem ptrValid_vtable (m : Mem) (s : String) (i k : Nat) : ptrValid m (.vtable s i k) = true := rfl
theorem read?_fn (m : Mem) (s : String) : m.read? (.fn s) = none := rfl
theorem read?_vtable (m : Mem) (s : String) (i k : Nat) : m.read? (.vtable s i k) = none := rfl
theorem write?_fn (m : Mem) (s : String) (w : Val) : m.write? (.fn s) w = none := rfl
theorem write?_vtable (m : Mem) (s : String) (i k : Nat) (w : Val) :
    m.write? (.vtable s i k) w = none := rfl
theorem ptrValid_addr (m : Mem) (a : Int) : ptrValid m (.addr a) = true := rfl
theorem read?_addr (m : Mem) (a : Int) : m.read? (.addr a) = none := rfl
theorem write?_addr (m : Mem) (a : Int) (w : Val) : m.write? (.addr a) w = none := rfl

attribute [cir_exec] ptrValid_loc ptrValid_null ptrValid_fn ptrValid_vtable read?_fn read?_vtable
  write?_fn write?_vtable ptrValid_addr read?_addr write?_addr

/-- Tag of a block of the caller (introduced when a pointer argument is split). -/
def IsCaller (_b : Nat) : Prop := True

/-- A typed `int` load of the integer `x` (cirlean's `loadTy`, after `fitsTy` and the type's
`match`): in the range of the type, or read through the unsigned counterpart (C11 6.5p7), the value
is `wrap true w x` either way.  Pointer mode uses it (and `load_int_merge_u`) as a rewrite rule of
both programs, so that a caller integer of unknown range is read on one path, not two. -/
theorem load_int_merge_s (w : Nat) (x : Int) (msg : String) (hw : 0 < w) :
    (if inRange true w x = true then (Res.ok (Val.int x) : Res Val)
      else if inRange false w x = true then Res.ok (Val.int (wrap true w x)) else Res.ub msg) =
    if (inRange true w x || inRange false w x) = true then Res.ok (Val.int (wrap true w x))
      else Res.ub msg := by
  by_cases h1 : inRange true w x = true
  · simp [h1, wrap_of_bounds hw (inRange_eq_true_iff.mp h1)]
  · simp [h1]

/-- `load_int_merge_s` for an unsigned type (read through the signed counterpart). -/
theorem load_int_merge_u (w : Nat) (x : Int) (msg : String) (hw : 0 < w) :
    (if inRange false w x = true then (Res.ok (Val.int x) : Res Val)
      else if inRange true w x = true then Res.ok (Val.int (wrap false w x)) else Res.ub msg) =
    if (inRange false w x || inRange true w x) = true then Res.ok (Val.int (wrap false w x))
      else Res.ub msg := by
  by_cases h1 : inRange false w x = true
  · simp [h1, wrap_of_bounds hw (inRange_eq_true_iff.mp h1)]
  · simp [h1]

end EquivLean.Cir

namespace EquivLean.Cir.Tactic

open Lean Meta Simp

/-- `M.findGlobal? s` for a symbol `s` that is not a literal (a `vtable` pointer argument):
`none` when the lookup computes to `none` whatever `s` is (no globals). -/
simproc [cir_exec] reduceFindGlobalNone (CIR.Module.findGlobal? _ _) := fun e => do
  unless e.isAppOfArity ``CIR.Module.findGlobal? 2 do return .continue
  if (e.getArg! 1).isStringLit then return .continue
  let r ← whnfD e
  unless r.isAppOfArity ``Option.none 1 do return .continue
  return .done { expr := r, proof? := some (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)) }

end EquivLean.Cir.Tactic

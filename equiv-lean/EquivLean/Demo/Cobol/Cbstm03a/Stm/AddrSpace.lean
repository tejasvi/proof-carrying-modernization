/-
# The constructed z/OS address space of the CBSTM03A runs (variant B)

`tools/coverage/creastmt_inputs.py`: the PSA at address 0 holds the TCB address 0x1000 at offset 536,
the TCB holds the TIOT address 0x2000 at offset 12, the TIOT starts with the job, step and procedure
step names (EBCDIC) and has one 20-byte entry per DD statement of the job step (length 20, DD name,
UCB address or zeros for SYSOUT data sets), then 24 zero bytes; every other address holds 0.
-/
import Cobol

namespace Cobol.Stm

def psaSeg : List UInt8 := List.replicate 536 0 ++ [0, 0, 16, 0]
def tcbSeg : List UInt8 := List.replicate 12 0 ++ [0, 0, 32, 0]
def ent (dd : List UInt8) (ucb : List UInt8) : List UInt8 := [20, 0, 0, 0] ++ dd ++ [0, 0, 0, 0, 0] ++ ucb
def jobNames : List UInt8 :=
  [195, 217, 197, 193, 226, 227, 212, 227] ++ [226, 227, 197, 215, 240, 244, 240, 64] ++ List.replicate 8 64
def ddEntries : List UInt8 :=
  ent [226, 227, 197, 215, 211, 201, 194, 64] [0, 122, 16] ++
  ent [226, 232, 226, 215, 217, 201, 213, 227] [0, 0, 0] ++
  ent [226, 232, 226, 214, 228, 227, 64, 64] [0, 0, 0] ++
  ent [227, 217, 213, 231, 198, 201, 211, 197] [0, 122, 19] ++
  ent [231, 217, 197, 198, 198, 201, 211, 197] [0, 122, 20] ++
  ent [193, 195, 195, 227, 198, 201, 211, 197] [0, 122, 21] ++
  ent [195, 228, 226, 227, 198, 201, 211, 197] [0, 122, 22] ++
  ent [226, 227, 212, 227, 198, 201, 211, 197] [0, 122, 23] ++
  ent [200, 227, 212, 211, 198, 201, 211, 197] [0, 122, 24]
def tiotSeg : List UInt8 := jobNames ++ ddEntries ++ List.replicate 24 0

/-- The address space. -/
@[irreducible] def asp (a : Nat) : UInt8 :=
  if a < 540 then psaSeg.getD a 0
  else if 4096 ≤ a ∧ a < 4112 then tcbSeg.getD (a - 4096) 0
  else if 8192 ≤ a ∧ a < 8420 then tiotSeg.getD (a - 8192) 0 else 0

set_option maxRecDepth 100000 in
theorem tiotSeg_length : tiotSeg.length = 228 := by decide +kernel

/-- A read inside a region written with bytes `f 0, …, f (n-1)` (what `SET ADDRESS OF` stores:
the address space from the pointer on) is again such a list: no expansion of the region. -/
theorem read_write_map_range (m : Mem) (o q n j : Nat) (f : Nat → UInt8)
    (h1 : o ≤ q) (h2 : q + j ≤ o + n) (hs : o + n ≤ m.size) :
    (m.write o ((List.range n).map f)).read q j = (List.range j).map (fun i => f (q - o + i)) := by
  rw [Mem.read_write_within m o q j _ h1 (by simp; omega) (by simp; omega)]
  apply List.ext_getElem
  · simp; omega
  · intro i hi _
    simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]

/-! Values of the address space at the addresses CBSTM03A reads, one theorem each, so that a
proof by symbolic execution only cites them (the kernel never evaluates `asp` there). -/
set_option maxRecDepth 100000
theorem asp_536 : asp 536 = 0 := by unfold asp; decide +kernel
theorem asp_537 : asp 537 = 0 := by unfold asp; decide +kernel
theorem asp_538 : asp 538 = 16 := by unfold asp; decide +kernel
theorem asp_539 : asp 539 = 0 := by unfold asp; decide +kernel
theorem asp_4108 : asp 4108 = 0 := by unfold asp; decide +kernel
theorem asp_4109 : asp 4109 = 0 := by unfold asp; decide +kernel
theorem asp_4110 : asp 4110 = 32 := by unfold asp; decide +kernel
theorem asp_4111 : asp 4111 = 0 := by unfold asp; decide +kernel

/-! Small reads of a region: the bytes one by one. -/
theorem map_range_1 {α : Type} (f : Nat → α) : (List.range 1).map f = [f 0] := rfl
theorem map_range_2 {α : Type} (f : Nat → α) : (List.range 2).map f = [f 0, f 1] := rfl
theorem map_range_3 {α : Type} (f : Nat → α) : (List.range 3).map f = [f 0, f 1, f 2] := rfl
theorem map_range_4 {α : Type} (f : Nat → α) : (List.range 4).map f = [f 0, f 1, f 2, f 3] := rfl
theorem map_range_8 {α : Type} (f : Nat → α) :
    (List.range 8).map f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := rfl

/-- Evaluate `asp a` on a numeral `a`, proved by `decide` (no kernel unfolding of `asp` inside
the enclosing proof term). -/
simproc_decl reduceAsp (asp _) := fun e => do
  let_expr asp a := e | return .continue
  let some _ ← Lean.Meta.getNatValue? a | return .continue
  let v ← unsafe Lean.Meta.evalExpr UInt8 (Lean.mkConst ``UInt8) e
  let ve := Lean.toExpr v
  let eq ← Lean.Meta.mkEq e ve
  let d ← Lean.Meta.mkDecide eq
  let pf := Lean.mkApp3 (Lean.mkConst ``of_decide_eq_true) eq d.appArg!
    (← Lean.Meta.mkEqRefl (Lean.mkConst ``Bool.true))
  return .done { expr := ve, proof? := some pf }

end Cobol.Stm

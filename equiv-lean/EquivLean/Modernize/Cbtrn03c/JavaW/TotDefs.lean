import EquivLean.Modernize.Cbtrn03c.JavaW.EditDefs

/-!
# CBTRN03C → Java: the texts of the total lines

The total line and the dashes as `writePageTotals`, `writeAccountTotals`, `writeGrandTotals`
build them, and `add11` on the totals.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

/-- A total line: the label padded to `w`, `n` dots, the edited total. -/
def totalLineJ (label : JStr) (w n : Nat) (v : I64) : JStr :=
  fixJ label w ++ (repJ (BitVec.ofNat 16 46) n ++
    editJ (decide (v.toInt < 0)) true (v.toInt.natAbs % 100000000000))

/-- 133 dashes. -/
def dashJ : JStr := repJ (BitVec.ofNat 16 45) 133

/-- `add11`. -/
def add11J (a b : I64) : I64 := (a + b).srem (BitVec.ofInt 64 100000000000)

theorem setWidth_46 : BitVec.setWidth 16 (46#32) = BitVec.ofNat 16 46 := by decide
theorem setWidth_45 : BitVec.setWidth 16 (45#32) = BitVec.ofNat 16 45 := by decide

end EquivLean.Modernize.Cbtrn03c.Java

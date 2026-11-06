import EquivLean.Modernize.Cbtrn03c.JavaTop.RunW

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `run`, the processing date as the symbolic execution writes it
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-- The first 10 characters of `TRAN-PROC-TS` (the `substring(0, 10)` of `run`), as `simp` writes the
field: the model's `tDate`. -/
theorem take10_procTs (t : List EquivLean.Cobol.Rec.FVal) :
    List.take 10 (Model.strOf (t[12]?.getD (EquivLean.Cobol.Rec.FVal.num 0))) = Model.tDate t := by
  simp only [Model.tDate, List.getD_eq_getElem?_getD]
  rfl

end EquivLean.Modernize.Cbtrn03c.Java.Top

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

theorem tdate_len_of {t : List EquivLean.Cobol.Rec.FVal}
    (h : (Model.strOf (t.getD 12 default)).length = 26) : (Model.tDate t).length = 10 := by
  simp only [Model.tDate, List.length_take, h]
  rfl

end EquivLean.Modernize.Cbtrn03c.Java.Top

import EquivLean.Modernize.Cbtrn03c.JavaTop.Glue1

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java, top layer: facts of valid records (2)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

theorem xacct_bound {x : List EquivLean.Cobol.Rec.FVal} (hx : CardXrefRecord.Valid x) :
    (Model.xAcct x).natAbs < 100000000000 := by
  obtain ⟨card, cust, acct, fill, rfl, -, -, -, h, -⟩ := Glue.xref_shape hx
  simpa [Model.xAcct, Model.numOf] using h

theorem xAcct_xref0 : Model.xAcct Model.xref0 = 0 := rfl

end EquivLean.Modernize.Cbtrn03c.Java.Top

import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib
import EquivLean.Modernize.Cbtrn03c.Glue

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java, top layer: facts of valid records
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

theorem tamt_bound {t : List EquivLean.Cobol.Rec.FVal} (ht : TranRecord.Valid t) :
    (Model.tAmt t).natAbs < 100000000000 := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, -, -, -,
    -, -, -, h7, -⟩ := Glue.tran_shape ht
  simpa [Model.tAmt, Model.numOf] using h7

end EquivLean.Modernize.Cbtrn03c.Java.Top

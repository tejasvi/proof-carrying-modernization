import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH4b

/-!
# CBTRN02C → Java: the texts of the model

The trailer of each reject reason, the record schemas of the model and of the statement.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The trailer of a reject record with reason `k`. -/
def trailerJ (k : I32) : JStr := zpadJ k.toInt.natAbs 4 ++ fitJ (descJ k.toInt) 76

set_option maxRecDepth 20000 in
theorem trailer_100 : trailerJ 100#32 =
    cp037Str (CardDemo.Cbtrn02c.trailer 100 CardDemo.Cbtrn02c.badCardDesc) := by decide

set_option maxRecDepth 20000 in
theorem trailer_101 : trailerJ 101#32 =
    cp037Str (CardDemo.Cbtrn02c.trailer 101 CardDemo.Cbtrn02c.noAcctDesc) := by decide

set_option maxRecDepth 20000 in
theorem trailer_102 : trailerJ 102#32 =
    cp037Str (CardDemo.Cbtrn02c.trailer 102 CardDemo.Cbtrn02c.overLimitDesc) := by decide

set_option maxRecDepth 20000 in
theorem trailer_103 : trailerJ 103#32 =
    cp037Str (CardDemo.Cbtrn02c.trailer 103 CardDemo.Cbtrn02c.expiredDesc) := by decide

theorem dal_schema : Model.DalytranRecord = DalytranRecord := rfl
theorem tran_schema : Model.TranRecord = TranRecord := rfl
theorem acct_schema : Model.AccountRecord = AccountRecord := rfl
theorem tcat_schema : Model.TranCatBalRecord = TranCatBalRecord := rfl
theorem xref_schema : Model.CardXrefRecord = CardXrefRecord := rfl
theorem rej_schema : Model.RejectRecord = RejectRecord := rfl

end EquivLean.Modernize.Cbtrn02c.Java

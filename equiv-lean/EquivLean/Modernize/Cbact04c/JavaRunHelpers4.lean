import EquivLean.Modernize.Cbact04c.JavaRunHelpers2

/-!
# CBACT04C → Java: `displayTcb`

The line DISPLAYed for a category record: account id (11 digits), type, category (4 digits),
balance (11 digits, overpunched sign), filler.
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

def fmtZonedSig : MethodSig :=
  { cls := "Cbact04c", ret := .cls "java.lang.String", name := "fmtZoned",
    params := [.prim .long, .prim .int] }

/-- The line `displayTcb` builds from the fields of a category record. -/
def tcbLine (a : I64) (ty : JStr) (c b : I64) (f : JStr) : JStr :=
  zpadJ a.toInt.natAbs 11 ++ ty ++ zpadJ c.toInt.natAbs 4 ++ zonedJ b.toInt 11 ++ f

abbrev displayTcbRef : MethodRef := Gen.Cbact04c.«displayTcb(Cbact04c$TranCatBalRecord)».ref

def displayTcbSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (a c b : I64) (tv fv : Addr)
       (ty f : JStr), args = [.ref x] ∧
     σ.heap x = some (.plain "Cbact04c$TranCatBalRecord" fs) ∧
     Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatAcctId") = some (.long a) ∧
     Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatTypeCd") = some (.ref tv) ∧
     σ.heap tv = some (.str ty) ∧
     Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatCd") = some (.long c) ∧
     Fields.get fs ("Cbact04c$TranCatBalRecord", "tranCatBal") = some (.long b) ∧
     Fields.get fs ("Cbact04c$TranCatBalRecord", "filler1") = some (.ref fv) ∧
     σ.heap fv = some (.str f) ∧
     -9223372036854775808 < a.toInt ∧ -9223372036854775808 < c.toInt ∧
     -9223372036854775808 < b.toInt ∧ σ.initOf "Cbact04c" = .done)
  (fun args σ r σ' => ∀ (x : Addr) (fs : List (FieldKey × Value)) (a c b : I64) (tv fv : Addr)
       (ty f : JStr), args = [.ref x] →
     σ.heap x = some (.plain "Cbact04c$TranCatBalRecord" fs) →
     Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatAcctId") = some (.long a) →
     Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatTypeCd") = some (.ref tv) →
     σ.heap tv = some (.str ty) →
     Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatCd") = some (.long c) →
     Fields.get fs ("Cbact04c$TranCatBalRecord", "tranCatBal") = some (.long b) →
     Fields.get fs ("Cbact04c$TranCatBalRecord", "filler1") = some (.ref fv) →
     σ.heap fv = some (.str f) →
     ∃ y, r = some (.ref y) ∧ σ'.heap y = some (.str (tcbLine a ty c b f)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem initOf_eq_of_inits {σ σ' : State} (h : σ'.inits = σ.inits) (c : ClassName) :
    σ'.initOf c = σ.initOf c := by
  simp [State.initOf, h]

def displayTcbC : Contracts := [(fmtUSig, fmtUSpec), (fmtZonedSig, fmtZonedSpec)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem displayTcb_vc : MethodVC Gen.prog displayTcbC.env 0 displayTcbRef displayTcbSpec [] 60 := by
  jverify [displayTcbSpec, displayTcbC, fmtUSig, fmtUSpec, fmtZonedSig, fmtZonedSpec, Grows,
    tcbLine, Native.valueOfArg, Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, strOf,
    initOf_eq_of_inits]
  all_goals (first | exact targets_static rfl rfl | skip)

end EquivLean.Modernize.Cbact04c.Java

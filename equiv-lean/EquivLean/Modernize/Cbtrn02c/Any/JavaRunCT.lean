import EquivLean.Modernize.Cbtrn02c.Any.JavaRunC

/-!
# CBTRN02C → Java: the constructor of `Cbtrn02c$TranRecord`
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The constructor of `Cbtrn02c$TranRecord`: its arguments into the fields of `this`. -/
def ctorTRSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
     args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] ∧ σ.heap x = some (.plain "Cbtrn02c$TranRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranId") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranTypeCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranCatCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranSource") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranDesc") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranAmt") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranMerchantId") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranMerchantName") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranMerchantCity") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranMerchantZip") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranCardNum") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranOrigTs") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "tranProcTs") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
     args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] → σ.heap x = some (.plain "Cbtrn02c$TranRecord" fs) →
     σ'.heap x = some (.plain "Cbtrn02c$TranRecord"
         (setFields "Cbtrn02c$TranRecord" fs ["tranId", "tranTypeCd", "tranCatCd", "tranSource", "tranDesc", "tranAmt", "tranMerchantId", "tranMerchantName", "tranMerchantCity", "tranMerchantZip", "tranCardNum", "tranOrigTs", "tranProcTs", "filler1"]
           [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14])) ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

abbrev ctorTRRef : MethodRef := Gen.«Cbtrn02c$TranRecord».«<init>(java.lang.String,java.lang.String,long,java.lang.String,java.lang.String,long,long,java.lang.String,java.lang.String,java.lang.String,java.lang.String,java.lang.String,java.lang.String,java.lang.String)».ref

def ctorTRSig : MethodSig :=
  { cls := "Cbtrn02c$TranRecord", ret := .void, name := "<init>",
    params := [.cls "java.lang.String", .cls "java.lang.String", .prim .long, .cls "java.lang.String", .cls "java.lang.String", .prim .long, .prim .long, .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String"] }

def ctorTRInv4 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
    args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] → σ0.heap x = some (.plain "Cbtrn02c$TranRecord" fs) →
    fr.get 3 = some (.ref x) ∧ fr.get 4 = some v1 ∧ fr.get 5 = some v2 ∧ fr.get 0 = some v3 ∧ fr.get 6 = some v4 ∧ fr.get 7 = some v5 ∧ fr.get 1 = some v6 ∧ fr.get 2 = some v7 ∧ fr.get 8 = some v8 ∧ fr.get 9 = some v9 ∧ fr.get 10 = some v10 ∧ fr.get 11 = some v11 ∧ fr.get 12 = some v12 ∧ fr.get 13 = some v13 ∧ fr.get 14 = some v14 ∧
    (∀ y, y ≠ x → σ.heap y = σ0.heap y) ∧ σ.next = σ0.next ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    σ.heap x = some (.plain "Cbtrn02c$TranRecord" (setFields "Cbtrn02c$TranRecord" fs ["tranId", "tranTypeCd", "tranCatCd", "tranSource"] [v1, v2, v3, v4]))

def ctorTRInv8 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
    args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] → σ0.heap x = some (.plain "Cbtrn02c$TranRecord" fs) →
    fr.get 3 = some (.ref x) ∧ fr.get 4 = some v1 ∧ fr.get 5 = some v2 ∧ fr.get 0 = some v3 ∧ fr.get 6 = some v4 ∧ fr.get 7 = some v5 ∧ fr.get 1 = some v6 ∧ fr.get 2 = some v7 ∧ fr.get 8 = some v8 ∧ fr.get 9 = some v9 ∧ fr.get 10 = some v10 ∧ fr.get 11 = some v11 ∧ fr.get 12 = some v12 ∧ fr.get 13 = some v13 ∧ fr.get 14 = some v14 ∧
    (∀ y, y ≠ x → σ.heap y = σ0.heap y) ∧ σ.next = σ0.next ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    σ.heap x = some (.plain "Cbtrn02c$TranRecord" (setFields "Cbtrn02c$TranRecord" fs ["tranId", "tranTypeCd", "tranCatCd", "tranSource", "tranDesc", "tranAmt", "tranMerchantId", "tranMerchantName"] [v1, v2, v3, v4, v5, v6, v7, v8]))

def ctorTRInv12 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
    args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] → σ0.heap x = some (.plain "Cbtrn02c$TranRecord" fs) →
    fr.get 3 = some (.ref x) ∧ fr.get 4 = some v1 ∧ fr.get 5 = some v2 ∧ fr.get 0 = some v3 ∧ fr.get 6 = some v4 ∧ fr.get 7 = some v5 ∧ fr.get 1 = some v6 ∧ fr.get 2 = some v7 ∧ fr.get 8 = some v8 ∧ fr.get 9 = some v9 ∧ fr.get 10 = some v10 ∧ fr.get 11 = some v11 ∧ fr.get 12 = some v12 ∧ fr.get 13 = some v13 ∧ fr.get 14 = some v14 ∧
    (∀ y, y ≠ x → σ.heap y = σ0.heap y) ∧ σ.next = σ0.next ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    σ.heap x = some (.plain "Cbtrn02c$TranRecord" (setFields "Cbtrn02c$TranRecord" fs ["tranId", "tranTypeCd", "tranCatCd", "tranSource", "tranDesc", "tranAmt", "tranMerchantId", "tranMerchantName", "tranMerchantCity", "tranMerchantZip", "tranCardNum", "tranOrigTs"] [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]))

/-- Cut points after 4, 8 and 12 of the 14 field stores (one stretch of 14 exceeds the simp budget). -/
def ctorTRInv : Invariants := [(20, ctorTRInv4), (24, ctorTRInv8), (28, ctorTRInv12)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorTR_vc : MethodVC Gen.prog (fun _ => none) 0 ctorTRRef ctorTRSpec ctorTRInv 40 := by
  jverify [ctorTRSpec, ctorTRInv, ctorTRInv4, ctorTRInv8, ctorTRInv12, setFields, Fields.get_set,
    fields_get_cons, fields_get_nil, narrow_long, narrow_cls]

theorem ctorTR_sat : Sat Gen.prog ctorTRRef ctorTRSpec := MethodVC.sat ctorTR_vc

set_option maxHeartbeats 0 in
theorem ctorTR_ok : ContractOK Gen.prog ctorTRSig ctorTRSpec := by
  jcontract_ok [ctorTR_sat]

end EquivLean.Modernize.Cbtrn02c.Java

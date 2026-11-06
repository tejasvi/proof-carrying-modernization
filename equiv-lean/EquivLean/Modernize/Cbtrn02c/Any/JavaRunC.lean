import EquivLean.Modernize.Cbtrn02c.Any.JavaRunLib

/-!
# CBTRN02C → Java: the record constructors

Each record class's constructor stores its arguments into the fields of `this`, in declaration
order.  Its callers (the copies, `run`) use these contracts instead of inlining the bodies
(java04b's form; inlining the 13-argument constructors blew up the symbolic states).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The field list after storing `vs` into the fields `keys` (class `cls`), in order. -/
def setFields (cls : ClassName) : List (FieldKey × Value) → List String → List Value →
    List (FieldKey × Value)
  | fs, k :: ks, v :: vs => setFields cls (Fields.set fs (cls, k) v) ks vs
  | fs, _, _ => fs

theorem targets_special {P : Program} {sig : MethodSig} {m : MethodRef}
    (h : P.selectSpecial sig = .jimple m) (hb : m.decl.body.isSome = true) : Targets P sig m :=
  ⟨Or.inr (Or.inl h), hb⟩

/-- The constructor of `Cbtrn02c$AccountRecord`: its arguments into the fields of `this`. -/
def ctorACSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Value),
     args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] ∧ σ.heap x = some (.plain "Cbtrn02c$AccountRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctId") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctActiveStatus") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctCurrBal") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctCreditLimit") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctCashCreditLimit") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctOpenDate") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctExpiraionDate") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctReissueDate") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctCurrCycCredit") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctCurrCycDebit") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctAddrZip") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "acctGroupId") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$AccountRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Value),
     args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] → σ.heap x = some (.plain "Cbtrn02c$AccountRecord" fs) →
     σ'.heap x = some (.plain "Cbtrn02c$AccountRecord"
         (setFields "Cbtrn02c$AccountRecord" fs ["acctId", "acctActiveStatus", "acctCurrBal", "acctCreditLimit", "acctCashCreditLimit", "acctOpenDate", "acctExpiraionDate", "acctReissueDate", "acctCurrCycCredit", "acctCurrCycDebit", "acctAddrZip", "acctGroupId", "filler1"]
           [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13])) ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

abbrev ctorACRef : MethodRef := Gen.«Cbtrn02c$AccountRecord».«<init>(long,java.lang.String,long,long,long,java.lang.String,java.lang.String,java.lang.String,long,long,java.lang.String,java.lang.String,java.lang.String)».ref

def ctorACSig : MethodSig :=
  { cls := "Cbtrn02c$AccountRecord", ret := .void, name := "<init>",
    params := [.prim .long, .cls "java.lang.String", .prim .long, .prim .long, .prim .long, .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String", .prim .long, .prim .long, .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String"] }

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorAC_vc : MethodVC Gen.prog (fun _ => none) 0 ctorACRef ctorACSpec [] 40 := by
  jverify [ctorACSpec, setFields, Fields.get_set, narrow_long, narrow_cls]

theorem ctorAC_sat : Sat Gen.prog ctorACRef ctorACSpec := MethodVC.sat ctorAC_vc

set_option maxHeartbeats 0 in
theorem ctorAC_ok : ContractOK Gen.prog ctorACSig ctorACSpec := by
  jcontract_ok [ctorAC_sat]

/-- The constructor of `Cbtrn02c$CardXrefRecord`: its arguments into the fields of `this`. -/
def ctorXRSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 : Value),
     args = [.ref x, v1, v2, v3, v4] ∧ σ.heap x = some (.plain "Cbtrn02c$CardXrefRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$CardXrefRecord", "xrefCardNum") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$CardXrefRecord", "xrefCustId") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$CardXrefRecord", "xrefAcctId") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$CardXrefRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 : Value),
     args = [.ref x, v1, v2, v3, v4] → σ.heap x = some (.plain "Cbtrn02c$CardXrefRecord" fs) →
     σ'.heap x = some (.plain "Cbtrn02c$CardXrefRecord"
         (setFields "Cbtrn02c$CardXrefRecord" fs ["xrefCardNum", "xrefCustId", "xrefAcctId", "filler1"]
           [v1, v2, v3, v4])) ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

abbrev ctorXRRef : MethodRef := Gen.«Cbtrn02c$CardXrefRecord».«<init>(java.lang.String,long,long,java.lang.String)».ref

def ctorXRSig : MethodSig :=
  { cls := "Cbtrn02c$CardXrefRecord", ret := .void, name := "<init>",
    params := [.cls "java.lang.String", .prim .long, .prim .long, .cls "java.lang.String"] }

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorXR_vc : MethodVC Gen.prog (fun _ => none) 0 ctorXRRef ctorXRSpec [] 40 := by
  jverify [ctorXRSpec, setFields, Fields.get_set, narrow_long, narrow_cls]

theorem ctorXR_sat : Sat Gen.prog ctorXRRef ctorXRSpec := MethodVC.sat ctorXR_vc

set_option maxHeartbeats 0 in
theorem ctorXR_ok : ContractOK Gen.prog ctorXRSig ctorXRSpec := by
  jcontract_ok [ctorXR_sat]

/-- The constructor of `Cbtrn02c$TranCatBalRecord`: its arguments into the fields of `this`. -/
def ctorTCSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 : Value),
     args = [.ref x, v1, v2, v3, v4, v5] ∧ σ.heap x = some (.plain "Cbtrn02c$TranCatBalRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranCatBalRecord", "trancatAcctId") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranCatBalRecord", "trancatTypeCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranCatBalRecord", "trancatCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranCatBalRecord", "tranCatBal") = some w) ∧
     (∃ w, Fields.get fs ("Cbtrn02c$TranCatBalRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 : Value),
     args = [.ref x, v1, v2, v3, v4, v5] → σ.heap x = some (.plain "Cbtrn02c$TranCatBalRecord" fs) →
     σ'.heap x = some (.plain "Cbtrn02c$TranCatBalRecord"
         (setFields "Cbtrn02c$TranCatBalRecord" fs ["trancatAcctId", "trancatTypeCd", "trancatCd", "tranCatBal", "filler1"]
           [v1, v2, v3, v4, v5])) ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

abbrev ctorTCRef : MethodRef := Gen.«Cbtrn02c$TranCatBalRecord».«<init>(long,java.lang.String,long,long,java.lang.String)».ref

def ctorTCSig : MethodSig :=
  { cls := "Cbtrn02c$TranCatBalRecord", ret := .void, name := "<init>",
    params := [.prim .long, .cls "java.lang.String", .prim .long, .prim .long, .cls "java.lang.String"] }

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorTC_vc : MethodVC Gen.prog (fun _ => none) 0 ctorTCRef ctorTCSpec [] 40 := by
  jverify [ctorTCSpec, setFields, Fields.get_set, narrow_long, narrow_cls]

theorem ctorTC_sat : Sat Gen.prog ctorTCRef ctorTCSpec := MethodVC.sat ctorTC_vc

set_option maxHeartbeats 0 in
theorem ctorTC_ok : ContractOK Gen.prog ctorTCSig ctorTCSpec := by
  jcontract_ok [ctorTC_sat]

end EquivLean.Modernize.Cbtrn02c.Java

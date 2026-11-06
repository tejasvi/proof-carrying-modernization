import EquivLean.Modernize.Cbact04c.JavaRunLib

/-!
# CBACT04C → Java: the contracts of the record constructors

Each record class's constructor stores its arguments into the fields of `this`, in declaration
order. Its callers (`copy*`, `run`) use these contracts instead of inlining the bodies; the
proofs are in `CtorProofs`.
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-- The constructor of `Cbact04c$TranCatBalRecord`: its arguments into the fields of `this`. -/
def ctorTCSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 : Value),
     args = [.ref x, v1, v2, v3, v4, v5] ∧ σ.heap x = some (.plain "Cbact04c$TranCatBalRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatAcctId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatTypeCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranCatBalRecord", "tranCatBal") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranCatBalRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 : Value),
     args = [.ref x, v1, v2, v3, v4, v5] → σ.heap x = some (.plain "Cbact04c$TranCatBalRecord" fs) →
     ∃ fs', σ'.heap x = some (.plain "Cbact04c$TranCatBalRecord" fs') ∧
       Fields.get fs' ("Cbact04c$TranCatBalRecord", "trancatAcctId") = some v1 ∧
       Fields.get fs' ("Cbact04c$TranCatBalRecord", "trancatTypeCd") = some v2 ∧
       Fields.get fs' ("Cbact04c$TranCatBalRecord", "trancatCd") = some v3 ∧
       Fields.get fs' ("Cbact04c$TranCatBalRecord", "tranCatBal") = some v4 ∧
       Fields.get fs' ("Cbact04c$TranCatBalRecord", "filler1") = some v5 ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

abbrev ctorTCRef : MethodRef := Gen.«Cbact04c$TranCatBalRecord».«<init>(long,java.lang.String,long,long,java.lang.String)».ref


/-- The constructor of `Cbact04c$CardXrefRecord`: its arguments into the fields of `this`. -/
def ctorXCSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 : Value),
     args = [.ref x, v1, v2, v3, v4] ∧ σ.heap x = some (.plain "Cbact04c$CardXrefRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbact04c$CardXrefRecord", "xrefCardNum") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$CardXrefRecord", "xrefCustId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$CardXrefRecord", "xrefAcctId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$CardXrefRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 : Value),
     args = [.ref x, v1, v2, v3, v4] → σ.heap x = some (.plain "Cbact04c$CardXrefRecord" fs) →
     ∃ fs', σ'.heap x = some (.plain "Cbact04c$CardXrefRecord" fs') ∧
       Fields.get fs' ("Cbact04c$CardXrefRecord", "xrefCardNum") = some v1 ∧
       Fields.get fs' ("Cbact04c$CardXrefRecord", "xrefCustId") = some v2 ∧
       Fields.get fs' ("Cbact04c$CardXrefRecord", "xrefAcctId") = some v3 ∧
       Fields.get fs' ("Cbact04c$CardXrefRecord", "filler1") = some v4 ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

abbrev ctorXCRef : MethodRef := Gen.«Cbact04c$CardXrefRecord».«<init>(java.lang.String,long,long,java.lang.String)».ref


/-- The constructor of `Cbact04c$AccountRecord`: its arguments into the fields of `this`. -/
def ctorACSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Value),
     args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] ∧ σ.heap x = some (.plain "Cbact04c$AccountRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctActiveStatus") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctCurrBal") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctCreditLimit") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctCashCreditLimit") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctOpenDate") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctExpiraionDate") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctReissueDate") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctCurrCycCredit") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctCurrCycDebit") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctAddrZip") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "acctGroupId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$AccountRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Value),
     args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] → σ.heap x = some (.plain "Cbact04c$AccountRecord" fs) →
     ∃ fs', σ'.heap x = some (.plain "Cbact04c$AccountRecord" fs') ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctId") = some v1 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctActiveStatus") = some v2 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctCurrBal") = some v3 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctCreditLimit") = some v4 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctCashCreditLimit") = some v5 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctOpenDate") = some v6 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctExpiraionDate") = some v7 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctReissueDate") = some v8 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctCurrCycCredit") = some v9 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctCurrCycDebit") = some v10 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctAddrZip") = some v11 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "acctGroupId") = some v12 ∧
       Fields.get fs' ("Cbact04c$AccountRecord", "filler1") = some v13 ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

abbrev ctorACRef : MethodRef := Gen.«Cbact04c$AccountRecord».«<init>(long,java.lang.String,long,long,long,java.lang.String,java.lang.String,java.lang.String,long,long,java.lang.String,java.lang.String,java.lang.String)».ref


/-- The constructor of `Cbact04c$DisGroupRecord`: its arguments into the fields of `this`. -/
def ctorDCSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 : Value),
     args = [.ref x, v1, v2, v3, v4, v5] ∧ σ.heap x = some (.plain "Cbact04c$DisGroupRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbact04c$DisGroupRecord", "disAcctGroupId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$DisGroupRecord", "disTranTypeCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$DisGroupRecord", "disTranCatCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$DisGroupRecord", "disIntRate") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$DisGroupRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 : Value),
     args = [.ref x, v1, v2, v3, v4, v5] → σ.heap x = some (.plain "Cbact04c$DisGroupRecord" fs) →
     ∃ fs', σ'.heap x = some (.plain "Cbact04c$DisGroupRecord" fs') ∧
       Fields.get fs' ("Cbact04c$DisGroupRecord", "disAcctGroupId") = some v1 ∧
       Fields.get fs' ("Cbact04c$DisGroupRecord", "disTranTypeCd") = some v2 ∧
       Fields.get fs' ("Cbact04c$DisGroupRecord", "disTranCatCd") = some v3 ∧
       Fields.get fs' ("Cbact04c$DisGroupRecord", "disIntRate") = some v4 ∧
       Fields.get fs' ("Cbact04c$DisGroupRecord", "filler1") = some v5 ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

abbrev ctorDCRef : MethodRef := Gen.«Cbact04c$DisGroupRecord».«<init>(java.lang.String,java.lang.String,long,long,java.lang.String)».ref


/-- The constructor of `Cbact04c$TranRecord`: its arguments into the fields of `this`. -/
def ctorRCSpec : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
     args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] ∧ σ.heap x = some (.plain "Cbact04c$TranRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranTypeCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranCatCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranSource") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranDesc") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranAmt") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranMerchantId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranMerchantName") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranMerchantCity") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranMerchantZip") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranCardNum") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranOrigTs") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "tranProcTs") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
     args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] → σ.heap x = some (.plain "Cbact04c$TranRecord" fs) →
     ∃ fs', σ'.heap x = some (.plain "Cbact04c$TranRecord" fs') ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranId") = some v1 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranTypeCd") = some v2 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranCatCd") = some v3 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranSource") = some v4 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranDesc") = some v5 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranAmt") = some v6 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantId") = some v7 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantName") = some v8 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantCity") = some v9 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantZip") = some v10 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranCardNum") = some v11 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranOrigTs") = some v12 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "tranProcTs") = some v13 ∧
       Fields.get fs' ("Cbact04c$TranRecord", "filler1") = some v14 ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

abbrev ctorRCRef : MethodRef := Gen.«Cbact04c$TranRecord».«<init>(java.lang.String,java.lang.String,long,java.lang.String,java.lang.String,long,long,java.lang.String,java.lang.String,java.lang.String,java.lang.String,java.lang.String,java.lang.String,java.lang.String)».ref


def ctorTCSig : MethodSig :=
  { cls := "Cbact04c$TranCatBalRecord", ret := .void, name := "<init>",
    params := [.prim .long, .cls "java.lang.String", .prim .long, .prim .long, .cls "java.lang.String"] }
def ctorXCSig : MethodSig :=
  { cls := "Cbact04c$CardXrefRecord", ret := .void, name := "<init>",
    params := [.cls "java.lang.String", .prim .long, .prim .long, .cls "java.lang.String"] }
def ctorACSig : MethodSig :=
  { cls := "Cbact04c$AccountRecord", ret := .void, name := "<init>",
    params := [.prim .long, .cls "java.lang.String", .prim .long, .prim .long, .prim .long,
      .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String", .prim .long,
      .prim .long, .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String"] }
def ctorDCSig : MethodSig :=
  { cls := "Cbact04c$DisGroupRecord", ret := .void, name := "<init>",
    params := [.cls "java.lang.String", .cls "java.lang.String", .prim .long, .prim .long,
      .cls "java.lang.String"] }
def ctorRCSig : MethodSig :=
  { cls := "Cbact04c$TranRecord", ret := .void, name := "<init>",
    params := [.cls "java.lang.String", .cls "java.lang.String", .prim .long, .cls "java.lang.String",
      .cls "java.lang.String", .prim .long, .prim .long, .cls "java.lang.String",
      .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String",
      .cls "java.lang.String", .cls "java.lang.String", .cls "java.lang.String"] }

end EquivLean.Modernize.Cbact04c.Java

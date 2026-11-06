import EquivLean.Modernize.Cbact04c.Every.JavaRunCtorSpecs

/-!
# CBACT04C → Java: the record constructors satisfy their contracts

The two long constructors (13 and 14 fields) are verified with cut points after every four
stores (the symbolic execution of one long straight-line body is slow).
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorTC_vc : MethodVC Gen.prog (fun _ => none) 0 ctorTCRef ctorTCSpec [] 40 := by
  jverify [ctorTCSpec, fields_get_set, fields_get_cons, fields_get_nil, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorXC_vc : MethodVC Gen.prog (fun _ => none) 0 ctorXCRef ctorXCSpec [] 40 := by
  jverify [ctorXCSpec, fields_get_set, fields_get_cons, fields_get_nil, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorDC_vc : MethodVC Gen.prog (fun _ => none) 0 ctorDCRef ctorDCSpec [] 40 := by
  jverify [ctorDCSpec, fields_get_set, fields_get_cons, fields_get_nil, narrow_long, narrow_cls]

def ctorACInv19 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Value),
    args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] → σ0.heap x = some (.plain "Cbact04c$AccountRecord" fs) →
    fr.get 6 = some (.ref x) ∧ fr.get 0 = some v1 ∧ fr.get 7 = some v2 ∧ fr.get 1 = some v3 ∧ fr.get 2 = some v4 ∧ fr.get 3 = some v5 ∧ fr.get 8 = some v6 ∧ fr.get 9 = some v7 ∧ fr.get 10 = some v8 ∧ fr.get 4 = some v9 ∧ fr.get 5 = some v10 ∧ fr.get 11 = some v11 ∧ fr.get 12 = some v12 ∧ fr.get 13 = some v13 ∧
    (∀ y, y ≠ x → σ.heap y = σ0.heap y) ∧ σ.next = σ0.next ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    ∃ fs', σ.heap x = some (.plain "Cbact04c$AccountRecord" fs') ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctId") = some v1 ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctActiveStatus") = some v2 ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctCurrBal") = some v3 ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctCreditLimit") = some v4 ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctCashCreditLimit") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctOpenDate") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctExpiraionDate") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctReissueDate") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctCurrCycCredit") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctCurrCycDebit") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctAddrZip") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctGroupId") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "filler1") = some w)

def ctorACInv23 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Value),
    args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] → σ0.heap x = some (.plain "Cbact04c$AccountRecord" fs) →
    fr.get 6 = some (.ref x) ∧ fr.get 0 = some v1 ∧ fr.get 7 = some v2 ∧ fr.get 1 = some v3 ∧ fr.get 2 = some v4 ∧ fr.get 3 = some v5 ∧ fr.get 8 = some v6 ∧ fr.get 9 = some v7 ∧ fr.get 10 = some v8 ∧ fr.get 4 = some v9 ∧ fr.get 5 = some v10 ∧ fr.get 11 = some v11 ∧ fr.get 12 = some v12 ∧ fr.get 13 = some v13 ∧
    (∀ y, y ≠ x → σ.heap y = σ0.heap y) ∧ σ.next = σ0.next ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    ∃ fs', σ.heap x = some (.plain "Cbact04c$AccountRecord" fs') ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctId") = some v1 ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctActiveStatus") = some v2 ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctCurrBal") = some v3 ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctCreditLimit") = some v4 ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctCashCreditLimit") = some v5 ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctOpenDate") = some v6 ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctExpiraionDate") = some v7 ∧
      Fields.get fs' ("Cbact04c$AccountRecord", "acctReissueDate") = some v8 ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctCurrCycCredit") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctCurrCycDebit") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctAddrZip") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "acctGroupId") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "filler1") = some w)

def ctorACInv27 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Value),
    args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] → σ0.heap x = some (.plain "Cbact04c$AccountRecord" fs) →
    fr.get 6 = some (.ref x) ∧ fr.get 0 = some v1 ∧ fr.get 7 = some v2 ∧ fr.get 1 = some v3 ∧ fr.get 2 = some v4 ∧ fr.get 3 = some v5 ∧ fr.get 8 = some v6 ∧ fr.get 9 = some v7 ∧ fr.get 10 = some v8 ∧ fr.get 4 = some v9 ∧ fr.get 5 = some v10 ∧ fr.get 11 = some v11 ∧ fr.get 12 = some v12 ∧ fr.get 13 = some v13 ∧
    (∀ y, y ≠ x → σ.heap y = σ0.heap y) ∧ σ.next = σ0.next ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    ∃ fs', σ.heap x = some (.plain "Cbact04c$AccountRecord" fs') ∧
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
      (∃ w, Fields.get fs' ("Cbact04c$AccountRecord", "filler1") = some w)

def ctorACInv : Invariants := [(19, ctorACInv19), (23, ctorACInv23), (27, ctorACInv27)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorAC_vc : MethodVC Gen.prog (fun _ => none) 0 ctorACRef ctorACSpec ctorACInv 40 := by
  jverify [ctorACSpec, ctorACInv, ctorACInv19, ctorACInv23, ctorACInv27, fields_get_set,
    fields_get_cons, fields_get_nil, narrow_long, narrow_cls]

def ctorRCInv20 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
    args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] → σ0.heap x = some (.plain "Cbact04c$TranRecord" fs) →
    fr.get 3 = some (.ref x) ∧ fr.get 4 = some v1 ∧ fr.get 5 = some v2 ∧ fr.get 0 = some v3 ∧ fr.get 6 = some v4 ∧ fr.get 7 = some v5 ∧ fr.get 1 = some v6 ∧ fr.get 2 = some v7 ∧ fr.get 8 = some v8 ∧ fr.get 9 = some v9 ∧ fr.get 10 = some v10 ∧ fr.get 11 = some v11 ∧ fr.get 12 = some v12 ∧ fr.get 13 = some v13 ∧ fr.get 14 = some v14 ∧
    (∀ y, y ≠ x → σ.heap y = σ0.heap y) ∧ σ.next = σ0.next ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    ∃ fs', σ.heap x = some (.plain "Cbact04c$TranRecord" fs') ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranId") = some v1 ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranTypeCd") = some v2 ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranCatCd") = some v3 ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranSource") = some v4 ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranDesc") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranAmt") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantId") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantName") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantCity") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantZip") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranCardNum") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranOrigTs") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranProcTs") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "filler1") = some w)

def ctorRCInv24 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
    args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] → σ0.heap x = some (.plain "Cbact04c$TranRecord" fs) →
    fr.get 3 = some (.ref x) ∧ fr.get 4 = some v1 ∧ fr.get 5 = some v2 ∧ fr.get 0 = some v3 ∧ fr.get 6 = some v4 ∧ fr.get 7 = some v5 ∧ fr.get 1 = some v6 ∧ fr.get 2 = some v7 ∧ fr.get 8 = some v8 ∧ fr.get 9 = some v9 ∧ fr.get 10 = some v10 ∧ fr.get 11 = some v11 ∧ fr.get 12 = some v12 ∧ fr.get 13 = some v13 ∧ fr.get 14 = some v14 ∧
    (∀ y, y ≠ x → σ.heap y = σ0.heap y) ∧ σ.next = σ0.next ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    ∃ fs', σ.heap x = some (.plain "Cbact04c$TranRecord" fs') ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranId") = some v1 ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranTypeCd") = some v2 ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranCatCd") = some v3 ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranSource") = some v4 ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranDesc") = some v5 ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranAmt") = some v6 ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantId") = some v7 ∧
      Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantName") = some v8 ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantCity") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranMerchantZip") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranCardNum") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranOrigTs") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranProcTs") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "filler1") = some w)

def ctorRCInv28 (args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∀ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
    args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] → σ0.heap x = some (.plain "Cbact04c$TranRecord" fs) →
    fr.get 3 = some (.ref x) ∧ fr.get 4 = some v1 ∧ fr.get 5 = some v2 ∧ fr.get 0 = some v3 ∧ fr.get 6 = some v4 ∧ fr.get 7 = some v5 ∧ fr.get 1 = some v6 ∧ fr.get 2 = some v7 ∧ fr.get 8 = some v8 ∧ fr.get 9 = some v9 ∧ fr.get 10 = some v10 ∧ fr.get 11 = some v11 ∧ fr.get 12 = some v12 ∧ fr.get 13 = some v13 ∧ fr.get 14 = some v14 ∧
    (∀ y, y ≠ x → σ.heap y = σ0.heap y) ∧ σ.next = σ0.next ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics ∧
    ∃ fs', σ.heap x = some (.plain "Cbact04c$TranRecord" fs') ∧
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
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "tranProcTs") = some w) ∧
      (∃ w, Fields.get fs' ("Cbact04c$TranRecord", "filler1") = some w)

def ctorRCInv : Invariants := [(20, ctorRCInv20), (24, ctorRCInv24), (28, ctorRCInv28)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorRC_vc : MethodVC Gen.prog (fun _ => none) 0 ctorRCRef ctorRCSpec ctorRCInv 40 := by
  jverify [ctorRCSpec, ctorRCInv, ctorRCInv20, ctorRCInv24, ctorRCInv28, fields_get_set,
    fields_get_cons, fields_get_nil, narrow_long, narrow_cls]

end EquivLean.Modernize.Cbact04c.Java

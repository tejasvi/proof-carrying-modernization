import EquivLean.Modernize.Cbact04c.JavaRunCallSpecs
import EquivLean.Modernize.Cbact04c.JavaRunCtorSpecs

/-!
# CBACT04C → Java: the record constructors' contracts as `run` uses them

`ctorXXF`: `ctorXXSpec` with the postcondition's universals fixed by the arguments (no `fs`
universal with a heap premise), from `ctorXXSpec` by the consequence rule.
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java


def ctorTCF : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 : Value),
     args = [.ref x, v1, v2, v3, v4, v5] ∧ σ.heap x = some (.plain "Cbact04c$TranCatBalRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatAcctId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatTypeCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranCatBalRecord", "trancatCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranCatBalRecord", "tranCatBal") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$TranCatBalRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (v1 v2 v3 v4 v5 : Value),
     args = [.ref x, v1, v2, v3, v4, v5] →
     ∃ fs', σ'.heap x = some (.plain "Cbact04c$TranCatBalRecord" fs') ∧
       Fields.get fs' ("Cbact04c$TranCatBalRecord", "trancatAcctId") = some v1 ∧
       Fields.get fs' ("Cbact04c$TranCatBalRecord", "trancatTypeCd") = some v2 ∧
       Fields.get fs' ("Cbact04c$TranCatBalRecord", "trancatCd") = some v3 ∧
       Fields.get fs' ("Cbact04c$TranCatBalRecord", "tranCatBal") = some v4 ∧
       Fields.get fs' ("Cbact04c$TranCatBalRecord", "filler1") = some v5 ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

theorem ctorTCF_of_sat (h : Sat Gen.prog ctorTCRef ctorTCSpec) : Sat Gen.prog ctorTCRef ctorTCF := by
  refine sat_conseq h (fun args σ hp => hp) ?_
  intro args σ o hp hpost
  obtain ⟨x, fs, v1, v2, v3, v4, v5, rfl, hx, -⟩ := hp
  cases o with
  | normal r σ' =>
    intro x' v1' v2' v3' v4' v5' hargs
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    exact hpost x fs v1 v2 v3 v4 v5 rfl hx
  | exc e σ' => exact hpost
  | wrong msg => exact hpost


def ctorXCF : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 : Value),
     args = [.ref x, v1, v2, v3, v4] ∧ σ.heap x = some (.plain "Cbact04c$CardXrefRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbact04c$CardXrefRecord", "xrefCardNum") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$CardXrefRecord", "xrefCustId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$CardXrefRecord", "xrefAcctId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$CardXrefRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (v1 v2 v3 v4 : Value),
     args = [.ref x, v1, v2, v3, v4] →
     ∃ fs', σ'.heap x = some (.plain "Cbact04c$CardXrefRecord" fs') ∧
       Fields.get fs' ("Cbact04c$CardXrefRecord", "xrefCardNum") = some v1 ∧
       Fields.get fs' ("Cbact04c$CardXrefRecord", "xrefCustId") = some v2 ∧
       Fields.get fs' ("Cbact04c$CardXrefRecord", "xrefAcctId") = some v3 ∧
       Fields.get fs' ("Cbact04c$CardXrefRecord", "filler1") = some v4 ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

theorem ctorXCF_of_sat (h : Sat Gen.prog ctorXCRef ctorXCSpec) : Sat Gen.prog ctorXCRef ctorXCF := by
  refine sat_conseq h (fun args σ hp => hp) ?_
  intro args σ o hp hpost
  obtain ⟨x, fs, v1, v2, v3, v4, rfl, hx, -⟩ := hp
  cases o with
  | normal r σ' =>
    intro x' v1' v2' v3' v4' hargs
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
    exact hpost x fs v1 v2 v3 v4 rfl hx
  | exc e σ' => exact hpost
  | wrong msg => exact hpost


def ctorACF : Spec := Spec.of
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
  (fun args σ r σ' => ∀ (x : Addr) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 : Value),
     args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13] →
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

theorem ctorACF_of_sat (h : Sat Gen.prog ctorACRef ctorACSpec) : Sat Gen.prog ctorACRef ctorACF := by
  refine sat_conseq h (fun args σ hp => hp) ?_
  intro args σ o hp hpost
  obtain ⟨x, fs, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, rfl, hx, -⟩ := hp
  cases o with
  | normal r σ' =>
    intro x' v1' v2' v3' v4' v5' v6' v7' v8' v9' v10' v11' v12' v13' hargs
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    exact hpost x fs v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 rfl hx
  | exc e σ' => exact hpost
  | wrong msg => exact hpost


def ctorDCF : Spec := Spec.of
  (fun args σ => ∃ (x : Addr) (fs : List (FieldKey × Value)) (v1 v2 v3 v4 v5 : Value),
     args = [.ref x, v1, v2, v3, v4, v5] ∧ σ.heap x = some (.plain "Cbact04c$DisGroupRecord" fs) ∧
     (∃ w, Fields.get fs ("Cbact04c$DisGroupRecord", "disAcctGroupId") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$DisGroupRecord", "disTranTypeCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$DisGroupRecord", "disTranCatCd") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$DisGroupRecord", "disIntRate") = some w) ∧
     (∃ w, Fields.get fs ("Cbact04c$DisGroupRecord", "filler1") = some w))
  (fun args σ r σ' => ∀ (x : Addr) (v1 v2 v3 v4 v5 : Value),
     args = [.ref x, v1, v2, v3, v4, v5] →
     ∃ fs', σ'.heap x = some (.plain "Cbact04c$DisGroupRecord" fs') ∧
       Fields.get fs' ("Cbact04c$DisGroupRecord", "disAcctGroupId") = some v1 ∧
       Fields.get fs' ("Cbact04c$DisGroupRecord", "disTranTypeCd") = some v2 ∧
       Fields.get fs' ("Cbact04c$DisGroupRecord", "disTranCatCd") = some v3 ∧
       Fields.get fs' ("Cbact04c$DisGroupRecord", "disIntRate") = some v4 ∧
       Fields.get fs' ("Cbact04c$DisGroupRecord", "filler1") = some v5 ∧
       (∀ y, y ≠ x → σ'.heap y = σ.heap y) ∧ σ'.next = σ.next ∧ σ'.inits = σ.inits ∧
       σ'.statics = σ.statics ∧ r = none)

theorem ctorDCF_of_sat (h : Sat Gen.prog ctorDCRef ctorDCSpec) : Sat Gen.prog ctorDCRef ctorDCF := by
  refine sat_conseq h (fun args σ hp => hp) ?_
  intro args σ o hp hpost
  obtain ⟨x, fs, v1, v2, v3, v4, v5, rfl, hx, -⟩ := hp
  cases o with
  | normal r σ' =>
    intro x' v1' v2' v3' v4' v5' hargs
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    exact hpost x fs v1 v2 v3 v4 v5 rfl hx
  | exc e σ' => exact hpost
  | wrong msg => exact hpost


def ctorRCF : Spec := Spec.of
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
  (fun args σ r σ' => ∀ (x : Addr) (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 : Value),
     args = [.ref x, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14] →
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

theorem ctorRCF_of_sat (h : Sat Gen.prog ctorRCRef ctorRCSpec) : Sat Gen.prog ctorRCRef ctorRCF := by
  refine sat_conseq h (fun args σ hp => hp) ?_
  intro args σ o hp hpost
  obtain ⟨x, fs, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, rfl, hx, -⟩ := hp
  cases o with
  | normal r σ' =>
    intro x' v1' v2' v3' v4' v5' v6' v7' v8' v9' v10' v11' v12' v13' v14' hargs
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    exact hpost x fs v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 rfl hx
  | exc e σ' => exact hpost
  | wrong msg => exact hpost


end EquivLean.Modernize.Cbact04c.Java

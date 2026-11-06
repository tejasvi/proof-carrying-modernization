import EquivLean.Modernize.Cbtrn02c.Any.JavaRunR1
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunCT

/-!
# CBTRN02C → Java: copying account, transaction and cross-reference records
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The fields of `Cbtrn02c$AccountRecord`. -/
def acKeys : List FieldKey :=
  [("Cbtrn02c$AccountRecord", "acctId"), ("Cbtrn02c$AccountRecord", "acctActiveStatus"), ("Cbtrn02c$AccountRecord", "acctCurrBal"), ("Cbtrn02c$AccountRecord", "acctCreditLimit"), ("Cbtrn02c$AccountRecord", "acctCashCreditLimit"), ("Cbtrn02c$AccountRecord", "acctOpenDate"), ("Cbtrn02c$AccountRecord", "acctExpiraionDate"), ("Cbtrn02c$AccountRecord", "acctReissueDate"), ("Cbtrn02c$AccountRecord", "acctCurrCycCredit"), ("Cbtrn02c$AccountRecord", "acctCurrCycDebit"), ("Cbtrn02c$AccountRecord", "acctAddrZip"), ("Cbtrn02c$AccountRecord", "acctGroupId"), ("Cbtrn02c$AccountRecord", "filler1")]

/-- The fields of `Cbtrn02c$TranRecord`. -/
def trKeys : List FieldKey :=
  [("Cbtrn02c$TranRecord", "tranId"), ("Cbtrn02c$TranRecord", "tranTypeCd"), ("Cbtrn02c$TranRecord", "tranCatCd"), ("Cbtrn02c$TranRecord", "tranSource"), ("Cbtrn02c$TranRecord", "tranDesc"), ("Cbtrn02c$TranRecord", "tranAmt"), ("Cbtrn02c$TranRecord", "tranMerchantId"), ("Cbtrn02c$TranRecord", "tranMerchantName"), ("Cbtrn02c$TranRecord", "tranMerchantCity"), ("Cbtrn02c$TranRecord", "tranMerchantZip"), ("Cbtrn02c$TranRecord", "tranCardNum"), ("Cbtrn02c$TranRecord", "tranOrigTs"), ("Cbtrn02c$TranRecord", "tranProcTs"), ("Cbtrn02c$TranRecord", "filler1")]

/-- The fields of `Cbtrn02c$CardXrefRecord`. -/
def xrKeys : List FieldKey :=
  [("Cbtrn02c$CardXrefRecord", "xrefCardNum"), ("Cbtrn02c$CardXrefRecord", "xrefCustId"), ("Cbtrn02c$CardXrefRecord", "xrefAcctId"), ("Cbtrn02c$CardXrefRecord", "filler1")]

abbrev copyAccountRef : MethodRef := Gen.Cbtrn02c.«copyAccount(Cbtrn02c$AccountRecord)».ref

def copyAccountSpec : Spec := Spec.of
  (fun args σ => ∃ (a : Addr) (fs : List (FieldKey × Value)), args = [.ref a] ∧
     σ.heap a = some (.plain "Cbtrn02c$AccountRecord" fs) ∧
     (∀ k ∈ acKeys, (Fields.get fs k).isSome) ∧ σ.initOf "Cbtrn02c$AccountRecord" = .done)
  (fun args σ r σ' => ∀ (a : Addr) (fs : List (FieldKey × Value)), args = [.ref a] →
     σ.heap a = some (.plain "Cbtrn02c$AccountRecord" fs) →
     ∃ x fs', r = some (.ref x) ∧ σ.next ≤ x ∧
       σ'.heap x = some (.plain "Cbtrn02c$AccountRecord" fs') ∧
       SameFields acKeys fs' fs ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

/-- The callee of `copyAccount`: the constructor (by its contract). -/
def copyAccountC : Contracts := [(ctorACSig, ctorACSpec)]

theorem copyAccountC_valid : Valid Gen.prog copyAccountC.env := by
  apply Contracts.valid_of_ok
  simp only [copyAccountC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ctorAC_ok

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem copyAccount_vc : MethodVC Gen.prog copyAccountC.env 0 copyAccountRef copyAccountSpec [] 40 := by
  refine ⟨Gen.Cbtrn02c.«copyAccount(Cbtrn02c$AccountRecord)», rfl, ?_⟩
  intro args σ0 hpre
  obtain ⟨a, fs, rfl, ha, hall, hi⟩ := hpre
  simp only [acKeys, List.forall_mem_cons, List.forall_mem_nil, and_true, Option.isSome_iff_exists] at hall
  obtain ⟨⟨v1, e1⟩, ⟨v2, e2⟩, ⟨v3, e3⟩, ⟨v4, e4⟩, ⟨v5, e5⟩, ⟨v6, e6⟩, ⟨v7, e7⟩, ⟨v8, e8⟩, ⟨v9, e9⟩, ⟨v10, e10⟩, ⟨v11, e11⟩, ⟨v12, e12⟩, ⟨v13, e13⟩⟩ := hall
  refine ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩
  jvc [copyAccountSpec, Invariants.inst, copyAccountC, ctorACSig, ctorACSpec, Grows, narrow_long, narrow_cls]
  all_goals first
    | exact targets_special rfl rfl
    | skip
  rename_i hA
  obtain ⟨hA1, hA2, hA3, hA4, hA5, -⟩ := hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (if_pos rfl)
  refine ⟨_, hA1, ?_, ⟨by rw [hA3]; jomega, fun z hz => ?_⟩, hA4, hA5, ?_⟩
  · unfold SameFields
    simp (config := { decide := true }) only [acKeys, setFields, List.forall_mem_cons,
      List.forall_mem_nil, Fields.get_set, ite_true, ite_false, and_true, true_and, and_self, List.not_mem_nil, false_implies, implies_true, *]
  · rw [hA2 z (by jomega), if_neg (by jomega)]
  · simp only [State.initOf, hA4]

abbrev copyTranRef : MethodRef := Gen.Cbtrn02c.«copyTran(Cbtrn02c$TranRecord)».ref

def copyTranSpec : Spec := Spec.of
  (fun args σ => ∃ (a : Addr) (fs : List (FieldKey × Value)), args = [.ref a] ∧
     σ.heap a = some (.plain "Cbtrn02c$TranRecord" fs) ∧
     (∀ k ∈ trKeys, (Fields.get fs k).isSome) ∧ σ.initOf "Cbtrn02c$TranRecord" = .done)
  (fun args σ r σ' => ∀ (a : Addr) (fs : List (FieldKey × Value)), args = [.ref a] →
     σ.heap a = some (.plain "Cbtrn02c$TranRecord" fs) →
     ∃ x fs', r = some (.ref x) ∧ σ.next ≤ x ∧
       σ'.heap x = some (.plain "Cbtrn02c$TranRecord" fs') ∧
       SameFields trKeys fs' fs ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

/-- The callee of `copyTran`: the constructor (by its contract). -/
def copyTranC : Contracts := [(ctorTRSig, ctorTRSpec)]

theorem copyTranC_valid : Valid Gen.prog copyTranC.env := by
  apply Contracts.valid_of_ok
  simp only [copyTranC, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ctorTR_ok

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem copyTran_vc : MethodVC Gen.prog copyTranC.env 0 copyTranRef copyTranSpec [] 40 := by
  refine ⟨Gen.Cbtrn02c.«copyTran(Cbtrn02c$TranRecord)», rfl, ?_⟩
  intro args σ0 hpre
  obtain ⟨a, fs, rfl, ha, hall, hi⟩ := hpre
  simp only [trKeys, List.forall_mem_cons, List.forall_mem_nil, and_true, Option.isSome_iff_exists] at hall
  obtain ⟨⟨v1, e1⟩, ⟨v2, e2⟩, ⟨v3, e3⟩, ⟨v4, e4⟩, ⟨v5, e5⟩, ⟨v6, e6⟩, ⟨v7, e7⟩, ⟨v8, e8⟩, ⟨v9, e9⟩, ⟨v10, e10⟩, ⟨v11, e11⟩, ⟨v12, e12⟩, ⟨v13, e13⟩, ⟨v14, e14⟩⟩ := hall
  refine ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩
  jvc [copyTranSpec, Invariants.inst, copyTranC, ctorTRSig, ctorTRSpec, Grows, narrow_long, narrow_cls]
  all_goals first
    | exact targets_special rfl rfl
    | skip
  rename_i hA
  obtain ⟨hA1, hA2, hA3, hA4, hA5, -⟩ := hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (if_pos rfl)
  refine ⟨_, hA1, ?_, ⟨by rw [hA3]; jomega, fun z hz => ?_⟩, hA4, hA5, ?_⟩
  · unfold SameFields
    simp (config := { decide := true }) only [trKeys, setFields, List.forall_mem_cons,
      List.forall_mem_nil, Fields.get_set, ite_true, ite_false, and_true, true_and, and_self, List.not_mem_nil, false_implies, implies_true, *]
  · rw [hA2 z (by jomega), if_neg (by jomega)]
  · simp only [State.initOf, hA4]

end EquivLean.Modernize.Cbtrn02c.Java

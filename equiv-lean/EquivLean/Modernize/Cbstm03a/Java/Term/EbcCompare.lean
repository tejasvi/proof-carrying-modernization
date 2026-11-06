import EquivLean.Modernize.Cbstm03a.Java.Term.Ebc

/-!
# CBSTM03A → Java, termination: `ebcCompare`

`ebcCompare(a, b)` compares position by position up to the longer length (loop head statement 12, `i < n`;
locals `$i0` (`n`) 3, `i` 4, `a` 7, `b` 8), with calls of `ebc` (`ebcSpecT`). Variant `n - i`. Frame contract (two
non-null strings of `int` length, `Cbstm03a` initialized, `CP037` an `int` array of length 256): an `int` result,
the state unchanged.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Term

def ebcCompareSpecT : Spec := Spec.of
  (fun args σ => ∃ av bv, args = [av, bv] ∧ StrArgN σ av ∧ StrArgN σ bv ∧ InitA σ ∧ CpOk σ)
  (fun _ σ r σ' => (∃ k : I32, r = some (.int k)) ∧ σ' = σ)

def ebcCompareInvT : Invariants := [(12, fun args σ0 fr σ => ∀ av bv, args = [av, bv] →
  ∃ (xa xb : Addr) (sa sb : JStr) (n i : I32), av = .ref xa ∧ bv = .ref xb ∧ fr.get 7 = some (.ref xa) ∧
    fr.get 8 = some (.ref xb) ∧ σ.heap xa = some (.str sa) ∧ σ.heap xb = some (.str sb) ∧
    sa.length < 2147483648 ∧ sb.length < 2147483648 ∧ fr.get 3 = some (.int n) ∧ fr.get 4 = some (.int i) ∧
    0 ≤ i.toInt ∧ σ = σ0)]

def ebcCompareVarT (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 3, fr.get 4 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

def ebcCompareCalleesT : Contracts := [(ebcSig, ebcSpecT)]

theorem ebcCompareCalleesT_ok : ∀ p ∈ ebcCompareCalleesT, ContractOK Gen.prog p.1 p.2 := by
  simp only [ebcCompareCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ebc_okT
theorem ebcCompareCalleesT_term : ∀ p ∈ ebcCompareCalleesT, ContractTerm Gen.prog p.1 p.2 := by
  simp only [ebcCompareCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ebc_ctermT

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ebcCompare_vcT :
    MethodVC Gen.prog ebcCompareCalleesT.env 0 ebcCompareRef ebcCompareSpecT ebcCompareInvT 60 := by
  jverify [ite_nat_ne, ebcCompareSpecT, ebcCompareInvT, ebcCompareCalleesT, ebcSig, ebcSpecT, StrArgN,
    Int.ofNat_eq_coe]
  all_goals jvc [ite_nat_ne, ebcCompareSpecT, ebcCompareInvT, ebcCompareCalleesT, ebcSig, ebcSpecT, StrArgN,
    Int.ofNat_eq_coe]
  all_goals (unfold CpOk; exact ⟨_, _, by assumption, by assumption, by assumption⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ebcCompare_thinT : ThinVC Gen.prog ebcCompareCalleesT.env 0 ebcCompareRef ebcCompareSpecT ebcCompareInvT
    (fun _ => ebcCompareVarT) 60 := by
  jthin [ite_nat_ne, ebcCompareSpecT, ebcCompareInvT, ebcCompareCalleesT, ebcSig, ebcSpecT, StrArgN,
    Int.ofNat_eq_coe, ebcCompareVarT]
  all_goals jvc [ite_nat_ne, ebcCompareSpecT, ebcCompareInvT, ebcCompareCalleesT, ebcSig, ebcSpecT, StrArgN,
    Int.ofNat_eq_coe, ebcCompareVarT]

theorem ebcCompare_termT : ∀ args σ, ebcCompareSpecT.pre args σ → MTerm Gen.prog ebcCompareRef args σ :=
  mterm_of_thin ebcCompareCalleesT_ok ebcCompareCalleesT_term ebcCompare_vcT ebcCompare_thinT

theorem ebcCompare_satT : Sat Gen.prog ebcCompareRef ebcCompareSpecT :=
  sat_of_table ebcCompareCalleesT_ok ebcCompare_vcT

set_option maxHeartbeats 4000000 in
theorem ebcCompare_ctermT : ContractTerm Gen.prog ebcCompareSig ebcCompareSpecT := by
  jcontract_term [ebcCompare_termT]
set_option maxHeartbeats 4000000 in
theorem ebcCompare_okT : ContractOK Gen.prog ebcCompareSig ebcCompareSpecT := by jcontract_ok [ebcCompare_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.ebcCompare_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.ebcCompare_okT

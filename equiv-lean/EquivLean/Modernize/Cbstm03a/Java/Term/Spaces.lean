import EquivLean.Modernize.Cbstm03a.Java.Term.Repeat

/-!
# CBSTM03A → Java, termination: `spaces`

`spaces(n)` is `repeat(' ', n)` (no loop), answered by `repeatSpecT`. Frame contract (`n ≤ 2^30`, `Cbstm03a`
initialized): a new string of length `max n 0`, `GrowsT`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

def spacesSpecT : Spec := Spec.of (fun args σ => ∃ n : I32, args = [.int n] ∧ n.toInt ≤ 1073741824 ∧ InitA σ)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] → StrResL σ r σ' n.toInt.toNat ∧ GrowsT σ σ')

def spacesCalleesT : Contracts := [(repeatSig, repeatSpecT)]

theorem spacesCalleesT_ok : ∀ p ∈ spacesCalleesT, ContractOK Gen.prog p.1 p.2 := by
  simp only [spacesCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact repeat_okT
theorem spacesCalleesT_term : ∀ p ∈ spacesCalleesT, ContractTerm Gen.prog p.1 p.2 := by
  simp only [spacesCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact repeat_ctermT

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem spaces_vcT : MethodVC Gen.prog spacesCalleesT.env 0 spacesRef spacesSpecT [] 20 := by
  jverify [ite_nat_ne, spacesSpecT, spacesCalleesT, repeatSig, repeatSpecT, StrResL, GrowsT, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem spaces_thinT :
    ThinVC Gen.prog spacesCalleesT.env 0 spacesRef spacesSpecT [] (fun _ _ _ _ _ => 0) 20 := by
  jthin [ite_nat_ne, spacesSpecT, spacesCalleesT, repeatSig, repeatSpecT]

theorem spaces_termT : ∀ args σ, spacesSpecT.pre args σ → MTerm Gen.prog spacesRef args σ :=
  mterm_of_thin spacesCalleesT_ok spacesCalleesT_term spaces_vcT spaces_thinT

theorem spaces_satT : Sat Gen.prog spacesRef spacesSpecT := sat_of_table spacesCalleesT_ok spaces_vcT

set_option maxHeartbeats 4000000 in
theorem spaces_ctermT : ContractTerm Gen.prog spacesSig spacesSpecT := by jcontract_term [spaces_termT]
set_option maxHeartbeats 4000000 in
theorem spaces_okT : ContractOK Gen.prog spacesSig spacesSpecT := by jcontract_ok [spaces_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.spaces_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.spaces_okT

import EquivLean.Modernize.Cbstm03a.Java.Term.Spaces

/-!
# CBSTM03A → Java, termination: `fix`

`fix(s, n)` (no loop) cuts or pads `s` (`""` for `null`) with `spaces(n - len)`, answered by `spacesSpecT`.
Frame contract (`s` null or a string of `int` length, `0 ≤ n ≤ 2^30`, `Cbstm03a` initialized): a string of
length `n` (new, or `s` itself), `GrowsT`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows jstr_empty)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

def fixSpecT : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrArg σ sv ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 1073741824 ∧ InitA σ)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
    (∃ x s, r = some (.ref x) ∧ σ'.heap x = some (.str s) ∧ s.length = n.toInt.toNat) ∧ GrowsT σ σ')

def fixCalleesT : Contracts := [(spacesSig, spacesSpecT)]

theorem fixCalleesT_ok : ∀ p ∈ fixCalleesT, ContractOK Gen.prog p.1 p.2 := by
  simp only [fixCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact spaces_okT
theorem fixCalleesT_term : ∀ p ∈ fixCalleesT, ContractTerm Gen.prog p.1 p.2 := by
  simp only [fixCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact spaces_ctermT

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem fix_vcT : MethodVC Gen.prog fixCalleesT.env 0 fixRef fixSpecT [] 30 := by
  set_option jimple.modelContracts true in
  jverify [ite_nat_ne, fixSpecT, fixCalleesT, spacesSig, spacesSpecT, StrArg, StrResL, GrowsT, Grows, jstr_empty]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem fix_thinT : ThinVC Gen.prog fixCalleesT.env 0 fixRef fixSpecT [] (fun _ _ _ _ _ => 0) 30 := by
  set_option jimple.modelContracts true in
  jthin [ite_nat_ne, fixSpecT, fixCalleesT, spacesSig, spacesSpecT, StrArg, StrResL, GrowsT, Grows, jstr_empty]

theorem fix_termT : ∀ args σ, fixSpecT.pre args σ → MTerm Gen.prog fixRef args σ :=
  mterm_of_thin fixCalleesT_ok fixCalleesT_term fix_vcT fix_thinT

theorem fix_satT : Sat Gen.prog fixRef fixSpecT := sat_of_table fixCalleesT_ok fix_vcT

set_option maxHeartbeats 4000000 in
theorem fix_ctermT : ContractTerm Gen.prog fixSig fixSpecT := by jcontract_term [fix_termT]
set_option maxHeartbeats 4000000 in
theorem fix_okT : ContractOK Gen.prog fixSig fixSpecT := by jcontract_ok [fix_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.fix_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.fix_okT

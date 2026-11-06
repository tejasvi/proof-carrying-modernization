import EquivLean.Modernize.Cbstm03a.Java.Term.Defs

/-!
# CBSTM03A → Java, termination: `pow10`

`pow10(n)` multiplies `p` by 10 while `i < n` (loop head statement 3; locals `n` 0, `i` 1, `p` 2). Variant
`n - i`. Frame contract: a `long` result, the state unchanged.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Term

def pow10SpecT : Spec := Spec.of (fun args _ => ∃ n : I32, args = [.int n])
  (fun _ σ r σ' => (∃ p : I64, r = some (.long p)) ∧ σ' = σ)

def pow10InvT : Invariants := [(3, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ (i : I32) (p : I64), fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧ fr.get 2 = some (.long p) ∧
    σ = σ0)]

def pow10VarT (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem pow10_vcT : MethodVC Gen.prog (fun _ => none) 0 pow10Ref pow10SpecT pow10InvT 40 := by
  jverify [ite_nat_ne, pow10SpecT, pow10InvT]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem pow10_thinT :
    ThinVC Gen.prog (fun _ => none) 0 pow10Ref pow10SpecT pow10InvT (fun _ => pow10VarT) 40 := by
  jthin [ite_nat_ne, pow10SpecT, pow10InvT, pow10VarT]

theorem pow10_termT : ∀ args σ, pow10SpecT.pre args σ → MTerm Gen.prog pow10Ref args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) pow10_vcT pow10_thinT)

theorem pow10_satT : Sat Gen.prog pow10Ref pow10SpecT := pow10_vcT.sat

set_option maxHeartbeats 4000000 in
theorem pow10_ctermT : ContractTerm Gen.prog pow10Sig pow10SpecT := by jcontract_term [pow10_termT]
set_option maxHeartbeats 4000000 in
theorem pow10_okT : ContractOK Gen.prog pow10Sig pow10SpecT := by jcontract_ok [pow10_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.pow10_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.pow10_okT

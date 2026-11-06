import EquivLean.Modernize.Cbstm03a.Java.Term.Defs

/-!
# CBSTM03A → Java, termination: `repeat`

`repeat(ch, n)` doubles `s` (from `String.valueOf(ch)`, length 1) while `s.length() < n` (loop head statement 5;
locals `n` 0, `$i0` 1, `ch` 2, `s` 3). `length()` is the length mod 2^32, so the loop ends only while the
lengths stay below 2^31: the precondition asks `n ≤ 2^30` (every call in `Cbstm03a` has `n ≤ 1000`). Variant
`2^31 - s.length`. Frame contract: a new string of length `max n 0`, `GrowsT`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

def repeatSpecT : Spec := Spec.of (fun args _ => ∃ (ch n : I32), args = [.int ch, .int n] ∧ n.toInt ≤ 1073741824)
  (fun args σ r σ' => ∀ (ch n : I32), args = [.int ch, .int n] → StrResL σ r σ' n.toInt.toNat ∧ GrowsT σ σ')

def repeatInvT : Invariants := [(5, fun args σ0 fr σ => ∀ (ch n : I32), args = [.int ch, .int n] →
  ∃ x cs, fr.get 0 = some (.int n) ∧ fr.get 3 = some (.ref x) ∧ σ.heap x = some (.str cs) ∧
    1 ≤ cs.length ∧ cs.length < 2147483648 ∧ 0 < n.toInt ∧ n.toInt ≤ 1073741824 ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

def repeatVarT (_ : List Value) (_ : State) (fr : Frame) (σ : State) : Nat :=
  match fr.get 3 with
  | some (.ref x) =>
    match σ.heap x with
    | some (.str cs) => 2147483648 - cs.length
    | _ => 0
  | _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem repeat_vcT : MethodVC Gen.prog (fun _ => none) 0 repeatRef repeatSpecT repeatInvT 40 := by
  set_option jimple.modelContracts true in
  jverify [ite_nat_ne, repeatSpecT, repeatInvT, StrResL, GrowsT, Grows, EquivLean.Modernize.Cbstm03b.Java.jstr_empty]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem repeat_thinT :
    ThinVC Gen.prog (fun _ => none) 0 repeatRef repeatSpecT repeatInvT (fun _ => repeatVarT) 40 := by
  set_option jimple.modelContracts true in
  jthin [ite_nat_ne, repeatSpecT, repeatInvT, Grows, repeatVarT]

theorem repeat_termT : ∀ args σ, repeatSpecT.pre args σ → MTerm Gen.prog repeatRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) repeat_vcT repeat_thinT)

theorem repeat_satT : Sat Gen.prog repeatRef repeatSpecT := repeat_vcT.sat

set_option maxHeartbeats 4000000 in
theorem repeat_ctermT : ContractTerm Gen.prog repeatSig repeatSpecT := by jcontract_term [repeat_termT]
set_option maxHeartbeats 4000000 in
theorem repeat_okT : ContractOK Gen.prog repeatSig repeatSpecT := by jcontract_ok [repeat_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.repeat_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.repeat_okT

import EquivLean.Modernize.Cbstm03a.Java.Term.Defs

/-!
# CBSTM03A → Java, termination: `zeroPad`

`zeroPad(v, n)` fills a new `char[n]` from index `n - 1` down to 0 (loop head statement 5; locals `x#1` 2,
`i#2` 6, `c` 7). Variant `i + 1`. Frame contract (`n ≥ 0`): a new string of length `n`, `GrowsT`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

def zeroPadSpecT : Spec := Spec.of
  (fun args _ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
    StrResL σ r σ' n.toInt.toNat ∧ GrowsT σ σ')

def zeroPadInvT : Invariants := [(5, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
  ∃ arr i l xs, fr.get 6 = some (.int i) ∧ fr.get 2 = some (.long l) ∧ fr.get 7 = some (.ref arr) ∧
    σ.heap arr = some (.array (.prim .char) xs) ∧ xs.length = n.toInt.toNat ∧
    -1 ≤ i.toInt ∧ i.toInt < n.toInt ∧ σ0.next ≤ arr ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧
    σ.statics = σ0.statics)]

def zeroPadVarT (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 6 with
  | some (.int i) => (i.toInt + 1).toNat
  | _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem zeroPad_vcT : MethodVC Gen.prog (fun _ => none) 0 zeroPadRef zeroPadSpecT zeroPadInvT 60 := by
  jverify [ite_nat_ne, zeroPadSpecT, zeroPadInvT, StrResL, GrowsT, Grows, Native.charsOf, List.length_map]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem zeroPad_thinT :
    ThinVC Gen.prog (fun _ => none) 0 zeroPadRef zeroPadSpecT zeroPadInvT (fun _ => zeroPadVarT) 60 := by
  jthin [ite_nat_ne, zeroPadSpecT, zeroPadInvT, Grows, zeroPadVarT]

theorem zeroPad_termT : ∀ args σ, zeroPadSpecT.pre args σ → MTerm Gen.prog zeroPadRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) zeroPad_vcT zeroPad_thinT)

theorem zeroPad_satT : Sat Gen.prog zeroPadRef zeroPadSpecT := zeroPad_vcT.sat

set_option maxHeartbeats 4000000 in
theorem zeroPad_ctermT : ContractTerm Gen.prog zeroPadSig zeroPadSpecT := by jcontract_term [zeroPad_termT]
set_option maxHeartbeats 4000000 in
theorem zeroPad_okT : ContractOK Gen.prog zeroPadSig zeroPadSpecT := by jcontract_ok [zeroPad_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.zeroPad_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.zeroPad_okT

import EquivLean.Modernize.Cbstm03a.Java.Term.ZeroPad
import EquivLean.Modernize.Cbstm03a.Java.Term.Spaces

/-!
# CBSTM03A → Java, termination: `fmtZ`

`fmtZ(v)` counts the leading zeros `k` of `zeroPad(a / 100, 9)` (loop head statement 15, `k < 9`; locals `a` 1,
`k` 5, `ip` 7, `$z2` 12). Variant `9 - k`. Frame contract (`Cbstm03a` initialized): a new string of length 13,
`GrowsT`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

def fmtZSpecT : Spec := Spec.of (fun args σ => ∃ v : I64, args = [.long v] ∧ InitA σ)
  (fun _ σ r σ' => StrResL σ r σ' 13 ∧ GrowsT σ σ')

def fmtZInvT : Invariants := [(15, fun _ σ0 fr σ =>
  ∃ (x : Addr) (s : JStr) (k z2 : I32) (a : I64), fr.get 7 = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length = 9 ∧
    fr.get 5 = some (.int k) ∧ 0 ≤ k.toInt ∧ k.toInt ≤ 9 ∧ fr.get 1 = some (.long a) ∧
    fr.get 12 = some (.int z2) ∧ Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

def fmtZVarT (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 5 with
  | some (.int k) => (9 - k.toInt).toNat
  | _ => 0

def fmtZCalleesT : Contracts := [(zeroPadSig, zeroPadSpecT), (spacesSig, spacesSpecT)]

theorem fmtZCalleesT_ok : ∀ p ∈ fmtZCalleesT, ContractOK Gen.prog p.1 p.2 := by
  simp only [fmtZCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨zeroPad_okT, spaces_okT⟩
theorem fmtZCalleesT_term : ∀ p ∈ fmtZCalleesT, ContractTerm Gen.prog p.1 p.2 := by
  simp only [fmtZCalleesT, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨zeroPad_ctermT, spaces_ctermT⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem fmtZ_vcT : MethodVC Gen.prog fmtZCalleesT.env 0 fmtZRef fmtZSpecT fmtZInvT 60 := by
  set_option jimple.modelContracts true in
  jverify [ite_nat_ne, fmtZSpecT, fmtZInvT, fmtZCalleesT, zeroPadSig, zeroPadSpecT, spacesSig, spacesSpecT,
    StrResL, GrowsT, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem fmtZ_thinT : ThinVC Gen.prog fmtZCalleesT.env 0 fmtZRef fmtZSpecT fmtZInvT (fun _ => fmtZVarT) 60 := by
  set_option jimple.modelContracts true in
  jthin [ite_nat_ne, fmtZSpecT, fmtZInvT, fmtZCalleesT, zeroPadSig, zeroPadSpecT, spacesSig, spacesSpecT,
    StrResL, GrowsT, Grows, fmtZVarT]

theorem fmtZ_termT : ∀ args σ, fmtZSpecT.pre args σ → MTerm Gen.prog fmtZRef args σ :=
  mterm_of_thin fmtZCalleesT_ok fmtZCalleesT_term fmtZ_vcT fmtZ_thinT

theorem fmtZ_satT : Sat Gen.prog fmtZRef fmtZSpecT := sat_of_table fmtZCalleesT_ok fmtZ_vcT

set_option maxHeartbeats 4000000 in
theorem fmtZ_ctermT : ContractTerm Gen.prog fmtZSig fmtZSpecT := by jcontract_term [fmtZ_termT]
set_option maxHeartbeats 4000000 in
theorem fmtZ_okT : ContractOK Gen.prog fmtZSig fmtZSpecT := by jcontract_ok [fmtZ_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.fmtZ_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.fmtZ_okT

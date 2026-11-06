import EquivLean.Modernize.Cbstm03a.Java.Term.Lemmas

/-!
# CBSTM03A → Java, termination: `ebc`

`ebc(c)` searches the static table `CP037` (loop head statement 2, `i < 256`; locals `i` 2, `c` 4). Variant
`256 - i`. Frame contract (`Cbstm03a` initialized and its static `CP037` an `int` array of length 256, which
`<clinit>` builds): an `int` result, the state unchanged.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Term

/-- The static `CP037` is an `int` array of length 256. -/
def CpOk (σ : State) : Prop :=
  ∃ (a : Addr) (ks : List I32), σ.static ("Cbstm03a", "CP037") = some (.ref a) ∧
    σ.heap a = some (.array (.prim .int) (ks.map Value.int)) ∧ ks.length = 256

def ebcSpecT : Spec := Spec.of (fun args σ => ∃ c : I32, args = [.int c] ∧ InitA σ ∧ CpOk σ)
  (fun _ σ r σ' => (∃ k : I32, r = some (.int k)) ∧ σ' = σ)

def ebcInvT : Invariants := [(2, fun args σ0 fr σ => ∀ c : I32, args = [.int c] →
  ∃ i : I32, fr.get 2 = some (.int i) ∧ fr.get 4 = some (.int c) ∧ 0 ≤ i.toInt ∧ i.toInt ≤ 256 ∧ σ = σ0)]

def ebcVarT (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 2 with
  | some (.int i) => (256 - i.toInt).toNat
  | _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ebc_vcT : MethodVC Gen.prog (fun _ => none) 0 ebcRef ebcSpecT ebcInvT 40 := by
  jverify [ite_nat_ne, ebcSpecT, ebcInvT, CpOk, getElem?_map_int]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem ebc_thinT : ThinVC Gen.prog (fun _ => none) 0 ebcRef ebcSpecT ebcInvT (fun _ => ebcVarT) 40 := by
  jthin [ite_nat_ne, ebcSpecT, ebcInvT, CpOk, getElem?_map_int, ebcVarT]

theorem ebc_termT : ∀ args σ, ebcSpecT.pre args σ → MTerm Gen.prog ebcRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) ebc_vcT ebc_thinT)

theorem ebc_satT : Sat Gen.prog ebcRef ebcSpecT := ebc_vcT.sat

set_option maxHeartbeats 4000000 in
theorem ebc_ctermT : ContractTerm Gen.prog ebcSig ebcSpecT := by jcontract_term [ebc_termT]
set_option maxHeartbeats 4000000 in
theorem ebc_okT : ContractOK Gen.prog ebcSig ebcSpecT := by jcontract_ok [ebc_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.ebc_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.ebc_okT

import EquivLean.Modernize.Cbstm03a.Java.Term.Chr

/-!
# CBSTM03A → Java, termination: `decodeZoned`

`decodeZoned(s)` reads the characters of `s` (loop head statement 5; locals `v` 1, `n` 3, `i` 5, `s` 6, `neg` 7).
Variant `n - i`. Frame contract (`s` a non-null string of `int` length): a `long` result, the state unchanged.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Term

def decodeZonedSpecT : Spec := Spec.of (fun args σ => ∃ sv, args = [sv] ∧ StrArgN σ sv)
  (fun _ σ r σ' => (∃ l : I64, r = some (.long l)) ∧ σ' = σ)

def decodeZonedInvT : Invariants := [(5, fun args σ0 fr σ => ∀ sv, args = [sv] →
  ∃ (x : Addr) (s : JStr) (n i neg : I32) (v : I64), sv = .ref x ∧ fr.get 6 = some (.ref x) ∧ σ.heap x = some (.str s) ∧
    s.length < 2147483648 ∧ fr.get 3 = some (.int n) ∧ n.toInt ≤ s.length ∧ fr.get 5 = some (.int i) ∧
    0 ≤ i.toInt ∧ fr.get 1 = some (.long v) ∧ fr.get 7 = some (.int neg) ∧ σ = σ0)]

def decodeZonedVarT (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 3, fr.get 5 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem decodeZoned_vcT :
    MethodVC Gen.prog (fun _ => none) 0 decodeZonedRef decodeZonedSpecT decodeZonedInvT 80 := by
  jverify [ite_nat_ne, decodeZonedSpecT, decodeZonedInvT, StrArgN, setWidth32_eq_ofNat, getElem_eq_chr, ite_nat_ne]
  all_goals jvc [ite_nat_ne, decodeZonedSpecT, decodeZonedInvT, StrArgN, setWidth32_eq_ofNat, getElem_eq_chr, ite_nat_ne]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem decodeZoned_thinT : ThinVC Gen.prog (fun _ => none) 0 decodeZonedRef decodeZonedSpecT decodeZonedInvT
    (fun _ => decodeZonedVarT) 80 := by
  jthin [ite_nat_ne, decodeZonedSpecT, decodeZonedInvT, StrArgN, decodeZonedVarT, setWidth32_eq_ofNat, getElem_eq_chr,
    ite_nat_ne]
  all_goals jvc [ite_nat_ne, decodeZonedSpecT, decodeZonedInvT, StrArgN, decodeZonedVarT, setWidth32_eq_ofNat, getElem_eq_chr,
    ite_nat_ne]

theorem decodeZoned_termT : ∀ args σ, decodeZonedSpecT.pre args σ → MTerm Gen.prog decodeZonedRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) decodeZoned_vcT decodeZoned_thinT)

theorem decodeZoned_satT : Sat Gen.prog decodeZonedRef decodeZonedSpecT := decodeZoned_vcT.sat

set_option maxHeartbeats 4000000 in
theorem decodeZoned_ctermT : ContractTerm Gen.prog decodeZonedSig decodeZonedSpecT := by
  jcontract_term [decodeZoned_termT]
set_option maxHeartbeats 4000000 in
theorem decodeZoned_okT : ContractOK Gen.prog decodeZonedSig decodeZonedSpecT := by
  jcontract_ok [decodeZoned_satT]

end EquivLean.Modernize.Cbstm03a.Java.Term

#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.decodeZoned_ctermT
#print axioms EquivLean.Modernize.Cbstm03a.Java.Term.decodeZoned_okT

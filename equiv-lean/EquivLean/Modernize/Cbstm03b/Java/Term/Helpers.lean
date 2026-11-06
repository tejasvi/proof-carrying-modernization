import EquivLean.Modernize.Cbstm03b.Java.HSpaces
import EquivLean.Modernize.Cbstm03b.Java.HZeroPad
import EquivLean.Modernize.Cbstm03b.Java.HFit
import EquivLean.Modernize.Cbstm03b.Java.HStatus2
import EquivLean.Modernize.Cbstm03b.Java.HKeySub
import EquivLean.Modernize.Cbstm03b.Java.HFresh

/-!
# CBSTM03B → Java, termination: the string helpers

The thin twins of the helpers' `MethodVC`s (`Jimple.TermVC.of_thin`): `spaces` counts `i` up to `n`
(statement 4, variant `n - i`), `zeroPad` counts `i` down to `-1` (statement 8, variant `i + 1`), `fit`
appends spaces until the builder's length `k` reaches `n` (statement 15, variant `n - k`); `status2` and
`keySub` have no loop. Each helper's contract terminates (`*_cterm`); so do the contracts with fresh results
(`status2SpecF`, `fitSpecF`), which have the same preconditions.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03b.Java

/-! ## Variants -/

/-- `spaces`: `n - i` (locals `i0` 0, `i1` 1). -/
def spacesVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

/-- `zeroPad`: `i + 1` (local `i0` 4). -/
def zeroPadVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 4 with
  | some (.int i) => (i.toInt + 1).toNat
  | _ => 0

/-- `fit`: `n - k` (locals `i0` 0, `$i1` 1: the builder's length). -/
def fitVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int k) => (n.toInt - k.toInt).toNat
  | _, _ => 0

/-! ## Thin VCs -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem spaces_thin :
    ThinVC Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv (fun _ => spacesVar) 60 := by
  jthin [ite_nat_ne, spacesSpec, spacesInv, Grows, fixStr, spacesVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem zeroPad_thin :
    ThinVC Gen.prog (fun _ => none) 0 zeroPadRef zeroPadSpec zeroPadInv (fun _ => zeroPadVar) 80 := by
  jthin [ite_nat_ne, zeroPadSpec, zeroPadInv, Grows, zpadStr, digitChar, sdiv10_toNat_of_nonneg, sdiv10_nonneg,
    digit_char, drop_set_self, zeroPadVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.hypHeapFacts true in
theorem fit_thin :
    ThinVC Gen.prog (fun _ => none) 0 fitRef fitSpec fitInv (fun _ => fitVar) 60 := by
  jthin [ite_nat_ne, fitSpec, fitInv, StrOk, argText, strOf, Grows, fixStr_eq_take, fixStr_succ_of_ge,
    fixStr_length, fixStr_eq_self, jstr_empty, max_zero_of_nonneg, space, Option.getD_some, fitVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem status2_thin :
    ThinVC Gen.prog (fun _ => none) 0 status2Ref status2Spec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [status2Spec, stChars, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem keySub_thin (q skey : Addr) (fs : List (FieldKey × Value)) (key : JStr) (kl : Int) :
    ThinVC Gen.prog (fun _ => none) 0 keySubRef (keySubG q skey fs key kl) [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [keySubG, Grows]

/-! ## Termination -/

theorem spaces_term : ∀ args σ, spacesSpec.pre args σ → MTerm Gen.prog spacesRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) spaces_vc spaces_thin)
theorem zeroPad_term : ∀ args σ, zeroPadSpec.pre args σ → MTerm Gen.prog zeroPadRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) zeroPad_vc zeroPad_thin)
theorem fit_term : ∀ args σ, fitSpec.pre args σ → MTerm Gen.prog fitRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) fit_vc fit_thin)
theorem status2_term : ∀ args σ, status2Spec.pre args σ → MTerm Gen.prog status2Ref args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) status2_vc status2_thin)
theorem keySubG_term (q skey : Addr) (fs : List (FieldKey × Value)) (key : JStr) (kl : Int) :
    ∀ args σ, (keySubG q skey fs key kl).pre args σ → MTerm Gen.prog keySubRef args σ :=
  TermVC.mterm (r := 1) (Jimple.valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) (keySub_vc q skey fs key kl)
      (keySub_thin q skey fs key kl))

/-- `keySub` terminates on every input of `keySubSpec`: the area's fields give the ghost values of
    `keySubG`. -/
theorem keySub_term : ∀ args σ, keySubSpec.pre args σ → MTerm Gen.prog keySubRef args σ := by
  intro args σ hpre
  obtain ⟨q, a, rfl, hA, hVa⟩ := hpre
  obtain ⟨q', fs, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq, -, -, -, -, hkl, hkl1, hkl2, -,
    -, -, -, -, -, -, gkey, jkey, gkl, -, -⟩ := areaAt_of hA hVa
  cases hqq
  obtain ⟨x, rfl, hx⟩ := jkey
  exact keySubG_term q x fs (cp037Str key) kl _ σ
    ⟨rfl, hq, gkey, hx, by rw [cp037Str_length]; exact hkl, gkl, hkl1, hkl2⟩

set_option maxHeartbeats 4000000 in
theorem spaces_cterm : ContractTerm Gen.prog spacesSig spacesSpec := by jcontract_term [spaces_term]
set_option maxHeartbeats 4000000 in
theorem zeroPad_cterm : ContractTerm Gen.prog zeroPadSig zeroPadSpec := by jcontract_term [zeroPad_term]
set_option maxHeartbeats 4000000 in
theorem fit_cterm : ContractTerm Gen.prog fitSig fitSpec := by jcontract_term [fit_term]
set_option maxHeartbeats 4000000 in
theorem status2_cterm : ContractTerm Gen.prog status2Sig status2Spec := by jcontract_term [status2_term]
set_option maxHeartbeats 4000000 in
theorem keySub_cterm : ContractTerm Gen.prog keySubSig keySubSpec := by jcontract_term [keySub_term]

/-- The contracts with fresh results have the same preconditions. -/
theorem status2F_cterm : ContractTerm Gen.prog status2Sig status2SpecF :=
  ContractTerm.mono status2_cterm fun _ _ h => h
theorem fitF_cterm : ContractTerm Gen.prog fitSig fitSpecF := ContractTerm.mono fit_cterm fun _ _ h => h

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.spaces_cterm
#print axioms EquivLean.Modernize.Cbstm03b.Java.zeroPad_cterm
#print axioms EquivLean.Modernize.Cbstm03b.Java.fit_cterm
#print axioms EquivLean.Modernize.Cbstm03b.Java.status2_cterm
#print axioms EquivLean.Modernize.Cbstm03b.Java.keySub_cterm
#print axioms EquivLean.Modernize.Cbstm03b.Java.status2F_cterm
#print axioms EquivLean.Modernize.Cbstm03b.Java.fitF_cterm

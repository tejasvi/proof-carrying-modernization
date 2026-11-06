-- Termination package by JimpleLean's session: TermPk/Cbtrn01c/JavaTermHelpers.lean (sha256 c340fcb3e9a10b61...); only the module root renamed.
import EquivLean.Modernize.Cbtrn01c.JavaRun
import EquivLean.Modernize.TermCommon

/-!
# CBTRN01C → Java, termination: the callees of `run`

Split VCs (`Jimple.TermVC.of_thin`): each `MethodVC` of `JavaRunHelpers`/`JavaRunZoned`/`JavaRunFormat`
with a thin VC. `spaces` counts up to `n` (variant `n - i`), `digits` down to `-1` (variant `i + 1`);
`signedZoned` and `formatDalytran` have no loop. The termination of each contract
(`ContractTerm`) for `run`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

/-- `spaces`'s loop: `n - i` (locals `n` 0, `i` 1). -/
def spacesVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_thin :
    ThinVC Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv (fun _ => spacesVar) 60 := by
  jthin [spacesSpec, spacesInv, spacesVar, Grows, spJ_succ, valueOfArg_char]

theorem spaces_term : ∀ args σ, spacesSpec.pre args σ → MTerm Gen.prog spacesRef args σ :=
  TermVC.mterm (r := 1) (valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) spaces_vc spaces_thin)

set_option maxHeartbeats 0 in
theorem spaces_cterm : ContractTerm Gen.prog spacesSig spacesSpec := by jcontract_term [spaces_term]

/-- `digits`'s loop: `i + 1` (local `i` 4, down to `-1`). -/
def digitsVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 4 with
  | some (.int i) => (i.toInt + 1).toNat
  | _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem digits_thin :
    ThinVC Gen.prog (fun _ => none) 0 digitsRef digitsSpec digitsInv (fun _ => digitsVar) 80 := by
  jthin [digitsSpec, digitsInv, digitsVar, Grows, zpadJ, digitJ, sdiv10_toNat_of_nonneg, sdiv10_nonneg,
    digit_char2, drop_set_self, cmp_zero_nonneg_iff, pos_toNat, negNat, toNat_add_one_of_neg,
    charsOf_cons_int, charsOf_replicate_drop, int_add_neg_one_add_one]

theorem digits_term : ∀ args σ, digitsSpec.pre args σ → MTerm Gen.prog digitsRef args σ :=
  TermVC.mterm (r := 1) (valid_none _) (contractTerm_none _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) digits_vc digits_thin)

set_option maxHeartbeats 0 in
theorem digits_cterm : ContractTerm Gen.prog digitsSig digitsSpec := by jcontract_term [digits_term]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem signedZoned_thin :
    ThinVC Gen.prog szCallees.env 0 signedZonedRef signedZonedSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [signedZonedSpec, szCallees, digitsSig, digitsSpec, Grows, szJ, overJ,
    EquivLean.Cobol.Rec.overpunch, digitJ, zpadJ_length, zpadJ_getElem?_pred, zpadJ_take_pred,
    i32_toNat_sub_one, i32_toNat_eq, digit_sub48, ofNat32_digit_eq_zero, cmp_zero_nonneg_iff,
    valueOfArg_char, idx_pred, evalDynamic, concatRecipe, Native.valueOfArg, Native.valueOfObj,
    Native.primStr, JType.isRef, jstrLitT, Native.valueOfObjN, Native.nObjStr, over_pos_char,
    over_neg_char]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

theorem signedZoned_term :
    ∀ args σ, signedZonedSpec.pre args σ → MTerm Gen.prog signedZonedRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Contracts.valid_of_ok (by
      simp only [szCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact digits_ok))
    (Contracts.term_of_ok (by
      simp only [szCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact digits_cterm) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) signedZoned_vc signedZoned_thin)

set_option maxHeartbeats 0 in
theorem signedZoned_cterm : ContractTerm Gen.prog signedZonedSig signedZonedSpec := by
  jcontract_term [signedZoned_term]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem formatDalytran_thin :
    ThinVC Gen.prog fdCallees.env 0 formatDalytranRef formatDalytranSpec [] (fun _ _ _ _ _ => 0) 80 := by
  jthin [formatDalytranSpec, fdCallees, digitsSig, signedZonedSig, digitsSpec, signedZonedSpec,
    DalOk, StrField, LongField, dalLine, fieldOf, fieldLong, argText, Grows, dalCls,
    Native.valueOfArg, Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, Native.primStr,
    JType.isRef]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

theorem formatDalytran_term :
    ∀ args σ, formatDalytranSpec.pre args σ → MTerm Gen.prog formatDalytranRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) fdCallees_valid
    (Contracts.term_of_ok (by
      simp only [fdCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      exact ⟨digits_cterm, signedZoned_cterm⟩) _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) formatDalytran_vc formatDalytran_thin)

set_option maxHeartbeats 0 in
theorem formatDalytran_cterm : ContractTerm Gen.prog formatDalytranSig formatDalytranSpec := by
  jcontract_term [formatDalytran_term]

/-- The callee contracts of `run` terminate. -/
theorem callees_term :
    ∀ sig S, (callees.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [callees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨spaces_cterm, digits_cterm, formatDalytran_cterm⟩) _ _

end EquivLean.Modernize.Cbtrn01c.Java

#print axioms EquivLean.Modernize.Cbtrn01c.Java.callees_term

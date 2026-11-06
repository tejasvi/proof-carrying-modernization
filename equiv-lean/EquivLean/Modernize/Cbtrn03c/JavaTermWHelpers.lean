-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/JavaTermWHelpers.lean (sha256 942614fe167063d3...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaW.W
import EquivLean.Modernize.Cbtrn03c.JavaW.W2
import EquivLean.Modernize.Cbtrn03c.JavaW.Edit
import EquivLean.Modernize.Cbtrn03c.JavaW.Num
import EquivLean.Modernize.Cbtrn03c.JavaW.Pad
import EquivLean.Modernize.Cbtrn03c.JavaW.Str
import EquivLean.Modernize.Cbtrn03c.JavaW.Zoned
import EquivLean.Modernize.TermCommon

/-!
# CBTRN03C → Java, termination: the writers' helpers (thin VCs)

`edit` counts up to 9 (local 4), `pad`, `repeat`, `pow10` up to `n`, `digits` down to `-1`; the
others have no loop.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

/-- An index in local `j`, counting up below `2^31`. -/
def wIdxVar (j : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get j with
  | some (.int i) => (2147483648 - i.toInt).toNat
  | _ => 0

/-- `n - i` (locals 0, 1). -/
def wUpVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

/-- `i + 1` (local 4, down to `-1`). -/
def wDownVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 4 with
  | some (.int i) => (i.toInt + 1).toNat
  | _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem incLine_thin :
    ThinVC Gen.prog (fun _ => none) 0 incLineRef incLineSpec [] (fun _ _ _ _ _ => 0) 20 := by
  jthin [incLineSpec, wsC, wsFs, wsF, longOf, incL]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem writeLine_thin :
    ThinVC Gen.prog writeLineCallees.env 1 writeLineRef writeLineSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [writeLineSpec, writeLineCallees, padSig, Grows, wsC, fdC,
    wsF, lrOf, refOf, listVals, listMods, argText, strOf, recText]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem edit_thin :
    ThinVC Gen.prog editCallees.env 0 editRef editSpec editInv (fun _ => wIdxVar 4) 80 := by
  jthin [editSpec, editInv, editCallees, spacesSig, spacesSpec, digitsSig, digitsSpec, Grows,
    signJ, edDigits_fold, edDigits_length, edDigits_neg, editJ_zero, editJ_pos, edS_stepN, edB_stepN,
    edS_four, edS_seven, edB_four, edB_seven, edS_zero, edB_zero, comma, space,
    spJ, valueOfArg_char, srem11_pos, srem11_neg, srem11_eq_zero_pos, srem11_eq_zero_neg, i32_eq_3,
    i32_eq_6, char_eq_48, i32_toNat_of_nonneg, Native.valueOfArg, Native.valueOfObj,
    valueOfObjN_ref, JType.isRef, wIdxVar]
  -- the remaining paths read a digit past the end of the 11 digits: infeasible
  all_goals (simp only [List.getElem?_eq_none_iff, edDigits_length] at hd; omega)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem digits_thin :
    ThinVC Gen.prog digitsCallees.env 0 digitsRef digitsSpec digitsInv (fun _ => wDownVar) 80 := by
  jthin [digitsSpec, digitsInv, digitsCallees, pow10Sig, pow10Spec, Grows, zpadJ_div_step,
    digit_div_char, valueOfArg_char, ofNat_pow10_eq_zero, zpadJ_mod, srem_abs_pos, srem_abs_neg,
    tmod_abs_pos, tmod_abs_neg, wDownVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_thin :
    ThinVC Gen.prog spacesCallees.env 0 spacesRef spacesSpec [] (fun _ _ _ _ _ => 0) 20 := by
  jthin [spacesSpec, spacesCallees, repeatSig, repeatSpec, Grows, spJ, setWidth_32]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pad_thin :
    ThinVC Gen.prog (fun _ => none) 0 padRef padSpec padInv (fun _ => wUpVar) 60 := by
  jthin [padSpec, padInv, Grows, fixJ, fixJ_length_self, fixJ_eq_take,
    setWidth_32, Native.valueOfArg, Native.valueOfObj, valueOfObjN_ref, JType.isRef, wUpVar]
  all_goals first
    | omega
    | (rw [List.getElem?_eq_none] <;> first | rfl | omega)
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem repeat_thin :
    ThinVC Gen.prog (fun _ => none) 0 repeatRef repeatSpec repeatInv (fun _ => wUpVar) 60 := by
  jthin [repeatSpec, repeatInv, Grows, repJ_succ, valueOfArg_char, wUpVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pow10_thin :
    ThinVC Gen.prog (fun _ => none) 0 pow10Ref pow10Spec pow10Inv (fun _ => wUpVar) 40 := by
  jthin [pow10Spec, pow10Inv, pow10_mul, wUpVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem add11_thin :
    ThinVC Gen.prog (fun _ => none) 0 add11Ref add11Spec [] (fun _ _ _ _ _ => 0) 20 := by
  jthin [add11Spec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem zoned_thin :
    ThinVC Gen.prog zonedCallees.env 0 zonedRef zonedSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [zonedSpec, zonedCallees, digitsSig, digitsSpec, Grows, zonedJ, overJ,
    EquivLean.Cobol.Rec.overpunch, digitJ, zpadJ_length, zpadJ_getElem?_pred, zpadJ_take_pred,
    i32_toNat_sub_one, i32_toNat_eq, digit_sub48, ofNat32_digit_eq_zero, cmp_zero_nonneg_iff,
    valueOfArg_char, idx_pred, Native.valueOfArg, Native.valueOfObj, Native.primStr, JType.isRef,
    valueOfObjN_ref, over_pos_char, over_neg_char]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java

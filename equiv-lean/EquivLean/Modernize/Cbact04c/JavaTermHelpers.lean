-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermHelpers.lean (sha256 b392303e6b38bfdc...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunHelpers4
import Jimple.TermSplit

/-!
# CBACT04C → Java, termination: the arithmetic and string helpers (thin VCs)

The thin twins of the helpers' `MethodVC`s (`JavaRunHelpers1`, `JavaRunHelpers2`,
`JavaRunHelpers4`): `pow10` and `spaces` count up to `n` (variant `n - i`), `fmtU` counts down to
`-1` (variant `i + 1`); `trunc`, `fixLen`, `fmtZoned` and `displayTcb` have no cut point.
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-- `pow10`: `n - i` (locals `n` 0, `i` 1). -/
def pow10Var (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

/-- `fmtU`: `i + 1` (local `i` 4, counting down to `-1`). -/
def fmtUVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 4 with
  | some (.int i) => (i.toInt + 1).toNat
  | _ => 0

/-- `spaces`: `n - i` (locals `n` 0, `i` 1). -/
def spacesVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pow10_thin :
    ThinVC Gen.prog (fun _ => none) 0 pow10Ref pow10Spec pow10Inv (fun _ => pow10Var) 30 := by
  jthin [pow10Spec, pow10Inv, pow10Var]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem trunc_thin :
    ThinVC Gen.prog truncC.env 0 truncRef truncSpec [] (fun _ _ _ _ _ => 0) 30 := by
  jthin [truncSpec, truncC, pow10Sig, pow10Spec, ofNat_pow10_eq_zero_iff]
  all_goals exact targets_static rfl rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem fmtU_thin :
    ThinVC Gen.prog fmtUC.env 0 fmtURef fmtUSpec fmtUInv (fun _ => fmtUVar) 60 := by
  jthin [fmtUSpec, fmtUInv, fmtUC, pow10Sig, pow10Spec, Grows, zpadJ, digitJ,
    sdiv10_toNat_of_nonneg, sdiv10_nonneg, digit_char, drop_set_self, cmp_zero_nonneg_iff,
    ofNat_pow10_eq_zero_iff, zpadJ_srem_pos, zpadJ_srem_neg, srem_pow10_nonneg_pos,
    srem_pow10_nonneg_neg, toNat_add_one_of_neg, int_add_neg_one_add_one, toChar_toChar,
    charsOf_cons, charsOf_nil, fmtUVar]
  all_goals exact targets_static rfl rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_thin :
    ThinVC Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv (fun _ => spacesVar) 60 := by
  jthin [spacesSpec, spacesInv, Grows, spJ_succ, valueOfArg_char, spacesVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem fixLen_thin :
    ThinVC Gen.prog (fun _ => none) 0 fixLenRef fixLenSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [fixLenSpec, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem fmtZoned_thin :
    ThinVC Gen.prog fmtZonedC.env 0 fmtZonedRef fmtZonedSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [fmtZonedSpec, fmtZonedC, fmtUSig, fmtUSpec, Grows, zonedJ, cmp_zero_nonneg_iff,
    charAtIdx_zpadJ_pred, charAtIdx_lit_pos, charAtIdx_lit_neg, evalDynamic, concatRecipe,
    Native.valueOfArg, Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, strOf, recipe2,
    valueOfArg_char, zpadJ_length, take_zpadJ_pred, mod32_pred, zpadJ_getElem?_pred, digitJ_toNat,
    lit_pos_getElem, lit_neg_getElem, mod32_sub48, lit_length_pos, lit_length_neg, lit_pos_get,
    lit_neg_get]
  all_goals (first | exact targets_static rfl rfl | skip)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem displayTcb_thin :
    ThinVC Gen.prog displayTcbC.env 0 displayTcbRef displayTcbSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [displayTcbSpec, displayTcbC, fmtUSig, fmtUSpec, fmtZonedSig, fmtZonedSpec, Grows,
    tcbLine, Native.valueOfArg, Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, strOf,
    initOf_eq_of_inits]
  all_goals (first | exact targets_static rfl rfl | skip)

end EquivLean.Modernize.Cbact04c.Java

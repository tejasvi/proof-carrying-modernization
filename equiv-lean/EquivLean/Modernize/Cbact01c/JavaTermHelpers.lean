-- Termination package by JimpleLean's session: TermPk/Cbact01c/JavaTermHelpers.lean (sha256 05df4f18a56a11a1...); only the module root renamed.
import EquivLean.Modernize.Cbact01c.JavaRun
import EquivLean.Modernize.TermCommon

/-!
# CBACT01C → Java, termination: the callees of `run` (thin VCs)

The thin twins of the helpers' `MethodVC`s: `spaces` and `pad` count up to `n` (variant `n - i`),
`zoned` has two loops (statements 15 and 22, the first above the second); the cut points of
`displayAcctRecord` (16, 30, 43), `writeOutRecord` (13, 16, 19) and `writeVbrcRecords` (18) are
straight-line (variants decreasing along the body); `cobdatft`, `accountRecordText` and
`writeArrayRecord` have none.
-/

-- as in the originals (JimpleLean 2006Z took `ite_nat_ne` out of `jsimp`)
attribute [local jsimp high] Jimple.ite_nat_ne

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

/-- `spaces`: `n - i` (locals `n` 0, `i` 1). -/
def spacesVar (_ : List Value) (_ : Jimple.State) (fr : Frame) (_ : Jimple.State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

/-- `pad`: `n - i` (locals `n` 0, `i` 2). -/
def padVar (_ : List Value) (_ : Jimple.State) (fr : Frame) (_ : Jimple.State) : Nat :=
  match fr.get 0, fr.get 2 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

/-- `zoned`: `n - i` (locals `n` 5, `i` 8), the first loop (statement 15) `2^32` above the second. -/
def zonedVs (pc : Nat) (_ : List Value) (_ : Jimple.State) (fr : Frame) (_ : Jimple.State) : Nat :=
  match fr.get 5, fr.get 8 with
  | some (.int n), some (.int i) => (if pc = 15 then 4294967296 else 0) + (n.toInt - i.toInt).toNat
  | _, _ => 0

/-- `displayAcctRecord`'s straight-line cut points 16, 30, 43. -/
def dispVs (pc : Nat) (_ : List Value) (_ : Jimple.State) (_ : Frame) (_ : Jimple.State) : Nat :=
  if pc = 16 then 3 else if pc = 30 then 2 else if pc = 43 then 1 else 0

/-- `writeOutRecord`'s straight-line cut points 13, 16, 19. -/
def woutVs (pc : Nat) (_ : List Value) (_ : Jimple.State) (_ : Frame) (_ : Jimple.State) : Nat :=
  if pc = 13 then 3 else if pc = 16 then 2 else if pc = 19 then 1 else 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_thin :
    ThinVC Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv (fun _ => spacesVar) 60 := by
  jthin [spacesSpec, spacesInv, Grows, fixStr, spacesVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pad_thin :
    ThinVC Gen.prog (fun _ => none) 0 padRef padSpec padInv (fun _ => padVar) 60 := by
  jthin [padSpec, padInv, StrOk, argText, Grows, fixStr, padVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem zoned_thin :
    ThinVC Gen.prog (fun _ => none) 0 zonedRef zonedSpec zonedInv zonedVs 80 := by
  jthin [zonedSpec, zonedInv, Grows, zonedJ, zonedPre, zch, digitJ, overpunch, ngOf, toInt_digit,
    digit_eq_zero, char48, char74, char65, sdiv10_toNat_of_nonneg, sdiv10_nonneg, mul10_toNat,
    pow10_pred_mul, pow10_div10, pow10_lt18, abs_neg_toNat, abs_neg_nonneg, abs_toNat, zonedVs]
  all_goals zoned_close

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cobdatft_thin :
    ThinVC Gen.prog (fun _ => none) 0 cobdatftRef cobdatftSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [cobdatftSpec, cobOut, argText, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem accountRecordText_thin :
    ThinVC Gen.prog textCallees.env 0 accountRecordTextRef accountRecordTextSpec [] (fun _ _ _ _ _ => 0) 80 := by
  jthin [accountRecordTextSpec, textCallees, zonedSig, padSig, zonedSpec, padSpec, AcctOk,
    StrField, LongField, StrOk, acctTextJ, sfJ, zfJ, fieldOf, fieldLong, argText, Grows, acctCls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem displayAcctRecord_thin (L : Addr) :
    ThinVC Gen.prog dispCallees.env 0 displayAcctRecordRef (displayAcctRecordSpec L) (dispInv L) dispVs 120 := by
  jthin [displayAcctRecordSpec, dispInv, dispCut3, dispCut6, dispCut9, dispLine, dispCallees,
    zonedSig, zonedSpec, AcctOkB, StrFieldB, LongField,
    dispLinesJ, lElems, lMods, sfJ, zfJ, fieldOf, fieldLong, argText, acctCls, resCls,
    evalDynamic, concatRecipe_nil', concatRecipe_const, concatRecipe_arg, Native.valueOfArg, JType.isRef, jstrLit, Grows,
    exists_and_left, exists_and_right, and_assoc, exists_eq_left, exists_eq_left', exists_eq_right,
    exists_eq_right', dispVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem writeOutRecord_thin (L : Addr) :
    ThinVC Gen.prog outCallees.env 1 writeOutRecordRef (writeOutRecordSpec L) woutInv woutVs 120 := by
  jthin [writeOutRecordSpec, woutInv, woutCut13, woutCut16, woutCut19, WOutBase, outCallees,
    padSig, padSpecF, AcctOkB, StrFieldB, LongField, StrOk, OutRecJ, outFields0, lElems, lMods, sfJ, fieldOf,
    fieldLong, argText, acctCls, resCls, outCls, inlineFuel, Grows, woutVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem writeArrayRecord_thin (L : Addr) :
    ThinVC Gen.prog arrCallees.env 1 writeArrayRecordRef (writeArrayRecordSpec L) [] (fun _ _ _ _ _ => 0) 120 := by
  jthin [writeArrayRecordSpec, arrCallees, spacesSig, spacesSpecF, AcctOkB, StrFieldB, LongField,
    ArrRecJ, balArr, debArr, lElems, lMods, fieldOf, fieldLong, acctCls, resCls, arrCls,
    inlineFuel, Grows]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem writeVbrcRecords_thin (L1 L4 : Addr) :
    ThinVC Gen.prog textCallees.env 0 writeVbrcRecordsRef (writeVbrcRecordsSpec L1 L4) vbrcInv (fun _ _ _ _ _ => 0) 120 := by
  jthin [writeVbrcRecordsSpec, vbrcInv, vbrcCut18, textCallees, zonedSig, padSig, zonedSpec,
    padSpec, AcctOkB, StrFieldB, LongField, StrOk, vb1J, vb2J, lElems, lMods, sfJ, zfJ, fieldOf,
    fieldLong, argText, acctCls, resCls,
    evalDynamic, concatRecipe_nil', concatRecipe_const, concatRecipe_arg, Native.valueOfArg, JType.isRef, jstrLit, Grows, fixStr_length]

end EquivLean.Modernize.Cbact01c.Java

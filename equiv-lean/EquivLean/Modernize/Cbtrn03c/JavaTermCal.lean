-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/JavaTermCal.lean (sha256 c683cafc209cab33...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalAdd11
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalBlank
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalEbc
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalFind
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalIo
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalNum
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalRec
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalSpaces
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalZoned
import EquivLean.Modernize.TermCommon

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java, termination: the helpers of the top layer (thin VCs)

`ebcdic` counts up to 256, `compareEbcdic` up to the length (local 2), the three searches up to
the array's end, `pow10` and `repeat` up to `n`, `digits` down to `-1`; `blankTran`'s cut points
are straight-line (the field assignments); the others have none.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

/-- `ebcdic`: `256 - i` (local 0). -/
def ebcdicVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0 with
  | some (.int i) => (256 - i.toInt).toNat
  | _ => 0

/-- `compareEbcdic`: `n - i` (locals 2, 4). -/
def cmpVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 2, fr.get 4 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

/-- A search index in local `j`, counting up below `2^31`. -/
def idxVar (j : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get j with
  | some (.int i) => (2147483648 - i.toInt).toNat
  | _ => 0

/-- `pow10`, `repeat`: `n - i` (locals 0, 1). -/
def upVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0, fr.get 1 with
  | some (.int n), some (.int i) => (n.toInt - i.toInt).toNat
  | _, _ => 0

/-- `digits`: `i + 1` (local 4, down to `-1`). -/
def downVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 4 with
  | some (.int i) => (i.toInt + 1).toNat
  | _ => 0

/-- Straight-line cut points: `1000 - pc`. -/
def seqVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat := 1000 - pc

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem add11_thin :
    ThinVC Gen.prog (fun _ => none) 0 add11Ref add11SpecT [] (fun _ _ _ _ _ => 0) 20 := by
  jthin [add11SpecT]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem blankTran_thin :
    ThinVC Gen.prog blankCallees.env 1 blankTranRef blankTranSpecT blankInv seqVs 80 := by
  jthin [blankTranSpecT, blankInv, blankCallees, spacesSig, spacesSpecT, Agree, TranFields, SFld,
    LFld, tranC, Model.tran0, Model.tId, Model.tType, Model.tCat, Model.tSource, Model.tAmt,
    Model.tCard, Model.strOf, Model.numOf, ite_nat_ne, seqVs]
  all_goals first
    | (intro h; subst h; jomega)
    | skip

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem ebcdic_thin :
    ThinVC Gen.prog (fun _ => none) 0 ebcdicRef ebcdicSpec ebcdicInv (fun _ => ebcdicVar) 40 := by
  jthin [ebcdicSpec, ebcdicInv, Agree, cpJ_length, setWidth32_inj, setWidth_16_32, ebcFrom_ne,
    ebcFrom_eq, ebcFrom_ge, ofInt_toNat_toInt, ofInt_toNat_toInt', List.getD_eq_getElem?_getD, ebcdicVar]
  all_goals first
    | (simp only [List.getElem?_eq_none_iff, cpJ_length] at hd; omega)
    | ((rw [ebcFrom_ne] <;> first
        | omega
        | (simp_all [List.getD_eq_getElem?_getD]; done));
       done)
    | ((rw [ebcFrom_eq, ofInt_toNat_toInt] <;> first
        | omega
        | (simp_all [List.getD_eq_getElem?_getD]; done));
       done)
    | (intro h; subst h; jomega)
    | skip

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem compareEbcdic_thin :
    ThinVC Gen.prog compareCallees.env 0 compareEbcdicRef compareEbcdicSpec compareEbcdicInv (fun _ => cmpVar) 60 := by
  jthin [compareEbcdicSpec, compareEbcdicInv, compareCallees, ebcdicSig, ebcdicSpec, Agree,
    cmpFrom_eq, cmpFrom_gt, cmpFrom_lt, cmpFrom_ge, List.getD_eq_getElem?_getD, argText, strOf,
    setWidth_16_32, cmpVar]
  all_goals first
    | ((rw [cmpFrom_eq] <;> first
        | omega
        | (simp_all [List.getD_eq_getElem?_getD, ebcV]; done));
       done)
    | ((rw [cmpFrom_gt] <;> first
        | omega
        | (simp_all [List.getD_eq_getElem?_getD, ebcV]; done));
       done)
    | ((rw [cmpFrom_lt] <;> first
        | omega
        | (simp_all [List.getD_eq_getElem?_getD, ebcV]; done));
       done)
    | (intro h; subst h; jomega)
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findXref_thin :
    ThinVC Gen.prog (fun _ => none) 0 findXrefRef findXrefSpec findXrefInv (fun _ => idxVar 2) 40 := by
  jthin [findXrefSpec, findXrefInv, StrFieldOk, xrefCls, fieldStr, argText, findFrom_ne,
    findFrom_eq, findFrom_ge, ofInt_toNat_toInt, ofInt_toNat_toInt', List.getD_eq_getElem?_getD,
    List.getElem?_map, idxVar]
  all_goals first
    | ((rw [findFrom_ne] <;> first
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, fieldStr, argText, strOf]; done));
       done)
    | ((rw [findFrom_eq, ofInt_toNat_toInt] <;> first
        | omega
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, fieldStr, argText, strOf]; done));
       done)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findTranType_thin :
    ThinVC Gen.prog (fun _ => none) 0 findTranTypeRef findTranTypeSpec findTranTypeInv (fun _ => idxVar 1) 40 := by
  jthin [findTranTypeSpec, findTranTypeInv, StrFieldOk, typeCls, fieldStr, argText, findFrom_ne,
    findFrom_eq, findFrom_ge, ofInt_toNat_toInt, ofInt_toNat_toInt', List.getD_eq_getElem?_getD,
    List.getElem?_map, idxVar]
  all_goals first
    | ((rw [findFrom_ne] <;> first
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, fieldStr, argText, strOf]; done));
       done)
    | ((rw [findFrom_eq, ofInt_toNat_toInt] <;> first
        | omega
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, fieldStr, argText, strOf]; done));
       done)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findTranCat_thin :
    ThinVC Gen.prog (fun _ => none) 0 findTranCatRef findTranCatSpec findTranCatInv (fun _ => idxVar 6) 40 := by
  jthin [findTranCatSpec, findTranCatInv, CatOk, catCls, catKey, fieldStr, fieldLongV, argText,
    findFrom_ne, findFrom_eq, findFrom_ge, ofInt_toNat_toInt, ofInt_toNat_toInt',
    List.getD_eq_getElem?_getD, List.getElem?_map, idxVar]
  all_goals first
    | ((rw [findFrom_ne] <;> first
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, catKey, catCls, fieldStr,
            fieldLongV, argText, strOf]; done)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, catKey, catCls, fieldStr,
            fieldLongV, argText, strOf]; intro h; subst_vars; omega));
       done)
    | ((rw [findFrom_eq, ofInt_toNat_toInt] <;> first
        | omega
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, catKey, catCls, fieldStr,
            fieldLongV, argText, strOf]; done));
       done)
    | ((rw [findFrom_ne'] <;> first
        | (simp only [List.length_map]; omega)
        | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, catKey, catCls, fieldStr,
            fieldLongV, argText, strOf]; done));
       done)
    | (simp_all [List.getD_eq_getElem?_getD, List.getElem?_map, catKey, catCls, fieldStr,
        fieldLongV, argText, strOf]; done)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ioStatusLine_thin :
    ThinVC Gen.prog (fun _ => none) 0 ioStatusLineRef ioStatusLineSpecT [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [ioStatusLineSpecT, Agree, jstrLit, txtLit, jline, valueOfArg_char, Native.valueOfArg,
    JType.isRef]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pow10_thin :
    ThinVC Gen.prog (fun _ => none) 0 pow10Ref pow10Spec pow10Inv (fun _ => upVar) 40 := by
  jthin [pow10Spec, pow10Inv, pow10_mul, upVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem digits_thin :
    ThinVC Gen.prog digitsCallees.env 0 digitsRef digitsSpec digitsInv (fun _ => downVar) 80 := by
  jthin [digitsSpec, digitsInv, digitsCallees, pow10Sig, pow10Spec, Agree, zpadJ_div_step,
    digit_div_char, valueOfArg_char, ofNat_pow10_eq_zero, zpadJ_mod, srem_abs_pos, srem_abs_neg,
    tmod_abs_pos, tmod_abs_neg, downVar]
  all_goals first
    | (intro h; subst h; jomega)
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem tranRecordText_thin :
    ThinVC Gen.prog trCallees.env 0 tranRecordTextRef tranRecordTextSpec [] (fun _ _ _ _ _ => 0) 80 := by
  jthin [tranRecordTextSpec, trCallees, digitsSig, zonedSig, digitsSpec, zonedSpec, TranOk, StrF,
    LongF, tranText, fieldStr, fieldLongV, argText, Agree, tranCls, Native.valueOfArg,
    Native.primStr, JType.isRef]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | (intro h; subst h; jomega)
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem repeat_thin :
    ThinVC Gen.prog (fun _ => none) 0 repeatRef repeatSpec repeatInv (fun _ => upVar) 60 := by
  jthin [repeatSpec, repeatInv, Agree, repJ_succ, valueOfArg_char, upVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_thin :
    ThinVC Gen.prog spacesCallees.env 0 spacesRef spacesSpecT [] (fun _ _ _ _ _ => 0) 20 := by
  jthin [spacesSpecT, spacesCallees, repeatSig, repeatSpec, Agree, cp037Str_sp, setWidth_32]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem zoned_thin :
    ThinVC Gen.prog zonedCallees.env 0 zonedRef zonedSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [zonedSpec, zonedCallees, digitsSig, digitsSpec, Agree, zonedJ, overJ,
    EquivLean.Cobol.Rec.overpunch, digitJ, zpadJ_length, zpadJ_getElem?_pred, zpadJ_take_pred,
    i32_toNat_sub_one, i32_toNat_eq, digit_sub48, ofNat32_digit_eq_zero, cmp_zero_nonneg_iff,
    valueOfArg_char, idx_pred, Native.valueOfArg, Native.primStr, JType.isRef,
    over_pos_char, over_neg_char]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | (intro h; subst h; jomega)
    | skip

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

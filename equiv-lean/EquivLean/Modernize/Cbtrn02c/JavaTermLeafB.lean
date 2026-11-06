-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermLeafB.lean (sha256 b858c44f4fd78ee5...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH6
import EquivLean.Modernize.TermCommon

/-!
# CBTRN02C → Java, termination: thin VCs of `zonedSigned`, `db2Timestamp`, `reasonDesc`, `ebcdic`,
`compareEbcdic`, `dalytranText`

The thin twins of `zonedSigned_vc` (`JavaRunH3`), `db2Timestamp_vc` (`JavaRunH4a`), `reasonDesc_vc`
(`JavaRunH4b`), `ebcdic_vc`, `compareEbcdic_vc` (`JavaRunH5`) and `dalytranText_vc` (`JavaRunH6`).
`db2Timestamp`'s cut points 12, 21 and `dalytranText`'s 11, 20, 29, 38 are straight-line; `ebcdic`
counts `i` up to 256; `compareEbcdic`'s loop head 9 and the cut 22 after the two `ebcdic` calls of an
iteration: `2 (n - i) + 2` and `2 (n - i) + 1`.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- `db2Timestamp`'s straight-line cut points 12, 21. -/
def db2Vs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat :=
  if pc = 12 then 2 else if pc = 21 then 1 else 0

/-- `ebcdic`: `256 - i` (local `i` 0). -/
def ebcdicVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 0 with
  | some (.int i) => (256 - i.toInt).toNat
  | _ => 0

/-- `compareEbcdic`: `2 (n - i) + 2` at the loop head 9, `2 (n - i) + 1` at 22 (locals `n` 2, `i` 3). -/
def ceVs (pc : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 2, fr.get 3 with
  | some (.int n), some (.int i) =>
    2 * (n.toInt - i.toInt).toNat + (if pc = 9 then 2 else if pc = 22 then 1 else 0)
  | _, _ => 0

/-- `dalytranText`'s straight-line cut points 11, 20, 29, 38. -/
def dtVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat :=
  if pc = 11 then 4 else if pc = 20 then 3 else if pc = 29 then 2 else if pc = 38 then 1 else 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem zonedSigned_thin :
    ThinVC Gen.prog szCallees.env 0 zonedSignedRef zonedSignedSpec [] (fun _ _ _ _ _ => 0) 60 := by
  jthin [zonedSignedSpec, szCallees, padNumSig, padNumSpec, Grows, szJ, overJ,
    EquivLean.Cobol.Rec.overpunch, digitJ, zpadJ_length, zpadJ_getElem?_pred, zpadJ_take_pred,
    i32_toNat_sub_one, i32_toNat_eq, digit_sub48, cmp_zero_nonneg_iff,
    valueOfArg_char, idx_pred, jstrLitT, jchar_rt, jchar_rt', Native.valueOfArg, JType.isRef,
    valueOfObj_eq, valueOfObjN_ref, idx_sub48, over_pos_lit, over_neg_lit]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem db2Timestamp_thin :
    ThinVC Gen.prog (fun _ => none) 0 db2TimestampRef db2TimestampSpec db2Inv db2Vs 60 := by
  jthin [db2TimestampSpec, db2Inv, Grows, db2J, valueOfArg_char, jstrLitT, Native.valueOfArg, JType.isRef,
    valueOfObj_eq, valueOfObjN_ref, db2Vs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem reasonDesc_thin :
    ThinVC Gen.prog (fun _ => none) 0 reasonDescRef reasonDescSpec [] (fun _ _ _ _ _ => 0) 20 := by
  jthin [reasonDescSpec, Grows, descJ]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ebcdic_thin :
    ThinVC Gen.prog (fun _ => none) 0 ebcdicRef ebcdicSpec ebcdicInv (fun _ => ebcdicVar) 40 := by
  jthin [ebcdicSpec, ebcdicInv, Grows, cp037Lit_eq, ebcdicVar]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem compareEbcdic_thin :
    ThinVC Gen.prog ceCallees.env 0 compareEbcdicRef compareEbcdicSpec compareEbcdicInv ceVs 60 := by
  jthin [compareEbcdicSpec, compareEbcdicInv, ceCallees, ebcdicSig, ebcdicSpec, Grows, cp037Str,
    toInt_ofNat_u8, ceVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem dalytranText_thin :
    ThinVC Gen.prog dtCallees.env 0 dalytranTextRef dalytranTextSpec dtInv dtVs 40 := by
  jthin [dalytranTextSpec, dtCallees, fitSig, fitSpecF, padNumSig, padNumSpec, zonedSignedSig,
    zonedSignedSpec, dtInv, dtCut, dtPre2, dtPre5, dtPre8, dtPre11, dtRet0, dtRet1, dtRet2, dtRet3,
    dtRet4, dtRet5, dtRet6, dtRet7, dtRet8, dtRet9, dtRet10, dtRet11, dtRet12, dtRet13,
    dtLine_eq_cut, DalOk, StrField, LongField, fieldOf, fieldLong, argText, strOfV, Grows, dtCls,
    Native.valueOfArg, valueOfObj_eq, valueOfObjN_ref, JType.isRef, List.append_assoc, dtVs]

end EquivLean.Modernize.Cbtrn02c.Java

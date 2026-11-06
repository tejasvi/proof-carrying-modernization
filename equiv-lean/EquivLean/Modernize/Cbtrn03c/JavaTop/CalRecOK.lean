import EquivLean.Modernize.Cbtrn03c.JavaTop.CalRec
import EquivLean.Modernize.Cbtrn03c.JavaTop.Glue1
import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `tranRecordText` builds the model's DISPLAY line of the record

For a valid record held as `TranFields` gives it: the record is one `tranRecordText` reads
(`TranOk`), and the text it builds (`tranText`) is `jline (Model.TranRecord.textS t)`: the CP037
texts of the record's bytes (`Glue.tran_cps`), with the numeric fields' texts as `digits` and
`zoned` build them (`text_unsigned`, `Glue.amt_cps`, `zpadJ_eq`, `zonedJ_eq`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

theorem cp037Str_append (a b : List UInt8) : cp037Str (a ++ b) = cp037Str a ++ cp037Str b :=
  List.map_append ..

theorem cp037Str_enc4 (v : Int) :
    cp037Str (_root_.Cobol.encodeNum {} ({ digits := 4 } : _root_.Cobol.NumFmt) v) = zpadJ v.natAbs 4 := by
  have e := text_unsigned (fmt := ({ digits := 4 } : _root_.Cobol.NumFmt)) rfl rfl (by decide) v
  rw [zpadJ_eq, ← jline_cps]
  exact congrArg jline e

theorem cp037Str_enc9 (v : Int) :
    cp037Str (_root_.Cobol.encodeNum {} CardDemo.Cbtrn03c.TRAN_MERCHANT_ID.fmt v) = zpadJ v.natAbs 9 := by
  have e := text_unsigned (fmt := CardDemo.Cbtrn03c.TRAN_MERCHANT_ID.fmt) rfl rfl (by decide) v
  rw [zpadJ_eq, ← jline_cps]
  exact congrArg jline e

theorem cp037Str_amt (v : Int) (hv : v.natAbs < 100000000000) :
    cp037Str (_root_.Cobol.encodeNum {} CardDemo.Cbtrn03c.TRAN_AMT.fmt v) = zonedJ (BitVec.ofInt 64 v) 11 := by
  rw [zonedJ_eq, toInt_ofInt64_small (by omega), ← jline_cps, Glue.amt_cps]

theorem fieldStr_of {σ : State} {c : Addr} {fs : List (FieldKey × Value)} {f : String} {y : Addr}
    {s : JStr} (hc : σ.heap c = some (.plain tranC fs))
    (he : Fields.get fs (tranC, f) = some (.ref y)) (hy : σ.heap y = some (.str s)) :
    fieldStr σ tranCls f (.ref c) = s := by
  simp only [fieldStr, hc]
  rw [show (tranCls, f) = (tranC, f) from rfl, he]
  simp [argText, strOf, hy]

theorem fieldLongV_of {σ : State} {c : Addr} {fs : List (FieldKey × Value)} {f : String} {v : Int}
    (hc : σ.heap c = some (.plain tranC fs)) (he : LFld tranC fs f v) :
    fieldLongV σ tranCls f (.ref c) = BitVec.ofInt 64 v := by
  simp only [fieldLongV, hc]
  rw [show (tranCls, f) = (tranC, f) from rfl,
    show Fields.get fs (tranC, f) = some (.long (BitVec.ofInt 64 v)) from he]

theorem lt_ofInt64 {v : Int} (hv : v.natAbs < 100000000000) :
    -9223372036854775808 < (BitVec.ofInt 64 v).toInt := by
  rw [toInt_ofInt64_small (by omega)]
  omega

/-- A valid record held as `TranFields` gives it: what `tranRecordText` reads, and its text. -/
theorem tran_glue {σ : State} {c : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (h : TranFields σ c t) (ht : TranRecord.Valid t) :
    TranOk σ c ∧ tranText σ c = jline (Model.TranRecord.textS t) := by
  have hcps := Glue.tran_cps ht
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl,
    -, -, hcat, -, -, -, hamt, hmerch, -⟩ := Glue.tran_shape ht
  obtain ⟨fs, hc, ⟨y0, e0, h0⟩, ⟨y1, e1, h1⟩, l2, ⟨y3, e3, h3⟩, ⟨y4, e4, h4⟩, l5, l6,
    ⟨y7, e7, h7⟩, ⟨y8, e8, h8⟩, ⟨y9, e9, h9⟩, ⟨y10, e10, h10⟩, ⟨y11, e11, h11⟩,
    ⟨y12, e12, h12⟩, ⟨y13, e13, h13⟩⟩ := h
  have l2' : LFld tranC fs "tranCatCd" cat := l2
  have l5' : LFld tranC fs "tranAmt" amt := l5
  have l6' : LFld tranC fs "tranMerchantId" merch := l6
  refine ⟨⟨fs, hc, ⟨y0, _, e0, h0⟩, ⟨y1, _, e1, h1⟩, ⟨_, l2', lt_ofInt64 (by omega)⟩,
    ⟨y3, _, e3, h3⟩, ⟨y4, _, e4, h4⟩, ⟨_, l5', lt_ofInt64 (by omega)⟩,
    ⟨_, l6', lt_ofInt64 (by omega)⟩, ⟨y7, _, e7, h7⟩, ⟨y8, _, e8, h8⟩, ⟨y9, _, e9, h9⟩,
    ⟨y10, _, e10, h10⟩, ⟨y11, _, e11, h11⟩, ⟨y12, _, e12, h12⟩, ⟨y13, _, e13, h13⟩⟩, ?_⟩
  unfold tranText
  rw [fieldStr_of hc e0 h0, fieldStr_of hc e1 h1, fieldLongV_of hc l2', fieldStr_of hc e3 h3,
    fieldStr_of hc e4 h4, fieldLongV_of hc l5', fieldLongV_of hc l6', fieldStr_of hc e7 h7,
    fieldStr_of hc e8 h8, fieldStr_of hc e9 h9, fieldStr_of hc e10 h10, fieldStr_of hc e11 h11,
    fieldStr_of hc e12 h12, fieldStr_of hc e13 h13, toInt_ofInt64_small (by omega),
    toInt_ofInt64_small (by omega), hcps, jline_cps]
  simp only [Glue.toTran, CardDemo.Cbtrn03c.Tran.bytes, cp037Str_append, cp037Str_enc4,
    cp037Str_enc9, cp037Str_amt amt hamt, Model.tId, Model.tType, Model.tCat, Model.tSource,
    Model.tAmt, Model.tCard, Model.strOf, Model.numOf, List.getD_cons_succ, List.getD_cons_zero,
    List.append_assoc]

theorem tranRecordTextT_sat : Sat Gen.prog tranRecordTextRef tranRecordTextSpecT := by
  intro args σ o hp hx
  obtain ⟨c, t, rfl, hf, hv, hi⟩ := hp
  have hf' : TranFields σ c t := by unfold TranFieldsI at hf; exact hf
  have ho := tranRecordText_sat _ σ o ⟨c, rfl, (tran_glue hf' hv).1, hi⟩ hx
  cases o with
  | normal r σ' =>
    intro c' t' heq hf2 hv2
    obtain ⟨x, hr, hxs, h1, h2, h3, h4, h5⟩ := ho c' heq
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at heq
    subst heq
    have hf2' : TranFields σ c t' := by unfold TranFieldsI at hf2; exact hf2
    refine ⟨x, hr, ?_, h1, h2, h3, h4, h5⟩
    rw [hxs, (tran_glue hf2' hv2).2]
  | exc e σ' => exact ho
  | wrong m => exact ho

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

set_option maxHeartbeats 0 in
theorem tranRecordText_ok : ContractOK Gen.prog tranRecordTextSig tranRecordTextSpecT := by
  jcontract_ok [Cal.tranRecordTextT_sat]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.tran_glue
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.tranRecordText_ok

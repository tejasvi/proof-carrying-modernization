import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5b
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2xs
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunModelX

/-!
# CBTRN02C → Java: `writeTransaction`'s precondition on any input, and its key search

`wtPreX_of`: `writeTransaction`'s precondition from `W` and `tranWs`; `wtIdx_neg`/`wtIdx_nonneg`:
its search over `tranKeys` fails exactly when the transaction's id was not written yet.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- A written id equals the id searched: `findKey` finds it. -/
theorem firstIdx_strs_some {σ : State} {ks : List Value} {strs : List JStr} {idcs : JStr}
    (h : Forall2 (JStrAt σ) ks strs) (hm : idcs ∈ strs) :
    0 ≤ firstIdx (fun v => strOfV σ v == some idcs) ks := by
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 hm
  have hlen := forall2_length h
  obtain ⟨x, hx, hxh⟩ := forall2_get h i (by omega) hi
  refine firstIdx_nonneg_of_mem (List.getElem_mem (by omega : i < ks.length)) ?_
  rw [hx]
  simp [strOfV, hxh, hie]

/-- **`writeTransaction`'s precondition** from `W` and `tranWs` holding a transaction record. -/
theorem wtPreX_of {σ : State} {A : Addrs} {s : Model.St} {b0 : List UInt8}
    {rest : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hwT : JRecAt TranRecord trCls σ (.ref A.wT) (.str b0 :: rest)) (hI : Inits σ) :
    writeTransactionSpecX.pre [.ref A.r, .ref A.wT, .ref A.lK] σ := by
  obtain ⟨hR, hD, hT, -, -, -, -, -, -, hK, -, -, -, hwT0, -, -, hnd⟩ := hW
  obtain ⟨fsR, hRo, r1, r2, -, -, -, -, -, r9⟩ := hR
  obtain ⟨ds, mD, hlD, -, -⟩ := hD
  obtain ⟨ts, mT, hlT, -, -, -⟩ := hT
  obtain ⟨ks, mK, hlK, hfK, hnK⟩ := hK
  obtain ⟨fsT, hto, hkT⟩ := hwT0
  obtain ⟨w', fsT', hwe, hto', hf⟩ := hwT
  have ew : w' = A.wT := (Value.ref.inj hwe).symm
  subst ew
  have efs : fsT = fsT' := by
    have e := hto.symm.trans hto'
    simp only [Option.some.injEq, Obj.plain.injEq, true_and] at e
    exact e
  subst efs
  obtain ⟨sv, hsv, sId, rfl, hsId⟩ : ∃ sv, Fields.get fsT (trCls, "tranId") = some sv ∧
      ∃ sId, sv = .ref sId ∧ σ.heap sId = some (.str (cp037Str b0)) := by
    cases hf with
    | cons j0 _ => exact j0
  obtain ⟨hI1, hI2, -, -, -, -, -, hI8⟩ := hI
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  obtain ⟨⟨n1, -, -, -, -, -, n7⟩, ⟨-, -, -, -, -, n13⟩, -⟩ := hnd
  refine ⟨A.r, A.wT, A.lK, fsR, A.lT, A.lD, fsT, sId, _, ks, mK, ts, mT, ds, mD, rfl, hRo, r2, r1, ⟨_, r9⟩, hto,
    by rw [← keysOf_tran']; exact hkT, hsv, hsId, hlK, hnK, strShapes_of hfK, hlT, hlD, ?_, hI1, hI8,
    hI2⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    and_true, not_false_eq_true]
  exact ⟨⟨fun h => n13 h.symm, fun h => n7 h.symm⟩, fun h => n1 h.symm⟩

/-- The text of the id field of `tranWs`. -/
theorem tranws_id {σ : State} {A : Addrs} {b0 : List UInt8} {rest : List EquivLean.Cobol.Rec.FVal}
    (hwT : JRecAt TranRecord trCls σ (.ref A.wT) (.str b0 :: rest)) :
    argText σ (fld σ A.wT trIdKey) = cp037Str b0 := by
  obtain ⟨w', fsT, hwe, hto, hf⟩ := hwT
  have ew : w' = A.wT := (Value.ref.inj hwe).symm
  subst ew
  obtain ⟨sv, hsv, sId, rfl, hsId⟩ : ∃ sv, Fields.get fsT (trCls, "tranId") = some sv ∧
      ∃ sId, sv = .ref sId ∧ σ.heap sId = some (.str (cp037Str b0)) := by
    cases hf with
    | cons j0 _ => exact j0
  simp [argText, strOfV, fld, fieldsOf, hto, hsv, hsId]

/-- The key search of `writeTransaction` fails on a new id. -/
theorem wtIdx_neg {σ : State} {A : Addrs} {s : Model.St} {b0 : List UInt8}
    {rest : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hwT : JRecAt TranRecord trCls σ (.ref A.wT) (.str b0 :: rest))
    (hn : tidJ (.str b0 :: rest) ∉ s.tranW.map tidJ) : wtIdx σ A.wT A.lK < 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hK, -⟩ := hW
  obtain ⟨ks, mK, hlK, hfK, -⟩ := hK
  have hn' : cp037Str b0 ∉ s.tranW.map tidJ := hn
  unfold wtIdx
  rw [tranws_id hwT, listOf_of hlK, firstIdx_strs_none hfK hn']
  decide

/-- The key search of `writeTransaction` succeeds on a written id. -/
theorem wtIdx_nonneg {σ : State} {A : Addrs} {s : Model.St} {b0 : List UInt8}
    {rest : List EquivLean.Cobol.Rec.FVal}
    (hW : W σ A s) (hwT : JRecAt TranRecord trCls σ (.ref A.wT) (.str b0 :: rest))
    (hm : tidJ (.str b0 :: rest) ∈ s.tranW.map tidJ) : 0 ≤ wtIdx σ A.wT A.lK := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hK, -⟩ := hW
  obtain ⟨ks, mK, hlK, hfK, -⟩ := hK
  have hm' : cp037Str b0 ∈ s.tranW.map tidJ := hm
  unfold wtIdx
  rw [tranws_id hwT, listOf_of hlK]
  exact firstIdx_strs_some hfK hm'

end EquivLean.Modernize.Cbtrn02c.Java

import EquivLean.Modernize.Cbtrn03c.RustRun7

/-!
# CBTRN03C → Rust, part 8: a record in the date range

A record in the date range whose lookups find their records (the domain): its line, then on the
current card the report lines (`step_same`); on a change of card the account totals (not before the
first transaction), the cross-reference record read, then the report lines (`step_new`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

/-! ## The model's steps -/

theorem dsp_card (s : Model.St) (l : List Nat) : (Model.dsp s l).card = s.card := rfl
theorem dsp_first (s : Model.St) (l : List Nat) : (Model.dsp s l).first = s.first := rfl
theorem dsp_xref (s : Model.St) (l : List Nat) : (Model.dsp s l).xref = s.xref := rfl

/-- The state after the card lookup on a change of card (the cross-reference record `x` found). -/
def newCardSt (s : Model.St) (L : List Nat) (t x : List FVal) : Model.St :=
  { (if s.first then Model.dsp s L else Model.acctTotals (Model.dsp s L)) with
    card := Model.tCard t
    xref := x }

theorem cardStep_same (xs : List (List FVal)) (s : Model.St) (L : List Nat) (t : List FVal)
    (h : s.card = Model.tCard t) : Model.cardStep xs (Model.dsp s L) t = .ok (Model.dsp s L) := by
  unfold Model.cardStep
  rw [ite_true_of (show (Model.dsp s L).card = Model.tCard t from h)]

theorem cardStep_new (xs : List (List FVal)) (s : Model.St) (L : List Nat) (t x : List FVal)
    (h : ¬ s.card = Model.tCard t) (hx : xs.find? (fun x => Model.xCard x == Model.tCard t) = some x) :
    Model.cardStep xs (Model.dsp s L) t = .ok (newCardSt s L t x) := by
  unfold Model.cardStep
  rw [ite_false_of (show ¬ (Model.dsp s L).card = Model.tCard t from h)]
  simp only [hx]
  rfl

theorem tranStep_found (xs ys cs : List (List FVal)) (d : List FVal) (s s1 : Model.St)
    (t y c : List FVal)
    (hcs : Model.cardStep xs (Model.dsp s (Model.TranRecord.textS t)) t = .ok s1)
    (hy : ys.find? (fun y => Model.yType y == Model.tType t) = some y)
    (hc : cs.find? (fun c => Model.cType c == Model.tType t && Model.cCat c == Model.tCat t) =
      some c) :
    Model.tranStep xs ys cs d s t = .ok (Model.report d s1 t y c) := by
  unfold Model.tranStep
  simp only [hcs, hy, hc]

theorem reportTail_first (s : Model.St) (t y c : List FVal) :
    (reportTail s t y c).first = s.first := by
  simp only [reportTail]
  split <;> rfl

theorem reportTail_card (s : Model.St) (t y c : List FVal) :
    (reportTail s t y c).card = s.card := by
  simp only [reportTail]
  split <;> rfl

theorem reportTail_xref (s : Model.St) (t y c : List FVal) :
    (reportTail s t y c).xref = s.xref := by
  simp only [reportTail]
  split <;> rfl

theorem bnd_reportTail (s : Model.St) (t y c : List FVal) (h : Bnd s) :
    Bnd (reportTail s t y c) := by
  simp only [reportTail]
  split
  · have h1 := bnd_headers _ (bnd_pageTotals _ h)
    exact bnd_inc _ (bnd_wr _ _ ⟨h1.1, trunc11_bound _, trunc11_bound _, h1.2.2.2⟩)
  · exact bnd_inc _ (bnd_wr _ _ ⟨h.1, trunc11_bound _, trunc11_bound _, h.2.2.2⟩)

theorem report_first (d : List FVal) (s : Model.St) (t y c : List FVal) :
    (Model.report d s t y c).first = false := by
  rw [report_eq, reportTail_first]
  split
  · rfl
  · simp_all

theorem report_card (d : List FVal) (s : Model.St) (t y c : List FVal) :
    (Model.report d s t y c).card = s.card := by
  rw [report_eq, reportTail_card]
  split <;> rfl

theorem report_xref (d : List FVal) (s : Model.St) (t y c : List FVal) :
    (Model.report d s t y c).xref = s.xref := by
  rw [report_eq, reportTail_xref]
  split <;> rfl

theorem bnd_report (d : List FVal) (s : Model.St) (t y c : List FVal) (h : Bnd s) :
    Bnd (Model.report d s t y c) := by
  rw [report_eq]
  apply bnd_reportTail
  split
  · exact bnd_headers _ h
  · exact h

/-! ## The paths -/

set_option maxHeartbeats 16000000 in
/-- A record in the date range on the current card (its type and category found): its line and the
report lines. -/
theorem step_same (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
    (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
    (ds : Array U8 10#usize) (df : Array U8 1#usize) (de : Array U8 10#usize) (R : Model.Out)
    (hL : s1.val.length < 2 ^ 28)
    (st : cbtrn03c.St) (a : Array U8 16#usize) (a1 : Array U8 2#usize) (i : I64)
    (a2 : Array U8 10#usize) (a3 : Array U8 100#usize) (i1 i2 : I64) (a4 a5 : Array U8 50#usize)
    (a6 : Array U8 10#usize) (a7 : Array U8 16#usize) (a8 a9 : Array U8 26#usize)
    (a10 : Array U8 20#usize) (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (first : Bool) (card : Array U8 16#usize) (idx : Usize)
    (s : Model.St) (hc : Corr st s) (hb : Bnd s) (hf : s.first = first)
    (hcard : s.card = card.val.map ebcU) (hx : s.xref = CardXrefRecord.vals xref)
    (hxa : -9223372036854775808 < xref.xref_acct_id.val)
    (hp : idx.val < s1.val.length) (t : cbtrn03c.TranRecord) (ht : s1.val[idx.val]'hp = t)
    (hc0 : 0 ≤ t.tran_cat_cd.val) (hamt : t.tran_amt.val.natAbs < 100000000000)
    (hm0 : 0 ≤ t.tran_merchant_id.val)
    (hwl : st.writes.val.length ≤ 13 * idx.val) (hdl : st.displays.val.length ≤ idx.val + 2)
    (hin : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩) (TranRecord.vals t) = true)
    (hsame : card.val = t.tran_card_num.val)
    (y : cbtrn03c.TranTypeRecord)
    (hy : s3.val.find? (fun y => decide (y.tran_type.val = t.tran_type_cd.val)) = some y)
    (c : cbtrn03c.TranCatRecord)
    (hcz : s4.val.find? (fun c => decide (c.tran_type_cd.val = t.tran_type_cd.val) &&
      decide (c.tran_cat_cd = t.tran_cat_cd)) = some c)
    (hR : rest (s2.val.map CardXrefRecord.vals) (s3.val.map TranTypeRecord.vals)
      (s4.val.map TranCatRecord.vals) (WsDateparmRecord.vals ⟨ds, df, de⟩)
      ((s1.val.map TranRecord.vals).drop (idx.val + 1)) (TranRecord.vals t)
      (Model.report (WsDateparmRecord.vals ⟨ds, df, de⟩)
        (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t))) (TranRecord.vals t)
        (TranTypeRecord.vals y) (TranCatRecord.vals c)) = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card false idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, false, idx)) := by
  have hU := usize_max_ge
  have hb1 : decide (card.val = t.tran_card_num.val) = true := decide_eq_true hsame
  have hbytes := tran_record_bytes_eq t (by omega) (by omega) (by omega)
  have hcz' := hcz
  simp only [IScalar.eq_equiv] at hcz'
  obtain ⟨hc1, hc2⟩ := inRange_true t ds df de hin
  simp only [cbtrn03c.run_loop0.body, cbtrn03c.finish]
  t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val, ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hsame, bytes_eq_eq, Array.val_to_slice, hbytes, run_loop0_loop0_eq,
    run_loop0_loop1_eq, hy, hcz, hcz']
  simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
  refine wp_mono (write_report_spec _ (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t)))
    first _ t xref y c ?_ hb hf hx ?_ hxa (by omega) hamt) ?_
  · refine ⟨?_, hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
    simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
      tranLine_text, Model.dsp]
  · show st.writes.val.length + 12 < Usize.max
    omega
  rintro _ ⟨st', rfl, hc', hl', hd'⟩
  have hl'' : st'.writes.val.length ≤ st.writes.val.length + 11 := hl'
  have hd'' : st'.displays.val.length = st.displays.val.length + 1 := by
    rw [hd']
    simp
  refine (wp_ok _ _).2 ?_
  simp only [stepPost, loopCls_cont, loopInv, loopVar, Bool.false_eq_true, ↓reduceIte,
    eq_self_iff_true, UScalar.ofNatCore_val_eq]
  refine ⟨⟨_, hc', bnd_report _ _ _ _ _ hb, report_first _ _ _ _ _, ?_, ?_, hxa, by omega,
    by omega, by omega, hamt, by omega, by omega, Or.inl ⟨by first | exact trivial | rfl, hR⟩⟩, by omega⟩
  · rw [report_card, dsp_card, hcard]
  · rw [report_xref, dsp_xref, hx]

set_option maxHeartbeats 16000000 in
/-- A record in the date range on a new card (its cross-reference, type and category found): its
line, the account totals (after the first transaction), the report lines. -/
theorem step_new (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
    (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
    (ds : Array U8 10#usize) (df : Array U8 1#usize) (de : Array U8 10#usize) (R : Model.Out)
    (hL : s1.val.length < 2 ^ 28)
    (st : cbtrn03c.St) (a : Array U8 16#usize) (a1 : Array U8 2#usize) (i : I64)
    (a2 : Array U8 10#usize) (a3 : Array U8 100#usize) (i1 i2 : I64) (a4 a5 : Array U8 50#usize)
    (a6 : Array U8 10#usize) (a7 : Array U8 16#usize) (a8 a9 : Array U8 26#usize)
    (a10 : Array U8 20#usize) (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (first : Bool) (card : Array U8 16#usize) (idx : Usize)
    (s : Model.St) (hc : Corr st s) (hb : Bnd s) (hf : s.first = first)
    (hp : idx.val < s1.val.length) (t : cbtrn03c.TranRecord) (ht : s1.val[idx.val]'hp = t)
    (hc0 : 0 ≤ t.tran_cat_cd.val) (hamt : t.tran_amt.val.natAbs < 100000000000)
    (hm0 : 0 ≤ t.tran_merchant_id.val)
    (hwl : st.writes.val.length ≤ 13 * idx.val) (hdl : st.displays.val.length ≤ idx.val + 2)
    (hin : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩) (TranRecord.vals t) = true)
    (hnew : ¬ card.val = t.tran_card_num.val)
    (x : cbtrn03c.CardXrefRecord)
    (hxr : s2.val.find? (fun x => decide (x.xref_card_num.val = t.tran_card_num.val)) = some x)
    (hxa : -9223372036854775808 < x.xref_acct_id.val)
    (y : cbtrn03c.TranTypeRecord)
    (hy : s3.val.find? (fun y => decide (y.tran_type.val = t.tran_type_cd.val)) = some y)
    (c : cbtrn03c.TranCatRecord)
    (hcz : s4.val.find? (fun c => decide (c.tran_type_cd.val = t.tran_type_cd.val) &&
      decide (c.tran_cat_cd = t.tran_cat_cd)) = some c)
    (hR : rest (s2.val.map CardXrefRecord.vals) (s3.val.map TranTypeRecord.vals)
      (s4.val.map TranCatRecord.vals) (WsDateparmRecord.vals ⟨ds, df, de⟩)
      ((s1.val.map TranRecord.vals).drop (idx.val + 1)) (TranRecord.vals t)
      (Model.report (WsDateparmRecord.vals ⟨ds, df, de⟩)
        (newCardSt s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t)
          (CardXrefRecord.vals x)) (TranRecord.vals t)
        (TranTypeRecord.vals y) (TranCatRecord.vals c)) = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card false idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, false, idx)) := by
  have hU := usize_max_ge
  have hb1 : decide (card.val = t.tran_card_num.val) = false := decide_eq_false hnew
  have hbytes := tran_record_bytes_eq t (by omega) (by omega) (by omega)
  have hcz' := hcz
  simp only [IScalar.eq_equiv] at hcz'
  have hdisp : ∀ v : alloc.vec.Vec (alloc.vec.Vec U8),
      v.val = st.displays.val ++ [alloc.vec.Vec.from (tranLine t)
        (by rw [tranLine_length]; omega)] →
      v.val.map (fun l => l.val.map UScalar.val) =
        (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t))).disp := by
    intro v hv
    rw [hv]
    simp only [List.map_append, List.map_cons, List.map_nil, hc.disp, alloc.vec.Vec.from_val,
      tranLine_text, Model.dsp]
  obtain ⟨hc1, hc2⟩ := inRange_true t ds df de hin
  simp only [cbtrn03c.run_loop0.body, cbtrn03c.finish]
  cases first with
  | true =>
    t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val, ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hnew, bytes_eq_eq, Array.val_to_slice, hbytes, run_loop0_loop2_eq, run_loop0_loop3_eq, run_loop0_loop4_eq,
      hxr, hy, hcz, hcz']
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (write_report_spec _ (newCardSt s (Model.TranRecord.textS (TranRecord.vals t))
      (TranRecord.vals t) (CardXrefRecord.vals x)) true _ t x y c ?_ ?_ ?_ rfl
      ?_ hxa (by omega) hamt) ?_
    · simp only [newCardSt, hf, ↓reduceIte, eq_self_iff_true]
      exact ⟨hdisp _ (by simp), hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
    · simp only [newCardSt, hf, ↓reduceIte, eq_self_iff_true]
      exact hb
    · simp only [newCardSt, hf, ↓reduceIte, eq_self_iff_true]
      exact hf
    · show st.writes.val.length + 12 < Usize.max
      omega
    rintro _ ⟨st', rfl, hc', hl', hd'⟩
    have hl'' : st'.writes.val.length ≤ st.writes.val.length + 11 := hl'
    have hd'' : st'.displays.val.length = st.displays.val.length + 1 := by
      rw [hd']
      simp
    refine (wp_ok _ _).2 ?_
    simp only [stepPost, loopCls_cont, loopInv, loopVar, Bool.false_eq_true, ↓reduceIte,
      eq_self_iff_true, UScalar.ofNatCore_val_eq]
    refine ⟨⟨_, hc', bnd_report _ _ _ _ _ ?_, report_first _ _ _ _ _, ?_, ?_, hxa, by omega,
      by omega, by omega, hamt, by omega, by omega, Or.inl ⟨by first | exact trivial | rfl, hR⟩⟩, by omega⟩
    · simp only [newCardSt, hf, ↓reduceIte, eq_self_iff_true]
      exact hb
    · rw [report_card]
      rfl
    · rw [report_xref]
      rfl
  | false =>
    t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val, ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hnew, bytes_eq_eq, Array.val_to_slice, hbytes, run_loop0_loop2_eq, run_loop0_loop3_eq, run_loop0_loop4_eq,
      hxr, hy, hcz, hcz']
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (write_account_totals_spec _
      (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t))) ?_ hb ?_) ?_
    · exact ⟨hdisp _ (by simp), hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
    · show st.writes.val.length + 2 < Usize.max
      omega
    rintro _ ⟨st1, rfl, hc1, hl1, hd1⟩
    have hl1' : st1.writes.val.length = st.writes.val.length + 2 := hl1
    have hb2 : Bnd (newCardSt s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t)
        (CardXrefRecord.vals x)) := by
      simp only [newCardSt, hf, Bool.false_eq_true, ↓reduceIte]
      exact bnd_acctTotals _ hb
    dsimp only
    refine wp_mono (write_report_spec st1 (newCardSt s (Model.TranRecord.textS (TranRecord.vals t))
      (TranRecord.vals t) (CardXrefRecord.vals x)) false _ t x y c ?_ hb2 ?_ rfl
      (by omega) hxa (by omega) hamt) ?_
    · simp only [newCardSt, hf, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hc1.disp, hc1.writes, hc1.lc, hc1.page, hc1.acct, hc1.grand, hc1.rs, hc1.re⟩
    · simp only [newCardSt, hf, Bool.false_eq_true, ↓reduceIte]
      exact hf
    rintro _ ⟨st', rfl, hc', hl', hd'⟩
    have hl'' : st'.writes.val.length ≤ st1.writes.val.length + 11 := hl'
    have hd'' : st'.displays.val.length = st.displays.val.length + 1 := by
      rw [hd', hd1]
      simp
    refine (wp_ok _ _).2 ?_
    simp only [stepPost, loopCls_cont, loopInv, loopVar, Bool.false_eq_true, ↓reduceIte,
      eq_self_iff_true, UScalar.ofNatCore_val_eq]
    refine ⟨⟨_, hc', bnd_report _ _ _ _ _ hb2, report_first _ _ _ _ _, ?_, ?_, hxa, by omega,
      by omega, by omega, hamt, by omega, by omega, Or.inl ⟨by first | exact trivial | rfl, hR⟩⟩, by omega⟩
    · rw [report_card]
      rfl
    · rw [report_xref]
      rfl

end EquivLean.Modernize.Cbtrn03c.Rust

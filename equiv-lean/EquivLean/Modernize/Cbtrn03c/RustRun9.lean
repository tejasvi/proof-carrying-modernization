import EquivLean.Modernize.Cbtrn03c.RustRun8

/-!
# CBTRN03C → Rust, part 9: the failed lookups

A record in the date range whose cross-reference, transaction type or category is not found: its
line (after the account totals on a change of card), the message with the key, the file status
and the abend message (`Model.abend23`); the run ends abended.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

/-! ## The model -/

/-- The state after a change of card, before the cross-reference lookup. -/
def cardSt0 (s : Model.St) (L : List Nat) (t : List FVal) : Model.St :=
  { (if s.first then Model.dsp s L else Model.acctTotals (Model.dsp s L)) with
    card := Model.tCard t }

theorem cardStep_nox (xs : List (List FVal)) (s : Model.St) (L : List Nat) (t : List FVal)
    (h : ¬ s.card = Model.tCard t) (hx : xs.find? (fun x => Model.xCard x == Model.tCard t) = none) :
    Model.cardStep xs (Model.dsp s L) t = .error (Model.abend23 (cardSt0 s L t)
      (Model.txt "INVALID CARD NUMBER : " ++ Model.cps (Model.tCard t))) := by
  unfold Model.cardStep
  rw [ite_false_of (show ¬ (Model.dsp s L).card = Model.tCard t from h)]
  simp only [hx]
  rfl

theorem tranStep_err (xs ys cs : List (List FVal)) (d : List FVal) (s e : Model.St)
    (t : List FVal)
    (hcs : Model.cardStep xs (Model.dsp s (Model.TranRecord.textS t)) t = .error e) :
    Model.tranStep xs ys cs d s t = .error e := by
  unfold Model.tranStep
  simp only [hcs]

theorem tranStep_noty (xs ys cs : List (List FVal)) (d : List FVal) (s s1 : Model.St)
    (t : List FVal)
    (hcs : Model.cardStep xs (Model.dsp s (Model.TranRecord.textS t)) t = .ok s1)
    (hy : ys.find? (fun y => Model.yType y == Model.tType t) = none) :
    Model.tranStep xs ys cs d s t = .error (Model.abend23 s1
      (Model.txt "INVALID TRANSACTION TYPE : " ++ Model.cps (Model.tType t))) := by
  unfold Model.tranStep
  simp only [hcs, hy]

theorem tranStep_nocat (xs ys cs : List (List FVal)) (d : List FVal) (s s1 : Model.St)
    (t y : List FVal)
    (hcs : Model.cardStep xs (Model.dsp s (Model.TranRecord.textS t)) t = .ok s1)
    (hy : ys.find? (fun y => Model.yType y == Model.tType t) = some y)
    (hc : cs.find? (fun c => Model.cType c == Model.tType t && Model.cCat c == Model.tCat t) =
      none) :
    Model.tranStep xs ys cs d s t = .error (Model.abend23 s1
      (Model.txt "INVALID TRAN CATG KEY : " ++ Model.cps (Model.tType t) ++
        Model.digs 4 (Model.tCat t))) := by
  unfold Model.tranStep
  simp only [hcs, hy, hc]

theorem txt_invType : Model.txt "INVALID TRANSACTION TYPE : " = [73, 78, 86, 65, 76, 73, 68, 32,
    84, 82, 65, 78, 83, 65, 67, 84, 73, 79, 78, 32, 84, 89, 80, 69, 32, 58, 32] := by
  decide

theorem txt_invCat : Model.txt "INVALID TRAN CATG KEY : " = [73, 78, 86, 65, 76, 73, 68, 32, 84,
    82, 65, 78, 32, 67, 65, 84, 71, 32, 75, 69, 89, 32, 58, 32] := by
  decide

theorem txt_invCard : Model.txt "INVALID CARD NUMBER : " = [73, 78, 86, 65, 76, 73, 68, 32, 67, 65,
    82, 68, 32, 78, 85, 77, 66, 69, 82, 32, 58, 32] := by
  decide

/-- The outputs of an abended run: the state after `abend_status23`. -/
theorem abend_out (st2 : cbtrn03c.St) (S : Model.St) (msg : List Nat) (R : Model.Out)
    (hc2 : Corr st2 (Model.dsp (Model.dsp (Model.dsp S msg) (Model.txt "FILE STATUS IS: NNNN0023"))
      (Model.txt "ABENDING PROGRAM")))
    (hR : Model.out (Model.abend23 S msg) true = R) :
    OutQ R (.ok { displays := st2.displays, report_file_writes := st2.writes, abended := true }) := by
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [← hR]
    exact hc2.disp
  · rw [← hR]
    exact out_writes st2 _ hc2 true
  · rw [← hR]
    rfl

/-! ## The paths -/

set_option maxHeartbeats 16000000 in
/-- On the current card, the transaction type not found. -/
theorem step_same_noty (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
    (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
    (ds : Array U8 10#usize) (df : Array U8 1#usize) (de : Array U8 10#usize) (R : Model.Out)
    (hL : s1.val.length < 2 ^ 28)
    (st : cbtrn03c.St) (a : Array U8 16#usize) (a1 : Array U8 2#usize) (i : I64)
    (a2 : Array U8 10#usize) (a3 : Array U8 100#usize) (i1 i2 : I64) (a4 a5 : Array U8 50#usize)
    (a6 : Array U8 10#usize) (a7 : Array U8 16#usize) (a8 a9 : Array U8 26#usize)
    (a10 : Array U8 20#usize) (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (first : Bool) (card : Array U8 16#usize) (idx : Usize)
    (s : Model.St) (hc : Corr st s)
    (hp : idx.val < s1.val.length) (t : cbtrn03c.TranRecord) (ht : s1.val[idx.val]'hp = t)
    (hc0 : 0 ≤ t.tran_cat_cd.val) (hamt : t.tran_amt.val.natAbs < 100000000000)
    (hm0 : 0 ≤ t.tran_merchant_id.val) (hdl : st.displays.val.length ≤ idx.val + 2)
    (hin : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩) (TranRecord.vals t) = true)
    (hsame : card.val = t.tran_card_num.val)
    (hy : s3.val.find? (fun y => decide (y.tran_type.val = t.tran_type_cd.val)) = none)
    (hR : Model.out (Model.abend23 (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t)))
      (Model.txt "INVALID TRANSACTION TYPE : " ++ Model.cps (Model.tType (TranRecord.vals t))))
      true = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card false idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, false, idx)) := by
  have hU := usize_max_ge
  have hb1 : decide (card.val = t.tran_card_num.val) = true := decide_eq_true hsame
  have hbytes := tran_record_bytes_eq t (by omega) (by omega) (by omega)
  obtain ⟨hc1, hc2⟩ := inRange_true t ds df de hin
  simp only [cbtrn03c.run_loop0.body, cbtrn03c.finish]
  t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val,
    ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hsame, bytes_eq_eq, Array.val_to_slice, hbytes,
    run_loop0_loop0_eq, hy]
  simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
    [dite_eq_left]
  refine wp_mono (abend_status23_spec _ (Model.dsp
    (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t)))
    (Model.txt "INVALID TRANSACTION TYPE : " ++ Model.cps (Model.tType (TranRecord.vals t))))
    ?_ ?_) ?_
  · refine ⟨?_, hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
    simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
      tranLine_text, Model.dsp, uscalar_ofNat_val, List.nil_append, tType_vals, cps_ebcU,
      txt_invType, List.append_assoc]
  · simp only [alloc.vec.Vec.from_val, List.length_append, List.length_cons, List.length_nil]
    omega
  rintro _ ⟨st2, rfl, hc2', -⟩
  dsimp only
  simp only [wp_ok, stepPost, loopCls_done]
  exact abend_out st2 _ _ R hc2' hR

set_option maxHeartbeats 16000000 in
/-- On the current card, the type found and the category not found. -/
theorem step_same_nocat (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
    (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
    (ds : Array U8 10#usize) (df : Array U8 1#usize) (de : Array U8 10#usize) (R : Model.Out)
    (hL : s1.val.length < 2 ^ 28)
    (st : cbtrn03c.St) (a : Array U8 16#usize) (a1 : Array U8 2#usize) (i : I64)
    (a2 : Array U8 10#usize) (a3 : Array U8 100#usize) (i1 i2 : I64) (a4 a5 : Array U8 50#usize)
    (a6 : Array U8 10#usize) (a7 : Array U8 16#usize) (a8 a9 : Array U8 26#usize)
    (a10 : Array U8 20#usize) (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (first : Bool) (card : Array U8 16#usize) (idx : Usize)
    (s : Model.St) (hc : Corr st s)
    (hp : idx.val < s1.val.length) (t : cbtrn03c.TranRecord) (ht : s1.val[idx.val]'hp = t)
    (hc0 : 0 ≤ t.tran_cat_cd.val) (hamt : t.tran_amt.val.natAbs < 100000000000)
    (hm0 : 0 ≤ t.tran_merchant_id.val) (hdl : st.displays.val.length ≤ idx.val + 2)
    (hin : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩) (TranRecord.vals t) = true)
    (hsame : card.val = t.tran_card_num.val)
    (y : cbtrn03c.TranTypeRecord)
    (hy : s3.val.find? (fun y => decide (y.tran_type.val = t.tran_type_cd.val)) = some y)
    (hcz : s4.val.find? (fun c => decide (c.tran_type_cd.val = t.tran_type_cd.val) &&
      decide (c.tran_cat_cd = t.tran_cat_cd)) = none)
    (hR : Model.out (Model.abend23 (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t)))
      (Model.txt "INVALID TRAN CATG KEY : " ++ Model.cps (Model.tType (TranRecord.vals t)) ++
        Model.digs 4 (Model.tCat (TranRecord.vals t)))) true = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card false idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, false, idx)) := by
  have hU := usize_max_ge
  have hb1 : decide (card.val = t.tran_card_num.val) = true := decide_eq_true hsame
  have hbytes := tran_record_bytes_eq t (by omega) (by omega) (by omega)
  have hcz' := hcz
  simp only [IScalar.eq_equiv] at hcz'
  have hcat : -9223372036854775808 < t.tran_cat_cd.val := by omega
  obtain ⟨hc1, hc2⟩ := inRange_true t ds df de hin
  simp only [cbtrn03c.run_loop0.body, cbtrn03c.finish]
  t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val,
    ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hsame, bytes_eq_eq, Array.val_to_slice, hbytes,
    run_loop0_loop0_eq, run_loop0_loop1_eq, hy, hcz, hcz', hcat]
  simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
    [dite_eq_left]
  refine wp_mono (abend_status23_spec _ (Model.dsp
    (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t)))
    (Model.txt "INVALID TRAN CATG KEY : " ++ Model.cps (Model.tType (TranRecord.vals t)) ++
      Model.digs 4 (Model.tCat (TranRecord.vals t)))) ?_ ?_) ?_
  · refine ⟨?_, hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
    simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
      tranLine_text, Model.dsp, uscalar_ofNat_val, List.nil_append, tType_vals, tCat_vals,
      cps_ebcU, Model.digs, zeroPad_val, txt_invCat, List.append_assoc]
  · simp only [alloc.vec.Vec.from_val, List.length_append, List.length_cons, List.length_nil]
    omega
  rintro _ ⟨st2, rfl, hc2', -⟩
  dsimp only
  simp only [wp_ok, stepPost, loopCls_done]
  exact abend_out st2 _ _ R hc2' hR

set_option maxHeartbeats 16000000 in
/-- On a new card, the cross-reference not found. -/
theorem step_new_nox (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
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
    (hxr : s2.val.find? (fun x => decide (x.xref_card_num.val = t.tran_card_num.val)) = none)
    (hR : Model.out (Model.abend23 (cardSt0 s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t))
      (Model.txt "INVALID CARD NUMBER : " ++ Model.cps (Model.tCard (TranRecord.vals t)))) true = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card false idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, false, idx)) := by
  have hU := usize_max_ge
  have hb1 : decide (card.val = t.tran_card_num.val) = false := decide_eq_false hnew
  have hbytes := tran_record_bytes_eq t (by omega) (by omega) (by omega)
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
    t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val,
      ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hnew, bytes_eq_eq, Array.val_to_slice, hbytes,
      run_loop0_loop2_eq, hxr]
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (abend_status23_spec _ (Model.dsp (cardSt0 s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t)) (Model.txt "INVALID CARD NUMBER : " ++ Model.cps (Model.tCard (TranRecord.vals t)))) ?_ ?_) ?_
    · simp only [cardSt0, hf, ↓reduceIte, eq_self_iff_true]
      refine ⟨?_, hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
        tranLine_text, Model.dsp, uscalar_ofNat_val, List.nil_append, tCard_vals, cps_ebcU, txt_invCard,
        List.append_assoc]
    · simp only [alloc.vec.Vec.from_val, List.length_append, List.length_cons, List.length_nil]
      omega
    rintro _ ⟨st2, rfl, hc2', -⟩
    dsimp only
    simp only [wp_ok, stepPost, loopCls_done]
    exact abend_out st2 _ _ R hc2' hR
  | false =>
    t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val,
      ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hnew, bytes_eq_eq, Array.val_to_slice, hbytes,
      run_loop0_loop2_eq, hxr]
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (write_account_totals_spec _ (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t))) ?_ hb ?_) ?_
    · exact ⟨hdisp _ (by simp), hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
    · show st.writes.val.length + 2 < Usize.max
      omega
    rintro _ ⟨st1, rfl, hc1', -, hd1⟩
    have hd1' : st1.displays.val.length = st.displays.val.length + 1 := by
      rw [hd1]
      simp
    dsimp only
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (abend_status23_spec _ (Model.dsp (cardSt0 s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t)) (Model.txt "INVALID CARD NUMBER : " ++ Model.cps (Model.tCard (TranRecord.vals t)))) ?_ ?_) ?_
    · simp only [cardSt0, hf, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, hc1'.writes, hc1'.lc, hc1'.page, hc1'.acct, hc1'.grand, hc1'.rs, hc1'.re⟩
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc1'.disp,
        Model.dsp, uscalar_ofNat_val, List.nil_append, tCard_vals, cps_ebcU, txt_invCard, List.append_assoc]
    · simp only [alloc.vec.Vec.from_val, List.length_append, List.length_cons, List.length_nil]
      omega
    rintro _ ⟨st2, rfl, hc2', -⟩
    dsimp only
    simp only [wp_ok, stepPost, loopCls_done]
    exact abend_out st2 _ _ R hc2' hR

set_option maxHeartbeats 16000000 in
/-- On a new card, the cross-reference found and the type not found. -/
theorem step_new_noty (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
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
    (hy : s3.val.find? (fun y => decide (y.tran_type.val = t.tran_type_cd.val)) = none)
    (hR : Model.out (Model.abend23 (newCardSt s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t) (CardXrefRecord.vals x))
      (Model.txt "INVALID TRANSACTION TYPE : " ++ Model.cps (Model.tType (TranRecord.vals t)))) true = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card false idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, false, idx)) := by
  have hU := usize_max_ge
  have hb1 : decide (card.val = t.tran_card_num.val) = false := decide_eq_false hnew
  have hbytes := tran_record_bytes_eq t (by omega) (by omega) (by omega)
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
    t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val,
      ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hnew, bytes_eq_eq, Array.val_to_slice, hbytes,
      run_loop0_loop2_eq, run_loop0_loop3_eq, hxr, hy]
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (abend_status23_spec _ (Model.dsp (newCardSt s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t) (CardXrefRecord.vals x)) (Model.txt "INVALID TRANSACTION TYPE : " ++ Model.cps (Model.tType (TranRecord.vals t)))) ?_ ?_) ?_
    · simp only [newCardSt, hf, ↓reduceIte, eq_self_iff_true]
      refine ⟨?_, hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
        tranLine_text, Model.dsp, uscalar_ofNat_val, List.nil_append, tType_vals, cps_ebcU, txt_invType,
        List.append_assoc]
    · simp only [alloc.vec.Vec.from_val, List.length_append, List.length_cons, List.length_nil]
      omega
    rintro _ ⟨st2, rfl, hc2', -⟩
    dsimp only
    simp only [wp_ok, stepPost, loopCls_done]
    exact abend_out st2 _ _ R hc2' hR
  | false =>
    t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val,
      ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hnew, bytes_eq_eq, Array.val_to_slice, hbytes,
      run_loop0_loop2_eq, run_loop0_loop3_eq, hxr, hy]
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (write_account_totals_spec _ (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t))) ?_ hb ?_) ?_
    · exact ⟨hdisp _ (by simp), hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
    · show st.writes.val.length + 2 < Usize.max
      omega
    rintro _ ⟨st1, rfl, hc1', -, hd1⟩
    have hd1' : st1.displays.val.length = st.displays.val.length + 1 := by
      rw [hd1]
      simp
    dsimp only
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (abend_status23_spec _ (Model.dsp (newCardSt s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t) (CardXrefRecord.vals x)) (Model.txt "INVALID TRANSACTION TYPE : " ++ Model.cps (Model.tType (TranRecord.vals t)))) ?_ ?_) ?_
    · simp only [newCardSt, hf, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, hc1'.writes, hc1'.lc, hc1'.page, hc1'.acct, hc1'.grand, hc1'.rs, hc1'.re⟩
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc1'.disp,
        Model.dsp, uscalar_ofNat_val, List.nil_append, tType_vals, cps_ebcU, txt_invType, List.append_assoc]
    · simp only [alloc.vec.Vec.from_val, List.length_append, List.length_cons, List.length_nil]
      omega
    rintro _ ⟨st2, rfl, hc2', -⟩
    dsimp only
    simp only [wp_ok, stepPost, loopCls_done]
    exact abend_out st2 _ _ R hc2' hR

set_option maxHeartbeats 16000000 in
/-- On a new card, the cross-reference and type found and the category not found. -/
theorem step_new_nocat (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
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
    (y : cbtrn03c.TranTypeRecord)
    (hy : s3.val.find? (fun y => decide (y.tran_type.val = t.tran_type_cd.val)) = some y)
    (hcz : s4.val.find? (fun c => decide (c.tran_type_cd.val = t.tran_type_cd.val) &&
      decide (c.tran_cat_cd = t.tran_cat_cd)) = none)
    (hR : Model.out (Model.abend23 (newCardSt s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t) (CardXrefRecord.vals x))
      (Model.txt "INVALID TRAN CATG KEY : " ++ Model.cps (Model.tType (TranRecord.vals t)) ++
        Model.digs 4 (Model.tCat (TranRecord.vals t)))) true = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card false idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, false, idx)) := by
  have hU := usize_max_ge
  have hb1 : decide (card.val = t.tran_card_num.val) = false := decide_eq_false hnew
  have hbytes := tran_record_bytes_eq t (by omega) (by omega) (by omega)
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
  have hcz' := hcz
  simp only [IScalar.eq_equiv] at hcz'
  have hcat : -9223372036854775808 < t.tran_cat_cd.val := by omega
  simp only [cbtrn03c.run_loop0.body, cbtrn03c.finish]
  cases first with
  | true =>
    t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val,
      ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hnew, bytes_eq_eq, Array.val_to_slice, hbytes,
      run_loop0_loop2_eq, run_loop0_loop3_eq, run_loop0_loop4_eq, hxr, hy, hcz, hcz', hcat]
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (abend_status23_spec _ (Model.dsp (newCardSt s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t) (CardXrefRecord.vals x)) (Model.txt "INVALID TRAN CATG KEY : " ++ Model.cps (Model.tType (TranRecord.vals t)) ++
        Model.digs 4 (Model.tCat (TranRecord.vals t)))) ?_ ?_) ?_
    · simp only [newCardSt, hf, ↓reduceIte, eq_self_iff_true]
      refine ⟨?_, hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
        tranLine_text, Model.dsp, uscalar_ofNat_val, List.nil_append, tType_vals, tCat_vals, cps_ebcU, Model.digs, zeroPad_val, txt_invCat,
        List.append_assoc]
    · simp only [alloc.vec.Vec.from_val, List.length_append, List.length_cons, List.length_nil]
      omega
    rintro _ ⟨st2, rfl, hc2', -⟩
    dsimp only
    simp only [wp_ok, stepPost, loopCls_done]
    exact abend_out st2 _ _ R hc2' hR
  | false =>
    t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val,
      ordI_nonneg, ordI_nonpos, hc1, hc2, hb1, hnew, bytes_eq_eq, Array.val_to_slice, hbytes,
      run_loop0_loop2_eq, run_loop0_loop3_eq, run_loop0_loop4_eq, hxr, hy, hcz, hcz', hcat]
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (write_account_totals_spec _ (Model.dsp s (Model.TranRecord.textS (TranRecord.vals t))) ?_ hb ?_) ?_
    · exact ⟨hdisp _ (by simp), hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩
    · show st.writes.val.length + 2 < Usize.max
      omega
    rintro _ ⟨st1, rfl, hc1', -, hd1⟩
    have hd1' : st1.displays.val.length = st.displays.val.length + 1 := by
      rw [hd1]
      simp
    dsimp only
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    refine wp_mono (abend_status23_spec _ (Model.dsp (newCardSt s (Model.TranRecord.textS (TranRecord.vals t)) (TranRecord.vals t) (CardXrefRecord.vals x)) (Model.txt "INVALID TRAN CATG KEY : " ++ Model.cps (Model.tType (TranRecord.vals t)) ++
        Model.digs 4 (Model.tCat (TranRecord.vals t)))) ?_ ?_) ?_
    · simp only [newCardSt, hf, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, hc1'.writes, hc1'.lc, hc1'.page, hc1'.acct, hc1'.grand, hc1'.rs, hc1'.re⟩
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc1'.disp,
        Model.dsp, uscalar_ofNat_val, List.nil_append, tType_vals, tCat_vals, cps_ebcU, Model.digs, zeroPad_val, txt_invCat, List.append_assoc]
    · simp only [alloc.vec.Vec.from_val, List.length_append, List.length_cons, List.length_nil]
      omega
    rintro _ ⟨st2, rfl, hc2', -⟩
    dsimp only
    simp only [wp_ok, stepPost, loopCls_done]
    exact abend_out st2 _ _ R hc2' hR

end EquivLean.Modernize.Cbtrn03c.Rust

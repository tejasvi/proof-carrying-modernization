import EquivLean.Modernize.Cbtrn03c.RustRun4

/-!
# CBTRN03C → Rust, part 5: the report step, the abend, the record line

`write_transaction_report` is `Model.report`; `abend_status23` writes the end of
`Model.abend23`; `tran_record_bytes` is the record's text (`Schema.textS`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

/-! ## The report step -/

/-- `Model.report` after the first-time headers. -/
def reportTail (s : Model.St) (t y c : List FVal) : Model.St :=
  let s := if s.lc % 20 = 0 then Model.headers (Model.pageTotals s) else s
  let s := { s with
    page := Model.trunc11 (s.page + Model.tAmt t)
    acct := Model.trunc11 (s.acct + Model.tAmt t) }
  Model.inc (Model.wr s (Model.detailLine t s.xref y c))

theorem report_eq (d : List FVal) (s : Model.St) (t y c : List FVal) :
    Model.report d s t y c = reportTail (if s.first then Model.headers { s with
      first := false
      rs := Model.cps (Model.dStart d)
      re := Model.cps (Model.dEnd d) } else s) t y c := rfl

set_option maxHeartbeats 8000000 in
/-- `write_transaction_report` after the first transaction: `reportTail`. -/
theorem write_report_false_spec (st : cbtrn03c.St) (s : Model.St)
    (dates : cbtrn03c.WsDateparmRecord) (tran : cbtrn03c.TranRecord)
    (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (hc : Corr st s) (hb : Bnd s)
    (hx : s.xref = CardXrefRecord.vals xref) (hw : st.writes.val.length + 8 < Usize.max)
    (ha : -9223372036854775808 < xref.xref_acct_id.val)
    (hcat : -9223372036854775808 < tran.tran_cat_cd.val)
    (hamt : tran.tran_amt.val.natAbs < 100000000000) :
    wp (cbtrn03c.write_transaction_report st false dates tran xref ttype tcat) (fun o =>
      ∃ st', o = .ok (st', false) ∧
        Corr st' (reportTail s (TranRecord.vals tran) (TranTypeRecord.vals ttype)
          (TranCatRecord.vals tcat)) ∧
        st'.writes.val.length ≤ st.writes.val.length + 7 ∧ st'.displays = st.displays) := by
  obtain ⟨hlc, hpg, hac, hgr⟩ := hb
  have hamt' : -9223372036854775808 < tran.tran_amt.val := by omega
  have hpa : -100000000000 < tran.tran_amt.val ∧ tran.tran_amt.val < 100000000000 := by omega
  have hl : 0 ≤ st.line_counter.val ∧ st.line_counter.val < 1000000000 := by
    rw [hc.lc]; omega
  unfold cbtrn03c.write_transaction_report cbtrn03c.trunc11
  t03_wp [List.nil_append]
  split
  · rename_i h
    have h20 : s.lc % 20 = 0 := by
      simp only [IScalar.eq_equiv, iscalar_srem_val, iscalar_ofInt_val, hc.lc] at h
      rw [Int.tmod_eq_emod_of_nonneg (by omega)] at h
      omega
    refine wp_mono (write_page_totals_spec st s hc ⟨hlc, hpg, hac, hgr⟩ (by omega)) ?_
    rintro _ ⟨st3, rfl, hc3, hl3, hd3⟩
    dsimp only
    refine wp_mono (write_headers_spec st3 _ hc3 (bnd_pageTotals s ⟨hlc, hpg, hac, hgr⟩)
      (by omega)) ?_
    rintro _ ⟨st4, rfl, hc4, hl4, hd4⟩
    dsimp only
    have hp4 : st4.page_total.val = 0 := hc4.page
    have ha4 : st4.account_total.val = s.acct := hc4.acct
    have ha4' : -100000000000 < st4.account_total.val ∧ st4.account_total.val < 100000000000 := by
      rw [ha4]; omega
    simp (disch := first | omega | scalar_tac) only [dite_eq_left]
    refine wp_mono (write_detail_spec _ { Model.headers (Model.pageTotals s) with
        page := Model.trunc11 ((Model.headers (Model.pageTotals s)).page +
          Model.tAmt (TranRecord.vals tran))
        acct := Model.trunc11 ((Model.headers (Model.pageTotals s)).acct +
          Model.tAmt (TranRecord.vals tran)) } tran xref ttype tcat ?_ ?_ hx ?_ ha hcat hamt') ?_
    · exact ⟨hc4.disp, hc4.writes, hc4.lc,
        by simp only [iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val, hp4, tAmt_vals,
          Model.trunc11, Model.headers, Model.pageTotals, Model.inc, Model.wr],
        by simp only [iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val, ha4, tAmt_vals,
          Model.trunc11, Model.headers, Model.pageTotals, Model.inc, Model.wr],
        hc4.grand, hc4.rs, hc4.re⟩
    · exact (bnd_headers _ (bnd_pageTotals s ⟨hlc, hpg, hac, hgr⟩)).1
    · show st4.writes.val.length + 1 < Usize.max
      omega
    · rintro _ ⟨st5, rfl, hc5, hl5, hd5⟩
      have hl5' : st5.writes.val.length = st4.writes.val.length + 1 := hl5
      have hd5' : st5.displays = st.displays := hd5.trans (hd4.trans hd3)
      have hc5' : Corr st5 (reportTail s (TranRecord.vals tran) (TranTypeRecord.vals ttype)
          (TranCatRecord.vals tcat)) := by
        simpa only [reportTail, ite_true_of h20] using hc5
      first
        | exact ⟨st5, rfl, hc5', by omega, hd5'⟩
        | exact ⟨hc5', by omega, hd5'⟩
  · rename_i h
    have h20 : ¬ s.lc % 20 = 0 := by
      intro h'
      apply h
      simp only [IScalar.eq_equiv, iscalar_srem_val, iscalar_ofInt_val, hc.lc]
      rw [Int.tmod_eq_emod_of_nonneg (by omega)]
      omega
    have hp' : -100000000000 < st.page_total.val ∧ st.page_total.val < 100000000000 := by
      rw [hc.page]; omega
    have ha' : -100000000000 < st.account_total.val ∧ st.account_total.val < 100000000000 := by
      rw [hc.acct]; omega
    simp (disch := first | omega | scalar_tac) only [dite_eq_left]
    refine wp_mono (write_detail_spec _ { s with
        page := Model.trunc11 (s.page + Model.tAmt (TranRecord.vals tran))
        acct := Model.trunc11 (s.acct + Model.tAmt (TranRecord.vals tran)) }
      tran xref ttype tcat ?_ hlc hx ?_ ha hcat hamt') ?_
    · exact ⟨hc.disp, hc.writes, hc.lc,
        by simp only [iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val, hc.page,
          tAmt_vals, Model.trunc11],
        by simp only [iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val, hc.acct,
          tAmt_vals, Model.trunc11],
        hc.grand, hc.rs, hc.re⟩
    · show st.writes.val.length + 1 < Usize.max
      omega
    · rintro _ ⟨st5, rfl, hc5, hl5, hd5⟩
      have hl5' : st5.writes.val.length = st.writes.val.length + 1 := hl5
      have hd5' : st5.displays = st.displays := hd5
      have hc5' : Corr st5 (reportTail s (TranRecord.vals tran) (TranTypeRecord.vals ttype)
          (TranCatRecord.vals tcat)) := by
        simpa only [reportTail, ite_false_of h20] using hc5
      first
        | exact ⟨st5, rfl, hc5', by omega, hd5'⟩
        | exact ⟨hc5', by omega, hd5'⟩

/-- `write_transaction_report` at the first transaction: the headers, then the later case. -/
theorem wtr_true (st : cbtrn03c.St) (dates : cbtrn03c.WsDateparmRecord)
    (tran : cbtrn03c.TranRecord) (xref : cbtrn03c.CardXrefRecord)
    (ttype : cbtrn03c.TranTypeRecord) (tcat : cbtrn03c.TranCatRecord) :
    cbtrn03c.write_transaction_report st true dates tran xref ttype tcat =
      (do
        let st2 ← cbtrn03c.write_headers { st with
          rept_start_date := dates.ws_start_date
          rept_end_date := dates.ws_end_date }
        cbtrn03c.write_transaction_report st2 false dates tran xref ttype tcat) := by
  unfold cbtrn03c.write_transaction_report
  simp only [↓reduceIte, Bool.false_eq_true, Aeneas.Std.bind_assoc, bind_ok]

set_option maxHeartbeats 8000000 in
/-- **`write_transaction_report` is `Model.report`.** -/
theorem write_report_spec (st : cbtrn03c.St) (s : Model.St) (first : Bool)
    (dates : cbtrn03c.WsDateparmRecord) (tran : cbtrn03c.TranRecord)
    (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (hc : Corr st s) (hb : Bnd s) (hf : s.first = first)
    (hx : s.xref = CardXrefRecord.vals xref) (hw : st.writes.val.length + 12 < Usize.max)
    (ha : -9223372036854775808 < xref.xref_acct_id.val)
    (hcat : -9223372036854775808 < tran.tran_cat_cd.val)
    (hamt : tran.tran_amt.val.natAbs < 100000000000) :
    wp (cbtrn03c.write_transaction_report st first dates tran xref ttype tcat) (fun o =>
      ∃ st', o = .ok (st', false) ∧
        Corr st' (Model.report (WsDateparmRecord.vals dates) s (TranRecord.vals tran)
          (TranTypeRecord.vals ttype) (TranCatRecord.vals tcat)) ∧
        st'.writes.val.length ≤ st.writes.val.length + 11 ∧ st'.displays = st.displays) := by
  rw [report_eq]
  cases first with
  | false =>
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    exact wp_mono (write_report_false_spec st s dates tran xref ttype tcat hc hb hx (by omega) ha
      hcat hamt) fun _ ⟨st', h1, h2, h3, h4⟩ => ⟨st', h1, h2, by omega, h4⟩
  | true =>
    simp only [hf, ↓reduceIte]
    rw [wtr_true]
    simp only [wp_bind]
    refine wp_mono (write_headers_spec { st with
        rept_start_date := dates.ws_start_date
        rept_end_date := dates.ws_end_date } { s with
        first := false
        rs := Model.cps (Model.dStart (WsDateparmRecord.vals dates))
        re := Model.cps (Model.dEnd (WsDateparmRecord.vals dates)) }
      ⟨hc.disp, hc.writes, hc.lc, hc.page, hc.acct, hc.grand, ?_, ?_⟩ hb
      (by show st.writes.val.length + 4 < Usize.max; omega)) ?_
    · simp only [dStart_vals, cps_ebcU]
    · simp only [dEnd_vals, cps_ebcU]
    rintro _ ⟨st2, rfl, hc2, hl2, hd2⟩
    have hl2' : st2.writes.val.length = st.writes.val.length + 4 := hl2
    dsimp only
    exact wp_mono (write_report_false_spec st2 _ dates tran xref ttype tcat hc2 (bnd_headers _ hb)
      hx (by omega) ha hcat hamt) fun _ ⟨st', h1, h2, h3, h4⟩ =>
        ⟨st', h1, h2, by omega, h4.trans hd2⟩

/-! ## The abend -/

set_option maxHeartbeats 4000000 in
/-- `abend_status23`: the file status and abend lines (`Model.abend23` after its message). -/
theorem abend_status23_spec (st : cbtrn03c.St) (s : Model.St) (hc : Corr st s)
    (hd : st.displays.val.length + 2 < Usize.max) :
    wp (cbtrn03c.abend_status23 st) (fun o => ∃ st', o = .ok st' ∧
      Corr st' (Model.dsp (Model.dsp s (Model.txt "FILE STATUS IS: NNNN0023"))
        (Model.txt "ABENDING PROGRAM")) ∧ st'.writes = st.writes) := by
  unfold cbtrn03c.abend_status23
  t03_wp [List.nil_append]
  try simp (disch := first | omega | scalar_tac) only [dite_eq_left]
  refine ⟨_, rfl, ⟨?_, hc.writes, hc.lc, hc.page, hc.acct, hc.grand, hc.rs, hc.re⟩, rfl⟩
  simp only [Model.dsp, alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil,
    hc.disp, uscalar_ofNat_val, List.nil_append,
    show Model.txt "FILE STATUS IS: NNNN0023" = [70, 73, 76, 69, 32, 83, 84, 65, 84, 85, 83, 32,
      73, 83, 58, 32, 78, 78, 78, 78, 48, 48, 50, 51] from by decide,
    show Model.txt "ABENDING PROGRAM" = [65, 66, 69, 78, 68, 73, 78, 71, 32, 80, 82, 79, 71, 82,
      65, 77] from by decide, List.append_assoc]

/-! ## The record line -/

/-- The DISPLAY line of a transaction record (`tran_record_bytes`). -/
def tranLine (t : cbtrn03c.TranRecord) : List U8 :=
  t.tran_id.val ++ t.tran_type_cd.val ++ zeroPad 4 t.tran_cat_cd.val.natAbs ++ t.tran_source.val ++
    t.tran_desc.val ++ (zeroPad 10 (t.tran_amt.val.natAbs / 10) ++ [overByte t.tran_amt.val]) ++
    zeroPad 9 t.tran_merchant_id.val.natAbs ++ t.tran_merchant_name.val ++
    t.tran_merchant_city.val ++ t.tran_merchant_zip.val ++ t.tran_card_num.val ++
    t.tran_orig_ts.val ++ t.tran_proc_ts.val ++ t.filler1.val

theorem tranLine_length (t : cbtrn03c.TranRecord) : (tranLine t).length = 350 := by
  simp [tranLine, zeroPad_length]

set_option maxHeartbeats 4000000 in
theorem tran_record_bytes_eq (t : cbtrn03c.TranRecord)
    (h1 : -9223372036854775808 < t.tran_cat_cd.val) (h2 : -9223372036854775808 < t.tran_amt.val)
    (h3 : -9223372036854775808 < t.tran_merchant_id.val) :
    cbtrn03c.tran_record_bytes t = .ok (alloc.vec.Vec.from (tranLine t)
      (by rw [tranLine_length]; have := usize_max_ge; omega)) := by
  refine eq_ok_of_wp ?_
  unfold cbtrn03c.tran_record_bytes
  t03_wp [h1, h2, h3]
  simp only [Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, tranLine,
    List.nil_append, List.append_assoc]

/-- A record's line is its text (`Schema.textS` of its field values). -/
theorem tranLine_text (t : cbtrn03c.TranRecord) :
    (tranLine t).map UScalar.val = Model.TranRecord.textS (TranRecord.vals t) := by
  simp only [tranLine, List.map_append, zeroPad_val, Schema.textS, TranRecord.vals,
    List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, fieldTextS, latin1_text, List.append_nil, List.append_assoc, overByte_val,
    Bool.false_eq_true, _root_.ite_false, _root_.ite_true, Nat.reduceSub]

end EquivLean.Modernize.Cbtrn03c.Rust

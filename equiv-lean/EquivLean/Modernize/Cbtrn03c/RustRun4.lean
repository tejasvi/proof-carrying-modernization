import EquivLean.Modernize.Cbtrn03c.RustRun3

/-!
# CBTRN03C → Rust, part 4: the other writers

`write_account_totals`, `write_grand_totals`, `write_headers` and `write_detail` are the model's
steps (`Corr`), the report records growing by the lines they write; `write_transaction_report` is
`Model.report`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

/-! ## Field values of the Rust records -/

theorem tId_vals (t : cbtrn03c.TranRecord) :
    Model.tId (TranRecord.vals t) = t.tran_id.val.map ebcU := rfl
theorem tType_vals (t : cbtrn03c.TranRecord) :
    Model.tType (TranRecord.vals t) = t.tran_type_cd.val.map ebcU := rfl
theorem tCat_vals (t : cbtrn03c.TranRecord) : Model.tCat (TranRecord.vals t) = t.tran_cat_cd.val :=
  rfl
theorem tSource_vals (t : cbtrn03c.TranRecord) :
    Model.tSource (TranRecord.vals t) = t.tran_source.val.map ebcU := rfl
theorem tAmt_vals (t : cbtrn03c.TranRecord) : Model.tAmt (TranRecord.vals t) = t.tran_amt.val :=
  rfl
theorem tCard_vals (t : cbtrn03c.TranRecord) :
    Model.tCard (TranRecord.vals t) = t.tran_card_num.val.map ebcU := rfl
theorem tDate_vals (t : cbtrn03c.TranRecord) :
    Model.tDate (TranRecord.vals t) = (t.tran_proc_ts.val.map ebcU).take 10 := rfl
theorem xCard_vals (x : cbtrn03c.CardXrefRecord) :
    Model.xCard (CardXrefRecord.vals x) = x.xref_card_num.val.map ebcU := rfl
theorem xAcct_vals (x : cbtrn03c.CardXrefRecord) :
    Model.xAcct (CardXrefRecord.vals x) = x.xref_acct_id.val := rfl
theorem yType_vals (y : cbtrn03c.TranTypeRecord) :
    Model.yType (TranTypeRecord.vals y) = y.tran_type.val.map ebcU := rfl
theorem yDesc_vals (y : cbtrn03c.TranTypeRecord) :
    Model.yDesc (TranTypeRecord.vals y) = y.tran_type_desc.val.map ebcU := rfl
theorem cType_vals (c : cbtrn03c.TranCatRecord) :
    Model.cType (TranCatRecord.vals c) = c.tran_type_cd.val.map ebcU := rfl
theorem cCat_vals (c : cbtrn03c.TranCatRecord) : Model.cCat (TranCatRecord.vals c) = c.tran_cat_cd.val :=
  rfl
theorem cDesc_vals (c : cbtrn03c.TranCatRecord) :
    Model.cDesc (TranCatRecord.vals c) = c.tran_cat_type_desc.val.map ebcU := rfl
theorem dStart_vals (d : cbtrn03c.WsDateparmRecord) :
    Model.dStart (WsDateparmRecord.vals d) = d.ws_start_date.val.map ebcU := rfl
theorem dEnd_vals (d : cbtrn03c.WsDateparmRecord) :
    Model.dEnd (WsDateparmRecord.vals d) = d.ws_end_date.val.map ebcU := rfl

/-- The code points of an alphanumeric field are its Latin-1 bytes. -/
theorem cps_ebcU (l : List U8) : Model.cps (l.map ebcU) = l.map UScalar.val :=
  latin1_text l

theorem cps_take_ebcU (l : List U8) (n : Nat) :
    Model.cps ((l.map ebcU).take n) = (l.take n).map UScalar.val := by
  have h : (l.map ebcU).take n = (l.take n).map ebcU := by
    induction l generalizing n with
    | nil => cases n <;> rfl
    | cons a l ih =>
      cases n with
      | zero => rfl
      | succ n => exact congrArg (List.cons (ebcU a)) (ih n)
  rw [h]
  exact latin1_text _

theorem ite_false_of {c : Prop} [Decidable c] {α : Type _} {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- The line counter's `% 10^9` on a nonnegative value. -/
theorem tmod9 (x : Int) (h : 0 ≤ x) : x.tmod 1000000000 = x % 1000000000 :=
  Int.tmod_eq_emod_of_nonneg h

/-! ## The bounds through the steps -/

theorem bnd_inc (s : Model.St) (h : Bnd s) : Bnd (Model.inc s) := by
  unfold Bnd at *
  exact ⟨Nat.mod_lt _ (by decide), h.2⟩

theorem bnd_wr (s : Model.St) (l : List Nat) (h : Bnd s) : Bnd (Model.wr s l) := h

theorem bnd_headers (s : Model.St) (h : Bnd s) : Bnd (Model.headers s) := by
  unfold Model.headers
  exact bnd_inc _ (bnd_wr _ _ (bnd_inc _ (bnd_wr _ _ (bnd_inc _ (bnd_wr _ _ (bnd_inc _
    (bnd_wr _ _ h)))))))

theorem bnd_pageTotals (s : Model.St) (h : Bnd s) : Bnd (Model.pageTotals s) := by
  unfold Bnd at *
  exact ⟨Nat.mod_lt _ (by decide), by simp [Model.pageTotals, Model.inc, Model.wr], h.2.2.1,
    trunc11_bound _⟩

theorem bnd_acctTotals (s : Model.St) (h : Bnd s) : Bnd (Model.acctTotals s) := by
  unfold Bnd at *
  exact ⟨Nat.mod_lt _ (by decide), h.2.1, by simp [Model.acctTotals, Model.inc, Model.wr],
    h.2.2.2⟩

/-! ## The writers -/

set_option maxHeartbeats 4000000 in
/-- `write_account_totals` is `Model.acctTotals`. -/
theorem write_account_totals_spec (st : cbtrn03c.St) (s : Model.St) (hc : Corr st s) (hb : Bnd s)
    (hw : st.writes.val.length + 2 < Usize.max) :
    wp (cbtrn03c.write_account_totals st) (fun o => ∃ st', o = .ok st' ∧
      Corr st' (Model.acctTotals s) ∧ st'.writes.val.length = st.writes.val.length + 2 ∧
      st'.displays = st.displays) := by
  obtain ⟨hlc, hpg, hac, hgr⟩ := hb
  have hav : -9223372036854775808 < st.account_total.val := by rw [hc.acct]; omega
  have hl : 0 ≤ st.line_counter.val ∧ st.line_counter.val < 1000000000 := by
    rw [hc.lc]; omega
  unfold cbtrn03c.write_account_totals cbtrn03c.write_rec cbtrn03c.inc_counter cbtrn03c.header2
  t03_wp [hav]
  simp (disch := omega) only [tmod9]
  simp (disch := first | omega | scalar_tac) only [dite_eq_left]
  refine ⟨_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp, rfl⟩
  · simp only [Model.acctTotals, Model.inc, Model.wr, hc.disp]
  · simp only [Model.acctTotals, Model.inc, Model.wr, alloc.vec.Vec.from_val, linesOf_append,
      linesOf_singleton, hc.writes, line133_val, Array.repeat_val, List.map_replicate,
      uscalar_ofNat_val, List.map_append, List.map_cons, List.map_nil, editArr_val, hc.acct,
      List.nil_append]
    simp only [Model.acctTotalLine, Model.header2, show Model.pad (Model.txt "Account Total") 13 =
      [65, 99, 99, 111, 117, 110, 116, 32, 84, 111, 116, 97, 108] from by decide,
      List.replicate_zero, List.append_nil, List.nil_append, List.append_assoc]
  · simp only [Model.acctTotals, Model.inc, Model.wr, iscalar_srem_val, IScalar.ofInt_val_eq,
      iscalar_ofInt_val, hc.lc]
    simp (disch := omega) only [tmod9]
    omega
  · simp only [Model.acctTotals, Model.inc, Model.wr, hc.page]
  · simp only [Model.acctTotals, Model.inc, Model.wr, iscalar_ofInt_val]
  · simp only [Model.acctTotals, Model.inc, Model.wr, hc.grand]
  · simp only [Model.acctTotals, Model.inc, Model.wr, hc.rs]
  · simp only [Model.acctTotals, Model.inc, Model.wr, hc.re]

set_option maxHeartbeats 4000000 in
/-- `write_grand_totals` is `Model.grandTotals`. -/
theorem write_grand_totals_spec (st : cbtrn03c.St) (s : Model.St) (hc : Corr st s) (hb : Bnd s)
    (hw : st.writes.val.length + 1 < Usize.max) :
    wp (cbtrn03c.write_grand_totals st) (fun o => ∃ st', o = .ok st' ∧
      Corr st' (Model.grandTotals s) ∧ st'.writes.val.length = st.writes.val.length + 1 ∧
      st'.displays = st.displays) := by
  obtain ⟨hlc, hpg, hac, hgr⟩ := hb
  have hgv : -9223372036854775808 < st.grand_total.val := by rw [hc.grand]; omega
  unfold cbtrn03c.write_grand_totals cbtrn03c.write_rec
  t03_wp [hgv]
  try simp (disch := first | omega | scalar_tac) only [dite_eq_left]
  refine ⟨_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp, rfl⟩
  · simp only [Model.grandTotals, Model.wr, hc.disp]
  · simp only [Model.grandTotals, Model.wr, alloc.vec.Vec.from_val, linesOf_append,
      linesOf_singleton, hc.writes, line133_val, List.map_replicate, uscalar_ofNat_val,
      List.map_append, List.map_cons, List.map_nil, editArr_val, hc.grand, List.nil_append]
    simp only [Model.grandTotalLine, show Model.pad (Model.txt "Grand Total") 11 =
      [71, 114, 97, 110, 100, 32, 84, 111, 116, 97, 108] from by decide,
      List.replicate_zero, List.append_nil, List.nil_append, List.append_assoc]
  · simp only [Model.grandTotals, Model.wr, hc.lc]
  · simp only [Model.grandTotals, Model.wr, hc.page]
  · simp only [Model.grandTotals, Model.wr, hc.acct]
  · simp only [Model.grandTotals, Model.wr, hc.grand]
  · simp only [Model.grandTotals, Model.wr, hc.rs]
  · simp only [Model.grandTotals, Model.wr, hc.re]

set_option maxHeartbeats 4000000 in
/-- `write_headers` is `Model.headers`. -/
theorem write_headers_spec (st : cbtrn03c.St) (s : Model.St) (hc : Corr st s) (hb : Bnd s)
    (hw : st.writes.val.length + 4 < Usize.max) :
    wp (cbtrn03c.write_headers st) (fun o => ∃ st', o = .ok st' ∧
      Corr st' (Model.headers s) ∧ st'.writes.val.length = st.writes.val.length + 4 ∧
      st'.displays = st.displays) := by
  obtain ⟨hlc, hpg, hac, hgr⟩ := hb
  have hl : 0 ≤ st.line_counter.val ∧ st.line_counter.val < 1000000000 := by
    rw [hc.lc]; omega
  unfold cbtrn03c.write_headers cbtrn03c.write_rec cbtrn03c.inc_counter cbtrn03c.header2
  t03_wp [List.nil_append]
  simp (config := { maxSteps := 5000000 }) (disch := omega) only [tmod9]
  simp (config := { maxSteps := 5000000 }) (disch := first | omega | scalar_tac) only
    [dite_eq_left]
  refine ⟨_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp, rfl⟩
  · simp only [Model.headers, Model.inc, Model.wr, hc.disp]
  · simp only [Model.headers, Model.inc, Model.wr, alloc.vec.Vec.from_val, linesOf_append,
      linesOf_singleton, hc.writes, line133_val, Array.repeat_val, List.map_replicate,
      uscalar_ofNat_val, List.map_append, List.map_cons, List.map_nil, hc.rs, hc.re,
      List.nil_append]
    simp only [Model.nameHeader, Model.header1, Model.header2, Model.blankLine,
      show Model.pad (Model.txt "DALYREPT") 38 =
        [68, 65, 76, 89, 82, 69, 80, 84] ++ List.replicate 30 32 from by decide,
      show Model.pad (Model.txt "Daily Transaction Report") 41 =
        [68, 97, 105, 108, 121, 32, 84, 114, 97, 110, 115, 97, 99, 116, 105, 111, 110, 32, 82,
          101, 112, 111, 114, 116] ++ List.replicate 17 32 from by decide,
      show Model.pad (Model.txt "Date Range: ") 12 =
        [68, 97, 116, 101, 32, 82, 97, 110, 103, 101, 58, 32] from by decide,
      show Model.txt " to " = [32, 116, 111, 32] from by decide,
      show Model.pad (Model.txt "Transaction ID") 17 =
        [84, 114, 97, 110, 115, 97, 99, 116, 105, 111, 110, 32, 73, 68] ++
          List.replicate 3 32 from by decide,
      show Model.pad (Model.txt "Account ID") 12 =
        [65, 99, 99, 111, 117, 110, 116, 32, 73, 68] ++ List.replicate 2 32 from by decide,
      show Model.pad (Model.txt "Transaction Type") 19 =
        [84, 114, 97, 110, 115, 97, 99, 116, 105, 111, 110, 32, 84, 121, 112, 101] ++
          List.replicate 3 32 from by decide,
      show Model.pad (Model.txt "Tran Category") 35 =
        [84, 114, 97, 110, 32, 67, 97, 116, 101, 103, 111, 114, 121] ++
          List.replicate 22 32 from by decide,
      show Model.pad (Model.txt "Tran Source") 14 =
        [84, 114, 97, 110, 32, 83, 111, 117, 114, 99, 101] ++ List.replicate 3 32 from by decide,
      show Model.pad (Model.txt " ") 1 = [32] from by decide,
      show Model.pad (Model.txt "        Amount") 16 =
        [32, 32, 32, 32, 32, 32, 32, 32, 65, 109, 111, 117, 110, 116] ++
          List.replicate 2 32 from by decide,
      List.replicate_zero, List.append_nil, List.nil_append, List.append_assoc]
  · simp only [Model.headers, Model.inc, Model.wr, iscalar_srem_val, IScalar.ofInt_val_eq,
      iscalar_ofInt_val, hc.lc]
    simp (disch := omega) only [tmod9]
    omega
  · simp only [Model.headers, Model.inc, Model.wr, hc.page]
  · simp only [Model.headers, Model.inc, Model.wr, hc.acct]
  · simp only [Model.headers, Model.inc, Model.wr, hc.grand]
  · simp only [Model.headers, Model.inc, Model.wr, hc.rs]
  · simp only [Model.headers, Model.inc, Model.wr, hc.re]

set_option maxHeartbeats 4000000 in
/-- `write_detail` writes the detail line of the transaction `tran` (`Model.detailLine`). -/
theorem write_detail_spec (st : cbtrn03c.St) (s : Model.St) (tran : cbtrn03c.TranRecord)
    (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (hc : Corr st s) (hlc : s.lc < 1000000000)
    (hx : s.xref = CardXrefRecord.vals xref) (hw : st.writes.val.length + 1 < Usize.max)
    (ha : -9223372036854775808 < xref.xref_acct_id.val)
    (hcat : -9223372036854775808 < tran.tran_cat_cd.val)
    (hamt : -9223372036854775808 < tran.tran_amt.val) :
    wp (cbtrn03c.write_detail st tran xref ttype tcat) (fun o => ∃ st', o = .ok st' ∧
      Corr st' (Model.inc (Model.wr s (Model.detailLine (TranRecord.vals tran) s.xref
        (TranTypeRecord.vals ttype) (TranCatRecord.vals tcat)))) ∧
      st'.writes.val.length = st.writes.val.length + 1 ∧ st'.displays = st.displays) := by
  have hl : 0 ≤ st.line_counter.val ∧ st.line_counter.val < 1000000000 := by
    rw [hc.lc]; omega
  rw [hx]
  unfold cbtrn03c.write_detail cbtrn03c.write_rec cbtrn03c.inc_counter
  t03_wp [ha, hcat, hamt, array_index_range0, Slice.from_val, Nat.reduceLeDiff,
    show min 15 50 = 15 from rfl, show min 29 50 = 29 from rfl, show min 15 15 = 15 from rfl,
    show min 29 29 = 29 from rfl]
  simp (disch := first | omega | scalar_tac) only [dite_eq_left]
  refine ⟨_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp, rfl⟩
  · simp only [Model.inc, Model.wr, hc.disp]
  · simp only [Model.inc, Model.wr, alloc.vec.Vec.from_val, linesOf_append, linesOf_singleton,
      hc.writes, line133_val, Model.detailLine, List.append_cancel_left_eq, List.cons.injEq,
      and_true]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, uscalar_ofNat_val, zeroPad_val,
      editArr_val, List.map_replicate, tId_vals, tType_vals, tCat_vals, tSource_vals, tAmt_vals,
      xAcct_vals, yDesc_vals, cDesc_vals, cps_ebcU, cps_take_ebcU, Model.digs, Model.pad,
      List.append_assoc, List.nil_append]
    simp [List.take_take, Nat.min_self]
  · simp only [Model.inc, Model.wr, iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val,
      hc.lc]
    simp (disch := omega) only [tmod9]
    omega
  · simp only [Model.inc, Model.wr, hc.page]
  · simp only [Model.inc, Model.wr, hc.acct]
  · simp only [Model.inc, Model.wr, hc.grand]
  · simp only [Model.inc, Model.wr, hc.rs]
  · simp only [Model.inc, Model.wr, hc.re]

end EquivLean.Modernize.Cbtrn03c.Rust

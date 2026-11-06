import EquivLean.Modernize.Cbtrn03c.RustRun2

/-!
# CBTRN03C → Rust, part 3: the report writers

`Corr st s`: the Rust state `st` (displays, report records, line counter, totals, report dates)
holds the fields of the model's state `s`; `Bnd s`: the counters and totals are in their pictures'
ranges.  Each writer of the Rust code is the corresponding step of the model, with the report
records growing by the lines it writes: `write_page_totals` is `Model.pageTotals`, …,
`write_transaction_report` is `Model.report`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

/-! ## Values -/

theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega

/-- Small lengths fit in a `usize` (the side conditions of the helpers, by `simp`). -/
theorem small_lt_usize_max {n : Nat} (h : n < 4294967295) : n < Usize.max :=
  Nat.lt_of_lt_of_le h usize_max_ge

/-- The value of a signed `%`. -/
theorem iscalar_srem_val {ty : IScalarTy} (x y : IScalar ty) :
    (⟨BitVec.srem x.bv y.bv⟩ : IScalar ty).val = Int.tmod x.val y.val := by
  show (BitVec.srem x.bv y.bv).toInt = _
  rw [BitVec.toInt_srem]
  rfl

/-- A report line, as code points. -/
theorem line133_val (l : List U8) :
    (line133 l).val.map UScalar.val = Model.to133 (l.map UScalar.val) := by
  simp [line133, Model.to133, Model.pad, List.map_take, List.map_replicate]

/-- A padded field, as code points. -/
theorem padB_val (s : List U8) (w : Nat) :
    (s.take w ++ List.replicate (w - s.length) 32#u8).map UScalar.val =
      Model.pad (s.map UScalar.val) w := by
  simp [Model.pad, List.map_take, List.map_replicate]

theorem zzz_lt : ∀ (p : List Char) (ds : List Nat) (sup : Bool), (∀ d ∈ ds, d < 10) →
    ∀ c ∈ Model.zzz p ds sup, c < 256
  | [], _, _, _ => by simp [Model.zzz]
  | c :: p, ds, sup, h => by
    by_cases hc : c = ','
    · simp only [Model.zzz, hc, _root_.ite_true, List.mem_cons]
      rintro x (rfl | hx)
      · split_ifs <;> omega
      · exact zzz_lt p ds sup h x hx
    · simp only [Model.zzz, hc, _root_.ite_false]
      match ds, h with
      | [], _ => simp
      | d :: ds, h =>
        have hd := h d (List.mem_cons_self ..)
        have h' : ∀ d ∈ ds, d < 10 := fun x hx => h x (List.mem_cons_of_mem _ hx)
        dsimp only
        split_ifs
        · simp only [List.mem_cons]
          rintro x (rfl | hx)
          · omega
          · exact zzz_lt p ds true h' x hx
        · simp only [List.mem_cons]
          rintro x (rfl | hx)
          · omega
          · exact zzz_lt p ds false h' x hx

theorem editAmt_lt (v : Int) (plus : Bool) : ∀ c ∈ Model.editAmt v plus, c < 256 := by
  unfold Model.editAmt
  dsimp only
  have hd : ∀ d ∈ toDigits 10 9 (v.natAbs % 100000000000 / 100), d < 10 :=
    fun d hd => Cobol.Digits.toDigits_lt (by decide) _ _ d hd
  split_ifs
  all_goals simp only [List.mem_cons, List.mem_append, List.mem_replicate, List.mem_singleton]
  all_goals intro c hc
  all_goals first
    | omega
    | (rcases hc with rfl | hc | hc
       · omega
       · exact zzz_lt _ _ _ hd c hc
       · rcases hc with rfl | rfl | rfl | hc <;> simp_all <;> omega)

/-- The edited amount, as code points. -/
theorem editArr_val (v : Int) (plus : Bool) :
    (editArr v plus).val.map UScalar.val = Model.editAmt v plus := by
  simp only [editArr, Array.from_val, List.map_map]
  conv_rhs => rw [← List.map_id (Model.editAmt v plus)]
  apply List.map_congr_left
  intro c hc
  exact byteOf_val _ (editAmt_lt v plus c hc)

/-- Symbolic execution with the value forms of the kit and the helpers of parts 1 and 2. -/
syntax "t03_wp" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

macro_rules
  | `(tactic| t03_wp [$args,*]) => do
    let args : SimpArgs := args.getElems
    `(tactic| aeneas_wp [slice_to_vec_U8, Array.to_slice, Array.make_val, Array.repeat_val,
      Array.from_val, array_index_usize_eq, array_update_eq, uscalar_ofNat_val, iscalar_ofInt_val,
      not_true_eq_false, not_false_eq_true, Nat.reduceEqDiff, Nat.reduceAdd, Bool.false_eq_true,
      Bool.true_eq_false, Int.reduceEq, Int.reduceNeg, List.length_append, List.length_cons,
      List.length_nil, List.length_replicate, List.length_take, Array.length_eq, zeroPad_length,
      small_lt_usize_max, push_bytes_eq, push_fill_eq, push_padded_eq, push_digits_eq,
      push_zoned_signed_eq, to133_eq, edit_amount_eq, alloc.vec.Vec.deref, iscalar_srem_val,
      Nat.reduceSub, List.take_of_length_le, $args,*])

/-- `a[0..k]` for an array. -/
theorem array_index_range0 {n : Usize} (a : Array U8 n) (k : Usize) (hk : k.val ≤ n.val) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      a { start := 0#usize, «end» := k } =
      .ok (Slice.from (a.val.take k.val) (by simp; scalar_tac)) := by
  simp only [core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice, core.slice.index.SliceIndexRangeUsizeSlice.index]
  have hl : a.to_slice.length = n.val := by simp [Array.to_slice]
  rw [ite_true_of ⟨by simp [UScalar.le_equiv], by rw [hl]; exact hk⟩]
  congr 1
  rw [Slice.eq_iff]
  simp [List.slice, Array.to_slice]

/-! ## The correspondence -/

/-- The report records written, as code points. -/
def linesOf (ws : List cbtrn03c.FdReptfileRec) : List (List Nat) :=
  ws.map fun r => r.fd_reptfile_rec.val.map UScalar.val

/-- The Rust state holds the model's outputs, counters, totals and report dates. -/
structure Corr (st : cbtrn03c.St) (s : Model.St) : Prop where
  disp : st.displays.val.map (fun l => l.val.map UScalar.val) = s.disp
  writes : linesOf st.writes.val = s.writes
  lc : st.line_counter.val = s.lc
  page : st.page_total.val = s.page
  acct : st.account_total.val = s.acct
  grand : st.grand_total.val = s.grand
  rs : st.rept_start_date.val.map UScalar.val = s.rs
  re : st.rept_end_date.val.map UScalar.val = s.re

/-- The counters and totals in range (`PIC 9(09)`, `S9(09)V99`). -/
def Bnd (s : Model.St) : Prop :=
  s.lc < 1000000000 ∧ s.page.natAbs < 100000000000 ∧ s.acct.natAbs < 100000000000 ∧
    s.grand.natAbs < 100000000000

/-- A total truncated by `ADD` stays in the picture's range. -/
theorem trunc11_bound (a : Int) : (Model.trunc11 a).natAbs < 100000000000 := by
  unfold Model.trunc11
  rw [Int.tmod_eq_emod]
  split_ifs with h
  · omega
  · have h2 : ¬ (100000000000 : Int) ∣ a := fun hd => h (Or.inr hd)
    have h3 : a % 100000000000 ≠ 0 := fun h0 => h2 (Int.dvd_of_emod_eq_zero h0)
    omega

theorem linesOf_append (ws vs : List cbtrn03c.FdReptfileRec) :
    linesOf (ws ++ vs) = linesOf ws ++ linesOf vs := by
  simp [linesOf]

theorem linesOf_singleton (a : Array U8 133#usize) :
    linesOf [{ fd_reptfile_rec := a }] = [a.val.map UScalar.val] := rfl

/-! ## The writers -/

set_option maxHeartbeats 4000000 in
/-- `write_page_totals` is `Model.pageTotals`. -/
theorem write_page_totals_spec (st : cbtrn03c.St) (s : Model.St) (hc : Corr st s) (hb : Bnd s)
    (hw : st.writes.val.length + 2 < Usize.max) :
    wp (cbtrn03c.write_page_totals st) (fun o => ∃ st', o = .ok st' ∧
      Corr st' (Model.pageTotals s) ∧ st'.writes.val.length = st.writes.val.length + 2 ∧
      st'.displays = st.displays) := by
  obtain ⟨hlc, hpg, hac, hgr⟩ := hb
  have hpv : -9223372036854775808 < st.page_total.val := by rw [hc.page]; omega
  have hg : -100000000000 < st.grand_total.val ∧ st.grand_total.val < 100000000000 := by
    rw [hc.grand]; omega
  have hp : -100000000000 < st.page_total.val ∧ st.page_total.val < 100000000000 := by
    rw [hc.page]; omega
  have hl : 0 ≤ st.line_counter.val ∧ st.line_counter.val < 1000000000 := by
    rw [hc.lc]; omega
  have hl1 : (st.line_counter.val + 1).tmod 1000000000 = (st.line_counter.val + 1) % 1000000000 :=
    Int.tmod_eq_emod_of_nonneg (by omega)
  unfold cbtrn03c.write_page_totals cbtrn03c.write_rec cbtrn03c.inc_counter cbtrn03c.trunc11
    cbtrn03c.header2
  t03_wp [hpv]
  simp only [hl1]
  simp (disch := first | omega | scalar_tac) only [dite_eq_left]
  refine ⟨_, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp, rfl⟩
  · simp only [Model.pageTotals, Model.inc, Model.wr, hc.disp]
  · simp only [Model.pageTotals, Model.inc, Model.wr, alloc.vec.Vec.from_val, linesOf_append,
      linesOf_singleton, hc.writes, line133_val, Array.repeat_val, List.map_replicate,
      uscalar_ofNat_val, List.map_append, List.map_cons, List.map_nil, editArr_val, hc.page,
      List.nil_append]
    simp only [Model.pageTotalLine, Model.header2, show Model.pad (Model.txt "Page Total") 11 =
      [80, 97, 103, 101, 32, 84, 111, 116, 97, 108] ++ List.replicate 1 32 from by decide]
  · simp only [Model.pageTotals, Model.inc, Model.wr, iscalar_srem_val, IScalar.ofInt_val_eq,
      iscalar_ofInt_val, hc.lc]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  · simp only [Model.pageTotals, Model.inc, Model.wr, iscalar_ofInt_val]
  · simp only [Model.pageTotals, Model.inc, Model.wr, hc.acct]
  · simp only [Model.pageTotals, Model.inc, Model.wr, iscalar_srem_val, IScalar.ofInt_val_eq,
      iscalar_ofInt_val, hc.grand, hc.page, Model.trunc11]
  · simp only [Model.pageTotals, Model.inc, Model.wr, hc.rs]
  · simp only [Model.pageTotals, Model.inc, Model.wr, hc.re]

end EquivLean.Modernize.Cbtrn03c.Rust

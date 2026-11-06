import EquivLean.Modernize.Cbtrn03c.RustRun6

/-!
# CBTRN03C → Rust, part 7: the loop invariant; end of file and records out of range

`loopInv`: the program state holds a model state `s`, and the outputs of the model from the
position in the transaction file with the record area (`rest`; after the end of file, those of
`s`) are the outputs `R`.  One iteration reads the next record (or, at the end of file, takes the
record area) and applies the date test (`inRange_cmpL`).  The paths here: after the end of file
(`step_eof`), a record out of the range (`step_out`), the record area at the end of file out of /
in the range (`step_end_out`, `step_end_in` = `Model.eofTail`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

/-! ## Valid records -/

theorem tran_ranges (t : cbtrn03c.TranRecord) (hv : Model.TranRecord.Valid (TranRecord.vals t)) :
    0 ≤ t.tran_cat_cd.val ∧ t.tran_cat_cd.val < 10000 ∧ t.tran_amt.val.natAbs < 100000000000 ∧
      0 ≤ t.tran_merchant_id.val ∧ t.tran_merchant_id.val < 1000000000 := by
  simp only [Schema.Valid, TranRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨-, _ | ⟨h2, _ | ⟨-, _ | ⟨-, _ | ⟨h5, _ | ⟨h6, -⟩⟩⟩⟩⟩⟩⟩
  obtain ⟨fmt2, hk2, -, -, hh2, -⟩ := h2
  obtain ⟨fmt5, hk5, -, -, hh5, -⟩ := h5
  obtain ⟨fmt6, hk6, -, -, hh6, -⟩ := h6
  cases hk2
  cases hk5
  cases hk6
  simp only [NumFmt.Holds, NumFmt.fullBinary, Bool.false_eq_true, _root_.ite_false,
    _root_.ite_true, true_implies, Nat.reducePow] at hh2 hh5 hh6
  omega

theorem xref_acct_range (x : cbtrn03c.CardXrefRecord)
    (hv : Model.CardXrefRecord.Valid (CardXrefRecord.vals x)) :
    0 ≤ x.xref_acct_id.val ∧ x.xref_acct_id.val < 100000000000 := by
  simp only [Schema.Valid, CardXrefRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨-, _ | ⟨h2, -⟩⟩⟩
  obtain ⟨fmt, hk, -, -, hh, -⟩ := h2
  cases hk
  simp only [NumFmt.Holds, NumFmt.fullBinary, Bool.false_eq_true, _root_.ite_false,
    true_implies, Nat.reducePow] at hh
  omega

/-! ## The model from a position of the transaction file -/

/-- The outputs of the model from the transactions `ts` still to read, with the record area `tran`
and the state `s`. -/
def rest (xs ys cs : List (List FVal)) (d : List FVal) (ts : List (List FVal)) (tran : List FVal)
    (s : Model.St) : Model.Out :=
  match Model.loop xs ys cs d ts tran s with
  | .ok s => Model.out s false
  | .error s => Model.out s true

theorem rest_nil (xs ys cs : List (List FVal)) (d tran : List FVal) (s : Model.St) :
    rest xs ys cs d [] tran s = if Model.inRange d tran then Model.out (Model.eofTail s tran) false
      else Model.out s false := by
  by_cases h : Model.inRange d tran = true <;> simp [rest, Model.loop, h]

theorem rest_cons_out (xs ys cs : List (List FVal)) (d t : List FVal) (ts : List (List FVal))
    (tran : List FVal) (s : Model.St) (h : Model.inRange d t = false) :
    rest xs ys cs d (t :: ts) tran s = Model.out s false := by
  simp [rest, Model.loop, h]

theorem rest_cons_in (xs ys cs : List (List FVal)) (d t : List FVal) (ts : List (List FVal))
    (tran : List FVal) (s : Model.St) (h : Model.inRange d t = true) :
    rest xs ys cs d (t :: ts) tran s = match Model.tranStep xs ys cs d s t with
      | .ok s' => rest xs ys cs d ts t s'
      | .error s' => Model.out s' true := by
  simp only [rest, Model.loop, h, ↓reduceIte, eq_self_iff_true]
  cases Model.tranStep xs ys cs d s t <;> rfl

/-! ## The outputs -/

theorem endL_txt : Model.txt "END OF EXECUTION OF PROGRAM CBTRN03C" = [69, 78, 68, 32, 79, 70, 32,
    69, 88, 69, 67, 85, 84, 73, 79, 78, 32, 79, 70, 32, 80, 82, 79, 71, 82, 65, 77, 32, 67, 66, 84,
    82, 78, 48, 51, 67] := by
  decide

/-- The report records written are the model's (`FD-REPTFILE-REC` field values). -/
theorem out_writes (st : cbtrn03c.St) (s : Model.St) (hc : Corr st s) (ab : Bool) :
    st.writes.val.map FdReptfileRec.vals = (Model.out s ab).writes := by
  show _ = s.writes.map fun l => [FVal.str (l.map Model.ebc)]
  rw [← hc.writes]
  simp only [linesOf, List.map_map]
  apply List.map_congr_left
  intro r _
  simp only [Function.comp_apply, FdReptfileRec.vals, List.map_map]
  rfl

/-- `t03_wp` with a larger simp step budget, for the body of the read loop. -/
syntax "t03_wpx" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

macro_rules
  | `(tactic| t03_wpx [$args,*]) => do
    let args : SimpArgs := args.getElems
    `(tactic| simp (config := { maxSteps := 4000000 }) only [wp_bind, wp_bind_tc, wp_ok, wp_fail,
      wp_div, wp_pure, wp_lift, wp_ite, wp_dite, wp_massert, wp_ofOption, wp_Slice_index_usize,
      wp_Vec_index_usize, wp_Vec_push, alloc.vec.Vec.index_slice_index, alloc.vec.Vec.len_val,
      alloc.vec.Vec.length, alloc.vec.Vec.from_val, Slice.from_val, wp_UScalar_add_val,
      wp_UScalar_sub_val, wp_UScalar_mul_val, wp_UScalar_div_val, wp_UScalar_rem_val,
      wp_IScalar_add_val, wp_IScalar_sub_val, wp_IScalar_mul_val, wp_IScalar_neg_val,
      wp_IScalar_div_val, wp_IScalar_rem, wp_UScalar_shl, wp_UScalar_shr,
      UScalar.cast_val_mod_pow_greater_numBits_eq, IScalar.val_mod_pow_greater_numBits,
      UScalar.hcast_val_of_numBits_lt, UScalar.lt_equiv, UScalar.le_equiv, IScalar.lt_equiv,
      IScalar.le_equiv, UScalar.eq_equiv, IScalar.eq_equiv, bne_iff_ne, ne_eq, decide_eq_true_eq,
      Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq,
      UScalarTy.U8_numBits_eq, UScalarTy.U16_numBits_eq, UScalarTy.U32_numBits_eq,
      UScalarTy.U64_numBits_eq, UScalarTy.U128_numBits_eq, IScalarTy.I8_numBits_eq,
      IScalarTy.I16_numBits_eq, IScalarTy.I32_numBits_eq, IScalarTy.I64_numBits_eq,
      IScalarTy.I128_numBits_eq, Nat.reduceLeDiff, Nat.reduceLT, UScalar.max_USize_eq,
      UScalar.max_UScalarTy_U8_eq, UScalar.max_UScalarTy_U16_eq, UScalar.max_UScalarTy_U32_eq,
      UScalar.max_UScalarTy_U64_eq, UScalar.max_UScalarTy_U128_eq, U8.max_eq, U16.max_eq,
      U32.max_eq, U64.max_eq, U128.max_eq, IScalar.min_IScalarTy_I8_eq,
      IScalar.max_IScalarTy_I8_eq, IScalar.min_IScalarTy_I16_eq, IScalar.max_IScalarTy_I16_eq,
      IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq, IScalar.min_IScalarTy_I64_eq,
      IScalar.max_IScalarTy_I64_eq, IScalar.min_IScalarTy_I128_eq, IScalar.max_IScalarTy_I128_eq,
      I8.min_eq, I8.max_eq, I16.min_eq, I16.max_eq, I32.min_eq, I32.max_eq, I64.min_eq,
      I64.max_eq, I128.min_eq, I128.max_eq, Prod.mk.injEq, Aeneas.Std.uncurry_apply_pair,
      _root_.dite_true, _root_.dite_false, _root_.ite_true, _root_.ite_false, and_self, and_true,
      true_and, slice_to_vec_U8, Array.to_slice, Array.make_val, Array.repeat_val,
      Array.from_val, array_index_usize_eq, array_update_eq, uscalar_ofNat_val, iscalar_ofInt_val,
      not_true_eq_false, not_false_eq_true, Nat.reduceEqDiff, Nat.reduceAdd, Bool.false_eq_true,
      Bool.true_eq_false, Int.reduceEq, Int.reduceNeg, List.length_append, List.length_cons,
      List.length_nil, List.length_replicate, List.length_take, Array.length_eq, zeroPad_length,
      small_lt_usize_max, push_bytes_eq, push_fill_eq, push_padded_eq, push_digits_eq,
      push_zoned_signed_eq, to133_eq, edit_amount_eq, alloc.vec.Vec.deref, iscalar_srem_val,
      Nat.reduceSub, List.take_of_length_le, eq_self_iff_true, $args,*])

/-! ## The date test, on the bytes -/

/-- `Model.cmpB` on the EBCDIC bytes of two Latin-1 byte lists. -/
def cmpL (x y : List U8) : Ordering := Model.cmpB (x.map ebcU) (y.map ebcU)

/-- The result of `cmp_ebcdic`. -/
def ordR : Ordering → I32
  | .lt => (-1)#i32
  | .eq => 0#i32
  | .gt => 1#i32

theorem ordR_val (c : Ordering) : (ordR c).val = ordI c := by
  cases c <;> simp [ordR, ordI, iscalar_ofInt_val]

theorem cmp_ebcdic_eq (a b : Slice U8) :
    cbtrn03c.cmp_ebcdic a b = .ok (ordR (cmpL a.val b.val)) := by
  obtain ⟨r, h, hr⟩ := exists_ok_of_wp (cmp_ebcdic_spec a b)
  rw [h]
  congr 1
  apply IScalar.eq_of_val_eq
  rw [ordR_val]
  exact hr

theorem ordR_ge (c : Ordering) : (ordR c ≥ 0#i32) ↔ ¬ c = .lt := by
  cases c <;> simp [ordR, IScalar.le_equiv, iscalar_ofInt_val]

theorem ordR_le (c : Ordering) : (ordR c ≤ 0#i32) ↔ ¬ c = .gt := by
  cases c <;> simp [ordR, IScalar.le_equiv, iscalar_ofInt_val]

theorem ordI_nonneg (c : Ordering) : (0 ≤ ordI c) ↔ ¬ c = .lt := by
  cases c <;> simp [ordI]

theorem ordI_nonpos (c : Ordering) : (ordI c ≤ 0) ↔ ¬ c = .gt := by
  cases c <;> simp [ordI]

/-- The date test of the model, on the bytes of the processing date and of the range. -/
theorem inRange_cmpL (t : cbtrn03c.TranRecord) (ds : Array U8 10#usize) (df : Array U8 1#usize)
    (de : Array U8 10#usize) :
    Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩) (TranRecord.vals t) =
      (cmpL (t.tran_proc_ts.val.take 10) ds.val != .lt &&
        cmpL (t.tran_proc_ts.val.take 10) de.val != .gt) := by
  simp only [Model.inRange, tDate_vals, dStart_vals, dEnd_vals, cmpL, map_ebcU_take]

theorem inRange_true (t : cbtrn03c.TranRecord) (ds : Array U8 10#usize) (df : Array U8 1#usize)
    (de : Array U8 10#usize)
    (h : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩) (TranRecord.vals t) = true) :
    ¬ cmpL (t.tran_proc_ts.val.take 10) ds.val = .lt ∧
      ¬ cmpL (t.tran_proc_ts.val.take 10) de.val = .gt := by
  rw [inRange_cmpL] at h
  simpa only [Bool.and_eq_true, bne_iff_ne, ne_eq] using h

theorem inRange_false (t : cbtrn03c.TranRecord) (ds : Array U8 10#usize) (df : Array U8 1#usize)
    (de : Array U8 10#usize)
    (h : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩) (TranRecord.vals t) = false)
    (h1 : ¬ cmpL (t.tran_proc_ts.val.take 10) ds.val = .lt) :
    cmpL (t.tran_proc_ts.val.take 10) de.val = .gt := by
  rw [inRange_cmpL] at h
  simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq] at h
  exact h.resolve_left h1

/-! ## The read loop -/

/-- The state of the read loop of `run`: the program state, the record area (`TRAN-RECORD`), the
records last read from the lookup files, `WS-FIRST-TIME`, the current card, the end-of-file flag
and the position in the transaction file. -/
abbrev LoopSt := cbtrn03c.St × Array U8 16#usize × Array U8 2#usize × I64 × Array U8 10#usize ×
  Array U8 100#usize × I64 × I64 × Array U8 50#usize × Array U8 50#usize × Array U8 10#usize ×
  Array U8 16#usize × Array U8 26#usize × Array U8 26#usize × Array U8 20#usize ×
  cbtrn03c.CardXrefRecord × cbtrn03c.TranTypeRecord × cbtrn03c.TranCatRecord × Bool ×
  Array U8 16#usize × Bool × Usize

/-- The loop invariant: a model state `s` that the program state holds (with `WS-FIRST-TIME`, the
current card and the cross-reference record area), and the outputs `R` of the model from the
position in the transaction file with the record area (after the end of file, of `s`). -/
def loopInv (S1 : List cbtrn03c.TranRecord) (xs ys cs : List (List FVal)) (d : List FVal)
    (R : Model.Out) : LoopSt → Prop
  | (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10, xref, _, _, first, card, eof,
      idx) =>
    ∃ s : Model.St, Corr st s ∧ Bnd s ∧ s.first = first ∧ s.card = card.val.map ebcU ∧
      s.xref = CardXrefRecord.vals xref ∧ -9223372036854775808 < xref.xref_acct_id.val ∧
      idx.val ≤ S1.length ∧
      st.writes.val.length ≤ 13 * idx.val + (if eof then 3 else 0) ∧
      st.displays.val.length ≤ idx.val + (if eof then 4 else 2) ∧
      i1.val.natAbs < 100000000000 ∧ -9223372036854775808 < i.val ∧
      -9223372036854775808 < i2.val ∧
      ((eof = false ∧ rest xs ys cs d ((S1.map TranRecord.vals).drop idx.val)
          (TranRecord.vals ⟨a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10⟩) s = R) ∨
        (eof = true ∧ Model.out s false = R))

/-- The variant: the records still to read, twice, and one more before the end of file. -/
def loopVar (n : Nat) : LoopSt → Nat
  | (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, eof, idx) =>
    2 * (n - idx.val) + (if eof then 0 else 1)

/-- The outputs of `run` are those of the model `R`. -/
def OutQ (R : Model.Out) (o : Except Error cbtrn03c.Output) : Prop :=
  ∃ out, o = .ok out ∧ out.displays.val.map (fun l => l.val.map (·.val)) = R.disp ∧
    out.report_file_writes.val.map FdReptfileRec.vals = R.writes ∧ out.abended = R.abended

/-- The postcondition of one iteration of the read loop (`wp_loop`). -/
def stepPost (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
    (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
    (ds : Array U8 10#usize) (df : Array U8 1#usize) (de : Array U8 10#usize) (R : Model.Out)
    (x : LoopSt) (r : Except Error (ControlFlow LoopSt cbtrn03c.Output)) : Prop :=
  match loopCls r with
  | .inl o => OutQ R o
  | .inr x' => loopInv s1.val (s2.val.map CardXrefRecord.vals) (s3.val.map TranTypeRecord.vals)
      (s4.val.map TranCatRecord.vals) (WsDateparmRecord.vals ⟨ds, df, de⟩) R x' ∧
    loopVar s1.val.length x' < loopVar s1.val.length x

set_option maxHeartbeats 4000000 in
/-- After the end of file: the end message. -/
theorem step_eof (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
    (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
    (ds : Array U8 10#usize) (df : Array U8 1#usize) (de : Array U8 10#usize) (R : Model.Out)
    (hL : s1.val.length < 2 ^ 28)
    (st : cbtrn03c.St) (a : Array U8 16#usize) (a1 : Array U8 2#usize) (i : I64)
    (a2 : Array U8 10#usize) (a3 : Array U8 100#usize) (i1 i2 : I64) (a4 a5 : Array U8 50#usize)
    (a6 : Array U8 10#usize) (a7 : Array U8 16#usize) (a8 a9 : Array U8 26#usize)
    (a10 : Array U8 20#usize) (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (first : Bool) (card : Array U8 16#usize) (idx : Usize)
    (s : Model.St) (hc : Corr st s) (hidx : idx.val ≤ s1.val.length)
    (hdl : st.displays.val.length ≤ idx.val + 4) (hR : Model.out s false = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card true idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, true, idx)) := by
  have hU := usize_max_ge
  simp only [cbtrn03c.run_loop0.body, cbtrn03c.finish]
  t03_wpx [List.nil_append]
  simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
  simp only [stepPost, loopCls_done, OutQ]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · rw [← hR]
    simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
      uscalar_ofNat_val, List.nil_append, Model.out, Bool.false_eq_true, ↓reduceIte, endL_txt]
  · rw [← hR]
    exact out_writes st s hc false
  · rw [← hR]
    rfl

theorem drop_map_cons {α β : Type _} (S : List α) (f : α → β) (k : Nat) (h : k < S.length) :
    (S.map f).drop k = f S[k] :: (S.map f).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

set_option maxHeartbeats 8000000 in
/-- A record outside the date range: the end message. -/
theorem step_out (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
    (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
    (ds : Array U8 10#usize) (df : Array U8 1#usize) (de : Array U8 10#usize) (R : Model.Out)
    (hL : s1.val.length < 2 ^ 28)
    (st : cbtrn03c.St) (a : Array U8 16#usize) (a1 : Array U8 2#usize) (i : I64)
    (a2 : Array U8 10#usize) (a3 : Array U8 100#usize) (i1 i2 : I64) (a4 a5 : Array U8 50#usize)
    (a6 : Array U8 10#usize) (a7 : Array U8 16#usize) (a8 a9 : Array U8 26#usize)
    (a10 : Array U8 20#usize) (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (first : Bool) (card : Array U8 16#usize) (idx : Usize)
    (s : Model.St) (hc : Corr st s) (hp : idx.val < s1.val.length) (t : cbtrn03c.TranRecord)
    (ht : s1.val[idx.val]'hp = t) (hdl : st.displays.val.length ≤ idx.val + 2)
    (hin : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩) (TranRecord.vals t) = false)
    (hR : Model.out s false = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card false idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, false, idx)) := by
  have hU := usize_max_ge
  simp only [cbtrn03c.run_loop0.body, cbtrn03c.finish]
  by_cases hc1 : cmpL (t.tran_proc_ts.val.take 10) ds.val = .lt
  · t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val, ordI_nonneg, ordI_nonpos, hc1]
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    simp only [stepPost, loopCls_done, OutQ]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [← hR]
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
        uscalar_ofNat_val, List.nil_append, Model.out, Bool.false_eq_true, ↓reduceIte, endL_txt]
    · rw [← hR]
      exact out_writes st s hc false
    · rw [← hR]
      rfl
  · have hc2 := inRange_false t ds df de hin hc1
    t03_wpx [hp, ht, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val, ordI_nonneg, ordI_nonpos, hc1, hc2]
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    simp only [stepPost, loopCls_done, OutQ]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [← hR]
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
        uscalar_ofNat_val, List.nil_append, Model.out, Bool.false_eq_true, ↓reduceIte, endL_txt]
    · rw [← hR]
      exact out_writes st s hc false
    · rw [← hR]
      rfl

set_option maxHeartbeats 8000000 in
/-- At the end of file, the record area outside the date range: the end message. -/
theorem step_end_out (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
    (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
    (ds : Array U8 10#usize) (df : Array U8 1#usize) (de : Array U8 10#usize) (R : Model.Out)
    (hL : s1.val.length < 2 ^ 28)
    (st : cbtrn03c.St) (a : Array U8 16#usize) (a1 : Array U8 2#usize) (i : I64)
    (a2 : Array U8 10#usize) (a3 : Array U8 100#usize) (i1 i2 : I64) (a4 a5 : Array U8 50#usize)
    (a6 : Array U8 10#usize) (a7 : Array U8 16#usize) (a8 a9 : Array U8 26#usize)
    (a10 : Array U8 20#usize) (xref : cbtrn03c.CardXrefRecord) (ttype : cbtrn03c.TranTypeRecord)
    (tcat : cbtrn03c.TranCatRecord) (first : Bool) (card : Array U8 16#usize) (idx : Usize)
    (s : Model.St) (hc : Corr st s) (hp : ¬ idx.val < s1.val.length)
    (hdl : st.displays.val.length ≤ idx.val + 2) (hidx : idx.val ≤ s1.val.length)
    (hin : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩)
      (TranRecord.vals ⟨a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10⟩) = false)
    (hR : Model.out s false = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card false idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, false, idx)) := by
  have hU := usize_max_ge
  simp only [cbtrn03c.run_loop0.body, cbtrn03c.finish]
  by_cases hc1 : cmpL (a9.val.take 10) ds.val = .lt
  · t03_wpx [hp, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val, ordI_nonneg, ordI_nonpos, hc1]
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    simp only [stepPost, loopCls_done, OutQ]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [← hR]
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
        uscalar_ofNat_val, List.nil_append, Model.out, Bool.false_eq_true, ↓reduceIte, endL_txt]
    · rw [← hR]
      exact out_writes st s hc false
    · rw [← hR]
      rfl
  · have hc2 : cmpL (a9.val.take 10) de.val = .gt :=
      inRange_false ⟨a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10⟩ ds df de hin hc1
    t03_wpx [hp, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val, ordI_nonneg, ordI_nonpos, hc1, hc2]
    simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
    simp only [stepPost, loopCls_done, OutQ]
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [← hR]
      simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
        uscalar_ofNat_val, List.nil_append, Model.out, Bool.false_eq_true, ↓reduceIte, endL_txt]
    · rw [← hR]
      exact out_writes st s hc false
    · rw [← hR]
      rfl

set_option maxHeartbeats 8000000 in
/-- At the end of file, the record area in the date range: its amount displayed and added once
more, the page and grand totals (`Model.eofTail`). -/
theorem step_end_in (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
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
    (hp : ¬ idx.val < s1.val.length) (hidx : idx.val ≤ s1.val.length)
    (hwl : st.writes.val.length ≤ 13 * idx.val) (hdl : st.displays.val.length ≤ idx.val + 2)
    (hamt0 : i1.val.natAbs < 100000000000) (hcat0 : -9223372036854775808 < i.val)
    (hmer0 : -9223372036854775808 < i2.val)
    (hin : Model.inRange (WsDateparmRecord.vals ⟨ds, df, de⟩)
      (TranRecord.vals ⟨a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10⟩) = true)
    (hR : Model.out (Model.eofTail s
      (TranRecord.vals ⟨a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10⟩)) false = R) :
    wp (cbtrn03c.run_loop0.body s1 s2 s3 s4 ds df de st a a1 i a2 a3 i1 i2 a4 a5 a6 a7 a8 a9 a10
      xref ttype tcat first card false idx)
      (stepPost s1 s2 s3 s4 ds df de R (st, a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10,
        xref, ttype, tcat, first, card, false, idx)) := by
  have hU := usize_max_ge
  obtain ⟨hlc, hpg, hac, hgr⟩ := hb
  have hpv : -9223372036854775808 < st.page_total.val := by rw [hc.page]; omega
  have hav : -9223372036854775808 < i1.val := by omega
  have hp' : -100000000000 < st.page_total.val ∧ st.page_total.val < 100000000000 := by
    rw [hc.page]; omega
  have ha' : -100000000000 < st.account_total.val ∧ st.account_total.val < 100000000000 := by
    rw [hc.acct]; omega
  have hi1 : -100000000000 < i1.val ∧ i1.val < 100000000000 := by omega
  have hboth := inRange_true ⟨a, a1, i, a2, a3, i1, i2, a4, a5, a6, a7, a8, a9, a10⟩ ds df de hin
  have hc1 : ¬ cmpL (a9.val.take 10) ds.val = .lt := hboth.1
  have hc2 : ¬ cmpL (a9.val.take 10) de.val = .gt := hboth.2
  simp only [cbtrn03c.run_loop0.body, cbtrn03c.finish]
  unfold cbtrn03c.trunc11
  t03_wpx [hp, hpv, hav, array_index_range0, Slice.from_val, cmp_ebcdic_eq, ordR_ge, ordR_le, ordR_val, ordI_nonneg, ordI_nonpos, hc1, hc2]
  simp (config := { maxSteps := 4000000 }) (disch := first | omega | scalar_tac) only
      [dite_eq_left]
  have hb5 : Bnd { Model.dsp (Model.dsp s (Model.txt "TRAN-AMT " ++ Model.zoned 11 i1.val))
      (Model.txt "WS-PAGE-TOTAL" ++ Model.zoned 11 s.page) with
      page := Model.trunc11 (s.page + i1.val), acct := Model.trunc11 (s.acct + i1.val) } :=
    ⟨hlc, trunc11_bound _, trunc11_bound _, hgr⟩
  refine wp_mono (write_page_totals_spec _ { Model.dsp (Model.dsp s
      (Model.txt "TRAN-AMT " ++ Model.zoned 11 i1.val))
      (Model.txt "WS-PAGE-TOTAL" ++ Model.zoned 11 s.page) with
      page := Model.trunc11 (s.page + i1.val), acct := Model.trunc11 (s.acct + i1.val) }
    ⟨?_, hc.writes, hc.lc, ?_, ?_, hc.grand, hc.rs, hc.re⟩ hb5 ?_) ?_
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil, hc.disp,
      uscalar_ofNat_val, List.nil_append, zeroPad_val, overByte_val, Model.dsp, Model.zoned,
      Nat.reduceSub, hc.page, List.append_assoc,
      show Model.txt "TRAN-AMT " = [84, 82, 65, 78, 45, 65, 77, 84, 32] from by decide,
      show Model.txt "WS-PAGE-TOTAL" = [87, 83, 45, 80, 65, 71, 69, 45, 84, 79, 84, 65, 76] from
        by decide]
  · simp only [iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val, hc.page, Model.trunc11]
  · simp only [iscalar_srem_val, IScalar.ofInt_val_eq, iscalar_ofInt_val, hc.acct, Model.trunc11]
  · show st.writes.val.length + 2 < Usize.max
    omega
  rintro _ ⟨st3, rfl, hc3, hl3, hd3⟩
  dsimp only
  have e3 : st3.writes.val.length = st.writes.val.length + 2 := hl3
  refine wp_mono (write_grand_totals_spec st3 _ hc3 (bnd_pageTotals _ hb5) (by omega)) ?_
  rintro _ ⟨st4, rfl, hc4, hl4, hd4⟩
  dsimp only
  simp only [stepPost, loopCls_cont, loopInv, loopVar, ↓reduceIte, eq_self_iff_true,
    Bool.false_eq_true]
  refine ⟨⟨_, hc4, bnd_pageTotals _ hb5, hf, hcard, hx, hxa, hidx, ?_, ?_, hamt0, hcat0, hmer0,
    Or.inr ⟨by first | exact trivial | rfl, hR⟩⟩, by omega⟩
  · omega
  · have e : st4.displays.val.length = st.displays.val.length + 2 := by
      rw [hd4, hd3]
      simp
    omega

end EquivLean.Modernize.Cbtrn03c.Rust

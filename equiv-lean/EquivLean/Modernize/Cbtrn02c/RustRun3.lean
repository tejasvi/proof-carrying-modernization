import EquivLean.Modernize.Cbtrn02c.RustRun2
/-!
# CBTRN02C → Rust: the model's invariants, and the relation of the main loop's state
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-! ## Rust's `i64` remainder -/

theorem srem_val (x y : I64) : (⟨BitVec.srem x.bv y.bv⟩ : I64).val = Int.tmod x.val y.val := by
  show (BitVec.srem x.bv y.bv).toInt = Int.tmod x.bv.toInt y.bv.toInt
  rw [BitVec.toInt_srem]

theorem P9_val : cbtrn02c.P9.val = 10 ^ 9 := by unfold cbtrn02c.P9; rfl
theorem P11_val : cbtrn02c.P11.val = 10 ^ 11 := by unfold cbtrn02c.P11; rfl
theorem P12_val : cbtrn02c.P12.val = 10 ^ 12 := by unfold cbtrn02c.P12; rfl

theorem tmod_small (v : Int) (n : Nat) (h : v.natAbs < 10 ^ n) : Int.tmod v (10 ^ n) = v := by
  have hm : (0 : Int) < 10 ^ n := by positivity
  have h' : (v.natAbs : Int) < 10 ^ n := by exact_mod_cast h
  rcases (show 0 ≤ v ∨ v < 0 by omega) with hv | hv
  · rw [Int.tmod_eq_emod_of_nonneg hv, Int.emod_eq_of_lt hv (by omega)]
  · have : Int.tmod (-v) (10 ^ n) = -v := by
      rw [Int.tmod_eq_emod_of_nonneg (by omega), Int.emod_eq_of_lt (by omega) (by omega)]
    rw [← neg_neg v, Int.neg_tmod, this, neg_neg]

theorem tmod_lt (v : Int) (n : Nat) : (Int.tmod v (10 ^ n)).natAbs < 10 ^ n := by
  rw [Int.natAbs_tmod]
  have h1 : (10 ^ n : Int).natAbs = 10 ^ n := by simp
  rw [h1]
  exact Nat.mod_lt _ (by positivity)

/-! ## coblean's truncation is Rust's `%` -/

theorem fitNum_tmod (fmt : NumFmt) (hs : fmt.signed = true) (hu : fmt.usage = .display) (v : Int) :
    (Sem.fitNum {} fmt v).2 = Int.tmod v (10 ^ fmt.digits) := by
  have hfb : fmt.fullBinary {} = false := by simp [NumFmt.fullBinary, hu]
  simp only [Sem.fitNum, hs, _root_.ite_true, hfb, Bool.false_eq_true, _root_.ite_false, Sem.fitDec]
  split_ifs with h
  · exact (tmod_small v _ h).symm
  · simp only [truncDigits]
    split_ifs with hv
    · rw [Int.tmod_eq_emod_of_nonneg hv]
    · rw [← neg_neg v, Int.neg_tmod, Int.tmod_eq_emod_of_nonneg (by omega), neg_neg]

/-! ## The numeric DISPLAY encodings as the Rust digits -/

theorem encodeNum_unsigned {fmt : NumFmt} (hu : fmt.usage = .display) (hs : fmt.signed = false)
    (hd : 0 < fmt.digits) (v : Int) : encodeNum {} fmt v = (digs fmt.digits v.natAbs).map ebc :=
  (digs_ebc hu hs hd v).symm

theorem encodeNum_signed {fmt : NumFmt} (hu : fmt.usage = .display) (hs : fmt.signed = true)
    (hsep : fmt.signSep = false) (hlead : fmt.signLead = false) (v : Int) :
    encodeNum {} fmt v = (sdigs fmt.digits v).map ebc := by
  apply map_cp037_inj
  rw [latin1_text, sdigs_val, text_signed hu hs hsep hlead]

/-! ## The daily record's bytes (`encode_dalytran`) -/

/-- The 350 Latin-1 bytes of a daily transaction record. -/
def encList (r : cbtrn02c.DalytranRecord) : List U8 :=
  r.dalytran_id.val ++ r.dalytran_type_cd.val ++ digs 4 r.dalytran_cat_cd.val.natAbs ++
    r.dalytran_source.val ++ r.dalytran_desc.val ++ sdigs 11 r.dalytran_amt.val ++
    digs 9 r.dalytran_merchant_id.val.natAbs ++ r.dalytran_merchant_name.val ++
    r.dalytran_merchant_city.val ++ r.dalytran_merchant_zip.val ++ r.dalytran_card_num.val ++
    r.dalytran_orig_ts.val ++ r.dalytran_proc_ts.val ++ r.filler1.val

theorem arr_len {α : Type _} {n : Usize} (a : Std.Array α n) : a.val.length = n.val := a.property

theorem encList_length (r : cbtrn02c.DalytranRecord) : (encList r).length = 350 := by
  simp only [encList, List.length_append, arr_len, digs_length, sdigs_length _ _ (by norm_num : 1 ≤ 11)]
  simp

set_option maxRecDepth 4000 in
/-- **The bytes of a daily record are its COBOL encoding** (CP037 of the Latin-1 bytes). -/
theorem encList_ebc (r : cbtrn02c.DalytranRecord) :
    (encList r).map ebc = Model.DalytranRecord.encode (DalytranRecord.vals r) := by
  simp only [encList, Model.DalytranRecord, DalytranRecord.vals, Schema.encode, List.zip_cons_cons,
    List.zip_nil_left, List.zip_nil_right, List.flatMap_cons, List.flatMap_nil, Field.encode,
    List.map_append, List.append_nil]
  simp (disch := decide) only [encodeNum_unsigned, encodeNum_signed]
  simp only [List.append_assoc]

/-! ## The validation trailer -/

theorem trailer_ebc (code : Int) (descR : List U8) (descM : List UInt8)
    (hd : descR.map ebc = descM ++ List.replicate (76 - descM.length) 64) :
    (digs 4 code.natAbs ++ descR).map ebc = CardDemo.Cbtrn02c.trailer code descM := by
  rw [List.map_append, hd, CardDemo.Cbtrn02c.trailer,
    encodeNum_unsigned (by rfl) (by rfl) (by decide)]
  simp only [List.append_assoc]

end EquivLean.Modernize.Cbtrn02c.Rust

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

theorem from_slice_from {α : Type _} {n : Usize} (b : Std.Array α n) (L : List α) (h : L.length ≤ Usize.max)
    (hl : L.length = n.val) :
    Std.Array.from_slice b (Slice.from L h) = Std.Array.from L hl := by
  rw [Std.Array.eq_iff, Std.Array.from_slice_val _ _ (by rw [Slice.from_val]; exact hl), Slice.from_val,
    Std.Array.from_val]

/-- `put` under `wp`: the new buffer is the old one with `src` at `pos`. -/
theorem wp_put (buf : Slice U8) (pos : Usize) (src : Slice U8)
    (Q : Except Error (Usize × Slice U8) → Prop)
    (h : pos.val + src.val.length ≤ buf.val.length)
    (hQ : ∀ b' : Slice U8,
      b'.val = buf.val.take pos.val ++ src.val ++ buf.val.drop (pos.val + src.val.length) →
      Q (.ok (usz (pos.val + src.val.length), b'))) :
    wp (cbtrn02c.put buf pos src) Q := by
  rw [put_eq _ _ _ h, wp_ok]
  exact hQ _ (Slice.from_val _ _)

theorem from_slice_eq {α : Type _} {n : Usize} {B : Std.Array α n} (b : Slice α) {L : List α}
    (hb : b.val = L) (hl : L.length = n.val) : Std.Array.from_slice B b = Std.Array.from L hl := by
  rw [Std.Array.eq_iff, Std.Array.from_slice_val _ _ (by rw [hb]; exact hl), hb, Std.Array.from_val]

/-- Lengths and linear arithmetic. -/
macro "len_tac" : tactic => `(tactic| (first
  | omega
  | (simp (disch := omega) only [Std.Array.to_slice, Slice.from_val, Std.Array.from_val,
      alloc.vec.Vec.deref, alloc.vec.Vec.from_val, digs_length, sdigs_length, usz_val, arr_len,
      UScalar.ofNatCore_val_eq, List.length_append, List.length_take, List.length_drop,
      List.length_replicate, Std.Array.repeat_val, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceLeDiff] <;> omega)
  | fail "len_tac"))

/-- One `put` into the record buffer: its bound; the new buffer in normal form (the fields so
far, then spaces), which replaces the buffer in the rest of the run. -/
macro "put_step" : tactic => `(tactic| (
  apply wp_put
  · len_tac
  intro b hb
  simp (disch := len_tac) only [Std.Array.to_slice, Slice.from_val, Std.Array.from_val,
    Std.Array.repeat_val, usz_val, UScalar.ofNatCore_val_eq, List.take_append, List.drop_append,
    List.length_append, List.length_take, List.length_drop, List.length_replicate, digs_length,
    sdigs_length, arr_len, List.drop_replicate, List.take_of_length_le, List.drop_of_length_le,
    Nat.sub_self, List.take_zero, List.drop_zero, List.nil_append, List.append_nil,
    List.append_assoc, List.replicate_zero, alloc.vec.Vec.from_val, Nat.reduceAdd,
    Nat.reduceSub] at hb
  aeneas_wp [Std.Array.to_slice_mut]
  rw [from_slice_eq b hb (by
    simp (disch := omega) only [List.length_append, arr_len, List.length_replicate,
      UScalar.ofNatCore_val_eq, digs_length, sdigs_length, Nat.reduceAdd])]))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem encode_dalytran_eq (r : cbtrn02c.DalytranRecord) :
    cbtrn02c.encode_dalytran r = .ok (Std.Array.from (encList r) (encList_length r)) := by
  have hm := usize_max_ge
  refine eq_ok_of_wp' ?_
  rw [cbtrn02c.encode_dalytran]
  aeneas_wp [Std.Array.to_slice_mut,
    digits_eq r.dalytran_cat_cd 4#usize (by simp),
    digits_eq r.dalytran_merchant_id 9#usize (by simp),
    signed_digits_eq r.dalytran_amt 11#usize (by simp) (by simp),
    alloc.vec.Vec.deref]
  put_step
  put_step
  put_step
  put_step
  put_step
  put_step
  put_step
  put_step
  put_step
  put_step
  put_step
  put_step
  put_step
  put_step
  simp only [Except.ok.injEq, Std.Array.eq_iff, Std.Array.from_val, encList, List.append_assoc]

end EquivLean.Modernize.Cbtrn02c.Rust

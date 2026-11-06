import EquivLean.Bridge.Aeneas.Digits
import EquivLean.Modernize.Cbtrn01c.RustProof

/-!
# CBTRN01C → Rust: the equation of `run` (`RunSpec`), hence the generated statement

The translation is veriforch's (`examples/rust/mod_cbtrn01c`, `Demo/Gen/Aeneas/ModCbtrn01c`).

* The helpers: `push_bytes`, the copy loop of `push_unsigned`, the record line `dalytran_bytes` and
  the two searches of `run` (2000-LOOKUP-XREF, 3000-READ-ACCOUNT, as `List.find?`) by
  `aeneas_spec`; by hand: `abs_u64` (it never overflows), the digit loop of `digits_of` (a
  `[u8; 18]` buffer filled from position `n` down), the copy loop of `push_signed_overpunch` (it
  compares `i + 1` with `n`) and `bytes_eq16`.  `push_unsigned_eq`: the `n` low digits of `|v|`;
  `push_signed_overpunch_eq`: the `n - 1` leading digits, then the overpunched last digit
  (`overByte`).
* The lines of `run` in bytes: the literals (`startL`, …), a record's line `dalLine`, what the
  lookups display `lookupLines` (with the account key as `run` computes it: `akeyOf`, the low
  11 digits of the cross-reference's account id; `akey_eq` folds that computation into one step),
  `recLines`.
* `run_loop0_spec`: the read loop (`while eof_flag != b'Y'`, with `pos` and `eof_hit`) by
  `wp_loop` with `loopInv`: while the flag is `'N'`, the start line and the lines of the records
  read so far, the last of them in the record area; the end-of-file iteration does the lookups
  once more for it and sets the flag to `'Y'`; the next iteration adds the end line and stops.
  Each step is symbolic execution (`trn01c_wp`) after a case split on the two searches.
  `run_eq`: `run` in bytes.
* The glue: a record's line is `Schema.textS` of its field values (`dalLine_text`), the lookups'
  lines are `Model.lookupText` (`lookupLines_text`: a valid cross-reference's account id is below
  `10 ^ 11`, so `run`'s key is the id), the literals are the texts of `Model.displayText`, and the
  initial record area is `Model.dal0` (`dal0R_vals`).
* `run_spec : RunSpec`, and `rust : Statement`.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn01c.Rust
open Cobol.Digits (toDigits)

/-! ## The helpers -/

/-- `push_bytes`: `src` after `dst`. -/
theorem push_bytes_eq (dst : alloc.vec.Vec U8) (src : Slice U8)
    (h : dst.val.length + src.val.length < Usize.max) :
    cbtrn01c.push_bytes dst src =
      .ok (alloc.vec.Vec.from (dst.val ++ src.val) (by simp; omega)) := by
  aeneas_spec [cbtrn01c.push_bytes, cbtrn01c.push_bytes_loop]

/-- `abs_u64`: `|v|`, for every `v` (the negation of `v + 1` never overflows). -/
theorem abs_u64_spec (v : I64) :
    wp (cbtrn01c.abs_u64 v) (fun o => ∃ w, o = .ok w ∧ w.val = v.val.natAbs) := by
  unfold cbtrn01c.abs_u64
  have hb := v.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hb
  by_cases hv : v.val < 0
  · have hlt : (v < 0#i64) = True := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_true]
    aeneas_wp [IScalar.cast_val_eq]
    simp only [IScalar.hcast_val_eq, IScalar.ofInt_val_eq, UScalarTy.U64_numBits_eq, Int.reducePow]
    split_ifs with h1 h2 h3
    · exact ⟨_, rfl, by simp only [UScalar.ofNatCore_val_eq]; omega⟩
    all_goals (exfalso; omega)
  · have hlt : (v < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_false, wp_ok]
    exact ⟨_, rfl, by rw [IScalar.hcast_val_eq]; simp only [UScalarTy.U64_numBits_eq]; omega⟩

/-- `abs_u64`'s value: `|v|` (it never overflows). -/
def absU (v : I64) : U64 := ⟨BitVec.ofNat 64 v.val.natAbs⟩

theorem absU_val (v : I64) : (absU v).val = v.val.natAbs := by
  have hb := v.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hb
  simp only [absU, UScalar.val]
  apply Nat.mod_eq_of_lt
  omega

theorem abs_u64_eq (v : I64) : cbtrn01c.abs_u64 v = .ok (absU v) := by
  obtain ⟨w, hw, hwv⟩ := exists_ok_of_wp (abs_u64_spec v)
  rw [hw]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hwv, absU_val]

set_option maxHeartbeats 2000000 in
/-- The digit loop of `digits_of`: from position `n` down, the `n` low digits of `x`,
right-aligned in the first `n` bytes of the buffer. -/
theorem digits_of_loop_spec (n : Usize) (x : Nat) (w : U64) (hn : n.val ≤ 18) (hw : w.val = x) :
    wp (cbtrn01c.digits_of_loop (Array.repeat 18#usize 48#u8) w n)
      (fun o => ∃ b, o = .ok b ∧ b.val = zeroPad n.val x ++ List.replicate (18 - n.val) 48#u8) := by
  simp only [cbtrn01c.digits_of_loop]
  refine wp_loop (loop_shape _) (fun s => s.2.2.val ≤ n.val ∧
      s.2.1.val = x / 10 ^ (n.val - s.2.2.val) ∧
      s.1.val = List.replicate s.2.2.val 48#u8 ++ zeroPad (n.val - s.2.2.val) x ++
        List.replicate (18 - n.val) 48#u8)
    (fun s => s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro buf w' i hinv
    obtain ⟨hi, hw', hbuf⟩ := hinv
    have hlen : buf.val.length = 18 := buf.property
    aeneas_wp [rust_loop_body, array_update_eq, UScalar.cast_val_eq, Array.from_val, hlen]
    by_cases h1 : 0 < i.val
    · have hd10 : w'.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have h256 : w'.val % 10 % 2 ^ 8 = w'.val % 10 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, _root_.ite_true, h256]
      split_ifs
      all_goals try (exfalso; omega)
      simp only [loopCls_cont]
      obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
      refine ⟨⟨by simp only [UScalar.ofNatCore_val_eq]; omega, ?_, ?_⟩, by
        simp only [UScalar.ofNatCore_val_eq]; omega⟩
      · rw [UScalar.ofNatCore_val_eq, UScalar.ofNatCore_val_eq, hw', Nat.div_div_eq_div_mul,
          ← Nat.pow_succ]
        congr 2
        omega
      · simp only [Array.from_val, hbuf, UScalar.ofNatCore_val_eq]
        rw [hk, show k + 1 - 1 = k by omega, List.append_assoc, set_replicate_end,
          show n.val - k = (n.val - (k + 1)) + 1 by omega, zeroPad_succ_left]
        simp only [List.append_assoc, List.cons_append, List.append_cancel_left_eq,
          List.cons.injEq, and_true]
        rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq, byteOf_val _ (by omega), hw', hk]
    · simp only [h1, _root_.ite_false, loopCls_done]
      refine ⟨buf, rfl, ?_⟩
      have e : i.val = 0 := by omega
      rw [hbuf, e, Nat.sub_zero, List.replicate_zero, List.nil_append]
  · refine ⟨le_refl _, by simp [hw], ?_⟩
    simp only [Array.repeat_val, uscalar_ofNat_val, Nat.sub_self]
    have z : zeroPad 0 x = [] := by simp [zeroPad, zpad, toDigits]
    rw [z, List.append_nil, ← List.replicate_add]
    congr 1
    omega

/-- `digits_of`: the `n` low digits of `|v|`, then the rest of the buffer (`'0'`s). -/
theorem digits_of_spec (v : I64) (n : Usize) (hn : n.val ≤ 18) :
    wp (cbtrn01c.digits_of v n) (fun o => ∃ b, o = .ok b ∧
      b.val = zeroPad n.val v.val.natAbs ++ List.replicate (18 - n.val) 48#u8) := by
  simp only [cbtrn01c.digits_of, wp_bind]
  refine wp_mono (abs_u64_spec v) ?_
  rintro _ ⟨w, rfl, hw⟩
  exact digits_of_loop_spec n _ w hn hw

/-- The copy loop of `push_unsigned`: the first `n` bytes of the buffer. -/
theorem push_unsigned_loop_eq (dst : alloc.vec.Vec U8) (n : Usize) (d : Array U8 18#usize)
    (hd : n.val ≤ 18) (h : dst.val.length + n.val < Usize.max) :
    cbtrn01c.push_unsigned_loop dst n d 0#usize =
      .ok (alloc.vec.Vec.from (dst.val ++ d.val.take n.val) (by simp; omega)) := by
  aeneas_spec [cbtrn01c.push_unsigned_loop]

/-- `push_unsigned`: the `n` low decimal digits of `|v|` after `dst` (`n ≤ 18`). -/
theorem push_unsigned_eq (dst : alloc.vec.Vec U8) (v : I64) (n : Usize)
    (hn : n.val ≤ 18) (h : dst.val.length + n.val < Usize.max) :
    cbtrn01c.push_unsigned dst v n =
      .ok (alloc.vec.Vec.from (dst.val ++ zeroPad n.val v.val.natAbs)
        (by simp [zeroPad_length]; omega)) := by
  refine eq_ok_of_wp ?_
  simp only [cbtrn01c.push_unsigned, wp_bind]
  refine wp_mono (digits_of_spec v n hn) ?_
  rintro _ ⟨b, rfl, hb⟩
  dsimp only
  rw [push_unsigned_loop_eq dst n b hn h]
  simp only [wp_ok, Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hb]
  rw [List.take_append_of_le_length (by simp [zeroPad_length]),
    List.take_of_length_le (by simp [zeroPad_length])]

theorem zeroPad_succ_right (m x : Nat) :
    zeroPad (m + 1) x = zeroPad m (x / 10) ++ [byteOf (48 + x % 10)] := by
  simp only [zeroPad, zpad, toDigits_succ, List.map_append, List.map_cons, List.map_nil]

/-- The copy loop of `push_signed_overpunch`: the first `n - 1` bytes of the buffer. -/
theorem push_signed_overpunch_loop_eq (dst : alloc.vec.Vec U8) (n : Usize)
    (d : Array U8 18#usize) (hn1 : 1 ≤ n.val) (hd : n.val ≤ 18)
    (h : dst.val.length + n.val < Usize.max) :
    cbtrn01c.push_signed_overpunch_loop dst n d 0#usize =
      .ok (alloc.vec.Vec.from (dst.val ++ d.val.take (n.val - 1)) (by simp; omega)) := by
  refine eq_ok_of_wp ?_
  simp only [cbtrn01c.push_signed_overpunch_loop]
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ n.val - 1 ∧ s.1.val = dst.val ++ d.val.take s.2.val)
    (fun s => n.val - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro out i hinv
    obtain ⟨hi, hout⟩ := hinv
    have hlen : d.val.length = 18 := d.property
    aeneas_wp [rust_loop_body, array_index_usize_eq, hlen]
    have hol : out.val.length = dst.val.length + i.val := by
      rw [hout, List.length_append, List.length_take]; omega
    split_ifs with h1 h2 h3 h4
    · simp only [loopCls_cont, UScalar.ofNatCore_val_eq, alloc.vec.Vec.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hout, take_succ_of_lt (by omega), List.append_assoc]
    · exfalso; omega
    · exfalso; omega
    · simp only [loopCls_done, Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hout]
      congr 2
      omega
    · exfalso; scalar_tac
  · simp

/-- The overpunched last digit of a signed DISPLAY value (`{`, `A` … `I`, `}`, `J` … `R`), as a
Latin-1 byte. -/
def overByte (v : Int) : U8 := byteOf (overpunch (decide (v < 0)) (v.natAbs % 10))

theorem overByte_val (v : Int) :
    (overByte v).val = overpunch (decide (v < 0)) (v.natAbs % 10) := by
  have := Nat.mod_lt v.natAbs (show 10 > 0 by norm_num)
  unfold overByte
  apply byteOf_val
  unfold overpunch
  split_ifs <;> omega

set_option maxHeartbeats 1000000 in
/-- `push_signed_overpunch`: the `n - 1` leading digits of `|v|` (of its `n` low ones), then the
overpunched last digit, after `dst` (`1 ≤ n ≤ 18`). -/
theorem push_signed_overpunch_eq (dst : alloc.vec.Vec U8) (v : I64) (n : Usize)
    (hn1 : 1 ≤ n.val) (hn : n.val ≤ 18) (h : dst.val.length + n.val < Usize.max) :
    cbtrn01c.push_signed_overpunch dst v n =
      .ok (alloc.vec.Vec.from
        (dst.val ++ zeroPad (n.val - 1) (v.val.natAbs / 10) ++ [overByte v.val])
        (by simp [zeroPad_length]; omega)) := by
  refine eq_ok_of_wp ?_
  simp only [cbtrn01c.push_signed_overpunch, wp_bind]
  refine wp_mono (digits_of_spec v n hn) ?_
  rintro _ ⟨b, rfl, hb⟩
  dsimp only
  simp only [push_signed_overpunch_loop_eq dst n b hn1 hn h, wp_ok]
  obtain ⟨m, hm⟩ : ∃ m, n.val = m + 1 := ⟨n.val - 1, by omega⟩
  have hzl := zeroPad_length m (v.val.natAbs / 10)
  have hbv : b.val = zeroPad m (v.val.natAbs / 10) ++ ([byteOf (48 + v.val.natAbs % 10)] ++
      List.replicate (18 - n.val) 48#u8) := by
    rw [hb, hm, zeroPad_succ_right, List.append_assoc]
  have hlen : b.val.length = 18 := b.property
  have htake : b.val.take (n.val - 1) = zeroPad m (v.val.natAbs / 10) := by
    rw [hbv, hm, Nat.add_sub_cancel]
    exact List.take_left' hzl
  have hget : ∀ hi : n.val - 1 < b.val.length,
      b.val[n.val - 1]'hi = byteOf (48 + v.val.natAbs % 10) := by
    intro hi
    simp only [hbv, hm, Nat.add_sub_cancel]
    rw [List.getElem_append_right (by omega)]
    simp [hzl]
  have hd10 : v.val.natAbs % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hbyte : (byteOf (48 + v.val.natAbs % 10)).val = 48 + v.val.natAbs % 10 :=
    byteOf_val _ (by omega)
  aeneas_wp [array_index_usize_eq, hlen, htake, hget, hbyte]
  have hm1 : n.val - 1 = m := by omega
  have c1 : (dst.val ++ zeroPad m (v.val.natAbs / 10)).length < Usize.max := by
    rw [List.length_append, hzl]; omega
  have c2 : n.val - 1 < 18 := by omega
  have c3 : 65 + v.val.natAbs % 10 ≤ 255 := by omega
  have c4 : 74 + v.val.natAbs % 10 ≤ 255 := by omega
  have c5 : 1 ≤ 65 + v.val.natAbs % 10 := by omega
  have c6 : 1 ≤ 74 + v.val.natAbs % 10 := by omega
  simp only [hn1, c1, c2, c3, c4, c5, c6, Nat.add_sub_cancel_left, Nat.le_add_right,
    _root_.dite_true, _root_.ite_true]
  split_ifs with hv hd hd
  all_goals simp only [Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hm1,
      List.append_cancel_left_eq, List.cons.injEq, and_true]
  all_goals simp only [UScalar.eq_equiv, overByte_val]
  · have : decide (v.val < 0) = false := decide_eq_false (by omega)
    simp [overpunch, this, hd]
  · have : decide (v.val < 0) = false := decide_eq_false (by omega)
    simp only [overpunch, this, hd, UScalar.ofNatCore_val_eq]
    simp
  · have : decide (v.val < 0) = true := decide_eq_true (by omega)
    simp [overpunch, this, hd]
  · have : decide (v.val < 0) = true := decide_eq_true (by omega)
    simp only [overpunch, this, hd, UScalar.ofNatCore_val_eq]
    simp

/-- The display line of a daily transaction record (Latin-1 bytes): its fields in order, the
unsigned numeric ones as zero-padded digits, the amount with its overpunched last digit. -/
def dalLine (r : cbtrn01c.DalytranRecord) : List U8 :=
  r.dalytran_id.val ++ r.dalytran_type_cd.val ++ zeroPad 4 r.dalytran_cat_cd.val.natAbs ++
    r.dalytran_source.val ++ r.dalytran_desc.val ++
    (zeroPad 10 (r.dalytran_amt.val.natAbs / 10) ++ [overByte r.dalytran_amt.val]) ++
    zeroPad 9 r.dalytran_merchant_id.val.natAbs ++ r.dalytran_merchant_name.val ++
    r.dalytran_merchant_city.val ++ r.dalytran_merchant_zip.val ++ r.dalytran_card_num.val ++
    r.dalytran_orig_ts.val ++ r.dalytran_proc_ts.val ++ r.filler1.val

theorem dalLine_length (r : cbtrn01c.DalytranRecord) : (dalLine r).length = 350 := by
  simp [dalLine, zeroPad_length]

set_option maxHeartbeats 4000000 in
/-- `dalytran_bytes`: the record's line. -/
theorem dalytran_bytes_eq (r : cbtrn01c.DalytranRecord) :
    cbtrn01c.dalytran_bytes r =
      .ok (alloc.vec.Vec.from (dalLine r) (by rw [dalLine_length]; scalar_tac)) := by
  aeneas_spec [cbtrn01c.dalytran_bytes, dalLine] with [push_bytes_eq, push_unsigned_eq,
    push_signed_overpunch_eq, Array.length_eq, zeroPad_length]

/-- `bytes_eq16`: equality of the two byte arrays. -/
theorem bytes_eq16_eq (a b : Array U8 16#usize) :
    cbtrn01c.bytes_eq16 a b = .ok (decide (a.val = b.val)) := by
  refine eq_ok_of_wp ?_
  simp only [cbtrn01c.bytes_eq16, cbtrn01c.bytes_eq16_loop]
  have ha : a.val.length = 16 := a.property
  have hb : b.val.length = 16 := b.property
  refine wp_loop (loop_shape _) (fun i => i.val ≤ 16 ∧ a.val.take i.val = b.val.take i.val)
    (fun i => 16 - i.val) ?_ _ ?_
  · rintro i ⟨hi, ht⟩
    aeneas_wp [rust_loop_body, array_index_usize_eq, ha, hb]
    split_ifs with h1 h2 h3
    · simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [take_succ_of_lt (by omega), take_succ_of_lt (by omega), ht, UScalar.eq_of_val_eq h2]
    · exfalso; scalar_tac
    · simp only [loopCls_done, Except.ok.injEq]
      refine (decide_eq_false fun hab => h2 ?_).symm
      rw [List.getElem_of_eq hab]
    · simp only [loopCls_done, Except.ok.injEq]
      have e : i.val = 16 := by omega
      rw [e, List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at ht
      simp [ht]
  · simp

/-- The search of the cross-reference file (2000-LOOKUP-XREF): the first record with the card
number, else the record area with the card number moved in. -/
theorem run_loop0_loop0_eq (xs : Slice cbtrn01c.CardXrefRecord) (key : Array U8 16#usize)
    (i i1 : I64) (a : Array U8 14#usize) (key1 : Array U8 16#usize) :
    cbtrn01c.run_loop0_loop0 xs key i i1 a key1 0#usize =
      .ok (match xs.val.find? (fun x => decide (x.xref_card_num.val = key1.val)) with
        | some x => (x, true)
        | none => ({ xref_card_num := key, xref_cust_id := i, xref_acct_id := i1, filler1 := a },
            false)) := by
  aeneas_spec [cbtrn01c.run_loop0_loop0] with [bytes_eq16_eq]

theorem run_loop0_loop2_eq (xs : Slice cbtrn01c.CardXrefRecord) (key : Array U8 16#usize)
    (i i1 : I64) (a : Array U8 14#usize) (key1 : Array U8 16#usize) :
    cbtrn01c.run_loop0_loop2 xs key i i1 a key1 0#usize =
      .ok (match xs.val.find? (fun x => decide (x.xref_card_num.val = key1.val)) with
        | some x => (x, true)
        | none => ({ xref_card_num := key, xref_cust_id := i, xref_acct_id := i1, filler1 := a },
            false)) := by
  aeneas_spec [cbtrn01c.run_loop0_loop2] with [bytes_eq16_eq]

/-- The search of the account file (3000-READ-ACCOUNT): the first record with the key, else the
record area with the key moved in. -/
theorem run_loop0_loop1_eq (accs : Slice cbtrn01c.AccountRecord) (akey : I64)
    (a : Array U8 1#usize) (i i1 i2 : I64) (a1 a2 a3 : Array U8 10#usize) (i3 i4 : I64)
    (a4 a5 : Array U8 10#usize) (a6 : Array U8 178#usize) (akey1 : I64) :
    cbtrn01c.run_loop0_loop1 accs akey a i i1 i2 a1 a2 a3 i3 i4 a4 a5 a6 akey1 0#usize =
      .ok (match accs.val.find? (fun r => decide (r.acct_id = akey1)) with
        | some r => (r, true)
        | none => (cbtrn01c.AccountRecord.mk akey a i i1 i2 a1 a2 a3 i3 i4 a4 a5 a6, false)) := by
  aeneas_spec [cbtrn01c.run_loop0_loop1]

theorem run_loop0_loop3_eq (accs : Slice cbtrn01c.AccountRecord) (akey : I64)
    (a : Array U8 1#usize) (i i1 i2 : I64) (a1 a2 a3 : Array U8 10#usize) (i3 i4 : I64)
    (a4 a5 : Array U8 10#usize) (a6 : Array U8 178#usize) (akey1 : I64) :
    cbtrn01c.run_loop0_loop3 accs akey a i i1 i2 a1 a2 a3 i3 i4 a4 a5 a6 akey1 0#usize =
      .ok (match accs.val.find? (fun r => decide (r.acct_id = akey1)) with
        | some r => (r, true)
        | none => (cbtrn01c.AccountRecord.mk akey a i i1 i2 a1 a2 a3 i3 i4 a4 a5 a6, false)) := by
  aeneas_spec [cbtrn01c.run_loop0_loop3]

/-! ## The lines of `run` -/

/-- `b"START OF EXECUTION OF PROGRAM CBTRN01C"`. -/
def startL : List U8 := [83#u8, 84#u8, 65#u8, 82#u8, 84#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8,
  88#u8, 69#u8, 67#u8, 85#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8,
  79#u8, 71#u8, 82#u8, 65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 84#u8, 82#u8, 78#u8, 48#u8, 49#u8, 67#u8]
/-- `b"END OF EXECUTION OF PROGRAM CBTRN01C"`. -/
def endL : List U8 := [69#u8, 78#u8, 68#u8, 32#u8, 79#u8, 70#u8, 32#u8, 69#u8, 88#u8, 69#u8, 67#u8,
  85#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 79#u8, 70#u8, 32#u8, 80#u8, 82#u8, 79#u8, 71#u8, 82#u8,
  65#u8, 77#u8, 32#u8, 67#u8, 66#u8, 84#u8, 82#u8, 78#u8, 48#u8, 49#u8, 67#u8]
/-- `b"SUCCESSFUL READ OF XREF"`. -/
def okXrefL : List U8 := [83#u8, 85#u8, 67#u8, 67#u8, 69#u8, 83#u8, 83#u8, 70#u8, 85#u8, 76#u8,
  32#u8, 82#u8, 69#u8, 65#u8, 68#u8, 32#u8, 79#u8, 70#u8, 32#u8, 88#u8, 82#u8, 69#u8, 70#u8]
/-- `b"CARD NUMBER: "`. -/
def cardNumL : List U8 := [67#u8, 65#u8, 82#u8, 68#u8, 32#u8, 78#u8, 85#u8, 77#u8, 66#u8, 69#u8,
  82#u8, 58#u8, 32#u8]
/-- `b"ACCOUNT ID : "`. -/
def acctIdL : List U8 := [65#u8, 67#u8, 67#u8, 79#u8, 85#u8, 78#u8, 84#u8, 32#u8, 73#u8, 68#u8,
  32#u8, 58#u8, 32#u8]
/-- `b"CUSTOMER ID: "`. -/
def custIdL : List U8 := [67#u8, 85#u8, 83#u8, 84#u8, 79#u8, 77#u8, 69#u8, 82#u8, 32#u8, 73#u8,
  68#u8, 58#u8, 32#u8]
/-- `b"INVALID CARD NUMBER FOR XREF"`. -/
def invCardL : List U8 := [73#u8, 78#u8, 86#u8, 65#u8, 76#u8, 73#u8, 68#u8, 32#u8, 67#u8, 65#u8,
  82#u8, 68#u8, 32#u8, 78#u8, 85#u8, 77#u8, 66#u8, 69#u8, 82#u8, 32#u8, 70#u8, 79#u8, 82#u8, 32#u8,
  88#u8, 82#u8, 69#u8, 70#u8]
/-- `b"SUCCESSFUL READ OF ACCOUNT FILE"`. -/
def okAcctL : List U8 := [83#u8, 85#u8, 67#u8, 67#u8, 69#u8, 83#u8, 83#u8, 70#u8, 85#u8, 76#u8,
  32#u8, 82#u8, 69#u8, 65#u8, 68#u8, 32#u8, 79#u8, 70#u8, 32#u8, 65#u8, 67#u8, 67#u8, 79#u8, 85#u8,
  78#u8, 84#u8, 32#u8, 70#u8, 73#u8, 76#u8, 69#u8]
/-- `b"INVALID ACCOUNT NUMBER FOUND"`. -/
def invAcctL : List U8 := [73#u8, 78#u8, 86#u8, 65#u8, 76#u8, 73#u8, 68#u8, 32#u8, 65#u8, 67#u8,
  67#u8, 79#u8, 85#u8, 78#u8, 84#u8, 32#u8, 78#u8, 85#u8, 77#u8, 66#u8, 69#u8, 82#u8, 32#u8, 70#u8,
  79#u8, 85#u8, 78#u8, 68#u8]
/-- `b"ACCOUNT "`. -/
def acctL : List U8 := [65#u8, 67#u8, 67#u8, 79#u8, 85#u8, 78#u8, 84#u8, 32#u8]
/-- `b" NOT FOUND"`. -/
def notFoundL : List U8 := [32#u8, 78#u8, 79#u8, 84#u8, 32#u8, 70#u8, 79#u8, 85#u8, 78#u8, 68#u8]
/-- `b"CARD NUMBER "`. -/
def cardL : List U8 := [67#u8, 65#u8, 82#u8, 68#u8, 32#u8, 78#u8, 85#u8, 77#u8, 66#u8, 69#u8, 82#u8,
  32#u8]
/-- `b" COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-"`. -/
def skipL : List U8 := [32#u8, 67#u8, 79#u8, 85#u8, 76#u8, 68#u8, 32#u8, 78#u8, 79#u8, 84#u8, 32#u8,
  66#u8, 69#u8, 32#u8, 86#u8, 69#u8, 82#u8, 73#u8, 70#u8, 73#u8, 69#u8, 68#u8, 46#u8, 32#u8, 83#u8,
  75#u8, 73#u8, 80#u8, 80#u8, 73#u8, 78#u8, 71#u8, 32#u8, 84#u8, 82#u8, 65#u8, 78#u8, 83#u8, 65#u8,
  67#u8, 84#u8, 73#u8, 79#u8, 78#u8, 32#u8, 73#u8, 68#u8, 45#u8]

/-- What the lookups display for the record `d` (2000-LOOKUP-XREF, then 3000-READ-ACCOUNT), as
`run` builds the lines: the first cross-reference record with the card number of `d`; then the
first account whose id is the cross-reference's account id as `run` computes it (the low 11 digits
of its absolute value). -/
def lookupLines (xs : List cbtrn01c.CardXrefRecord) (accs : List cbtrn01c.AccountRecord)
    (d : cbtrn01c.DalytranRecord) : List (List U8) :=
  match xs.find? (fun x => decide (x.xref_card_num.val = d.dalytran_card_num.val)) with
  | none => [invCardL, cardL ++ d.dalytran_card_num.val ++ skipL ++ d.dalytran_id.val]
  | some x =>
    [okXrefL, cardNumL ++ x.xref_card_num.val, acctIdL ++ zeroPad 11 x.xref_acct_id.val.natAbs,
      custIdL ++ zeroPad 9 x.xref_cust_id.val.natAbs] ++
    match accs.find? (fun a => decide (a.acct_id.val =
        ((x.xref_acct_id.val.natAbs % 100000000000 : Nat) : Int))) with
    | none => [invAcctL,
        acctL ++ zeroPad 11 (x.xref_acct_id.val.natAbs % 100000000000) ++ notFoundL]
    | some _ => [okAcctL]

/-- The lines of a record read: its line, then what its lookups display. -/
def recLines (xs : List cbtrn01c.CardXrefRecord) (accs : List cbtrn01c.AccountRecord)
    (r : cbtrn01c.DalytranRecord) : List (List U8) :=
  dalLine r :: lookupLines xs accs r

theorem lookupLines_length_le (xs : List cbtrn01c.CardXrefRecord)
    (accs : List cbtrn01c.AccountRecord) (d : cbtrn01c.DalytranRecord) :
    (lookupLines xs accs d).length ≤ 6 := by
  unfold lookupLines
  split
  · simp
  · split <;> simp

theorem recLines_length_le (xs : List cbtrn01c.CardXrefRecord)
    (accs : List cbtrn01c.AccountRecord) :
    ∀ l : List cbtrn01c.DalytranRecord, (l.flatMap (recLines xs accs)).length ≤ 7 * l.length
  | [] => by simp
  | r :: l => by
    have h1 := recLines_length_le xs accs l
    have h2 := lookupLines_length_le xs accs r
    simp only [List.flatMap_cons, List.length_append, recLines, List.length_cons]
    omega

/-- The record area `run` starts with (`init_dalytran`: spaces and zeros). -/
def dal0R : cbtrn01c.DalytranRecord :=
  { dalytran_id := Array.repeat 16#usize 32#u8, dalytran_type_cd := Array.repeat 2#usize 32#u8,
    dalytran_cat_cd := 0#i64, dalytran_source := Array.repeat 10#usize 32#u8,
    dalytran_desc := Array.repeat 100#usize 32#u8, dalytran_amt := 0#i64,
    dalytran_merchant_id := 0#i64, dalytran_merchant_name := Array.repeat 50#usize 32#u8,
    dalytran_merchant_city := Array.repeat 50#usize 32#u8,
    dalytran_merchant_zip := Array.repeat 10#usize 32#u8,
    dalytran_card_num := Array.repeat 16#usize 32#u8,
    dalytran_orig_ts := Array.repeat 26#usize 32#u8,
    dalytran_proc_ts := Array.repeat 26#usize 32#u8, filler1 := Array.repeat 20#usize 32#u8 }

theorem init_dalytran_eq : cbtrn01c.init_dalytran = .ok dal0R := rfl

/-- A `usize` has at least 32 bits. -/
theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega

/-- Small lengths fit in a `usize` (the side conditions of the helpers, by `simp`). -/
theorem small_lt_usize_max {n : Nat} (h : n < 4294967295) : n < Usize.max :=
  Nat.lt_of_lt_of_le h usize_max_ge

/-- The account key `run` computes from a cross-reference's account id:
`(|id| % 100_000_000_000) as i64`. -/
def akeyOf (x : I64) : I64 :=
  UScalar.hcast IScalarTy.I64 (⟨BitVec.ofNat 64 (x.val.natAbs % 100000000000)⟩ : U64)

theorem akeyU_val (x : I64) :
    (⟨BitVec.ofNat 64 (x.val.natAbs % 100000000000)⟩ : U64).val =
      x.val.natAbs % 100000000000 := by
  have h1 := Nat.mod_lt x.val.natAbs (show 100000000000 > 0 by norm_num)
  show (BitVec.ofNat 64 (x.val.natAbs % 100000000000)).toNat = _
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem akeyOf_val (x : I64) :
    (akeyOf x).val = ((x.val.natAbs % 100000000000 : Nat) : Int) := by
  have h1 := Nat.mod_lt x.val.natAbs (show 100000000000 > 0 by norm_num)
  rw [akeyOf, UScalar.hcast_val_eq, akeyU_val]
  simp only [IScalarTy.I64_numBits_eq]
  exact Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)

/-- The key computation of 3000-READ-ACCOUNT in `run` (`abs_u64`, `% 100_000_000_000`, the cast
to `i64`), in one step. -/
theorem akey_eq {α : Type} (x : I64) (f : I64 → Result α) :
    (do
      let i1 ← cbtrn01c.abs_u64 x
      let i2 ← i1 % 100000000000#u64
      let akey ← lift (UScalar.hcast .I64 i2)
      f akey) = f (akeyOf x) := by
  rw [abs_u64_eq]
  have h : absU x % 100000000000#u64 =
      Result.ok (⟨BitVec.ofNat 64 (x.val.natAbs % 100000000000)⟩ : U64) := by
    refine eq_ok_of_wp ?_
    aeneas_wp []
    have h1 := Nat.mod_lt x.val.natAbs (show 100000000000 > 0 by norm_num)
    simp only [Nat.reduceEqDiff, not_false_eq_true, _root_.ite_true, Except.ok.injEq]
    apply UScalar.eq_of_val_eq
    rw [UScalar.ofNatCore_val_eq, absU_val, akeyU_val]
  simp only [bind_ok, h, lift, akeyOf]

/-- Symbolic execution with the value forms of the kit and the helpers above. -/
syntax "trn01c_wp" " [" Lean.Parser.Tactic.simpArg,* "]" : tactic

macro_rules
  | `(tactic| trn01c_wp [$args,*]) => do
    let args : SimpArgs := args.getElems
    `(tactic| aeneas_wp [slice_to_vec_U8, Array.to_slice, Array.make_val, Array.repeat_val,
      Array.from_val, array_index_usize_eq, uscalar_ofNat_val, iscalar_ofInt_val,
      not_true_eq_false, not_false_eq_true, Nat.reduceEqDiff, Nat.reduceAdd, Bool.false_eq_true,
      Bool.true_eq_false, Int.reduceEq, Int.reduceNeg, List.length_append, List.length_cons,
      List.length_nil, Array.length_eq, zeroPad_length, dalLine_length, small_lt_usize_max,
      push_bytes_eq, push_unsigned_eq, dalytran_bytes_eq, abs_u64_eq, absU_val, $args,*])

/-! ## The read loop, and `run` -/

/-- The invariant of the read loop (state: lines, record area, cross-reference and account areas,
end-of-file flag, position, end of file seen): while the flag is `'N'`, the start line and the
lines of the records read so far, the last of them in the record area; once it is `'Y'`, also the
lookups once more for the last record (or the initial record area). -/
def loopInv (L : List cbtrn01c.DalytranRecord) (xs : List cbtrn01c.CardXrefRecord)
    (accs : List cbtrn01c.AccountRecord) :
    alloc.vec.Vec (alloc.vec.Vec U8) × cbtrn01c.DalytranRecord × cbtrn01c.CardXrefRecord ×
      cbtrn01c.AccountRecord × U8 × Usize × Bool → Prop
  | (v, dal, _, _, ef, pos, eh) =>
    (ef = 78#u8 ∧ eh = false ∧ pos.val ≤ L.length ∧
      v.val.map (·.val) = startL :: (L.take pos.val).flatMap (recLines xs accs) ∧
      dal = (L.take pos.val).getLast?.getD dal0R) ∨
    (ef = 89#u8 ∧ v.val.map (·.val) =
      startL :: L.flatMap (recLines xs accs) ++ lookupLines xs accs (L.getLast?.getD dal0R))

/-- The variant of the read loop. -/
def loopVar (L : List cbtrn01c.DalytranRecord) :
    alloc.vec.Vec (alloc.vec.Vec U8) × cbtrn01c.DalytranRecord × cbtrn01c.CardXrefRecord ×
      cbtrn01c.AccountRecord × U8 × Usize × Bool → Nat
  | (_, _, _, _, ef, pos, _) => L.length - pos.val + (if ef = 89#u8 then 0 else 1)

set_option maxHeartbeats 4000000 in
/-- **The read loop**, in bytes. -/
theorem run_loop0_spec (s1 : Slice cbtrn01c.DalytranRecord) (s3 : Slice cbtrn01c.CardXrefRecord)
    (s5 : Slice cbtrn01c.AccountRecord) (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (xref : cbtrn01c.CardXrefRecord) (acct : cbtrn01c.AccountRecord)
    (hv : v.val.map (·.val) = [startL]) (hL : s1.val.length < 2 ^ 28) :
    wp (cbtrn01c.run_loop0 s1 s3 s5 v dal0R xref acct 78#u8 0#usize false)
      (fun o => ∃ w, o = .ok (w, false) ∧ w.val.map (·.val) =
        startL :: s1.val.flatMap (recLines s3.val s5.val) ++
          lookupLines s3.val s5.val (s1.val.getLast?.getD dal0R) ++ [endL]) := by
  have hU := usize_max_ge
  unfold cbtrn01c.run_loop0
  refine wp_loop (loop_shape _) (loopInv s1.val s3.val s5.val) (loopVar s1.val) ?_ _ ?_
  · rintro ⟨v, dal, xref, acct, ef, pos, eh⟩ hinv
    simp only [loopInv] at hinv
    rcases hinv with ⟨rfl, rfl, hpos, hv, hdal⟩ | ⟨rfl, hv⟩
    · have hvl : v.val.length ≤ 1 + 7 * pos.val := by
        have e := congrArg List.length hv
        have := recLines_length_le s3.val s5.val (s1.val.take pos.val)
        simp only [List.length_map, List.length_cons, List.length_take] at e this
        omega
      by_cases hp : pos.val < s1.val.length
      · have hlast : (s1.val.take (pos.val + 1)).getLast?.getD dal0R = s1.val[pos.val] := by
          rw [take_succ_of_lt hp, List.getLast?_append_of_ne_nil _ (by simp)]
          simp
        rcases hx : s3.val.find? (fun x => decide (x.xref_card_num.val =
          (s1.val[pos.val]'hp).dalytran_card_num.val)) with _ | x
        · simp only [cbtrn01c.run_loop0.body]
          trn01c_wp [hp, run_loop0_loop0_eq, run_loop0_loop1_eq, hx]
          simp (disch := omega) only [dite_eq_left]
          simp only [loopCls_cont, loopInv, loopVar]
          refine ⟨Or.inl ⟨by simp, by simp, by simp only [UScalar.ofNatCore_val_eq]; omega, ?_,
            ?_⟩, by simp only [UScalar.ofNatCore_val_eq]; simp; omega⟩
          · simp only [UScalar.ofNatCore_val_eq, take_succ_of_lt hp, List.flatMap_append,
              List.flatMap_cons, List.flatMap_nil, List.append_nil, recLines]
            simp only [List.map_append, hv, alloc.vec.Vec.from_val, List.map_cons, List.map_nil,
              lookupLines, hx, invCardL, cardL, skipL, List.nil_append, List.append_assoc,
              List.cons_append]
          · simp only [UScalar.ofNatCore_val_eq, hlast]
        · simp only [cbtrn01c.run_loop0.body, akey_eq]
          rcases ha : s5.val.find? (fun a => decide (a.acct_id.val =
            ((x.xref_acct_id.val.natAbs % 100000000000 : Nat) : Int))) with _ | a
          all_goals
            trn01c_wp [hp, run_loop0_loop0_eq, run_loop0_loop1_eq, hx, ha, akeyOf_val,
              Int.natAbs_natCast]
            simp (disch := omega) only [dite_eq_left]
            simp only [loopCls_cont, loopInv, loopVar]
            refine ⟨Or.inl ⟨by simp, by simp, by simp only [UScalar.ofNatCore_val_eq]; omega, ?_,
              ?_⟩, by simp only [UScalar.ofNatCore_val_eq]; simp; omega⟩
            · simp only [UScalar.ofNatCore_val_eq, take_succ_of_lt hp, List.flatMap_append,
                List.flatMap_cons, List.flatMap_nil, List.append_nil, recLines]
              simp only [List.map_append, hv, alloc.vec.Vec.from_val, List.map_cons, List.map_nil,
                lookupLines, hx, ha, okXrefL, cardNumL, acctIdL, custIdL, invAcctL, acctL,
                notFoundL, okAcctL, List.nil_append, List.append_assoc, List.cons_append]
            · simp only [UScalar.ofNatCore_val_eq, hlast]
      · have hpe : pos.val = s1.val.length := by omega
        rcases hx : s3.val.find? (fun x => decide (x.xref_card_num.val =
          dal.dalytran_card_num.val)) with _ | x
        · simp only [cbtrn01c.run_loop0.body]
          trn01c_wp [hp, run_loop0_loop2_eq, hx]
          simp (disch := omega) only [dite_eq_left]
          simp only [loopCls_cont, loopInv, loopVar]
          refine ⟨Or.inr ⟨by simp, ?_⟩, by simp⟩
          rw [hpe, List.take_length] at hv hdal
          simp only [List.map_append, hv, alloc.vec.Vec.from_val, List.map_cons, List.map_nil,
            ← hdal, lookupLines, hx, invCardL, cardL, skipL, List.nil_append, List.append_assoc,
            List.cons_append]
        · simp only [cbtrn01c.run_loop0.body, akey_eq]
          rcases ha : s5.val.find? (fun a => decide (a.acct_id.val =
            ((x.xref_acct_id.val.natAbs % 100000000000 : Nat) : Int))) with _ | a
          all_goals
            trn01c_wp [hp, run_loop0_loop2_eq, run_loop0_loop3_eq, hx, ha, akeyOf_val,
              Int.natAbs_natCast]
            simp (disch := omega) only [dite_eq_left]
            simp only [loopCls_cont, loopInv, loopVar]
            refine ⟨Or.inr ⟨by simp, ?_⟩, by simp⟩
            rw [hpe, List.take_length] at hv hdal
            simp only [List.map_append, hv, alloc.vec.Vec.from_val, List.map_cons, List.map_nil,
              ← hdal, lookupLines, hx, ha, okXrefL, cardNumL, acctIdL, custIdL, invAcctL, acctL,
              notFoundL, okAcctL, List.nil_append, List.append_assoc, List.cons_append]
    · have hvl : v.val.length ≤ 7 * s1.val.length + 7 := by
        have e := congrArg List.length hv
        have := recLines_length_le s3.val s5.val s1.val
        have := lookupLines_length_le s3.val s5.val (s1.val.getLast?.getD dal0R)
        simp only [List.length_map, List.length_cons, List.length_append] at e
        omega
      simp only [cbtrn01c.run_loop0.body]
      aeneas_wp [slice_to_vec_U8, Array.to_slice, Array.make_val, not_true_eq_false,
        not_false_eq_true, Nat.reduceEqDiff]
      simp (disch := omega) only [dite_eq_left]
      simp only [loopCls_done]
      refine ⟨_, rfl, ?_⟩
      simp only [List.map_append, List.map_cons, List.map_nil, hv, alloc.vec.Vec.from_val, endL,
        List.cons_append, List.append_assoc]
  · simp only [loopInv]
    left
    refine ⟨trivial, trivial, by simp, ?_, by simp⟩
    simp [hv]

/-- **`run`, in bytes**: the start line, each record's lines, the lookups once more for the last
record (or the initial record area), the end line; no abend. -/
theorem run_eq (s1 : Slice cbtrn01c.DalytranRecord) (s2 : Slice cbtrn01c.FdCustfileRec)
    (s3 : Slice cbtrn01c.CardXrefRecord) (s4 : Slice cbtrn01c.FdCardfileRec)
    (s5 : Slice cbtrn01c.AccountRecord) (s6 : Slice cbtrn01c.FdTranfileRec)
    (hL : s1.val.length < 2 ^ 28) :
    ∃ out, cbtrn01c.run s1 s2 s3 s4 s5 s6 = .ok out ∧
      out.displays.val.map (·.val) = startL :: s1.val.flatMap (recLines s3.val s5.val) ++
        lookupLines s3.val s5.val (s1.val.getLast?.getD dal0R) ++ [endL] ∧
      out.abended = false := by
  refine exists_ok_of_wp ?_
  simp only [cbtrn01c.run, init_dalytran_eq]
  trn01c_wp [cbtrn01c.init_xref, cbtrn01c.init_account]
  refine wp_mono (run_loop0_spec s1 s3 s5 _ _ _ ?_ hL) ?_
  · simp [startL]
  · rintro _ ⟨w, rfl, hw⟩
    trn01c_wp [wp_ok]
    exact ⟨_, rfl, hw, rfl⟩

/-! ## Glue: the lines of `run` are those of `Model.displayText` -/

theorem startL_text :
    startL.map UScalar.val = Model.txt "START OF EXECUTION OF PROGRAM CBTRN01C" := by
  decide +kernel

theorem endL_text : endL.map UScalar.val = Model.txt "END OF EXECUTION OF PROGRAM CBTRN01C" := by
  decide +kernel

/-- A record's line is its text (`Schema.textS` of its field values). -/
theorem dalLine_text (r : cbtrn01c.DalytranRecord) :
    (dalLine r).map UScalar.val = DalytranRecord.textS (DalytranRecord.vals r) := by
  simp only [dalLine, List.map_append, zeroPad_val, Schema.textS, DalytranRecord.vals,
    List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, fieldTextS, latin1_text, List.append_nil, List.append_assoc, overByte_val,
    Bool.false_eq_true, _root_.ite_false, _root_.ite_true, Nat.reduceSub]

/-- The initial record area holds the field values `Model.dal0`. -/
theorem dal0R_vals : DalytranRecord.vals dal0R = Model.dal0 := by
  decide +kernel

/-- The EBCDIC bytes of an alphanumeric field determine its Latin-1 bytes. -/
theorem ebcdic_map_beq (l1 l2 : List U8) :
    (l1.map (fun u => ebcdicOfLatin1 u.val) == l2.map (fun u => ebcdicOfLatin1 u.val)) =
      decide (l1 = l2) := by
  have inj : ∀ u w : U8, ebcdicOfLatin1 u.val = ebcdicOfLatin1 w.val → u = w := by
    intro u w h
    have hu := cp037_roundtrip ⟨u.val, by have := u.hBounds; simpa using this⟩
    have hw := cp037_roundtrip ⟨w.val, by have := w.hBounds; simpa using this⟩
    simp only at hu hw
    apply UScalar.eq_of_val_eq
    rw [← hu, ← hw, h]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    exact List.map_injective_iff.mpr (fun u w huw => inj u w huw) h
  · rintro rfl
    rfl

/-- The account id of a valid cross-reference record (`PIC 9(11)`). -/
theorem xref_acct_range (x : cbtrn01c.CardXrefRecord)
    (hv : CardXrefRecord.Valid (CardXrefRecord.vals x)) :
    0 ≤ x.xref_acct_id.val ∧ x.xref_acct_id.val < 100000000000 := by
  simp only [Schema.Valid, CardXrefRecord.vals] at hv
  rcases hv with _ | ⟨-, _ | ⟨-, _ | ⟨h2, -⟩⟩⟩
  obtain ⟨fmt, hk, -, -, hh, -⟩ := h2
  cases hk
  simp only [NumFmt.Holds, NumFmt.fullBinary, Bool.false_eq_true, _root_.ite_false,
    true_implies, Nat.reducePow] at hh
  omega

/-- The literals are the texts of `Model.lookupText`. -/
theorem lit_texts :
    invCardL.map UScalar.val = Model.txt "INVALID CARD NUMBER FOR XREF" ∧
    cardL.map UScalar.val = Model.txt "CARD NUMBER " ∧
    skipL.map UScalar.val = Model.txt " COULD NOT BE VERIFIED. SKIPPING TRANSACTION ID-" ∧
    okXrefL.map UScalar.val = Model.txt "SUCCESSFUL READ OF XREF" ∧
    cardNumL.map UScalar.val = Model.txt "CARD NUMBER: " ∧
    acctIdL.map UScalar.val = Model.txt "ACCOUNT ID : " ∧
    custIdL.map UScalar.val = Model.txt "CUSTOMER ID: " ∧
    invAcctL.map UScalar.val = Model.txt "INVALID ACCOUNT NUMBER FOUND" ∧
    acctL.map UScalar.val = Model.txt "ACCOUNT " ∧
    notFoundL.map UScalar.val = Model.txt " NOT FOUND" ∧
    okAcctL.map UScalar.val = Model.txt "SUCCESSFUL READ OF ACCOUNT FILE" := by
  decide +kernel

/-- **What the lookups display is `Model.lookupText`** (for valid cross-reference records). -/
theorem lookupLines_text (xs : List cbtrn01c.CardXrefRecord)
    (accs : List cbtrn01c.AccountRecord) (d : cbtrn01c.DalytranRecord)
    (hxs : ∀ x ∈ xs, CardXrefRecord.Valid (CardXrefRecord.vals x)) :
    (lookupLines xs accs d).map (List.map UScalar.val) =
      Model.lookupText (xs.map CardXrefRecord.vals) (accs.map AccountRecord.vals)
        (DalytranRecord.vals d) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11⟩ := lit_texts
  have hpx : (fun x => Model.strOf (x.getD 0 default) ==
      Model.strOf ((DalytranRecord.vals d).getD 10 default)) ∘ CardXrefRecord.vals =
      fun x => decide (x.xref_card_num.val = d.dalytran_card_num.val) := by
    funext x
    simp only [Function.comp_apply, CardXrefRecord.vals, DalytranRecord.vals,
      List.getD_cons_zero, List.getD_cons_succ, Model.strOf]
    exact ebcdic_map_beq _ _
  unfold lookupLines Model.lookupText
  rw [List.find?_map, hpx]
  rcases hx : xs.find? (fun x => decide (x.xref_card_num.val = d.dalytran_card_num.val))
    with _ | x
  · simp only [hx, Option.map_none, List.map_cons, List.map_nil, List.map_append, t1, t2, t3,
      DalytranRecord.vals, List.getD_cons_zero, List.getD_cons_succ, Model.strOf, latin1_text]
  · have hr := xref_acct_range x (hxs x (List.mem_of_find?_eq_some hx))
    have hpa : (fun a => Model.numOf (a.getD 0 default) ==
        Model.numOf ((CardXrefRecord.vals x).getD 2 default)) ∘ AccountRecord.vals =
        fun a => decide (a.acct_id.val =
          ((x.xref_acct_id.val.natAbs % 100000000000 : Nat) : Int)) := by
      funext a
      simp only [Function.comp_apply, CardXrefRecord.vals, AccountRecord.vals,
        List.getD_cons_zero, List.getD_cons_succ, Model.numOf]
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
      omega
    simp only [hx, Option.map_some, List.find?_map, hpa]
    have hm : x.xref_acct_id.val.natAbs % 100000000000 = x.xref_acct_id.val.natAbs := by omega
    rcases ha : accs.find? (fun a => decide (a.acct_id.val =
      ((x.xref_acct_id.val.natAbs % 100000000000 : Nat) : Int))) with _ | a
    · simp only [ha, Option.map_none]
      simp only [List.map_cons, List.map_nil, List.map_append,
        t4, t5, t6, t7, t8, t9, t10, hm, zeroPad_val, CardXrefRecord.vals, List.getD_cons_zero,
        List.getD_cons_succ, Model.strOf, Model.numOf, latin1_text, List.cons_append,
        List.nil_append]
    · simp only [ha, Option.map_some]
      simp only [List.map_cons, List.map_nil, List.map_append, t4, t5, t6, t7,
        t11, zeroPad_val, CardXrefRecord.vals, List.getD_cons_zero, List.getD_cons_succ,
        Model.strOf, Model.numOf, latin1_text, List.cons_append, List.nil_append]

/-- **The equation of `run`** (`RunSpec` of `RustProof.lean`). -/
theorem run_spec : RunSpec := by
  intro s1 s2 s3 s4 s5 s6 vals1 vals3 vals5 h1 h3 h5 hv1 hv3 hv5 hn1 hn3 hn5
  have hL : s1.val.length < 2 ^ 28 := by rw [← h1, List.length_map] at hn1; exact hn1
  obtain ⟨out, hrun, hd, ha⟩ := run_eq s1 s2 s3 s4 s5 s6 hL
  refine ⟨out, hrun, ?_, ha⟩
  have hxs : ∀ x ∈ s3.val, CardXrefRecord.Valid (CardXrefRecord.vals x) := fun x hx =>
    hv3 _ (h3 ▸ List.mem_map_of_mem hx)
  have e := congrArg (List.map (List.map UScalar.val)) hd
  simp only [List.map_map] at e
  rw [show (List.map UScalar.val ∘ fun x : alloc.vec.Vec U8 => x.val) =
    (fun l => l.val.map UScalar.val) from rfl] at e
  rw [e, ← h1, ← h3, ← h5]
  simp only [Model.displayText, List.map_append, List.map_cons, List.map_nil, startL_text,
    endL_text, List.flatMap_map, List.map_flatMap, List.getLast?_map]
  have hlk : ∀ d, (lookupLines s3.val s5.val d).map (List.map UScalar.val) =
      Model.lookupText (s3.val.map CardXrefRecord.vals) (s5.val.map AccountRecord.vals)
        (DalytranRecord.vals d) := fun d => lookupLines_text _ _ d hxs
  rw [← dalytranRecord_eq]
  simp only [recLines, List.map_cons, dalLine_text, hlk]
  cases h : s1.val.getLast? with
  | none => simp only [Option.getD_none, Option.map_none, dal0R_vals, List.cons_append,
      List.append_assoc]
  | some r => simp only [Option.getD_some, Option.map_some, List.cons_append, List.append_assoc]

/-- **CBTRN01C → Rust, every input.** -/
theorem rust : Statement := statement_of_run run_spec

end EquivLean.Modernize.Cbtrn01c.Rust

#print axioms EquivLean.Modernize.Cbtrn01c.Rust.run_spec
#print axioms EquivLean.Modernize.Cbtrn01c.Rust.rust

import EquivLean.Bridge.Aeneas.Digits
import EquivLean.Demo.Gen.Aeneas.ModCbact01c.Funs

/-!
# CBACT01C → Rust: the helpers of `run`

The translation is veriforch's guided v3 (`examples/rust/mod_cbact01c`,
`Demo/Gen/Aeneas/ModCbact01c`).  Value equations for the helpers `run` calls:
* `push_bytes`, `lit`, `push_first4`, `labeled_num`, `labeled_x` by `aeneas_spec`;
* `push_zoned`: the digit loop (a `[u8; 20]` buffer filled from position `digits` down) by hand
  (`push_zoned_loop0_spec`), then the overpunched last digit of a signed item: `zonedText`;
* the date conversion of a record (`set_inp_date`, the two types, `COBDATFT` in mode 2,
  `get_out_date`) as one equation, `codate_bind`: the output date is the characters 1-4, 6-7,
  9-10 of the reissue date followed by bytes 30-31 of the conversion area, which no record
  writes.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Rust
open cbact01c

theorem push_bytes_eq (dst : alloc.vec.Vec U8) (src : Slice U8)
    (h : dst.val.length + src.val.length < Usize.max) :
    push_bytes dst src = .ok (alloc.vec.Vec.from (dst.val ++ src.val) (by simp; omega)) := by
  aeneas_spec [push_bytes, push_bytes_loop]

theorem lit_eq (s : Slice U8) (h : s.val.length < Usize.max) :
    lit s = .ok (alloc.vec.Vec.from s.val (by omega)) := by
  aeneas_spec [lit] with [push_bytes_eq]

theorem push_first4_eq (out : alloc.vec.Vec U8) (s : Array U8 10#usize)
    (h : out.val.length + 4 < Usize.max) :
    push_first4 out s = .ok (alloc.vec.Vec.from (out.val ++ s.val.take 4)
      (by have := s.property; simp; omega)) := by
  aeneas_spec [push_first4, push_first4_loop]
    using (fun (p : alloc.vec.Vec U8 × Usize) => p.2.val ≤ 4 ∧ p.1.val = out.val ++ s.val.take p.2.val)
      (fun (p : alloc.vec.Vec U8 × Usize) => 4 - p.2.val)

theorem magnitude_eq (v : I64) : ∃ m, magnitude v = .ok m ∧ m.val = v.val.natAbs := by
  unfold magnitude
  have hb := v.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hb
  by_cases hv : v.val < 0
  · have hlt : (v < 0#i64) = True := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_true]
    refine exists_ok_of_wp ?_
    aeneas_wp [IScalar.hcast_val_eq]
    have hb' : -9223372036854775808 ≤ v.val ∧ v.val < 9223372036854775808 := by
      simpa using hb
    have e1 : -9223372036854775808 ≤ v.val + 1 ∧ v.val + 1 ≤ 9223372036854775807 := by omega
    have e2 : -9223372036854775808 ≤ -(v.val + 1) ∧ -(v.val + 1) ≤ 9223372036854775807 := by
      omega
    have e3 : (-(v.val + 1) % 2 ^ 64).toNat = (-(v.val + 1)).toNat := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
    have e4 : (-(v.val + 1) % 2 ^ 64).toNat ≤ 18446744073709551614 := by rw [e3]; omega
    rw [dite_eq_left_of_eq_true (eq_true e1), dite_eq_left_of_eq_true (eq_true e2),
      dite_eq_left_of_eq_true (eq_true e4)]
    refine ⟨_, rfl, ?_⟩
    rw [UScalar.ofNatCore_val_eq, e3]
    omega
  · have hlt : (v < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_false]
    refine ⟨_, rfl, ?_⟩
    rw [IScalar.hcast_val_eq]
    simp only [UScalarTy.U64_numBits_eq]
    omega

theorem overpunch_eq (d : U8) (neg : Bool) (hd : d.val < 10) :
    ∃ r, cbact01c.overpunch d neg = .ok r ∧ r.val = EquivLean.Cobol.Rec.overpunch neg d.val := by
  unfold cbact01c.overpunch
  refine exists_ok_of_wp ?_
  by_cases h0 : d.val = 0
  · have hz : d = 0#u8 := UScalar.eq_of_val_eq (by simp [h0])
    cases neg <;> simp [hz, EquivLean.Cobol.Rec.overpunch]
  · have hz : ¬ d = 0#u8 := fun h => h0 (by simp [h])
    cases neg
    · simp only [hz, Bool.false_eq_true, _root_.ite_false]
      aeneas_wp
      simp only [show 65 + d.val ≤ 255 by omega, show 1 ≤ 65 + d.val by omega,
        _root_.dite_true, _root_.ite_true]
      exact ⟨_, rfl, by rw [UScalar.ofNatCore_val_eq]; simp [EquivLean.Cobol.Rec.overpunch, h0]⟩
    · simp only [hz, _root_.ite_true, _root_.ite_false]
      aeneas_wp
      simp only [show 74 + d.val ≤ 255 by omega, show 1 ≤ 74 + d.val by omega,
        _root_.dite_true, _root_.ite_true]
      exact ⟨_, rfl, by rw [UScalar.ofNatCore_val_eq]; simp [EquivLean.Cobol.Rec.overpunch, h0]⟩

theorem overpunch_lt (neg : Bool) (d : Nat) (hd : d < 10) :
    EquivLean.Cobol.Rec.overpunch neg d < 256 := by
  unfold EquivLean.Cobol.Rec.overpunch; split_ifs <;> omega

theorem overpunch_eq' (d : U8) (neg : Bool) (hd : d.val < 10) :
    cbact01c.overpunch d neg = .ok (byteOf (EquivLean.Cobol.Rec.overpunch neg d.val)) := by
  obtain ⟨r, hr, hv⟩ := overpunch_eq d neg hd
  rw [hr]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hv, byteOf_val _ (overpunch_lt _ _ hd)]

set_option maxHeartbeats 2000000 in
/-- The digit loop of `push_zoned` (from position `digits` down): the `digits` low digits of `x`
in the first `digits` bytes of the buffer. -/
theorem push_zoned_loop0_spec (digits : Usize) (x : Nat) (m : U64) (hd : digits.val ≤ 20)
    (hm : m.val = x) :
    wp (push_zoned_loop0 m (Array.repeat 20#usize 48#u8) digits)
      (fun o => ∃ b, o = .ok b ∧
        b.val = zeroPad digits.val x ++ List.replicate (20 - digits.val) 48#u8) := by
  simp only [push_zoned_loop0]
  refine wp_loop (loop_shape _) (fun s => s.2.2.val ≤ digits.val ∧
      s.1.val = x / 10 ^ (digits.val - s.2.2.val) ∧
      s.2.1.val = List.replicate s.2.2.val 48#u8 ++ zeroPad (digits.val - s.2.2.val) x ++
        List.replicate (20 - digits.val) 48#u8)
    (fun s => s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro w buf i hinv
    obtain ⟨hi, hw, hbuf⟩ := hinv
    have hlen : buf.val.length = 20 := buf.property
    aeneas_wp [rust_loop_body, array_update_eq, UScalar.cast_val_eq, Array.from_val, hlen]
    by_cases h1 : 0 < i.val
    · have hd10 : w.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have h256 : w.val % 10 % 2 ^ 8 = w.val % 10 := Nat.mod_eq_of_lt (by omega)
      obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by omega⟩
      simp only [h1, _root_.ite_true, h256, show 1 ≤ i.val by omega, show ¬ (10 = 0) by norm_num,
        not_false_eq_true, show 48 + w.val % 10 ≤ 255 by omega, _root_.dite_true,
        show i.val - 1 < 20 by omega, loopCls_cont]
      refine ⟨⟨by simp only [UScalar.ofNatCore_val_eq]; omega, ?_, ?_⟩, by
        simp only [UScalar.ofNatCore_val_eq]; omega⟩
      · rw [UScalar.ofNatCore_val_eq, UScalar.ofNatCore_val_eq, hw, Nat.div_div_eq_div_mul,
          ← Nat.pow_succ]
        congr 2
        omega
      · simp only [Array.from_val, hbuf, UScalar.ofNatCore_val_eq]
        rw [hk, show k + 1 - 1 = k by omega, List.append_assoc, set_replicate_end,
          show digits.val - k = (digits.val - (k + 1)) + 1 by omega, zeroPad_succ_left]
        simp only [List.append_assoc, List.singleton_append, List.append_cancel_left_eq]
        rw [List.cons_append]
        congr 1
        apply UScalar.eq_of_val_eq
        rw [UScalar.ofNatCore_val_eq, byteOf_val _ (by omega), hw, hk]
    · simp only [h1, _root_.ite_false, loopCls_done]
      refine ⟨buf, rfl, ?_⟩
      rw [hbuf, show i.val = 0 by omega]
      simp
  · refine ⟨le_refl _, by simp [hm], ?_⟩
    simp only [Array.repeat_val, uscalar_ofNat_val, Nat.sub_self]
    have z : zeroPad 0 x = [] := by simp [zeroPad, zpad, Cobol.Digits.toDigits]
    rw [z, List.append_nil, ← List.replicate_add]
    congr 1
    omega

/-- The copy loop of `push_zoned`: the first `digits` bytes of the buffer. -/
theorem push_zoned_loop1_eq (out : alloc.vec.Vec U8) (digits : Usize) (buf : Array U8 20#usize)
    (hd : digits.val ≤ 20) (h : out.val.length + digits.val < Usize.max) :
    push_zoned_loop1 out digits buf 0#usize =
      .ok (alloc.vec.Vec.from (out.val ++ buf.val.take digits.val) (by simp; omega)) := by
  aeneas_spec [push_zoned_loop1]

theorem zeroPad_succ_right (n x : Nat) :
    zeroPad (n + 1) x = zeroPad n (x / 10) ++ [byteOf (48 + x % 10)] := by
  simp [zeroPad, zpad, EquivLean.Cobol.Rec.toDigits_succ]

/-- The zoned text `push_zoned` appends (Latin-1 bytes): the `digits` low digits of `|v|`, the
last one overpunched when `signed`. -/
def zonedText (v : Int) (digits : Nat) (signed : Bool) : List U8 :=
  if signed then
    zeroPad (digits - 1) (v.natAbs / 10) ++
      [byteOf (EquivLean.Cobol.Rec.overpunch (decide (v < 0)) (v.natAbs % 10))]
  else zeroPad digits v.natAbs

theorem zonedText_length (v : Int) (digits : Nat) (signed : Bool) (hd : 0 < digits) :
    (zonedText v digits signed).length = digits := by
  unfold zonedText
  split <;> simp [zeroPad_length]; omega

set_option maxHeartbeats 2000000 in
/-- `push_zoned`: the zoned text of `v` after `out` (`0 < digits ≤ 20`). -/
theorem push_zoned_eq (out : alloc.vec.Vec U8) (v : I64) (digits : Usize) (signed : Bool)
    (hd0 : 0 < digits.val) (hd : digits.val ≤ 20) (h : out.val.length + digits.val < Usize.max) :
    push_zoned out v digits signed =
      .ok (alloc.vec.Vec.from (out.val ++ zonedText v.val digits.val signed)
        (by simp [zonedText_length _ _ _ hd0]; omega)) := by
  refine eq_ok_of_wp ?_
  unfold push_zoned
  obtain ⟨m, hm, hmv⟩ := magnitude_eq v
  rw [hm, wp_bind, wp_ok]
  dsimp only
  rw [wp_bind]
  refine wp_mono (push_zoned_loop0_spec digits v.val.natAbs m hd hmv) ?_
  rintro _ ⟨b, rfl, hb⟩
  obtain ⟨n, hn⟩ : ∃ n, digits.val = n + 1 := ⟨digits.val - 1, by omega⟩
  have hblen : b.val.length = 20 := b.property
  cases signed
  · simp only [Bool.false_eq_true, _root_.ite_false, wp_bind, wp_ok]
    rw [push_zoned_loop1_eq out digits b hd h]
    simp only [wp_ok, Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hb, zonedText,
      Bool.false_eq_true, _root_.ite_false]
    rw [List.take_append_of_le_length (by simp [zeroPad_length]),
      List.take_of_length_le (by simp [zeroPad_length])]
  · simp only [_root_.ite_true]
    have hb' : b.val = zeroPad n (v.val.natAbs / 10) ++ [byteOf (48 + v.val.natAbs % 10)] ++
        List.replicate (20 - digits.val) 48#u8 := by rw [hb, hn, zeroPad_succ_right]
    have hdig : digits.val - 1 = n := by omega
    have hn20 : n < 20 := by omega
    have hzl : (zeroPad n (v.val.natAbs / 10)).length = n := zeroPad_length _ _
    have hbn : b.val[n]'(by omega) = byteOf (48 + v.val.natAbs % 10) := by
      simp only [hb', List.append_assoc]
      rw [List.getElem_append_right (by omega)]
      simp [hzl]
    have hd10 : v.val.natAbs % 10 < 10 := Nat.mod_lt _ (by norm_num)
    have hbyte : (byteOf (48 + v.val.natAbs % 10)).val = 48 + v.val.natAbs % 10 :=
      byteOf_val _ (by omega)
    aeneas_wp [array_update_eq, Array.from_val, hblen]
    simp only [hd0, _root_.ite_true, show 1 ≤ digits.val by omega, array_index_usize_eq,
      UScalar.ofNatCore_val_eq, hdig, hblen, hn20, _root_.dite_true, wp_ok]
    simp only [hbn, hbyte,
      show 48 ≤ 48 + v.val.natAbs % 10 by omega, _root_.ite_true]
    rw [overpunch_eq' _ _ (by rw [UScalar.ofNatCore_val_eq]; omega)]
    simp only [wp_ok, UScalar.ofNatCore_val_eq, 
      show 48 + v.val.natAbs % 10 - 48 = v.val.natAbs % 10 by omega]
    rw [push_zoned_loop1_eq out digits _ hd h]
    simp only [wp_ok, Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val,
      Array.from_val, zonedText, _root_.ite_true, hb', hdig, List.append_cancel_left_eq]
    rw [List.append_assoc, List.set_append_right _ _ (by omega), hzl, Nat.sub_self,
      List.singleton_append, List.set_cons_zero, hn, List.take_append,
      List.take_of_length_le (by omega), hzl, show n + 1 - n = 1 by omega]
    rfl

theorem labeled_num_eq (label : Slice U8) (v : I64) (digits : Usize) (signed : Bool)
    (hd0 : 0 < digits.val) (hd : digits.val ≤ 20)
    (h : label.val.length + digits.val < Usize.max) :
    labeled_num label v digits signed =
      .ok (alloc.vec.Vec.from (label.val ++ zonedText v.val digits.val signed)
        (by simp [zonedText_length _ _ _ hd0]; omega)) := by
  aeneas_spec [labeled_num] with [lit_eq, push_zoned_eq, zonedText_length]

theorem labeled_x_eq (label x : Slice U8) (h : label.val.length + x.val.length < Usize.max) :
    labeled_x label x = .ok (alloc.vec.Vec.from (label.val ++ x.val) (by simp; omega)) := by
  aeneas_spec [labeled_x] with [lit_eq, push_bytes_eq]

/-- One step of a copy to positions `1 + i` (`rec[1 + i] = src[i]`). -/
theorem set_offset_step {α : Type _} (c D : List α) (i : Nat) (x : α) (hi : i < D.length)
    (hc : 1 + i < c.length) (hx : D[i] = x) :
    (c.take 1 ++ D.take i ++ c.drop (1 + i)).set (1 + i) x =
      c.take 1 ++ D.take (i + 1) ++ c.drop (1 + (i + 1)) := by
  have hl : (c.take 1 ++ D.take i).length = 1 + i := by simp; omega
  rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self, set_drop_zero _ _ _ hc,
    take_succ_of_lt hi, hx]
  simp [List.append_assoc, show 1 + i + 1 = 1 + (i + 1) by omega]

/-- One step of a copy into a run of spaces (`r[j] = src[j]`). -/
theorem set_pad_step {α : Type _} (D : List α) (j n : Nat) (a x : α) (hj : j < D.length)
    (hn : j < n) (hx : D[j] = x) :
    (D.take j ++ List.replicate (n - j) a).set j x = D.take (j + 1) ++ List.replicate (n - (j + 1)) a := by
  have hl : (D.take j).length = j := by simp; omega
  rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self, set_replicate_zero _ _ _ (by omega),
    take_succ_of_lt hj, hx]
  simp [List.append_assoc, show n - j - 1 = n - (j + 1) by omega]

/-- `set_inp_date`: the date and ten spaces at positions 1 … 20. -/
theorem set_inp_date_eq (c : Array U8 80#usize) (d : Array U8 10#usize) :
    set_inp_date c d = .ok (Array.from (c.val.take 1 ++ (d.val ++ List.replicate 10 32#u8) ++
      c.val.drop 21) (by have := c.property; have := d.property; simp_all)) := by
  refine eq_ok_of_wp ?_
  simp only [set_inp_date, set_inp_date_loop]
  have hc : c.val.length = 80 := c.property
  have hd : d.val.length = 10 := d.property
  refine wp_loop (loop_shape _) (fun p => p.2.val ≤ 20 ∧
      p.1.val = c.val.take 1 ++ (d.val ++ List.replicate 10 32#u8).take p.2.val ++
        c.val.drop (1 + p.2.val))
    (fun p => 20 - p.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro r i hinv
    obtain ⟨hi, hr⟩ := hinv
    have hrl : r.val.length = 80 := r.property
    aeneas_wp [rust_loop_body, array_update_eq, array_index_usize_eq, Array.from_val, hrl, hd]
    have hD : (d.val ++ List.replicate 10 32#u8).length = 20 := by simp [hd]
    by_cases h1 : i.val < 20
    · have hs1 : 1 + i.val ≤ Usize.max := by scalar_tac
      have hs2 : i.val + 1 ≤ Usize.max := by scalar_tac
      by_cases h2 : i.val < 10
      · have hx : (d.val ++ List.replicate 10 32#u8)[i.val]'(by omega) = d.val[i.val]'(by omega) :=
          List.getElem_append_left _
        simp only [h1, h2, _root_.ite_true, _root_.dite_true, hs1, hs2,
          show 1 + i.val < 80 by omega, loopCls_cont]
        refine ⟨⟨by simp only [UScalar.ofNatCore_val_eq]; omega, ?_⟩, by
          simp only [UScalar.ofNatCore_val_eq]; omega⟩
        simp only [Array.from_val, UScalar.ofNatCore_val_eq, hr]
        exact set_offset_step _ _ _ _ (by omega) (by omega) hx
      · have hx : (d.val ++ List.replicate 10 32#u8)[i.val]'(by omega) = 32#u8 := by
          rw [List.getElem_append_right (by omega), List.getElem_replicate]
        simp only [h1, h2, _root_.ite_true, _root_.ite_false, _root_.dite_true, hs1, hs2,
          show 1 + i.val < 80 by omega, loopCls_cont]
        refine ⟨⟨by simp only [UScalar.ofNatCore_val_eq]; omega, ?_⟩, by
          simp only [UScalar.ofNatCore_val_eq]; omega⟩
        simp only [Array.from_val, UScalar.ofNatCore_val_eq, hr]
        exact set_offset_step _ _ _ _ (by omega) (by omega) hx
    · simp only [h1, _root_.ite_false, loopCls_done, Except.ok.injEq]
      apply Aeneas.Std.Array.ext
      rw [Array.from_val, hr, show i.val = 20 by omega,
        List.take_of_length_le (l := d.val ++ List.replicate 10 32#u8) (by omega)]
  · simp only [uscalar_ofNat_val, List.take_zero, List.append_nil, Nat.add_zero,
      List.take_append_drop]
    exact ⟨by omega, trivial⟩

/-- `get_out_date`: the ten bytes at positions 22 … 31. -/
theorem get_out_date_eq (c : Array U8 80#usize) :
    get_out_date c = .ok (Array.from ((c.val.drop 22).take 10)
      (by have := c.property; simp_all)) := by
  refine eq_ok_of_wp ?_
  simp only [get_out_date, get_out_date_loop]
  have hc : c.val.length = 80 := c.property
  refine wp_loop (loop_shape _) (fun p => p.2.val ≤ 10 ∧
      p.1.val = (c.val.drop 22).take p.2.val ++ List.replicate (10 - p.2.val) 32#u8)
    (fun p => 10 - p.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro r j hinv
    obtain ⟨hj, hr⟩ := hinv
    have hrl : r.val.length = 10 := r.property
    aeneas_wp [rust_loop_body, array_update_eq, array_index_usize_eq, Array.from_val, hrl, hc]
    by_cases h1 : j.val < 10
    · have hs1 : 22 + j.val ≤ Usize.max := by scalar_tac
      have hs2 : j.val + 1 ≤ Usize.max := by scalar_tac
      have hx : (c.val.drop 22)[j.val]'(by simp; omega) = c.val[22 + j.val]'(by omega) := by
        simp [List.getElem_drop]
      simp only [h1, _root_.ite_true, _root_.dite_true, hs1, hs2, show 22 + j.val < 80 by omega,
        loopCls_cont]
      refine ⟨⟨by simp only [UScalar.ofNatCore_val_eq]; omega, ?_⟩, by
        simp only [UScalar.ofNatCore_val_eq]; omega⟩
      simp only [Array.from_val, UScalar.ofNatCore_val_eq, hr]
      exact set_pad_step _ _ _ _ _ (by simp; omega) h1 hx
    · simp only [h1, _root_.ite_false, loopCls_done, Except.ok.injEq]
      apply Aeneas.Std.Array.ext
      rw [Array.from_val, hr, show j.val = 10 by omega]
      simp
  · simp [Array.repeat_val]

theorem list10 {α : Type _} (l : List α) (h : l.length = 10) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] := by
  refine ⟨l[0], l[1], l[2], l[3], l[4], l[5], l[6], l[7], l[8], l[9], ?_⟩
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  match i, h2 with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | n + 10, h => omega

theorem list9 {α : Type _} (l : List α) (h : l.length = 9) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8] := by
  refine ⟨l[0], l[1], l[2], l[3], l[4], l[5], l[6], l[7], l[8], ?_⟩
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [List.length_cons, List.length_nil] at h2
  match i, h2 with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | n + 9, h => omega

/-- The characters of a reissue date that `COBDATFT` keeps (type 2: `YYYY-MM-DD` ↦ `YYYYMMDD`). -/
def picks (d : List U8) : List U8 := d.take 4 ++ (d.drop 5).take 2 ++ (d.drop 8).take 2

/-- The conversion area after one record: types `2`, the date and ten spaces, the converted date
over the first eight bytes of the output date. -/
def codateNext (c d : List U8) : List U8 :=
  50#u8 :: (d ++ List.replicate 10 32#u8) ++ 50#u8 :: (picks d ++ c.drop 30)

theorem take_one_set {α : Type _} (l : List α) (x : α) (h : 0 < l.length) :
    (l.take 1).set 0 x = [x] := by
  cases l with
  | nil => simp at h
  | cons a l => simp


set_option maxHeartbeats 1000000 in
/-- `COBDATFT` with input and output type 2 (`YYYY-MM-DD` ↦ `YYYYMMDD`): the characters 1-4,
6-7 and 9-10 of the input date over positions 22 … 29. -/
theorem cobdatft_mode2 (r : Array U8 80#usize) (h0 : r.val.getD 0 0#u8 = 50#u8)
    (h21 : r.val.getD 21 0#u8 = 50#u8) :
    cobdatft r = .ok (Array.from
      ((((((((r.val.set 22 (r.val.getD 1 0#u8)).set 23 (r.val.getD 2 0#u8)).set 24
        (r.val.getD 3 0#u8)).set 25 (r.val.getD 4 0#u8)).set 26 (r.val.getD 6 0#u8)).set 27
        (r.val.getD 7 0#u8)).set 28 (r.val.getD 9 0#u8)).set 29 (r.val.getD 10 0#u8))
      (by have := r.property; simp_all)) := by
  have hl : r.val.length = 80 := by rw [Array.length_eq]; rfl
  have e : ∀ i (h : i < r.val.length), r.val[i]'h = r.val.getD i 0#u8 :=
    fun i h => (List.getD_eq_getElem _ _ h).symm
  have m1 : ((50#u8 : U8) = 49#u8) = False := by decide
  have m2 : ((50#u8 : U8) != 49#u8) = true := by decide
  have m3 : ((2#u8 : U8) = 1#u8) = False := by decide
  unfold cobdatft
  simp only [array_index_usize_eq, hl, uscalar_ofNat_val, Nat.reduceLT, _root_.dite_true, bind_ok,
    e, h0, h21, m1, m2, m3, _root_.ite_true, _root_.ite_false]
  simp only [array_update_eq, Array.from_val, List.length_set, hl, uscalar_ofNat_val, Nat.reduceLT,
    _root_.dite_true, bind_ok, List.getElem_set, Nat.reduceEqDiff, _root_.ite_false, e]

theorem codateNext_length (c d : List U8) (hc : c.length = 80) (hd : d.length = 10) :
    (codateNext c d).length = 80 := by
  simp only [codateNext, picks, List.length_cons, List.length_append, List.length_take,
    List.length_drop, List.length_replicate, hc, hd]
  omega

theorem picks_length (c d : List U8) (hc : c.length = 80) (hd : d.length = 10) :
    (picks d ++ (c.drop 30).take 2).length = 10 := by
  simp only [picks, List.length_append, List.length_take, List.length_drop, hc, hd]
  omega

/-- The date conversion of one record in `run`: `set_inp_date`, the types, `COBDATFT`,
`get_out_date`. -/
theorem codate_bind {β : Type} (c : Array U8 80#usize) (d : Array U8 10#usize)
    (f : Array U8 80#usize → Array U8 10#usize → Result β) :
    (do
      let c1 ← set_inp_date c d
      let c2 ← Array.update c1 0#usize 50#u8
      let c3 ← Array.update c2 21#usize 50#u8
      let c4 ← cobdatft c3
      let a5 ← get_out_date c4
      f c4 a5) =
    f (Array.from (codateNext c.val d.val) (codateNext_length _ _ c.property d.property))
      (Array.from (picks d.val ++ (c.val.drop 30).take 2) (picks_length _ _ c.property d.property)) := by
  have hc : c.val.length = 80 := c.property
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, hd⟩ := list10 d.val d.property
  obtain ⟨c0, hc0⟩ : ∃ c0, c.val.take 1 = [c0] := ⟨c.val[0], by
    rw [List.take_add_one, List.take_zero, List.getElem?_eq_getElem (by omega)]; rfl⟩
  obtain ⟨c21, c22, c23, c24, c25, c26, c27, c28, c29, h21⟩ :=
    list9 ((c.val.drop 21).take 9) (by simp [hc])
  have hdrop : c.val.drop 21 = [c21, c22, c23, c24, c25, c26, c27, c28, c29] ++ c.val.drop 30 := by
    rw [← h21, ← List.take_append_drop 9 (c.val.drop 21), List.drop_drop]
    simp
  rw [set_inp_date_eq]
  simp only [hc0, hd, hdrop, bind_ok, array_update_eq, Array.from_val, List.length_cons,
    List.length_drop, hc,
    uscalar_ofNat_val, List.replicate_succ, List.replicate_zero, List.cons_append,
    List.nil_append, List.set_cons_zero, List.set_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, _root_.dite_true]
  rw [cobdatft_mode2 _ (by simp) (by simp)]
  simp only [bind_ok, get_out_date_eq, Array.from_val, List.getD_cons_succ, List.getD_cons_zero,
    List.set_cons_succ, List.set_cons_zero]
  simp only [codateNext, picks, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
    List.take_zero, List.cons_append, List.nil_append, List.replicate_succ, List.replicate_zero,
    ]

end EquivLean.Modernize.Cbact01c.Rust

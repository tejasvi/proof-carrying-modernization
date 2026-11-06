import EquivLean.Bridge.Aeneas.Digits
import EquivLean.Modernize.Cbtrn03c.RustSpec

/-!
# CBTRN03C → Rust, part 1: the byte helpers

The Latin-1 bytes the helpers produce:
* `push_bytes`, `push_fill`, `push_padded` (a field of a given width: truncated or padded with
  spaces) and the copy loop of `push_digits` by `aeneas_spec`;
* `push_digits`: its digit loop fills a `[u8; 20]` buffer from position `width - 1` down (by hand,
  as `digits_of` of CBTRN01C); the result is `zeroPad width |v|`;
* `push_zoned_signed`: the digits, the last one overpunched with the sign through `index_mut`;
* `to133` (a report line: the first 133 bytes, padded with spaces), `bytes_eq`;
* `cmp_ebcdic`: `ebcdic_weight` is the position of a byte in the table `CP037`, which is
  coblean's CP037 decoding table, so the weight of a Latin-1 byte is its EBCDIC byte
  (`ebcdicOfLatin1`); the comparison is `Model.cmpB` on the EBCDIC bytes.
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

/-- An `if` whose condition holds (a rewrite rule for `simp (disch := …)`). -/
theorem ite_true_of {c : Prop} [Decidable c] {α : Sort _} {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

/-- Writing after a prefix of length `n`, into a run of `k + 1` copies. -/
theorem set_after' {α : Type _} (pre : List α) (k n : Nat) (a c : α) (hn : pre.length = n) :
    (pre ++ List.replicate (k + 1) a).set n c = pre ++ c :: List.replicate k a := by
  subst hn
  rw [List.set_append_right _ _ (le_refl _), Nat.sub_self, List.replicate_succ]
  rfl

/-- The last element of `P ++ [x]`. -/
theorem getElem_last_append {α : Type _} (L P : List α) (x : α) (hL : L = P ++ [x])
    (hi : L.length - 1 < L.length) : L[L.length - 1]'hi = x := by
  subst hL
  simp

/-! ## Appending bytes -/

set_option maxHeartbeats 1000000 in
/-- `push_bytes`: `s` after `out`. -/
theorem push_bytes_eq (out : alloc.vec.Vec U8) (s : Slice U8)
    (h : out.val.length + s.val.length < Usize.max) :
    cbtrn03c.push_bytes out s =
      .ok (alloc.vec.Vec.from (out.val ++ s.val) (by simp; omega)) := by
  aeneas_spec [cbtrn03c.push_bytes, cbtrn03c.push_bytes_loop]

set_option maxHeartbeats 1000000 in
/-- `push_fill`: `w` copies of `c` after `out`. -/
theorem push_fill_eq (out : alloc.vec.Vec U8) (c : U8) (w : Usize)
    (h : out.val.length + w.val < Usize.max) :
    cbtrn03c.push_fill out c w =
      .ok (alloc.vec.Vec.from (out.val ++ List.replicate w.val c) (by simp; omega)) := by
  aeneas_spec [cbtrn03c.push_fill, cbtrn03c.push_fill_loop]

set_option maxHeartbeats 1000000 in
/-- `push_padded`: `s` in a field of width `w` (truncated, or padded with spaces) after `out`. -/
theorem push_padded_eq (out : alloc.vec.Vec U8) (s : Slice U8) (w : Usize)
    (h : out.val.length + w.val < Usize.max) :
    cbtrn03c.push_padded out s w =
      .ok (alloc.vec.Vec.from (out.val ++ (s.val.take w.val ++
        List.replicate (w.val - s.val.length) 32#u8)) (by simp; omega)) := by
  aeneas_spec [cbtrn03c.push_padded, cbtrn03c.push_padded_loop]

/-! ## Digits -/

set_option maxHeartbeats 2000000 in
/-- The digit loop of `push_digits`: after `width` iterations, the `width` low digits of `x`,
right-aligned in the first `width` bytes of the buffer. -/
theorem push_digits_loop0_spec (w : Usize) (x : Nat) (m : U64) (hw : w.val ≤ 20)
    (hm : m.val = x) :
    wp (cbtrn03c.push_digits_loop0 w m (Array.repeat 20#usize 48#u8) 0#usize)
      (fun o => ∃ b, o = .ok b ∧
        b.val = zeroPad w.val x ++ List.replicate (20 - w.val) 48#u8) := by
  simp only [cbtrn03c.push_digits_loop0]
  refine wp_loop (loop_shape _) (fun s => s.2.2.val ≤ w.val ∧
      s.1.val = x / 10 ^ s.2.2.val ∧
      s.2.1.val = List.replicate (w.val - s.2.2.val) 48#u8 ++ zeroPad s.2.2.val x ++
        List.replicate (20 - w.val) 48#u8)
    (fun s => w.val - s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro m' buf i hinv
    obtain ⟨hi, hm', hbuf⟩ := hinv
    have hlen : buf.val.length = 20 := buf.property
    aeneas_wp [rust_loop_body, array_update_eq, UScalar.cast_val_eq, Array.from_val, hlen]
    by_cases h1 : i.val < w.val
    · have hd10 : m'.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have h256 : m'.val % 10 % 2 ^ 8 = m'.val % 10 := Nat.mod_eq_of_lt (by omega)
      simp only [h1, _root_.ite_true, h256]
      split_ifs
      all_goals try (exfalso; omega)
      all_goals try (exfalso; scalar_tac)
      simp only [loopCls_cont]
      refine ⟨⟨by simp only [UScalar.ofNatCore_val_eq]; omega, ?_, ?_⟩, by
        simp only [UScalar.ofNatCore_val_eq]; omega⟩
      · rw [UScalar.ofNatCore_val_eq, UScalar.ofNatCore_val_eq, hm', Nat.div_div_eq_div_mul,
          ← Nat.pow_succ]
      · simp only [Array.from_val, hbuf, UScalar.ofNatCore_val_eq]
        rw [set_mid _ _ h1, zeroPad_succ_left,
          show w.val - (i.val + 1) = w.val - 1 - i.val by omega]
        simp only [List.append_cancel_left_eq, List.append_cancel_right_eq,
          List.singleton_append, List.cons.injEq, and_true]
        rw [UScalar.eq_equiv, UScalar.ofNatCore_val_eq, byteOf_val _ (by omega), hm']
    · simp only [h1, _root_.ite_false, loopCls_done]
      refine ⟨buf, rfl, ?_⟩
      have e : i.val = w.val := by omega
      rw [hbuf, e, Nat.sub_self, List.replicate_zero, List.nil_append]
  · refine ⟨by simp, by simp [hm], ?_⟩
    simp only [Array.repeat_val, uscalar_ofNat_val, Nat.sub_zero]
    have z : zeroPad 0 x = [] := by simp [zeroPad, zpad, toDigits]
    rw [z, List.append_nil, ← List.replicate_add]
    congr 1
    omega

set_option maxHeartbeats 1000000 in
/-- The copy loop of `push_digits`: the first `width` bytes of the buffer. -/
theorem push_digits_loop1_eq (out : alloc.vec.Vec U8) (w : Usize) (buf : Array U8 20#usize)
    (hw : w.val ≤ 20) (h : out.val.length + w.val < Usize.max) :
    cbtrn03c.push_digits_loop1 out w buf 0#usize =
      .ok (alloc.vec.Vec.from (out.val ++ buf.val.take w.val) (by simp; omega)) := by
  aeneas_spec [cbtrn03c.push_digits_loop1]

/-- `push_digits`: the `w` low decimal digits of `|v|` after `out` (`w ≤ 20`). -/
theorem push_digits_eq (out : alloc.vec.Vec U8) (v : I64) (w : Usize)
    (hw : w.val ≤ 20) (hmin : -9223372036854775808 < v.val)
    (h : out.val.length + w.val < Usize.max) :
    cbtrn03c.push_digits out v w =
      .ok (alloc.vec.Vec.from (out.val ++ zeroPad w.val v.val.natAbs)
        (by simp [zeroPad_length]; omega)) := by
  refine eq_ok_of_wp ?_
  unfold cbtrn03c.push_digits
  have key : ∀ m : U64, m.val = v.val.natAbs →
      wp (Std.bind (cbtrn03c.push_digits_loop0 w m (Array.repeat 20#usize 48#u8) 0#usize)
        (fun buf1 => cbtrn03c.push_digits_loop1 out w buf1 0#usize))
      (fun o => o = .ok (alloc.vec.Vec.from (out.val ++ zeroPad w.val v.val.natAbs)
        (by simp [zeroPad_length]; omega))) := by
    intro m hm
    rw [wp_bind]
    refine wp_mono (push_digits_loop0_spec w v.val.natAbs m hw hm) ?_
    rintro _ ⟨b, rfl, hb⟩
    dsimp only
    rw [push_digits_loop1_eq out w b hw h]
    simp only [wp_ok, Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hb]
    rw [List.take_append_of_le_length (by simp [zeroPad_length]),
      List.take_of_length_le (by simp [zeroPad_length])]
  by_cases hv : v.val < 0
  · have hlt : (v < 0#i64) = True := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_true]
    aeneas_wp [IScalar.cast_val_eq]
    simp (disch := omega) only [dite_eq_left]
    refine (wp_bind _ _ _).mp (key _ ?_)
    simp only [IScalar.hcast_val_eq, IScalar.ofInt_val_eq, UScalarTy.U64_numBits_eq, Int.reducePow]
    omega
  · have hlt : (v < 0#i64) = False := by simp [IScalar.lt_equiv, hv]
    simp only [hlt, _root_.ite_false, wp_bind, wp_ok]
    refine (wp_bind _ _ _).mp (key _ ?_)
    have := v.hBounds
    simp only [IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, IScalarTy.I64_numBits_eq,
      Int.reducePow] at *
    omega

theorem zeroPad_succ_right (m x : Nat) :
    zeroPad (m + 1) x = zeroPad m (x / 10) ++ [byteOf (48 + x % 10)] := by
  simp only [zeroPad, zpad, toDigits_succ, List.map_append, List.map_cons, List.map_nil]

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
/-- `push_zoned_signed`: the `w` low digits of `|v|` after `out`, the last one overpunched with the
sign of `v` (`1 ≤ w ≤ 20`). -/
theorem push_zoned_signed_eq (out : alloc.vec.Vec U8) (v : I64) (w : Usize)
    (hw1 : 1 ≤ w.val) (hw : w.val ≤ 20) (hmin : -9223372036854775808 < v.val)
    (h : out.val.length + w.val < Usize.max) :
    cbtrn03c.push_zoned_signed out v w =
      .ok (alloc.vec.Vec.from
        (out.val ++ zeroPad (w.val - 1) (v.val.natAbs / 10) ++ [overByte v.val])
        (by simp [zeroPad_length]; omega)) := by
  obtain ⟨m, hm⟩ : ∃ m, w.val = m + 1 := ⟨w.val - 1, by omega⟩
  have hzl := zeroPad_length m (v.val.natAbs / 10)
  have hd10 : v.val.natAbs % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hLeq : out.val ++ zeroPad w.val v.val.natAbs =
      (out.val ++ zeroPad m (v.val.natAbs / 10)) ++ [byteOf (48 + v.val.natAbs % 10)] := by
    rw [hm, zeroPad_succ_right, List.append_assoc]
  have hpd : cbtrn03c.push_digits out v w =
      .ok (alloc.vec.Vec.from ((out.val ++ zeroPad m (v.val.natAbs / 10)) ++
        [byteOf (48 + v.val.natAbs % 10)]) (by simp [zeroPad_length]; omega)) := by
    rw [push_digits_eq out v w hw hmin h]
    simp only [hLeq]
  have hb : (byteOf (48 + v.val.natAbs % 10)).val = 48 + v.val.natAbs % 10 :=
    byteOf_val _ (by omega)
  have hm1 : w.val - 1 = m := by omega
  refine eq_ok_of_wp ?_
  simp only [cbtrn03c.push_zoned_signed, hpd, wp_bind, wp_ok]
  aeneas_wp [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize,
    alloc.vec.Vec.len_val, List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.getElem_concat_length, hb, hm1]
  have c1 : (out.val ++ zeroPad m (v.val.natAbs / 10)).length = out.val.length + m := by
    simp [hzl]
  simp only [hzl, Nat.add_sub_cancel_left, Nat.lt_succ_self, Nat.le_add_right, _root_.dite_true,
    _root_.ite_true, show 74 + v.val.natAbs % 10 ≤ 255 by omega,
    show 65 + v.val.natAbs % 10 ≤ 255 by omega, show 1 ≤ 74 + v.val.natAbs % 10 by omega,
    show 1 ≤ 65 + v.val.natAbs % 10 by omega]
  have hset : ∀ c : U8, (out.val ++ zeroPad m (v.val.natAbs / 10) ++
      [byteOf (48 + v.val.natAbs % 10)]).set (out.val.length + m) c =
      out.val ++ zeroPad m (v.val.natAbs / 10) ++ [c] := by
    intro c
    rw [List.set_append_right _ _ (by rw [c1])]
    simp [c1]
  split_ifs with hv hd hd
  all_goals simp only [Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.set_val_eq,
    alloc.vec.Vec.from_val, UScalar.ofNatCore_val_eq, hset, List.append_cancel_left_eq,
    List.cons.injEq, and_true]
  all_goals simp only [UScalar.eq_equiv, overByte_val]
  · have : decide (v.val < 0) = true := decide_eq_true (by omega)
    simp [overpunch, this, hd]
  · have : decide (v.val < 0) = true := decide_eq_true (by omega)
    simp only [overpunch, this, hd, UScalar.ofNatCore_val_eq]
    simp
  · have : decide (v.val < 0) = false := decide_eq_false (by omega)
    simp [overpunch, this, hd]
  · have : decide (v.val < 0) = false := decide_eq_false (by omega)
    simp only [overpunch, this, hd, UScalar.ofNatCore_val_eq]
    simp

/-! ## Report lines -/

/-- A report line: the first 133 bytes of `l`, padded with spaces. -/
def line133 (l : List U8) : Array U8 133#usize :=
  Array.from (l.take 133 ++ List.replicate (133 - l.length) 32#u8) (by simp; omega)

theorem to133_eq (v : Slice U8) : cbtrn03c.to133 v = .ok (line133 v.val) := by
  refine eq_ok_of_wp ?_
  simp only [cbtrn03c.to133, cbtrn03c.to133_loop]
  refine wp_loop (loop_shape _) (fun s => s.2.val ≤ 133 ∧ s.2.val ≤ v.val.length ∧
      s.1.val = v.val.take s.2.val ++ List.replicate (133 - s.2.val) 32#u8)
    (fun s => 133 - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro r i hinv
    obtain ⟨hi1, hi2, hr⟩ := hinv
    have hlen : r.val.length = 133 := r.property
    aeneas_wp [rust_loop_body, array_update_eq, Array.from_val, hlen]
    have hti : (v.val.take i.val).length = i.val := by simp; omega
    split_ifs with h1 h2 h3 h4 h5
    · simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Array.from_val]
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [hr, show 133 - i.val = (133 - (i.val + 1)) + 1 by omega, set_after' _ _ _ _ _ hti,
        take_succ_of_lt (show i.val < v.val.length by omega)]
      simp only [List.append_assoc, List.singleton_append]
    · exfalso; scalar_tac
    · simp only [loopCls_done, Except.ok.injEq, Array.eq_iff, line133, Array.from_val, hr]
      have e : i.val = v.val.length := by omega
      rw [e, List.take_length, List.take_of_length_le (by omega)]
    · simp only [loopCls_done, Except.ok.injEq, Array.eq_iff, line133, Array.from_val, hr]
      have e : i.val = 133 := by omega
      rw [e, show 133 - v.val.length = 0 by omega]
  · simp

/-! ## Comparisons -/

/-- `bytes_eq`: equality of the two byte slices. -/
theorem bytes_eq_eq (a b : Slice U8) : cbtrn03c.bytes_eq a b = .ok (decide (a.val = b.val)) := by
  refine eq_ok_of_wp ?_
  unfold cbtrn03c.bytes_eq
  aeneas_wp []
  split_ifs with hl
  · simp only [cbtrn03c.bytes_eq_loop]
    refine wp_loop (loop_shape _) (fun i => i.val ≤ a.val.length ∧
        a.val.take i.val = b.val.take i.val) (fun i => a.val.length - i.val) ?_ _ ?_
    · rintro i ⟨hi, ht⟩
      aeneas_wp [rust_loop_body]
      split_ifs with h1 h2 h3 h4
      · simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [take_succ_of_lt h1, take_succ_of_lt h2, ht, UScalar.eq_of_val_eq h3]
      · exfalso; scalar_tac
      · simp only [loopCls_done, Except.ok.injEq]
        refine (decide_eq_false fun hab => h3 ?_).symm
        rw [List.getElem_of_eq hab]
      · exfalso; omega
      · simp only [loopCls_done, Except.ok.injEq]
        have e : i.val = a.val.length := by omega
        rw [e, List.take_length, hl, List.take_length] at ht
        simp [ht]
    · simp
  · simp only [Except.ok.injEq]
    exact (decide_eq_false fun hab => hl (by rw [hab])).symm

/-! ## The EBCDIC collating sequence -/

/-- The EBCDIC byte of a Latin-1 byte. -/
def ebcU (u : U8) : UInt8 := ebcdicOfLatin1 u.val

/-- `CP037` is coblean's CP037 decoding table. -/
theorem cp037_table : cbtrn03c.CP037.val.map UScalar.val =
    (List.range 256).map fun j => cp037Code (UInt8.ofNat j) := by
  decide +kernel

/-- CP037 encodes the code point of every byte back to it. -/
theorem ebcdic_cp037 : ∀ j : Fin 256, ebcdicOfLatin1 (cp037Code (UInt8.ofNat j.val)) =
    UInt8.ofNat j.val := by
  decide +kernel

theorem cp037_at (j : Nat) (hj : j < 256) :
    (cbtrn03c.CP037.val[j]'(by simp; omega)).val = cp037Code (UInt8.ofNat j) := by
  have h := congrArg (fun l => l[j]?) cp037_table
  simp only [List.getElem?_map, List.getElem?_range hj] at h
  rw [List.getElem?_eq_getElem (by simp; omega)] at h
  simpa using h

/-- The weight `ebcdic_weight` gives a byte: its EBCDIC byte, as a `usize`. -/
def wtOf (u : U8) : Usize :=
  UScalar.ofNatCore (ebcU u).toNat (by
    have h1 := UInt8.toNat_lt (ebcU u)
    have h2 : 2 ^ 32 ≤ 2 ^ UScalarTy.Usize.numBits := by
      rcases System.Platform.numBits_eq with h | h <;> simp [UScalarTy.Usize_numBits_eq, h]
    omega)

theorem wtOf_val (u : U8) : (wtOf u).val = (ebcU u).toNat := UScalar.ofNatCore_val_eq _

/-- `ebcdic_weight`: the position of the byte in `CP037`, its EBCDIC byte. -/
theorem ebcdic_weight_eq (b : U8) : cbtrn03c.ebcdic_weight b = .ok (wtOf b) := by
  have hb : b.val < 256 := by have := b.hBounds; simpa using this
  have he : (ebcU b).toNat < 256 := UInt8.toNat_lt _
  have hfound : cp037Code (UInt8.ofNat (ebcU b).toNat) = b.val := by
    simp only [ebcU, UInt8.ofNat_toNat]
    exact cp037_roundtrip ⟨b.val, hb⟩
  have huniq : ∀ j, j < 256 → cp037Code (UInt8.ofNat j) = b.val → j = (ebcU b).toNat := by
    intro j hj hc
    have := ebcdic_cp037 ⟨j, hj⟩
    simp only at this
    rw [hc] at this
    simp only [ebcU, this, UInt8.toNat_ofNat']
    omega
  refine eq_ok_of_wp ?_
  simp only [cbtrn03c.ebcdic_weight, cbtrn03c.ebcdic_weight_loop]
  refine wp_loop (loop_shape _) (fun i => i.val ≤ (ebcU b).toNat) (fun i => 256 - i.val) ?_ _
    (by simp)
  intro i hi
  aeneas_wp [rust_loop_body, array_index_usize_eq]
  split_ifs with h1 h2 h3 h4
  · simp only [loopCls_done, Except.ok.injEq]
    have hc : cp037Code (UInt8.ofNat i.val) = b.val := by
      rw [cp037_at _ (by omega)] at h3; exact h3
    apply UScalar.eq_of_val_eq
    rw [wtOf_val]
    exact huniq _ (by omega) hc
  · simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
    have hc : cp037Code (UInt8.ofNat i.val) ≠ b.val := fun hc =>
      h3 (by rw [cp037_at _ (by omega)]; exact hc)
    have hne : i.val ≠ (ebcU b).toNat := fun h => hc (h ▸ hfound)
    omega
  · exfalso; scalar_tac
  · exfalso; simp at h2; omega
  · exfalso; omega

/-- A comparison result as `cmp_ebcdic` returns it. -/
def ordI : Ordering → Int
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- `cmp_ebcdic`: `Model.cmpB` on the EBCDIC bytes. -/
theorem cmp_ebcdic_spec (a b : Slice U8) :
    wp (cbtrn03c.cmp_ebcdic a b) (fun o => ∃ r, o = .ok r ∧
      r.val = ordI (Model.cmpB (a.val.map ebcU) (b.val.map ebcU))) := by
  simp only [cbtrn03c.cmp_ebcdic, cbtrn03c.cmp_ebcdic_loop]
  refine wp_loop (loop_shape _) (fun i => i.val ≤ a.val.length ∧ i.val ≤ b.val.length ∧
      Model.cmpB (a.val.map ebcU) (b.val.map ebcU) =
        Model.cmpB ((a.val.map ebcU).drop i.val) ((b.val.map ebcU).drop i.val))
    (fun i => a.val.length - i.val) ?_ _ (by simp)
  rintro i ⟨hia, hib, hc⟩
  have hdrop : ∀ (l : List U8) (j : Nat) (h : j < l.length),
      (l.map ebcU).drop j = ebcU l[j] :: (l.map ebcU).drop (j + 1) := by
    intro l j h
    rw [List.drop_eq_getElem_cons (by simpa using h)]
    simp
  aeneas_wp [rust_loop_body, ebcdic_weight_eq, wtOf_val]
  by_cases h1 : i.val < a.val.length
  · by_cases h2 : i.val < b.val.length
    · have hc' := hc
      rw [hdrop _ _ h1, hdrop _ _ h2] at hc'
      simp only [Model.cmpB, UInt8.lt_iff_toNat_lt] at hc'
      simp only [h1, h2, _root_.ite_true, _root_.dite_true]
      by_cases h3 : (ebcU a.val[i.val]).toNat < (ebcU b.val[i.val]).toNat
      · simp only [h3, _root_.ite_true, loopCls_done] at hc' ⊢
        exact ⟨_, rfl, by rw [hc']; rfl⟩
      · by_cases h4 : (ebcU b.val[i.val]).toNat < (ebcU a.val[i.val]).toNat
        · simp only [h3, h4, _root_.ite_true, _root_.ite_false, loopCls_done] at hc' ⊢
          exact ⟨_, rfl, by rw [hc']; rfl⟩
        · simp only [h3, h4, _root_.ite_false] at hc' ⊢
          rw [dite_eq_left_of_eq_true (eq_true (by scalar_tac))]
          simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
          exact ⟨⟨by omega, by omega, hc'⟩, by omega⟩
    · have hd : (b.val.map ebcU).drop i.val = [] := by simp; omega
      rw [hd] at hc
      simp only [h1, h2, _root_.ite_true, _root_.ite_false, loopCls_done]
      refine ⟨_, rfl, ?_⟩
      rw [hc]
      cases (a.val.map ebcU).drop i.val <;> rfl
  · have hd : (a.val.map ebcU).drop i.val = [] := by simp; omega
    rw [hd] at hc
    simp only [h1, _root_.ite_false, loopCls_done]
    refine ⟨_, rfl, ?_⟩
    rw [hc]
    rfl

end EquivLean.Modernize.Cbtrn03c.Rust

import EquivLean.Modernize.Cbact04c.RustSpec
import EquivLean.Bridge.Aeneas.Tactic

/-!
# CBACT04C → Rust: the helper functions

Equations `f args = .ok value` for the helpers of the Rust translation (Charon + Aeneas output in
`Demo/Gen/Aeneas/ModCbact04c`), each with the value as a function of the arguments:
* byte copies: `to_vec`, `push_bytes`, `push_digits`'s copy loop, `run`'s first loop (the account
  table);
* `eq10`, `eq2` (`decide` of the byte lists' equality);
* numbers: `abs_u64` (`absU`), `pow10`, `trunc_digits` (`tmodI`: Rust's `%` is `Int.tmod`, from
  `BitVec.toInt_srem`);
* digits: `digits_of` (`digs n |v|`: the `n` low decimal digits, zero-padded), `push_digits`,
  `push_signed` (`sdigs`: the last digit with the sign overpunched), `display_tcat` (`tcatLine`);
* the searches `find_account`, `find_xref`, `find_disc`: the index of the first match, else the
  length (`List.findIdx`; loop invariant `SearchInv`);
* `make_timestamp` (`tsArr`), `build_tran` (`tranOf`; four copy loops, `copy_step`),
  `update_account` (`postedR`, the table updated with `List.set` at the first match).

The loops are proved with `wp_loop` and an invariant.  Symbolically executed branch conditions are
decided by `ifs_omega` (`simp` with `omega` as discharger).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Rust

/-! ## Basics -/

/-- `c = ok v` from its weakest precondition. -/
theorem eq_ok_of_wp' {α : Type _} {c : Result α} {v : α} (h : wp c (fun o => o = .ok v)) :
    c = .ok v := by
  rcases (wp_iff _ _).1 h with ⟨s, hs, hok⟩ | ⟨e, he, herr⟩
  · cases hok; exact hs
  · cases herr

theorem take_succ_of_lt' {α : Type _} {l : List α} {i : Nat} (h : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl

/-- `a[i]` for an array. -/
theorem arr_index_eq {α : Type _} {n : Usize} (a : Std.Array α n) (i : Usize) :
    Std.Array.index_usize a i =
      if h : i.val < a.val.length then .ok (a.val[i.val]) else .fail .arrayOutOfBounds := by
  simp only [Std.Array.index_usize, Std.Array.getElem?_Usize_eq]
  have hl : a.val.length = n.val := a.property
  by_cases h : i.val < a.val.length
  · have h' : i.val < n.val := by omega
    simp [h']
  · have h' : ¬ i.val < n.val := by omega
    simp [h']

/-- `a[i] = x` for an array. -/
theorem arr_update_eq {α : Type _} {n : Usize} (a : Std.Array α n) (i : Usize) (x : α) :
    Std.Array.update a i x = if _h : i.val < a.val.length then
      .ok (Std.Array.from (a.val.set i.val x) (by simp [a.property])) else .fail .arrayOutOfBounds := by
  simp only [Std.Array.update, Std.Array.getElem?_Usize_eq]
  have hl : a.val.length = n.val := a.property
  by_cases h : i.val < a.val.length
  · have h' : i.val < n.val := by omega
    simp [h']
  · have h' : ¬ i.val < n.val := by omega
    simp [h']

theorem usz_lit_val {ty : UScalarTy} (x : Nat) (h : x ≤ UScalar.cMax ty) :
    (UScalar.ofNat x h).val = x := UScalar.ofNatCore_val_eq _

theorem isz_lit_val {ty : IScalarTy} (x : Int) (h : IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty) :
    (IScalar.ofInt x h).val = x := IScalar.ofInt_val_eq _

theorem take_eq_take_succ {α : Type _} {l1 l2 : List α} {i : Nat} (h1 : i < l1.length)
    (h2 : i < l2.length) :
    (l1.take (i + 1) = l2.take (i + 1)) ↔ (l1.take i = l2.take i ∧ l1[i] = l2[i]) := by
  rw [take_succ_of_lt' h1, take_succ_of_lt' h2]
  constructor
  · intro h
    have := List.append_inj h (by simp; omega)
    simp only [List.cons.injEq, and_true] at this
    exact this
  · rintro ⟨h, h'⟩
    rw [h, h']

theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max_eq, U64.max_eq]

/-- Decide the `if`s of a symbolically executed goal whose conditions are linear arithmetic. -/
macro "ifs_omega" : tactic =>
  `(tactic| simp (disch := omega) only [dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right])

theorem eq10_eq (a b : Std.Array U8 10#usize) :
    cbact04c_t.eq10 a b = .ok (decide (a.val = b.val)) := by
  have ha : a.val.length = 10 := a.property
  have hb : b.val.length = 10 := b.property
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.eq10, cbact04c_t.eq10_loop]
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ 10 ∧ s.1 = decide (a.val.take s.2.val = b.val.take s.2.val))
    (fun s => 10 - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro eq i hinv
    obtain ⟨hi, he⟩ := hinv
    simp only [cbact04c_t.eq10_loop.body]
    aeneas_wp [arr_index_eq, ha, hb, usz_lit_val]
    by_cases h : i.val < 10
    · have hov : i.val + 1 ≤ Usize.max := by have := usize_max_ge; omega
      have hlt1 : i.val < a.val.length := by omega
      have hlt2 : i.val < b.val.length := by omega
      by_cases h1 : a.val[i.val].val = b.val[i.val].val
      · have e1 : a.val[i.val] = b.val[i.val] := UScalar.eq_of_val_eq h1
        simp only [h, hov, h1, not_true_eq_false, _root_.ite_true, _root_.ite_false,
          _root_.dite_true, loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [he]
        simp only [take_eq_take_succ hlt1 hlt2, e1, and_true]
      · have e1 : ¬ a.val[i.val] = b.val[i.val] := fun e => h1 (e ▸ rfl)
        simp only [h, hov, h1, not_false_eq_true, _root_.ite_true,
          _root_.dite_true, loopCls_cont, UScalar.ofNatCore_val_eq]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        simp only [take_eq_take_succ hlt1 hlt2, e1, and_false, decide_false]
    · simp only [h, _root_.ite_false, loopCls_done]
      have hi' : i.val = 10 := by omega
      rw [he, hi', List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
  · simp

theorem eq2_eq (a b : Std.Array U8 2#usize) :
    cbact04c_t.eq2 a b = .ok (decide (a.val = b.val)) := by
  have ha : a.val.length = 2 := a.property
  have hb : b.val.length = 2 := b.property
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.eq2]
  aeneas_wp [arr_index_eq, ha, hb, usz_lit_val]
  match ha' : a.val, hb' : b.val, ha, hb with
  | [x0, x1], [y0, y1], _, _ =>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.cons.injEq, and_true]
    have e0 : (x0.val = y0.val) ↔ x0 = y0 := ⟨UScalar.eq_of_val_eq, fun h => h ▸ rfl⟩
    have e1 : (x1.val = y1.val) ↔ x1 = y1 := ⟨UScalar.eq_of_val_eq, fun h => h ▸ rfl⟩
    by_cases h0 : x0 = y0
    · simp [h0, e1]
    · simp [h0, e0]

/-! ## Byte copies -/

theorem push_bytes_loop_spec (s : Slice U8) (v0 : alloc.vec.Vec U8)
    (h : v0.val.length + s.val.length ≤ Usize.max) :
    wp (loop (fun (v1, i1) => cbact04c_t.push_bytes_loop.body s v1 i1) (v0, 0#usize))
      (fun o => o = .ok (alloc.vec.Vec.from (v0.val ++ s.val) (by simp; omega))) := by
  refine wp_loop (loop_shape _)
    (fun x => x.2.val ≤ s.val.length ∧ x.1.val = v0.val ++ s.val.take x.2.val)
    (fun x => s.val.length - x.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro v i hinv
    obtain ⟨hi, hv⟩ := hinv
    simp only [cbact04c_t.push_bytes_loop.body]
    aeneas_wp [usz_lit_val]
    by_cases hlt : i.val < s.val.length
    · have hvl : v.val.length < Usize.max := by
        rw [hv]; simp only [List.length_append, List.length_take]; omega
      have hov : i.val + 1 ≤ Usize.max := by omega
      simp only [hlt, hvl, hov, _root_.dite_true, _root_.ite_true, loopCls_cont,
        UScalar.ofNatCore_val_eq, alloc.vec.Vec.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hv, take_succ_of_lt' hlt, List.append_assoc]
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq, alloc.vec.Vec.eq_iff,
        alloc.vec.Vec.from_val]
      rw [hv, List.take_of_length_le (by omega)]
  · simp

theorem to_vec_eq (s : Slice U8) :
    cbact04c_t.to_vec s = .ok (alloc.vec.Vec.from s.val (by scalar_tac)) := by
  have hs : s.val.length ≤ Usize.max := by scalar_tac
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.to_vec, cbact04c_t.to_vec_loop]
  have hb : cbact04c_t.to_vec_loop.body = cbact04c_t.push_bytes_loop.body := rfl
  rw [hb]
  have := push_bytes_loop_spec s (alloc.vec.Vec.new U8) (by simp)
  simpa using this

theorem push_bytes_eq (dst : alloc.vec.Vec U8) (src : Slice U8)
    (h : dst.val.length + src.val.length < Usize.max) :
    cbact04c_t.push_bytes dst src = .ok (alloc.vec.Vec.from (dst.val ++ src.val) (by simp; omega)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.push_bytes, cbact04c_t.push_bytes_loop]
  exact push_bytes_loop_spec src dst (by omega)

theorem run_loop0_eq (s : Slice cbact04c_t.AccountRecord) :
    cbact04c_t.run_loop0 s (alloc.vec.Vec.new cbact04c_t.AccountRecord) 0#usize =
      .ok (alloc.vec.Vec.from s.val (by scalar_tac)) := by
  have hs : s.val.length ≤ Usize.max := by scalar_tac
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.run_loop0]
  refine wp_loop (loop_shape _)
    (fun x => x.2.val ≤ s.val.length ∧ x.1.val = s.val.take x.2.val)
    (fun x => s.val.length - x.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro v i hinv
    obtain ⟨hi, hv⟩ := hinv
    simp only [cbact04c_t.run_loop0.body]
    aeneas_wp [usz_lit_val]
    by_cases hlt : i.val < s.val.length
    · have hvl : v.val.length < Usize.max := by
        rw [hv]; simp only [List.length_take]; omega
      have hov : i.val + 1 ≤ Usize.max := by omega
      simp only [hlt, hvl, hov, _root_.dite_true, _root_.ite_true, loopCls_cont,
        UScalar.ofNatCore_val_eq, alloc.vec.Vec.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hv, take_succ_of_lt' hlt]
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq, alloc.vec.Vec.eq_iff,
        alloc.vec.Vec.from_val]
      rw [hv, List.take_of_length_le (by omega)]
  · simp

/-! ## Numbers -/

/-- `|v|` as a `u64`. -/
def absU (v : I64) : U64 :=
  UScalar.ofNatCore v.val.natAbs (by
    have := v.hBounds
    simp only [IScalarTy.I64_numBits_eq, UScalarTy.U64_numBits_eq] at *
    omega)

theorem abs_u64_eq (v : I64) : cbact04c_t.abs_u64 v = .ok (absU v) := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.abs_u64]
  have hb := v.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hb
  aeneas_wp [isz_lit_val, usz_lit_val]
  split_ifs with h1 h2 h3 h4
  · simp only [Except.ok.injEq]
    apply UScalar.eq_of_val_eq
    simp only [UScalar.ofNatCore_val_eq, IScalar.hcast_val_eq, IScalar.ofInt_val_eq, absU,
      UScalarTy.U64_numBits_eq]
    omega
  · exfalso; apply h4
    simp only [IScalar.hcast_val_eq, IScalar.ofInt_val_eq, UScalarTy.U64_numBits_eq]
    omega
  · exfalso; omega
  · exfalso; omega
  · simp only [Except.ok.injEq]
    apply UScalar.eq_of_val_eq
    simp only [UScalar.ofNatCore_val_eq, IScalar.hcast_val_eq, absU, UScalarTy.U64_numBits_eq]
    omega


theorem pow10_spec (n : U32) (hn : n.val ≤ 18) :
    wp (cbact04c_t.pow10 n) (fun o => ∃ p, o = .ok p ∧ p.val = 10 ^ n.val) := by
  simp only [cbact04c_t.pow10, cbact04c_t.pow10_loop]
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = 10 ^ s.2.val) (fun s => n.val - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro p i hinv
    obtain ⟨hi, hp⟩ := hinv
    simp only [cbact04c_t.pow10_loop.body]
    aeneas_wp [isz_lit_val, usz_lit_val]
    by_cases h : i.val < n.val
    · have h10 : (10 : Int) ^ i.val ≤ 10 ^ 17 := pow_le_pow_right₀ (by norm_num) (by omega)
      have h0 : (0 : Int) < 10 ^ i.val := by positivity
      have hm : -9223372036854775808 ≤ p.val * 10 ∧ p.val * 10 ≤ 9223372036854775807 := by
        rw [hp]; constructor <;> omega
      have hov : i.val ≤ 4294967294 := by omega
      simp only [h, hm, hov, _root_.ite_true, _root_.dite_true, loopCls_cont,
        UScalar.ofNatCore_val_eq, IScalar.ofInt_val_eq]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hp, pow_succ]
    · simp only [h, _root_.ite_false, loopCls_done]
      exact ⟨p, rfl, by rw [hp]; congr 1; omega⟩
  · simp

/-- `v % 10 ^ n` (Rust's `%`: the remainder has the sign of `v`). -/
def tmodI (v : I64) (n : Nat) : I64 := ⟨BitVec.ofInt _ (Int.tmod v.val (10 ^ n))⟩

theorem tmod_pow_bound (v : Int) (n : Nat) (hn : n ≤ 18) :
    (Int.tmod v (10 ^ n)).natAbs < 10 ^ 18 := by
  rw [Int.natAbs_tmod]
  have h1 : (10 ^ n : Int).natAbs = 10 ^ n := by simp
  rw [h1]
  have := Nat.mod_lt v.natAbs (show 0 < 10 ^ n by positivity)
  have h2 : 10 ^ n ≤ 10 ^ 18 := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem tmodI_val (v : I64) (n : Nat) (hn : n ≤ 18) : (tmodI v n).val = Int.tmod v.val (10 ^ n) := by
  have hb := tmod_pow_bound v.val n hn
  show (BitVec.ofInt _ (Int.tmod v.val (10 ^ n))).toInt = Int.tmod v.val (10 ^ n)
  rw [BitVec.toInt_ofInt]
  simp only [IScalarTy.I64_numBits_eq]
  apply Int.bmod_eq_of_le <;> push_cast <;> omega

theorem trunc_digits_eq (v : I64) (n : U32) (hn : n.val ≤ 18) :
    cbact04c_t.trunc_digits v n = .ok (tmodI v n.val) := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.trunc_digits, wp_bind]
  refine wp_mono (pow10_spec n hn) ?_
  rintro _ ⟨p, rfl, hp⟩
  simp only [wp_IScalar_rem]
  have hp0 : p.val ≠ 0 := by rw [hp]; positivity
  simp only [hp0, ne_eq, not_false_eq_true, _root_.ite_true, Except.ok.injEq]
  apply IScalar.eq_of_val_eq
  rw [tmodI_val v n.val hn]
  simp only [IScalar.val]
  rw [BitVec.toInt_srem]
  change Int.tmod v.val p.val = _
  rw [hp]
  rfl

/-! ## Digits -/

open Cobol.Digits (toDigits)

/-- A code point as a byte. -/
def byt (d : Nat) : U8 := ⟨BitVec.ofNat 8 d⟩

theorem byt_val (d : Nat) (h : d < 256) : (byt d).val = d := by
  simp [byt, UScalar.val, Nat.mod_eq_of_lt h]

/-- The `n` zero-padded decimal digits of `v`, as Latin-1 bytes. -/
def digs (n v : Nat) : List U8 := (zpad n v).map byt

theorem digs_length (n v : Nat) : (digs n v).length = n := by
  simp [digs, zpad]

/-- Digit `j` (from the left) of the `n` digits of `v`. -/
theorem toDigits_getElem' (n v j : Nat) (h : j < n) :
    (toDigits 10 n v)[j]'(by simpa using h) = v / 10 ^ (n - 1 - j) % 10 := by
  induction n generalizing v j with
  | zero => omega
  | succ n ih =>
    simp only [toDigits]
    by_cases hj : j < n
    · rw [List.getElem_append_left (by simpa using hj), ih (v / 10) j hj]
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3
      omega
    · have : j = n := by omega
      subst this
      rw [List.getElem_append_right (by simp)]
      simp

/-- The digits of `x` grow on the left. -/
theorem toDigits_succ_left' (i x : Nat) :
    toDigits 10 (i + 1) x = [x / 10 ^ i % 10] ++ toDigits 10 i x := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    rw [toDigits_getElem' (i + 1) x j (by simpa using h1)]
    cases j with
    | zero => simp
    | succ j =>
      simp only [List.singleton_append, List.getElem_cons_succ]
      rw [toDigits_getElem' i x j (by simp at h1; omega)]
      have : i + 1 - 1 - (j + 1) = i - 1 - j := by omega
      rw [this]

theorem digs_succ_left (i x : Nat) :
    digs (i + 1) x = [byt (48 + x / 10 ^ i % 10)] ++ digs i x := by
  simp only [digs, zpad, toDigits_succ_left', List.map_append, List.map_cons, List.map_nil]

theorem digs_succ_right (i x : Nat) :
    digs (i + 1) x = digs i (x / 10) ++ [byt (48 + x % 10)] := by
  simp only [digs, zpad, toDigits_succ, List.map_append, List.map_cons, List.map_nil]

theorem digs_zero (x : Nat) : digs 0 x = [] := by simp [digs, zpad, toDigits]

theorem digits_of_loop0_spec (n : Usize) (x : Nat) (a : U64) (ha : a.val = x)
    (hn : n.val ≤ 20) :
    wp (cbact04c_t.digits_of_loop0 n a (alloc.vec.Vec.new U8) 0#usize)
      (fun o => ∃ t, o = .ok t ∧ t.val = (digs n.val x).reverse) := by
  simp only [cbact04c_t.digits_of_loop0]
  refine wp_loop (loop_shape _)
    (fun s => s.2.2.val ≤ n.val ∧ s.1.val = x / 10 ^ s.2.2.val ∧
      s.2.1.val = (digs s.2.2.val x).reverse)
    (fun s => n.val - s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro w t i hinv
    obtain ⟨hi, hw, ht⟩ := hinv
    simp only [cbact04c_t.digits_of_loop0.body]
    aeneas_wp [usz_lit_val, UScalar.cast_val_eq]
    by_cases h : i.val < n.val
    · have hd : w.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have h256 : w.val % 10 % 256 = w.val % 10 := Nat.mod_eq_of_lt (by omega)
      have hov1 : 48 + w.val % 10 ≤ 255 := by omega
      have hlen : t.val.length < Usize.max := by
        rw [ht, List.length_reverse, digs_length]; have := usize_max_ge; omega
      have hov2 : i.val + 1 ≤ Usize.max := by have := usize_max_ge; omega
      ifs_omega
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
      · rw [hw, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      · simp only [alloc.vec.Vec.from_val]
        rw [ht, digs_succ_left, List.reverse_append, List.reverse_singleton]
        congr 2
        apply UScalar.eq_of_val_eq
        rw [byt_val _ (by omega), UScalar.ofNatCore_val_eq, hw]
        have : x / 10 ^ i.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
        simp only [Nat.reducePow]
        omega
    · simp only [h, _root_.ite_false, loopCls_done]
      refine ⟨t, rfl, ?_⟩
      rw [ht, show i.val = n.val by omega]
  · simp [digs_zero, ha]

theorem digits_of_loop1_spec (t : alloc.vec.Vec U8) (n : Usize) (ht : t.val.length = n.val) :
    wp (cbact04c_t.digits_of_loop1 t (alloc.vec.Vec.new U8) n)
      (fun o => ∃ v, o = .ok v ∧ v.val = t.val.reverse) := by
  simp only [cbact04c_t.digits_of_loop1]
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = (t.val.drop s.2.val).reverse)
    (fun s => s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro v j hinv
    obtain ⟨hj, hv⟩ := hinv
    simp only [cbact04c_t.digits_of_loop1.body]
    aeneas_wp [usz_lit_val]
    by_cases h : 0 < j.val
    · have hlt : j.val - 1 < t.val.length := by omega
      have hlen : v.val.length < Usize.max := by
        rw [hv, List.length_reverse, List.length_drop]
        have := t.val.length.le_refl; have := usize_max_ge
        have := t.property; scalar_tac
      ifs_omega
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      simp only [alloc.vec.Vec.from_val]
      rw [hv, ← List.reverse_singleton, ← List.reverse_append, List.singleton_append]
      congr 1
      rw [List.drop_eq_getElem_cons hlt, show j.val - 1 + 1 = j.val by omega]
    · simp only [h, _root_.ite_false, loopCls_done]
      refine ⟨v, rfl, ?_⟩
      rw [hv, show j.val = 0 by omega, List.drop_zero]
  · simp [ht]

theorem digits_of_eq (v : I64) (n : Usize) (hn : n.val ≤ 20) :
    cbact04c_t.digits_of v n =
      .ok (alloc.vec.Vec.from (digs n.val v.val.natAbs) (by
        rw [digs_length]; have := usize_max_ge; omega)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.digits_of, abs_u64_eq, wp_bind, wp_ok]
  refine wp_mono (digits_of_loop0_spec n v.val.natAbs (absU v)
    (by simp [absU]) hn) ?_
  rintro _ ⟨t, rfl, ht⟩
  simp only
  refine wp_mono (digits_of_loop1_spec t n (by rw [ht, List.length_reverse, digs_length])) ?_
  rintro _ ⟨w, rfl, hw⟩
  simp only [Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hw, ht,
    List.reverse_reverse]

theorem push_digits_loop_eq (v d : alloc.vec.Vec U8)
    (h : v.val.length + d.val.length < Usize.max) :
    cbact04c_t.push_digits_loop v d 0#usize =
      .ok (alloc.vec.Vec.from (v.val ++ d.val) (by simp; omega)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.push_digits_loop]
  refine wp_loop (loop_shape _)
    (fun x => x.2.val ≤ d.val.length ∧ x.1.val = v.val ++ d.val.take x.2.val)
    (fun x => d.val.length - x.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro w i hinv
    obtain ⟨hi, hw⟩ := hinv
    simp only [cbact04c_t.push_digits_loop.body]
    aeneas_wp [usz_lit_val]
    by_cases hlt : i.val < d.val.length
    · have hwl : w.val.length < Usize.max := by
        rw [hw]; simp only [List.length_append, List.length_take]; omega
      have hov : i.val + 1 ≤ Usize.max := by omega
      simp only [hlt, hwl, hov, _root_.dite_true, _root_.ite_true, loopCls_cont,
        UScalar.ofNatCore_val_eq, alloc.vec.Vec.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hw, take_succ_of_lt' hlt, List.append_assoc]
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq, alloc.vec.Vec.eq_iff,
        alloc.vec.Vec.from_val]
      rw [hw, List.take_of_length_le (by omega)]
  · simp

theorem push_digits_eq (v : alloc.vec.Vec U8) (x : I64) (n : Usize) (hn : n.val ≤ 20)
    (h : v.val.length + n.val < Usize.max) :
    cbact04c_t.push_digits v x n =
      .ok (alloc.vec.Vec.from (v.val ++ digs n.val x.val.natAbs) (by
        simp only [List.length_append, digs_length]; omega)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.push_digits, digits_of_eq x n hn, wp_bind, wp_ok]
  rw [push_digits_loop_eq _ _ (by simp only [alloc.vec.Vec.from_val, digs_length]; omega)]
  simp only [alloc.vec.Vec.from_val, wp_ok]

/-- The signed DISPLAY digits of `v` in `n` bytes: the leading digits, zero-padded, then the last
digit with the sign overpunched (`EquivLean.Cobol.Rec.overpunch`). -/
def sdigs (n : Nat) (v : Int) : List U8 :=
  digs (n - 1) (v.natAbs / 10) ++ [byt (overpunch (decide (v < 0)) (v.natAbs % 10))]

theorem sdigs_length (n : Nat) (v : Int) (hn : 1 ≤ n) : (sdigs n v).length = n := by
  simp only [sdigs, List.length_append, digs_length, List.length_singleton]; omega

theorem digs_getElem_last (n x i : Nat) (hi : i + 1 = n) :
    (digs n x)[i]'(by rw [digs_length]; omega) = byt (48 + x % 10) := by
  subst hi
  simp only [digs_succ_right]
  rw [List.getElem_append_right (by simp [digs_length])]
  simp [digs_length]

/-- The bytes `push_signed`'s loop has written after `i` iterations. -/
def psig (n : Nat) (v : Int) (d : List U8) (i : Nat) : List U8 :=
  if i < n then d.take i else sdigs n v

theorem digs_take_pred (n x : Nat) (hn : 1 ≤ n) : (digs n x).take (n - 1) = digs (n - 1) (x / 10) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [digs_succ_right, Nat.add_sub_cancel, List.take_append_of_le_length (by simp [digs_length]),
    List.take_of_length_le (by simp [digs_length])]

theorem overpunch_lt (neg : Bool) (d : Nat) (hd : d < 10) : overpunch neg d < 256 := by
  unfold overpunch; split_ifs <;> omega

theorem push_signed_loop_spec (v0 : alloc.vec.Vec U8) (x : I64) (n : Usize) (d : alloc.vec.Vec U8)
    (hn1 : 1 ≤ n.val) (hd : d.val = digs n.val x.val.natAbs)
    (h : v0.val.length + n.val < Usize.max) :
    wp (cbact04c_t.push_signed_loop v0 n d (decide (x.val < 0)) 0#usize)
      (fun o => ∃ w, o = .ok w ∧ w.val = v0.val ++ sdigs n.val x.val) := by
  simp only [cbact04c_t.push_signed_loop]
  have hdl : d.val.length = n.val := by rw [hd, digs_length]
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ n.val ∧ s.1.val = v0.val ++ psig n.val x.val d.val s.2.val)
    (fun s => n.val - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro v i hinv
    obtain ⟨hi, hv⟩ := hinv
    simp only [cbact04c_t.push_signed_loop.body]
    aeneas_wp [usz_lit_val]
    by_cases hlt : i.val < n.val
    · have hov : i.val + 1 ≤ Usize.max := by omega
      have hpv : psig n.val x.val d.val i.val = d.val.take i.val := by simp [psig, hlt]
      have hvl : v.val.length < Usize.max := by
        rw [hv, hpv]; simp only [List.length_append, List.length_take]; omega
      have h1 : i.val < d.val.length := by omega
      by_cases hlast : i.val + 1 = n.val
      · -- the last digit, with the sign
        have hx : d.val[i.val]'h1 = byt (48 + x.val.natAbs % 10) := by
          rw [List.getElem_of_eq hd]
          exact digs_getElem_last _ _ _ hlast
        have hm : x.val.natAbs % 10 < 10 := Nat.mod_lt _ (by norm_num)
        have hxv : (d.val[i.val]'h1).val = 48 + x.val.natAbs % 10 := by
          rw [hx, byt_val _ (by omega)]
        have hA : 48 ≤ 48 + x.val.natAbs % 10 := by omega
        have hB : 48 + x.val.natAbs % 10 - 48 = x.val.natAbs % 10 := by omega
        have hC : 74 + x.val.natAbs % 10 ≤ 255 := by omega
        have hD : 1 ≤ 74 + x.val.natAbs % 10 := by omega
        have hE : 65 + x.val.natAbs % 10 ≤ 255 := by omega
        have hF : 1 ≤ 65 + x.val.natAbs % 10 := by omega
        have hpn : psig n.val x.val d.val (i.val + 1) = sdigs n.val x.val := by
          simp [psig, hlast]
        have htk : d.val.take i.val = digs (n.val - 1) (x.val.natAbs / 10) := by
          rw [hd, show i.val = n.val - 1 by omega, digs_take_pred _ _ hn1]
        simp only [hlt, hlast, h1, hxv, hA, hB, hC, hD, hE, hF, hvl, _root_.dite_true,
          _root_.ite_true, loopCls_cont, UScalar.ofNatCore_val_eq, alloc.vec.Vec.from_val]
        have hnm : n.val ≤ Usize.max := by omega
        have hps : psig n.val x.val d.val n.val = sdigs n.val x.val := by simp [psig]
        simp only [hnm, _root_.dite_true, hps]
        have key : ∀ c : U8, c.val = overpunch (decide (x.val < 0)) (x.val.natAbs % 10) →
            (n.val ≤ n.val ∧ v.val ++ [c] = v0.val ++ sdigs n.val x.val) ∧
              n.val - n.val < n.val - i.val := by
          intro c hc
          refine ⟨⟨le_refl _, ?_⟩, by omega⟩
          rw [hv, hpv, htk, sdigs, List.append_assoc]
          congr 2
          simp only [List.cons.injEq, and_true]
          apply UScalar.eq_of_val_eq
          rw [hc, byt_val _ (overpunch_lt _ _ hm)]
        by_cases hneg : x.val < 0 <;> by_cases hz : x.val.natAbs % 10 = 0 <;>
          simp only [hneg, hz, _root_.ite_true, _root_.ite_false] <;> apply key <;>
          simp [overpunch, hneg, hz]
      · -- a leading digit
        have hpn : psig n.val x.val d.val (i.val + 1) = d.val.take (i.val + 1) := by
          simp [psig, show i.val + 1 < n.val by omega]
        simp only [hlt, hov, hlast, h1, hvl, _root_.dite_true, _root_.ite_true, _root_.ite_false,
          loopCls_cont, UScalar.ofNatCore_val_eq, alloc.vec.Vec.from_val]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        rw [hv, hpv, hpn, take_succ_of_lt' h1, List.append_assoc]
    · simp only [hlt, _root_.ite_false, loopCls_done]
      refine ⟨v, rfl, ?_⟩
      rw [hv]
      simp [psig, show i.val = n.val by omega]
  · simp only [usz_lit_val]
    refine ⟨by omega, ?_⟩
    simp [psig, show 0 < n.val by omega]

theorem push_signed_eq (v : alloc.vec.Vec U8) (x : I64) (n : Usize) (hn1 : 1 ≤ n.val)
    (hn : n.val ≤ 20) (h : v.val.length + n.val < Usize.max) :
    cbact04c_t.push_signed v x n =
      .ok (alloc.vec.Vec.from (v.val ++ sdigs n.val x.val) (by
        simp only [List.length_append, sdigs_length _ _ hn1]; omega)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.push_signed, digits_of_eq x n hn, wp_bind, wp_ok]
  have hneg : decide (x < 0#i64) = decide (x.val < 0) := by
    simp only [IScalar.lt_equiv, isz_lit_val]
  rw [hneg]
  refine wp_mono (push_signed_loop_spec v x n _ hn1 (by simp) h) ?_
  rintro _ ⟨w, rfl, hw⟩
  simp only [Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hw]

/-- The display line of a category record (`display_tcat`): the account id (11 digits), the type,
the category (4 digits), the balance (11 digits, overpunched sign), the filler. -/
def tcatLine (r : cbact04c_t.TranCatBalRecord) : List U8 :=
  digs 11 r.trancat_acct_id.val.natAbs ++ r.trancat_type_cd.val ++ digs 4 r.trancat_cd.val.natAbs ++
    sdigs 11 r.tran_cat_bal.val ++ r.filler1.val

theorem tcatLine_length (r : cbact04c_t.TranCatBalRecord) : (tcatLine r).length = 50 := by
  simp [tcatLine, digs_length, sdigs_length]

theorem display_tcat_eq (r : cbact04c_t.TranCatBalRecord) :
    cbact04c_t.display_tcat r =
      .ok (alloc.vec.Vec.from (tcatLine r) (by rw [tcatLine_length]; have := usize_max_ge; omega)) := by
  have hm := usize_max_ge
  have h2 : r.trancat_type_cd.val.length = 2 := r.trancat_type_cd.property
  have h22 : r.filler1.val.length = 22 := r.filler1.property
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.display_tcat]
  rw [push_digits_eq _ _ _ (by simp) (by simp; omega)]
  simp only [wp_bind, wp_ok, wp_lift, Std.Array.to_slice]
  rw [push_bytes_eq _ _ (by simp [digs_length, h2]; omega)]
  simp only [wp_ok]
  rw [push_digits_eq _ _ _ (by simp) (by simp [digs_length, h2]; omega)]
  simp only [wp_ok]
  rw [push_signed_eq _ _ _ (by simp) (by simp) (by simp [digs_length, h2]; omega)]
  simp only [wp_ok]
  rw [push_bytes_eq _ _ (by simp [digs_length, sdigs_length, h2, h22]; omega)]
  simp only [wp_ok, alloc.vec.Vec.from_val, Slice.from_val,
    tcatLine, List.append_assoc, List.nil_append, usz_lit_val]

/-! ## The searches (index of the first match, or the length) -/

/-- A natural number as a `usize` (an index or a length). -/
def usz (k : Nat) : Usize := ⟨BitVec.ofNat _ k⟩

theorem usz_val (k : Nat) (h : k ≤ Usize.max) : (usz k).val = k := by
  have h2 : k < 2 ^ UScalarTy.Usize.numBits := by
    rw [UScalar.lt_pow_iff_le_max, UScalar.max_USize_eq]; exact h
  show (BitVec.ofNat _ k).toNat = k
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]

/-- The search invariant: either the first match was found before `i`, or there is none before
`i` and the result is still the length. -/
def SearchInv {α : Type _} (xs : List α) (p : α → Bool) (i res : Nat) : Prop :=
  (res < i ∧ res = xs.findIdx p) ∨ (res = xs.length ∧ i ≤ xs.findIdx p)

theorem searchInv_zero {α : Type _} (xs : List α) (p : α → Bool) : SearchInv xs p 0 xs.length :=
  Or.inr ⟨rfl, Nat.zero_le _⟩

theorem searchInv_step {α : Type _} (xs : List α) (p : α → Bool) (i res : Nat) (hi : i < xs.length)
    (h : SearchInv xs p i res) :
    SearchInv xs p (i + 1) (if res = xs.length then (if p xs[i] then i else res) else res) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : res ≠ xs.length := by omega
    simp only [this, _root_.ite_false]
    exact Or.inl ⟨by omega, h2⟩
  · simp only [h1, _root_.ite_true]
    by_cases hp : p xs[i] = true
    · simp only [hp, _root_.ite_true]
      refine Or.inl ⟨by omega, ?_⟩
      symm
      rw [List.findIdx_eq hi]
      refine ⟨hp, fun j hj => ?_⟩
      exact List.not_of_lt_findIdx (by omega)
    · simp only [hp, Bool.false_eq_true, _root_.ite_false]
      refine Or.inr ⟨rfl, ?_⟩
      rcases Nat.lt_or_ge i (xs.findIdx p) with h3 | h3
      · omega
      · have he : xs.findIdx p = i := by omega
        exfalso; apply hp
        have := List.findIdx_getElem (p := p) (xs := xs) (w := by omega)
        simp only [he] at this
        exact this

theorem searchInv_exit {α : Type _} (xs : List α) (p : α → Bool) (res : Nat)
    (h : SearchInv xs p xs.length res) : res = xs.findIdx p := by
  rcases h with ⟨_, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · have := List.findIdx_le_length (p := p) (xs := xs); omega

theorem find_account_eq (accounts : alloc.vec.Vec cbact04c_t.AccountRecord) (id : I64) :
    cbact04c_t.find_account accounts id =
      .ok (usz (accounts.val.findIdx (fun r => r.acct_id.val == id.val))) := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.find_account, cbact04c_t.find_account_loop]
  have hlen : accounts.val.length ≤ Usize.max := accounts.property
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ accounts.val.length ∧
      SearchInv accounts.val (fun r => r.acct_id.val == id.val) s.2.val s.1.val)
    (fun s => accounts.val.length - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro res i hinv
    obtain ⟨hi, hs⟩ := hinv
    simp only [cbact04c_t.find_account_loop.body]
    aeneas_wp [usz_lit_val]
    by_cases hlt : i.val < accounts.val.length
    · have hov : i.val + 1 ≤ Usize.max := by omega
      have hstep := searchInv_step _ _ _ _ hlt hs
      simp only [hlt, hov, _root_.dite_true, _root_.ite_true, loopCls_cont, UScalar.ofNatCore_val_eq]
      simp only [beq_iff_eq] at hstep
      split_ifs at hstep ⊢ <;> exact ⟨⟨by omega, hstep⟩, by omega⟩
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq]
      apply UScalar.eq_of_val_eq
      rw [usz_val _ (le_trans List.findIdx_le_length hlen)]
      exact searchInv_exit _ _ _ (by rw [show accounts.val.length = i.val by omega]; exact hs)
  · refine ⟨by simp, ?_⟩
    simp only [usz_lit_val, alloc.vec.Vec.len_val]
    exact searchInv_zero _ _

theorem find_xref_eq (xrefs : Slice cbact04c_t.CardXrefRecord) (id : I64) :
    cbact04c_t.find_xref xrefs id =
      .ok (usz (xrefs.val.findIdx (fun r => r.xref_acct_id.val == id.val))) := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.find_xref, cbact04c_t.find_xref_loop]
  have hlen : xrefs.val.length ≤ Usize.max := by scalar_tac
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ xrefs.val.length ∧
      SearchInv xrefs.val (fun r => r.xref_acct_id.val == id.val) s.2.val s.1.val)
    (fun s => xrefs.val.length - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro res i hinv
    obtain ⟨hi, hs⟩ := hinv
    simp only [cbact04c_t.find_xref_loop.body]
    aeneas_wp [usz_lit_val]
    by_cases hlt : i.val < xrefs.val.length
    · have hov : i.val + 1 ≤ Usize.max := by omega
      have hstep := searchInv_step _ _ _ _ hlt hs
      simp only [hlt, hov, _root_.dite_true, _root_.ite_true, loopCls_cont, UScalar.ofNatCore_val_eq]
      simp only [beq_iff_eq] at hstep
      split_ifs at hstep ⊢ <;> exact ⟨⟨by omega, hstep⟩, by omega⟩
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq]
      apply UScalar.eq_of_val_eq
      rw [usz_val _ (le_trans List.findIdx_le_length hlen)]
      exact searchInv_exit _ _ _ (by rw [show xrefs.val.length = i.val by omega]; exact hs)
  · refine ⟨by simp, ?_⟩
    simp only [usz_lit_val, Slice.len_val]
    exact searchInv_zero _ _

/-- The key test of `find_disc`: group, type and category. -/
def discKey (group : Std.Array U8 10#usize) (typ : Std.Array U8 2#usize) (cat : I64)
    (r : cbact04c_t.DisGroupRecord) : Bool :=
  decide (r.dis_acct_group_id.val = group.val) && decide (r.dis_tran_type_cd.val = typ.val) &&
    (r.dis_tran_cat_cd.val == cat.val)

theorem find_disc_eq (discs : Slice cbact04c_t.DisGroupRecord) (group : Std.Array U8 10#usize)
    (typ : Std.Array U8 2#usize) (cat : I64) :
    cbact04c_t.find_disc discs group typ cat =
      .ok (usz (discs.val.findIdx (discKey group typ cat))) := by
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.find_disc, cbact04c_t.find_disc_loop]
  have hlen : discs.val.length ≤ Usize.max := by scalar_tac
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ discs.val.length ∧
      SearchInv discs.val (discKey group typ cat) s.2.val s.1.val)
    (fun s => discs.val.length - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro res i hinv
    obtain ⟨hi, hs⟩ := hinv
    simp only [cbact04c_t.find_disc_loop.body]
    aeneas_wp [usz_lit_val, eq10_eq, eq2_eq]
    by_cases hlt : i.val < discs.val.length
    · have hov : i.val + 1 ≤ Usize.max := by omega
      have hstep := searchInv_step _ _ _ _ hlt hs
      simp only [hlt, hov, _root_.dite_true, _root_.ite_true, loopCls_cont, UScalar.ofNatCore_val_eq]
      simp only [discKey, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hstep
      by_cases hA : discs.val[i.val].dis_acct_group_id.val = group.val <;>
      by_cases hB : discs.val[i.val].dis_tran_type_cd.val = typ.val <;>
      by_cases hC : discs.val[i.val].dis_tran_cat_cd.val = cat.val <;>
      simp only [hA, hB, hC, and_self, and_true, and_false, _root_.ite_true,
        _root_.ite_false] at hstep ⊢ <;>
      split_ifs at hstep ⊢ <;> exact ⟨⟨by omega, hstep⟩, by omega⟩
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq]
      apply UScalar.eq_of_val_eq
      rw [usz_val _ (le_trans List.findIdx_le_length hlen)]
      exact searchInv_exit _ _ _ (by rw [show discs.val.length = i.val by omega]; exact hs)
  · refine ⟨by simp, ?_⟩
    simp only [usz_lit_val, Slice.len_val]
    exact searchInv_zero _ _

/-! ## The transaction record -/

/-- The DB2 timestamp of a clock reading (`make_timestamp`), in Latin-1 bytes. -/
def tsList (c : List U8) : List U8 :=
  [c.getD 0 0#u8, c.getD 1 0#u8, c.getD 2 0#u8, c.getD 3 0#u8, 45#u8, c.getD 4 0#u8, c.getD 5 0#u8,
    45#u8, c.getD 6 0#u8, c.getD 7 0#u8, 45#u8, c.getD 8 0#u8, c.getD 9 0#u8, 46#u8,
    c.getD 10 0#u8, c.getD 11 0#u8, 46#u8, c.getD 12 0#u8, c.getD 13 0#u8, 46#u8,
    c.getD 14 0#u8, c.getD 15 0#u8, 48#u8, 48#u8, 48#u8, 48#u8]

def tsArr (clock : Std.Array U8 21#usize) : Std.Array U8 26#usize :=
  Std.Array.from (tsList clock.val) (by simp [tsList])

/-- `a[i]` for an array, the bound against the array's size. -/
theorem arr_index_n {α : Type _} {n : Usize} (a : Std.Array α n) (i : Usize) :
    Std.Array.index_usize a i =
      if h : i.val < n.val then .ok (a.val[i.val]'(by rw [a.property]; exact h))
      else .fail .arrayOutOfBounds := by
  rw [arr_index_eq]
  have hl : a.val.length = n.val := a.property
  by_cases h : i.val < n.val
  · rw [dite_eq_left (by omega), dite_eq_left h]
  · rw [dite_eq_right (by omega), dite_eq_right h]

/-- `a[i] = x` for an array, as `Array.set`. -/
theorem arr_update_set {α : Type _} {n : Usize} (a : Std.Array α n) (i : Usize) (x : α) :
    Std.Array.update a i x = if i.val < n.val then .ok (a.set i x) else .fail .arrayOutOfBounds := by
  rw [arr_update_eq]
  have hl : a.val.length = n.val := a.property
  by_cases h : i.val < n.val
  · rw [dite_eq_left (by omega), ite_eq_left h]; rfl
  · rw [dite_eq_right (by omega), ite_eq_right h]

set_option maxHeartbeats 1000000 in
theorem make_timestamp_eq (clock : Std.Array U8 21#usize) :
    cbact04c_t.make_timestamp clock = .ok (tsArr clock) := by
  have hc : clock.val.length = 21 := clock.property
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.make_timestamp]
  aeneas_wp [arr_index_n, arr_update_set, usz_lit_val]
  simp only [Except.ok.injEq, Std.Array.eq_iff, Std.Array.set_val_eq, Std.Array.repeat_val, tsArr,
    Std.Array.from_val, usz_lit_val]
  simp only [tsList, List.replicate_succ, List.replicate_zero, List.set_cons_zero, List.set_cons_succ]
  simp (disch := omega) only [List.getD_eq_getElem]

/-- One step of a copy loop `a[off + p] = src[p]`. -/
theorem copy_step {α : Type _} (orig src : List α) (off p : Nat) (hp : p < src.length)
    (ho : off + p < orig.length) :
    (orig.take off ++ src.take p ++ orig.drop (off + p)).set (off + p) src[p] =
      orig.take off ++ src.take (p + 1) ++ orig.drop (off + p + 1) := by
  have h1 : (orig.take off).length = off := by simp; omega
  have h2 : (src.take p).length = p := by simp; omega
  rw [List.append_assoc, List.set_append_right _ _ (by omega), h1, Nat.add_sub_cancel_left,
    List.set_append_right _ _ (by omega), h2, Nat.sub_self, List.drop_eq_getElem_cons ho,
    List.set_cons_zero, take_succ_of_lt' hp]
  simp only [List.append_assoc, List.singleton_append]

theorem build_tran_loop0_spec (parm : Std.Array U8 10#usize) (tid : Std.Array U8 16#usize) :
    wp (cbact04c_t.build_tran_loop0 parm tid 0#usize)
      (fun o => ∃ t, o = .ok t ∧ t.val = parm.val ++ tid.val.drop 10) := by
  have hp : parm.val.length = 10 := parm.property
  have ht : tid.val.length = 16 := tid.property
  simp only [cbact04c_t.build_tran_loop0]
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ 10 ∧ s.1.val = tid.val.take 0 ++ parm.val.take s.2.val ++ tid.val.drop (0 + s.2.val))
    (fun s => 10 - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro a p hinv
    obtain ⟨hi, ha⟩ := hinv
    simp only [cbact04c_t.build_tran_loop0.body]
    aeneas_wp [arr_index_n, arr_update_set, usz_lit_val]
    by_cases h : p.val < 10
    · have hov : p.val + 1 ≤ Usize.max := by have := usize_max_ge; omega
      have hp16 : p.val < 16 := by omega
      simp only [h, hp16, hov, _root_.ite_true, _root_.dite_true, loopCls_cont, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [Std.Array.set_val_eq, ha]
      have := copy_step tid.val parm.val 0 p.val (by omega) (by omega)
      simp only [Nat.zero_add] at this ⊢
      exact this
    · simp only [h, _root_.ite_false, loopCls_done]
      refine ⟨a, rfl, ?_⟩
      rw [ha, show p.val = 10 by omega]
      simp [List.take_of_length_le (show parm.val.length ≤ 10 by omega)]
  · simp

theorem build_tran_loop1_spec (tid : Std.Array U8 16#usize) (sd : alloc.vec.Vec U8)
    (hsd : sd.val.length = 6) :
    wp (cbact04c_t.build_tran_loop1 tid sd 0#usize)
      (fun o => ∃ t, o = .ok t ∧ t.val = tid.val.take 10 ++ sd.val) := by
  have ht : tid.val.length = 16 := tid.property
  simp only [cbact04c_t.build_tran_loop1]
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ 6 ∧ s.1.val = tid.val.take 10 ++ sd.val.take s.2.val ++ tid.val.drop (10 + s.2.val))
    (fun s => 6 - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro a q hinv
    obtain ⟨hi, ha⟩ := hinv
    simp only [cbact04c_t.build_tran_loop1.body]
    aeneas_wp [arr_index_n, arr_update_set, usz_lit_val]
    by_cases h : q.val < 6
    · have hm := usize_max_ge
      ifs_omega
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [Std.Array.set_val_eq, ha, UScalar.ofNatCore_val_eq]
      exact copy_step tid.val sd.val 10 q.val (by omega) (by omega)
    · simp only [h, _root_.ite_false, loopCls_done]
      refine ⟨a, rfl, ?_⟩
      rw [ha, show q.val = 6 by omega, List.take_of_length_le (l := sd.val) (by omega),
        List.drop_of_length_le (l := tid.val) (by omega), List.append_nil]
  · simp

theorem build_tran_loop2_spec (pre : Std.Array U8 13#usize) (desc : Std.Array U8 100#usize) :
    wp (cbact04c_t.build_tran_loop2 pre desc 0#usize)
      (fun o => ∃ t, o = .ok t ∧ t.val = pre.val ++ desc.val.drop 13) := by
  have hp : pre.val.length = 13 := pre.property
  have ht : desc.val.length = 100 := desc.property
  simp only [cbact04c_t.build_tran_loop2]
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ 13 ∧ s.1.val = desc.val.take 0 ++ pre.val.take s.2.val ++ desc.val.drop (0 + s.2.val))
    (fun s => 13 - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro a p hinv
    obtain ⟨hi, ha⟩ := hinv
    simp only [cbact04c_t.build_tran_loop2.body]
    aeneas_wp [arr_index_n, arr_update_set, usz_lit_val]
    by_cases h : p.val < 13
    · have hm := usize_max_ge
      ifs_omega
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [Std.Array.set_val_eq, ha]
      have := copy_step desc.val pre.val 0 p.val (by omega) (by omega)
      simp only [Nat.zero_add] at this ⊢
      exact this
    · simp only [h, _root_.ite_false, loopCls_done]
      refine ⟨a, rfl, ?_⟩
      rw [ha, show p.val = 13 by omega]
      simp [List.take_of_length_le (show pre.val.length ≤ 13 by omega)]
  · simp

theorem build_tran_loop3_spec (desc : Std.Array U8 100#usize) (ad : alloc.vec.Vec U8)
    (had : ad.val.length = 11) :
    wp (cbact04c_t.build_tran_loop3 desc ad 0#usize)
      (fun o => ∃ t, o = .ok t ∧ t.val = desc.val.take 13 ++ ad.val ++ desc.val.drop 24) := by
  have ht : desc.val.length = 100 := desc.property
  simp only [cbact04c_t.build_tran_loop3]
  refine wp_loop (loop_shape _)
    (fun s => s.2.val ≤ 11 ∧ s.1.val = desc.val.take 13 ++ ad.val.take s.2.val ++ desc.val.drop (13 + s.2.val))
    (fun s => 11 - s.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro a q hinv
    obtain ⟨hi, ha⟩ := hinv
    simp only [cbact04c_t.build_tran_loop3.body]
    aeneas_wp [arr_index_n, arr_update_set, usz_lit_val]
    by_cases h : q.val < 11
    · have hm := usize_max_ge
      ifs_omega
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [Std.Array.set_val_eq, ha, UScalar.ofNatCore_val_eq]
      exact copy_step desc.val ad.val 13 q.val (by omega) (by omega)
    · simp only [h, _root_.ite_false, loopCls_done]
      refine ⟨a, rfl, ?_⟩
      rw [ha, show q.val = 11 by omega, List.take_of_length_le (l := ad.val) (by omega)]
  · simp

/-- `Int. for a/c ` in Latin-1 bytes. -/
def descPre : List U8 :=
  [73#u8, 110#u8, 116#u8, 46#u8, 32#u8, 102#u8, 111#u8, 114#u8, 32#u8, 97#u8, 47#u8, 99#u8, 32#u8]

/-- The interest transaction `build_tran` returns. -/
def tranOf (prev : cbact04c_t.TranRecord) (parm : Std.Array U8 10#usize) (suffix acct amt : I64)
    (card : Std.Array U8 16#usize) (clock : Std.Array U8 21#usize) : cbact04c_t.TranRecord :=
  { prev with
    tran_id := Std.Array.from (parm.val ++ digs 6 suffix.val.natAbs)
      (by simp only [List.length_append, digs_length, parm.property]; rfl)
    tran_type_cd := Std.Array.make 2#usize [48#u8, 49#u8]
    tran_cat_cd := 5#i64
    tran_source := Std.Array.make 10#usize
      [83#u8, 121#u8, 115#u8, 116#u8, 101#u8, 109#u8, 32#u8, 32#u8, 32#u8, 32#u8]
    tran_desc := Std.Array.from (descPre ++ digs 11 acct.val.natAbs ++ prev.tran_desc.val.drop 24)
      (by simp only [List.length_append, digs_length, List.length_drop, prev.tran_desc.property,
            descPre, List.length_cons, List.length_nil]; rfl)
    tran_amt := amt
    tran_merchant_id := 0#i64
    tran_merchant_name := Std.Array.repeat 50#usize 32#u8
    tran_merchant_city := Std.Array.repeat 50#usize 32#u8
    tran_merchant_zip := Std.Array.repeat 10#usize 32#u8
    tran_card_num := card
    tran_orig_ts := tsArr clock
    tran_proc_ts := tsArr clock }

theorem build_tran_eq (prev : cbact04c_t.TranRecord) (parm : Std.Array U8 10#usize)
    (suffix acct amt : I64) (card : Std.Array U8 16#usize) (clock : Std.Array U8 21#usize) :
    cbact04c_t.build_tran prev parm suffix acct amt card clock =
      .ok (tranOf prev parm suffix acct amt card clock) := by
  have hp : parm.val.length = 10 := parm.property
  have hd : prev.tran_desc.val.length = 100 := prev.tran_desc.property
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.build_tran, wp_bind]
  refine wp_mono (build_tran_loop0_spec parm _) ?_
  rintro _ ⟨t1, rfl, ht1⟩
  simp only [wp_ok, digits_of_eq suffix 6#usize (by simp)]
  refine wp_mono (build_tran_loop1_spec t1 _ (by simp [digs_length])) ?_
  rintro _ ⟨t2, rfl, ht2⟩
  simp only []
  refine wp_mono (build_tran_loop2_spec _ _) ?_
  rintro _ ⟨t3, rfl, ht3⟩
  simp only [wp_ok, digits_of_eq acct 11#usize (by simp)]
  refine wp_mono (build_tran_loop3_spec t3 _ (by simp [digs_length])) ?_
  rintro _ ⟨t4, rfl, ht4⟩
  simp only [wp_ok, make_timestamp_eq, Except.ok.injEq, tranOf, cbact04c_t.TranRecord.mk.injEq,
    Std.Array.eq_iff, Std.Array.from_val, and_true, true_and]
  refine ⟨?_, ?_⟩
  · rw [ht2, ht1, List.take_left' hp, alloc.vec.Vec.from_val, usz_lit_val]
  · rw [ht4, ht3, alloc.vec.Vec.from_val, usz_lit_val]
    have hpre : ∀ h, (Std.Array.make 13#usize
        [73#u8, 110#u8, 116#u8, 46#u8, 32#u8, 102#u8, 111#u8, 114#u8, 32#u8, 97#u8, 47#u8, 99#u8, 32#u8]
        h).val = descPre := fun _ => rfl
    rw [hpre]
    have hl : descPre.length = 13 := rfl
    rw [List.take_left' hl, List.drop_append, hl, List.drop_drop]
    simp
    all_goals (rw [hl]; omega)

/-! ## 1050-UPDATE-ACCOUNT -/

/-- The account record with interest `total` posted: balance plus interest, truncated to 12 digits;
cycle credit and debit 0. -/
def postedR (a : cbact04c_t.AccountRecord) (total : I64) : cbact04c_t.AccountRecord :=
  { a with acct_curr_bal := ⟨BitVec.ofInt _ (Int.tmod (a.acct_curr_bal.val + total.val) (10 ^ 12))⟩,
           acct_curr_cyc_credit := 0#i64, acct_curr_cyc_debit := 0#i64 }

theorem update_account_eq (st : cbact04c_t.State) (out : cbact04c_t.Output)
    (hb : -9223372036854775808 ≤ st.account_record.acct_curr_bal.val + st.total_int.val ∧
      st.account_record.acct_curr_bal.val + st.total_int.val ≤ 9223372036854775807)
    (hf : ∃ a ∈ st.accounts.val, a.acct_id.val = st.account_record.acct_id.val)
    (hr : out.account_file_rewrites.val.length < Usize.max) :
    cbact04c_t.update_account st out =
      .ok (true,
        { st with
          accounts := st.accounts.set
            (usz (st.accounts.val.findIdx (fun r => r.acct_id.val == st.account_record.acct_id.val)))
            (postedR st.account_record st.total_int),
          account_record := postedR st.account_record st.total_int },
        { out with
          account_file_rewrites := alloc.vec.Vec.from
            (out.account_file_rewrites.val ++ [postedR st.account_record st.total_int])
            (by simp; omega) }) := by
  have hlen : st.accounts.val.length ≤ Usize.max := st.accounts.property
  have hlt : st.accounts.val.findIdx (fun r => r.acct_id.val == st.account_record.acct_id.val) <
      st.accounts.val.length := by
    rw [List.findIdx_lt_length]
    obtain ⟨a, ha, he⟩ := hf
    exact ⟨a, ha, by simp [he]⟩
  refine eq_ok_of_wp' ?_
  simp only [cbact04c_t.update_account]
  aeneas_wp [find_account_eq, trunc_digits_eq, alloc.vec.Vec.index_mut_slice_index,
    alloc.vec.Vec.index_mut_usize, usz_lit_val]
  have hu := usz_val _ (le_trans (Nat.le_of_lt hlt) hlen)
  simp only [hu]
  ifs_omega
  simp only [postedR, tmodI, IScalar.ofInt_val_eq]

end EquivLean.Modernize.Cbact04c.Rust

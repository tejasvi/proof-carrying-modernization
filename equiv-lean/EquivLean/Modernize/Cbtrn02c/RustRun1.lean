import EquivLean.Modernize.Cbtrn02c.RustSpec
import EquivLean.Bridge.Aeneas.Tactic

/-!
# CBTRN02C → Rust: generic lemmas (copied from `Cbact04c/RustRun1.lean` and `RustRun2.lean`)
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

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
macro "omega_ifs" : tactic =>
  `(tactic| simp (disch := omega) only [dite_eq_left, ite_eq_left, dite_eq_right, ite_eq_right])

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

theorem digs_take_pred (n x : Nat) (hn : 1 ≤ n) : (digs n x).take (n - 1) = digs (n - 1) (x / 10) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [digs_succ_right, Nat.add_sub_cancel, List.take_append_of_le_length (by simp [digs_length]),
    List.take_of_length_le (by simp [digs_length])]

theorem overpunch_lt (neg : Bool) (d : Nat) (hd : d < 10) : overpunch neg d < 256 := by
  unfold overpunch; split_ifs <;> omega

/-- A natural number as a `usize` (an index or a length). -/
def usz (k : Nat) : Usize := ⟨BitVec.ofNat _ k⟩

theorem usz_val (k : Nat) (h : k ≤ Usize.max) : (usz k).val = k := by
  have h2 : k < 2 ^ UScalarTy.Usize.numBits := by
    rw [UScalar.lt_pow_iff_le_max, UScalar.max_USize_eq]; exact h
  show (BitVec.ofNat _ k).toNat = k
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]

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

/-! ## CP037 round trips -/

theorem cp037_rt : ∀ n : Fin 256, cp037Code (ebcdicOfLatin1 n.val) = n.val := by
  decide +kernel

theorem latin_rt_fin : ∀ n : Fin 256,
    ebcdicOfLatin1 (latin1OfEbcdic (UInt8.ofNat n.val)) = UInt8.ofNat n.val := by
  decide +kernel

theorem latin_rt (b : UInt8) : ebcdicOfLatin1 (latin1OfEbcdic b) = b := by
  have h := latin_rt_fin ⟨b.toNat, b.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  exact h

/-- The EBCDIC byte of a Rust byte. -/
abbrev ebc (u : U8) : UInt8 := ebcdicOfLatin1 u.val

theorem cp037_ebc (u : U8) : cp037Code (ebc u) = u.val :=
  cp037_rt ⟨u.val, by have := u.hBounds; simpa using this⟩

/-- The Latin-1 bytes of an alphanumeric field are the CP037 text of its EBCDIC bytes. -/
theorem latin1_text (l : List U8) : (l.map ebc).map cp037Code = l.map UScalar.val := by
  rw [List.map_map]
  exact List.map_congr_left fun u _ => cp037_ebc u

theorem ebc_inj {u v : U8} (h : ebc u = ebc v) : u = v := by
  apply UScalar.eq_of_val_eq
  rw [← cp037_ebc u, ← cp037_ebc v, h]

theorem map_ebc_inj {l1 l2 : List U8} : l1.map ebc = l2.map ebc ↔ l1 = l2 :=
  ⟨fun h => List.map_injective_iff.2 (fun _ _ => ebc_inj) h, fun h => h ▸ rfl⟩

theorem cp037Code_inj {a b : UInt8} (h : cp037Code a = cp037Code b) : a = b := by
  have ha := latin_rt a
  have hb := latin_rt b
  have e : latin1OfEbcdic a = latin1OfEbcdic b := h
  rw [← ha, ← hb, e]

theorem map_cp037_inj {l1 l2 : List UInt8} (h : l1.map cp037Code = l2.map cp037Code) : l1 = l2 :=
  List.map_injective_iff.2 (fun _ _ => cp037Code_inj) h

/-! ## Digits -/

theorem digs_val (n v : Nat) : (digs n v).map UScalar.val = zpad n v := by
  simp only [digs, zpad, List.map_map]
  apply List.map_congr_left
  intro e he
  have := Cobol.Digits.toDigits_lt (by decide) n v e he
  simp only [Function.comp_apply]
  rw [byt_val _ (by omega)]

theorem sdigs_val (n : Nat) (v : Int) :
    (sdigs n v).map UScalar.val =
      zpad (n - 1) (v.natAbs / 10) ++ [overpunch (decide (v < 0)) (v.natAbs % 10)] := by
  simp only [sdigs, List.map_append, digs_val, List.map_cons, List.map_nil]
  rw [byt_val _ (overpunch_lt _ _ (Nat.mod_lt _ (by norm_num)))]

/-- The EBCDIC digits of an unsigned DISPLAY field are the EBCDIC bytes of its Latin-1 digits. -/
theorem digs_ebc {fmt : NumFmt} (hu : fmt.usage = .display) (hs : fmt.signed = false)
    (hd : 0 < fmt.digits) (v : Int) :
    (digs fmt.digits v.natAbs).map ebc = encodeNum {} fmt v := by
  apply map_cp037_inj
  rw [latin1_text, digs_val, text_unsigned hu hs hd]

theorem getD_ebc (c : List U8) (k : Nat) :
    ebc (c.getD k 0#u8) = ebcdicOfLatin1 ((c.map UScalar.val).getD k 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases c[k]? <;> rfl

theorem tsList_ebc (clock : Std.Array U8 21#usize) (clk : List UInt8)
    (hclk : clock.val.map (·.val) = rustLine clk) (hlen : clk.length = 21) :
    (tsList clock.val).map ebc = CardDemo.Cbtrn02c.db2ts clk := by
  have key : ∀ k, ebc (clock.val.getD k 0#u8) = ebcdicOfLatin1 ((rustLine clk).getD k 0) := by
    intro k; rw [getD_ebc]; congr 2
  simp only [tsList, List.map_cons, List.map_nil, key]
  match clk, hlen with
  | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20], _ =>
    have e45 : ebc 45#u8 = 96 := by decide +kernel
    have e46 : ebc 46#u8 = 75 := by decide +kernel
    have e48 : ebc 48#u8 = 240 := by decide +kernel
    simp only [rustLine, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero,
      latin_rt, CardDemo.Cbtrn02c.db2ts, e45, e46, e48, List.take_succ_cons, List.drop_succ_cons,
      List.take_zero, List.cons_append, List.nil_append, List.drop_zero]


end EquivLean.Modernize.Cbtrn02c.Rust

/-!
# CBTRN02C → Rust: the helper functions
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Rust

/-! ## Byte copies -/

theorem push_bytes_loop_spec (s : Slice U8) (v0 : alloc.vec.Vec U8)
    (h : v0.val.length + s.val.length ≤ Usize.max) :
    wp (loop (fun (v1, i1) => cbtrn02c.push_bytes_loop.body s v1 i1) (v0, 0#usize))
      (fun o => o = .ok (alloc.vec.Vec.from (v0.val ++ s.val) (by simp; omega))) := by
  refine wp_loop (loop_shape _)
    (fun x => x.2.val ≤ s.val.length ∧ x.1.val = v0.val ++ s.val.take x.2.val)
    (fun x => s.val.length - x.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro v i hinv
    obtain ⟨hi, hv⟩ := hinv
    simp only [cbtrn02c.push_bytes_loop.body]
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

theorem push_bytes_eq (dst : alloc.vec.Vec U8) (src : Slice U8)
    (h : dst.val.length + src.val.length ≤ Usize.max) :
    cbtrn02c.push_bytes dst src = .ok (alloc.vec.Vec.from (dst.val ++ src.val) (by simp; omega)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.push_bytes, cbtrn02c.push_bytes_loop]
  exact push_bytes_loop_spec src dst h

theorem lit_eq (s : Slice U8) :
    cbtrn02c.lit s = .ok (alloc.vec.Vec.from s.val (by scalar_tac)) := by
  have hs : s.val.length ≤ Usize.max := by scalar_tac
  simp only [cbtrn02c.lit]
  rw [push_bytes_eq _ _ (by simpa using hs)]
  simp

theorem run_loop0_eq (s : Slice cbtrn02c.AccountRecord) :
    cbtrn02c.run_loop0 s (alloc.vec.Vec.new cbtrn02c.AccountRecord) 0#usize =
      .ok (alloc.vec.Vec.from s.val (by scalar_tac)) := by
  have hs : s.val.length ≤ Usize.max := by scalar_tac
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop0]
  refine wp_loop (loop_shape _)
    (fun x => x.2.val ≤ s.val.length ∧ x.1.val = s.val.take x.2.val)
    (fun x => s.val.length - x.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro v i hinv
    obtain ⟨hi, hv⟩ := hinv
    simp only [cbtrn02c.run_loop0.body]
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

theorem run_loop1_eq (s : Slice cbtrn02c.TranCatBalRecord) :
    cbtrn02c.run_loop1 s 0#usize (alloc.vec.Vec.new cbtrn02c.TranCatBalRecord) =
      .ok (alloc.vec.Vec.from s.val (by scalar_tac)) := by
  have hs : s.val.length ≤ Usize.max := by scalar_tac
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.run_loop1]
  refine wp_loop (loop_shape _)
    (fun x => x.1.val ≤ s.val.length ∧ x.2.val = s.val.take x.1.val)
    (fun x => s.val.length - x.1.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro i v hinv
    obtain ⟨hi, hv⟩ := hinv
    simp only [cbtrn02c.run_loop1.body]
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

theorem abs_u64_eq (v : I64) : cbtrn02c.abs_u64 v = .ok (absU v) := by
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.abs_u64]
  have hb := v.hBounds
  simp only [IScalarTy.I64_numBits_eq] at hb
  aeneas_wp [isz_lit_val, usz_lit_val]
  split_ifs with h1 h2 h3 h4
  all_goals first
    | (exfalso; omega)
    | (simp only [Except.ok.injEq]
       apply UScalar.eq_of_val_eq
       simp only [UScalar.ofNatCore_val_eq, IScalar.hcast_val_eq, IScalar.ofInt_val_eq, absU,
         UScalarTy.U64_numBits_eq] at *
       omega)
    | (exfalso
       simp only [UScalar.ofNatCore_val_eq, IScalar.hcast_val_eq, IScalar.ofInt_val_eq,
         UScalarTy.U64_numBits_eq] at *
       omega)

/-! ## Digits -/

/-- Writing at the end of a run of `k + 1` copies. -/
theorem set_replicate_end' {α : Type _} (k : Nat) (a c : α) (rest : List α) :
    (List.replicate (k + 1) a ++ rest).set k c = List.replicate k a ++ [c] ++ rest := by
  rw [List.replicate_succ', List.append_assoc, List.set_append_right _ _ (by simp)]
  simp

/-- Writing the digit in front of the digits already written. -/
theorem set_mid' {α : Type _} (d i : Nat) (hi : i < d) (Z R : List α) (a c : α) :
    (List.replicate (d - i) a ++ Z ++ R).set (d - 1 - i) c =
      List.replicate (d - 1 - i) a ++ ([c] ++ Z) ++ R := by
  obtain ⟨k, hk⟩ : ∃ k, d - i = k + 1 := ⟨d - 1 - i, by omega⟩
  have hk' : d - 1 - i = k := by omega
  rw [hk, hk', List.append_assoc, set_replicate_end']
  simp

set_option maxHeartbeats 2000000 in
/-- The digit loop of `digits`: after `len` iterations, the `len` low digits of `x`, right-aligned
in the first `len` bytes of the buffer. -/
theorem digits_loop0_spec (len : Usize) (x : Nat) (m : U64) (hl : len.val ≤ 20) (hm : m.val = x) :
    wp (cbtrn02c.digits_loop0 len m (Std.Array.repeat 20#usize 48#u8) 0#usize)
      (fun o => ∃ b, o = .ok b ∧
        b.val = digs len.val x ++ List.replicate (20 - len.val) 48#u8) := by
  simp only [cbtrn02c.digits_loop0]
  refine wp_loop (loop_shape _) (fun s => s.2.2.val ≤ len.val ∧ s.1.val = x / 10 ^ s.2.2.val ∧
      s.2.1.val = List.replicate (len.val - s.2.2.val) 48#u8 ++ digs s.2.2.val x ++
        List.replicate (20 - len.val) 48#u8)
    (fun s => len.val - s.2.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro w buf k hinv
    obtain ⟨hk, hw, hbuf⟩ := hinv
    have hlen : buf.val.length = 20 := buf.property
    simp only [cbtrn02c.digits_loop0.body]
    aeneas_wp [arr_update_eq, UScalar.cast_val_eq, usz_lit_val]
    by_cases h1 : k.val < len.val
    · have hd10 : w.val % 10 < 10 := Nat.mod_lt _ (by norm_num)
      have h256 : w.val % 10 % 2 ^ 8 = w.val % 10 := Nat.mod_eq_of_lt (by omega)
      have hm := usize_max_ge
      simp only [h256]
      omega_ifs
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Std.Array.from_val]
      refine ⟨⟨by omega, ?_, ?_⟩, by omega⟩
      · rw [hw, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      · rw [hbuf, show len.val - 1 - k.val = len.val - 1 - k.val from rfl, set_mid' _ _ h1,
          digs_succ_left, show len.val - (k.val + 1) = len.val - 1 - k.val by omega]
        simp only [List.append_assoc, List.singleton_append, List.cons_append]
        congr 2
        apply UScalar.eq_of_val_eq
        rw [byt_val _ (by omega), UScalar.ofNatCore_val_eq, hw]
    · simp only [h1, _root_.ite_false, loopCls_done]
      refine ⟨buf, rfl, ?_⟩
      rw [hbuf, show k.val = len.val by omega, Nat.sub_self, List.replicate_zero, List.nil_append]
  · refine ⟨by simp, by simp [hm], ?_⟩
    simp only [Std.Array.repeat_val, usz_lit_val, UScalar.ofNatCore_val_eq, Nat.sub_zero, digs_zero,
      List.append_nil, ← List.replicate_add]
    congr 1
    omega

theorem digits_loop1_spec (len : Usize) (buf : Std.Array U8 20#usize) (hl : len.val ≤ 20) :
    wp (cbtrn02c.digits_loop1 len buf (alloc.vec.Vec.new U8) 0#usize)
      (fun o => ∃ v, o = .ok v ∧ v.val = buf.val.take len.val) := by
  have hb : buf.val.length = 20 := buf.property
  have hm := usize_max_ge
  simp only [cbtrn02c.digits_loop1]
  refine wp_loop (loop_shape _)
    (fun x => x.2.val ≤ len.val ∧ x.1.val = buf.val.take x.2.val)
    (fun x => len.val - x.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro v i hinv
    obtain ⟨hi, hv⟩ := hinv
    simp only [cbtrn02c.digits_loop1.body]
    aeneas_wp [arr_index_eq, usz_lit_val]
    by_cases hlt : i.val < len.val
    · have hvl : v.val.length < Usize.max := by
        rw [hv]; simp only [List.length_take]; omega
      have hib : i.val < buf.val.length := by omega
      omega_ifs
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq, alloc.vec.Vec.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hv, take_succ_of_lt' hib]
    · simp only [hlt, _root_.ite_false, loopCls_done]
      exact ⟨v, rfl, by rw [hv, show i.val = len.val by omega]⟩
  · simp

theorem digits_eq (v : I64) (len : Usize) (hl : len.val ≤ 20) :
    cbtrn02c.digits v len =
      .ok (alloc.vec.Vec.from (digs len.val v.val.natAbs) (by
        rw [digs_length]; have := usize_max_ge; omega)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.digits, abs_u64_eq, wp_bind, wp_ok]
  refine wp_mono (digits_loop0_spec len v.val.natAbs (absU v) hl (by simp [absU])) ?_
  rintro _ ⟨b, rfl, hb⟩
  simp only
  refine wp_mono (digits_loop1_spec len b hl) ?_
  rintro _ ⟨w, rfl, hw⟩
  simp only [Except.ok.injEq, alloc.vec.Vec.eq_iff, alloc.vec.Vec.from_val, hw, hb]
  rw [List.take_left' (digs_length _ _)]

theorem negTab_val : ∀ d : Fin 10,
    (([125#u8, 74#u8, 75#u8, 76#u8, 77#u8, 78#u8, 79#u8, 80#u8, 81#u8, 82#u8] : List U8).getD d.val
      0#u8).val = overpunch true d.val := by decide

theorem posTab_val : ∀ d : Fin 10,
    (([123#u8, 65#u8, 66#u8, 67#u8, 68#u8, 69#u8, 70#u8, 71#u8, 72#u8, 73#u8] : List U8).getD d.val
      0#u8).val = overpunch false d.val := by decide

theorem vec_index_mut_eq {α : Type _} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i =
      .ok (v.val[i.val], fun x => v.set i x) := by
  refine eq_ok_of_wp' ?_
  rw [alloc.vec.Vec.index_mut_slice_index]
  simp only [alloc.vec.Vec.index_mut_usize, wp_bind, wp_bind_tc, wp_Vec_index_usize, h,
    _root_.dite_true, wp_ok]

set_option maxHeartbeats 1000000 in
theorem signed_digits_eq (v : I64) (len : Usize) (h1 : 1 ≤ len.val) (hl : len.val ≤ 20) :
    cbtrn02c.signed_digits v len =
      .ok (alloc.vec.Vec.from (sdigs len.val v.val) (by
        rw [sdigs_length _ _ h1]; have := usize_max_ge; omega)) := by
  have hm := usize_max_ge
  have hd : (digs len.val v.val.natAbs).length = len.val := digs_length _ _
  have hlast := digs_getElem_last len.val v.val.natAbs (len.val - 1) (by omega)
  have hmod : v.val.natAbs % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hlv : (byt (48 + v.val.natAbs % 10)).val = 48 + v.val.natAbs % 10 := byt_val _ (by omega)
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.signed_digits, digits_eq v len hl, wp_bind, wp_ok]
  aeneas_wp [usz_lit_val, UScalar.cast_val_eq, arr_index_eq]
  have h10 : 10 < 2 ^ UScalarTy.Usize.numBits := by
    rw [UScalar.lt_pow_iff_le_max, UScalar.max_USize_eq]; omega
  have hdm : v.val.natAbs % 10 % 2 ^ UScalarTy.Usize.numBits = v.val.natAbs % 10 :=
    Nat.mod_eq_of_lt (by omega)
  have hlen1 : len.val - 1 < (digs len.val v.val.natAbs).length := by omega
  simp only [hlast, hlv, Nat.add_sub_cancel_left, hdm, h1, hlen1, _root_.ite_true, _root_.dite_true,
    show (48 : Nat) ≤ 48 + v.val.natAbs % 10 from by omega]
  have hset : ∀ c : U8, (digs len.val v.val.natAbs).set (len.val - 1) c =
      digs (len.val - 1) (v.val.natAbs / 10) ++ [c] := by
    intro c
    obtain ⟨k, hk⟩ : ∃ k, len.val = k + 1 := ⟨len.val - 1, by omega⟩
    rw [hk, digs_succ_right, Nat.add_sub_cancel, List.set_append_right _ _ (by simp [digs_length])]
    simp [digs_length]
  have hi : (UScalar.ofNatCore (len.val - 1) (by scalar_tac) : Usize).val <
      (alloc.vec.Vec.from (digs len.val v.val.natAbs) (by rw [digs_length]; omega)).val.length := by
    simp [digs_length]; omega
  by_cases hneg : v.val < 0
  · simp only [hneg, _root_.ite_true]
    have htl : ∀ h, (Std.Array.make 10#usize
        [125#u8, 74#u8, 75#u8, 76#u8, 77#u8, 78#u8, 79#u8, 80#u8, 81#u8, 82#u8] h).val =
        [125#u8, 74#u8, 75#u8, 76#u8, 77#u8, 78#u8, 79#u8, 80#u8, 81#u8, 82#u8] := fun _ => rfl
    simp only [htl, List.length_cons, List.length_nil, hmod, _root_.dite_true]
    rw [vec_index_mut_eq _ _ hi]
    simp only [wp_ok, Aeneas.Std.uncurry_apply_pair, Except.ok.injEq, alloc.vec.Vec.eq_iff,
      alloc.vec.Vec.set_val_eq, alloc.vec.Vec.from_val, UScalar.ofNatCore_val_eq, hset, sdigs]
    simp only [List.append_cancel_left_eq, List.cons.injEq, and_true]
    apply UScalar.eq_of_val_eq
    rw [byt_val _ (overpunch_lt _ _ hmod)]
    have := negTab_val ⟨_, hmod⟩
    rw [List.getD_eq_getElem _ _ (by simp; omega)] at this
    rw [this]
    simp [hneg]
  · simp only [hneg, _root_.ite_false]
    have htl : ∀ h, (Std.Array.make 10#usize
        [123#u8, 65#u8, 66#u8, 67#u8, 68#u8, 69#u8, 70#u8, 71#u8, 72#u8, 73#u8] h).val =
        [123#u8, 65#u8, 66#u8, 67#u8, 68#u8, 69#u8, 70#u8, 71#u8, 72#u8, 73#u8] := fun _ => rfl
    simp only [htl, List.length_cons, List.length_nil, hmod, _root_.dite_true]
    rw [vec_index_mut_eq _ _ hi]
    simp only [wp_ok, Aeneas.Std.uncurry_apply_pair, Except.ok.injEq, alloc.vec.Vec.eq_iff,
      alloc.vec.Vec.set_val_eq, alloc.vec.Vec.from_val, UScalar.ofNatCore_val_eq, hset, sdigs]
    simp only [List.append_cancel_left_eq, List.cons.injEq, and_true]
    apply UScalar.eq_of_val_eq
    rw [byt_val _ (overpunch_lt _ _ hmod)]
    have := posTab_val ⟨_, hmod⟩
    rw [List.getD_eq_getElem _ _ (by simp; omega)] at this
    rw [this]
    simp [hneg]

/-! ## `put`, `same`, `alpha76` -/

/-- `s[i] = x` for a slice. -/
theorem slice_update_eq {α : Type _} (v : Slice α) (i : Usize) (x : α) :
    Slice.update v i x = if _h : i.val < v.val.length then
      .ok (Slice.from (v.val.set i.val x) (by simp)) else .fail .arrayOutOfBounds := by
  simp only [Slice.update, Slice.getElem?_Usize_eq]
  by_cases h : i.val < v.val.length <;> simp [h]

theorem put_loop_spec (buf : Slice U8) (pos : Usize) (src : Slice U8)
    (h : pos.val + src.val.length ≤ buf.val.length) :
    wp (cbtrn02c.put_loop buf pos src 0#usize)
      (fun o => ∃ b, o = .ok b ∧
        b.val = buf.val.take pos.val ++ src.val ++ buf.val.drop (pos.val + src.val.length)) := by
  have hb : buf.val.length ≤ Usize.max := by scalar_tac
  simp only [cbtrn02c.put_loop]
  refine wp_loop (loop_shape _)
    (fun x => x.2.val ≤ src.val.length ∧
      x.1.val = buf.val.take pos.val ++ src.val.take x.2.val ++ buf.val.drop (pos.val + x.2.val))
    (fun x => src.val.length - x.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro b i hinv
    obtain ⟨hi, hbv⟩ := hinv
    have hbl : b.val.length = buf.val.length := by
      rw [hbv]; simp only [List.length_append, List.length_take, List.length_drop]; omega
    simp only [cbtrn02c.put_loop.body]
    aeneas_wp [slice_update_eq, usz_lit_val]
    by_cases hlt : i.val < src.val.length
    · omega_ifs
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Slice.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hbv]
      exact copy_step buf.val src.val pos.val i.val hlt (by omega)
    · simp only [hlt, _root_.ite_false, loopCls_done]
      refine ⟨b, rfl, ?_⟩
      rw [hbv, show i.val = src.val.length by omega, List.take_of_length_le (le_refl _)]
  · refine ⟨by simp, ?_⟩
    simp

theorem put_eq (buf : Slice U8) (pos : Usize) (src : Slice U8)
    (h : pos.val + src.val.length ≤ buf.val.length) :
    cbtrn02c.put buf pos src =
      .ok (usz (pos.val + src.val.length),
        Slice.from (buf.val.take pos.val ++ src.val ++ buf.val.drop (pos.val + src.val.length))
          (by simp; scalar_tac)) := by
  have hb : buf.val.length ≤ Usize.max := by scalar_tac
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.put, wp_bind]
  refine wp_mono (put_loop_spec buf pos src h) ?_
  rintro _ ⟨b, rfl, hbv⟩
  aeneas_wp []
  have hov : pos.val + src.val.length ≤ Usize.max := by omega
  simp only [hov, _root_.dite_true, Except.ok.injEq, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · apply UScalar.eq_of_val_eq; rw [usz_val _ hov, UScalar.ofNatCore_val_eq]
  · rw [Slice.eq_iff]
    simp [hbv]

theorem same_eq (a b : Slice U8) : cbtrn02c.same a b = .ok (decide (a.val = b.val)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.same]
  aeneas_wp []
  by_cases hl : a.val.length = b.val.length
  · simp only [hl, not_true_eq_false, _root_.ite_false]
    simp only [cbtrn02c.same_loop]
    refine wp_loop (loop_shape _)
      (fun i => i.val ≤ a.val.length ∧ a.val.take i.val = b.val.take i.val)
      (fun i => a.val.length - i.val) ?_ _ ?_
    · intro i hinv
      obtain ⟨hi, he⟩ := hinv
      simp only [cbtrn02c.same_loop.body]
      aeneas_wp [usz_lit_val]
      by_cases hlt : i.val < a.val.length
      · have hlb : i.val < b.val.length := by omega
        by_cases hx : a.val[i.val].val = b.val[i.val].val
        · have hov : i.val + 1 ≤ Usize.max := by scalar_tac
          simp only [hlt, hlb, hx, not_true_eq_false, _root_.dite_true, _root_.ite_false, hov,
            loopCls_cont, UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          rw [take_eq_take_succ hlt hlb]
          exact ⟨he, UScalar.eq_of_val_eq hx⟩
        · simp only [hlt, hlb, hx, not_false_eq_true, _root_.dite_true, _root_.ite_true,
            loopCls_done, Except.ok.injEq]
          symm
          rw [decide_eq_false_iff_not]
          intro hab
          apply hx
          rw [List.getElem_of_eq hab]
      · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq]
        have hi' : i.val = a.val.length := by omega
        rw [hi', List.take_of_length_le (le_refl _), List.take_of_length_le (by omega)] at he
        simp [he]
    · simp
  · simp only [hl, not_false_eq_true, _root_.ite_true, wp_ok, Except.ok.injEq]
    symm
    rw [decide_eq_false_iff_not]
    intro hab
    exact hl (by rw [hab])

/-- A message padded with spaces to 76 characters (`alpha76`). -/
def pad76 (s : List U8) : List U8 := s ++ List.replicate (76 - s.length) 32#u8

theorem alpha76_eq (s : Slice U8) (h : s.val.length ≤ 76) :
    cbtrn02c.alpha76 s = .ok (Std.Array.from (pad76 s.val) (by simp [pad76]; omega)) := by
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.alpha76, cbtrn02c.alpha76_loop]
  refine wp_loop (loop_shape _)
    (fun x => x.2.val ≤ s.val.length ∧
      x.1.val = s.val.take x.2.val ++ List.replicate (76 - x.2.val) 32#u8)
    (fun x => s.val.length - x.2.val) ?_ _ ?_
  · simp only [Prod.forall]
    intro r i hinv
    obtain ⟨hi, hr⟩ := hinv
    have hrl : r.val.length = 76 := r.property
    simp only [cbtrn02c.alpha76_loop.body]
    aeneas_wp [arr_update_eq, usz_lit_val]
    by_cases hlt : i.val < s.val.length
    · have hm := usize_max_ge
      omega_ifs
      simp only [loopCls_cont, UScalar.ofNatCore_val_eq, Std.Array.from_val]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hr, take_succ_of_lt' hlt]
      obtain ⟨k, hk⟩ : ∃ k, 76 - i.val = k + 1 := ⟨75 - i.val, by omega⟩
      rw [hk, List.replicate_succ, List.set_append_right _ _ (by simp only [List.length_take]; omega)]
      simp only [List.length_take, show min i.val s.val.length = i.val by omega, Nat.sub_self,
        List.set_cons_zero, List.append_assoc, List.singleton_append]
      rw [show 76 - (i.val + 1) = k by omega]
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq, Std.Array.eq_iff,
        Std.Array.from_val]
      rw [hr, show i.val = s.val.length by omega, List.take_of_length_le (le_refl _), pad76]
  · simp

/-! ## `ebcdic` and `ge_prefix` (EBCDIC collating order) -/

theorem ebcTab_fin : ∀ e : Fin 256,
    (cbtrn02c.EBC_DEC.val[e.val]?).map UScalar.val = some (latin1OfEbcdic (UInt8.ofNat e.val)) := by
  unfold cbtrn02c.EBC_DEC
  decide +kernel

theorem ebcTab_len : cbtrn02c.EBC_DEC.val.length = 256 := cbtrn02c.EBC_DEC.property

theorem ebcTab_val (e : Nat) (h : e < 256) :
    (cbtrn02c.EBC_DEC.val[e]'(by rw [ebcTab_len]; exact h)).val = latin1OfEbcdic (UInt8.ofNat e) := by
  have := ebcTab_fin ⟨e, h⟩
  rw [List.getElem?_eq_getElem (by rw [ebcTab_len]; exact h)] at this
  simpa using this

/-- The EBCDIC byte of a Latin-1 byte, as a Rust byte. -/
def ebcU (b : U8) : U8 := byt (ebcdicOfLatin1 b.val).toNat

theorem ebcU_val (b : U8) : (ebcU b).val = (ebc b).toNat := byt_val _ (UInt8.toNat_lt _)

theorem ebcdic_eq (b : U8) : cbtrn02c.ebcdic b = .ok (ebcU b) := by
  have hbl : b.val < 256 := by have := b.hBounds; simpa using this
  set E := (ebcdicOfLatin1 b.val).toNat with hEdef
  have hE : E < 256 := UInt8.toNat_lt _
  have hofE : UInt8.ofNat E = ebcdicOfLatin1 b.val := by simp [hEdef]
  have hfound : (cbtrn02c.EBC_DEC.val[E]'(by rw [ebcTab_len]; exact hE)).val = b.val := by
    rw [ebcTab_val E hE, hofE]
    exact cp037_rt ⟨b.val, hbl⟩
  have hnot : ∀ e (he : e < E), (cbtrn02c.EBC_DEC.val[e]'(by rw [ebcTab_len]; omega)).val ≠ b.val := by
    intro e he heq
    rw [ebcTab_val e (by omega)] at heq
    have h1 : ebcdicOfLatin1 (latin1OfEbcdic (UInt8.ofNat e)) = UInt8.ofNat e := latin_rt _
    rw [heq] at h1
    have h2 : (UInt8.ofNat e).toNat = e := by simp; omega
    rw [← hofE] at h1
    have h3 := congrArg UInt8.toNat h1
    simp at h3
    omega
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.ebcdic, cbtrn02c.ebcdic_loop]
  refine wp_loop (loop_shape _) (fun e => e.val ≤ E) (fun e => 256 - e.val) ?_ _ ?_
  · intro e he
    simp only [cbtrn02c.ebcdic_loop.body]
    aeneas_wp [arr_index_eq, usz_lit_val, UScalar.cast_val_eq, ebcTab_len]
    have hlt : e.val < 256 := by omega
    by_cases heq : e.val = E
    · have hb' := hfound
      simp only [_root_.ite_true, heq, hb', loopCls_done, Except.ok.injEq, hE, _root_.dite_true]
      apply UScalar.eq_of_val_eq
      rw [UScalar.cast_val_eq, ebcU_val, heq]
      simp only [UScalarTy.U8_numBits_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
    · have hne := hnot e.val (by omega)
      have hov : e.val + 1 ≤ Usize.max := by have := usize_max_ge; omega
      simp only [hlt, _root_.ite_true, _root_.dite_true, hne, _root_.ite_false, hov, loopCls_cont,
        UScalar.ofNatCore_val_eq]
      omega
  · simp [usz_lit_val]

theorem cmpBytes_append (P Q R : List UInt8) :
    Sem.cmpBytes (P ++ Q) (P ++ R) = Sem.cmpBytes Q R := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [Sem.cmpBytes, ih]

theorem cmpBytes_self (A : List UInt8) : Sem.cmpBytes A A = .eq := by
  induction A with
  | nil => rfl
  | cons a A ih => simp [Sem.cmpBytes, ih]

/-- `a(1:n) >= b(1:n)` in the EBCDIC collating sequence, on the EBCDIC bytes. -/
def geEbc (a b : List U8) (n : Nat) : Bool :=
  Sem.cmpBytes ((a.take n).map ebc) ((b.take n).map ebc) != .lt

theorem cmpBytes_cons (x y : UInt8) (A B : List UInt8) :
    Sem.cmpBytes (x :: A) (y :: B) = if x < y then .lt else if y < x then .gt else Sem.cmpBytes A B := rfl

theorem take_split {α : Type _} (l : List α) (n i : Nat) (hi : i < n) (hl : n ≤ l.length) :
    l.take n = l.take i ++ l[i]'(by omega) :: (l.take n).drop (i + 1) := by
  have h1 : (l.take n).take i = l.take i := by rw [List.take_take]; congr 1; omega
  have h2 : (l.take n)[i]'(by simp; omega) = l[i]'(by omega) := by simp
  conv_lhs => rw [← List.take_append_drop i (l.take n)]
  rw [h1, List.drop_eq_getElem_cons (by simp; omega), h2]

theorem geEbc_split (a b : List U8) (n i : Nat) (hi : i < n) (ha : n ≤ a.length) (hb : n ≤ b.length)
    (he : (a.take i).map ebc = (b.take i).map ebc) :
    Sem.cmpBytes ((a.take n).map ebc) ((b.take n).map ebc) =
      if ebc (a[i]'(by omega)) < ebc (b[i]'(by omega)) then .lt
      else if ebc (b[i]'(by omega)) < ebc (a[i]'(by omega)) then .gt
      else Sem.cmpBytes (((a.take n).drop (i + 1)).map ebc) (((b.take n).drop (i + 1)).map ebc) := by
  rw [take_split a n i hi ha, take_split b n i hi hb, List.map_append, List.map_append, he,
    cmpBytes_append, List.map_cons, List.map_cons, cmpBytes_cons]
  rw [← take_split a n i hi ha, ← take_split b n i hi hb]

theorem ge_prefix_eq (a b : Slice U8) (n : Usize) (ha : n.val ≤ a.val.length)
    (hb : n.val ≤ b.val.length) :
    cbtrn02c.ge_prefix a b n = .ok (geEbc a.val b.val n.val) := by
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.ge_prefix, cbtrn02c.ge_prefix_loop]
  refine wp_loop (loop_shape _)
    (fun i => i.val ≤ n.val ∧ (a.val.take i.val).map ebc = (b.val.take i.val).map ebc)
    (fun i => n.val - i.val) ?_ _ ?_
  · intro i hinv
    obtain ⟨hi, he⟩ := hinv
    simp only [cbtrn02c.ge_prefix_loop.body]
    aeneas_wp [ebcdic_eq, usz_lit_val]
    by_cases hlt : i.val < n.val
    · have hia : i.val < a.val.length := by omega
      have hib : i.val < b.val.length := by omega
      have hsplit := geEbc_split a.val b.val n.val i.val hlt ha hb he
      simp only [hlt, hia, hib, _root_.ite_true, _root_.dite_true, ebcU_val]
      by_cases h1 : (ebc b.val[i.val]).toNat < (ebc a.val[i.val]).toNat
      · have h1' : ebc b.val[i.val] < ebc a.val[i.val] := UInt8.lt_iff_toNat_lt.2 h1
        have h2' : ¬ ebc a.val[i.val] < ebc b.val[i.val] := fun h => by
          rw [UInt8.lt_iff_toNat_lt] at h; omega
        simp only [h1, _root_.ite_true, loopCls_done, Except.ok.injEq, geEbc, hsplit, h1', h2',
          _root_.ite_false]
        rfl
      · by_cases h2 : (ebc a.val[i.val]).toNat < (ebc b.val[i.val]).toNat
        · have h2' : ebc a.val[i.val] < ebc b.val[i.val] := UInt8.lt_iff_toNat_lt.2 h2
          simp only [h1, h2, _root_.ite_true, _root_.ite_false, loopCls_done, Except.ok.injEq,
            geEbc, hsplit, h2']
          rfl
        · have hov : i.val + 1 ≤ Usize.max := by scalar_tac
          simp only [h1, h2, _root_.ite_false, hov, _root_.dite_true, loopCls_cont,
            UScalar.ofNatCore_val_eq]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          have heq : ebc a.val[i.val] = ebc b.val[i.val] := by
            apply UInt8.toNat_inj.1; omega
          rw [take_succ_of_lt' hia, take_succ_of_lt' hib, List.map_append, List.map_append, he,
            List.map_singleton, List.map_singleton, heq]
    · simp only [hlt, _root_.ite_false, loopCls_done, Except.ok.injEq]
      have hin : i.val = n.val := by omega
      rw [hin] at he
      simp [geEbc, he, cmpBytes_self]
  · simp

/-! ## `db2_timestamp`, the blank records, `abend`, the file status line -/

set_option maxHeartbeats 1000000 in
theorem db2_timestamp_eq (clock : Std.Array U8 21#usize) :
    cbtrn02c.db2_timestamp clock = .ok (tsArr clock) := by
  have hc : clock.val.length = 21 := clock.property
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.db2_timestamp]
  aeneas_wp [arr_index_n, arr_update_set, usz_lit_val]
  simp only [Except.ok.injEq, Std.Array.eq_iff, Std.Array.set_val_eq, Std.Array.repeat_val, tsArr,
    Std.Array.from_val, usz_lit_val]
  simp only [tsList, List.replicate_succ, List.replicate_zero, List.set_cons_zero, List.set_cons_succ]
  simp (disch := omega) only [List.getD_eq_getElem]

/-- `ABENDING PROGRAM` (Latin-1). -/
def abendBytes : List U8 :=
  [65#u8, 66#u8, 69#u8, 78#u8, 68#u8, 73#u8, 78#u8, 71#u8, 32#u8, 80#u8, 82#u8, 79#u8, 71#u8, 82#u8,
    65#u8, 77#u8]

theorem abend_eq (out : cbtrn02c.Output) (h : out.displays.val.length < Usize.max) :
    cbtrn02c.abend out = .ok { out with
      displays := alloc.vec.Vec.from (out.displays.val ++ [alloc.vec.Vec.from abendBytes
        (by have := usize_max_ge; simp [abendBytes]; omega)]) (by simp; omega),
      abended := true } := by
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.abend, lift, Std.Array.to_slice, bind_tc_ok, bind_ok, lit_eq]
  simp only [wp_bind, wp_ok, wp_Vec_push, h, _root_.dite_true]
  rfl

/-- `FILE STATUS IS: NNNN` and the status `22` / `23` (Latin-1). -/
def statusBytes (s1 : U8) : List U8 :=
  [70#u8, 73#u8, 76#u8, 69#u8, 32#u8, 83#u8, 84#u8, 65#u8, 84#u8, 85#u8, 83#u8, 32#u8, 73#u8, 83#u8,
    58#u8, 32#u8, 78#u8, 78#u8, 78#u8, 78#u8, 48#u8, 48#u8, 50#u8, s1]

theorem display_io_status_eq (out : cbtrn02c.Output) (st : Std.Array U8 2#usize) (s1 : U8)
    (hst : st.val = [50#u8, s1]) (hs1 : 48 ≤ s1.val ∧ s1.val ≤ 57)
    (h : out.displays.val.length < Usize.max) :
    cbtrn02c.display_io_status out st = .ok { out with
      displays := alloc.vec.Vec.from (out.displays.val ++ [alloc.vec.Vec.from (statusBytes s1)
        (by have := usize_max_ge; simp [statusBytes]; omega)]) (by simp; omega) } := by
  have hm := usize_max_ge
  refine eq_ok_of_wp' ?_
  simp only [cbtrn02c.display_io_status]
  have htl : ∀ h, (Std.Array.make 20#usize
      [70#u8, 73#u8, 76#u8, 69#u8, 32#u8, 83#u8, 84#u8, 65#u8, 84#u8, 85#u8, 83#u8, 32#u8, 73#u8, 83#u8,
        58#u8, 32#u8, 78#u8, 78#u8, 78#u8, 78#u8] h).val =
      [70#u8, 73#u8, 76#u8, 69#u8, 32#u8, 83#u8, 84#u8, 65#u8, 84#u8, 85#u8, 83#u8, 32#u8, 73#u8, 83#u8,
        58#u8, 32#u8, 78#u8, 78#u8, 78#u8, 78#u8] := fun _ => rfl
  aeneas_wp [arr_index_eq, hst, usz_lit_val, lit_eq, lift, Std.Array.to_slice, htl,
    List.getElem_cons_zero, List.getElem_cons_succ, List.length_cons, List.length_nil]
  have h50 : ((50#u8 : U8)).val = 50 := rfl
  simp only [h50, hs1, show (48 : Nat) ≤ 50 from by omega, show (50 : Nat) ≤ 57 from by omega,
    show ¬ (50 : Nat) = 57 from by omega, _root_.ite_true, _root_.ite_false, _root_.dite_true]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega_ifs
  simp only [Except.ok.injEq, statusBytes, List.append_assoc, List.cons_append, List.nil_append,
    List.singleton_append]

end EquivLean.Modernize.Cbtrn02c.Rust

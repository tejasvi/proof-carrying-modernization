import EquivLean.Demo.XLang.Crc32.Spec
import EquivLean.Demo.Gen.Aeneas.Crc32Base.Funs
import EquivLean.Bridge.Aeneas.Behaves

/-!
# crc32fast's baseline CRC-32 (Rust, Charon + Aeneas) is zlib's CRC-32

`examples/rust/crc32fast_base` is crc32fast 1.4.2's `baseline.rs` and `table.rs`, translated to
`Demo/Gen/Aeneas/Crc32Base`.  Each function equals `crc32` of `Spec.lean` on every input, so it
never panics:

* `update_slow_eq`: the byte-wise loop over `buf.iter()`;
* `update_fast_16_eq`: slice-by-16 unrolled four times, then the byte-wise tail;
* `State_update_eq`, `state_crc32`, `state_crc32_append`: the `State` API (`new`, `update`,
  `finalize`), also for two updates in a row;
* `update_slow_equiv_crc32`, `update_fast_16_equiv_crc32`: the same as `Equiv` with
  `pureVal (crc32 …)`.

The proof has three parts.
1. GF(2) algebra on the specification: feeding a zero byte to the register (`Z`) is linear, and
   feeding the byte `b` is `Z (c ^^^ b)`.  So 16 steps are 16 table lookups (`block`), with the
   table entry `tv k i = Zᵏ⁺¹ i`.
2. The concrete table: entry `i` of table `k` of `CRC32_TABLE` is `tv k i` (`table_bv`), by one
   kernel evaluation of a Boolean checker over the 4096 entries (`chkRows_table`).
3. The generated code: each primitive step is an equation `… = ok _` under the bound that makes
   it succeed; one `simp` runs the unrolled body (`inner_body_some`); the loops go by induction
   on the bytes left, through `loop.eq_1`.
-/

open Aeneas Aeneas.Std

namespace EquivLean.Demo.Crc32.Rust

open EquivLean.Demo.Crc32

/-! ## GF(2) algebra: the slice-by-16 identity

Pure bit-vector algebra on the specification.  `Z c` feeds a zero byte to the register; it is
linear (`Z_xor`), and feeding the byte `b` is `Z (c ^^^ b)` (`step_eq`).  So 16 steps are `Z¹⁶ c`
plus one term per byte (`foldl_step`), and `Z¹⁶ c` splits into the four bytes of the register
(`zpow_reg`).
-/

/-- zlib's table entry of a register (`entry` takes the index as a `Nat`). -/
def E (c : BitVec 32) : BitVec 32 := Nat.repeat entryStep 8 c

theorem entry_eq (n : Nat) : entry n = E (BitVec.ofNat 32 n) := rfl

/-- Feeding a zero byte to the register. -/
def Z (c : BitVec 32) : BitVec 32 := E (c &&& (0xFF : BitVec 32)) ^^^ (c >>> 8)

/-- Feeding `n` zero bytes. -/
def zpow : Nat → BitVec 32 → BitVec 32
  | 0, c => c
  | n + 1, c => zpow n (Z c)

/-- The slice-by-16 table: `tv k i` is entry `i` of table `k` (`k` extra zero bytes). -/
def tv (k i : Nat) : BitVec 32 := zpow (k + 1) (BitVec.ofNat 32 i)

/-! ### Linearity -/

theorem and_xor_distrib {w : Nat} (x y m : BitVec w) :
    (x ^^^ y) &&& m = (x &&& m) ^^^ (y &&& m) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.and_xor_distrib_right]

theorem xor_cancel {w : Nat} (p a b : BitVec w) : (p ^^^ a) ^^^ (p ^^^ b) = a ^^^ b := by
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc a, BitVec.xor_comm a p, BitVec.xor_assoc,
    ← BitVec.xor_assoc p p, BitVec.xor_self, BitVec.zero_xor]

theorem and_one_cases (x : BitVec 32) : x &&& 1 = 0 ∨ x &&& 1 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h
  · left; apply BitVec.eq_of_toNat_eq; simp [h]
  · right; apply BitVec.eq_of_toNat_eq; simp [h]

theorem entryStep_xor (x y : BitVec 32) : entryStep (x ^^^ y) = entryStep x ^^^ entryStep y := by
  unfold entryStep
  rw [and_xor_distrib, BitVec.ushiftRight_xor_distrib]
  have h00 : (0 : BitVec 32) ^^^ 0 = 0 := by decide
  have h01 : (0 : BitVec 32) ^^^ 1 = 1 := by decide
  have h10 : (1 : BitVec 32) ^^^ 0 = 1 := by decide
  have h11 : (1 : BitVec 32) ^^^ 1 = 0 := by decide
  have hne : ((1 : BitVec 32) = 0) = False := by decide
  rcases and_one_cases x with hx | hx <;> rcases and_one_cases y with hy | hy <;>
    simp only [hx, hy, h00, h01, h10, h11, hne, ↓reduceIte]
  · ac_rfl
  · ac_rfl
  · rw [xor_cancel]

theorem repeat_entryStep_xor (n : Nat) (x y : BitVec 32) :
    Nat.repeat entryStep n (x ^^^ y) = Nat.repeat entryStep n x ^^^ Nat.repeat entryStep n y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.repeat, ih, entryStep_xor]

theorem E_xor (x y : BitVec 32) : E (x ^^^ y) = E x ^^^ E y := repeat_entryStep_xor 8 x y

theorem Z_xor (x y : BitVec 32) : Z (x ^^^ y) = Z x ^^^ Z y := by
  unfold Z
  rw [and_xor_distrib, E_xor, BitVec.ushiftRight_xor_distrib]
  ac_rfl

theorem zpow_xor (n : Nat) (x y : BitVec 32) : zpow n (x ^^^ y) = zpow n x ^^^ zpow n y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => simp only [zpow, Z_xor, ih]

/-! ### One byte, sixteen bytes -/

theorem setWidth_shr8 (b : BitVec 8) : b.setWidth 32 >>> 8 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp [Nat.shiftRight_eq_div_pow]
  omega

/-- Feeding the byte `b` is feeding a zero byte to the register xor `b`. -/
theorem step_eq (c : BitVec 32) (b : BitVec 8) : step c b = Z (c ^^^ b.setWidth 32) := by
  unfold step Z
  rw [entry_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ushiftRight_xor_distrib,
    setWidth_shr8, BitVec.xor_zero]

/-- The contribution of the bytes to a fold (each byte followed by the later ones). -/
def bytesTerm : List (BitVec 8) → BitVec 32
  | [] => 0
  | b :: bs => zpow (bs.length + 1) (b.setWidth 32) ^^^ bytesTerm bs

theorem foldl_step (bs : List (BitVec 8)) (c : BitVec 32) :
    bs.foldl step c = zpow bs.length c ^^^ bytesTerm bs := by
  induction bs generalizing c with
  | nil => simp [bytesTerm, zpow]
  | cons b bs ih =>
    rw [List.foldl_cons, ih, step_eq, List.length_cons, bytesTerm,
      show zpow bs.length (Z (c ^^^ b.setWidth 32))
        = zpow (bs.length + 1) (c ^^^ b.setWidth 32) from rfl, zpow_xor]
    ac_rfl

theorem and_ff_shr8 (c : BitVec 32) : (c &&& (0xFF : BitVec 32)) >>> 8 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  have : c.toNat &&& 255 < 2 ^ 8 := Nat.and_lt_two_pow _ (by decide)
  simp [Nat.shiftRight_eq_div_pow]
  omega

/-- A zero byte on the register: the low byte through the table, the rest shifted. -/
theorem Z_split (c : BitVec 32) : Z c = Z (c &&& (0xFF : BitVec 32)) ^^^ (c >>> 8) := by
  have h : Z (c &&& (0xFF : BitVec 32)) = E (c &&& (0xFF : BitVec 32)) := by
    rw [Z, BitVec.and_assoc, BitVec.and_self, and_ff_shr8, BitVec.xor_zero]
  rw [h]
  rfl

theorem zpow_split (n : Nat) (c : BitVec 32) :
    zpow (n + 1) c = zpow (n + 1) (c &&& (0xFF : BitVec 32)) ^^^ zpow n (c >>> 8) := by
  rw [zpow, Z_split, zpow_xor]
  rfl

theorem shr24_and (c : BitVec 32) : (c >>> 24) &&& (0xFF : BitVec 32) = c >>> 24 := by
  apply BitVec.eq_of_toNat_eq
  have hc : c.toNat < 2 ^ 32 := c.isLt
  have h : c.toNat >>> 24 < 2 ^ 8 := by rw [Nat.shiftRight_eq_div_pow]; omega
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  rw [show (0xFF : BitVec 32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt h]

/-- `n + 4` zero bytes on the register: its four bytes, through 4..1 fewer steps. -/
theorem zpow_reg (n : Nat) (c : BitVec 32) :
    zpow (n + 4) c = zpow (n + 4) (c &&& (0xFF : BitVec 32)) ^^^ zpow (n + 3) ((c >>> 8) &&& (0xFF : BitVec 32))
      ^^^ zpow (n + 2) ((c >>> 16) &&& (0xFF : BitVec 32)) ^^^ zpow (n + 1) ((c >>> 24) &&& (0xFF : BitVec 32)) := by
  rw [zpow_split (n + 3), zpow_split (n + 2), zpow_split (n + 1)]
  simp only [← BitVec.shiftRight_add, Nat.reduceAdd, Nat.add_assoc]
  rw [shr24_and]
  ac_rfl

/-- **The slice-by-16 identity.** Sixteen steps of the byte-wise update equal sixteen table
lookups, the first four indexed by a message byte xor a register byte. -/
theorem block (c : BitVec 32) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15].foldl step c =
      zpow 1 (b15.setWidth 32) ^^^ zpow 2 (b14.setWidth 32) ^^^ zpow 3 (b13.setWidth 32)
      ^^^ zpow 4 (b12.setWidth 32) ^^^ zpow 5 (b11.setWidth 32) ^^^ zpow 6 (b10.setWidth 32)
      ^^^ zpow 7 (b9.setWidth 32) ^^^ zpow 8 (b8.setWidth 32) ^^^ zpow 9 (b7.setWidth 32)
      ^^^ zpow 10 (b6.setWidth 32) ^^^ zpow 11 (b5.setWidth 32) ^^^ zpow 12 (b4.setWidth 32)
      ^^^ zpow 13 (b3.setWidth 32 ^^^ ((c >>> 24) &&& (0xFF : BitVec 32)))
      ^^^ zpow 14 (b2.setWidth 32 ^^^ ((c >>> 16) &&& (0xFF : BitVec 32)))
      ^^^ zpow 15 (b1.setWidth 32 ^^^ ((c >>> 8) &&& (0xFF : BitVec 32)))
      ^^^ zpow 16 (b0.setWidth 32 ^^^ (c &&& (0xFF : BitVec 32))) := by
  rw [foldl_step]
  simp only [bytesTerm, List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [zpow_reg 12 c]
  simp only [zpow_xor, Nat.reduceAdd]
  ac_rfl

/-! ## `CRC32_TABLE` is the slice-by-16 table

The 4096 entries are checked by one kernel evaluation (`chkRows_table`) of a Boolean checker:
table 0 against zlib's `entry`, and table `k + 1` against table `k` through one zero byte (`Z`),
entry by entry.
-/

/-- Table 0 from index `i` on is zlib's table. -/
def chk0 : Nat → List U32 → Bool
  | _, [] => true
  | i, x :: xs => (x.bv == E (BitVec.ofNat 32 i)) && chk0 (i + 1) xs

/-- Each entry of `ys` is the corresponding entry of `xs` through a zero byte. -/
def chkS : List U32 → List U32 → Bool
  | x :: xs, y :: ys => (y.bv == Z x.bv) && chkS xs ys
  | [], [] => true
  | _, _ => false

/-- `chkS` on consecutive tables. -/
def chkPairs : Std.Array U32 256#usize → List (Std.Array U32 256#usize) → Bool
  | _, [] => true
  | r, s :: rs => chkS r.val s.val && chkPairs s rs

/-- The whole check: table 0, then each table from the previous one. -/
def chkRows : List (Std.Array U32 256#usize) → Bool
  | r :: rs => chk0 0 r.val && chkPairs r rs
  | [] => false

set_option maxRecDepth 100000 in
theorem chkRows_table : chkRows crc32fast_base.table.CRC32_TABLE.val = true := by
  decide +kernel

/-! ### Soundness of the checker -/

theorem chk0_sound : ∀ (l : List U32) (i : Nat), chk0 i l = true →
    ∀ j (h : j < l.length), (l[j]'h).bv = E (BitVec.ofNat 32 (i + j))
  | [], _, _, j, h => absurd h (by simp)
  | x :: xs, i, hc, j, h => by
    simp only [chk0, Bool.and_eq_true, beq_iff_eq] at hc
    cases j with
    | zero => simpa using hc.1
    | succ j =>
      rw [List.getElem_cons_succ, chk0_sound xs (i + 1) hc.2 j (by simpa using h),
        Nat.add_assoc, Nat.add_comm 1 j]

theorem chkS_sound : ∀ (xs ys : List U32), chkS xs ys = true →
    xs.length = ys.length ∧
      ∀ j (h1 : j < xs.length) (h2 : j < ys.length), (ys[j]'h2).bv = Z (xs[j]'h1).bv
  | [], [], _ => ⟨rfl, fun _ h => absurd h (by simp)⟩
  | x :: xs, y :: ys, hc => by
    simp only [chkS, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hl, hs⟩ := chkS_sound xs ys hc.2
    refine ⟨by simp [hl], fun j h1 h2 => ?_⟩
    cases j with
    | zero => simpa using hc.1
    | succ j => simpa using hs j (by simpa using h1) (by simpa using h2)
  | [], _ :: _, hc => by simp [chkS] at hc
  | _ :: _, [], hc => by simp [chkS] at hc

theorem chkPairs_sound : ∀ (r : Std.Array U32 256#usize) (rs : List (Std.Array U32 256#usize)),
    chkPairs r rs = true → ∀ k (hk : k < rs.length) j (h1 : j < r.val.length)
      (h2 : j < (rs[k]'hk).val.length), ((rs[k]'hk).val[j]'h2).bv = zpow (k + 1) (r.val[j]'h1).bv
  | _, [], _, _, hk, _, _, _ => absurd hk (by simp)
  | r, s :: rs, hc, k, hk, j, h1, h2 => by
    simp only [chkPairs, Bool.and_eq_true] at hc
    obtain ⟨hl, hs⟩ := chkS_sound r.val s.val hc.1
    cases k with
    | zero => simpa [zpow] using hs j h1 (by simpa using h2)
    | succ k =>
      have hj : j < s.val.length := by rw [← hl]; exact h1
      simp only [List.getElem_cons_succ]
      rw [chkPairs_sound s rs hc.2 k (by simpa using hk) j hj, hs j h1 hj]
      rfl

theorem E_byte (i : Nat) (hi : i < 256) : E (BitVec.ofNat 32 i) = tv 0 i := by
  have hand : BitVec.ofNat 32 i &&& (0xFF : BitVec 32) = BitVec.ofNat 32 i := by
    apply BitVec.eq_of_toNat_eq
    have h32 : i < 2 ^ 32 := by omega
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32]
    rw [show (0xFF : BitVec 32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt (by omega)]
  have hshr : BitVec.ofNat 32 i >>> 8 = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftRight_eq_div_pow]
    omega
  show _ = Z (BitVec.ofNat 32 i)
  rw [Z, hand, hshr, BitVec.xor_zero]

theorem rows_sound (T : List (Std.Array U32 256#usize)) (hc : chkRows T = true) (k i : Nat)
    (hi : i < 256) (h1 : k < T.length) (h2 : i < (T[k]'h1).val.length) :
    ((T[k]'h1).val[i]'h2).bv = tv k i := by
  match T, hc with
  | r :: rs, hc =>
    simp only [chkRows, Bool.and_eq_true] at hc
    have hr : i < r.val.length := by simpa using hi
    cases k with
    | zero =>
      simp only [List.getElem_cons_zero]
      rw [chk0_sound r.val 0 hc.1 i hr, Nat.zero_add, E_byte i hi]
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [chkPairs_sound r rs hc.2 k (by simpa using h1) i hr,
        chk0_sound r.val 0 hc.1 i hr, Nat.zero_add, E_byte i hi]
      rfl

/-- **The concrete table.** Entry `i` of table `k` of crc32fast's `CRC32_TABLE` is `tv k i`. -/
theorem table_bv (k i : Nat) (hi : i < 256) (h1 : k < crc32fast_base.table.CRC32_TABLE.val.length)
    (h2 : i < (crc32fast_base.table.CRC32_TABLE.val[k]'h1).val.length) :
    ((crc32fast_base.table.CRC32_TABLE.val[k]'h1).val[i]'h2).bv = tv k i :=
  rows_sound _ chkRows_table k i hi h1 h2

/-! ## `update_slow` (byte-wise)

The primitive steps of the generated code as equations, each with the bound that makes it
succeed; then `update_slow_eq` by induction on the bytes left.
-/

/-! ### Primitive steps -/

theorem exists_ok_of_spec {α : Type} {m : Result α} {p : α → Prop} (h : WP.spec m p) :
    ∃ a, m = .ok a ∧ p a := by
  rcases EquivLean.Aeneas.result_trichotomy m with ⟨a, rfl⟩ | ⟨e, rfl⟩ | rfl
  · exact ⟨a, rfl, (WP.spec_ok a).1 h⟩
  · simp at h
  · simp at h

theorem slice_index_ok {α : Type} (v : Slice α) (i : Usize) (h : i.val < v.val.length) :
    v.index_usize i = .ok (v.val[i.val]) := by
  simp only [Slice.index_usize, Slice.getElem?_Usize_eq, List.getElem?_eq_getElem h]

theorem array_index_ok {α : Type} {n : Usize} (v : Std.Array α n) (i : Usize)
    (h : i.val < v.val.length) : v.index_usize i = .ok (v.val[i.val]) := by
  simp only [Std.Array.index_usize, Std.Array.getElem?_Usize_eq, List.getElem?_eq_getElem h]

theorem shr_ok (x : U32) (s : I32) (h0 : 0 ≤ s.val) (h1 : s.toNat < 32) :
    x >>> s = .ok ⟨x.bv >>> s.toNat⟩ := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight]
  simp [h0, h1]

theorem shr0 (x : U32) : x >>> (0#i32) = .ok ⟨x.bv >>> 0⟩ := by rw [shr_ok] <;> simp
theorem shr8 (x : U32) : x >>> (8#i32) = .ok ⟨x.bv >>> 8⟩ := by rw [shr_ok] <;> simp
theorem shr16 (x : U32) : x >>> (16#i32) = .ok ⟨x.bv >>> 16⟩ := by rw [shr_ok] <;> simp
theorem shr24 (x : U32) : x >>> (24#i32) = .ok ⟨x.bv >>> 24⟩ := by rw [shr_ok] <;> simp

theorem table_length : crc32fast_base.table.CRC32_TABLE.val.length = 16 := by simp

theorem row_length (a : Std.Array U32 256#usize) : a.val.length = 256 := by simp

theorem iter_next_some {α : Type} (buf : Slice α) (i : Nat) (h : i < buf.val.length) :
    core.slice.iter.IteratorSliceIter.next ⟨buf, i⟩ = .ok (some (buf.val[i]'h), ⟨buf, i + 1⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  rw [dite_eq_left (by simpa using h)]
  rfl

theorem iter_next_none {α : Type} (buf : Slice α) (i : Nat) (h : buf.val.length ≤ i) :
    core.slice.iter.IteratorSliceIter.next ⟨buf, i⟩ = .ok (none, ⟨buf, i⟩) := by
  unfold core.slice.iter.IteratorSliceIter.next
  simp [show ¬ i < buf.val.length by omega]

/-! ### One byte -/

/-- The byte-wise step through table 0, in the form of crc32fast's `update_slow`. -/
theorem step_tv (c : BitVec 32) (b : BitVec 8) :
    step c b = tv 0 ((c.setWidth 8 ^^^ b).toNat) ^^^ (c >>> 8) := by
  have hb := b.isLt
  have hidx : ((c ^^^ b.setWidth 32) &&& (0xFF : BitVec 32)).toNat = (c.setWidth 8 ^^^ b).toNat := by
    have hb32 : b.toNat % 2 ^ 32 = b.toNat := Nat.mod_eq_of_lt (by omega)
    have hb8 : b.toNat % 2 ^ 8 = b.toNat := Nat.mod_eq_of_lt hb
    simp only [BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_setWidth, hb32]
    rw [show (0xFF : BitVec 32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.xor_mod_two_pow, hb8]
  have hlt : (c.setWidth 8 ^^^ b).toNat < 256 := (c.setWidth 8 ^^^ b).isLt
  unfold step
  rw [hidx, entry_eq, E_byte _ hlt]

theorem slow_body_some (buf : Slice U8) (i : Nat) (h : i < buf.val.length) (crc : U32) :
    crc32fast_base.update_slow_loop.body ⟨buf, i⟩ crc =
      .ok (.cont (⟨buf, i + 1⟩, ⟨step crc.bv (buf.val[i]'h).bv⟩)) := by
  unfold crc32fast_base.update_slow_loop.body
  rw [iter_next_some buf i h]
  simp only [bind_ok, Aeneas.Std.uncurry_apply_pair, lift]
  have h0 : (0#usize).val < crc32fast_base.table.CRC32_TABLE.val.length := by
    rw [table_length]; decide
  rw [array_index_ok _ _ h0]
  simp only [bind_ok]
  have hidx : (UScalar.cast .Usize (UScalar.cast .U8 crc ^^^ buf.val[i])).val <
      (crc32fast_base.table.CRC32_TABLE.val[(0#usize).val]'h0).val.length := by
    rw [row_length, U8.cast_Usize_val_eq]
    exact (UScalar.cast .U8 crc ^^^ buf.val[i]).bv.isLt
  rw [array_index_ok _ _ hidx, shr8]
  simp only [bind_ok]
  congr 3
  have ht := table_bv (0#usize).val _ (by simpa [row_length] using hidx) h0 hidx
  rw [UScalar.eq_equiv_bv_eq, UScalar.bv_xor]
  simp only [ht]
  rw [step_tv]
  congr 2
  rw [U8.cast_Usize_val_eq, UScalar.val, UScalar.bv_xor, UScalar.cast_bv_eq]
  rfl

theorem slow_body_none (buf : Slice U8) (i : Nat) (h : buf.val.length ≤ i) (crc : U32) :
    crc32fast_base.update_slow_loop.body ⟨buf, i⟩ crc = .ok (.done crc) := by
  unfold crc32fast_base.update_slow_loop.body
  rw [iter_next_none buf i h]
  simp only [bind_ok, Aeneas.Std.uncurry_apply_pair]

/-! ### The loop -/

theorem update_slow_loop_eq (buf : Slice U8) :
    ∀ (n i : Nat) (crc : U32), buf.val.length - i = n → i ≤ buf.val.length →
      crc32fast_base.update_slow_loop ⟨buf, i⟩ crc =
        .ok ⟨((buf.val.drop i).map (·.bv)).foldl step crc.bv⟩
  | 0, i, crc, hn, hi => by
    have hle : buf.val.length ≤ i := by omega
    unfold crc32fast_base.update_slow_loop
    rw [loop.eq_1]
    simp only [slow_body_none buf i hle crc, bind_ok, List.drop_eq_nil_of_le hle, List.map_nil,
      List.foldl_nil]
  | n + 1, i, crc, hn, hi => by
    have hlt : i < buf.val.length := by omega
    have ih := update_slow_loop_eq buf n (i + 1) ⟨step crc.bv (buf.val[i]'hlt).bv⟩ (by omega)
      (by omega)
    unfold crc32fast_base.update_slow_loop at ih ⊢
    rw [loop.eq_1]
    simp only [slow_body_some buf i hlt crc, bind_ok]
    rw [ih, List.drop_eq_getElem_cons hlt, List.map_cons, List.foldl_cons]

/-- **`update_slow` is zlib's CRC-32**, and it never panics. -/
theorem update_slow_eq (prev : U32) (buf : Slice U8) :
    crc32fast_base.update_slow prev buf = .ok ⟨crc32 prev.bv (buf.val.map (·.bv))⟩ := by
  unfold crc32fast_base.update_slow
  simp only [lift, bind_ok, core.slice.Slice.iter]
  rw [update_slow_loop_eq buf _ 0 _ rfl (Nat.zero_le _)]
  simp only [bind_ok, List.drop_zero, crc32]
  rfl

/-! ## `update_fast_16` (slice-by-16) and `State`

The unrolled step of the generated code is the xor of 16 table entries (`inner_body_some`,
`blkCode`); by `table_bv` and `block` it is 16 byte-wise steps (`blkCode_eq`).  Then the
`for _ in 0..4` loop (`inner_loop`), the `while buf.len() >= 64` loop (`outer_loop`) and the
byte-wise tail give `update_fast_16_eq`.
-/

/-! ### Primitive steps of the unrolled body -/

theorem u8_lt (b : U8) : b.val < 256 := b.bv.isLt

theorem xor_idx_lt (b : U8) (x : U32) : b.val ^^^ (x.val &&& 255) < 256 :=
  Nat.xor_lt_two_pow (n := 8) (u8_lt b) (Nat.and_lt_two_pow _ (by decide))

theorem tbl_index (k : Usize) (hk : k.val < 16) :
    crc32fast_base.table.CRC32_TABLE.index_usize k =
      .ok (crc32fast_base.table.CRC32_TABLE.val[k.val]'(by rw [table_length]; exact hk)) :=
  array_index_ok _ _ _

theorem row_index_u8 (a : Std.Array U32 256#usize) (b : U8) :
    a.index_usize (UScalar.cast .Usize b) = .ok (a.val[b.val]'(by rw [row_length]; exact u8_lt b)) := by
  rw [array_index_ok _ _ (by rw [row_length, U8.cast_Usize_val_eq]; exact u8_lt b)]
  simp only [U8.cast_Usize_val_eq]

theorem row_index_xor (a : Std.Array U32 256#usize) (b : U8) (x : U32) :
    a.index_usize (UScalar.cast .Usize b ^^^ UScalar.cast .Usize (x &&& 255#u32)) =
      .ok (a.val[b.val ^^^ (x.val &&& 255)]'(by rw [row_length]; exact xor_idx_lt b x)) := by
  have hv : (UScalar.cast .Usize b ^^^ UScalar.cast .Usize (x &&& 255#u32)).val =
      b.val ^^^ (x.val &&& 255) := by
    rw [UScalar.val_xor, U8.cast_Usize_val_eq, U32.cast_Usize_val_eq, UScalar.val_and]
    rfl
  rw [array_index_ok _ _ (by rw [row_length, hv]; exact xor_idx_lt b x)]
  simp only [hv]

theorem slice_from_ok (buf : Slice U8) (k : Usize) (h : k.val ≤ buf.val.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) buf
      { start := k } = .ok (buf.drop k) := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index]
  simp [h]

/-- `table_bv` without the bound on the index (it follows from the row length). -/
theorem table_bv' (k i : Nat) (h1 : k < crc32fast_base.table.CRC32_TABLE.val.length)
    (h2 : i < (crc32fast_base.table.CRC32_TABLE.val[k]'h1).val.length) :
    ((crc32fast_base.table.CRC32_TABLE.val[k]'h1).val[i]'h2).bv = tv k i :=
  table_bv k i (by rw [row_length] at h2; exact h2) h1 h2

/-! ### The unrolled step -/

/-- The 16 table lookups of one unrolled step, as the generated code computes them. -/
def blkCode (c : BitVec 32) (buf : List U8) (h : 16 ≤ buf.length) : BitVec 32 :=
  tv 0 (buf[15]).val
    ^^^ tv 1 (buf[14]).val
    ^^^ tv 2 (buf[13]).val
    ^^^ tv 3 (buf[12]).val
    ^^^ tv 4 (buf[11]).val
    ^^^ tv 5 (buf[10]).val
    ^^^ tv 6 (buf[9]).val
    ^^^ tv 7 (buf[8]).val
    ^^^ tv 8 (buf[7]).val
    ^^^ tv 9 (buf[6]).val
    ^^^ tv 10 (buf[5]).val
    ^^^ tv 11 (buf[4]).val
    ^^^ tv 12 ((buf[3]).val ^^^ ((c >>> 24).toNat &&& 255))
    ^^^ tv 13 ((buf[2]).val ^^^ ((c >>> 16).toNat &&& 255))
    ^^^ tv 14 ((buf[1]).val ^^^ ((c >>> 8).toNat &&& 255))
    ^^^ tv 15 ((buf[0]).val ^^^ ((c >>> 0).toNat &&& 255))

theorem inner_body_some (iter : core.ops.range.Range Usize) (buf : Slice U8) (crc : U32)
    (hit : iter.start.val < iter.end.val) (hlen : 16 ≤ buf.val.length) :
    ∃ iter', crc32fast_base.update_fast_16_loop0_loop0.body iter buf crc =
        .ok (.cont (iter', buf.drop 16#usize, ⟨blkCode crc.bv buf.val hlen⟩)) ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  obtain ⟨⟨o, iter'⟩, hnext, ho, hs, he⟩ :=
    exists_ok_of_spec (core.iter.range.IteratorRange.next_Usize_some_spec iter hit)
  subst ho
  refine ⟨iter', ?_, hs, he⟩
  unfold crc32fast_base.update_fast_16_loop0_loop0.body
  have h0 : (0#usize).val < buf.val.length := by
    have : (0#usize).val = 0 := rfl
    omega
  have h1 : (1#usize).val < buf.val.length := by
    have : (1#usize).val = 1 := rfl
    omega
  have h2 : (2#usize).val < buf.val.length := by
    have : (2#usize).val = 2 := rfl
    omega
  have h3 : (3#usize).val < buf.val.length := by
    have : (3#usize).val = 3 := rfl
    omega
  have h4 : (4#usize).val < buf.val.length := by
    have : (4#usize).val = 4 := rfl
    omega
  have h5 : (5#usize).val < buf.val.length := by
    have : (5#usize).val = 5 := rfl
    omega
  have h6 : (6#usize).val < buf.val.length := by
    have : (6#usize).val = 6 := rfl
    omega
  have h7 : (7#usize).val < buf.val.length := by
    have : (7#usize).val = 7 := rfl
    omega
  have h8 : (8#usize).val < buf.val.length := by
    have : (8#usize).val = 8 := rfl
    omega
  have h9 : (9#usize).val < buf.val.length := by
    have : (9#usize).val = 9 := rfl
    omega
  have h10 : (10#usize).val < buf.val.length := by
    have : (10#usize).val = 10 := rfl
    omega
  have h11 : (11#usize).val < buf.val.length := by
    have : (11#usize).val = 11 := rfl
    omega
  have h12 : (12#usize).val < buf.val.length := by
    have : (12#usize).val = 12 := rfl
    omega
  have h13 : (13#usize).val < buf.val.length := by
    have : (13#usize).val = 13 := rfl
    omega
  have h14 : (14#usize).val < buf.val.length := by
    have : (14#usize).val = 14 := rfl
    omega
  have h15 : (15#usize).val < buf.val.length := by
    have : (15#usize).val = 15 := rfl
    omega
  have h16 : (16#usize).val ≤ buf.val.length := by
    have : (16#usize).val = 16 := rfl
    omega
  simp (disch := decide) only [hnext, bind_ok, Aeneas.Std.uncurry_apply_pair, lift,
    slice_index_ok _ _ h0, slice_index_ok _ _ h1, slice_index_ok _ _ h2, slice_index_ok _ _ h3, slice_index_ok _ _ h4, slice_index_ok _ _ h5, slice_index_ok _ _ h6, slice_index_ok _ _ h7, slice_index_ok _ _ h8, slice_index_ok _ _ h9, slice_index_ok _ _ h10, slice_index_ok _ _ h11, slice_index_ok _ _ h12, slice_index_ok _ _ h13, slice_index_ok _ _ h14, slice_index_ok _ _ h15,
    tbl_index, row_index_u8, row_index_xor, shr0, shr8, shr16, shr24, slice_from_ok _ _ h16]
  congr 4
  apply (UScalar.eq_equiv_bv_eq _ _).mpr
  simp only [UScalar.bv_xor, table_bv']
  rfl

/-! ### The unrolled step is 16 byte-wise steps -/

theorem ofNat_u8 (b : U8) : BitVec.ofNat 32 b.val = b.bv.setWidth 32 :=
  BitVec.ofNat_toNat 32 b.bv

theorem ofNat_xor (b : U8) (x : BitVec 32) :
    BitVec.ofNat 32 (b.val ^^^ (x.toNat &&& 255)) = b.bv.setWidth 32 ^^^ (x &&& (0xFF : BitVec 32)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : b.val ^^^ (x.toNat &&& 255) < 256 :=
    Nat.xor_lt_two_pow (n := 8) (u8_lt b) (Nat.and_lt_two_pow _ (by decide))
  have h2 : b.bv.toNat < 256 := u8_lt b
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_xor, BitVec.toNat_and,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega),
    show (0xFF : BitVec 32).toNat = 255 from rfl]
  rfl

theorem blkCode_eq (c : BitVec 32) (buf : List U8) (h : 16 ≤ buf.length) :
    blkCode c buf h = ((buf.take 16).map (·.bv)).foldl step c := by
  rcases buf with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at h; done)
  simp only [blkCode, tv, List.getElem_cons_succ, List.getElem_cons_zero, List.take_succ_cons,
    List.take_zero, List.map_cons, List.map_nil]
  rw [block]
  simp only [ofNat_u8, ofNat_xor, BitVec.ushiftRight_zero]

/-! ### The `for _ in 0..4` loop -/

theorem inner_body_none (iter : core.ops.range.Range Usize) (buf : Slice U8) (crc : U32)
    (hit : ¬ iter.start.val < iter.end.val) :
    crc32fast_base.update_fast_16_loop0_loop0.body iter buf crc = .ok (.done (buf, crc)) := by
  obtain ⟨⟨o, iter'⟩, hnext, ho, -⟩ :=
    exists_ok_of_spec (core.iter.range.IteratorRange.next_Usize_none_spec iter (by omega))
  subst ho
  unfold crc32fast_base.update_fast_16_loop0_loop0.body
  simp only [hnext, bind_ok, Aeneas.Std.uncurry_apply_pair]

theorem inner_loop : ∀ (n : Nat) (iter : core.ops.range.Range Usize) (buf : Slice U8) (crc : U32),
    iter.start.val + n = iter.end.val → 16 * n ≤ buf.val.length →
    ∃ buf' crc', crc32fast_base.update_fast_16_loop0_loop0 iter buf crc = .ok (buf', crc') ∧
      buf'.val = buf.val.drop (16 * n) ∧
      crc'.bv = ((buf.val.take (16 * n)).map (·.bv)).foldl step crc.bv
  | 0, iter, buf, crc, hn, _ => by
    refine ⟨buf, crc, ?_, by simp, by simp⟩
    unfold crc32fast_base.update_fast_16_loop0_loop0
    rw [loop.eq_1]
    simp only [inner_body_none iter buf crc (by omega), bind_ok]
  | n + 1, iter, buf, crc, hn, hl => by
    have hlen : 16 ≤ buf.val.length := by omega
    obtain ⟨iter', hb, hs, he⟩ := inner_body_some iter buf crc (by omega) hlen
    have hd : (buf.drop 16#usize).val = buf.val.drop 16 := Slice.getElem!_val_drop _ _
    obtain ⟨buf', crc', hl', hv, hc⟩ := inner_loop n iter' (buf.drop 16#usize)
      ⟨blkCode crc.bv buf.val hlen⟩ (by rw [hs, he]; omega) (by rw [hd, List.length_drop]; omega)
    refine ⟨buf', crc', ?_, ?_, ?_⟩
    · unfold crc32fast_base.update_fast_16_loop0_loop0 at hl' ⊢
      rw [loop.eq_1]
      simp only [hb, bind_ok]
      exact hl'
    · rw [hv, hd, List.drop_drop]
      congr 1
      omega
    · rw [hc, hd, blkCode_eq, ← List.foldl_append, ← List.map_append, ← List.take_add,
        Nat.mul_succ, Nat.add_comm]

/-! ### The `while buf.len() >= 64` loop -/

theorem bytes_at_once : ∃ z : Usize, crc32fast_base.update_fast_16.BYTES_AT_ONCE = .ok z ∧ z.val = 64 := by
  unfold crc32fast_base.update_fast_16.BYTES_AT_ONCE crc32fast_base.update_fast_16.UNROLL
  obtain ⟨z, hz, hv⟩ := exists_ok_of_spec (UScalar.mul_spec (x := 16#usize) (y := 4#usize) (by scalar_tac))
  exact ⟨z, hz, by rw [hv]; rfl⟩

theorem unroll_val : crc32fast_base.update_fast_16.UNROLL.val = 4 := by
  unfold crc32fast_base.update_fast_16.UNROLL
  rfl

theorem outer_body_done (buf : Slice U8) (crc : U32) (h : buf.val.length < 64) :
    crc32fast_base.update_fast_16_loop0.body buf crc = .ok (.done (buf, crc)) := by
  obtain ⟨z, hz, hv⟩ := bytes_at_once
  have hc : ¬ (Slice.len buf ≥ z) := by
    rw [ge_iff_le, UScalar.le_equiv, hv, Slice.len_val, Slice.length]
    omega
  unfold crc32fast_base.update_fast_16_loop0.body
  simp only [hz, bind_ok, hc, ↓reduceIte]

theorem outer_body_cont (buf : Slice U8) (crc : U32) (h : 64 ≤ buf.val.length) :
    ∃ buf' crc', crc32fast_base.update_fast_16_loop0.body buf crc = .ok (.cont (buf', crc')) ∧
      buf'.val = buf.val.drop 64 ∧ crc'.bv = ((buf.val.take 64).map (·.bv)).foldl step crc.bv := by
  obtain ⟨z, hz, hv⟩ := bytes_at_once
  have hc : Slice.len buf ≥ z := by
    rw [ge_iff_le, UScalar.le_equiv, hv, Slice.len_val, Slice.length]
    omega
  obtain ⟨buf', crc', hl, hb, hcrc⟩ := inner_loop 4
    { start := 0#usize, «end» := crc32fast_base.update_fast_16.UNROLL } buf crc
    (by rw [unroll_val]; rfl) (by omega)
  refine ⟨buf', crc', ?_, hb, hcrc⟩
  unfold crc32fast_base.update_fast_16_loop0.body
  simp only [hz, bind_ok, hc, ↓reduceIte, hl, Aeneas.Std.uncurry_apply_pair]

theorem outer_loop : ∀ (n : Nat) (buf : Slice U8) (crc : U32), buf.val.length < 64 * (n + 1) →
    ∃ buf' crc', crc32fast_base.update_fast_16_loop0 buf crc = .ok (buf', crc') ∧
      (buf.val.map (·.bv)).foldl step crc.bv = (buf'.val.map (·.bv)).foldl step crc'.bv
  | n, buf, crc, hn => by
    by_cases h : buf.val.length < 64
    · refine ⟨buf, crc, ?_, rfl⟩
      unfold crc32fast_base.update_fast_16_loop0
      rw [loop.eq_1]
      simp only [outer_body_done buf crc h, bind_ok]
    · obtain ⟨buf1, crc1, hb, hv, hc⟩ := outer_body_cont buf crc (by omega)
      match n, hn with
      | n + 1, hn =>
        obtain ⟨buf', crc', hl, hf⟩ := outer_loop n buf1 crc1 (by rw [hv, List.length_drop]; omega)
        refine ⟨buf', crc', ?_, ?_⟩
        · unfold crc32fast_base.update_fast_16_loop0 at hl ⊢
          rw [loop.eq_1]
          simp only [hb, bind_ok]
          exact hl
        · rw [← hf, hc, hv, ← List.foldl_append, ← List.map_append, List.take_append_drop]
      | 0, hn => omega

/-! ### `update_fast_16` and the `State` API -/

/-- **`update_fast_16` (slice-by-16) is zlib's CRC-32**, and it never panics. -/
theorem update_fast_16_eq (prev : U32) (buf : Slice U8) :
    crc32fast_base.update_fast_16 prev buf = .ok ⟨crc32 prev.bv (buf.val.map (·.bv))⟩ := by
  obtain ⟨buf', crc', hl, hf⟩ := outer_loop buf.val.length buf (~~~ prev) (by omega)
  unfold crc32fast_base.update_fast_16
  simp only [lift, bind_ok, hl, Aeneas.Std.uncurry_apply_pair, update_slow_eq]
  congr 2
  simp only [crc32, UScalar.bv_not, BitVec.not_not]
  rw [← UScalar.bv_not, hf]

theorem State_new_eq (s : U32) : crc32fast_base.State.new s = .ok ⟨s⟩ := rfl

/-- `State::update` is `update_fast_16` on the state. -/
theorem State_update_eq (s : U32) (buf : Slice U8) :
    crc32fast_base.State.update ⟨s⟩ buf = .ok ⟨⟨crc32 s.bv (buf.val.map (·.bv))⟩⟩ := by
  unfold crc32fast_base.State.update
  simp only [update_fast_16_eq, bind_ok]

theorem State_finalize_eq (s : U32) : crc32fast_base.State.finalize ⟨s⟩ = .ok s := rfl

/-- **The `State` API**: `State::new(init)`, `update(buf)`, `finalize()` is zlib's
`crc32(init, buf)`. -/
theorem state_crc32 (init : U32) (buf : Slice U8) :
    (do
      let st ← crc32fast_base.State.new init
      let st ← crc32fast_base.State.update st buf
      crc32fast_base.State.finalize st) = .ok ⟨crc32 init.bv (buf.val.map (·.bv))⟩ := by
  simp only [State_new_eq, State_update_eq, State_finalize_eq, bind_tc_ok]

/-- Incremental use: two `update` calls checksum the concatenation. -/
theorem state_crc32_append (init : U32) (b1 b2 : Slice U8) :
    (do
      let st ← crc32fast_base.State.new init
      let st ← crc32fast_base.State.update st b1
      let st ← crc32fast_base.State.update st b2
      crc32fast_base.State.finalize st) =
      .ok ⟨crc32 init.bv ((b1.val ++ b2.val).map (·.bv))⟩ := by
  simp only [State_new_eq, State_update_eq, State_finalize_eq, bind_tc_ok, List.map_append,
    crc32_append]

/-! ### The same, as equivalences with the specification (`pureVal`) -/

theorem update_slow_equiv_crc32 (prev : U32) (buf : Slice U8) :
    EquivLean.Equiv (fun o r => o = .ok ⟨r⟩) (crc32fast_base.update_slow prev buf)
      (EquivLean.pureVal (crc32 prev.bv (buf.val.map (·.bv)))) :=
  EquivLean.Aeneas.equiv_pureVal_iff.2 (by rw [update_slow_eq]; simp)

theorem update_fast_16_equiv_crc32 (prev : U32) (buf : Slice U8) :
    EquivLean.Equiv (fun o r => o = .ok ⟨r⟩) (crc32fast_base.update_fast_16 prev buf)
      (EquivLean.pureVal (crc32 prev.bv (buf.val.map (·.bv)))) :=
  EquivLean.Aeneas.equiv_pureVal_iff.2 (by rw [update_fast_16_eq]; simp)

end EquivLean.Demo.Crc32.Rust

#print axioms EquivLean.Demo.Crc32.Rust.update_slow_eq
#print axioms EquivLean.Demo.Crc32.Rust.update_fast_16_eq
#print axioms EquivLean.Demo.Crc32.Rust.State_update_eq
#print axioms EquivLean.Demo.Crc32.Rust.state_crc32
#print axioms EquivLean.Demo.Crc32.Rust.state_crc32_append
#print axioms EquivLean.Demo.Crc32.Rust.update_slow_equiv_crc32
#print axioms EquivLean.Demo.Crc32.Rust.update_fast_16_equiv_crc32

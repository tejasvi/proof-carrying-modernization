import EquivLean.Demo.XLang.Adler32.CBase
import EquivLean.Demo.XLang.Adler32.ModelLemmas

/-!
# zlib adler32 → model, C side: `adler32_z`

Total contracts (`Returns`, from any memory `m`, the caller's blocks unchanged): for every `adler` below `2^64`,
* `adler32_z(adler, Z_NULL, len)` with `len ≠ 1` returns 1 (`adler32_z_null`); with `len = 1` the call has no
  outcome (`adler32_z_null_one`: it reads `buf[0]`);
* `adler32_z(adler, buf, bs.length)`, `buf` pointing at a read-only array of the bytes `bs` (fewer than `2^28`),
  returns the model's `adler32z adler (some bs)` (`adler32_z_buf`), by the code's paths: one byte
  (`adler32_z_one`), fewer than 16 (`adler32_z_short`), 16 or more (`adler32_z_long`: the loop over blocks of
  `NMAX` bytes with its sixteen-byte inner loop, then the remaining bytes, sixteen and then one at a time).

The loop invariants state the model's sums (`sums`, `mainPath`) of the bytes read so far; the bytes of one turn are
named (`cirH_x0` … `cirH_x15`) so that the executor reads them, and `sums_take16` / `sums_take1` give the sums after
them.
-/

open CIR EquivLean.Cir
open EquivLean.Demo.Gen.Cir.Adler32.Adler32 (ctx module)
open EquivLean.Demo.XLang.Adler32 (adler32z sums mainPath pack BASE NMAX adler32z_one lo16 hi16)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

namespace EquivLean.Demo.XLang.Adler32.C

/-- Sixteen bytes from position `k`. -/
theorem take16 {bs : List Nat} {k x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat}
    (h0 : bs[k]? = some x0) (h1 : bs[k + 1]? = some x1) (h2 : bs[k + 2]? = some x2) (h3 : bs[k + 3]? = some x3)
    (h4 : bs[k + 4]? = some x4) (h5 : bs[k + 5]? = some x5) (h6 : bs[k + 6]? = some x6)
    (h7 : bs[k + 7]? = some x7) (h8 : bs[k + 8]? = some x8) (h9 : bs[k + 9]? = some x9)
    (h10 : bs[k + 10]? = some x10) (h11 : bs[k + 11]? = some x11) (h12 : bs[k + 12]? = some x12)
    (h13 : bs[k + 13]? = some x13) (h14 : bs[k + 14]? = some x14) (h15 : bs[k + 15]? = some x15) :
    (bs.drop k).take 16 = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_drop]
  by_cases hi : i < 16
  · simp only [hi, ↓reduceIte]
    match i, hi with
    | 0, _ => simpa using h0
    | 1, _ => simpa using h1
    | 2, _ => simpa using h2
    | 3, _ => simpa using h3
    | 4, _ => simpa using h4
    | 5, _ => simpa using h5
    | 6, _ => simpa using h6
    | 7, _ => simpa using h7
    | 8, _ => simpa using h8
    | 9, _ => simpa using h9
    | 10, _ => simpa using h10
    | 11, _ => simpa using h11
    | 12, _ => simpa using h12
    | 13, _ => simpa using h13
    | 14, _ => simpa using h14
    | 15, _ => simpa using h15
    | n + 16, h => exact absurd h (by omega)
  · simp only [hi, ↓reduceIte]
    rw [List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]

/-- The sums after `k + 16` bytes from position `J`: the sums after `k` bytes, then the sixteen bytes. -/
theorem sums_take16 {bs : List Nat} {J k A S a s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat}
    (ha : (sums A S ((bs.drop J).take k)).1 = a) (hs : (sums A S ((bs.drop J).take k)).2 = s)
    (h0 : bs[J + k]? = some x0) (h1 : bs[J + k + 1]? = some x1) (h2 : bs[J + k + 2]? = some x2)
    (h3 : bs[J + k + 3]? = some x3) (h4 : bs[J + k + 4]? = some x4) (h5 : bs[J + k + 5]? = some x5)
    (h6 : bs[J + k + 6]? = some x6) (h7 : bs[J + k + 7]? = some x7) (h8 : bs[J + k + 8]? = some x8)
    (h9 : bs[J + k + 9]? = some x9) (h10 : bs[J + k + 10]? = some x10) (h11 : bs[J + k + 11]? = some x11)
    (h12 : bs[J + k + 12]? = some x12) (h13 : bs[J + k + 13]? = some x13) (h14 : bs[J + k + 14]? = some x14)
    (h15 : bs[J + k + 15]? = some x15) :
    sums A S ((bs.drop J).take (k + 16)) =
      sums a s [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] := by
  rw [List.take_add, Adler32.sums_append, ha, hs, List.drop_drop,
    take16 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15]

/-- After a block of `NMAX` bytes and `MOD` of both sums: the main path from the next position. -/
theorem block_post {M : Nat × Nat} {bs : List Nat} {A S J k P1 P2 p q b : Nat}
    (hmp : M = mainPath A S (bs.drop J)) (hk : k = 16 * (347 - 1) + 16) (hlen : k ≤ (bs.drop J).length)
    (hnext : sums A S ((bs.drop J).take k) = (P1, P2)) (h1 : P1 % 65521 = p) (h2 : P2 % 65521 = q)
    (hb : J + k = b) : M = mainPath p q (bs.drop b) := by
  subst hk
  rw [hmp, Adler32.mainPath_block (show NMAX ≤ (bs.drop J).length from hlen)]
  change mainPath ((sums A S ((bs.drop J).take (16 * (347 - 1) + 16))).1 % 65521)
    ((sums A S ((bs.drop J).take (16 * (347 - 1) + 16))).2 % 65521) ((bs.drop J).drop (16 * (347 - 1) + 16)) = _
  rw [hnext, h1, h2, List.drop_drop, hb]

/-- One byte from position `k`. -/
theorem take1 {bs : List Nat} {k y : Nat} (h : bs[k]? = some y) : (bs.drop k).take 1 = [y] := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_drop]
  by_cases hi : i < 1
  · simp only [hi, ↓reduceIte]
    match i, hi with
    | 0, _ => simpa using h
    | n + 1, h => exact absurd h (by omega)
  · simp only [hi, ↓reduceIte]
    rw [List.getElem?_eq_none (by simp only [List.length_cons, List.length_nil]; omega)]

/-- The sums after `k + 1` bytes from position `J`. -/
theorem sums_take1 {bs : List Nat} {J k A S a s y : Nat}
    (ha : (sums A S ((bs.drop J).take k)).1 = a) (hs : (sums A S ((bs.drop J).take k)).2 = s)
    (h0 : bs[J + k]? = some y) :
    sums A S ((bs.drop J).take (k + 1)) = (a + y, s + (a + y)) := by
  rw [List.take_add, Adler32.sums_append, ha, hs, List.drop_drop, take1 h0]
  rfl

/-- One byte from the start. -/
theorem take1_start {bs : List Nat} {k y : Nat} (h : bs[k]? = some y) : (bs.drop k).take 1 = [y] := take1 h

/-- The sums after the first `k + 1` bytes. -/
theorem sums_take1_start {bs : List Nat} {k A S a s y : Nat}
    (ha : (sums A S (bs.take k)).1 = a) (hs : (sums A S (bs.take k)).2 = s) (h0 : bs[k]? = some y) :
    sums A S (bs.take (k + 1)) = (a + y, s + (a + y)) := by
  rw [List.take_add, Adler32.sums_append, ha, hs, take1_start h0]
  rfl

theorem pack_congr {a a' s s' : Nat} (h1 : a = a') (h2 : s = s') : pack a s = pack a' s' := by
  rw [h1, h2]

theorem or_congr_left {x x' y : Nat} (h : x = x') : ((x ||| y : Nat) : Int) = ((x' ||| y : Nat) : Int) := by
  rw [h]

theorem pack_lt {a s : Nat} (ha : a < 2 ^ 32) (hs : s < 2 ^ 32) : pack a s < 2 ^ 64 := by
  unfold pack
  rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 16 = 65536 from rfl]
  exact Nat.or_lt_two_pow (by omega) (by omega)

/-- The model's value is an `unsigned long`. -/
theorem adler32z_lt (a0 : Nat) (bs : List Nat) (hbs : ∀ b ∈ bs, b < 256) :
    adler32z a0 (some bs) < 2 ^ 64 := by
  by_cases h1 : bs.length = 1
  · obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp h1
    have hb := hbs b (by simp)
    rw [Adler32.adler32z_one]
    simp only [lo16, shiftRight_16, BASE]
    apply pack_lt <;> (repeat' split) <;> omega
  · by_cases h16 : bs.length < 16
    · rw [Adler32.adler32z_short a0 bs h1 h16]
      have hL := (Adler32.sums_le (a0 &&& 0xffff) ((a0 >>> 16) &&& 0xffff) bs hbs).1
      simp only [lo16, shiftRight_16, BASE] at hL ⊢
      apply pack_lt
      · split <;> omega
      · omega
    · rw [Adler32.adler32z_long a0 bs (by omega), Adler32.mainPath_eq _ _ bs (by intro h; simp [h] at h16)]
      simp only [BASE]
      apply pack_lt <;> omega

/-- The model when the bytes run out after whole blocks of `NMAX`. -/
theorem final_zero {a0 : Nat} {bs : List Nat} {A S buf : Nat} (hl16 : 16 ≤ bs.length)
    (hmp : mainPath (a0 % 65536) (a0 / 65536 % 65536) bs = mainPath A S (bs.drop buf)) (hb : bs.length ≤ buf) :
    adler32z a0 (some bs) = pack A S := by
  rw [Adler32.adler32z_long a0 bs hl16, hi16, lo16, hmp, List.drop_eq_nil_of_le hb,
    Adler32.mainPath_tail (by simp [NMAX])]
  rfl

/-- The model after the remaining bytes (fewer than `NMAX`, at least one) and `MOD` of both sums. -/
theorem final_tail {a0 : Nat} {bs : List Nat} {A S J buf : Nat} (hl16 : 16 ≤ bs.length)
    (hmp : mainPath (a0 % 65536) (a0 / 65536 % 65536) bs = mainPath A S (bs.drop J))
    (hJ : J < bs.length) (hJn : bs.length < J + 5552) (hb : bs.length ≤ buf) :
    adler32z a0 (some bs) =
      pack ((sums A S ((bs.drop J).take (buf - J))).1 % 65521) ((sums A S ((bs.drop J).take (buf - J))).2 % 65521) := by
  rw [Adler32.adler32z_long a0 bs hl16, hi16, lo16, hmp,
    Adler32.mainPath_tail (by simp only [List.length_drop, NMAX]; omega),
    List.take_of_length_le (by simp only [List.length_drop]; omega)]
  simp only [List.length_drop, show bs.length - J ≠ 0 by omega, ↓reduceIte]
  rfl

/-- **`adler32_z(adler, Z_NULL, len)` with `len ≠ 1` returns 1.** -/
theorem adler32_z_null (a0 len : Nat) (m : Mem) (ha : a0 < 2 ^ 64) (hlen : len < 2 ^ 64) (h1 : len ≠ 1) :
    Returns ctx "adler32_z" [.int a0, .ptr .null, .int len] m
      (fun r m' => r = some (.int 1) ∧ m.next ≤ m'.next ∧ ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_b1 := bw_and_ffff_mod a0 ha
  have cirH_b3 := bw_shr16_and a0 ha
  have cirH_h1 : ¬ ((len : Int) = 1) := by omega
  cir_start
  cir_vcg

/-- `adler32_z(adler, Z_NULL, 1)` reads `buf[0]` through the null pointer: it has no outcome. -/
theorem adler32_z_null_one (a0 : Nat) (m : Mem) (ha : a0 < 2 ^ 64) (a : Exit × Mem) :
    evalCall ctx "adler32_z" [.int a0, .ptr .null, .int 1] m ≠ .ok a := by
  intro hr
  have hs : (evalCall ctx "adler32_z" [.int a0, .ptr .null, .int 1] m).holds (· = a) := by rw [hr]; rfl
  have cirH_b1 := bw_and_ffff_mod a0 ha
  have cirH_b3 := bw_shr16_and a0 ha
  cir_hstep hs
  cir_hrun_c hs

/-- **`adler32_z(adler, buf, 1)`**: one byte. -/
theorem adler32_z_one (a0 b : Nat) (m : Mem) (bb : Nat) (hbb : bb < m.next)
    (hm : m.blocks bb = some ⟨.readonly, true, .array (.int false 8) 1, .arr [Val.int b]⟩)
    (ha : a0 < 2 ^ 64) (hb : b < 256) :
    Returns ctx "adler32_z" [.int a0, .ptr (.loc bb [.idx 0]), .int 1] m
      (fun r m' => r = some (.int (adler32z a0 (some [b]))) ∧ m.next ≤ m'.next ∧
        ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_b1 := bw_and_ffff_mod a0 ha
  have cirH_b3 := bw_shr16_and a0 ha
  have cirH_or : ∀ x y : Int, 0 ≤ x → x < 2 ^ 64 → 0 ≤ y → y < 2 ^ 64 →
      bitwise false 64 (fun a b => a ||| b) x y = ((x.toNat ||| y.toNat : Nat) : Int) := bw_or_int
  have cirH_orr := or_not_gt
  have cirH_m0 := hm
  cir_start
  cir_vcg
  all_goals
    clear cirH_or cirH_orr cirH_m0
    rw [or_pack _ _ (by omega), adler32z_one]
    simp only [lo16, shiftRight_16, BASE]
    congr 2 <;> (repeat' split) <;> omega

/-- **`adler32_z(adler, buf, len)` with `len < 16`, `len ≠ 1`**: the bytes one at a time, one subtraction for
`adler`, `MOD28` of `sum2`. -/
theorem adler32_z_short (a0 : Nat) (bs : List Nat) (m : Mem) (bb : Nat) (hbb : bb < m.next)
    (hm : m.blocks bb =
      some ⟨.readonly, true, .array (.int false 8) bs.length, .arr (bs.map fun b : Nat => Val.int b)⟩)
    (ha : a0 < 2 ^ 64) (hbs : ∀ b ∈ bs, b < 256) (h1 : bs.length ≠ 1) (h16 : bs.length < 16) :
    Returns ctx "adler32_z" [.int a0, .ptr (.loc bb [.idx 0]), .int bs.length] m
      (fun r m' => r = some (.int (adler32z a0 (some bs))) ∧ m.next ≤ m'.next ∧
        ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_b1 := bw_and_ffff_mod a0 ha
  have cirH_b3 := bw_shr16_and a0 ha
  have cirH_or : ∀ x y : Int, 0 ≤ x → x < 2 ^ 64 → 0 ≤ y → y < 2 ^ 64 →
      bitwise false 64 (fun a b => a ||| b) x y = ((x.toNat ||| y.toNat : Nat) : Int) := bw_or_int
  have cirH_orr := or_not_gt
  have cirH_m0 := hm
  have cirH_h1 : ¬ ((bs.length : Int) = 1) := by omega
  cir_start
  cir_vcg
  cir_loop (fun len buf adler sum2 => buf + len = bs.length ∧
      adler = (sums (a0 % 65536) (a0 / 65536 % 65536) (bs.take buf)).1 ∧
      sum2 = (sums (a0 % 65536) (a0 / 65536 % 65536) (bs.take buf)).2)
    (fun len buf adler sum2 => (len : Int))
  case cir_init_goal =>
    cir_vcg
    all_goals simp [Adler32.sums]
  case cir_step_goal =>
    obtain ⟨hbl, hadl, hsum⟩ := cirH_user
    subst cir_nat0 cir_nat2 cir_nat3
    have hL : ∀ b ∈ bs.take buf, b < 256 := fun b hb => hbs b (List.mem_of_mem_take hb)
    obtain ⟨hb1, hb2⟩ := Adler32.sums_le (a0 % 65536) (a0 / 65536 % 65536) _ hL
    have hlenL : (bs.take buf).length ≤ 15 := by simp only [List.length_take]; omega
    have hm1 := Nat.mul_le_mul hlenL (show a0 % 65536 ≤ 65535 by omega)
    have hm2 := Nat.mul_le_mul hlenL hlenL
    have hadlb : adler ≤ 100000 := by rw [hadl]; omega
    have hsumb : sum2 ≤ 2000000 := by rw [hsum]; omega
    clear hL hb1 hb2 hlenL hm1 hm2
    by_cases hz : len = 0
    · -- the end: one subtraction for `adler`, `MOD28` of `sum2`, the return value
      cir_vcg
      all_goals clear cirH_or cirH_m0
      all_goals cir_strip_mdata
      all_goals first
        | (rename_i h
           rcases h with h | h
           · omega
           · exact absurd h (or_not_gt _ _ (by omega) (by omega)))
        | skip
      all_goals
        rw [List.take_of_length_le (show bs.length ≤ buf by omega)] at hadl hsum
        have eY : ((sum2 : Int) % 65521 * 65536).toNat = (sum2 % 65521) <<< 16 := by
          rw [Nat.shiftLeft_eq]; omega
        rw [eY, Adler32.adler32z_short a0 bs h1 h16, hi16, lo16, ← hadl, ← hsum]
        unfold pack
        simp only [BASE]
        refine or_congr_left ?_
        by_cases hc : 65521 ≤ adler <;> simp only [hc, ↓reduceIte] <;> omega
    · obtain ⟨y, cirH_y⟩ : ∃ x, bs[buf]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hy := hbs _ (List.mem_of_getElem? cirH_y)
      have hnext := sums_take1_start hadl.symm hsum.symm cirH_y
      cir_vcg

/-- **`adler32_z(adler, buf, len)` with `len ≥ 16`**: blocks of `NMAX` bytes (sixteen at a time), each followed by
`MOD` of both sums, then the remaining bytes (sixteen at a time, then one at a time) and `MOD` of both sums. -/
theorem adler32_z_long (a0 : Nat) (bs : List Nat) (m : Mem) (bb : Nat) (hbb : bb < m.next)
    (hm : m.blocks bb =
      some ⟨.readonly, true, .array (.int false 8) bs.length, .arr (bs.map fun b : Nat => Val.int b)⟩)
    (ha : a0 < 2 ^ 64) (hbs : ∀ b ∈ bs, b < 256) (hl16 : 16 ≤ bs.length) (hl : bs.length < 2 ^ 28) :
    Returns ctx "adler32_z" [.int a0, .ptr (.loc bb [.idx 0]), .int bs.length] m
      (fun r m' => r = some (.int (adler32z a0 (some bs))) ∧ m.next ≤ m'.next ∧
        ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  have cirH_b1 := bw_and_ffff_mod a0 ha
  have cirH_b3 := bw_shr16_and a0 ha
  have cirH_or : ∀ x y : Int, 0 ≤ x → x < 2 ^ 64 → 0 ≤ y → y < 2 ^ 64 →
      bitwise false 64 (fun a b => a ||| b) x y = ((x.toNat ||| y.toNat : Nat) : Int) := bw_or_int
  have cirH_orr := or_not_gt
  have cirH_m0 := hm
  cir_start
  cir_vcg
  cir_loop (fun len buf adler sum2 => buf + len = bs.length ∧ adler < 65536 ∧ sum2 < 65536 ∧
      mainPath (a0 % 65536) (a0 / 65536 % 65536) bs = mainPath adler sum2 (bs.drop buf))
    (fun len buf adler sum2 => (len : Int))
  case cir_init_goal =>
    cir_vcg
  case cir_step_goal =>
    obtain ⟨hbl, hA, hS, hmp⟩ := cirH_user
    subst cir_nat0 cir_nat2 cir_nat3
    by_cases hc : 5552 ≤ len
    · -- a block of `NMAX` bytes
      generalize hJ : buf = J at *
      generalize hAA : adler = A at *
      generalize hSS : sum2 = S at *
      cir_vcg
      cir_loop (fun buf adler sum2 n => 1 ≤ n ∧ n ≤ 347 ∧ buf = J + 16 * (347 - n) ∧
          adler = (sums A S ((bs.drop J).take (16 * (347 - n)))).1 ∧
          sum2 = (sums A S ((bs.drop J).take (16 * (347 - n)))).2)
        (fun buf adler sum2 n => (n : Int))
      case cir_init_goal =>
        cir_vcg
        all_goals simp [Adler32.sums]
      case cir_step_goal =>
        obtain ⟨hn1, hn2, hbuf, hadl, hsum⟩ := cirH_user
        -- the bounds of the sums so far
        have hL : ∀ b ∈ (bs.drop J).take (16 * (347 - n)), b < 256 :=
          fun b hb => hbs b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
        obtain ⟨hb1, hb2⟩ := Adler32.sums_le A S _ hL
        have hlenL : ((bs.drop J).take (16 * (347 - n))).length ≤ 5536 := by
          simp only [List.length_take]; omega
        have hm1 := Nat.mul_le_mul hlenL (show A ≤ 65535 by omega)
        have hm2 := Nat.mul_le_mul hlenL hlenL
        have hadlb : adler ≤ 1500000 := by rw [hadl]; omega
        have hsumb : sum2 ≤ 9000000000 := by rw [hsum]; omega
        clear hL hb1 hb2 hlenL hm1 hm2
        -- the sixteen bytes
        have hlt : buf + 15 < bs.length := by omega
        obtain ⟨x0, cirH_x0⟩ : ∃ x, bs[buf]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x1, cirH_x1⟩ : ∃ x, bs[buf + 1]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x2, cirH_x2⟩ : ∃ x, bs[buf + 2]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x3, cirH_x3⟩ : ∃ x, bs[buf + 3]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x4, cirH_x4⟩ : ∃ x, bs[buf + 4]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x5, cirH_x5⟩ : ∃ x, bs[buf + 5]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x6, cirH_x6⟩ : ∃ x, bs[buf + 6]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x7, cirH_x7⟩ : ∃ x, bs[buf + 7]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x8, cirH_x8⟩ : ∃ x, bs[buf + 8]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x9, cirH_x9⟩ : ∃ x, bs[buf + 9]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x10, cirH_x10⟩ : ∃ x, bs[buf + 10]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x11, cirH_x11⟩ : ∃ x, bs[buf + 11]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x12, cirH_x12⟩ : ∃ x, bs[buf + 12]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x13, cirH_x13⟩ : ∃ x, bs[buf + 13]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x14, cirH_x14⟩ : ∃ x, bs[buf + 14]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨x15, cirH_x15⟩ : ∃ x, bs[buf + 15]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hx0 := hbs _ (List.mem_of_getElem? cirH_x0)
        have hx1 := hbs _ (List.mem_of_getElem? cirH_x1)
        have hx2 := hbs _ (List.mem_of_getElem? cirH_x2)
        have hx3 := hbs _ (List.mem_of_getElem? cirH_x3)
        have hx4 := hbs _ (List.mem_of_getElem? cirH_x4)
        have hx5 := hbs _ (List.mem_of_getElem? cirH_x5)
        have hx6 := hbs _ (List.mem_of_getElem? cirH_x6)
        have hx7 := hbs _ (List.mem_of_getElem? cirH_x7)
        have hx8 := hbs _ (List.mem_of_getElem? cirH_x8)
        have hx9 := hbs _ (List.mem_of_getElem? cirH_x9)
        have hx10 := hbs _ (List.mem_of_getElem? cirH_x10)
        have hx11 := hbs _ (List.mem_of_getElem? cirH_x11)
        have hx12 := hbs _ (List.mem_of_getElem? cirH_x12)
        have hx13 := hbs _ (List.mem_of_getElem? cirH_x13)
        have hx14 := hbs _ (List.mem_of_getElem? cirH_x14)
        have hx15 := hbs _ (List.mem_of_getElem? cirH_x15)
        -- the sums after the sixteen bytes
        have hnext := sums_take16 (bs := bs) (J := J) (k := 16 * (347 - n)) hadl.symm hsum.symm
          (by rw [← hbuf]; exact cirH_x0) (by rw [← hbuf]; exact cirH_x1) (by rw [← hbuf]; exact cirH_x2)
          (by rw [← hbuf]; exact cirH_x3) (by rw [← hbuf]; exact cirH_x4) (by rw [← hbuf]; exact cirH_x5)
          (by rw [← hbuf]; exact cirH_x6) (by rw [← hbuf]; exact cirH_x7) (by rw [← hbuf]; exact cirH_x8)
          (by rw [← hbuf]; exact cirH_x9) (by rw [← hbuf]; exact cirH_x10) (by rw [← hbuf]; exact cirH_x11)
          (by rw [← hbuf]; exact cirH_x12) (by rw [← hbuf]; exact cirH_x13) (by rw [← hbuf]; exact cirH_x14)
          (by rw [← hbuf]; exact cirH_x15)
        simp only [Adler32.sums_cons, Adler32.sums_nil] at hnext
        cir_vcg
        -- the last turn (`n` was 1): `MOD` of both sums, the main path's next block
        rename_i hq
        clear cirH_or cirH_orr cirH_m0
        have hn1' : n = 1 := by
          have : (n : Int) - 1 = 0 := by simpa using hq
          omega
        subst hn1'
        cir_strip_mdata
        exact block_post hmp rfl (by simp only [List.length_drop]; omega) hnext (by omega) (by omega) (by omega)
    · -- fewer than `NMAX` bytes remain
      by_cases h0 : len = 0
      · -- none: the sums after the last block
        cir_vcg
        clear cirH_or cirH_orr cirH_m0
        cir_strip_mdata
        have e : ((sum2 : Int) * 65536).toNat = sum2 <<< 16 := by rw [Nat.shiftLeft_eq]; omega
        rw [e, final_zero hl16 hmp (by omega)]
        rfl
      · generalize hJ : buf = J at *
        generalize hAA : adler = A at *
        generalize hSS : sum2 = S at *
        generalize hRR : len = R at *
        cir_vcg
        cir_loop (fun len buf adler sum2 => J ≤ buf ∧ buf + len = bs.length ∧
            adler = (sums A S ((bs.drop J).take (buf - J))).1 ∧
            sum2 = (sums A S ((bs.drop J).take (buf - J))).2)
          (fun len buf adler sum2 => (len : Int))
        case cir_init_goal =>
          cir_vcg
          all_goals simp [Adler32.sums]
        case cir_step_goal =>
          obtain ⟨hJb, hbl4, hadl, hsum⟩ := cirH_user
          subst cir_nat0 cir_nat2 cir_nat3
          -- the bounds of the sums so far
          have hL : ∀ b ∈ (bs.drop J).take (buf - J), b < 256 :=
            fun b hb => hbs b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
          obtain ⟨hb1, hb2⟩ := Adler32.sums_le A S _ hL
          have hlenL : ((bs.drop J).take (buf - J)).length ≤ 5552 := by
            simp only [List.length_take]; omega
          have hm1 := Nat.mul_le_mul hlenL (show A ≤ 65535 by omega)
          have hm2 := Nat.mul_le_mul hlenL hlenL
          have hadlb : adler ≤ 1500000 := by rw [hadl]; omega
          have hsumb : sum2 ≤ 9000000000 := by rw [hsum]; omega
          clear hL hb1 hb2 hlenL hm1 hm2
          by_cases hc4 : 16 ≤ len
          · -- sixteen bytes
            have hlt : buf + 15 < bs.length := by omega
            obtain ⟨x0, cirH_x0⟩ : ∃ x, bs[buf]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x1, cirH_x1⟩ : ∃ x, bs[buf + 1]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x2, cirH_x2⟩ : ∃ x, bs[buf + 2]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x3, cirH_x3⟩ : ∃ x, bs[buf + 3]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x4, cirH_x4⟩ : ∃ x, bs[buf + 4]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x5, cirH_x5⟩ : ∃ x, bs[buf + 5]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x6, cirH_x6⟩ : ∃ x, bs[buf + 6]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x7, cirH_x7⟩ : ∃ x, bs[buf + 7]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x8, cirH_x8⟩ : ∃ x, bs[buf + 8]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x9, cirH_x9⟩ : ∃ x, bs[buf + 9]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x10, cirH_x10⟩ : ∃ x, bs[buf + 10]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x11, cirH_x11⟩ : ∃ x, bs[buf + 11]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x12, cirH_x12⟩ : ∃ x, bs[buf + 12]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x13, cirH_x13⟩ : ∃ x, bs[buf + 13]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x14, cirH_x14⟩ : ∃ x, bs[buf + 14]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨x15, cirH_x15⟩ : ∃ x, bs[buf + 15]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
            have hx0 := hbs _ (List.mem_of_getElem? cirH_x0)
            have hx1 := hbs _ (List.mem_of_getElem? cirH_x1)
            have hx2 := hbs _ (List.mem_of_getElem? cirH_x2)
            have hx3 := hbs _ (List.mem_of_getElem? cirH_x3)
            have hx4 := hbs _ (List.mem_of_getElem? cirH_x4)
            have hx5 := hbs _ (List.mem_of_getElem? cirH_x5)
            have hx6 := hbs _ (List.mem_of_getElem? cirH_x6)
            have hx7 := hbs _ (List.mem_of_getElem? cirH_x7)
            have hx8 := hbs _ (List.mem_of_getElem? cirH_x8)
            have hx9 := hbs _ (List.mem_of_getElem? cirH_x9)
            have hx10 := hbs _ (List.mem_of_getElem? cirH_x10)
            have hx11 := hbs _ (List.mem_of_getElem? cirH_x11)
            have hx12 := hbs _ (List.mem_of_getElem? cirH_x12)
            have hx13 := hbs _ (List.mem_of_getElem? cirH_x13)
            have hx14 := hbs _ (List.mem_of_getElem? cirH_x14)
            have hx15 := hbs _ (List.mem_of_getElem? cirH_x15)
            have hJk : J + (buf - J) = buf := by omega
            have hnext := sums_take16 (bs := bs) (J := J) (k := buf - J) hadl.symm hsum.symm
              (by rw [hJk]; exact cirH_x0) (by rw [hJk]; exact cirH_x1) (by rw [hJk]; exact cirH_x2)
              (by rw [hJk]; exact cirH_x3) (by rw [hJk]; exact cirH_x4) (by rw [hJk]; exact cirH_x5)
              (by rw [hJk]; exact cirH_x6) (by rw [hJk]; exact cirH_x7) (by rw [hJk]; exact cirH_x8)
              (by rw [hJk]; exact cirH_x9) (by rw [hJk]; exact cirH_x10) (by rw [hJk]; exact cirH_x11)
              (by rw [hJk]; exact cirH_x12) (by rw [hJk]; exact cirH_x13) (by rw [hJk]; exact cirH_x14)
              (by rw [hJk]; exact cirH_x15)
            simp only [Adler32.sums_cons, Adler32.sums_nil] at hnext
            cir_vcg
          · -- the last bytes, one at a time
            cir_vcg
            cir_loop (fun len buf adler sum2 => J ≤ buf ∧ buf + len = bs.length ∧
                adler = (sums A S ((bs.drop J).take (buf - J))).1 ∧
                sum2 = (sums A S ((bs.drop J).take (buf - J))).2)
              (fun len buf adler sum2 => (len : Int))
            case cir_init_goal =>
              cir_vcg
            case cir_step_goal =>
              obtain ⟨hJb5, hbl5, hadl5, hsum5⟩ := cirH_user
              subst cir_nat0 cir_nat2 cir_nat3
              have hL : ∀ b ∈ (bs.drop J).take (buf - J), b < 256 :=
                fun b hb => hbs b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
              obtain ⟨hb1, hb2⟩ := Adler32.sums_le A S _ hL
              have hlenL : ((bs.drop J).take (buf - J)).length ≤ 5552 := by
                simp only [List.length_take]; omega
              have hm1 := Nat.mul_le_mul hlenL (show A ≤ 65535 by omega)
              have hm2 := Nat.mul_le_mul hlenL hlenL
              have hadlb5 : adler ≤ 1500000 := by rw [hadl5]; omega
              have hsumb5 : sum2 ≤ 9000000000 := by rw [hsum5]; omega
              clear hL hb1 hb2 hlenL hm1 hm2
              by_cases hz : len = 0
              · -- the end: `MOD` of both sums, the return value
                cir_vcg
                all_goals clear cirH_or cirH_m0
                all_goals cir_strip_mdata
                all_goals first
                  | (rename_i h
                     rcases h with h | h
                     · omega
                     · exact absurd h (or_not_gt _ _ (by omega) (by omega)))
                  | skip
                have e : ((sum2 : Int) % 65521 * 65536).toNat = (sum2 % 65521) <<< 16 := by
                  rw [Nat.shiftLeft_eq]; omega
                have e2 : ((adler : Int) % 65521).toNat = adler % 65521 := by omega
                rw [e, e2, final_tail hl16 hmp (by omega) (by omega) (show bs.length ≤ buf by omega), ← hadl5,
                  ← hsum5]
                rfl
              · obtain ⟨y, cirH_y⟩ : ∃ x, bs[buf]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
                have hy := hbs _ (List.mem_of_getElem? cirH_y)
                have hJk : J + (buf - J) = buf := by omega
                have hnext := sums_take1 (bs := bs) (J := J) (k := buf - J) hadl5.symm hsum5.symm
                  (by rw [hJk]; exact cirH_y)
                cir_vcg

/-- **`adler32_z(adler, buf, len)` on a buffer of fewer than `2^28` bytes returns the model's value**, and changes
no block of the caller. -/
theorem adler32_z_buf (a0 : Nat) (bs : List Nat) (m : Mem) (bb : Nat) (hbb : bb < m.next)
    (hm : m.blocks bb =
      some ⟨.readonly, true, .array (.int false 8) bs.length, .arr (bs.map fun b : Nat => Val.int b)⟩)
    (ha : a0 < 2 ^ 64) (hbs : ∀ b ∈ bs, b < 256) (hl : bs.length < 2 ^ 28) :
    Returns ctx "adler32_z" [.int a0, .ptr (.loc bb [.idx 0]), .int bs.length] m
      (fun r m' => r = some (.int (adler32z a0 (some bs))) ∧ m.next ≤ m'.next ∧
        ∀ b, b < m.next → m'.blocks b = m.blocks b) := by
  by_cases h1 : bs.length = 1
  · obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp h1
    exact adler32_z_one a0 b m bb hbb (by simpa using hm) ha (hbs b (by simp))
  · by_cases h16 : bs.length < 16
    · exact adler32_z_short a0 bs m bb hbb hm ha hbs h1 h16
    · exact adler32_z_long a0 bs m bb hbb hm ha hbs (by omega) hl

end EquivLean.Demo.XLang.Adler32.C

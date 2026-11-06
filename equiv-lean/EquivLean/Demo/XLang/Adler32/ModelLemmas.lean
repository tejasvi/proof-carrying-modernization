import EquivLean.Demo.XLang.Adler32.Model

/-!
# zlib adler32 model: facts for the C and Rust sides

* `sums`: `sums_append` (the `DO16` loops are 16 steps of `DO1`), the closed forms `sums_fst` (`a + Σ bytes`) and
  `sums_snd` (`s + len · a + wsum`, byte `i` of `n` counted `n - i` times), `sums_mod` (the sums only depend on
  the start values modulo `BASE`, modulo `BASE`), and the bounds `sums_le`.
* The NMAX-block invariant: `mainPath_block`, `mainPath_tail` (one turn of the main path) and `mainPath_eq`: on
  nonempty bytes the main path is `sums` followed by `% BASE`, its blocks' `MOD`s notwithstanding.
* The paths of `adler32z` (`adler32z_none`, `adler32z_one`, `adler32z_short`, `adler32z_long`) and the bit forms
  `pack_eq`, `lo16`, `hi16`.
-/

namespace EquivLean.Demo.XLang.Adler32

/-! ## `sums` -/

theorem sums_nil (a s : Nat) : sums a s [] = (a, s) := rfl

theorem sums_cons (a s b : Nat) (bs : List Nat) : sums a s (b :: bs) = sums (a + b) (s + (a + b)) bs := rfl

theorem sums_append : ∀ (a s : Nat) (xs ys : List Nat),
    sums a s (xs ++ ys) = sums (sums a s xs).1 (sums a s xs).2 ys
  | _, _, [], _ => rfl
  | a, s, x :: xs, ys => by
    rw [List.cons_append, sums_cons, sums_cons]
    exact sums_append _ _ xs ys

/-- The weighted byte sum: byte `i` of `n` counted `n - i` times. -/
def wsum : List Nat → Nat
  | [] => 0
  | b :: bs => (bs.length + 1) * b + wsum bs

theorem sums_fst : ∀ (a s : Nat) (bs : List Nat), (sums a s bs).1 = a + bs.sum
  | _, _, [] => by simp [sums]
  | a, s, b :: bs => by
    rw [sums_cons, sums_fst, List.sum_cons]
    omega

theorem sums_snd : ∀ (a s : Nat) (bs : List Nat), (sums a s bs).2 = s + bs.length * a + wsum bs
  | _, _, [] => by simp [sums, wsum]
  | a, s, b :: bs => by
    rw [sums_cons, sums_snd]
    simp only [List.length_cons, wsum, Nat.add_mul, Nat.mul_add, Nat.one_mul]
    omega

/-- The sums modulo `BASE` only depend on the start values modulo `BASE`. -/
theorem sums_mod (a s a' s' : Nat) (bs : List Nat) (ha : a % BASE = a' % BASE) (hs : s % BASE = s' % BASE) :
    (sums a s bs).1 % BASE = (sums a' s' bs).1 % BASE ∧ (sums a s bs).2 % BASE = (sums a' s' bs).2 % BASE := by
  rw [sums_fst, sums_fst, sums_snd, sums_snd]
  have hm : bs.length * a % BASE = bs.length * a' % BASE := by rw [Nat.mul_mod, ha, ← Nat.mul_mod]
  unfold BASE at *
  constructor <;> omega

theorem sum_le : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) → bs.sum ≤ 255 * bs.length
  | [], _ => by simp
  | b :: bs, h => by
    have hb := h b (by simp)
    have ih := sum_le bs (fun x hx => h x (by simp [hx]))
    rw [List.sum_cons, List.length_cons]
    omega

theorem wsum_le : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) → wsum bs ≤ 255 * (bs.length * bs.length)
  | [], _ => by simp [wsum]
  | b :: bs, h => by
    have hb : b ≤ 255 := by have := h b (by simp); omega
    have ih := wsum_le bs (fun x hx => h x (by simp [hx]))
    have h1 : (bs.length + 1) * b ≤ (bs.length + 1) * 255 := Nat.mul_le_mul_left _ hb
    have e : (bs.length + 1) * (bs.length + 1) = bs.length * bs.length + 2 * bs.length + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
    simp only [wsum, List.length_cons]
    rw [e]
    omega

/-- Bounds of the sums over bytes below 256. -/
theorem sums_le (a s : Nat) (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    (sums a s bs).1 ≤ a + 255 * bs.length ∧
      (sums a s bs).2 ≤ s + bs.length * a + 255 * (bs.length * bs.length) := by
  rw [sums_fst, sums_snd]
  have := sum_le bs h
  have := wsum_le bs h
  constructor <;> omega

/-! ## The main path: the NMAX-block invariant -/

theorem mainPath_block {a s : Nat} {bs : List Nat} (h : NMAX ≤ bs.length) :
    mainPath a s bs =
      mainPath ((sums a s (bs.take NMAX)).1 % BASE) ((sums a s (bs.take NMAX)).2 % BASE) (bs.drop NMAX) := by
  rw [mainPath, dite_eq_left h]

theorem mainPath_tail {a s : Nat} {bs : List Nat} (h : bs.length < NMAX) :
    mainPath a s bs =
      if bs.length = 0 then (a, s) else ((sums a s bs).1 % BASE, (sums a s bs).2 % BASE) := by
  rw [mainPath, dite_eq_right (by omega)]

/-- **The NMAX-block invariant**: on nonempty bytes, `adler32_z`'s main path gives the sums of all the bytes
modulo `BASE`; the `MOD` after each block of `NMAX` bytes does not change the result. -/
theorem mainPath_eq (a s : Nat) (bs : List Nat) (hne : bs ≠ []) :
    mainPath a s bs = ((sums a s bs).1 % BASE, (sums a s bs).2 % BASE) := by
  by_cases h : NMAX ≤ bs.length
  · rw [mainPath_block h]
    have hsplit : sums a s bs =
        sums (sums a s (bs.take NMAX)).1 (sums a s (bs.take NMAX)).2 (bs.drop NMAX) := by
      rw [← sums_append, List.take_append_drop]
    by_cases hd : bs.drop NMAX = []
    · rw [hd, mainPath_tail (by simp [NMAX]), hsplit, hd]
      rfl
    · rw [mainPath_eq _ _ (bs.drop NMAX) hd, hsplit]
      obtain ⟨h1, h2⟩ := sums_mod ((sums a s (bs.take NMAX)).1 % BASE) ((sums a s (bs.take NMAX)).2 % BASE)
        (sums a s (bs.take NMAX)).1 (sums a s (bs.take NMAX)).2 (bs.drop NMAX) (Nat.mod_mod _ _) (Nat.mod_mod _ _)
      rw [h1, h2]
  · rw [mainPath_tail (by omega), ite_eq_right (by simpa using hne)]
termination_by bs.length
decreasing_by simp only [List.length_drop]; unfold NMAX at h ⊢; omega

/-! ## The paths of `adler32_z` -/

theorem adler32z_none (adler : Nat) : adler32z adler none = 1 := rfl

theorem adler32z_one (adler b : Nat) :
    adler32z adler (some [b]) =
      pack (if BASE ≤ (adler &&& 0xffff) + b then (adler &&& 0xffff) + b - BASE else (adler &&& 0xffff) + b)
        (if BASE ≤ ((adler >>> 16) &&& 0xffff) +
            (if BASE ≤ (adler &&& 0xffff) + b then (adler &&& 0xffff) + b - BASE else (adler &&& 0xffff) + b)
          then ((adler >>> 16) &&& 0xffff) +
            (if BASE ≤ (adler &&& 0xffff) + b then (adler &&& 0xffff) + b - BASE else (adler &&& 0xffff) + b) - BASE
          else ((adler >>> 16) &&& 0xffff) +
            (if BASE ≤ (adler &&& 0xffff) + b then (adler &&& 0xffff) + b - BASE else (adler &&& 0xffff) + b)) := by
  rfl

theorem adler32z_short (adler : Nat) (bs : List Nat) (h1 : bs.length ≠ 1) (h2 : bs.length < 16) :
    adler32z adler (some bs) =
      pack (if BASE ≤ (sums (adler &&& 0xffff) ((adler >>> 16) &&& 0xffff) bs).1
          then (sums (adler &&& 0xffff) ((adler >>> 16) &&& 0xffff) bs).1 - BASE
          else (sums (adler &&& 0xffff) ((adler >>> 16) &&& 0xffff) bs).1)
        ((sums (adler &&& 0xffff) ((adler >>> 16) &&& 0xffff) bs).2 % BASE) := by
  simp only [adler32z, ite_eq_right h1, ite_eq_left h2]

theorem adler32z_long (adler : Nat) (bs : List Nat) (h : 16 ≤ bs.length) :
    adler32z adler (some bs) =
      pack (mainPath (adler &&& 0xffff) ((adler >>> 16) &&& 0xffff) bs).1
        (mainPath (adler &&& 0xffff) ((adler >>> 16) &&& 0xffff) bs).2 := by
  simp only [adler32z, ite_eq_right (show bs.length ≠ 1 by omega), ite_eq_right (show ¬ bs.length < 16 by omega)]

/-! ## Bit forms -/

/-- `a | (s << 16)` is `a + s · 2^16` when `a < 2^16`. -/
theorem pack_eq {a : Nat} (s : Nat) (h : a < 65536) : pack a s = a + s * 65536 := by
  unfold pack
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 16) (by omega) s, Nat.shiftLeft_eq]
  omega

theorem lo16 (x : Nat) : x &&& 0xffff = x % 65536 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod x 16

theorem hi16 (x : Nat) : (x >>> 16) &&& 0xffff = x / 65536 % 65536 := by
  rw [lo16, Nat.shiftRight_eq_div_pow]

end EquivLean.Demo.XLang.Adler32

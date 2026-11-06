import CIR.Std.Float
import CIR.Semantics.Basic

/-!
  No NaN from `strtod`'s rounding, and `(int)x` defined after the range tests
  of cJSON's `parse_number`.

  `Float.ofBits` canonicalizes only NaN patterns (`Float.Model.ofBits` is
  `pack ∘ unpack`), and the bits that `ratToFloat` builds from `roundBin` are
  never a NaN pattern: `roundBin 53 (-1074) 971` gives a significand below
  `2^53` and an exponent in `[-1074, 971]`. After `x >= (double)INT_MAX` and
  `x <= (double)INT_MIN` both fail, a finite `x` truncates into `int`.
-/

namespace CIR.Std

open Float.Model Float.Model.UnpackedFloat

/-! ### NaN bit patterns -/

theorem decodeBits_eq_nan_iff (n : Nat) :
    decodeBits n = .nan ↔ (n / 2 ^ 52 % 2048 = 2047 ∧ n % 2 ^ 52 ≠ 0) := by
  simp only [decodeBits]
  split
  · split <;> simp_all
  · split <;> simp_all

theorem unpackExponent_toNat (b : BitVec Format.binary64.numBits) :
    (unpackExponent (spec := Format.binary64) b).toNat = b.toNat / 2 ^ 52 % 2048 := by
  simp [unpackExponent, Nat.shiftRight_eq_div_pow]

theorem unpackMantissa_toNat (b : BitVec Format.binary64.numBits) :
    (unpackMantissa (spec := Format.binary64) b).toNat = b.toNat % 2 ^ 52 := by
  simp [unpackMantissa]

/-- The NaN patterns, in the terms of the model. -/
theorem decodeBits_eq_nan_iff_bv (b : BitVec Format.binary64.numBits) :
    decodeBits b.toNat = .nan ↔
      (unpackExponent (spec := Format.binary64) b = -1#_ ∧
        unpackMantissa (spec := Format.binary64) b ≠ 0#_) := by
  have h1 : unpackExponent (spec := Format.binary64) b = -1#_ ↔
      (unpackExponent (spec := Format.binary64) b).toNat = 2047 := by
    rw [← BitVec.toNat_inj]
    have : (-1#Format.binary64.exponentBits).toNat = 2047 := by decide
    rw [this]
  have h2 : unpackMantissa (spec := Format.binary64) b = 0#_ ↔
      (unpackMantissa (spec := Format.binary64) b).toNat = 0 := by
    rw [← BitVec.toNat_inj]
    have : (0#Format.binary64.mantissaBitsWithoutImplicit).toNat = 0 := by decide
    rw [this]
  rw [decodeBits_eq_nan_iff, ← unpackExponent_toNat, ← unpackMantissa_toNat, h1, Ne, Ne, h2]

theorem unpack_eq_nan {b : BitVec Format.binary64.numBits}
    (h : UnpackedFloat.unpack Format.binary64 b = .notANumber) :
    unpackExponent (spec := Format.binary64) b = -1#_ ∧
      unpackMantissa (spec := Format.binary64) b ≠ 0#_ := by
  simp only [UnpackedFloat.unpack] at h
  split at h
  · split at h
    · cases h
    · exact ⟨‹_›, ‹_›⟩
  · split at h
    · split at h <;> cases h
    · cases h

theorem pack_not_nan {f : UnpackedFloat} (hf : f ≠ .notANumber) :
    ¬ (unpackExponent (spec := Format.binary64) (UnpackedFloat.pack Format.binary64 f) = -1#_ ∧
       unpackMantissa (spec := Format.binary64) (UnpackedFloat.pack Format.binary64 f) ≠ 0#_) := by
  revert hf
  fun_cases UnpackedFloat.pack with
  | case1 => intro h; exact absurd rfl h
  | case2 s => intro _; simp [packedInfinity]
  | case3 s => intro _; simp [packedZero]
  | case4 s m e hm biasedExponent h => intro _; simp [packedInfinity]
  | case5 s m e hm actualMantissaBits biasedExponent h₁ h₂ =>
    intro _
    rw [unpackExponent_packComponents]
    intro ⟨h, _⟩
    have := congrArg BitVec.toNat h
    have e1 : Format.binary64.exponentBits = 11 := rfl
    rw [e1] at h₁
    simp at this
    omega
  | case6 s m e hm actualMantissaBits biasedExponent h₁ h₂ =>
    intro _; simp

theorem decodeF_ofBits_ne_nan (u : UInt64) (h : decodeBits u.toNat ≠ .nan) :
    decodeF (Float.ofBits u) ≠ .nan := by
  have hu : UnpackedFloat.unpack Format.binary64 u.toBitVec ≠ .notANumber := by
    intro hn
    exact h ((decodeBits_eq_nan_iff_bv u.toBitVec).2 (unpack_eq_nan hn))
  show decodeBits (UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (UnpackedFloat.unpack Format.binary64 u.toBitVec))).toNat ≠ .nan
  rw [UInt64.toNat_ofBitVec]
  intro hn
  exact pack_not_nan hu ((decodeBits_eq_nan_iff_bv _).1 hn)

/-! ### Bounds of `roundBin` -/

/-- `num / den < 2 ^ t` (as `num * 2^(-t) < den * 2^t`), scaled by `2 ^ k`. -/
theorem ltPow2_scale {num den : Nat} {t : Int} (k : Nat) (hk : 0 ≤ t + k) :
    num * 2 ^ (-t).toNat < den * 2 ^ t.toNat ↔ num * 2 ^ k < den * 2 ^ (t + k).toNat := by
  rcases Int.le_total 0 t with ht | ht
  · have h1 : (-t).toNat = 0 := by omega
    have h2 : (t + k).toNat = t.toNat + k := by omega
    rw [h1, h2, Nat.pow_add, Nat.pow_zero, Nat.mul_one, ← Nat.mul_assoc]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos k)).symm
  · have h1 : t.toNat = 0 := by omega
    obtain ⟨j, hj⟩ : ∃ j, (t + k).toNat = j := ⟨_, rfl⟩
    have h2 : k = (-t).toNat + j := by omega
    rw [h1, hj, h2, Nat.pow_zero, Nat.mul_one, Nat.pow_add, ← Nat.mul_assoc]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos j)).symm

theorem ltPow2_mono {num den : Nat} {t t' : Int} (htt : t ≤ t')
    (h : num * 2 ^ (-t).toNat < den * 2 ^ t.toNat) :
    num * 2 ^ (-t').toNat < den * 2 ^ t'.toNat := by
  rw [ltPow2_scale (-t).toNat (by omega)] at h
  rw [ltPow2_scale (-t).toNat (by omega)]
  exact Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))

/-- `num / den < 2 ^ (log2Q num den + 1)`. -/
theorem log2Q_upper {num den : Nat} (hd : den ≠ 0) :
    num * 2 ^ (-(log2Q num den + 1)).toNat < den * 2 ^ (log2Q num den + 1).toNat := by
  have hA : num * 2 ^ Nat.log2 den < den * 2 ^ (Nat.log2 num + 1) :=
    calc num * 2 ^ Nat.log2 den < 2 ^ (Nat.log2 num + 1) * 2 ^ Nat.log2 den :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 Nat.lt_log2_self
      _ ≤ 2 ^ (Nat.log2 num + 1) * den := Nat.mul_le_mul_left _ (Nat.log2_self_le hd)
      _ = den * 2 ^ (Nat.log2 num + 1) := Nat.mul_comm _ _
  simp only [log2Q]
  generalize hl : (Nat.log2 num : Int) - Nat.log2 den = l
  by_cases h0 : 0 ≤ l
  · rw [ite_eq_left h0]
    by_cases hc : den * 2 ^ l.toNat ≤ num
    · rw [ite_eq_left (decide_eq_true hc)]
      rw [ltPow2_scale (Nat.log2 den) (by omega)]
      have : (l + 1 + (Nat.log2 den : Int)).toNat = Nat.log2 num + 1 := by omega
      rw [this]
      exact hA
    · rw [ite_eq_right (fun h => hc (of_decide_eq_true h))]
      have h3 : l - 1 + 1 = l := by omega
      have h4 : (-l).toNat = 0 := by omega
      rw [h3, h4, Nat.pow_zero, Nat.mul_one]
      omega
  · rw [ite_eq_right h0]
    by_cases hc : den ≤ num * 2 ^ (-l).toNat
    · rw [ite_eq_left (decide_eq_true hc)]
      rw [ltPow2_scale (Nat.log2 den) (by omega)]
      have : (l + 1 + (Nat.log2 den : Int)).toNat = Nat.log2 num + 1 := by omega
      rw [this]
      exact hA
    · rw [ite_eq_right (fun h => hc (of_decide_eq_true h))]
      have h3 : l - 1 + 1 = l := by omega
      have h4 : l.toNat = 0 := by omega
      rw [h3, h4, Nat.pow_zero, Nat.mul_one]
      omega

theorem roundHalfEven_le {num den N : Nat} (h : num < den * N) : roundHalfEven num den ≤ N := by
  have hq : num / den < N := Nat.div_lt_of_lt_mul h
  have h2 : num / den % 2 < 2 := Nat.mod_lt _ (by decide)
  simp only [roundHalfEven]
  split
  · omega
  · split <;> omega

theorem roundHalfEven_zero (num : Nat) : roundHalfEven num 0 ≤ 1 := by
  simp only [roundHalfEven, Nat.div_zero, Nat.mod_zero]
  split
  · omega
  · split <;> omega

theorem roundScaled_le {num den p : Nat} {e : Int}
    (h : num * 2 ^ (-(e + p)).toNat < den * 2 ^ (e + p).toNat) : roundScaled num den e ≤ 2 ^ p := by
  simp only [roundScaled]
  split
  · rename_i he
    apply roundHalfEven_le
    have h1 : (-(e + p)).toNat = 0 := by omega
    have h2 : (e + p).toNat = e.toNat + p := by omega
    rw [h1, h2, Nat.pow_zero, Nat.mul_one, Nat.pow_add, ← Nat.mul_assoc] at h
    exact h
  · rename_i he
    apply roundHalfEven_le
    rw [ltPow2_scale (-e).toNat (by omega)] at h
    have h1 : (e + p + ((-e).toNat : Int)).toNat = p := by omega
    rw [h1] at h
    exact h

theorem roundScaled_le_pow {p : Nat} (hp : 1 ≤ p) (emin : Int) (num den : Nat) :
    roundScaled num den (max (log2Q num den - ((p - 1 : Nat) : Int)) emin) ≤ 2 ^ p := by
  by_cases hd : den = 0
  · subst hd
    simp only [roundScaled]
    split
    · rw [Nat.zero_mul]; exact Nat.le_trans (roundHalfEven_zero _) (Nat.one_le_two_pow)
    · exact Nat.le_trans (roundHalfEven_zero _) (Nat.one_le_two_pow)
  · apply roundScaled_le
    apply ltPow2_mono _ (log2Q_upper hd)
    omega

/-- `roundBin` stays within the format: `m < 2^p` and `emin ≤ e ≤ emax`. -/
theorem roundBin_bound {p : Nat} (hp : 1 ≤ p) {emin emax : Int} (hee : emin ≤ emax)
    {num den m : Nat} {e : Int}
    (h : roundBin p emin emax num den = some (m, e)) : m < 2 ^ p ∧ emin ≤ e ∧ e ≤ emax := by
  have hb := roundScaled_le_pow hp emin num den
  unfold roundBin at h
  by_cases h0 : num = 0
  · rw [ite_eq_left h0] at h
    cases h
    exact ⟨Nat.two_pow_pos p, Int.le_refl _, hee⟩
  · rw [ite_eq_right h0] at h
    dsimp only at h
    generalize hr : roundScaled num den (max (log2Q num den - ((p - 1 : Nat) : Int)) emin) = r at h hb
    generalize hx : max (log2Q num den - ((p - 1 : Nat) : Int)) emin = x at h hr
    have hx1 : emin ≤ x := by omega
    by_cases hr2 : r = 2 ^ p
    · rw [ite_eq_left hr2] at h
      dsimp only at h
      by_cases he : emax < x + 1
      · rw [ite_eq_left he] at h; cases h
      · rw [ite_eq_right he] at h
        cases h
        exact ⟨Nat.pow_lt_pow_right (by decide) (by omega), by omega, by omega⟩
    · rw [ite_eq_right hr2] at h
      dsimp only at h
      by_cases he : emax < x
      · rw [ite_eq_left he] at h; cases h
      · rw [ite_eq_right he] at h
        cases h
        exact ⟨by omega, by omega, by omega⟩

/-! ### The bits of a rounded value are not a NaN -/

theorem bitsOf_none_ok (neg : Bool) :
    bitsOf neg none < 2 ^ 64 ∧ decodeBits (bitsOf neg none) ≠ .nan := by
  cases neg <;> decide

theorem bitsOf_some_ok (neg : Bool) {m : Nat} {e : Int} (hm : m < 2 ^ 53) (he1 : -1074 ≤ e)
    (he2 : e ≤ 971) :
    bitsOf neg (some (m, e)) < 2 ^ 64 ∧ decodeBits (bitsOf neg (some (m, e))) ≠ .nan := by
  rw [Ne, decodeBits_eq_nan_iff]
  have h52 : (2 : Nat) ^ 52 = 4503599627370496 := by decide
  have h53 : (2 : Nat) ^ 53 = 9007199254740992 := by decide
  have h63 : (2 : Nat) ^ 63 = 9223372036854775808 := by decide
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  rw [h53] at hm
  cases neg <;> simp only [bitsOf, h52, h63, h64, Bool.false_eq_true, ↓reduceIte] <;> split <;> omega

theorem bitsOf_roundBin_ok (neg : Bool) (num den : Nat) :
    bitsOf neg (roundBin 53 (-1074) 971 num den) < 2 ^ 64 ∧
      decodeBits (bitsOf neg (roundBin 53 (-1074) 971 num den)) ≠ .nan := by
  cases h : roundBin 53 (-1074) 971 num den with
  | none => exact bitsOf_none_ok neg
  | some r =>
    obtain ⟨m, e⟩ := r
    obtain ⟨hm, he1, he2⟩ := roundBin_bound (by decide) (by decide) h
    exact bitsOf_some_ok neg hm he1 he2

theorem decodeF_ratToFloat_ne_nan (neg : Bool) (num den : Nat) :
    decodeF (ratToFloat neg num den) ≠ .nan := by
  obtain ⟨hlt, hne⟩ := bitsOf_roundBin_ok neg num den
  apply decodeF_ofBits_ne_nan
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  exact hne

theorem decodeF_valToFloat_ne_nan (neg : Bool) (m : Nat) (e : Int) :
    decodeF (valToFloat neg m e) ≠ .nan :=
  decodeF_ratToFloat_ne_nan neg _ _

theorem decodeF_infF_ne_nan (neg : Bool) : decodeF (infF neg) ≠ .nan := by
  apply decodeF_ofBits_ne_nan
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (bitsOf_none_ok neg).1]
  exact (bitsOf_none_ok neg).2

/-! ### Conversion to `int` after the range tests -/

theorem decodeBits_finite_exp {n : Nat} {neg : Bool} {m : Nat} {e : Int}
    (h : decodeBits n = .finite neg m e) : -1074 ≤ e := by
  simp only [decodeBits] at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h; omega
    · cases h; omega

theorem fkey_finite (neg : Bool) (m : Nat) (e : Int) :
    fkey (.finite neg m e) =
      some (if neg then -((m * 2 ^ (e + 1074).toNat : Nat) : Int)
        else ((m * 2 ^ (e + 1074).toNat : Nat) : Int)) := by
  cases neg <;> simp [fkey]

-- the keys are multiples of `2^1074`: let the elaborator evaluate such powers
set_option exponentiation.threshold 1200 in
/-- `(double)INT_MAX = 2147483647`. -/
theorem fkey_intMax :
    fkey (decodeF (Float.ofInt 2147483647)) = some ((2147483647 * 2 ^ 1074 : Nat) : Int) := by
  have c : decodeF (Float.ofInt 2147483647) = .finite false (2147483647 * 2 ^ 22) (-22) := by decide
  rw [c, fkey_finite]
  decide

set_option exponentiation.threshold 1200 in
/-- `(double)INT_MIN = -2147483648`. -/
theorem fkey_intMin :
    fkey (decodeF (Float.ofInt (-2147483648))) = some (-((2147483648 * 2 ^ 1074 : Nat) : Int)) := by
  have c : decodeF (Float.ofInt (-2147483648)) = .finite true (2 ^ 52) (-21) := by decide
  rw [c, fkey_finite]
  decide

theorem cmpFloat_ge_false {x y : Float} {a b : Int} (hx : fkey (decodeF x) = some a)
    (hy : fkey (decodeF y) = some b) (h : CIR.cmpFloat .ge x y = false) : a < b := by
  simp only [CIR.cmpFloat, hx, hy] at h
  exact Int.lt_of_not_ge (of_decide_eq_false h)

theorem cmpFloat_le_false {x y : Float} {a b : Int} (hx : fkey (decodeF x) = some a)
    (hy : fkey (decodeF y) = some b) (h : CIR.cmpFloat .le x y = false) : b < a := by
  simp only [CIR.cmpFloat, hx, hy] at h
  exact Int.lt_of_not_ge (of_decide_eq_false h)

/-- The integer part of `m · 2^e` from a bound on its key `m · 2^(e + 1074)`. -/
theorem truncNat_lt {m : Nat} {e : Int} {C : Nat} (he : -1074 ≤ e)
    (h : m * 2 ^ (e + 1074).toNat < C * 2 ^ 1074) :
    (if 0 ≤ e then m * 2 ^ e.toNat else m / 2 ^ (-e).toNat) < C := by
  split
  · rename_i h0
    have h1 : (e + 1074).toNat = e.toNat + 1074 := by omega
    rw [h1, Nat.pow_add, ← Nat.mul_assoc] at h
    exact Nat.lt_of_mul_lt_mul_right h
  · rename_i h0
    obtain ⟨j, hj⟩ : ∃ j, (e + 1074).toNat = j := ⟨_, rfl⟩
    have h1 : 1074 = (-e).toNat + j := by omega
    rw [hj, h1, Nat.pow_add, ← Nat.mul_assoc] at h
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact Nat.lt_of_mul_lt_mul_right h)

theorem inRange_i32_iff (x : Int) :
    CIR.inRange true 32 x = true ↔ -2147483648 ≤ x ∧ x ≤ 2147483647 := by
  simp [CIR.inRange, CIR.intMin, CIR.intMax]

theorem truncVal_inRange_i32 {f : Float} {neg : Bool} {m : Nat} {e : Int}
    (hf : decodeF f = .finite neg m e)
    (hge : CIR.cmpFloat .ge f (Float.ofInt 2147483647) = false)
    (hle : CIR.cmpFloat .le f (Float.ofInt (-2147483648)) = false) :
    CIR.inRange true 32 (truncVal neg m e) = true := by
  have he : -1074 ≤ e := decodeBits_finite_exp hf
  have h1 := cmpFloat_ge_false (by rw [hf, fkey_finite]) fkey_intMax hge
  have h2 := cmpFloat_le_false (by rw [hf, fkey_finite]) fkey_intMin hle
  rw [inRange_i32_iff]
  simp only [truncVal]
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    have := truncNat_lt (C := 2147483647) he (Int.ofNat_lt.1 h1)
    omega
  · simp only [↓reduceIte] at h2 ⊢
    have := truncNat_lt (C := 2147483648) he (Int.ofNat_lt.1 (Int.neg_lt_neg_iff.1 h2))
    omega

set_option exponentiation.threshold 2200 in
/-- The two tests exclude the infinities: a value that is not a NaN is finite. -/
theorem decodeF_finite_of_cmp {f : Float} (hn : decodeF f ≠ .nan)
    (hge : CIR.cmpFloat .ge f (Float.ofInt 2147483647) = false)
    (hle : CIR.cmpFloat .le f (Float.ofInt (-2147483648)) = false) :
    ∃ neg m e, decodeF f = .finite neg m e := by
  cases h : decodeF f with
  | finite neg m e => exact ⟨neg, m, e, rfl⟩
  | inf neg =>
    cases neg
    · have := cmpFloat_ge_false (by rw [h]; rfl) fkey_intMax hge
      simp at this
    · have := cmpFloat_le_false (by rw [h]; rfl) fkey_intMin hle
      simp at this
  | nan => exact absurd h hn

/-- `(int)x` (`floatToInt` to a signed 32-bit integer) is defined after the
two tests, for `x` not a NaN. -/
theorem floatToInt_i32_ok {f : Float} (hn : decodeF f ≠ .nan)
    (hge : CIR.cmpFloat .ge f (Float.ofInt 2147483647) = false)
    (hle : CIR.cmpFloat .le f (Float.ofInt (-2147483648)) = false) :
    ∃ neg m e, decodeF f = .finite neg m e ∧ CIR.inRange true 32 (truncVal neg m e) = true := by
  obtain ⟨neg, m, e, h⟩ := decodeF_finite_of_cmp hn hge hle
  exact ⟨neg, m, e, h, truncVal_inRange_i32 h hge hle⟩

end CIR.Std

#print axioms CIR.Std.decodeF_ofBits_ne_nan
#print axioms CIR.Std.decodeF_ratToFloat_ne_nan
#print axioms CIR.Std.decodeF_valToFloat_ne_nan
#print axioms CIR.Std.decodeF_infF_ne_nan
#print axioms CIR.Std.truncVal_inRange_i32
#print axioms CIR.Std.decodeF_finite_of_cmp
#print axioms CIR.Std.floatToInt_i32_ok

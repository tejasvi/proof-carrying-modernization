/-
StrictTS proof layer: number facts used by loops over indices.

`for (let i = 0; i < a.length; i++)` keeps `i` a double; these lemmas turn index arithmetic,
comparisons (`<`, `<=`, `===`), `Math.floor(a / b)`, `%` and element access with such a counter
into `Nat` arithmetic, so that loop proofs run on natural numbers (`omega`), and so do tests on
lengths (`xs.length === 0` is `xs.size = 0`).
-/
import StrictTS.Proof.Exec
import StrictTS.Num.F64Lemmas

namespace StrictTS
open F64

set_option warning.simp.varHead false in
/-- Numeric literals of type `F64` are `F64.ofNat`. -/
@[simp] theorem F64.lit_eq_ofNat (n : Nat) : (no_index (OfNat.ofNat n) : F64) = F64.ofNat n := rfl

/-- Safe integers are finite and denote themselves under ToIntegerOrInfinity. -/
@[simp] theorem Conv.toIntegerOrInf_ofInt {n : Int} (h : Safe n) : Conv.toIntegerOrInf (ofInt n) = .fin n := by
  obtain ⟨x, h1, -⟩ := ofInt_fin n h
  rw [h1]
  simp only [Conv.toIntegerOrInf]
  rw [← h1, truncInt_ofInt h]

@[simp] theorem Conv.toIntegerOrInf_ofNat {n : Nat} (h : n ≤ 2 ^ 53) :
    Conv.toIntegerOrInf (ofNat n) = .fin n := by
  rw [ofNat_eq_ofInt]
  exact Conv.toIntegerOrInf_ofInt (by simp only [Safe]; omega)

/-- Natural numbers below `2^32 - 1` are array indices. -/
@[simp] theorem Conv.arrayIndex?_ofNat {n : Nat} (h : n < 2 ^ 32 - 1) : Conv.arrayIndex? (ofNat n) = some n := by
  simp only [Conv.arrayIndex?, Conv.toInt?, ofNat_eq_ofInt]
  rw [toInt?_ofInt (by simp only [Safe]; omega)]
  simp
  omega

/-- Integers in `[0, 2^32 - 1)` are array indices (a counter running down to `0`). -/
theorem Conv.arrayIndex?_ofInt {z : Int} (h0 : 0 ≤ z) (h : z < 2 ^ 32 - 1) :
    Conv.arrayIndex? (ofInt z) = some z.toNat := by
  simp only [Conv.arrayIndex?, Conv.toInt?]
  rw [toInt?_ofInt (by simp only [Safe]; omega)]
  simp
  omega

/-- A safe natural is an integer (`Number.isInteger(i)`, the test of a string index `s[i]`). -/
theorem isInteger_ofNat_safe {n : Nat} (h : n ≤ 2 ^ 53) : (ofNat n).isInteger = true := by
  simp only [F64.isInteger, ofNat_eq_ofInt]
  rw [toInt?_ofInt (by simp only [Safe]; omega)]
  rfl

/-- `i + 1` on a safe natural-number counter. -/
@[simp] theorem ofNat_add_one {n : Nat} (h : n + 1 ≤ 2 ^ 53) : ofNat n + ofNat 1 = ofNat (n + 1) := by
  simp only [ofNat_eq_ofInt]
  rw [add_ofInt (by simp only [Safe]; omega) (by simp only [Safe]; omega) (by simp only [Safe]; omega)]
  simp

/-- `a - b` on safe natural numbers as an integer (the bound `xs.length - 1` is `-1` for an empty
array). -/
theorem ofNat_sub_ofNat_int {a b : Nat} (ha : a ≤ 2 ^ 53) (hb : b ≤ 2 ^ 53) :
    ofNat a - ofNat b = ofInt ((a : Int) - b) := by
  simp only [ofNat_eq_ofInt]
  rw [sub_ofInt (by simp only [Safe]; omega) (by simp only [Safe]; omega) (by simp only [Safe]; omega)]

/-- Comparisons of a safe natural with a safe integer (`i < xs.length - 1`). -/
theorem lt_ofNat_ofInt {a : Nat} {z : Int} (ha : a ≤ 2 ^ 53) (hz1 : -2 ^ 53 ≤ z) (hz2 : z ≤ 2 ^ 53) :
    (ofNat a).lt (ofInt z) = decide ((a : Int) < z) := by
  simp only [ofNat_eq_ofInt]
  exact lt_ofInt (by simp only [Safe]; omega) (by simp only [Safe]; omega)

theorem le_ofNat_ofInt {a : Nat} {z : Int} (ha : a ≤ 2 ^ 53) (hz1 : -2 ^ 53 ≤ z) (hz2 : z ≤ 2 ^ 53) :
    (ofNat a).le (ofInt z) = decide ((a : Int) ≤ z) := by
  simp only [ofNat_eq_ofInt]
  exact le_ofInt (by simp only [Safe]; omega) (by simp only [Safe]; omega)

/-- `a + b` on safe natural numbers (a counter's step `j += i`). -/
theorem ofNat_add_ofNat {a b : Nat} (h : a + b ≤ 2 ^ 53) : ofNat a + ofNat b = ofNat (a + b) := by
  simp only [ofNat_eq_ofInt]
  rw [add_ofInt (by simp only [Safe]; omega) (by simp only [Safe]; omega) (by simp only [Safe]; omega)]
  simp

/-- The length of a substring (`str.slice(a, b)`, `str.substring(a, b)` once clamped). -/
theorem JSStr.length_sub (s : JSStr) (a b : Nat) : (s.sub a b).length = min (b - a) (s.length - a) := by
  simp [JSStr.sub, JSStr.length, List.length_take, List.length_drop]

/-- The length of `s.slice(a, b)`, through the clamped indices (`JSStr.relIndex`, which `simp`
evaluates for literal and natural indices). -/
theorem JSStr.length_slice (s : JSStr) (a b : Int) :
    (s.slice a b).length =
      min (JSStr.relIndex s.length b - JSStr.relIndex s.length a) (s.length - JSStr.relIndex s.length a) := by
  simp only [JSStr.slice, JSStr.length_sub]

/-- A natural index of `slice` clamped to the length. -/
theorem JSStr.relIndex_natCast' (len a : Nat) : JSStr.relIndex len (a : Int) = min a len := by
  unfold JSStr.relIndex
  rw [if_neg (by omega)]
  simp

theorem JSStr.relIndex_ofNat_lit (len n : Nat) :
    JSStr.relIndex len (no_index (OfNat.ofNat n : Int)) = min n len :=
  JSStr.relIndex_natCast' len n

/-- `s[k]` (`s.at(k)`) at a natural number below the length: the code unit there. -/
theorem JSStr.at?_natCast {s : JSStr} {k : Nat} (h : k < s.length) :
    s.at? (k : Int) = some ⟨[s.units[k]'h]⟩ := by
  have h' : k < s.units.length := h
  simp [JSStr.at?, List.getElem?_eq_getElem h']
  rfl

/-- `s[k]` at a numeral below the length. -/
theorem JSStr.at?_ofNat_lit {s : JSStr} {k : Nat} (h : k < s.length) :
    s.at? (no_index (OfNat.ofNat k : Int)) = some ⟨[s.units[k]'h]⟩ :=
  JSStr.at?_natCast h

/-- `n - k` on safe natural numbers with `k ≤ n` (the last index `xs.length - 1` of a non-empty
array). -/
@[simp] theorem ofNat_sub_ofNat {a b : Nat} (ha : a ≤ 2 ^ 53) (hba : b ≤ a) :
    ofNat a - ofNat b = ofNat (a - b) := by
  simp only [ofNat_eq_ofInt]
  rw [sub_ofInt (by simp only [Safe]; omega) (by simp only [Safe]; omega) (by simp only [Safe]; omega)]
  congr 1
  omega

/-- `i < n` on safe natural numbers. -/
@[simp] theorem lt_ofNat {a b : Nat} (ha : a ≤ 2 ^ 53) (hb : b ≤ 2 ^ 53) :
    (ofNat a).lt (ofNat b) = decide (a < b) := by
  simp only [ofNat_eq_ofInt]
  rw [lt_ofInt (by simp only [Safe]; omega) (by simp only [Safe]; omega)]
  simp

/-- `i <= n` on safe natural numbers. -/
@[simp] theorem le_ofNat {a b : Nat} (ha : a ≤ 2 ^ 53) (hb : b ≤ 2 ^ 53) :
    (ofNat a).le (ofNat b) = decide (a ≤ b) := by
  simp only [ofNat_eq_ofInt]
  rw [le_ofInt (by simp only [Safe]; omega) (by simp only [Safe]; omega)]
  simp

/-- `===` on safe integers is integer equality. -/
@[simp] theorem numEq_ofInt {a b : Int} (ha : Safe a) (hb : Safe b) :
    Conv.numEq (ofInt a) (ofInt b) = decide (a = b) := by
  obtain ⟨x, hx1, -, hx3⟩ := ofInt_spec a ha
  obtain ⟨y, hy1, -, hy3⟩ := ofInt_spec b hb
  by_cases hab : a = b
  · subst hab
    rw [hx1] at hy1
    cases hy1
    rw [hx1]
    simp [Conv.numEq]
  · have hxy : x ≠ y := by
      intro e
      subst e
      exact hab (ofInt_inj ha hb (hx1.trans hy1.symm))
    -- two zeros are both `0`
    have hz : ¬ (x.man = 0 ∧ y.man = 0) := by
      rintro ⟨h1, h2⟩
      rw [← Fin64.mag_eq_zero_iff] at h1 h2
      rw [h1] at hx3
      rw [h2] at hy3
      have hp := Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos 1074)
      have h1' : a.natAbs = 0 := (Nat.mul_eq_zero.1 hx3.symm).resolve_right hp
      have h2' : b.natAbs = 0 := (Nat.mul_eq_zero.1 hy3.symm).resolve_right hp
      omega
    rw [hx1, hy1]
    simp only [Conv.numEq, hab, decide_false]
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨by omega, hxy⟩

/-- `===` on safe natural numbers is equality (the validation test `xs.length === 0` is
`xs.size = 0`). -/
@[simp] theorem numEq_ofNat {a b : Nat} (ha : a ≤ 2 ^ 53) (hb : b ≤ 2 ^ 53) :
    Conv.numEq (ofNat a) (ofNat b) = decide (a = b) := by
  simp only [ofNat_eq_ofInt]
  rw [numEq_ofInt (by simp only [Safe]; omega) (by simp only [Safe]; omega)]
  simp only [Int.ofNat_inj]

/-- `Math.floor(a / b)` on safe natural numbers is natural-number division (the middle index
`Math.floor(n / 2)`). -/
theorem floor_div_ofNat {a b : Nat} (ha : a ≤ 2 ^ 53) (hb : b ≤ 2 ^ 53) (hb0 : b ≠ 0) :
    (ofNat a / ofNat b).floor = ofNat (a / b) := by
  simp only [ofNat_eq_ofInt]
  rw [floor_div_ofInt (by simp only [Safe]; omega) (by simp only [Safe]; omega) (by omega) (by omega),
    Int.fdiv_eq_ediv_of_nonneg _ (by omega)]
  rfl

set_option exponentiation.threshold 1100 in
/-- `a % b` on safe natural numbers (JS `%` is exact). -/
theorem rem_ofNat {a b : Nat} (ha : a ≤ 2 ^ 53) (hb : b ≤ 2 ^ 53) (hb0 : b ≠ 0) :
    ofNat a % ofNat b = ofNat (a % b) := by
  simp only [ofNat_eq_ofInt]
  obtain ⟨x, hx1, hx2, hx3⟩ := ofInt_spec a (by simp only [Safe]; omega)
  obtain ⟨y, hy1, hy2, hy3⟩ := ofInt_spec b (by simp only [Safe]; omega)
  have hxm := ofInt_man_eq_zero hx3
  have hym := ofInt_man_eq_zero hy3
  rw [hx1, hy1]
  show rem (.fin x) (.fin y) = _
  by_cases a0 : a = 0
  · subst a0
    simp only [rem, (not_congr hym).2 (by omega : (b : Int) ≠ 0), hxm.2 rfl, ite_true, ite_false,
      Nat.zero_mod]
    rw [← hx1]
  · simp only [rem, (not_congr hym).2 (by omega : (b : Int) ≠ 0), (not_congr hxm).2 (by omega : (a : Int) ≠ 0),
      ite_false]
    have hneg : x.neg = false := by rw [hx2]; simp
    have hE := Fin64.minExp_ge x y
    have hA := Fin64.ints_fst_mul x y
    have hB := Fin64.ints_snd_mul x y
    rw [Fin64.sval_eq x a hx2 hx3] at hA
    rw [Fin64.sval_eq y b hy2 hy3] at hB
    have hm : x.minExp y = -1074 + ((x.minExp y + 1074).toNat : Int) := by omega
    generalize (x.minExp y + 1074).toNat = E at hA hB hm
    -- the aligned significands are `a`, `b` scaled alike, and so is their remainder
    have hA' : (x.ints y).1.natAbs * 2 ^ E = a * 2 ^ 1074 := by
      have := congrArg Int.natAbs hA
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at this
      exact this
    have hB' : (x.ints y).2.natAbs * 2 ^ E = b * 2 ^ 1074 := by
      have := congrArg Int.natAbs hB
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at this
      exact this
    have hR : ((x.ints y).1.natAbs % (x.ints y).2.natAbs) * 2 ^ E = (a % b) * 2 ^ 1074 := by
      rw [← Nat.mul_mod_mul_right, hA', hB', Nat.mul_mod_mul_right]
    rw [hneg, hm, ← round_scale, hR, round_scale, ofInt_natCast]
    congr 1

/-- The start index of `slice()`. -/
@[simp] theorem Conv.relIndex_fin_zero (len : Nat) : Conv.relIndex (.fin 0) len = 0 := by
  simp [Conv.relIndex]

/-- `Number.isNaN(x)` holds exactly for NaN. -/
theorem isNaN_eq_true_iff (x : F64) : x.isNaN = true ↔ x = .nan := by
  cases x <;> simp [F64.isNaN]

/-- `uint32` values convert to `ToInt32` bits. -/
@[simp] theorem toInt32_ofNat_u16 {n : Nat} (h : n < 2 ^ 16) : (ofNat n).toInt32 = BitVec.ofNat 32 n := by
  simp only [ofNat_eq_ofInt]
  rw [toInt32_ofInt (by simp only [Safe]; omega)]
  simp

end StrictTS

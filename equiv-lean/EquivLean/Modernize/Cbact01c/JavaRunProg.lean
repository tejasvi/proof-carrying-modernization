import EquivLean.Modernize.Cbact01c.JavaSpec
import EquivLean.Bridge.Jimple.SpecDigits

/-!
# CBACT01C → Java: the texts the helpers build

`argText` (a string argument's characters, `""` for `null`), `fixStr s n` (`pad(s, n)`: the
first `n` characters, padded with spaces; `spaces(n)` is `fixStr [] n`), `zonedJ` (`zoned(v, n,
signed)`: the DISPLAY text of `v` in `n` digits, the last one overpunched with the sign when
`signed`), each defined in the order the Java loop builds it.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

def space : JChar := BitVec.ofNat 16 32

/-- The text of a string argument: its characters, `""` for `null` (and for a non-string). -/
def argText (σ : Jimple.State) (v : Value) : JStr := (strOf σ v).getD []

/-- A string argument: `null`, or a string (of `int` length, as every Java string). -/
def StrOk (σ : Jimple.State) (v : Value) : Prop :=
  v = .null ∨ ∃ x s, v = .ref x ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

/-- `fixStr s n`: the first `n` characters of `s`, padded with spaces to `n` (`pad`). -/
def fixStr (s : JStr) : Nat → JStr
  | 0 => []
  | i + 1 => fixStr s i ++ [s.getD i space]

/-- The digit `d` as a character. -/
def digitJ (d : Nat) : JChar := BitVec.ofNat 16 (48 + d)

/-- Character `j` (from the left) of `zoned(a, n, signed)` for `a = |v|`, `neg = v < 0`. -/
def zch (a n : Nat) (signed neg : Bool) (j : Nat) : JChar :=
  if signed ∧ j + 1 = n then BitVec.ofNat 16 (overpunch neg (a % 10))
  else digitJ (a / 10 ^ (n - 1 - j) % 10)

/-- The first `i` characters of `zoned(a, n, signed)`. -/
def zonedPre (a n : Nat) (signed neg : Bool) : Nat → JStr
  | 0 => []
  | i + 1 => zonedPre a n signed neg i ++ [zch a n signed neg i]

/-- `zoned(v, n, signed)`. -/
def zonedJ (v : Int) (n : Nat) (signed : Bool) : JStr :=
  zonedPre v.natAbs n signed (decide (v < 0)) n

/-! ## Machine arithmetic of the digit loops (non-negative `long`s) -/

theorem msb_false_of_toInt_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) : l.msb = false := by
  have := BitVec.toInt_eq_toNat_cond l
  have hl := l.isLt
  rw [BitVec.msb_eq_decide]
  simp only [decide_eq_false_iff_not, Nat.not_le]
  by_cases hc : 2 * l.toNat < 2 ^ 64
  · omega
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' hc)] at this
    · omega

theorem toInt_nonneg_of_toNat_lt (l : BitVec 64) (h : l.toNat < 2 ^ 63) : 0 ≤ l.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

theorem sdiv_toNat_of_nonneg (a b : BitVec 64) (ha : 0 ≤ a.toInt) (hb : 0 ≤ b.toInt) :
    (a.sdiv b).toNat = a.toNat / b.toNat := by
  rw [BitVec.sdiv_eq, msb_false_of_toInt_nonneg a ha, msb_false_of_toInt_nonneg b hb]
  simp [BitVec.toNat_udiv]

theorem sdiv_nonneg (a b : BitVec 64) (ha : 0 ≤ a.toInt) (hb : 0 ≤ b.toInt) :
    0 ≤ (a.sdiv b).toInt := by
  apply toInt_nonneg_of_toNat_lt
  rw [sdiv_toNat_of_nonneg a b ha hb]
  have := BitVec.toInt_eq_toNat_cond a
  have hl := a.isLt
  have : a.toNat < 2 ^ 63 := by
    rw [BitVec.toInt_eq_toNat_cond] at ha; split at ha <;> omega
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this

theorem srem10_of_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) :
    l.srem 10#64 = BitVec.ofNat 64 (l.toNat % 10) := by
  have hmsb := msb_false_of_toInt_nonneg l h
  have h10 : (10#64).msb = false := by decide
  rw [BitVec.srem_eq, hmsb, h10]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : l.toNat % 10 < 2 ^ 64 := by omega
  simp [Nat.mod_eq_of_lt this]

/-- The digit `zoned` takes: `(int) ((a / d) % 10)`. -/
theorem toInt_digit (a d : BitVec 64) (ha : 0 ≤ a.toInt) (hd : 0 ≤ d.toInt) :
    JLong.toInt ((a.sdiv d).srem 10#64) = BitVec.ofNat 32 (a.toNat / d.toNat % 10) := by
  rw [srem10_of_nonneg _ (sdiv_nonneg a d ha hd), sdiv_toNat_of_nonneg a d ha hd]
  apply BitVec.eq_of_toNat_eq
  simp only [JLong.toInt, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem digit_eq_zero (x : Nat) : (BitVec.ofNat 32 (x % 10) = 0#32) = (x % 10 = 0) := by
  apply propext
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h; rw [h]

/-- The characters `zoned` appends: a digit, an overpunched digit (`'J' + d - 1`, `'A' + d - 1`). -/
theorem char48 (x : Nat) :
    (JInt.toChar (48#32 + BitVec.ofNat 32 (x % 10))).setWidth 16 = BitVec.ofNat 16 (48 + x % 10) := by
  apply BitVec.eq_of_toNat_eq
  simp only [JInt.toChar, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem char74 (x : Nat) :
    (JInt.toChar (74#32 + BitVec.ofNat 32 (x % 10) - 1#32)).setWidth 16 =
      BitVec.ofNat 16 (73 + x % 10) := by
  apply BitVec.eq_of_toNat_eq
  simp only [JInt.toChar, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub,
    BitVec.toNat_ofNat]
  omega

theorem char65 (x : Nat) :
    (JInt.toChar (65#32 + BitVec.ofNat 32 (x % 10) - 1#32)).setWidth 16 =
      BitVec.ofNat 16 (64 + x % 10) := by
  apply BitVec.eq_of_toNat_eq
  simp only [JInt.toChar, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub,
    BitVec.toNat_ofNat]
  omega

theorem sdiv10_toNat_of_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) :
    (l.sdiv 10#64).toNat = l.toNat / 10 :=
  sdiv_toNat_of_nonneg l 10#64 h (by decide)

theorem sdiv10_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) : 0 ≤ (l.sdiv 10#64).toInt :=
  sdiv_nonneg l 10#64 h (by decide)

theorem mul10_toNat (x : BitVec 64) (h : x.toNat < 10 ^ 18) : (x * 10#64).toNat = x.toNat * 10 := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  have : x.toNat * 10 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt (by decide : 10 < 2 ^ 64), Nat.mod_eq_of_lt this]

theorem pow10_pred_mul {k : Nat} (h : 1 ≤ k) : 10 ^ (k - 1) * 10 = 10 ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.pow_succ]

theorem pow10_div10 {m : Nat} (h : 1 ≤ m) : 10 ^ m / 10 = 10 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]; rfl

theorem pow10_lt18 {k : Nat} (h : k ≤ 17) : 10 ^ k < 10 ^ 18 :=
  Nat.pow_lt_pow_right (by decide) (by omega)

theorem toNat_lt_of_pow10 (x : BitVec 64) {k : Nat} (hx : x.toNat = 10 ^ k) (hk : k ≤ 18) :
    x.toNat < 2 ^ 63 := by
  have : 10 ^ k ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hk
  have h2 : (10 : Nat) ^ 18 < 2 ^ 63 := by decide
  omega

theorem toNat_of_toInt_nonneg (x : BitVec 64) (h : 0 ≤ x.toInt) : x.toNat = x.toInt.toNat := by
  have hc := BitVec.toInt_eq_toNat_cond x
  have hl := x.isLt
  simp only [Nat.reducePow] at hc hl
  split at hc <;> omega

theorem neg_toInt_of_bounds (v : BitVec 64) (hb : v.toInt.natAbs < 10 ^ 18) :
    (-v).toInt = -v.toInt := by
  rw [BitVec.toInt_neg]
  have := v.toInt_lt; have := v.le_toInt
  rw [Jimple.bmod64_of_bounds] <;> omega

/-- `|v|` as `zoned` computes it (`neg l0` when `v < 0`). -/
theorem abs_neg_toNat (v : BitVec 64) (h : v.toInt < 0) (hb : v.toInt.natAbs < 10 ^ 18) :
    (-v).toNat = v.toInt.natAbs := by
  have h1 := neg_toInt_of_bounds v hb
  rw [toNat_of_toInt_nonneg _ (by omega), h1]; omega

theorem abs_neg_nonneg (v : BitVec 64) (h : v.toInt < 0) (hb : v.toInt.natAbs < 10 ^ 18) :
    0 ≤ (-v).toInt := by
  rw [neg_toInt_of_bounds v hb]; omega

theorem abs_toNat (v : BitVec 64) (h : 0 ≤ v.toInt) : v.toNat = v.toInt.natAbs := by
  rw [toNat_of_toInt_nonneg _ h]; omega

/-- The sign flag of `zoned` (`$z2`). -/
def ngOf (v : I64) : I32 := if v.toInt < 0 then 1#32 else 0#32

end EquivLean.Modernize.Cbact01c.Java

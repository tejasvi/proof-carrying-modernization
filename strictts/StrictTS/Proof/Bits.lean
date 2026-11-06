import StrictTS.Proof.Numbers
import StrictTS.Proof.Attr

/-!
# Bitwise operators on arbitrary numbers

The interpreter's bitwise operators (`&`, `|`, `^`, `~`, `<<`, `>>`, `>>>`) convert their
operands with ToInt32. When the operand is a loop state (an arbitrary number, e.g. a hash or a
CRC register), lemmas about `F64.ofInt32 x` operands never fire inside the loop's step; the
lemmas below rewrite each operator on any operand into the 32-bit operation on `toInt32`, and
a literal right operand into its 32-bit value. They form the simp set `ts_bits`, which is
not part of `ts_sym` (it changes the normal form of every bitwise expression): pass it to
`ts_summarize [ts_bits]`, `ts_auto [ts_bits]` or `simp [ts_bits]` where a loop computes on bits.
-/

namespace StrictTS

namespace F64

/-- A literal operand, converted by ToInt32. -/
@[ts_bits] theorem toInt32_ofNat {n : Nat} (h : n ≤ 2 ^ 53) : (ofNat n).toInt32 = BitVec.ofNat 32 n := by
  rw [ofNat_eq_ofInt, toInt32_ofInt (by simp only [Safe]; omega)]
  simp

@[ts_bits] theorem band_eq (x y : F64) : x.band y = ofInt32 (x.toInt32 &&& y.toInt32) := rfl
@[ts_bits] theorem bor_eq (x y : F64) : x.bor y = ofInt32 (x.toInt32 ||| y.toInt32) := rfl
@[ts_bits] theorem bxor_eq (x y : F64) : x.bxor y = ofInt32 (x.toInt32 ^^^ y.toInt32) := rfl
@[ts_bits] theorem bnot_eq (x : F64) : x.bnot = ofInt32 (~~~x.toInt32) := rfl

/-- `x << n` for a literal shift count below 32. -/
@[ts_bits] theorem shl_ofNat (x : F64) {n : Nat} (h : n < 32) :
    x.shl (ofNat n) = ofInt32 (x.toInt32 <<< n) := by
  simp only [shl, toInt32_ofNat (n := n) (by omega), BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32), Nat.mod_eq_of_lt h]

/-- `x >> n` for a literal shift count below 32. -/
@[ts_bits] theorem sar_ofNat (x : F64) {n : Nat} (h : n < 32) :
    x.sar (ofNat n) = ofInt32 (x.toInt32.sshiftRight n) := by
  simp only [sar, toInt32_ofNat (n := n) (by omega), BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32), Nat.mod_eq_of_lt h]

/-- `x >>> n` for a literal shift count below 32. -/
@[ts_bits] theorem shr_ofNat (x : F64) {n : Nat} (h : n < 32) :
    x.shr (ofNat n) = ofUint32 (x.toInt32 >>> n) := by
  simp only [shr, toInt32_ofNat (n := n) (by omega), BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32), Nat.mod_eq_of_lt h]

set_option warning.simp.varHead false in
attribute [ts_bits] toInt32_ofInt32 toInt32_ofUint32 lit_eq_ofNat

end F64

attribute [ts_bits] BitVec.or_zero BitVec.zero_or BitVec.xor_zero BitVec.zero_xor BitVec.and_zero
  BitVec.zero_and

/-- An int32 below `2^31` used as an array index (e.g. a value masked with `& 0xFF`). -/
theorem Conv.arrayIndex?_ofInt32 {u : BitVec 32} (h : u.toNat < 2 ^ 31) :
    Conv.arrayIndex? (F64.ofInt32 u) = some u.toNat := by
  have h1 : F64.ofInt32 u = F64.ofNat u.toNat := by
    rw [F64.ofInt32_eq, F64.ofNat_eq_ofInt, BitVec.toInt_eq_toNat_cond]
    split
    · rfl
    · omega
  rw [h1, Conv.arrayIndex?_ofNat (by omega)]

/-- A value masked with a literal below `2^31` is a valid array index. -/
@[ts_bits] theorem Conv.arrayIndex?_ofInt32_and (v : BitVec 32) {m : Nat} (hm : m < 2 ^ 31) :
    Conv.arrayIndex? (F64.ofInt32 (v &&& BitVec.ofNat 32 m)) = some (v &&& BitVec.ofNat 32 m).toNat :=
  Conv.arrayIndex?_ofInt32 (by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hm))

/-- The bound of a masked index (for the array read's bounds test `k < xs.size`). -/
@[ts_bits] theorem toNat_and_ofNat_lt (v : BitVec 32) {m k : Nat} (h : m < k) :
    ((v &&& BitVec.ofNat 32 m).toNat < k) = True :=
  eq_true (by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    exact Nat.lt_of_le_of_lt (Nat.le_trans Nat.and_le_right (Nat.mod_le _ _)) h)

end StrictTS

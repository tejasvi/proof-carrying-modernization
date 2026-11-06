import CIR
import EquivLean.Repr.Int

/-!
# C integers as bit vectors

cirlean keeps C integers as mathematical integers with range checks (`Val.int v`): signed
overflow is undefined, unsigned arithmetic wraps (`CIR.wrap`), bitwise operators go through
the two's-complement representation (`CIR.bitwise`).  Rust (Aeneas `U32.bv`), Java
(`Value.int : BitVec 32`) and the TypeScript int32 idioms work on bit vectors.

This file restates the unsigned C operations on bit vectors: for operands in range, the
result of `evalBinop`/`evalShift`/`evalUnop` is the `toNat` of the corresponding `BitVec`
operation.  With the coupling `v = ↑b.toNat` between a C variable and a bit vector of another
encoding, a leaf goal of a C ↔ Rust/Java proof becomes an identity of bit-vector terms, which
`simp` (via `ofInt_toNat`) or `bv_decide` closes.
-/

namespace EquivLean.Cir

open CIR

/-- Unsigned `wrap` is reduction modulo `2^w`. -/
theorem wrap_false (w : Nat) (z : Int) : wrap false w z = z % 2 ^ w := by
  simp [wrap]

theorem emod_two_pow_eq (w : Nat) (z : Int) :
    z % 2 ^ w = ((BitVec.ofInt w z).toNat : Int) := by
  have hpos : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  have h2 : ((2 ^ w : Nat) : Int) = 2 ^ w := by norm_cast
  rw [BitVec.toNat_ofInt, h2, Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hpos))]

/-- Unsigned `wrap` is the `toNat` of the bit vector. -/
theorem wrap_false_eq (w : Nat) (z : Int) : wrap false w z = ((BitVec.ofInt w z).toNat : Int) := by
  rw [wrap_false, emod_two_pow_eq]

/-- Unsigned bitwise operations are bit-vector operations. -/
theorem bitwise_false_eq (w : Nat) (f : BitVec w → BitVec w → BitVec w) (x y : Int) :
    bitwise false w f x y = ((f (BitVec.ofInt w x) (BitVec.ofInt w y)).toNat : Int) := by
  simp [bitwise]

/-- A bit vector read back through `toNat` and `ofInt` is itself. -/
@[simp] theorem ofInt_toNat {w : Nat} (b : BitVec w) : BitVec.ofInt w (b.toNat : Int) = b := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem inRange_false_iff (w : Nat) (x : Int) : inRange false w x = true ↔ URange w x := by
  simp [inRange, intMin, intMax, URange]
  omega

/-- In-range unsigned values are the `toNat` of their bit vector. -/
theorem eq_toNat_of_urange {w : Nat} {x : Int} (h : URange w x) :
    x = ((BitVec.ofInt w x).toNat : Int) := by
  rw [← emod_two_pow_eq, Int.emod_eq_of_lt h.1 h.2]

private theorem chk_u (w : Nat) (nsw : Bool) (z : Int) :
    (if inRange false w z then (Res.ok z : Res Int)
     else if (false && nsw) || (!false && false) then .ub "integer overflow"
     else .ok (wrap false w z)) = .ok ((BitVec.ofInt w z).toNat : Int) := by
  split
  · next h => rw [inRange_false_iff] at h; rw [← eq_toNat_of_urange h]
  · simp [wrap_false_eq]

/-- Unsigned addition (no `nuw`): bit-vector addition. -/
theorem evalBinop_add_u (nsw : Bool) (w : Nat) (x y : Int) :
    evalBinop .add nsw false false w x y = .ok ((BitVec.ofInt w x + BitVec.ofInt w y).toNat : Int) := by
  simp only [evalBinop]
  rw [chk_u, BitVec.ofInt_add]

theorem evalBinop_sub_u (nsw : Bool) (w : Nat) (x y : Int) :
    evalBinop .sub nsw false false w x y = .ok ((BitVec.ofInt w x - BitVec.ofInt w y).toNat : Int) := by
  simp only [evalBinop]
  rw [chk_u, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, ← BitVec.sub_eq_add_neg]

theorem evalBinop_mul_u (nsw : Bool) (w : Nat) (x y : Int) :
    evalBinop .mul nsw false false w x y = .ok ((BitVec.ofInt w x * BitVec.ofInt w y).toNat : Int) := by
  simp only [evalBinop]
  rw [chk_u, BitVec.ofInt_mul]

theorem evalBinop_and_u (nsw nuw : Bool) (w : Nat) (x y : Int) :
    evalBinop .and nsw nuw false w x y = .ok ((BitVec.ofInt w x &&& BitVec.ofInt w y).toNat : Int) := by
  simp [evalBinop, bitwise_false_eq]

theorem evalBinop_or_u (nsw nuw : Bool) (w : Nat) (x y : Int) :
    evalBinop .or nsw nuw false w x y = .ok ((BitVec.ofInt w x ||| BitVec.ofInt w y).toNat : Int) := by
  simp [evalBinop, bitwise_false_eq]

theorem evalBinop_xor_u (nsw nuw : Bool) (w : Nat) (x y : Int) :
    evalBinop .xor nsw nuw false w x y = .ok ((BitVec.ofInt w x ^^^ BitVec.ofInt w y).toNat : Int) := by
  simp [evalBinop, bitwise_false_eq]

/-- Unsigned left shift by an in-range amount. -/
theorem evalShift_shl_u (w : Nat) (x n : Int) (hn : 0 ≤ n ∧ n < w) :
    evalShift true false w x n = .ok ((BitVec.ofInt w x <<< n.toNat).toNat : Int) := by
  have h1 : ¬ (n < 0 ∨ (w : Int) ≤ n) := by omega
  simp only [evalShift, h1, ite_false, Bool.false_eq_true]
  rw [wrap_false_eq, BitVec.shiftLeft_eq_mul_twoPow]
  have h2 : ((2 : Int) ^ n.toNat) = ((2 ^ n.toNat : Nat) : Int) := by simp
  rw [h2, BitVec.ofInt_mul, BitVec.ofInt_natCast]
  have h3 : BitVec.ofNat w (2 ^ n.toNat) = BitVec.twoPow w n.toNat := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_twoPow]
  rw [h3]
  simp

/-- Unsigned right shift of an in-range value by an in-range amount. -/
theorem evalShift_shr_u (w : Nat) (x n : Int) (hx : URange w x) (hn : 0 ≤ n ∧ n < w) :
    evalShift false false w x n = .ok ((BitVec.ofInt w x >>> n.toNat).toNat : Int) := by
  have h1 : ¬ (n < 0 ∨ (w : Int) ≤ n) := by omega
  simp only [evalShift, h1, ite_false, Bool.false_eq_true]
  congr 1
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  conv => lhs; rw [eq_toNat_of_urange hx]
  push_cast
  rfl


/-- The `toNat` of a bit vector, as an integer, is in the unsigned range. -/
theorem natCast_toNat_urange {w : Nat} (b : BitVec w) : URange w (b.toNat : Int) :=
  ⟨by omega, by have := b.isLt; exact_mod_cast this⟩

/-- Unsigned bitwise results are in range (so stores of them never fail). -/
theorem inRange_bitwise_false (w : Nat) (f : BitVec w → BitVec w → BitVec w) (x y : Int) :
    inRange false w (bitwise false w f x y) = true := by
  rw [inRange_false_iff, bitwise_false_eq]; exact natCast_toNat_urange _

/-- Unsigned wrapped results are in range. -/
theorem inRange_wrap_false (w : Nat) (z : Int) : inRange false w (wrap false w z) = true := by
  rw [inRange_false_iff, wrap_false_eq]; exact natCast_toNat_urange _


/-- The failed range check of a store of a 32-bit unsigned bitwise result is impossible. -/
theorem bitwise_false_32_bad (f : BitVec 32 → BitVec 32 → BitVec 32) (x y : Int) :
    ¬ (bitwise false 32 f x y < 0 ∨ 4294967295 < bitwise false 32 f x y) := by
  have h := inRange_bitwise_false 32 f x y
  rw [inRange_false_iff] at h
  unfold URange at h
  omega

/-- The failed range check of a store of a 32-bit unsigned wrapped result is impossible. -/
theorem wrap_false_32_bad (z : Int) :
    ¬ (wrap false 32 z < 0 ∨ 4294967295 < wrap false 32 z) := by
  have h := inRange_wrap_false 32 z
  rw [inRange_false_iff] at h
  unfold URange at h
  omega

end EquivLean.Cir

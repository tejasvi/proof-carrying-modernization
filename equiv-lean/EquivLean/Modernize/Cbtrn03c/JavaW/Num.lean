import EquivLean.Modernize.Cbtrn03c.JavaW.Pad

/-!
# CBTRN03C → Java: the helper `digits`

`digits(v, n)`: the last `n` decimal digits of `|v|`, zero-padded (`v > Long.MIN_VALUE`,
`n ≤ 18`), against the contract of `pow10`.  The loop (statement 13) appends digit `i` (from the
right) of `m = |v| % 10 ^ n` for `i = n - 1, …, 0`.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

def pow10Sig : MethodSig := ⟨"Cbtrn03c", .prim .long, "pow10", [.prim .int]⟩

theorem pow10_sat : Sat Gen.prog pow10Ref pow10Spec := pow10_vc.sat

set_option maxHeartbeats 0 in
theorem pow10_ok : ContractOK Gen.prog pow10Sig pow10Spec := by
  jcontract_ok [pow10_sat]

/-- The digits of `c / 10 ^ k`: one more digit than those of `c / 10 ^ (k + 1)`. -/
theorem zpadJ_div_step (c n k : Nat) (h : k < n) :
    zpadJ (c / 10 ^ k) (n - k) = zpadJ (c / 10 ^ (k + 1)) (n - (k + 1)) ++ [digitJ (c / 10 ^ k % 10)] := by
  obtain ⟨r, hr⟩ : ∃ r, n - k = r + 1 := ⟨n - (k + 1), by omega⟩
  rw [hr, show n - (k + 1) = r by omega, zpadJ, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

/-- The character `(char) ('0' + (int) (m / 10 ^ k % 10))` of a non-negative `long` `m`. -/
theorem digit_div_char (m : I64) (k : Nat) (hm : 0 ≤ m.toInt) (hk : k ≤ 18) :
    (JInt.toChar (48#32 + JLong.toInt ((m.sdiv (BitVec.ofNat 64 (10 ^ k))).srem 10#64))).setWidth 16 =
      digitJ (m.toNat / 10 ^ k % 10) := by
  have hp : 0 ≤ (BitVec.ofNat 64 (10 ^ k)).toInt := by rw [pow10_toInt hk]; exact Int.natCast_nonneg _
  have hq := sdiv_nonneg m _ hm hp
  have h10 : 0 ≤ (10#64 : BitVec 64).toInt := by decide
  have hd : ((m.sdiv (BitVec.ofNat 64 (10 ^ k))).srem 10#64).toNat = m.toNat / 10 ^ k % 10 := by
    rw [srem_toNat_of_nonneg _ _ hq h10, sdiv_toNat_of_nonneg _ _ hm hp, pow10_toNat hk]
    rfl
  rw [digit_char_of_lt _ (by rw [hd]; exact Nat.mod_lt _ (by decide)), hd]

/-- `10 ^ k` is 0 as a `long` exactly when `2 ^ 64` divides it. -/
theorem ofNat_pow10_eq_zero (k : Nat) : (BitVec.ofNat 64 (10 ^ k) = 0#64) = (64 ≤ k) := by
  apply propext
  rw [BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.zero_mod]
  constructor
  · intro h
    have h1 : 2 ^ 64 ∣ 10 ^ k := Nat.dvd_of_mod_eq_zero h
    have h2 : 2 ^ 64 ∣ 2 ^ k * 5 ^ k := by rw [← Nat.mul_pow]; exact h1
    have hc : Nat.Coprime (2 ^ 64) (5 ^ k) := Nat.Coprime.pow 64 k (by decide)
    exact (Nat.pow_dvd_pow_iff_le_right (by decide)).1 (hc.dvd_of_dvd_mul_right h2)
  · intro h
    apply Nat.mod_eq_zero_of_dvd
    obtain ⟨j, rfl⟩ : ∃ j, k = 64 + j := ⟨k - 64, by omega⟩
    rw [Nat.pow_add, show (10 : Nat) ^ 64 = 2 ^ 64 * 5 ^ 64 by rw [← Nat.mul_pow]]
    exact Nat.dvd_trans (Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _)

theorem pow10_nonneg {k : Nat} (h : k ≤ 18) : 0 ≤ (BitVec.ofNat 64 (10 ^ k)).toInt := by
  rw [pow10_toInt h]; exact Int.natCast_nonneg _

/-! The value `m = |v| % 10 ^ n` of `digits`, for `v ≥ 0` and for `v < 0`. -/

theorem srem_abs_pos (v : I64) (k : Nat) (h1 : 0 ≤ v.toInt) (hk : k ≤ 18) :
    (BitVec.srem v (BitVec.ofNat 64 (10 ^ k))).toNat = v.toInt.natAbs % 10 ^ k := by
  rw [srem_toNat_of_nonneg _ _ h1 (pow10_nonneg hk), pow10_toNat hk, pos_toNat v h1]

theorem srem_abs_neg (v : I64) (k : Nat) (h1 : v.toInt < 0) (h2 : -9223372036854775808 < v.toInt)
    (hk : k ≤ 18) :
    (BitVec.srem (-v) (BitVec.ofNat 64 (10 ^ k))).toNat = v.toInt.natAbs % 10 ^ k := by
  obtain ⟨hn, hn0⟩ := neg_toNat v h2 h1
  rw [srem_toNat_of_nonneg _ _ hn0 (pow10_nonneg hk), pow10_toNat hk, hn]

theorem tmod_abs_pos (v : I64) (k : Nat) (h1 : 0 ≤ v.toInt) :
    0 ≤ v.toInt.tmod (BitVec.ofNat 64 (10 ^ k)).toInt :=
  Int.tmod_nonneg _ h1

theorem tmod_abs_neg (v : I64) (k : Nat) (h1 : v.toInt < 0) (h2 : -9223372036854775808 < v.toInt) :
    0 ≤ (-v).toInt.tmod (BitVec.ofNat 64 (10 ^ k)).toInt :=
  Int.tmod_nonneg _ (neg_toNat v h2 h1).2

abbrev digitsRef : MethodRef := Gen.Cbtrn03c.«digits(long,int)».ref

def digitsCallees : Contracts := [(pow10Sig, pow10Spec)]

def digitsSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧
     -9223372036854775808 < v.toInt ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 18 ∧ σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (zpadJ v.toInt.natAbs n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn03c" = σ.initOf "Cbtrn03c")

/-- At the loop head (statement 13): `m = |v| % 10 ^ n`, and the builder holds the digits of `m`
above position `i`. -/
def digitsInv : Invariants := [(13, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
  ∃ sb m i, fr.get 0 = some (.long m) ∧ fr.get 4 = some (.int i) ∧ fr.get 6 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder"
      (zpadJ (m.toNat / 10 ^ (i.toInt + 1).toNat) (n.toInt.toNat - (i.toInt + 1).toNat))) ∧
    m.toNat = v.toInt.natAbs % 10 ^ n.toInt.toNat ∧ 0 ≤ m.toInt ∧
    -1 ≤ i.toInt ∧ i.toInt < n.toInt ∧ n.toInt ≤ 18 ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ.initOf "Cbtrn03c" = σ0.initOf "Cbtrn03c" ∧
    σ0.initOf "Cbtrn03c" = .done)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem digits_vc : MethodVC Gen.prog digitsCallees.env 0 digitsRef digitsSpec digitsInv 80 := by
  jverify [digitsSpec, digitsInv, digitsCallees, pow10Sig, pow10Spec, Grows, zpadJ_div_step,
    digit_div_char, valueOfArg_char, ofNat_pow10_eq_zero, zpadJ_mod, srem_abs_pos, srem_abs_neg,
    tmod_abs_pos, tmod_abs_neg]

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.digits_vc

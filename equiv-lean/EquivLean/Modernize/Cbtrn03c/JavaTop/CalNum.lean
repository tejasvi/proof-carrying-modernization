import EquivLean.Modernize.Cbtrn03c.JavaTop.CalSpaces

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: the contracts of `pow10` and `digits`

`pow10(n)`: `10 ^ n` as a `long` (one loop invariant, statement 3).  `digits(v, n)`: the last `n`
decimal digits of `|v|`, zero-padded (`v > Long.MIN_VALUE`, `n ≤ 18`), against the contract of
`pow10`; the loop (statement 13) appends digit `i` (from the right) of `m = |v| % 10 ^ n` for
`i = n - 1, …, 0`.  Ported from cir-repin's `T3/Lib.lean`, `T3/Str.lean`, `T3/Num.lean` (a new
string, `Agree` as the frame); `digits_ok` (the model's `digs`) by the rule of consequence.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

/-! ## Digits -/

/-- The digit `d` as a UTF-16 unit. -/
def digitJ (d : Nat) : JChar := BitVec.ofNat 16 (48 + d)

/-- The last `m` decimal digits of `c`, zero-padded (`digits`). -/
def zpadJ (c : Nat) : Nat → JStr
  | 0 => []
  | m + 1 => zpadJ (c / 10) m ++ [digitJ (c % 10)]

theorem zpadJ_length (c m : Nat) : (zpadJ c m).length = m := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih => simp [zpadJ, ih]

/-- Only the last `m` digits count. -/
theorem zpadJ_mod (c m : Nat) : zpadJ (c % 10 ^ m) m = zpadJ c m := by
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
    have h1 : c % 10 ^ (m + 1) / 10 = c / 10 % 10 ^ m := by
      rw [Nat.pow_succ, Nat.mul_comm (10 ^ m) 10, Nat.mod_mul_right_div_self]
    have h2 : c % 10 ^ (m + 1) % 10 = c % 10 := by
      rw [Nat.pow_succ]; exact Nat.mod_mod_of_dvd _ (Nat.dvd_mul_left 10 _)
    simp only [zpadJ, h1, h2, ih]

theorem toDigits_succ' (n v : Nat) : _root_.Cobol.Digits.toDigits 10 (n + 1) v =
    _root_.Cobol.Digits.toDigits 10 n (v / 10) ++ [v % 10] := rfl

/-- `digits` builds the model's zero-padded digits. -/
theorem zpadJ_eq (c n : Nat) : zpadJ c n = jline (zpad n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [zpadJ, ih, zpad, zpad, toDigits_succ', List.map_append]
    simp [jline, digitJ]

/-! ## Machine arithmetic -/

theorem msb_false_of_toInt_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) : l.msb = false := by
  have := BitVec.toInt_eq_toNat_cond l
  have hl := l.isLt
  rw [BitVec.msb_eq_decide]
  simp only [decide_eq_false_iff_not, Nat.not_le]
  by_cases hc : 2 * l.toNat < 2 ^ 64
  · omega
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' hc)] at this
    · omega

theorem toNat_of_toInt_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) : (l.toNat : Int) = l.toInt := by
  have := BitVec.toInt_eq_toNat_cond l
  split at this <;> omega

/-- `sdiv` of non-negative `long`s is the natural quotient. -/
theorem sdiv_toNat_of_nonneg (l p : BitVec 64) (hl : 0 ≤ l.toInt) (hp : 0 ≤ p.toInt) :
    (l.sdiv p).toNat = l.toNat / p.toNat := by
  rw [BitVec.sdiv_eq, msb_false_of_toInt_nonneg l hl, msb_false_of_toInt_nonneg p hp]
  simp [BitVec.toNat_udiv]

theorem sdiv_nonneg (l p : BitVec 64) (hl : 0 ≤ l.toInt) (hp : 0 ≤ p.toInt) :
    0 ≤ (l.sdiv p).toInt := by
  have hn := sdiv_toNat_of_nonneg l p hl hp
  have hl2 := l.isLt
  have hlt : 2 * l.toNat < 2 ^ 64 := by
    have := BitVec.toInt_eq_toNat_cond l; split at this <;> omega
  have hq : (l.sdiv p).toNat ≤ l.toNat := by rw [hn]; exact Nat.div_le_self _ _
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

/-- `srem` of non-negative `long`s is the natural remainder. -/
theorem srem_toNat_of_nonneg (l p : BitVec 64) (hl : 0 ≤ l.toInt) (hp : 0 ≤ p.toInt) :
    (l.srem p).toNat = l.toNat % p.toNat := by
  rw [BitVec.srem_eq, msb_false_of_toInt_nonneg l hl, msb_false_of_toInt_nonneg p hp]
  simp [BitVec.toNat_umod]

theorem srem_nonneg (l p : BitVec 64) (hl : 0 ≤ l.toInt) (hp : 0 ≤ p.toInt) :
    0 ≤ (l.srem p).toInt := by
  have hn := srem_toNat_of_nonneg l p hl hp
  have hl2 := l.isLt
  have hlt : 2 * l.toNat < 2 ^ 64 := by
    have := BitVec.toInt_eq_toNat_cond l; split at this <;> omega
  have hq : (l.srem p).toNat ≤ l.toNat := by rw [hn]; exact Nat.mod_le _ _
  rw [BitVec.toInt_eq_toNat_cond]; split <;> omega

/-- `10 ^ k` as a `long` times 10. -/
theorem pow10_mul (k : Nat) : BitVec.ofNat 64 (10 ^ k) * 10#64 = BitVec.ofNat 64 (10 ^ (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.pow_succ, Nat.mod_mul_mod]

theorem pow10_toNat {k : Nat} (h : k ≤ 18) : (BitVec.ofNat 64 (10 ^ k)).toNat = 10 ^ k := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  calc 10 ^ k ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) h
    _ < 2 ^ 64 := by decide

theorem pow10_toInt {k : Nat} (h : k ≤ 18) : (BitVec.ofNat 64 (10 ^ k)).toInt = (10 ^ k : Nat) := by
  rw [BitVec.toInt_eq_toNat_cond, pow10_toNat h]
  have : 2 * 10 ^ k < 2 ^ 64 := by
    calc 2 * 10 ^ k ≤ 2 * 10 ^ 18 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h)
      _ < 2 ^ 64 := by decide
  simp [this]

/-- The character `(char) ('0' + (int) d)` of a `long` digit `0 ≤ d < 10`. -/
theorem digit_char_of_lt (l : BitVec 64) (h : l.toNat < 10) :
    (JInt.toChar (48#32 + JLong.toInt l)).setWidth 16 = digitJ l.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [digitJ, JInt.toChar, JLong.toInt, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

/-- `lcmp` against 0, as the sign of the value. -/
theorem cmp_zero_nonneg_iff (a : I64) : 0 ≤ (JLong.cmp a 0#64).toInt ↔ 0 ≤ a.toInt := by
  unfold JLong.cmp
  by_cases h1 : a.slt 0#64
  · have : a.toInt < 0 := by
      rw [BitVec.slt_iff_toInt_lt] at h1; simpa using h1
    simp only [h1, ite_true]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; omega
  · have : 0 ≤ a.toInt := by
      rw [BitVec.slt_iff_toInt_lt] at h1; simp at h1; omega
    simp only [h1]
    constructor
    · intro _; exact this
    · intro _
      by_cases h2 : a = 0#64
      · simp [h2]
      · simp only [h2, ite_false]; decide

/-- The absolute value of a `long` other than `Long.MIN_VALUE`, as the helpers compute it. -/
theorem abs_toNat (v : I64) (hv : -9223372036854775808 < v.toInt) :
    (if 0 ≤ v.toInt then v else -v).toNat = v.toInt.natAbs ∧
    0 ≤ (if 0 ≤ v.toInt then v else -v).toInt := by
  have habs : (if 0 ≤ v.toInt then v else -v).toInt = (v.toInt.natAbs : Int) := by
    split
    · next h => omega
    · next h =>
      rw [BitVec.toInt_neg_of_ne_intMin]
      · omega
      · intro he
        have := congrArg BitVec.toInt he
        rw [BitVec.toInt_intMin] at this
        simp at this
        omega
  have hnn : 0 ≤ (if 0 ≤ v.toInt then v else -v).toInt := by rw [habs]; omega
  refine ⟨?_, hnn⟩
  have := toNat_of_toInt_nonneg _ hnn
  omega

theorem neg_toNat (v : I64) (hv : -9223372036854775808 < v.toInt) (hneg : v.toInt < 0) :
    (-v).toNat = v.toInt.natAbs ∧ 0 ≤ (-v).toInt := by
  have h := abs_toNat v hv
  simp only [show ¬ (0 ≤ v.toInt) by omega, ↓reduceIte] at h
  exact h

theorem pos_toNat (v : I64) (hpos : 0 ≤ v.toInt) : v.toNat = v.toInt.natAbs := by
  have := toNat_of_toInt_nonneg v hpos
  omega

/-! ## `pow10` -/

abbrev pow10Ref : MethodRef := Gen.Cbtrn03c.«pow10(int)».ref

def pow10Sig : MethodSig := ⟨"Cbtrn03c", .prim .long, "pow10", [.prim .int]⟩

def pow10Spec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     r = some (.long (BitVec.ofNat 64 (10 ^ n.toInt.toNat))) ∧ σ' = σ)

/-- At the loop head (statement 3): the product is `10 ^ i`.  Locals: `i0` 0, `i2` 1, `l1` 2. -/
def pow10Inv : Invariants := [(3, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧
    fr.get 2 = some (.long (BitVec.ofNat 64 (10 ^ i.toInt.toNat))) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ = σ0)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pow10_vc : MethodVC Gen.prog (fun _ => none) 0 pow10Ref pow10Spec pow10Inv 40 := by
  jverify [pow10Spec, pow10Inv, pow10_mul]

theorem pow10_sat : Sat Gen.prog pow10Ref pow10Spec := pow10_vc.sat

set_option maxHeartbeats 0 in
theorem pow10_ok : ContractOK Gen.prog pow10Sig pow10Spec := by
  jcontract_ok [pow10_sat]

/-! ## `digits` -/

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

/-- `digits` (cir-repin's `digitsSpec`, a new string, `Agree` as the frame). -/
def digitsSpec : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧
     -9223372036854775808 < v.toInt ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 18 ∧ σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (zpadJ v.toInt.natAbs n.toInt.toNat)) ∧
       σ.next ≤ x ∧ σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- At the loop head (statement 13): `m = |v| % 10 ^ n`, and the builder holds the digits of `m`
above position `i`.  Locals: `l0` 0, `i1` 4, `$r0` 6. -/
def digitsInv : Invariants := [(13, fun args σ0 fr σ => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
  ∃ sb m i, fr.get 0 = some (.long m) ∧ fr.get 4 = some (.int i) ∧ fr.get 6 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder"
      (zpadJ (m.toNat / 10 ^ (i.toInt + 1).toNat) (n.toInt.toNat - (i.toInt + 1).toNat))) ∧
    m.toNat = v.toInt.natAbs % 10 ^ n.toInt.toNat ∧ 0 ≤ m.toInt ∧
    -1 ≤ i.toInt ∧ i.toInt < n.toInt ∧ n.toInt ≤ 18 ∧ σ0.next ≤ sb ∧ σ0.next ≤ σ.next ∧
    Agree σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
    σ.initOf "Cbtrn03c" = σ0.initOf "Cbtrn03c" ∧ σ0.initOf "Cbtrn03c" = .done)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem digits_vc : MethodVC Gen.prog digitsCallees.env 0 digitsRef digitsSpec digitsInv 80 := by
  jverify [digitsSpec, digitsInv, digitsCallees, pow10Sig, pow10Spec, Agree, zpadJ_div_step,
    digit_div_char, valueOfArg_char, ofNat_pow10_eq_zero, zpadJ_mod, srem_abs_pos, srem_abs_neg,
    tmod_abs_pos, tmod_abs_neg]
  all_goals first
    | (intro h; subst h; jomega)
    | skip

theorem digits_sat : Sat Gen.prog digitsRef digitsSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [digitsCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact pow10_ok)) digits_vc

set_option maxHeartbeats 0 in
theorem digitsC_ok : ContractOK Gen.prog digitsSig digitsSpec := by
  jcontract_ok [digits_sat]

/-- `digits` on the model's `digs`. -/
theorem digitsT_sat : Sat Gen.prog digitsRef digitsSpecT := by
  intro args σ o hp hx
  have ho := digits_sat args σ o hp hx
  cases o with
  | normal r σ' =>
    intro v n heq
    obtain ⟨x, hr, hxs, h1, h2, h3, h4, h5⟩ := ho v n heq
    refine ⟨x, hr, ?_, h1, h2, h3, h4, h5⟩
    rw [hxs, zpadJ_eq]
    rfl
  | exc e σ' => exact ho
  | wrong m => exact ho

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

set_option maxHeartbeats 0 in
theorem digits_ok : ContractOK Gen.prog digitsSig digitsSpecT := by
  jcontract_ok [Cal.digitsT_sat]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.pow10_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.digitsC_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.digits_ok

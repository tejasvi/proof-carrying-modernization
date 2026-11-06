/-
`examples/Hash/fnv.ts`: two FNV-1a implementations over the UTF-16 code units of a string.
Each is proved to compute the same 32-bit function `fnvBV` (stated on `BitVec 32`), for every
string shorter than 2^30 code units (JavaScript engines cap string length well below that).
The 32-bit identity behind the shift version is proved twice: `shift_sum` by `bv_decide`, and
`shift_sum_kernel` by the kernel alone (`bv_omega`: `BitVec.toNat` and linear arithmetic modulo
`2^32`); the equivalence theorem uses the kernel-only proof, so it needs only the standard axioms.
-/
import Hash.FnvEx
import StrictTS.Proof.Tactics

open StrictTS JS FnvEx F64

/-- One FNV-1a step on 32-bit words. -/
def fnvStep (h : BitVec 32) (u : UInt16) : BitVec 32 := (h ^^^ BitVec.ofNat 32 u.toNat) * 16777619#32

/-- FNV-1a of a sequence of code units, from the offset basis `2166136261`. -/
def fnvBV (us : List UInt16) : BitVec 32 := us.foldl fnvStep 2166136261#32

/-- Natural number held by a counter variable. -/
def ctr (v : Val TT .num) : Nat := match v.toNum.toInt? with | some n => n.toNat | none => 0

@[simp] theorem ctr_ofNat (n : Nat) (h : n ≤ 2 ^ 53) : ctr (.num (ofNat n)) = n := by
  simp only [ctr, ofNat_eq_ofInt]
  rw [toInt?_ofInt (by simp only [Safe]; omega)]
  simp

/-- The prefix hash after one more code unit. -/
theorem fnvBV_take_succ {us : List UInt16} {i : Nat} (hu : i < us.length) :
    fnvBV (us.take (i + 1)) = fnvStep (fnvBV (us.take i)) us[i] := by
  simp only [fnvBV, List.take_add_one, List.getElem?_eq_getElem hu, Option.toList, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- One loop iteration of `fnvImul`, as a statement about doubles. -/
theorem step_imul (x : BitVec 32) (u : UInt16) :
    (((ofUint32 x).bxor (ofNat u.toNat)).imul (ofNat 16777619)).shr (ofNat 0) = ofUint32 (fnvStep x u) := by
  have hu : u.toNat < 2 ^ 16 := u.toNat_lt
  simp only [F64.bxor, F64.imul, F64.shr, F64.toInt32_ofUint32, F64.toInt32_ofInt32, fnvStep,
    toInt32_ofNat_u16 hu]
  simp (disch := ts_safe) only [F64.ofNat_eq_ofInt, F64.toInt32_ofInt]
  simp

theorem fnvImul_spec (I : Impl) (s : JSStr) (hs : s.length < 2 ^ 30) (w : World TT) :
    exec (callFun I program fnvImulRef (.cons (.str s) .nil)) w =
      some (.ok (.num (ofUint32 (fnvBV s.units))), w) := by
  rw [fnvImul_call]
  simp only [fnvImulDef, ts_sym]
  ts_while
    (fun env w₁ => ∃ i, i ≤ s.length ∧ w₁ = w ∧
      env = .cons (.num (ofNat i)) (.cons (.num (ofUint32 (fnvBV (s.units.take i)))) (.cons (.str s) .nil))),
    (fun env _ => s.length - ctr env.head),
    (fun env w₁ => w₁ = w ∧
      env = .cons (.num (ofNat s.length)) (.cons (.num (ofUint32 (fnvBV s.units))) (.cons (.str s) .nil)))
  case step =>
    rintro env w₁ ⟨i, hi, rfl, rfl⟩
    have hi53 : i ≤ 2 ^ 53 := by omega
    have hl53 : s.length ≤ 2 ^ 53 := by omega
    by_cases hlt : i < s.length
    · have hu : i < s.units.length := hlt
      simp (disch := omega) [ts_sym, hlt, JSStr.charCodeAt?]
      refine ⟨⟨i + 1, by omega, rfl, ?_⟩, by omega⟩
      rw [fnvBV_take_succ hu]
      exact step_imul _ _
    · simp (disch := omega) [ts_sym, hlt]
      obtain rfl : i = s.length := by omega
      simp [List.take_of_length_le, JSStr.length]
  case init => exact ⟨0, by omega, rfl, by simp [fnvBV, ofUint32_eq, ofNat_eq_ofInt]⟩
  obtain ⟨rfl, rfl⟩ := hpost
  simp [ts_sym]

/-- `(h ^ c) >>> 0` on a uint32 `h` and a code unit `c`. -/
theorem xor_shr_zero (x : BitVec 32) (u : UInt16) :
    ((ofUint32 x).bxor (ofNat u.toNat)).shr (ofNat 0) = ofUint32 (x ^^^ BitVec.ofNat 32 u.toNat) := by
  have hu : u.toNat < 2 ^ 16 := u.toNat_lt
  simp only [F64.bxor, F64.shr, F64.toInt32_ofUint32, F64.toInt32_ofInt32, toInt32_ofNat_u16 hu]
  simp (disch := ts_safe) only [F64.ofNat_eq_ofInt, F64.toInt32_ofInt]
  simp

/-- The FNV prime as shifts and additions, on doubles holding a uint32. -/
theorem shift_sum (b : BitVec 32) :
    (ofUint32 b + (ofUint32 b).shl (ofNat 1) + (ofUint32 b).shl (ofNat 4) + (ofUint32 b).shl (ofNat 7) +
      (ofUint32 b).shl (ofNat 8) + (ofUint32 b).shl (ofNat 24)).shr (ofNat 0) = ofUint32 (b * 16777619#32) := by
  ts_int32

/-- The FNV prime as shifts and additions on 32-bit words, checked by the kernel alone:
`bv_omega` turns it into linear arithmetic on `BitVec.toNat` modulo `2^32` (`omega`), with no
`bv_decide` and no compiled LRAT checker. -/
theorem fnv_prime_shifts (b : BitVec 32) :
    b + b <<< 1 + b <<< 4 + b <<< 7 + b <<< 8 + b <<< 24 = b * 16777619#32 := by
  bv_omega

/-- `shift_sum` with a kernel-only proof: the normalisation of `ts_int32` into `BitVec 32`,
then `fnv_prime_shifts` in place of `bv_decide`. -/
theorem shift_sum_kernel (b : BitVec 32) :
    (ofUint32 b + (ofUint32 b).shl (ofNat 1) + (ofUint32 b).shl (ofNat 4) + (ofUint32 b).shl (ofNat 7) +
      (ofUint32 b).shl (ofNat 8) + (ofUint32 b).shl (ofNat 24)).shr (ofNat 0) = ofUint32 (b * 16777619#32) := by
  simp only [F64.shr, F64.shl, F64.ofNat_eq_ofInt, F64.toInt32_ofUint32]
  simp (disch := ts_safe) only [F64.toInt32_ofInt]
  simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.zero_mod,
    BitVec.ushiftRight_zero, F64.ofUint32_eq, F64.ofInt32_eq]
  simp (disch := ts_safe) only [F64.add_ofInt, F64.toInt32_ofInt]
  simp (disch := ts_safe) only [F64.ofInt_inj_iff, Int.ofNat_inj, BitVec.toNat_inj]
  simp only [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  exact fnv_prime_shifts b

/-- One loop iteration of `fnvShift`. -/
theorem step_shift (x : BitVec 32) (u : UInt16) :
    (((ofUint32 x).bxor (ofNat u.toNat)).shr (ofNat 0) +
      (((ofUint32 x).bxor (ofNat u.toNat)).shr (ofNat 0)).shl (ofNat 1) +
      (((ofUint32 x).bxor (ofNat u.toNat)).shr (ofNat 0)).shl (ofNat 4) +
      (((ofUint32 x).bxor (ofNat u.toNat)).shr (ofNat 0)).shl (ofNat 7) +
      (((ofUint32 x).bxor (ofNat u.toNat)).shr (ofNat 0)).shl (ofNat 8) +
      (((ofUint32 x).bxor (ofNat u.toNat)).shr (ofNat 0)).shl (ofNat 24)).shr (ofNat 0)
      = ofUint32 (fnvStep x u) := by
  rw [xor_shr_zero, shift_sum_kernel]
  rfl

theorem fnvShift_spec (I : Impl) (s : JSStr) (hs : s.length < 2 ^ 30) (w : World TT) :
    exec (callFun I program fnvShiftRef (.cons (.str s) .nil)) w =
      some (.ok (.num (ofUint32 (fnvBV s.units))), w) := by
  rw [fnvShift_call]
  simp only [fnvShiftDef, ts_sym]
  ts_while
    (fun env w₁ => ∃ i, i ≤ s.length ∧ w₁ = w ∧
      env = .cons (.num (ofNat i)) (.cons (.num (ofUint32 (fnvBV (s.units.take i)))) (.cons (.str s) .nil))),
    (fun env _ => s.length - ctr env.head),
    (fun env w₁ => w₁ = w ∧
      env = .cons (.num (ofNat s.length)) (.cons (.num (ofUint32 (fnvBV s.units))) (.cons (.str s) .nil)))
  case step =>
    rintro env w₁ ⟨i, hi, rfl, rfl⟩
    have hi53 : i ≤ 2 ^ 53 := by omega
    have hl53 : s.length ≤ 2 ^ 53 := by omega
    by_cases hlt : i < s.length
    · have hu : i < s.units.length := hlt
      simp (disch := omega) [ts_sym, hlt, JSStr.charCodeAt?]
      refine ⟨⟨i + 1, by omega, rfl, ?_⟩, by omega⟩
      rw [fnvBV_take_succ hu]
      exact step_shift _ _
    · simp (disch := omega) [ts_sym, hlt]
      obtain rfl : i = s.length := by omega
      simp [List.take_of_length_le, JSStr.length]
  case init => exact ⟨0, by omega, rfl, by simp [fnvBV, ofUint32_eq, ofNat_eq_ofInt]⟩
  obtain ⟨rfl, rfl⟩ := hpost
  simp [ts_sym]

/-- **Differential equivalence** of the two FNV-1a implementations (for all strings shorter
than 2^30 code units, on every world). -/
theorem fnvShift_eq_fnvImul (I : Impl) (s : JSStr) (hs : s.length < 2 ^ 30) (w : World TT) :
    exec (callFun I program fnvShiftRef (.cons (.str s) .nil)) w =
      exec (callFun I program fnvImulRef (.cons (.str s) .nil)) w := by
  rw [fnvShift_spec I s hs w, fnvImul_spec I s hs w]

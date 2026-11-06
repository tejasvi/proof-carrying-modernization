import EquivLean.Demo.Thrift.Java.Bits
import EquivLean.Demo.Thrift.Spec

/-!
# Thrift → Java (T4): the varint readers' accumulator

`readVarint32`/`readVarint64` OR the 7-bit groups of the bytes into an `int`/`long`, shifted by
`7·k`. `vacc cs` is the value of the groups `cs` (least significant first); `readVarint_prefix`
reads a varint whose first bytes are the continuation bytes `cs`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

open EquivLean.Demo.Thrift

/-- The value of the 7-bit groups `cs`, least significant first. -/
def vacc : List UInt8 → Nat
  | [] => 0
  | c :: cs => c.toNat % 128 + 128 * vacc cs

theorem vacc_lt : ∀ (cs : List UInt8), vacc cs < 128 ^ cs.length
  | [] => by simp [vacc]
  | c :: cs => by
    have h1 := vacc_lt cs
    have h2 : c.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
    simp only [vacc, List.length_cons, Nat.pow_succ]
    have : 128 * vacc cs + 128 ≤ 128 * 128 ^ cs.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h1
    rw [Nat.mul_comm (128 ^ cs.length) 128]
    omega

theorem vacc_append : ∀ (cs ds : List UInt8), vacc (cs ++ ds) = vacc cs + 128 ^ cs.length * vacc ds
  | [], ds => by simp [vacc]
  | c :: cs, ds => by
    simp only [List.cons_append, vacc, vacc_append cs ds, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 128 (128 ^ cs.length)]
    omega

/-- A varint whose first bytes `cs` all have the high bit: the rest is read with `k` fewer bytes. -/
theorem readVarint_prefix : ∀ (cs : List UInt8) (m : Nat) (s : Spec.Bytes),
    (∀ c ∈ cs, 128 ≤ c.toNat) →
    Spec.readVarint (cs.length + m) (cs ++ s) =
      (Spec.readVarint m s).map fun p => (vacc cs + 128 ^ cs.length * p.1, p.2)
  | [], m, s, _ => by
    simp only [List.length_nil, Nat.zero_add, List.nil_append, vacc, Nat.pow_zero, Nat.one_mul]
    cases Spec.readVarint m s <;> rfl
  | c :: cs, m, s, h => by
    have hc : 128 ≤ c.toNat := h c List.mem_cons_self
    have ih := readVarint_prefix cs m s (fun d hd => h d (List.mem_cons_of_mem _ hd))
    rw [List.length_cons, show cs.length + 1 + m = (cs.length + m) + 1 by omega, List.cons_append]
    simp only [Spec.readVarint, if_neg (show ¬ c.toNat < 128 by omega), ih, Option.map_map]
    congr 1
    funext p
    simp only [Function.comp, vacc, List.length_cons, Nat.pow_succ]
    congr 1
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 128 (128 ^ cs.length)]
    omega

/-! ## The accumulation on `int` -/

theorem ofNat_getLsbD_high {a i s : Nat} (ha : a < 2 ^ s) (hi : s ≤ i) :
    (BitVec.ofNat 32 a).getLsbD i = false := by
  rw [BitVec.getLsbD_ofNat]
  have : a.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hi))
  simp [this]

/-- OR-ing a group above the bits already accumulated adds it. -/
theorem or_shl_eq_add {a s : Nat} {g : I32} (ha : a < 2 ^ s) (hs : s < 32) :
    BitVec.ofNat 32 a ||| (g <<< s) = BitVec.ofNat 32 (a + 2 ^ s * g.toNat) := by
  have hand : BitVec.ofNat 32 a &&& (g <<< s) = 0#32 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
    by_cases h : s ≤ i
    · rw [ofNat_getLsbD_high ha h]; simp
    · simp [show i < s by omega]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hand]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_comm (2 ^ s) g.toNat]

theorem shl_ofNat (x : I32) {s : Nat} (hs : s < 32) : JInt.shl x (BitVec.ofNat 32 s) = x <<< s := by
  simp only [JInt.shl, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : s < 2 ^ 32), Nat.mod_eq_of_lt hs]

end EquivLean.Demo.Thrift.Java

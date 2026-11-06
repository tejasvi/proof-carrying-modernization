import EquivLean.Demo.Thrift.Java.Zz

/-!
# Thrift → Java (T4): the zigzag methods' bodies
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev zz32Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«intToZigZag(int)».ref
abbrev zz64Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«longToZigzag(long)».ref
abbrev uzz32Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«zigzagToInt(int)».ref
abbrev uzz64Ref : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«zigzagToLong(long)».ref

/-- `intToZigZag(n)` returns `zigzag n` and changes nothing. -/
def zz32Spec : Spec := Spec.of (fun args _ => ∃ (p : Addr) (n : I32), args = [.ref p, .int n])
  (fun args σ r σ' => ∀ (p : Addr) (n : I32), args = [.ref p, .int n] →
    ∃ z : I32, r = some (.int z) ∧ z.toNat = Spec.zigzag n.toInt ∧ σ' = σ)

/-- `longToZigzag(n)` returns `zigzag n` and changes nothing. -/
def zz64Spec : Spec := Spec.of (fun args _ => ∃ (p : Addr) (n : I64), args = [.ref p, .long n])
  (fun args σ r σ' => ∀ (p : Addr) (n : I64), args = [.ref p, .long n] →
    ∃ z : I64, r = some (.long z) ∧ z.toNat = Spec.zigzag n.toInt ∧ σ' = σ)

/-- `zigzagToInt(u)` returns `unzigzag u` (every pattern) and changes nothing. -/
def uzz32Spec : Spec := Spec.of (fun args _ => ∃ (p : Addr) (u : I32), args = [.ref p, .int u])
  (fun args σ r σ' => ∀ (p : Addr) (u : I32), args = [.ref p, .int u] →
    ∃ z : I32, r = some (.int z) ∧ z.toInt = Spec.unzigzag u.toNat ∧ σ' = σ)

/-- `zigzagToLong(u)` returns `unzigzag u` (every pattern) and changes nothing. -/
def uzz64Spec : Spec := Spec.of (fun args _ => ∃ (p : Addr) (u : I64), args = [.ref p, .long u])
  (fun args σ r σ' => ∀ (p : Addr) (u : I64), args = [.ref p, .long u] →
    ∃ z : I64, r = some (.long z) ∧ z.toInt = Spec.unzigzag u.toNat ∧ σ' = σ)

theorem ushr1_32 (w : I32) : (JInt.ushr w 1#32).toNat = w.toNat / 2 := by
  simp only [JInt.ushr, show (1#32 : I32).toNat % 32 = 1 from rfl, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem ushr1_64 (w : I64) : (JLong.ushr w 1#32).toNat = w.toNat / 2 := by
  simp only [JLong.ushr, show (1#32 : I32).toNat % 64 = 1 from rfl, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem uzz32_goal (w : I32) :
    (((((JInt.ushr w 1#32).toNat ^^^ (4294967296 - w.toNat % 2) % 4294967296 : Nat) : Int)).bmod
      4294967296) = Spec.unzigzag w.toNat := by
  have h1 : (JInt.ushr w 1#32).toNat = w.toNat / 2 := ushr1_32 w
  have h2 : (4294967296 - w.toNat % 2) % 4294967296 = if w.toNat % 2 = 0 then 0 else 2 ^ 32 - 1 := by
    split <;> omega
  rw [h1, h2, ← Spec.unzigzag_xor32 w.isLt]
  exact Spec.toS_toU32 (Spec.unzigzag_range32 w.isLt)

theorem uzz64_goal (w : I64) :
    (((((JLong.ushr w 1#32).toNat ^^^ (18446744073709551616 - w.toNat % 2) % 18446744073709551616 : Nat) :
      Int)).bmod 18446744073709551616) = Spec.unzigzag w.toNat := by
  have h1 : (JLong.ushr w 1#32).toNat = w.toNat / 2 := ushr1_64 w
  have h2 : (18446744073709551616 - w.toNat % 2) % 18446744073709551616 =
      if w.toNat % 2 = 0 then 0 else 2 ^ 64 - 1 := by
    split <;> omega
  rw [h1, h2, ← Spec.unzigzag_xor64 w.isLt]
  exact Spec.toS_toU64 (Spec.unzigzag_range64 w.isLt)

theorem zz32_body : BodyVCP (Contains · [cpC]) (fun _ => Contracts.env []) 0 zz32Ref (fun _ => zz32Spec)
    [] 20 := by
  jverify_body [Contains, zz32Spec]
  all_goals (rw [← BitVec.toNat_xor]; exact zz32_val _)

theorem zz64_body : BodyVCP (Contains · [cpC]) (fun _ => Contracts.env []) 0 zz64Ref (fun _ => zz64Spec)
    [] 20 := by
  jverify_body [Contains, zz64Spec]
  all_goals (rw [← BitVec.toNat_xor]; exact zz64_val _)

/- JimpleLean 2312Z keeps `BitVec.toInt_xor`/`_and`/`_or` out of its simp set: the goal left is then
`uzz32_val`'s statement (0149Z rewrote it to `uzz32_goal`'s form), and the leaf closers need more
recursion depth before they give it up. -/
set_option maxRecDepth 100000 in
theorem uzz32_body : BodyVCP (Contains · [cpC]) (fun _ => Contracts.env []) 0 uzz32Ref (fun _ => uzz32Spec)
    [] 20 := by
  jverify_body [Contains, uzz32Spec]
  all_goals exact uzz32_val _

set_option maxRecDepth 100000 in
theorem uzz64_body : BodyVCP (Contains · [cpC]) (fun _ => Contracts.env []) 0 uzz64Ref (fun _ => uzz64Spec)
    [] 20 := by
  jverify_body [Contains, uzz64Spec]
  all_goals exact uzz64_val _

end EquivLean.Demo.Thrift.Java

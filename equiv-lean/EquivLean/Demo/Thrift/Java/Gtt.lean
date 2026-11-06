import EquivLean.Demo.Thrift.Java.Gam2

/-!
# Thrift → Java (T4): `getTType(byte)`, the TType of a compact type nibble

`getTType(b)` returns `ttypeOfCompact (b & 0x0F)`, and throws a `TProtocolException` ("don't know
what type") for the nibbles 14 and 15.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

abbrev gttRef : MethodRef :=
  EquivLean.Gen.ThriftJ.«org.apache.thrift.protocol.TCompactProtocol».«getTType(byte)».ref

def gttN (args : List Value) (σ : State) (r : Option Value) (σ' : State) : Prop :=
  ∀ (p : Addr) (b : I32), args = [.ref p, .int b] →
    ∃ tt, Spec.ttypeOfCompact (b.toNat % 16) = some tt ∧ r = some (.int (BitVec.ofNat 32 tt)) ∧ σ' = σ

def gttE (args : List Value) (σ : State) (e : Addr) (σ' : State) : Prop :=
  ∀ (p : Addr) (b : I32), args = [.ref p, .int b] →
    Spec.ttypeOfCompact (b.toNat % 16) = none ∧ ∃ fs, σ'.heap e = some (.plain tpeCls fs)

attribute [irreducible] gttN gttE

/-- (On the valid nibbles: the callers check the nibble first; nibbles 14 and 15 throw.) -/
def gttSpec : Spec := Spec.of
  (fun args σ => ∃ (p : Addr) (b : I32), args = [.ref p, .int b] ∧
     (Spec.ttypeOfCompact (b.toNat % 16)).isSome)
  gttN gttE

theorem and15_toNat (w : I32) : (w &&& 15#32).toNat = w.toNat % 16 := by
  rw [BitVec.toNat_and, show (15#32 : I32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem and15_toInt (w : I32) : (w &&& 15#32).toInt = ((w.toNat % 16 : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, and15_toNat]
  have : w.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [if_pos (by omega)]

theorem bmod_and15 (x : Nat) : ((x &&& 15 : Nat) : Int).bmod 4294967296 = ((x % 16 : Nat) : Int) := by
  rw [show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have : x % 2 ^ 4 < 16 := Nat.mod_lt _ (by decide)
  rw [Int.bmod_eq_of_le (by omega) (by omega)]

theorem gtt_ok {σ : State} {p : Addr} {w : I32} {k tt : Nat} (hk : ((w.toNat : Int) % 16).toNat = k)
    (htt : Spec.ttypeOfCompact k = some tt) :
    gttN [.ref p, .int w] σ (some (.int (BitVec.ofNat 32 tt))) σ := by
  unfold gttN
  intro p' w' h
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at h
  obtain ⟨-, rfl⟩ := h
  have : w.toNat % 16 = k := by omega
  exact ⟨tt, by rw [this]; exact htt, rfl, rfl⟩

theorem gtt_default {w : I32} (hcase : 14 ≤ ((w.toNat : Int) % 16).toNat)
    (hv : (Spec.ttypeOfCompact (w.toNat % 16)).isSome = true) : False := by
  have h : w.toNat % 16 = 14 ∨ w.toNat % 16 = 15 := by omega
  rcases h with h | h <;> rw [h] at hv <;> exact absurd hv (by decide)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem gtt_body : BodyVCP (Contains · [cpC, tpeC, teC]) (fun _ => Contracts.env []) 3 gttRef
    (fun _ => gttSpec) [] 100 := by
  jverify_body [Contains, gttSpec, instanceFields_tpe, ctorCall_exc_str, tpeCls, and15_toInt, and15_toNat, bmod_and15]
  all_goals first | exact gtt_ok ‹_› rfl | exact (gtt_default ‹_› ‹_›).elim

end EquivLean.Demo.Thrift.Java

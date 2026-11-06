import EquivLean.Demo.Thrift.Java.ZzB

/-!
# Thrift → Java (T4): zigzag i32 / i64, the results (E, D, M)

In every program that contains `TCompactProtocol`:
- (E) `intToZigZag(n)` returns `zigzag n` (`longToZigzag` likewise);
- (D) `zigzagToInt(zigzag n)` returns `n` (`zigzagToLong` likewise);
- (M) the decoders are total: on every pattern `u` they return `unzigzag u` and throw nothing.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem valid_empty (P : Program) : Valid P (Contracts.env []) := by
  intro sig S h
  simp [Contracts.env, List.lookup] at h

/-- **E for zigzag i32.** -/
theorem zz32_E {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (n : I32) {o : Outcome}
    (hm : MExec P zz32Ref [.ref p, .int n] σ o) :
    ∃ z : I32, o = .normal (some (.int z)) σ ∧ z.toNat = Spec.zigzag n.toInt := by
  have h := BodyVCP.sat zz32_body hF (valid_empty P) [.ref p, .int n] σ o ⟨p, n, rfl⟩ hm
  cases o with
  | normal r σ' =>
    simp only [zz32Spec, Spec.of] at h
    obtain ⟨z, hr, hz, hs⟩ := h p n rfl
    exact ⟨z, by rw [hr, hs], hz⟩
  | exc e σ' => simp only [zz32Spec, Spec.of] at h
  | wrong m => simp only [zz32Spec, Spec.of] at h

/-- **E for zigzag i64.** -/
theorem zz64_E {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (n : I64) {o : Outcome}
    (hm : MExec P zz64Ref [.ref p, .long n] σ o) :
    ∃ z : I64, o = .normal (some (.long z)) σ ∧ z.toNat = Spec.zigzag n.toInt := by
  have h := BodyVCP.sat zz64_body hF (valid_empty P) [.ref p, .long n] σ o ⟨p, n, rfl⟩ hm
  cases o with
  | normal r σ' =>
    simp only [zz64Spec, Spec.of] at h
    obtain ⟨z, hr, hz, hs⟩ := h p n rfl
    exact ⟨z, by rw [hr, hs], hz⟩
  | exc e σ' => simp only [zz64Spec, Spec.of] at h
  | wrong m => simp only [zz64Spec, Spec.of] at h

/-- **M for zigzag i32**: `zigzagToInt` is total, it returns `unzigzag u` on every pattern `u`. -/
theorem uzz32_M {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (u : I32) {o : Outcome}
    (hm : MExec P uzz32Ref [.ref p, .int u] σ o) :
    ∃ z : I32, o = .normal (some (.int z)) σ ∧ z.toInt = Spec.unzigzag u.toNat := by
  have h := BodyVCP.sat uzz32_body hF (valid_empty P) [.ref p, .int u] σ o ⟨p, u, rfl⟩ hm
  cases o with
  | normal r σ' =>
    simp only [uzz32Spec, Spec.of] at h
    obtain ⟨z, hr, hz, hs⟩ := h p u rfl
    exact ⟨z, by rw [hr, hs], hz⟩
  | exc e σ' => simp only [uzz32Spec, Spec.of] at h
  | wrong m => simp only [uzz32Spec, Spec.of] at h

/-- **M for zigzag i64**: `zigzagToLong` is total, it returns `unzigzag u` on every pattern `u`. -/
theorem uzz64_M {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (u : I64) {o : Outcome}
    (hm : MExec P uzz64Ref [.ref p, .long u] σ o) :
    ∃ z : I64, o = .normal (some (.long z)) σ ∧ z.toInt = Spec.unzigzag u.toNat := by
  have h := BodyVCP.sat uzz64_body hF (valid_empty P) [.ref p, .long u] σ o ⟨p, u, rfl⟩ hm
  cases o with
  | normal r σ' =>
    simp only [uzz64Spec, Spec.of] at h
    obtain ⟨z, hr, hz, hs⟩ := h p u rfl
    exact ⟨z, by rw [hr, hs], hz⟩
  | exc e σ' => simp only [uzz64Spec, Spec.of] at h
  | wrong m => simp only [uzz64Spec, Spec.of] at h

/-- **D for zigzag i32**: on `zigzag x`, `zigzagToInt` returns `x`. -/
theorem uzz32_D {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (x : I32) {o : Outcome}
    (hm : MExec P uzz32Ref [.ref p, .int (BitVec.ofNat 32 (Spec.zigzag x.toInt))] σ o) :
    o = .normal (some (.int x)) σ := by
  obtain ⟨z, ho, hz⟩ := uzz32_M hF _ hm
  have hlt := Spec.zigzag_lt32 (inI32_toInt x)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Spec.unzigzag_zigzag] at hz
  rw [ho, BitVec.toInt_inj.mp hz]

/-- **D for zigzag i64**: on `zigzag x`, `zigzagToLong` returns `x`. -/
theorem uzz64_D {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (x : I64) {o : Outcome}
    (hm : MExec P uzz64Ref [.ref p, .long (BitVec.ofNat 64 (Spec.zigzag x.toInt))] σ o) :
    o = .normal (some (.long x)) σ := by
  obtain ⟨z, ho, hz⟩ := uzz64_M hF _ hm
  have hlt := Spec.zigzag_lt64 (inI64_toInt x)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Spec.unzigzag_zigzag] at hz
  rw [ho, BitVec.toInt_inj.mp hz]

end EquivLean.Demo.Thrift.Java

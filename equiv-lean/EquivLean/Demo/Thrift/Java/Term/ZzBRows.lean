-- Termination package by JimpleLean's session: TermT4/ZzBRows.lean (sha256 2e4456d5881a6a62...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.ZzBTotal

/-!
# Thrift → Java (T4): the zigzag theorems (E, D, M), total

Each E/D/M theorem of `ZzP.lean` with termination: the zigzag method terminates on the theorem's
premises, and every run ends as the theorem states. No premise (no call, the contract table is empty).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- **E for zigzag i32, total.** -/
theorem zz32_E_total {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (n : I32) :
    (∃ o, MExec P zz32Ref [.ref p, .int n] σ o) ∧ ∀ o, MExec P zz32Ref [.ref p, .int n] σ o →
    ∃ z : I32, o = .normal (some (.int z)) σ ∧ z.toNat = Spec.zigzag n.toInt :=
  ⟨(zz32_term hF [.ref p, .int n] σ ⟨p, n, rfl⟩).run, fun _ hm => zz32_E hF n hm⟩

/-- **D for zigzag i32, total.** -/
theorem uzz32_D_total {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (x : I32) :
    (∃ o, MExec P uzz32Ref [.ref p, .int (BitVec.ofNat 32 (Spec.zigzag x.toInt))] σ o) ∧
    ∀ o, MExec P uzz32Ref [.ref p, .int (BitVec.ofNat 32 (Spec.zigzag x.toInt))] σ o →
    o = .normal (some (.int x)) σ :=
  ⟨(uzz32_term hF [.ref p, .int (BitVec.ofNat 32 (Spec.zigzag x.toInt))] σ ⟨p, _, rfl⟩).run,
    fun _ hm => uzz32_D hF x hm⟩

/-- **M for zigzag i32, total.** -/
theorem uzz32_M_total {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (u : I32) :
    (∃ o, MExec P uzz32Ref [.ref p, .int u] σ o) ∧ ∀ o, MExec P uzz32Ref [.ref p, .int u] σ o →
    ∃ z : I32, o = .normal (some (.int z)) σ ∧ z.toInt = Spec.unzigzag u.toNat :=
  ⟨(uzz32_term hF [.ref p, .int u] σ ⟨p, u, rfl⟩).run, fun _ hm => uzz32_M hF u hm⟩

/-- **E for zigzag i64, total.** -/
theorem zz64_E_total {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (n : I64) :
    (∃ o, MExec P zz64Ref [.ref p, .long n] σ o) ∧ ∀ o, MExec P zz64Ref [.ref p, .long n] σ o →
    ∃ z : I64, o = .normal (some (.long z)) σ ∧ z.toNat = Spec.zigzag n.toInt :=
  ⟨(zz64_term hF [.ref p, .long n] σ ⟨p, n, rfl⟩).run, fun _ hm => zz64_E hF n hm⟩

/-- **D for zigzag i64, total.** -/
theorem uzz64_D_total {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (x : I64) :
    (∃ o, MExec P uzz64Ref [.ref p, .long (BitVec.ofNat 64 (Spec.zigzag x.toInt))] σ o) ∧
    ∀ o, MExec P uzz64Ref [.ref p, .long (BitVec.ofNat 64 (Spec.zigzag x.toInt))] σ o →
    o = .normal (some (.long x)) σ :=
  ⟨(uzz64_term hF [.ref p, .long (BitVec.ofNat 64 (Spec.zigzag x.toInt))] σ ⟨p, _, rfl⟩).run,
    fun _ hm => uzz64_D hF x hm⟩

/-- **M for zigzag i64, total.** -/
theorem uzz64_M_total {P : Program} (hF : Contains P [cpC]) {σ : State} {p : Addr} (u : I64) :
    (∃ o, MExec P uzz64Ref [.ref p, .long u] σ o) ∧ ∀ o, MExec P uzz64Ref [.ref p, .long u] σ o →
    ∃ z : I64, o = .normal (some (.long z)) σ ∧ z.toInt = Spec.unzigzag u.toNat :=
  ⟨(uzz64_term hF [.ref p, .long u] σ ⟨p, u, rfl⟩).run, fun _ hm => uzz64_M hF u hm⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.zz32_E_total
#print axioms EquivLean.Demo.Thrift.Java.uzz32_D_total
#print axioms EquivLean.Demo.Thrift.Java.uzz32_M_total
#print axioms EquivLean.Demo.Thrift.Java.zz64_E_total
#print axioms EquivLean.Demo.Thrift.Java.uzz64_D_total
#print axioms EquivLean.Demo.Thrift.Java.uzz64_M_total

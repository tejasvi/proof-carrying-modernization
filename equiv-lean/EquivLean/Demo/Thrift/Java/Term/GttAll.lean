-- Termination package by JimpleLean's session: TermT4/GttAll.lean (sha256 e27d2cf132c9e39e...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.FhR
import EquivLean.Demo.Thrift.Java.RlbD
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4): `getTType(byte)` on every nibble, partial and total

`gtt_body` covers the nibbles with a TType: its precondition excludes 14 and 15. Here the precondition
is only the shape of the arguments and the initialized `TProtocolException` class, so the nibbles 14 and 15
are covered too: `getTType` throws a new `TProtocolException` (`gttE`), its message built by string
concatenation (`StringBuilder`, through the same models as `checkContainerReadLength`). Same postcondition
as `gttSpec`; new names only.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- `getTType(b)` for every byte `b`. -/
def gttSpecAll : Spec := Spec.of
  (fun args σ => ∃ (p : Addr) (b : I32), args = [.ref p, .int b] ∧ σ.initOf tpeCls = .done)
  gttN gttE

/-- The nibbles 14 and 15 have no TType. -/
theorem ttype_none_of_ge14 {n : Nat} (h1 : 14 ≤ n % 16) : Spec.ttypeOfCompact (n % 16) = none := by
  have h2 : n % 16 < 16 := Nat.mod_lt _ (by decide)
  have : n % 16 = 14 ∨ n % 16 = 15 := by omega
  rcases this with h | h <;> rw [h] <;> rfl

/-- The nibbles 14 and 15: the new `TProtocolException`. -/
theorem gtt_exc {σ0 σ : State} {p : Addr} {w : I32} {F : List (FieldKey × Value)}
    (hcase : 14 ≤ ((w.toNat : Int) % 16).toNat) (hlt : σ0.next < σ.next) :
    gttE [.ref p, .int w] σ0 σ0.next (σ.setObj σ0.next (.plain tpeCls F)) := by
  unfold gttE
  intro p' w' he
  simp only [List.cons.injEq, Value.ref.injEq, Value.int.injEq, and_true] at he
  obtain ⟨-, rfl⟩ := he
  refine ⟨?_, F, setObj_heap_self hlt⟩
  have h : w.toNat % 16 = 14 ∨ w.toNat % 16 = 15 := by omega
  rcases h with h | h <;> rw [h] <;> rfl

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem gttAll_body : BodyVCP (Contains · [cpC, tpeC, teC]) (fun _ => Contracts.env []) 3 gttRef
    (fun _ => gttSpecAll) [] 100 := by
  jverify_body [Contains, gttSpecAll, instanceFields_tpe, ctorCall_exc_str, instanceFields_sb, ctorCall_sb,
    tpeCls, and15_toInt, and15_toNat, bmod_and15]
  all_goals first
    | exact gtt_ok ‹_› rfl
    | (refine gtt_exc ‹_› ?_
       simp only [State.next_setObj, State.next_alloc]
       exact lt_add4 _)

theorem gttAll_sat {P : Program} (hF : Contains P [cpC, tpeC, teC]) : Sat P gttRef gttSpecAll :=
  BodyVCP.sat gttAll_body hF (fun sig S h => by simp [Contracts.env, List.lookup] at h)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem gttAll_thin : ThinVCPX (Contains · [cpC, tpeC, teC]) (fun _ => Contracts.env []) (fun _ => noX) 3
    gttRef (fun _ => gttSpecAll) [] (fun _ _ _ _ _ => 0) 100 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ (fun _ _ _ _ h => nomatch h)
  intro args σ0 hpre
  try dsimp only
  jvc_body [Contains, gttSpecAll, instanceFields_tpe, ctorCall_exc_str, instanceFields_sb, ctorCall_sb,
    tpeCls, and15_toInt, and15_toNat, bmod_and15, noX]
  all_goals first | assumption | skip

/-- **`getTType(byte)` terminates on every byte.** -/
theorem gttAll_term {P : Program} (hF : Contains P [cpC, tpeC, teC]) :
    ∀ args σ, gttSpecAll.pre args σ → MTerm P gttRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1)
    (Valid.strengthen noX (fun _ _ h => by simp [Contracts.env, List.lookup] at h))
    (SpecEnv.strengthen_term (fun _ _ h => by simp [Contracts.env, List.lookup] at h) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide)) (gttAll_body P hF)
      (gttAll_thin P hF))

/-- **`getTType(byte)` on every byte, total correctness**: the TType of a known nibble, a
    `TProtocolException` for the nibbles 14 and 15. -/
theorem gttAll_total {P : Program} (hF : Contains P [cpC, tpeC, teC]) :
    ∀ args σ, gttSpecAll.pre args σ →
      (∃ o, MExec P gttRef args σ o) ∧ ∀ o, MExec P gttRef args σ o → gttSpecAll.post args σ o :=
  fun args σ hpre => ⟨(gttAll_term hF args σ hpre).run, fun o ho => gttAll_sat hF args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.gttAll_total

import EquivLean.Demo.Jimple.Cbact04c.JavaRunLoop
import EquivLean.Demo.Jimple.Cbact04c.JavaRunCalls

/-!
# CBACT04C in Java: `run` computes `jRun`

`run_vc` collects the verification conditions of `run` (entry path and the cut points 12, 21,
28, 29, 33 of `Cbact04c/JavaRunDefs.lean`); the callees are answered by their contracts `callees`
(valid by `callees_valid`, `Cbact04c/JavaCallees.lean`) and the `Result` constructor is inlined.
`run_sat` is the contract `runSpec` of `Cbact04c/Model.lean`: every terminating execution of
`run(cats, accounts, discs)` returns a `Result` holding the rewrites and the transaction count
of `jRun acctOf rateOf cs`.
-/

open Jimple

namespace EquivLean.Demo.Cbact04c.Java

/- The verification conditions are applied as they are stated: `bodyWP` must not be unfolded
(and evaluated) when they are matched against `MethodVC`. -/
attribute [local irreducible] bodyWP

theorem run_isStatic : runMRef.decl.mods.isStatic = true := rfl

theorem run_vc (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) :
    MethodVC Gen.prog callees.env 1 runMRef (runSpecG ca aa da acctOf rateOf cs)
      (runInv ca aa da acctOf rateOf cs) 60 := by
  refine ⟨runBody, rfl, ?_⟩
  intro args σ0 hpre
  have hargs : args = [.ref ca, .ref aa, .ref da] := hpre.1
  subst hargs
  refine ⟨?_, ?_⟩
  · have hl : ((runInv ca aa da acctOf rateOf cs).inst [.ref ca, .ref aa, .ref da] σ0).lookup 0 =
        none := rfl
    have h := run_seg0 ca aa da acctOf rateOf cs σ0 hpre
    unfold RunWP at h
    simp only [hl, run_isStatic]
    exact h
  · intro p hp fr σ hJ
    simp only [runInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · have h := run_seg12 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg21 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg28 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg29 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg33 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h

/-- `run` against the contract with fixed ghost values. -/
theorem run_satG (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) : Sat Gen.prog runMRef (runSpecG ca aa da acctOf rateOf cs) :=
  MethodVC.sat_of_valid callees_valid (run_vc ca aa da acctOf rateOf cs)

end EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c

/-- **`run` computes `jRun`**: the contract `runSpec` of `Cbact04c/Model.lean`. -/
theorem run_sat :
    Sat Gen.prog Gen.Cbact04c.«run(Cbact04c$Cat[],Cbact04c$Account[],Cbact04c$Disc[])».ref
      runSpec := by
  intro args σ o hpre hm
  obtain ⟨ca, aa, da, acctOf, rateOf, cs, rfl, hrun⟩ := hpre
  have h0 := Java.run_satG ca aa da acctOf rateOf cs _ σ o ⟨rfl, hrun⟩ hm
  cases o with
  | normal r σ' =>
    intro ca' aa' da' acctOf' rateOf' cs' hargs hrun'
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl⟩ := hargs
    exact Java.run_satG ca aa da acctOf' rateOf' cs' _ σ _ ⟨rfl, hrun'⟩ hm
  | exc e σ' => exact h0
  | wrong msg => exact h0

end EquivLean.Demo.Cbact04c

#print axioms EquivLean.Demo.Cbact04c.Java.run_vc
#print axioms EquivLean.Demo.Cbact04c.Java.run_satG
#print axioms EquivLean.Demo.Cbact04c.run_sat

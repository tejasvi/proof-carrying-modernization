import EquivLean.Demo.Jimple.Cbact04c.Fixed.JavaRunLoop
import EquivLean.Demo.Jimple.Cbact04c.Fixed.JavaRunCalls
import EquivLean.Demo.Jimple.Cbact04c.Fixed.JavaRunStep
import EquivLean.Demo.Jimple.Cbact04c.Fixed.JavaRunLast

/-!
# CBACT04C in Java, the fixed port: `run` computes `jRunFix`

`run_vc` collects the verification conditions of `Cbact04cFixed.run` (entry path and the cut points
13, 22, 30, 31, 35, 48 of `Cbact04c/Fixed/JavaRunDefs.lean`); the callees are answered by their contracts
`callees` (valid by `callees_valid`, `Cbact04c/Fixed/JavaCallees.lean`) and the `Result` constructor is
inlined. `runFix_sat` is the contract `runFixSpec` of `Cbact04c/Fixed/Model.lean`: every terminating
execution of `run(cats, accounts, discs)` returns a `Result` holding the rewrites `jRunFix` (every
account posted, the last one too) and the transaction count of `jRun acctOf rateOf cs`.
-/

open Jimple EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c.JavaF

/- The verification conditions are applied as they are stated: `bodyWP` must not be unfolded
(and evaluated) when they are matched against `MethodVC`. -/
attribute [local irreducible] bodyWP

theorem run_isStatic : runMRef.decl.mods.isStatic = true := rfl

theorem run_vc (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) :
    MethodVC GenF.prog callees.env 1 runMRef (runSpecG ca aa da acctOf rateOf cs)
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
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · have h := run_seg13 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg22 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg30 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg31 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg35 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h
    · have h := run_seg48 ca aa da acctOf rateOf cs σ0 fr σ hpre hJ
      unfold RunWP at h
      exact h

/-- `run` of the fixed port against the contract with fixed ghost values. -/
theorem run_satG (ca aa da : Addr) (acctOf : I64 → JAcct) (rateOf : JStr → JStr → I32 → I64)
    (cs : List JCat) : Sat GenF.prog runMRef (runSpecG ca aa da acctOf rateOf cs) :=
  MethodVC.sat_of_valid callees_valid (run_vc ca aa da acctOf rateOf cs)

end EquivLean.Demo.Cbact04c.JavaF

namespace EquivLean.Demo.Cbact04c

/-- **The fixed port computes `jRunFix`**: the contract `runFixSpec` of `Cbact04c/Fixed/Model.lean`. -/
theorem runFix_sat :
    Sat GenF.prog
      GenF.Cbact04cFixed.«run(Cbact04cFixed$Cat[],Cbact04cFixed$Account[],Cbact04cFixed$Disc[])».ref
      runFixSpec := by
  intro args σ o hpre hm
  obtain ⟨ca, aa, da, acctOf, rateOf, cs, rfl, hrun⟩ := hpre
  have h0 := JavaF.run_satG ca aa da acctOf rateOf cs _ σ o ⟨rfl, hrun⟩ hm
  cases o with
  | normal r σ' =>
    intro ca' aa' da' acctOf' rateOf' cs' hargs hrun'
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl⟩ := hargs
    exact JavaF.run_satG ca aa da acctOf' rateOf' cs' _ σ _ ⟨rfl, hrun'⟩ hm
  | exc e σ' => exact h0
  | wrong msg => exact h0

end EquivLean.Demo.Cbact04c

#print axioms EquivLean.Demo.Cbact04c.JavaF.run_vc
#print axioms EquivLean.Demo.Cbact04c.JavaF.run_satG
#print axioms EquivLean.Demo.Cbact04c.runFix_sat

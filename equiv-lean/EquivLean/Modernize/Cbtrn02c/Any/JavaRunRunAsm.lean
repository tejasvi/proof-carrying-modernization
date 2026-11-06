import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg0X
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg12X
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg22X
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg35X
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg44X
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSeg48X
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunL65c
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunL75
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunL83
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVt4
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM1v

/-!
# CBTRN02C → Java: `run`'s verification conditions on any input, assembled from the segments

`run_satG`: for fixed inputs `g`, `run` satisfies `runSpecGX g` (the outputs of `Model.runX`).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- The cut points of `run`. -/
def runInvX (g : G) : Invariants :=
  [(12, J12 g), (22, J22 g), (35, J35 g), (44, J44 g), (48, J48 g), (65, L65X g), (75, L75X g),
   (83, J83X g)]

theorem runInvX_lookup_none (g : G) (args : List Value) (σ0 : State) (k : Nat)
    (h : k ∉ [12, 22, 35, 44, 48, 65, 75, 83]) : ((runInvX g).inst args σ0).lookup k = none := by
  apply lookup_none_of
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [runInvX, Invariants.inst, List.map, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨fun e => h1 e.symm, fun e => h2 e.symm, fun e => h3 e.symm, fun e => h4 e.symm,
    fun e => h5 e.symm, fun e => h6 e.symm, fun e => h7 e.symm, fun e => h8 e.symm⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem run_vcX (g : G) :
    MethodVC Gen.prog runCX.env 1 Any.Java.runRef (runSpecGX g) (runInvX g) 60 := by
  refine ⟨runBodyT, rfl, ?_⟩
  intro args σ0 hpre
  have hpre0 := hpre
  obtain ⟨rfl, -, -⟩ := hpre0
  have hn : ∀ k, k ∉ [12, 22, 35, 44, 48, 65, 75, 83] →
      ((runInvX g).inst g.args σ0).lookup k = none :=
    fun k h => runInvX_lookup_none g g.args σ0 k h
  refine ⟨?_, ?_⟩
  · have h0 : ((runInvX g).inst g.args σ0).lookup 0 = none := rfl
    simp only [h0]
    dsimp only [jground]
    rw [← RunWPcX_eq]
    exact run_seg0 g σ0 _ hpre
      (hn 1 (by decide)) (hn 2 (by decide)) (hn 3 (by decide)) (hn 4 (by decide))
      (hn 5 (by decide)) (hn 6 (by decide)) (hn 7 (by decide)) (hn 8 (by decide))
      (hn 9 (by decide)) (hn 10 (by decide)) (hn 11 (by decide)) rfl
  · intro p hp fr σ hI
    rw [← RunWPcX_eq]
    simp only [runInvX, Invariants.inst, List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact run_seg12 g σ0 fr σ _ hpre hI
        (hn 13 (by decide)) (hn 14 (by decide)) (hn 15 (by decide)) (hn 16 (by decide))
        (hn 17 (by decide)) (hn 18 (by decide)) (hn 19 (by decide)) (hn 20 (by decide))
        (hn 21 (by decide)) rfl rfl
    · exact run_seg22 g σ0 fr σ _ hpre hI
        (hn 23 (by decide)) (hn 24 (by decide)) (hn 25 (by decide)) (hn 26 (by decide))
        (hn 27 (by decide)) (hn 28 (by decide)) (hn 29 (by decide)) (hn 30 (by decide))
        (hn 31 (by decide)) (hn 32 (by decide)) (hn 33 (by decide)) (hn 34 (by decide)) rfl rfl
    · exact run_seg35 g σ0 fr σ _ hpre hI
        (hn 36 (by decide)) (hn 37 (by decide)) (hn 38 (by decide)) (hn 39 (by decide))
        (hn 40 (by decide)) (hn 41 (by decide)) (hn 42 (by decide)) (hn 43 (by decide)) rfl
    · exact run_seg44 g σ0 fr σ _ hpre hI
        (hn 45 (by decide)) (hn 46 (by decide)) (hn 47 (by decide)) rfl
    · exact run_seg48 g σ0 fr σ _ hpre hI
        (hn 49 (by decide)) (hn 50 (by decide)) (hn 51 (by decide)) (hn 52 (by decide))
        (hn 53 (by decide)) (hn 54 (by decide)) (hn 55 (by decide)) (hn 56 (by decide))
        (hn 57 (by decide)) (hn 58 (by decide)) (hn 59 (by decide)) (hn 60 (by decide))
        (hn 61 (by decide)) (hn 62 (by decide)) (hn 63 (by decide)) (hn 64 (by decide)) rfl
    · exact run_seg65 g σ0 _ fr σ hpre hI
        (fun k h1 h2 => hn k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)) rfl rfl rfl
    · exact run_seg75 g σ0 _ fr σ hpre hI
        (fun k h1 h2 => hn k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega)) rfl
    · exact run_seg83 g σ0 _ fr σ hpre hI
        (fun k h1 h2 => hn k (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; omega))

/-- The contracts `run` calls hold. -/
theorem runCX_valid : Valid Gen.prog runCX.env := Contracts.valid_of_ok (by
  intro p hp
  simp only [runCX, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact copyAccountF_ok
  · exact copyTcatF_ok
  · exact spaces_ok
  · exact ctorXR_ok
  · exact ctorAC_ok
  · exact ctorTC_ok
  · exact ctorTR_ok
  · exact padNum_ok
  · exact validateTran_ok
  · exact writeReject_ok
  · exact postTransaction_ok)

/-- **`run` on fixed inputs**: the outputs of `Model.runX`. -/
theorem run_satG (g : G) : Sat Gen.prog Any.Java.runRef (runSpecGX g) :=
  MethodVC.sat_of_valid runCX_valid (run_vcX g)

end EquivLean.Modernize.Cbtrn02c.Java

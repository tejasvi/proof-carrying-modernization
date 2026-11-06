import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM4
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunH3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSigs

/-!
# CBTRN02C → Java: `updateTcatbal`'s verification conditions, assembled from the segments
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem lookup_none_of {β : Type} : ∀ (l : List (Nat × β)) (k : Nat), (∀ p ∈ l, p.1 ≠ k) →
    l.lookup k = none
  | [], _, _ => rfl
  | (a, b) :: l, k, h => by
    have hne : k ≠ a := fun e => h (a, b) (by simp) e.symm
    have hb : (k == a) = false := by simp [hne]
    simp only [List.lookup, hb]
    exact lookup_none_of l k (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem utInv_lookup_none (args : List Value) (σ0 : State) (k : Nat) (h1 : k ≠ 21) (h2 : k ≠ 41)
    (h3 : k ≠ 59) : (utInv.inst args σ0).lookup k = none := by
  apply lookup_none_of
  simp only [utInv, Invariants.inst, List.map, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨fun e => h1 e.symm, fun e => h2 e.symm, fun e => h3 e.symm⟩

/-- `UtWPc` is the symbolic execution against `updateTcatbalSpec`'s postcondition (stated once,
with every argument abstract: instances are then rewritten, never unfolded). -/
theorem UtWPc_eq (args : List Value) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) :
    UtWPc args σ0 cuts pc fr σ = bodyWP Gen.prog (callWP Gen.prog utCallees.env 0) utBody cuts
      (updateTcatbalSpec.post args σ0) 80 pc fr σ := by
  unfold UtWPc utPost
  rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem updateTcatbal_vc :
    MethodVC Gen.prog utCallees.env 0 updateTcatbalRef updateTcatbalSpec utInv 80 := by
  refine ⟨utBody, rfl, ?_⟩
  intro args σ0 hpre
  obtain ⟨r, d, wX, wC, lC, rfl, hP⟩ := hpre
  have hnone : ∀ k, k ≠ 21 → k ≠ 41 → k ≠ 59 →
      (utInv.inst [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0).lookup k = none :=
    fun k h1 h2 h3 => utInv_lookup_none _ σ0 k h1 h2 h3
  refine ⟨?_, ?_⟩
  · have h0 : (utInv.inst [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0).lookup 0 = none := rfl
    simp only [h0]
    dsimp only [jground]
    rw [← UtWPc_eq]
    rcases Int.lt_or_le (utIdx σ0 d wX lC) 0 with hn | hp
    · exact ut_entry_neg r d wX wC lC σ0 _ hP hn
        (hnone 1 (by omega) (by omega) (by omega)) (hnone 2 (by omega) (by omega) (by omega))
        (hnone 3 (by omega) (by omega) (by omega)) (hnone 4 (by omega) (by omega) (by omega))
        (hnone 5 (by omega) (by omega) (by omega)) (hnone 6 (by omega) (by omega) (by omega))
        (hnone 7 (by omega) (by omega) (by omega)) (hnone 8 (by omega) (by omega) (by omega))
        (hnone 9 (by omega) (by omega) (by omega)) (hnone 10 (by omega) (by omega) (by omega))
        (hnone 11 (by omega) (by omega) (by omega)) (hnone 12 (by omega) (by omega) (by omega))
        (hnone 13 (by omega) (by omega) (by omega)) (hnone 14 (by omega) (by omega) (by omega))
        (hnone 15 (by omega) (by omega) (by omega)) (hnone 16 (by omega) (by omega) (by omega))
        (hnone 17 (by omega) (by omega) (by omega)) rfl
    · exact ut_entry_pos r d wX wC lC σ0 _ hP hp
        (hnone 1 (by omega) (by omega) (by omega)) (hnone 2 (by omega) (by omega) (by omega))
        (hnone 3 (by omega) (by omega) (by omega)) (hnone 4 (by omega) (by omega) (by omega))
        (hnone 5 (by omega) (by omega) (by omega)) (hnone 6 (by omega) (by omega) (by omega))
        (hnone 7 (by omega) (by omega) (by omega)) (hnone 8 (by omega) (by omega) (by omega))
        (hnone 9 (by omega) (by omega) (by omega)) (hnone 10 (by omega) (by omega) (by omega))
        (hnone 18 (by omega) (by omega) (by omega)) (hnone 19 (by omega) (by omega) (by omega))
        (hnone 20 (by omega) (by omega) (by omega)) rfl
  · intro p hp fr σ hI
    rw [← UtWPc_eq]
    simp only [utInv, Invariants.inst, List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rcases Int.lt_or_le (utIdx σ0 d wX lC) 0 with hn | hp
      · exact ut_seg21_neg r d wX wC lC σ0 _ fr σ hP hn hI
          (fun k h1 h2 => hnone k (by omega) (by omega) (by omega)) rfl
      · exact ut_seg21_pos r d wX wC lC σ0 _ fr σ hP hp hI
          (fun k h1 h2 => hnone k (by omega) (by omega) (by omega)) rfl
    · have hn := (hI r d wX wC lC rfl hP).1
      exact ut_seg41 r d wX wC lC σ0 _ fr σ hP hn hI
        (fun k h1 h2 => hnone k (by omega) (by omega) (by omega)) rfl
    · have hp := (hI r d wX wC lC rfl hP).1
      exact ut_seg59 r d wX wC lC σ0 _ fr σ hP hp hI
        (fun k h1 h2 => hnone k (by omega) (by omega) (by omega))

theorem updateTcatbal_sat : Sat Gen.prog updateTcatbalRef updateTcatbalSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [utCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact findTcatbalF_ok
    · exact padNum_ok
    · exact assignTcatF_ok
    · exact spaces_ok
    · exact copyTcatF_ok
    · exact abend_ok)) updateTcatbal_vc

set_option maxHeartbeats 0 in
theorem updateTcatbal_ok : ContractOK Gen.prog updateTcatbalSig updateTcatbalSpec := by
  jcontract_ok [updateTcatbal_sat]

end EquivLean.Modernize.Cbtrn02c.Java

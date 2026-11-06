import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2xb2
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2xd
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSigs

/-!
# CBTRN02C → Java: `abend` (status 22) and `writeTransaction` (any input) satisfy their contracts
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem abend22_sat : Sat Gen.prog abendRef abendSpec22 :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (T := []) (by intro p hp; cases hp)) abend22i_vc

set_option maxHeartbeats 0 in
theorem abend22_ok : ContractOK Gen.prog abendSig abendSpec22 := by jcontract_ok [abend22_sat]

theorem WtWP_eq (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) :
    WtWP args σ0 pc fr σ = bodyWP Gen.prog (callWP Gen.prog wtCalleesX.env 0) wtBody []
      (writeTransactionSpecX.post args σ0) 40 pc fr σ := by
  unfold WtWP wtPostX
  rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem writeTransactionX_vc :
    MethodVC Gen.prog wtCalleesX.env 0 writeTransactionRef writeTransactionSpecX [] 40 := by
  refine ⟨wtBody, rfl, ?_⟩
  intro args σ0 hpre
  have hpre' := hpre
  obtain ⟨r, wT, lK, -, -, -, -, -, -, -, -, -, -, -, -, rfl, -⟩ := hpre'
  refine ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩
  have h0 : Invariants.inst [] [.ref r, .ref wT, .ref lK] σ0 = [] := rfl
  simp only [h0, List.lookup]
  dsimp only [jground]
  rw [← WtWP_eq]
  exact wt_entry r wT lK σ0 hpre

theorem writeTransactionX_sat : Sat Gen.prog writeTransactionRef writeTransactionSpecX :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [wtCalleesX, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact findKeyF_ok
    · exact copyTranF_ok
    · exact abend22_ok)) writeTransactionX_vc

set_option maxHeartbeats 0 in
theorem writeTransactionX_ok : ContractOK Gen.prog writeTransactionSig writeTransactionSpecX := by
  jcontract_ok [writeTransactionX_sat]

end EquivLean.Modernize.Cbtrn02c.Java

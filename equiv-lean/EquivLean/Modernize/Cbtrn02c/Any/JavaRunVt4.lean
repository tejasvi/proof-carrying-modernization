import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVt1
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVt2
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunVt3
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSigs
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM4v

/-!
# CBTRN02C → Java: `validateTran`'s verification conditions, assembled from the segments
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem vtInv_lookup_none (args : List Value) (σ0 : State) (k : Nat) (h1 : k ≠ 11) (h2 : k ≠ 17) :
    (vtInv.inst args σ0).lookup k = none := by
  apply lookup_none_of
  simp only [vtInv, Invariants.inst, List.map, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨fun e => h1 e.symm, fun e => h2 e.symm⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem validateTran_vc :
    MethodVC Gen.prog vtCallees.env 0 validateTranRef validateTranSpec vtInv 80 := by
  refine ⟨vtBodyC, rfl, ?_⟩
  intro args σ0 hpre
  have hpre0 := hpre
  obtain ⟨d, xA, aD, wX, wA, -, -, -, -, -, rfl, -⟩ := hpre0
  have hn : ∀ k, k ≠ 11 → k ≠ 17 →
      (vtInv.inst [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0).lookup k = none :=
    fun k h1 h2 => vtInv_lookup_none _ σ0 k h1 h2
  refine ⟨?_, ?_⟩
  · have h0 : (vtInv.inst [.ref d, .ref xA, .ref aD, .ref wX, .ref wA] σ0).lookup 0 = none := rfl
    simp only [h0]
    dsimp only [jground]
    rw [← VtWPc_eq]
    exact vt_seg0 d xA aD wX wA σ0 _ hpre (fun k h1 h2 => hn k (by omega) (by omega)) rfl
  · intro p hp fr σ hI
    rw [← VtWPc_eq]
    simp only [vtInv, Invariants.inst, List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact vt_seg11 d xA aD wX wA σ0 _ fr σ hpre hI
        (fun k h1 h2 => hn k (by omega) (by omega)) rfl
    · exact vt_seg17 d xA aD wX wA σ0 _ fr σ hpre hI (fun k h1 h2 => hn k (by omega) (by omega))

theorem validateTran_sat : Sat Gen.prog validateTranRef validateTranSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [vtCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact findXrefF_ok
    · exact findAccountF_ok
    · exact assignXrefF_ok
    · exact assignAccountF_ok
    · exact compareEbcdicF_ok)) validateTran_vc

set_option maxHeartbeats 0 in
theorem validateTran_ok : ContractOK Gen.prog validateTranSig validateTranSpec := by
  jcontract_ok [validateTran_sat]

end EquivLean.Modernize.Cbtrn02c.Java

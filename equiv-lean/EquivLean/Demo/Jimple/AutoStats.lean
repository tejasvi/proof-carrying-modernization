import EquivLean.Demo.Jimple.PrDiffStats
import EquivLean.Bridge.Jimple.Auto

/-!
# `Stats.total` again, with the automatic product

The Java PR diff of `Demo/Jimple/PrDiffStats.lean` (`Stats.total`: an index loop changed to an
enhanced `for`, real javac + Soot output), proved twice more with the tactics of
`Bridge/Jimple/Auto.lean`:

* **pairs and couplings written, nothing else** (`stats_vc`, `stats_vc_rev`): the `ProdVC`
  statements of `PrDiffStats` with its pairs and couplings (`pairs`, `J0`, `JL`; `pairsR`, `JLr`),
  each by one call `jprod_vc [IntArr]`, in place of the three source lemmas (`src_entry`,
  `src_iter`, `src_exit`) and the product proof of each direction; `stats_equiv_given` assembles
  them as `PrDiffStats` does;
* **nothing written** (`stats_sim`, `stats_sim_rev`, `stats_equiv`): the statements of
  `PrDiffStats.stats_sim`, `stats_sim_rev`, `stats_equiv`, each by one call `equiv_jimple`.  The
  loop heads (statement 4 of the new body, 3 of the old one) are paired and the couplings are
  generated from runs of both methods; for new ⊑ old the loop coupling is, in Soot's numbering
  (new: array 0, length 1, sum 3, index 4; old: array 0, sum 2, index 3),

      ∃ t xs, σ₁.heap a = some (.array t xs) ∧ σ₁ = σ₂ ∧ σ₁ = σ ∧
        fr₁.get 0 = some (.ref a) ∧ fr₁.get 1 = some (.int (BitVec.ofNat 32 xs.length)) ∧
        fr₂.get 0 = some (.ref a) ∧ (∃ v, fr₁.get 3 = some (.int v) ∧ fr₂.get 2 = some (.int v)) ∧
        ∃ v, fr₁.get 4 = some (.int v) ∧ fr₂.get 3 = some (.int v) ∧ 0 ≤ v.toInt ∧ v.toInt ≤ xs.length

  (the hand-written `JL` with the heap pinned to the entry state `σ`, about which `IntArr σ a xs`
  is known).
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Gen

namespace EquivLean.Demo.AutoStats
open EquivLean.Demo.PrDiffStats (bOld bNew IntArr J0 JL pairs JLr pairsR)

/-! ## Pairs and couplings written -/

set_option maxRecDepth 30000 in
/-- `PrDiffStats.stats_vc` (new ⊑ old) from its pairs and couplings alone. -/
theorem stats_vc : ProdVC StatsNew.prog bNew StatsOld.prog bOld pairs (· = ·) 0 20 8 := by
  jprod_vc [IntArr]

set_option maxRecDepth 30000 in
/-- `PrDiffStats.stats_vc_rev` (old ⊑ new) from its pairs and couplings alone. -/
theorem stats_vc_rev : ProdVC StatsOld.prog bOld StatsNew.prog bNew pairsR (· = ·) 0 20 8 := by
  jprod_vc [IntArr]

/-- The pull request preserves behaviour, from the two products above. -/
theorem stats_equiv_given (a : Addr) (xs : List Value) (σ : State) (h : IntArr σ a xs) :
    Equiv (· = ·)
      (Call.mk StatsNew.prog (mref StatsNew.prog "Stats" "total") [.ref a] σ)
      (Call.mk StatsOld.prog (mref StatsOld.prog "Stats" "total") [.ref a] σ) :=
  ⟨sim_of_prodVC (b₁ := bNew) (b₂ := bOld) rfl rfl stats_vc (J₀ := J0) (by simp [pairs])
      ⟨a, xs, rfl, h, rfl, rfl⟩,
    (sim_of_prodVC (b₁ := bOld) (b₂ := bNew) rfl rfl stats_vc_rev (J₀ := J0) (by simp [pairsR])
      ⟨a, xs, rfl, h, rfl, rfl⟩).mono fun _ _ e => e.symm⟩

/-! ## Nothing written -/

set_option maxRecDepth 30000 in
/-- **new ⊑ old with no pairs or couplings written.** -/
theorem stats_sim (a : Addr) (xs : List Value) (σ : State) (h : IntArr σ a xs) :
    Sim (· = ·)
      (Call.mk StatsNew.prog (mref StatsNew.prog "Stats" "total") [.ref a] σ)
      (Call.mk StatsOld.prog (mref StatsOld.prog "Stats" "total") [.ref a] σ) := by
  equiv_jimple

set_option maxRecDepth 30000 in
/-- **old ⊑ new with no pairs or couplings written.** -/
theorem stats_sim_rev (a : Addr) (xs : List Value) (σ : State) (h : IntArr σ a xs) :
    Sim (· = ·)
      (Call.mk StatsOld.prog (mref StatsOld.prog "Stats" "total") [.ref a] σ)
      (Call.mk StatsNew.prog (mref StatsNew.prog "Stats" "total") [.ref a] σ) := by
  equiv_jimple

set_option maxRecDepth 30000 in
/-- **The pull request preserves behaviour, one tactic call**: both directions generated. -/
theorem stats_equiv (a : Addr) (xs : List Value) (σ : State) (h : IntArr σ a xs) :
    Equiv (· = ·)
      (Call.mk StatsNew.prog (mref StatsNew.prog "Stats" "total") [.ref a] σ)
      (Call.mk StatsOld.prog (mref StatsOld.prog "Stats" "total") [.ref a] σ) := by
  equiv_jimple

end EquivLean.Demo.AutoStats

#print axioms EquivLean.Demo.AutoStats.stats_vc
#print axioms EquivLean.Demo.AutoStats.stats_vc_rev
#print axioms EquivLean.Demo.AutoStats.stats_equiv_given
#print axioms EquivLean.Demo.AutoStats.stats_sim
#print axioms EquivLean.Demo.AutoStats.stats_sim_rev
#print axioms EquivLean.Demo.AutoStats.stats_equiv

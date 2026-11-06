/-
  Examples/Caching/TermLink.lean

  Termination at the link step. `Item.price` terminates on the interface contract of `Priced.price`
  (`jterm`), so the interface contract terminates (`ContractTerm`): `jcontract_term` enumerates the
  implementing application classes as `jcontract_ok` does. `Item` selects `Item.price`; the interface
  `Priced` is abstract and drops out. The static `max` needs no enumeration.
-/
import Examples.Caching.Link

open Jimple Examples.Caching

namespace Examples.Caching

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem price_termvc :
    TermVC Whole.prog (fun _ => none) (fun _ => 0) 0 0 HItem.Item.«price()».ref pricedSpec [] 20 := by
  jterm [pricedSpec, ItemAt]

theorem price_term :
    ∀ args σ, pricedSpec.pre args σ → MTerm Whole.prog HItem.Item.«price()».ref args σ :=
  TermVC.mterm (Γ := fun _ => none) (rank := fun _ => 0) (r := 0)
    (fun _ _ h => by simp at h) (fun _ _ h => by simp [SpecEnv.below] at h) price_termvc

/-- **The interface contract terminates**: every implementing class of `Priced` selects a terminating
    method (only `Item`). -/
theorem priced_cterm : ContractTerm Whole.prog pricedPrice pricedSpec := by
  jcontract_term [price_term]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem max_termvc :
    TermVC Whole.prog (fun _ => none) (fun _ => 0) 0 0 BB.Basics.«max(int,int)».ref maxSpec [] 20 := by
  jterm [maxSpec]

theorem max_term :
    ∀ args σ, maxSpec.pre args σ → MTerm Whole.prog BB.Basics.«max(int,int)».ref args σ :=
  TermVC.mterm (Γ := fun _ => none) (rank := fun _ => 0) (r := 0)
    (fun _ _ h => by simp at h) (fun _ _ h => by simp [SpecEnv.below] at h) max_termvc

/-- A static method's contract: no virtual part. -/
theorem max_cterm : ContractTerm Whole.prog BB.Basics.«max(int,int)».ref.sig maxSpec := by
  jcontract_term [max_term]

end Examples.Caching

#print axioms Examples.Caching.priced_cterm
#print axioms Examples.Caching.max_cterm

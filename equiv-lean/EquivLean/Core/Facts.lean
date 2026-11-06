import EquivLean.Core.Sim

/-!
# What `Sim` and `Equiv` mean

Sanity facts that pin down the judgements:

* with equality as the outcome relation, equivalence means the same outcomes wherever either
  side is safe (`Equiv.runs_iff`);
* for `Option`-valued meanings (StrictTS, any `optLoop`), `Equiv (· = ·)` is equality of the
  meanings wherever the source is defined (`Equiv.option_eq`);
* `Sim` against a deterministic safe source is the usual "if the source terminates with `o`,
  the target terminates with an outcome related to `o`" (`Sim.runs_of_runs`).
-/

namespace EquivLean

universe u₁ u₂ v₁ v₂

section
variable {T : Type u₁} {S : Type u₂} {O : Type v₁}
variable [Behaves T O] [Behaves S O]

/-- Equivalent computations have the same outcomes where either is safe. -/
theorem Equiv.runs_iff {t : T} {s : S} (h : Equiv (· = ·) t s) (hs : Safe s) (o : O) :
    Runs t o ↔ Runs s o := by
  have ht : Safe t := (h.1 hs).1
  constructor
  · intro ho
    obtain ⟨o', ho', he⟩ := (h.1 hs).2 o ho
    exact he ▸ ho'
  · intro ho
    obtain ⟨o', ho', he⟩ := (h.2 ht).2 o ho
    exact he ▸ ho'

theorem Equiv.runs_iff' {t : T} {s : S} (h : Equiv (· = ·) t s) (ht : Safe t) (o : O) :
    Runs t o ↔ Runs s o :=
  h.runs_iff (h.safe_iff.1 ht) o

end

/-- For `Option`-valued meanings, equivalence is equality where the source is defined. -/
theorem Equiv.option_eq {α : Type u₁} {t s : Option α} (h : Equiv (· = ·) t s)
    (hs : s.isSome) : t = s := by
  obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.1 hs
  have := (h.runs_iff (s := some v) hs v).2 rfl
  exact this

/-- Simulation of a deterministic safe source with a known outcome. -/
theorem Sim.runs_of_runs {T : Type u₁} {S : Type u₂} {OT : Type v₁} {OS : Type v₂}
    [Behaves T OT] [Behaves S OS] [Behaves.Det S] {R : OT → OS → Prop} {t : T} {s : S}
    (h : Sim R t s) (hs : Safe s) {os : OS} (hos : Runs s os) :
    Safe t ∧ ∀ ot, Runs t ot → R ot os := by
  obtain ⟨ht, hrun⟩ := h hs
  refine ⟨ht, fun ot ho => ?_⟩
  obtain ⟨os', hos', hr⟩ := hrun ot ho
  rwa [Behaves.Det.det s os os' hos hos']


/-! ## Deriving simulations without a product

* `Sim.of_wp_pair`: both programs meet a common functional specification ("meet in the
  middle"); no coupling of the two executions is needed.
* `Equiv.of_sim_of_safe`: one simulation direction plus "the target is safe whenever the
  source is" gives equivalence for a total target and a deterministic source.  Use it to
  prove `Equiv` with the product construction in the direction where both executors run
  comfortably (the source in a hypothesis, the target in the goal).
-/

section
variable {T : Type u₁} {S : Type u₂} {OT : Type v₁} {OS : Type v₂}
variable [Behaves T OT] [Behaves S OS]

theorem Sim.of_wp_pair [Behaves.Total S] {R : OT → OS → Prop} {t : T} {s : S}
    {Qt : OT → Prop} {Qs : OS → Prop} (ht : wp t Qt) (hs : wp s Qs)
    (hR : ∀ ot os, Qt ot → Qs os → R ot os) : Sim R t s := fun _ =>
  let ⟨os, hos, hq⟩ := wp_exists hs
  ⟨ht.1, fun ot ho => ⟨os, hos, hR ot os (ht.2 ot ho) hq⟩⟩

theorem Equiv.of_wp_pair [Behaves.Total T] [Behaves.Total S] {R : OT → OS → Prop} {t : T} {s : S}
    {Qt : OT → Prop} {Qs : OS → Prop} (ht : wp t Qt) (hs : wp s Qs)
    (hR : ∀ ot os, Qt ot → Qs os → R ot os) : Equiv R t s :=
  ⟨Sim.of_wp_pair ht hs hR, Sim.of_wp_pair hs ht fun os ot hs ht => hR ot os ht hs⟩

theorem Equiv.of_sim_of_safe [Behaves.Total T] [Behaves.Det S] {R : OT → OS → Prop} {t : T} {s : S}
    (h : Sim R t s) (hsafe : Safe t → Safe s) : Equiv R t s := by
  refine ⟨h, fun ht => ⟨hsafe ht, fun os hos => ?_⟩⟩
  obtain ⟨_, hrun⟩ := h (hsafe ht)
  obtain ⟨ot, hot⟩ := Behaves.Total.progress t ht
  obtain ⟨os', hos', hr⟩ := hrun ot hot
  exact ⟨ot, hot, Behaves.Det.det s os' os hos' hos ▸ hr⟩

end

end EquivLean

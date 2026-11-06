import EquivLean.Core.Loop

/-!
# Generic relational tactics

These tactics know nothing about any particular encoding.  They build the product program
out of three moves, each backed by a lemma of the core:

* **intro** (`equiv_intro`): a `Sim`/`Equiv`/`FSim`/`EquivOn` goal becomes "source in a
  hypothesis `hs : wp s P`, target in the goal `wp t (fun ot => ∃ os, P os ∧ R ot os)`"
  (`sim_iff_wp`).  Symbolic execution then runs *forward* on the source hypothesis and
  *backward* on the target goal, each with its own encoding's simp sets (bridges extend
  `equiv_exec`).
* **align** (`equiv_loop`, `equiv_cut`): when both sides stop at a loop (or at calls with a
  relational specification), pair them with `wp_loop_rel` / `Sim.wp_cut`.  This yields the
  body obligation (a relational goal for one iteration of each loop), the coupling at entry,
  and the continuation after both loops, which is again a relational goal of the same shape.
* **branch** (`equiv_branch`): split data-dependent branches on both sides.  Each pair of
  paths is a separate goal; pairs whose path conditions contradict each other are closed by
  `equiv_prune` (contradiction, `omega`, `simp_all`), which is how the branches of the two
  programs are aligned without any annotation.

Leaves (`equiv_leaf`) pick the source's outcome from the hypothesis and discharge the
remaining outcome relation with `rfl`, `simp`, `omega`, `bv_decide`, `decide` or `grind`.
-/

namespace EquivLean

open Lean Elab Tactic Meta

/-- Unfold the user-facing statements (`Equiv`, `FSim`, `FEquiv`, `EquivOn`, `⊑`, `≈`) down to
`Sim` goals, introducing inputs and preconditions. -/
syntax (name := equivSplit) "equiv_split" : tactic

macro_rules
  | `(tactic| equiv_split) => `(tactic| (
      try simp only [FSim, FEquiv, EquivOn, Equivalent, Simulates.sim] at *
      try intros
      try (refine ⟨?_, ?_⟩)))

/-- `equiv_intro P hs`: turn a `Sim R t s` goal into `hs : wp s P ⊢ wp t (∃ os, P os ∧ R · os)`. -/
syntax (name := equivIntro) "equiv_intro" (ppSpace ident ppSpace ident)? : tactic

macro_rules
  | `(tactic| equiv_intro) => `(tactic| equiv_intro P hs)
  | `(tactic| equiv_intro $P:ident $hs:ident) =>
    `(tactic| (refine Sim.intro_wp (fun $P $hs => ?_)))

/-- Symbolic execution of both sides: the source hypotheses and the target goal.  Bridges
extend this with `macro_rules` for their encoding (they are tried most-recent first). -/
syntax (name := equivExec) "equiv_exec" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| equiv_exec) => `(tactic| equiv_exec [])
  | `(tactic| equiv_exec [$ts,*]) =>
    `(tactic| (simp only [wp_id, wp_except, wp_some, wp_none, wp_option_bind, pureVal,
        bind, Option.bind, Except.bind, pure, Except.pure, $ts,*] at *))

/-- Close a contradictory goal (a pair of paths that cannot both be taken). -/
syntax (name := equivPrune) "equiv_prune" : tactic

macro_rules
  | `(tactic| equiv_prune) => `(tactic| first
      | contradiction
      | (exfalso; omega)
      | (exfalso; simp_all; done)
      | (exfalso; grind))

/-- Split the next data-dependent branch, in the goal or in a hypothesis. -/
syntax (name := equivBranch) "equiv_branch" : tactic

macro_rules
  | `(tactic| equiv_branch) => `(tactic| first
      | (refine ⟨fun _ => ?_, fun _ => ?_⟩)
      | split
      | (split at *))

/-- Discharge a pure outcome relation. -/
syntax (name := equivClose) "equiv_close" : tactic

macro_rules
  | `(tactic| equiv_close) => `(tactic| first
      | rfl
      | assumption
      | (simp_all; done)
      | omega
      | decide
      | (simp_all; omega)
      | bv_decide
      | grind)

/-- At a leaf: the target finished with `ot`, the source hypothesis says `P os`.  Choose that
source outcome and prove the outcome relation. -/
syntax (name := equivLeaf) "equiv_leaf" : tactic

macro_rules
  | `(tactic| equiv_leaf) => `(tactic| (
      refine ⟨_, ‹_›, ?_⟩
      try equiv_close))

/-- `equiv_cut h`: the next pieces of the two programs are related by `h : Sim R t s` (a
relational specification of two calls, or two loops proved separately).  The goal must have
`t` at its head and a hypothesis must have `s` at its head; the remaining goal is the
continuation. -/
syntax (name := equivCut) "equiv_cut" term : tactic

macro_rules
  | `(tactic| equiv_cut $h) =>
    `(tactic| (refine Sim.wp_cut $h (by assumption) ?_; intro _ _ _ _))

/-- `equiv_loop I (with R)? using h₁, h₂, ht`: pair the loop at the head of the goal (shape
`h₁`) with the loop at the head of a hypothesis (shape `h₂`, termination `ht`), with coupling
invariant `I`; `R` relates the two loops' outcomes when they leave (default: equality).
Goals: `init` (the coupling at entry), `step` (one lockstep iteration, a `Sim` goal on the
two bodies), `post` (the continuation after both loops). -/
syntax (name := equivLoop) "equiv_loop" term (" with " term)? " using " term ", " term ", " term :
  tactic

macro_rules
  | `(tactic| equiv_loop $I using $h₁, $h₂, $ht) =>
    `(tactic| equiv_loop $I with (fun o₁ o₂ => o₁ = o₂) using $h₁, $h₂, $ht)
  | `(tactic| equiv_loop $I with $R using $h₁, $h₂, $ht) =>
    `(tactic| (refine wp_loop_rel (R := $R) $h₁ $h₂ $ht $I (by assumption) ?init ?step ?post))

end EquivLean

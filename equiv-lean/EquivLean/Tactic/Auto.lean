import Lean
import EquivLean.Tactic.Basic

/-!
# Automation for loop bodies and straight-line code

`equiv_cases` splits every `if`/`match` in the goal and in the hypotheses until none is left
(Lean's `splitTarget?`/`splitLocalDecl?`), and drops each pair of paths whose conditions
contradict each other.  On the product of two straight-line programs (or of two loop
bodies) this enumerates exactly the aligned pairs of paths.

`equiv_body defs*` is the standard proof of a lockstep iteration or of two straight-line
programs: introduce the weakest-precondition form, unfold `defs`, execute both sides, split,
prune, and close every leaf.
-/

namespace EquivLean

open Lean Elab Tactic Meta

/-- Split all `if`/`match` expressions in the goal and the hypotheses, recursively. -/
partial def splitAll (g : MVarId) (fuel : Nat := 64) : MetaM (List MVarId) := do
  if fuel = 0 then return [g]
  if let some gs ← (try splitTarget? g catch _ => pure none) then
    return (← gs.mapM (splitAll · (fuel - 1))).flatten
  let lctx := (← g.getDecl).lctx
  for d in lctx do
    if d.isImplementationDetail then continue
    if !(← isProp d.type) then continue
    if let some gs ← (try splitLocalDecl? g d.fvarId catch _ => pure none) then
      return (← gs.mapM (splitAll · (fuel - 1))).flatten
  return [g]

/-- Split every `if`/`match` in the goal and in the hypotheses. -/
elab "equiv_cases" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    out := out ++ (← splitAll g)
  setGoals out

/-- Unfold the one-iteration relation of a lockstep product. -/
syntax (name := equivStepRel) "equiv_steprel" : tactic

macro_rules
  | `(tactic| equiv_steprel) => `(tactic|
      simp only [StepRel, id, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at *)

/-- One lockstep iteration, or two straight-line programs: introduce, unfold `defs`,
execute, split, prune, close the leaves. -/
syntax (name := equivBody) "equiv_body" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| equiv_body) => `(tactic| equiv_body [])
  | `(tactic| equiv_body [$ts,*]) => `(tactic| (
      equiv_intro Q hq
      equiv_exec [$ts,*]
      equiv_cases
      all_goals (first
        | equiv_prune
        | (equiv_exec [$ts,*]
           first
             | equiv_prune
             | (refine ⟨_, ‹_›, ?_⟩
                try simp only [StepRel, id, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
                  $ts,*] at *
                try equiv_close)))))

end EquivLean

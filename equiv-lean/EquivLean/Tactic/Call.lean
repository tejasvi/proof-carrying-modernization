import EquivLean.Tactic.Attr
import EquivLean.Tactic.Basic

namespace EquivLean

open Lean Elab Tactic Meta

/-- Apply `Sim.wp_cut` with the relational specification `lem`: the goal must have the target
call at its head, some hypothesis the source call at its head.  Returns the new goals: the
continuation, then the specification's side conditions. -/
def cutWith (g : MVarId) (lem : Name) : MetaM (Option (List MVarId)) := do
  let s ← saveState
  try
    -- `Sim.wp_cut ?hsim ?hs ?hk` against the goal `wp t K₁`
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``Sim.wp_cut) { allowSynthFailures := true }
    let some ghsim ← gs.findM? (fun x => return (← x.getType).isAppOf ``Sim) | throwError "no Sim goal"
    let some ghs ← gs.findM? (fun x => return (← x.getType).isAppOf ``wp) | throwError "no wp goal"
    let others := gs.filter (fun x => x != ghsim && x != ghs)
    -- the relational specification, without unfolding `Sim`
    let side ← ghsim.apply (← mkConstWithFreshMVarLevels lem)
    -- the source side: a hypothesis `wp s K₂`
    ghs.assumption
    -- instance arguments left open by `apply` are solved by unification above or by synthesis
    let mut rest := []
    for x in others do
      if ← x.isAssigned then continue
      let ty ← instantiateMVars (← x.getType)
      if (← isClass? ty).isSome then
        x.assign (← synthInstance ty)
      else rest := rest ++ [x]
    return some (rest ++ side)
  catch _ =>
    restoreState s
    return none

/-- Use the first applicable `@[equiv_spec]` theorem (or the given ones) at the current pair
of calls.  The new goal is the continuation `∀ ot os, R ot os → K₂ os → K₁ ot`, followed by the
specification's own side conditions. -/
syntax (name := equivCall) "equiv_call" (" [" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| equiv_call) => do
    let g ← getMainGoal
    for lem in ← labelled `equiv_spec do
      if let some gs ← cutWith g lem then
        replaceMainGoal gs
        return
    throwError "equiv_call: no @[equiv_spec] theorem applies"
  | `(tactic| equiv_call [$ids,*]) => do
    let g ← getMainGoal
    for id in ids.getElems do
      if let some gs ← cutWith g id.getId then
        replaceMainGoal gs
        return
    throwError "equiv_call: none of the given specifications applies"

/-- The single entry point.  Bridges add alternatives with `macro_rules`; they are tried most
recent first. -/
syntax (name := equivAuto) "equiv_auto" : tactic

end EquivLean

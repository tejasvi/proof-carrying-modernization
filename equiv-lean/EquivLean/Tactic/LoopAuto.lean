import EquivLean.Tactic.LoopAttr
import EquivLean.Tactic.Basic
import EquivLean.Core.LoopAsync

/-!
# Automatic loop pairing

`equiv_loop_auto I (with R)?` applies the lockstep rule `wp_loop_rel` to the loop at the head
of the goal (the target) and the loop at the head of a hypothesis `wp (L₂ s₂) K₂` (the source),
whatever their encodings: the shapes and the source's termination are found in the
`@[equiv_loop_shape]` / `@[equiv_loop_term]` databases.  The goals left are the same as for
`equiv_loop`: `init` (coupling at entry), `step` (one lockstep iteration, a `Sim` goal on the
two loop bodies), `post` (the continuations after both loops).
-/

namespace EquivLean

open Lean Elab Tactic Meta

/-- Solve `g` (a `LoopShape …` or `LoopShape.Terminates …` goal) with the first lemma of
`lems` that applies with all its arguments fixed by unification. -/
def solveWithFirst (g : MVarId) (lems : Array Name) : MetaM Bool := do
  for lem in lems do
    let s ← saveState
    try
      let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
      let mut ok := true
      for x in gs do
        unless ← x.isAssigned do ok := false
      if ok then return true
      restoreState s
    catch _ => restoreState s
  return false

syntax (name := equivLoopAuto) "equiv_loop_auto" term (" with " term)? : tactic

/-- `equiv_loop_same`: `equiv_loop_auto` with the coupling "the two loops' states are equal"
(the common case of a refactoring that keeps the loop state; no invariant to write). -/
macro "equiv_loop_same" : tactic => `(tactic| equiv_loop_auto (fun s₁ s₂ => s₁ = s₂))

elab_rules : tactic
  | `(tactic| equiv_loop_auto $I $[with $R]?) => withMainContext do
    let g ← getMainGoal
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``wp_loop_rel) { allowSynthFailures := true }
    -- explicit arguments of `wp_loop_rel`, in order: h₁ h₂ ht I hs hI hstep hk
    let tagged ← gs.mapM fun x => return (x, ← x.getTag)
    -- `apply` names the new goals after the binders, under the main goal's tag
    let get (n : Name) : TacticM MVarId := do
      match tagged.find? (fun (_, t) => t == n || t.componentsRev.head? == some n) with
      | some (x, _) => pure x
      | none => throwError "equiv_loop_auto: internal: no goal {n}"
    let gh₁ ← get `h₁; let gh₂ ← get `h₂; let ght ← get `ht
    let gI ← get `I; let ghs ← get `hs
    let ghI ← get `hI; let gstep ← get `hstep; let gk ← get `hk
    -- the source loop: a hypothesis
    ghs.assumption
    -- shapes and termination from the databases
    unless ← solveWithFirst gh₁ (← labelled `equiv_loop_shape) do
      throwError "equiv_loop_auto: no @[equiv_loop_shape] theorem matches {← gh₁.getType}"
    unless ← solveWithFirst gh₂ (← labelled `equiv_loop_shape) do
      throwError "equiv_loop_auto: no @[equiv_loop_shape] theorem matches {← gh₂.getType}"
    unless ← solveWithFirst ght (← labelled `equiv_loop_term) do
      throwError "equiv_loop_auto: no @[equiv_loop_term] theorem matches {← ght.getType}"
    -- the coupling invariant and the exit relation
    let Ie ← elabTermEnsuringType I (← gI.getType)
    gI.assign Ie
    let tgtTy ← instantiateMVars (← g.getType)
    let _ := tgtTy
    match R with
    | some R =>
      -- `R` is the implicit relation of the rule: it occurs in the step goal's type
      let some rm := (← instantiateMVars (← gk.getType)).find? (fun e => e.isMVar)
        | pure ()
      let rty ← inferType rm
      let Re ← elabTermEnsuringType R rty
      unless ← isDefEq rm Re do throwError "equiv_loop_auto: cannot use the exit relation {R}"
    | none => pure ()
    -- remaining instance arguments
    for (x, _) in tagged do
      unless ← x.isAssigned do
        let ty ← instantiateMVars (← x.getType)
        if (← isClass? ty).isSome then x.assign (← synthInstance ty)
    -- default exit relation: equality
    let kty ← instantiateMVars (← gk.getType)
    if let some rm := kty.find? (fun e => e.isMVar) then
      let rty ← inferType rm
      let eqRel ← forallTelescope rty fun xs _ => do
        if xs.size == 2 then mkLambdaFVars xs (← mkEq xs[0]! xs[1]!) else throwError "no default"
      discard <| isDefEq rm eqRel
    ghI.setTag `init; gstep.setTag `step; gk.setTag `post
    replaceMainGoal [ghI, gstep, gk]

end EquivLean

namespace EquivLean

open Lean Elab Tactic Meta

/-- `equiv_loop_async I V sched (with R)?`: pair the loop at the head of the goal with the
loop at the head of a hypothesis *asynchronously* (`wp_loop_stutter_rel`): in each product
state the scheduler `sched` picks whether both loops iterate, only the target, or only the
source; `V` decreases on every product step.  Goals: `init`, `both`, `left`, `right`, `post`. -/
syntax (name := equivLoopAsync) "equiv_loop_async" term:max term:max term:max (" with " term)? :
  tactic

elab_rules : tactic
  | `(tactic| equiv_loop_async $I $V $sched $[with $R]?) => withMainContext do
    let g ← getMainGoal
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``wp_loop_stutter_rel)
      { allowSynthFailures := true }
    let tagged ← gs.mapM fun x => return (x, ← x.getTag)
    let get (n : Name) : TacticM MVarId := do
      match tagged.find? (fun (_, t) => t == n || t.componentsRev.head? == some n) with
      | some (x, _) => pure x
      | none => throwError "equiv_loop_async: internal: no goal {n}"
    let gh₁ ← get `h₁; let gh₂ ← get `h₂
    let gI ← get `I; let gV ← get `V; let gS ← get `sched; let ghs ← get `hs
    let ghI ← get `hI; let gb ← get `hboth; let gl ← get `hleft; let gr ← get `hright
    let gk ← get `hk
    ghs.assumption
    unless ← solveWithFirst gh₁ (← labelled `equiv_loop_shape) do
      throwError "equiv_loop_async: no @[equiv_loop_shape] theorem matches {← gh₁.getType}"
    unless ← solveWithFirst gh₂ (← labelled `equiv_loop_shape) do
      throwError "equiv_loop_async: no @[equiv_loop_shape] theorem matches {← gh₂.getType}"
    gI.assign (← elabTermEnsuringType I (← gI.getType))
    gV.assign (← elabTermEnsuringType V (← gV.getType))
    gS.assign (← elabTermEnsuringType sched (← gS.getType))
    if let some R := R then
      if let some rm := (← instantiateMVars (← gk.getType)).find? (fun e => e.isMVar) then
        let Re ← elabTermEnsuringType R (← inferType rm)
        unless ← isDefEq rm Re do throwError "equiv_loop_async: cannot use the exit relation {R}"
    for (x, _) in tagged do
      unless ← x.isAssigned do
        let ty ← instantiateMVars (← x.getType)
        if (← isClass? ty).isSome then x.assign (← synthInstance ty)
    let kty ← instantiateMVars (← gk.getType)
    if let some rm := kty.find? (fun e => e.isMVar) then
      let eqRel ← forallTelescope (← inferType rm) fun xs _ => do
        if xs.size == 2 then mkLambdaFVars xs (← mkEq xs[0]! xs[1]!) else throwError "no default"
      discard <| isDefEq rm eqRel
    ghI.setTag `init; gb.setTag `both; gl.setTag `left; gr.setTag `right; gk.setTag `post
    replaceMainGoal [ghI, gb, gl, gr, gk]

end EquivLean

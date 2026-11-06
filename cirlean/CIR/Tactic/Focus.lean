import Lean
import CIR.Logic.Exec

/-!
  Focused simplification for symbolic execution.

  Goals during symbolic execution have the shape `Res.holds X K`, where `X` is
  the computation at the head and `K` the rest of the program applied to its
  result. `simp` alone simplifies bottom-up and would keep re-simplifying `K`
  while its inputs are still unknown. `cir_head simp-args` instead abstracts
  `K` to a fresh variable, simplifies, and substitutes `K` back, so the work
  per step is proportional to the head computation and the current state.
-/

namespace CIR.Tactic

open Lean Meta Elab Tactic

/-- The continuation `K` of a goal `Res.holds X K`, if any. -/
def holdsCont? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``CIR.Res.holds 3 then some e.appArg! else none

/-- `cir_head [lemmas]`: on a goal `Res.holds X K`, generalize `K`, run the
given `simp` call, put `K` back and beta-reduce. -/
syntax (name := cirHead) "cir_head " tactic : tactic

@[tactic cirHead] def evalCirHead : Tactic := fun stx => do
  let tac : TSyntax `tactic := ⟨stx[1]⟩
  let g ← getMainGoal
  let rest := (← getGoals).drop 1
  let t ← instantiateMVars (← g.getType)
  let t := t.consumeMData
  let g ← g.replaceTargetDefEq t
  let some k := holdsCont? t | throwError "cir_head: goal is not of the form `Res.holds X K`"
  if k.isFVar then
    setGoals (g :: rest)
    evalTactic tac
    return
  let (fvars, g') ← g.generalize #[{ expr := k, xName? := `K, hName? := `hK }]
  g'.withContext do
    setGoals [g']
    evalTactic tac
    -- put the continuation back: `hK : k = K`
    let gs ← getGoals
    let mut out := #[]
    for g'' in gs do
      let r ← g''.withContext do
        let some hK := fvars[1]? | throwError "cir_head: generalization lost its equation"
        let g3 ← substCore g'' hK (symm := true) (tryToSkip := true)
        let g3 := g3.2
        let t3 ← instantiateMVars (← g3.getType)
        g3.change (← Core.betaReduce t3)
      out := out.push r
    setGoals (out.toList ++ rest)

/-- Apply a rule whose conclusion unifies with the goal syntactically.
Unlike `apply`, the goal is never put in weak head normal form (`apply`
counts the goal's arrows with `whnf`, which on `Res.holds X K` evaluates the
program `X` as far as it can: costly, and on arithmetic with large literals
it exhausts the recursion limit). The rule's remaining hypotheses become the
new goals, in order. -/
def applyNoWhnf (g : MVarId) (rule : Name) : MetaM (List MVarId) := g.withContext do
  let r ← mkConstWithFreshMVarLevels rule
  let (mvars, _, concl) ← forallMetaTelescope (← inferType r)
  let t ← instantiateMVars (← g.getType)
  unless ← isDefEq concl t.consumeMData do throwError "cir_apply: {rule} does not apply"
  g.assign (mkAppN r mvars)
  let mut out := #[]
  for m in mvars do
    let m := m.mvarId!
    unless ← m.isAssigned do
      m.setKind .syntheticOpaque
      out := out.push m
  return out.toList

elab "cir_apply " r:ident : tactic => do
  let g ← getMainGoal
  let rest := (← getGoals).drop 1
  let n ← realizeGlobalConstNoOverloadWithInfo r
  setGoals ((← applyNoWhnf g n) ++ rest)

end CIR.Tactic

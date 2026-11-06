import Lean

/-!
# `spec_eqs`: instantiate callee posts over their argument lists

`jvc` leaves a constructor's post as `h : ∀ x v₁ … vₙ, a = x → b₁ = v₁ → … → bₙ = vₙ → P x v₁ … vₙ`
(its arguments, matched against the post's argument list). `spec_eqs` adds, for every such
hypothesis, `hspecK : P a b₁ … bₙ` (K = 1, 2, … in context order).
-/

open Lean Meta Elab Tactic

namespace EquivLean.Modernize.Cbact04c.Java

/-- The instance of `h : ty` at the values its equations give, if `ty` has that shape. -/
def specEqsInst (h : Expr) (ty : Expr) : MetaM (Option Expr) :=
  forallTelescope ty fun xs _ => do
    let n := xs.size / 2
    if n == 0 || xs.size != 2 * n then return none
    let mut vals : Array (Option Expr) := Array.replicate n none
    for i in [n:xs.size] do
      let t ← whnfR (← inferType xs[i]!)
      match t.eq? with
      | some (_, a, b) =>
        match xs.findIdx? (· == b) with
        | some j =>
          if j ≥ n then return none
          if a.hasAnyFVar (fun f => xs.any (· == .fvar f)) then return none
          vals := vals.set! j (some a)
        | none => return none
      | none => return none
    let mut args : Array Expr := #[]
    for v in vals do
      match v with
      | some a => args := args.push a
      | none => return none
    -- the equations, now `a = a`
    let mut pf := mkAppN h args
    for _ in [0:n] do
      let t ← whnfR (← inferType pf)
      match t with
      | .forallE _ d _ _ =>
        match d.eq? with
        | some (_, a, _) => pf := mkApp pf (← mkEqRefl a)
        | none => return none
      | _ => return none
    return some pf

/-- Split a hypothesis built from `∃` and `∧` into its parts. -/
partial def splitHyp (g : MVarId) (h : FVarId) : MetaM MVarId := g.withContext do
  let ty ← whnfR (← h.getType)
  if ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2 then
    let gs ← g.cases h
    match gs.toList with
    | [sg] =>
      let mut g' := sg.mvarId
      for f in sg.fields do
        if f.isFVar then g' ← splitHyp g' f.fvarId!
      return g'
    | _ => return g
  else return g

/-- `spec_eqs` and split the instances (`spec_eqs!`). -/
elab "spec_eqs!" : tactic => withMainContext do
  let mut g ← getMainGoal
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    unless ty.isForall do continue
    match ← specEqsInst (.fvar ld.fvarId) ty with
    | some pf =>
      let (h, g') ← g.note `hspec pf
      g ← splitHyp g' h
    | none => pure ()
  replaceMainGoal [g]

elab "spec_eqs" : tactic => withMainContext do
  let mut g ← getMainGoal
  let mut k := 1
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    unless ty.isForall do continue
    match ← specEqsInst (.fvar ld.fvarId) ty with
    | some pf =>
      let (_, g') ← g.note (Name.mkSimple s!"hspec{k}") pf
      g := g'
      k := k + 1
    | none => pure ()
  replaceMainGoal [g]

end EquivLean.Modernize.Cbact04c.Java

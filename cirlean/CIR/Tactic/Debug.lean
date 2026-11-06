import Lean

/-!
  Debugging tactics for long symbolic executions.

  * `cir_export_goals n` adds every goal, closed over its context, as a
    theorem `n.g0`, `n.g1`, … proved by `sorry`. Compile the file with
    `lean -o`; a second file that imports its olean states a goal with
    `theorem t : type_of% n.g0 := by intro …; <closer>` and develops the
    closer in seconds instead of re-running symbolic execution.
  * `cir_kernel_blame tac` runs `tac` on the main goal, admits what is left,
    and checks the proof with the kernel. If the kernel rejects it, it
    reports a minimal rejected proof subterm (each subterm is added as a
    declaration of its own, top-down) and, for an `Eq.trans`, where its
    middle term and its two equations differ: a definitional step that the
    kernel cannot redo cheaply (the cause of `ok_bind`'s "deep recursion",
    see `CIR/Semantics/Basic.lean`). The goal is then closed by `sorry`.
-/

namespace CIR.Tactic

open Lean Meta Elab Tactic

elab "cir_export_goals " n:ident : tactic => do
  let mut i := 0
  for g in ← getGoals do
    let ty ← g.withContext do
      let t ← instantiateMVars (← g.getType)
      let fvars := (← getLCtx).foldl (init := #[]) fun acc d =>
        if d.isImplementationDetail then acc else acc.push d.toExpr
      instantiateMVars (← mkForallFVars fvars t)
    let name := n.getId ++ Name.mkSimple s!"g{i}"
    addDecl (.thmDecl { name, levelParams := [], type := ty, value := ← mkSorry ty false })
    logInfo m!"cir_export_goals: {name}"
    i := i + 1

/-- The kernel's verdict on `e` (any term, closed over the local context and
added as a definition or theorem): `none` when accepted. -/
def kernelVerdict? (e : Expr) : MetaM (Option String) := do
  let e ← instantiateMVars e
  let ty ← instantiateMVars (← inferType e)
  let fvars := (← getLCtx).getFVars
  let s ← saveState
  tryCatchRuntimeEx (do
      let ty' ← mkForallFVars fvars ty
      let e' ← mkLambdaFVars fvars e
      let name ← mkFreshUserName `cir_blame
      if ← isProp ty then
        addDecl (.thmDecl { name, levelParams := [], type := ty', value := e' })
      else
        let dv : DefinitionVal := { name := name, levelParams := [], type := ty', value := e', hints := ReducibilityHints.opaque, safety := DefinitionSafety.safe }
        addDecl (.defnDecl dv)
      s.restore
      return none)
    fun ex => do
      s.restore
      return some (← ex.toMessageData.toString)

/-- A minimal proof subterm of `pf` that the kernel rejects. -/
partial def blameProof (pf : Expr) (depth : Nat := 0) : MetaM (Option (Expr × String)) := do
  let some err ← kernelVerdict? pf | return none
  if depth > 3000 then return some (pf, err)
  let kids : Array Expr := match pf with
    | .app .. => #[pf.getAppFn] ++ pf.getAppArgs
    | .mdata _ b => #[b]
    | .letE _ _ v b _ => #[v, b]
    | _ => #[]
  for c in kids do
    if c.hasLooseBVars || c.isFVar || c.isConst || c.isSort then continue
    let isPf ← try isProof c catch _ => pure false
    if isPf then
      if let some r ← blameProof c (depth + 1) then return some r
    else if c.isLambda then
      let r ← lambdaTelescope c fun _ body => do
        if ← (try isProof body catch _ => pure false) then blameProof body (depth + 1) else pure none
      if let some r := r then return some r
  if pf.isLambda then
    if let some r ← lambdaTelescope pf fun _ body => blameProof body (depth + 1) then return some r
  return some (pf, err)

/-- The first position where `x` and `y` differ structurally. -/
partial def firstDiff (x y : Expr) : Option (Expr × Expr) :=
  if x == y then none else
  match x, y with
  | .mdata _ e, _ => firstDiff e y
  | _, .mdata _ e => firstDiff x e
  | .app .., .app .. =>
    let ax := x.getAppArgs
    let ay := y.getAppArgs
    if x.getAppFn == y.getAppFn && ax.size == ay.size then Id.run do
      for i in [0:ax.size] do
        if ax[i]! != ay[i]! then return firstDiff ax[i]! ay[i]!
      return some (x, y)
    else some (x, y)
  | .lam _ t b _, .lam _ t' b' _ | .forallE _ t b _, .forallE _ t' b' _ =>
    if t != t' then firstDiff t t' else firstDiff b b'
  | _, _ => some (x, y)

elab "cir_kernel_blame " t:tacticSeq : tactic => withTheReader Core.Context
    (fun c => { c with maxRecDepth := 1000000 }) do
  let g ← getMainGoal
  g.withContext do
    let g' ← mkFreshExprSyntheticOpaqueMVar (← instantiateMVars (← g.getType))
    setGoals [g'.mvarId!]
    evalTactic t
    for r in ← getGoals do
      unless ← r.isAssigned do r.admit
    let pf ← instantiateMVars g'
    match ← blameProof pf with
    | none => logInfo "cir_kernel_blame: the kernel accepts the proof"
    | some (e, err) =>
      let mut msg := m!"cir_kernel_blame: the kernel rejects{indentD err}\nminimal subterm (head {e.getAppFn}):{indentExpr e}"
      if e.isAppOfArity ``Eq.trans 6 then
        let tA ← instantiateMVars (← inferType (e.getArg! 4))
        let tB ← instantiateMVars (← inferType (e.getArg! 5))
        if let (some (_, _, b1), some (_, b2, _)) := (tA.eq?, tB.eq?) then
          for (what, l, r) in [("first equation's right side", b1, e.getArg! 2),
              ("second equation's left side", b2, e.getArg! 2)] do
            if let some (u, v) := firstDiff l r then
              msg := msg ++ m!"\n{what} and the middle term differ at{indentExpr u}\nvs{indentExpr v}"
      logWarning msg
  g.admit
  setGoals []

end CIR.Tactic

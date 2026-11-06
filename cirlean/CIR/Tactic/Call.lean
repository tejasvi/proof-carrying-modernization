import CIR.Semantics.Init
import CIR.Tactic.Focus
import CIR.Tactic.Attr
import CIR.Tactic.Options
import CIR.Logic.Exec
import CIR.Tactic.Lookup
import CIR.Logic.Loops
import CIR.Logic.WFGlobal

/-!
  Calls during symbolic execution.

  `cir_call_inline`, on a goal whose head is `evalCall ctx sym args m`, looks
  `sym` up in the module (by computation) and
  * if the function has a native library model, continues with the model's
    Lean code (`Std.runModel`);
  * otherwise continues with the function body (inlining).
  `cir_start` turns a `Returns` / `Calls` goal into the symbolic execution of
  the function body.

  `cir_call_spec` instead uses a proved specification of the callee (a
  theorem tagged `@[cir_spec]`); `cir_vcg` tries it first. With
  `set_option cir.inline false`, callees with a body are never inlined.
-/

namespace CIR.Tactic

open Lean Meta Elab Tactic Term

/-- The head computation `X` of a goal `Res.holds X K`. -/
def holdsHead' (e : Expr) : Option Expr :=
  if e.isAppOfArity ``CIR.Res.holds 3 then some (e.getArg! 1) else none

/-- The symbol a specification (a theorem or a local hypothesis of type `ty`)
is about: its conclusion, under the binders, is `Returns ctx sym args m
post`; and for each binder whether it is a proof (a precondition). -/
partial def specSymbolOfType? (ty : Expr) : MetaM (Option (String × Array Bool)) := do
  forallTelescopeReducing ty fun xs concl => do
    let concl ← whnfR concl
    unless concl.isAppOfArity ``CIR.Returns 5 do return none
    let sym ← whnfD (concl.getArg! 1)
    let .lit (.strVal s) := sym | return none
    let props ← xs.mapM fun x => do isProp (← inferType x)
    return some (s, props)

/-- `specSymbolOfType?` of a `@[cir_spec]` theorem. -/
def specSymbol? (thm : Name) : MetaM (Option (String × Array Bool)) := do
  specSymbolOfType? (← getConstInfo thm).type

/-- Split a hypothesis `h : A ∧ B ∧ …` into named facts `h_1, h_2, …`
(prefix kept, so `cir_step` uses them) and substitute equations `x = e` whose
left side is a local variable. -/
partial def splitFact (h : Name) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
    let some d := (← getLCtx).findFromUserName? h | return
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``And 2 then
      let a := Name.mkSimple (h.toString ++ "a")
      let b := Name.mkSimple (h.toString ++ "b")
      evalTactic (← `(tactic| obtain ⟨$(mkIdent a):ident, $(mkIdent b):ident⟩ := $(mkIdent h):ident))
      splitFact a
      splitFact b
    else if ty.isAppOfArity ``Exists 2 then
      -- `∃ s, …` in a postcondition: a fresh witness
      let x := Name.mkSimple ("cir_w_" ++ h.toString)
      let p := Name.mkSimple (h.toString ++ "p")
      evalTactic (← `(tactic| obtain ⟨$(mkIdent x):ident, $(mkIdent p):ident⟩ := $(mkIdent h):ident))
      splitFact p
    else if let some (_, lhs, _) := ty.eq? then
      if lhs.isFVar then
        try evalTactic (← `(tactic| subst $(mkIdent h):ident)) catch _ => pure ()

/-- Well-formedness of the memory at a call: writes below `next` and scope
exits (`Mem.WF_upd`, `Mem.WF_killRange`) down to a well-formedness fact
(`Mem.WF_mono'` when `next` grew). -/
macro "cir_wf_core" : tactic => `(tactic| (
  repeat (first
    | refine Mem.WF_upd ?_ (by omega) _
    | refine Mem.WF_killRange ?_)
  first
    | assumption
    | exact Mem.WF_mono' ‹_› (by omega)
    | exact Mem.WF_mono ‹_› (by omega)))

/-- Use a `@[cir_spec]` theorem for the call at the head of the goal: its
preconditions become goals, and the rest of the program continues from an
arbitrary result satisfying its postcondition (`cirH_post`). -/
elab "cir_call_spec" : tactic => Lean.Core.withCurrHeartbeats do
  let g ← getMainGoal
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some x := holdsHead' t | throwError "cir_call_spec: goal is not `Res.holds _ _`"
  let x ← instantiateMVars x
  unless x.isAppOfArity ``CIR.evalCall 4 do throwError "cir_call_spec: no call at the head"
  let sym ← whnfD (x.getArg! 1)
  let .lit (.strVal symS) := sym | throwError "cir_call_spec: callee symbol is not a literal"
  let mut lastErr : MessageData := m!"no @[cir_spec] theorem for {symS}"
  -- specifications: local hypotheses (contracts of callees taken as
  -- assumptions, e.g. for per-function proofs over an abstract context),
  -- then the `@[cir_spec]` theorems
  let mut specs : Array (Term × MessageData × Array Bool) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if let some (s, props) ← specSymbolOfType? (← instantiateMVars d.type) then
      if s == symS then
        specs := specs.push (← exprToSyntax (mkFVar d.fvarId), m!"{d.userName}", props)
  for thm in ← Lean.labelled `cir_spec do
    let some (s, props) ← specSymbol? thm | continue
    unless s == symS do continue
    specs := specs.push (← `(@$(mkIdent thm)), m!"{thm}", props)
  for (thmS, thmName, props) in specs do
    let saved ← saveState
    try
      -- preconditions become goals; values are found by unification with the
      -- call, or (ghost values such as the current contents of a pointee) while
      -- the preconditions are proved
      let holes : Array Term ← props.mapM fun p => if p then `(?_) else `(_)
      let rest := (← getGoals).drop 1
      -- with the memory before the call well formed (`cir_wf_core`), the
      -- continuation also gets the well-formedness of the memory after it
      -- (`holds_call_spec_wf`, from `Returns.wf`), whatever the specification
      -- says (opt-in: `set_option cir.callWF true`)
      let wfPf? ← if !(← getOptions).getBool `cir.callWF false then pure none else do
        let w ← mkFreshExprMVar (← mkAppM ``CIR.Mem.WF #[x.getArg! 3])
        let s0 ← saveState
        try
          setGoals [w.mvarId!]
          evalTactic (← `(tactic| cir_wf_core))
          unless (← getGoals).isEmpty do throwError "cir_call_spec: WF not proved"
          pure (some (← instantiateMVars w))
        catch _ =>
          s0.restore
          pure none
      setGoals (g :: rest)
      let gs ← g.apply (← mkConstWithFreshMVarLevels
        (if wfPf?.isSome then ``CIR.holds_call_spec_wf else ``CIR.holds_call_spec))
      -- the new goals are tagged `<tag of g>.hspec` and `<tag of g>.hk`
      let tagged (s : String) (g : MVarId) : TacticM Bool := do
        match ← g.getTag with
        | .str _ t => return t == s
        | _ => return false
      let some hspec ← gs.findM? (tagged "hspec")
        | throwError "cir_call_spec: no specification goal"
      let some kg ← gs.findM? (tagged "hk")
        | throwError "cir_call_spec: no continuation goal"
      if let some w := wfPf? then
        let some hwfG ← gs.findM? (tagged "hwf")
          | throwError "cir_call_spec: no well-formedness goal"
        unless ← isDefEq (mkMVar hwfG) w do throwError "cir_call_spec: well-formedness mismatch"
      setGoals [hspec]
      evalTactic (← `(tactic| refine' $thmS $holes*))
      let mut pres := #[]
      let mut ghosts := #[]
      for ng in ← getGoals do
        if ← isProp (← ng.getType) then pres := pres.push ng
        else ghosts := ghosts.push ng
      -- continue after the call with the postcondition as named facts
      setGoals [kg]
      let n := (← kg.getDecl).lctx.foldl (init := 0) fun acc d =>
        if d.userName.toString.startsWith "cirH_post" then acc + 1 else acc
      let v := mkIdent (Name.mkSimple s!"cir_ret{n}")
      let m' := mkIdent (Name.mkSimple s!"cir_mem{n}")
      let h := mkIdent (Name.mkSimple s!"cirH_post{n}")
      evalTactic (← `(tactic| intro $v:ident $m':ident $h:ident))
      if wfPf?.isSome then
        let hw := mkIdent (Name.mkSimple s!"cirH_cwf{n}")
        evalTactic (← `(tactic| intro $hw:ident))
      evalTactic (← `(tactic| try simp only [CIR.Frame, List.not_mem_nil,
        not_false_eq_true, true_implies, forall_const] at $h:ident))
      splitFact h.getId
      setGoals (pres.toList ++ (← getGoals) ++ ghosts.toList ++ rest)
      return
    catch e =>
      saved.restore
      lastErr := m!"cir_call_spec: {thmName} does not apply: {e.toMessageData}"
  throwError lastErr

/-- Replace a call at the head of the goal by the callee's body or model. -/
elab "cir_call_inline" : tactic => Lean.Core.withCurrHeartbeats do
  let g ← getMainGoal
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some x := holdsHead' t | throwError "cir_call_inline: goal is not `Res.holds _ _`"
  let x ← instantiateMVars x
  unless x.isAppOfArity ``CIR.evalCall 4 do
    throwError "cir_call_inline: the head of the goal is not a call"
  let ctx := x.getArg! 0
  let sym := x.getArg! 1
  let look ← mkAppM ``CIR.Module.findFunc? #[← mkAppM ``CIR.Ctx.mod #[ctx], sym]
  -- a concrete module is searched; for an abstract context, a hypothesis
  -- `ctx.mod.findFunc? sym = some fd` gives the callee
  let found ← match ← lookupEq? look with
    | some r => pure (some r)
    | none => (← getLCtx).findDeclM? fun d => do
        if d.isImplementationDetail then return none
        let ty ← instantiateMVars d.type
        let some (_, lhs, rhs) := ty.eq? | return none
        unless ← withReducible (isDefEq lhs look) do return none
        return some (rhs, mkFVar d.fvarId)
  let some (fdOpt, hfind) := found
    | throwError "cir_call_inline: cannot look up {sym} in the module"
  let_expr Option.some _ fd := fdOpt
    | throwError "cir_call_inline: function {sym} is not in the module"
  let fdS ← exprToSyntax fd
  let hfindS ← exprToSyntax hfind
  let mdlOpt ← whnfD (← mkAppM ``CIR.FuncDecl.model #[fd])
  match_expr mdlOpt with
  | Option.some _ mdl =>
    let mdlS ← exprToSyntax mdl
    evalTactic (← `(tactic| rw [CIR.evalCall_model (fd := $fdS) (mdl := $mdlS) $hfindS rfl]))
  | _ =>
    unless (← getOptions).getBool `cir.inline true do
      throwError "cir_call_inline: {sym} needs a @[cir_spec] theorem (inlining is off: cir.inline)"
    let bodyOpt ← whnfD (← mkAppM ``CIR.FuncDecl.body #[fd])
    let_expr Option.some _ body := bodyOpt
      | throwError "cir_call_inline: {sym} has neither a body nor a library model"
    let bodyS ← exprToSyntax body
    -- a destructor's return ends its object's lifetime (`evalCall_dtor`)
    let special ← whnfD (← mkAppM ``CIR.FuncDecl.special #[fd])
    if special.isConstOf ``CIR.SpecialMember.dtor then
      evalTactic (← `(tactic| rw [CIR.evalCall_dtor (fd := $fdS) (body := $bodyS) $hfindS rfl rfl rfl]))
    else
      evalTactic (← `(tactic| rw [CIR.evalCall_body (fd := $fdS) (body := $bodyS) $hfindS rfl rfl
        (by decide)]))

/-- Replace `Std.runModel ctx mdl args m` (concrete `mdl`, `args`) at the head
of the goal by the matching branch of the model, by definitional unfolding. -/
elab "cir_model_unfold" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some x := holdsHead' t | throwError "cir_model_unfold: goal is not `Res.holds _ _`"
  let x ← instantiateMVars x
  unless x.isAppOfArity ``CIR.Std.runModel 4 do throwError "cir_model_unfold: no model call at the head"
  let some x1 ← unfoldDefinition? x | throwError "cir_model_unfold: cannot unfold runModel"
  let x2 ← whnfCore x1
  if x2.isAppOf ``CIR.Std.runModel then throwError "cir_model_unfold: no matching model case"
  replaceMainGoal [← g.replaceTargetDefEq (mkAppN t.getAppFn #[t.getArg! 0, x2, t.getArg! 2])]

/-- Close a lookup equation in a concrete module (`ctx.mod.findFunc? s = some
fd`, `ctx.record? "R" = some r`, ...) by computing the lookup; the kernel
checks the `rfl`. Assembles per-function proofs over an abstract context. -/
elab "cir_lookup" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let some (_, lhs, rhs) := (← instantiateMVars (← g.getType)).eq?
      | throwError "cir_lookup: the goal is not an equation"
    let some (v, pf) ← lookupEq? lhs | throwError "cir_lookup: not a lookup in a concrete module"
    unless ← isDefEq v rhs do throwError "cir_lookup: the lookup gives {v}"
    g.assign pf
    replaceMainGoal []

/-- Integer constructors applied to literals (`Int.ofNat 110`, as produced by
reduction) as numerals (`110`, `-3`), so that `simp` can match them. -/
def intNumerals (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if x.isAppOfArity ``Int.ofNat 1 then
      if let .lit (.natVal n) := x.appArg! then
        return .done (← mkNumeral (mkConst ``Int) n)
    if x.isAppOfArity ``Int.negSucc 1 then
      if let .lit (.natVal n) := x.appArg! then
        return .done (← mkAppM ``Neg.neg #[← mkNumeral (mkConst ``Int) (n + 1)])
    return .continue)

/-- `cir_ro_globals h` for `h : Module.RoGlobals M m` with a concrete module
`M`: adds `m.blocks i = some ⟨.readonly, true, ty, v⟩` for every constant
global `i` of `M`, with `v` its initial value (computed here, checked by the
kernel; for a constant global the module only declares, its read-only block,
which is not alive). `cir_vcg` then reads string literals and constant
tables. -/
elab "cir_ro_globals " h:ident : tactic => do
  let g ← getMainGoal
  g.withContext do
    let hd ← getLocalDeclFromUserName h.getId
    let ty ← whnfR (← instantiateMVars hd.type)
    let_expr CIR.Module.RoGlobals M m := ty
      | throwError "cir_ro_globals: {h.getId} is not `Module.RoGlobals M m`"
    -- walk the list with `whnf` (long literals are elaborated in chunks)
    let some gl ← listElems (← mkAppM ``CIR.Module.globals #[M])
      | throwError "cir_ro_globals: the module's globals are not a list"
    let mut goal := g
    for (gd, i) in gl.toList.zipIdx do
      let c ← whnfD (← mkAppM ``CIR.GlobalDecl.constant #[gd])
      unless c.isConstOf ``Bool.true do continue
      let iE := mkNatLit i
      let lhs ← mkAppM ``CIR.Mem.blocks #[m, iE]
      let rhs0 ← mkAppM ``CIR.Mem.blocks #[← mkAppM ``CIR.Module.initMem #[M], iE]
      let rhs ← intNumerals (← withTransparency .all <| Meta.reduce rhs0 (skipTypes := false))
      let hget ← mkEqRefl (← mkAppM ``Option.some #[gd])
      let hconst ← mkEqRefl (mkConst ``Bool.true)
      let pf0 ← mkAppM' (mkFVar hd.fvarId) #[iE, gd, hget, hconst]
      let pf ← mkExpectedTypeHint (← mkEqTrans pf0 (← mkEqRefl rhs)) (← mkEq lhs rhs)
      let (_, goal') ← (← goal.assert (Name.mkSimple s!"cirH_ro{i}") (← mkEq lhs rhs) pf).intro1P
      goal := goal'
    replaceMainGoal [goal]

/-- `cir_init_mem`: for the initial memory `Module.initMem M` of a concrete
module in the goal, adds `(Module.initMem M).blocks i = some …` for every
global `i` and `(Module.initMem M).next = n` (values computed here, checked by
the kernel), so that `cir_vcg` runs code from the program's initial state
(test functions: `cir_start; cir_init_mem; cir_eval`). -/
elab "cir_init_mem" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let some im := tgt.find? (fun e => e.isAppOfArity ``CIR.Module.initMem 1)
      | throwError "cir_init_mem: no `Module.initMem` in the goal"
    let M := im.getArg! 0
    let some gl ← listElems (← mkAppM ``CIR.Module.globals #[M])
      | throwError "cir_init_mem: the module's globals are not a list"
    let mut goal := g
    let mut facts : Array (Name × Expr) := #[]
    for i in [0:gl.size] do
      facts := facts.push (Name.mkSimple s!"cirH_init{i}", ← mkAppM ``CIR.Mem.blocks #[im, mkNatLit i])
    facts := facts.push (`cirH_initNext, ← mkAppM ``CIR.Mem.next #[im])
    for (nm, lhs) in facts do
      let rhs ← intNumerals (← withTransparency .all <| Meta.reduce lhs (skipTypes := false))
      let pf ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)
      let (_, goal') ← (← goal.assert nm (← mkEq lhs rhs) pf).intro1P
      goal := goal'
    replaceMainGoal [goal]
    -- the initial memory becomes an opaque variable described by the facts, so
    -- that nothing evaluates `Module.initMem` again
    let imS ← Lean.Elab.Term.exprToSyntax im
    evalTactic (← `(tactic| generalize $imS = $(mkIdent `cirInit) at *))

/-- Start the verification of a function: unfold `Returns` / `Calls` and
replace the call by the function body. -/
macro "cir_start" : tactic => `(tactic| (
  simp only [CIR.Returns, CIR.Calls]
  set_option cir.inline true in cir_call_inline))

end CIR.Tactic

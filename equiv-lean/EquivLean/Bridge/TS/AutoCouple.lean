import EquivLean.Bridge.TS.Tactic

/-!
# StrictTS bridge: generated couplings for lockstep loops

`equiv_ts_auto [defs…]` is `equiv_ts [defs…]` followed, on each direction, by `ts_auto_couple`: the
lockstep pairing of the two loops with a *generated* coupling (`ts_auto_lockstep`), or, for
loop-free code, the straight-line closer.  A direction the automation does not close is left
exactly as `equiv_ts` leaves it, for `ts_lockstep J, R` with a user coupling.

The generated coupling `J` of two loop states:
* the two loop environments are aligned from the bottom (outer scope) by slot;
* aligned mutable entries are equal (shared variables); aligned `const` entries and unaligned
  entries keep their values at loop entry (e.g. a flag that is set only right before `break`);
* the counter of an index loop paired with a `for … of` is the double of the `for … of` index,
  and the `for … of` array has a length below `2^32` that bounds the index (this needs a
  hypothesis `size < 2^32` in context: the StrictTS model does not bound array lengths);
* the worlds are equal.

The loop-exit relation is not generated: `R o₁ o₂ := K₂ o₂ → K₁ o₁`, the implication between the
two continuations after the loops, so the `exit` goal is trivial and the code after the loops is
checked inside the step, on the concrete exit states.  The step is closed by symbolic execution
(`ts_step_simp` lemmas plus the hypotheses), case splits on the remaining `if` conditions and
structural closers.  The whole pairing is atomic: if any goal stays open, `ts_auto_lockstep`
fails and leaves the goal unchanged.
-/

namespace EquivLean.TS
open StrictTS Lean Elab Tactic Meta

private inductive LKind where
  | forOf | loop | dowhile
  deriving BEq, Inhabited

private structure LoopInfo where
  kind : LKind
  TT : Expr
  env : Expr
  idx : Option Expr := none
  arr : Option (Expr × Expr) := none
  ctx : Expr

private def loopInfo? (L : Expr) : MetaM (Option LoopInfo) := do
  let L := L.cleanupAnnotations
  let as_ := L.getAppArgs
  if L.isAppOfArity ``StrictTS.evalForOf 10 then
    -- evalForOf {TT} I P {Γ} {ρ} {t} a i body env
    return some (LoopInfo.mk .forOf (as_[0]!) (as_[9]!) (some (as_[7]!)) (some ((as_[6]!), (as_[5]!)))
      (as_[3]!))
  else if L.isAppOfArity ``StrictTS.evalLoop 9 then
    return some (LoopInfo.mk .loop (as_[0]!) (as_[8]!) none none (as_[3]!))
  else if L.isAppOfArity ``StrictTS.evalDo 8 then
    return some (LoopInfo.mk .dowhile (as_[0]!) (as_[7]!) none none (as_[3]!))
  else return none

/-- The slots of a context, top first. -/
private partial def ctxSlots (Γ : Expr) : MetaM (Array Expr) := do
  let Γ ← whnfD (← instantiateMVars Γ)
  if Γ.isAppOfArity ``List.cons 3 then
    return #[Γ.getArg! 1] ++ (← ctxSlots (Γ.getArg! 2))
  else return #[]

/-- The values of an explicit environment, top first. -/
private partial def envVals (e : Expr) : MetaM (Option (Array Expr)) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  if e.isAppOfArity ``StrictTS.Env.cons 5 then
    let some rest ← envVals (e.getArg! 4) | return none
    return some (#[e.getArg! 3] ++ rest)
  else if e.isAppOfArity ``StrictTS.Env.nil 1 then return some #[]
  else return none

private def slotTy (s : Expr) : MetaM Expr := do
  whnfD (mkApp (mkConst ``StrictTS.Slot.ty) s)

/-- `wp (JS.exec L w) K`: the loop info, the world and the postcondition. -/
private def wpLoop? (e : Expr) : MetaM (Option (LoopInfo × Expr × Expr × Expr)) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  unless e.isAppOfArity ``EquivLean.wp 5 do return none
  let c := e.getAppArgs[3]!.cleanupAnnotations
  unless c.isAppOfArity ``StrictTS.JS.exec 4 do return none
  let L := (c.getArg! 2).cleanupAnnotations
  let some li ← loopInfo? L | return none
  return some (li, L, c.getArg! 3, e.getAppArgs[4]!)

private def shapeStx (li : LoopInfo) (L : Expr) : TacticM (Term × Term × Term) := do
  let as_ := L.getAppArgs
  let s (i : Nat) : TacticM Term := Term.exprToSyntax as_[i]!
  match li.kind with
  | .forOf => return (← `(EquivLean.TS.forOfShape $(← s 1) $(← s 2) $(← s 6) $(← s 8)),
      ← `(EquivLean.TS.forOfTerminates $(← s 1) $(← s 2) $(← s 6) $(← s 8)), ← `(Term.hole))
  | .loop => return (← `(EquivLean.TS.loopShape $(← s 1) $(← s 2) $(← s 5) $(← s 6) $(← s 7)),
      ← `(EquivLean.TS.loopTerminates $(← s 1) $(← s 2) $(← s 5) $(← s 6) $(← s 7)), ← `(Term.hole))
  | .dowhile => return (← `(EquivLean.TS.doShape $(← s 1) $(← s 2) $(← s 5) $(← s 6)),
      ← `(EquivLean.TS.doTerminates $(← s 1) $(← s 2) $(← s 5) $(← s 6)), ← `(Term.hole))

/-- Projections of a loop state: environment, index (for … of), world. -/
private def stEnv (li : LoopInfo) (s : Ident) : TacticM Term :=
  if li.kind == .forOf then `($s.1.2) else `($s.1)

private def stInit (li : LoopInfo) (w : Expr) : TacticM Term := do
  let ws ← Term.exprToSyntax w
  let es ← Term.exprToSyntax li.env
  if li.kind == .forOf then
    let is ← Term.exprToSyntax li.idx.get!
    `((($is, $es), $ws))
  else `(($es, $ws))

/-- Build the generated coupling. -/
private def genCoupling (l₁ l₂ : LoopInfo) : TacticM Term := do
  let s₁ := mkIdent `s₁; let s₂ := mkIdent `s₂
  let sl₁ ← ctxSlots l₁.ctx; let sl₂ ← ctxSlots l₂.ctx
  let some v₁ ← envVals l₁.env | throwError "auto coupling: target loop environment not explicit"
  let some v₂ ← envVals l₂.env | throwError "auto coupling: source loop environment not explicit"
  unless v₁.size == sl₁.size && v₂.size == sl₂.size do throwError "auto coupling: shape mismatch"
  -- align from the bottom
  let n₁ := sl₁.size; let n₂ := sl₂.size
  let mut p := 0
  while p < n₁ && p < n₂ && (← withNewMCtxDepth (isDefEq sl₁[n₁ - 1 - p]! sl₂[n₂ - 1 - p]!)) do
    p := p + 1
  let k₁ := n₁ - p; let k₂ := n₂ - p
  -- the counter of an index loop paired with a for … of
  let ctr₁ := l₁.kind != .forOf && l₂.kind == .forOf && k₁ ≥ 1
  let ctr₂ := l₂.kind != .forOf && l₁.kind == .forOf && k₂ ≥ 1
  -- matched mutable slots become shared variables; immutable ones keep their entry values
  let mut isMut : Array Bool := #[]
  for m in [0:p] do
    let b ← whnfD (mkApp (mkConst ``StrictTS.Slot.mutable) sl₁[n₁ - 1 - m]!)
    isMut := isMut.push (b.isConstOf ``Bool.true)
  let xs : Array Ident := (Array.range p).map fun j => mkIdent (Name.mkSimple s!"x{j}")
  let idxOf (li : LoopInfo) (s : Ident) : TacticM Term := do
    if li.kind == .forOf then `($s.1.1) else `(0)
  let chain (vs : Array Expr) (k : Nat) (ctr : Bool) (other : LoopInfo) (os : Ident) : TacticM Term := do
    let mut acc ← `(StrictTS.Env.nil)
    for j' in [0:vs.size] do
      let j := vs.size - 1 - j'
      let m := vs.size - 1 - j
      let v ← if j ≥ k && isMut[m]! then pure (xs[m]! : Term)
        else if j ≥ k then Term.exprToSyntax vs[j]!
        else if ctr && j == 0 then do
          let i ← idxOf other os
          `(StrictTS.Val.num (StrictTS.F64.ofNat $i))
        else Term.exprToSyntax vs[j]!
      acc ← `(StrictTS.Env.cons $v $acc)
    return acc
  let c₁ ← chain v₁ k₁ ctr₁ l₂ s₂
  let c₂ ← chain v₂ k₂ ctr₂ l₁ s₁
  let e₁ ← stEnv l₁ s₁; let e₂ ← stEnv l₂ s₂
  let mut conj : Array Term := #[← `($e₁ = $c₁), ← `($e₂ = $c₂), ← `($s₁.2 = $s₂.2)]
  -- bounds of a for … of
  let bound (li : LoopInfo) (s : Ident) : TacticM (Option Term) := do
    match li.arr with
    | some (a, t) =>
      let aS ← Term.exprToSyntax a; let tS ← Term.exprToSyntax t
      return some (← `(∃ c, ($s.2).heap.get? (StrictTS.HKind.arr $tS, $aS) = some c ∧
        $s.1.1 ≤ c.size ∧ c.size < 4294967296))
    | none => return none
  -- the bound is needed only when an index loop (a `number` counter) meets a `for … of`
  if (l₁.kind == .forOf) != (l₂.kind == .forOf) then
    if let some b ← bound l₁ s₁ then conj := conj.push b
    else if let some b ← bound l₂ s₂ then conj := conj.push b
  if l₁.kind == .forOf && l₂.kind == .forOf then conj := conj.push (← `($s₁.1.1 = $s₂.1.1))
  let mut body := conj.back!
  for c in (conj.pop).reverse do
    body ← `($c ∧ $body)
  for m' in [0:p] do
    let m := p - 1 - m'
    if isMut[m]! then body ← `(∃ $(xs[m]!):ident, $body)
  `(fun $s₁ $s₂ => $body)

/-- Lemmas for one iteration, the continuation after the loop, and the counter bridge. -/
macro "ts_auto_simp" : tactic => `(tactic|
  simp (disch := omega) only [EquivLean.TS.forOfStep, EquivLean.TS.forOfStepWith,
    EquivLean.TS.loopStep, EquivLean.TS.loopStepWith, EquivLean.TS.doStep,
    EquivLean.TS.doStepWith, ts_sym, StrictTS.lt_ofNat, StrictTS.le_ofNat,
    StrictTS.Conv.arrayIndex?_ofNat, StrictTS.ofNat_add_one, StrictTS.F64.lit_eq_ofNat,
    EquivLean.TS.sim_some_some, EquivLean.StepRel, EquivLean.TS.stepCls_inr,
    EquivLean.TS.stepCls_inl, EquivLean.TS.stepCls_error, decide_true, decide_false,
    decide_eq_true_eq, dite_true, dite_false, and_self, and_true, true_and, Bool.not_true,
    Bool.not_false, EquivLean.wp_some, EquivLean.TS.wp_exec_match, exists_eq', exists_eq_left,
    EquivLean.TS.evalE_taGet_u8, *])

/-- Destruct values of single-constructor types (numbers, booleans, strings, references, external
handles; not `unknown` values, whose single constructor carries a runtime type). -/
elab "ts_destruct_vals" : tactic => do
  let mut fuel := 64
  let mut progress := true
  while progress && fuel > 0 do
    progress := false
    fuel := fuel - 1
    let g ← getMainGoal
    let lctx := (← g.getDecl).lctx
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ty.isAppOfArity ``StrictTS.Val 2 do continue
      let t ← whnfD ty.appArg!
      let single := t.isConstOf ``StrictTS.Ty.num || t.isConstOf ``StrictTS.Ty.bool ||
        t.isConstOf ``StrictTS.Ty.str || t.isConstOf ``StrictTS.Ty.bigint ||
        t.isAppOf ``StrictTS.Ty.arr || t.isAppOf ``StrictTS.Ty.tarr || t.isAppOf ``StrictTS.Ty.map ||
        t.isAppOf ``StrictTS.Ty.set || t.isAppOf ``StrictTS.Ty.obj ||
        t.isAppOf ``StrictTS.Ty.dict || t.isAppOf ``StrictTS.Ty.ext
      unless single do continue
      try
        let gs ← g.cases d.fvarId
        replaceMainGoal (gs.map (·.mvarId)).toList
        progress := true
        break
      catch _ => pure ()

/-- Case split on the first closed `if` condition of the goal (loop conditions, `===`, …). -/
elab "ts_split_if" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun e =>
      (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) && !(e.getArg! 1).hasLooseBVars &&
        !(e.getArg! 1).hasMVar)
    | throwError "ts_split_if: no if"
  let c ← Term.exprToSyntax (e.getArg! 1)
  let hI := mkIdent `hsplit
  evalTactic (← `(tactic| (by_cases $hI:ident : $c <;>
    try simp only [Bool.not_eq_true, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true,
      Bool.not_false, decide_eq_true_eq] at $hI:ident)))

/-- Structural closer for the generated coupling and for the continuation implication. -/
macro "ts_auto_close" : tactic => `(tactic|
  repeat' (first | rfl | (intro h; exact ⟨_, h, rfl⟩) | (refine ⟨_, ?_⟩) | (refine ⟨?_, ?_⟩) | assumption | omega | trivial))

/-- Number of mutable entries aligned from the bottom (the coupling's variables). -/
private def matchedCount (l₁ l₂ : LoopInfo) : TacticM Nat := do
  let sl₁ ← ctxSlots l₁.ctx; let sl₂ ← ctxSlots l₂.ctx
  let n₁ := sl₁.size; let n₂ := sl₂.size
  let mut p := 0
  while p < n₁ && p < n₂ && (← withNewMCtxDepth (isDefEq sl₁[n₁ - 1 - p]! sl₂[n₂ - 1 - p]!)) do
    p := p + 1
  let mut nv := 0
  for m in [0:p] do
    let b ← whnfD (mkApp (mkConst ``StrictTS.Slot.mutable) sl₁[n₁ - 1 - m]!)
    if b.isConstOf ``Bool.true then nv := nv + 1
  return nv

/-- The `rintro` pattern of the generated coupling. -/
private def jPattern (nvars : Nat) (hasBound bothFor : Bool) : TacticM (TSyntax `rcasesPat) := do
  let mut ps : Array (TSyntax `rcasesPat) := #[]
  for j in [0:nvars] do
    ps := ps.push (← `(rcasesPat| $(mkIdent (Name.mkSimple s!"x{j}")):ident))
  ps := ps.push (← `(rcasesPat| he₁)); ps := ps.push (← `(rcasesPat| he₂))
  ps := ps.push (← `(rcasesPat| hww))
  if hasBound then
    ps := ps.push (← `(rcasesPat| ⟨c, hc, hci, hcl⟩))
  if bothFor then ps := ps.push (← `(rcasesPat| hii))
  `(rcasesPat| ⟨$ps,*⟩)

/-- `ts_auto_lockstep`: lockstep with the generated coupling, all three goals closed
automatically (fails, leaving no goals changed, if the automation does not close them). -/
elab "ts_auto_lockstep" : tactic => withMainContext do
  let some (l₁, L₁, w₁, K₁) ← wpLoop? (← getMainTarget)
    | throwError "ts_auto_lockstep: the goal is not `wp (JS.exec loop w) K`"
  let lctx ← getLCtx
  let some hd := lctx.findFromUserName? `hs | throwError "ts_auto_lockstep: no hypothesis hs"
  let some (l₂, L₂, w₂, K₂) ← wpLoop? hd.type
    | throwError "ts_auto_lockstep: hs is not `wp (JS.exec loop w) K`"
  let J ← genCoupling l₁ l₂
  let (sh₁, _, _) ← shapeStx l₁ L₁
  let (sh₂, tm₂, _) ← shapeStx l₂ L₂
  let st₁ ← stInit l₁ w₁; let st₂ ← stInit l₂ w₂
  let K₁s ← Term.exprToSyntax K₁; let K₂s ← Term.exprToSyntax K₂
  let pat (li : LoopInfo) (e w : Name) : TacticM (TSyntax `rcasesPat) := do
    if li.kind == .forOf then `(rcasesPat| ⟨⟨_, $(mkIdent e):ident⟩, $(mkIdent w):ident⟩)
    else `(rcasesPat| ⟨$(mkIdent e):ident, $(mkIdent w):ident⟩)
  let p₁ ← pat l₁ `ae₁ `aw₁; let p₂ ← pat l₂ `ae₂ `aw₂
  -- the pattern of the generated coupling
  let nx := (← ctxSlots l₁.ctx).size - 0
  let _ := nx
  let hasBound := (l₁.kind == .forOf) != (l₂.kind == .forOf)
  let bothFor := l₁.kind == .forOf && l₂.kind == .forOf
  let pJ ← jPattern (← matchedCount l₁ l₂) hasBound bothFor
  let hsI := mkIdent `hs
  evalTactic (← `(tactic| (
    refine EquivLean.wp_loop_rel $sh₁ $sh₂ $tm₂ (R := fun o₁ o₂ => $K₂s o₂ → $K₁s o₁) $J
      (s₁ := $st₁) (s₂ := $st₂) $hsI ?_ ?_ ?_
    · (try dsimp only); ts_auto_close
    · clear $hsI
      rintro $p₁ $p₂ $pJ
      subst_vars
      (try dsimp only at *)
      ts_destruct_vals
      (try ts_auto_simp)
      iterate 4 (all_goals (try (ts_split_if <;> (try ts_auto_simp))))
      all_goals ts_auto_close
    · intro o₁ o₂ h hk; exact h hk)))


set_option hygiene false in
/-- One direction after `ts_start`: the generated lockstep, or the straight-line closer
(`hs : Q o` against the goal `∃ os, Q os ∧ o = os`).  (Not named `ts_auto`: that is StrictTS's
own automation, `StrictTS.Proof.Auto`, which a file may import next to this one.) -/
macro "ts_auto_couple" : tactic => `(tactic| first | ts_auto_lockstep | exact ⟨_, hs, rfl⟩)

/-- `equiv_ts_auto [defs…]`: `equiv_ts [defs…]`, then `ts_auto_couple` on each direction;
directions it does not close are left for a user coupling. -/
syntax (name := equivTsAuto) "equiv_ts_auto" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| equiv_ts_auto) => `(tactic| (equiv_ts <;> try ts_auto_couple))
  | `(tactic| equiv_ts_auto [$ls,*]) => `(tactic| (equiv_ts [$ls,*] <;> try ts_auto_couple))

end EquivLean.TS

import CIR.Logic.Exec
import CIR.Tactic.Simprocs

/-!
  Facts about list elements for the goals left after symbolic execution.

  * `cir_elems` instantiates every hypothesis `h : ∀ x ∈ l, P x` at the
    elements `l[i]` that occur in the goal or the hypotheses (a contract's
    `∀ x ∈ xs, -128 ≤ x ∧ x ≤ 127` about the characters of a string, read at
    a symbolic index by a loop).
  * `cir_unwrap` removes integer conversions `wrap s w x` whose argument is
    known to be in range.
-/

namespace CIR

/-! Conversions of values in range, for `grind` (it does not unfold `intMin`). -/

theorem wrap_s8_self {x : Int} (h0 : -128 ≤ x) (h1 : x ≤ 127) : wrap true 8 x = x :=
  wrap_of_bounds (by decide) (by simp only [intMin_s8, intMax_s8]; omega)
theorem wrap_s16_self {x : Int} (h0 : -32768 ≤ x) (h1 : x ≤ 32767) : wrap true 16 x = x :=
  wrap_of_bounds (by decide) (by simp only [intMin_s16, intMax_s16]; omega)
theorem wrap_s32_self {x : Int} (h0 : -2147483648 ≤ x) (h1 : x ≤ 2147483647) : wrap true 32 x = x :=
  wrap_of_bounds (by decide) (by simp only [intMin_s32, intMax_s32]; omega)
theorem wrap_s64_self {x : Int} (h0 : -9223372036854775808 ≤ x) (h1 : x ≤ 9223372036854775807) :
    wrap true 64 x = x :=
  wrap_of_bounds (by decide) (by simp only [intMin_s64, intMax_s64]; omega)
theorem wrap_u8_self {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 255) : wrap false 8 x = x :=
  wrap_of_bounds (by decide) (by simp only [intMin_u, intMax_u8]; omega)
theorem wrap_u16_self {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 65535) : wrap false 16 x = x :=
  wrap_of_bounds (by decide) (by simp only [intMin_u, intMax_u16]; omega)
theorem wrap_u32_self {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 4294967295) : wrap false 32 x = x :=
  wrap_of_bounds (by decide) (by simp only [intMin_u, intMax_u32]; omega)
theorem wrap_u64_self {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 18446744073709551615) : wrap false 64 x = x :=
  wrap_of_bounds (by decide) (by simp only [intMin_u, intMax_u64]; omega)

end CIR

namespace CIR.Tactic

open Lean Meta Elab Tactic Term

/-- Is `e` a list element access `l[i]` without loose bound variables? -/
def isListGetElem (e : Expr) : Bool :=
  e.isAppOfArity ``GetElem.getElem 8 && !e.hasLooseBVars && (e.getArg! 0).isAppOfArity ``List 1

/-- The list element accesses `l[i]` in `e`, added to `acc` (each shared
subterm is visited once: states are large terms with much sharing). -/
def listGetElems (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
  let r ← IO.mkRef acc
  e.forEachWhere isListGetElem fun t => r.modify fun a => if a.contains t then a else a.push t
  r.get

/-- Is `e` a list element access `l[i]?` without loose bound variables? -/
def isListGetElem? (e : Expr) : Bool :=
  e.isAppOfArity ``GetElem?.getElem? 7 && !e.hasLooseBVars && (e.getArg! 0).isAppOfArity ``List 1

/-- The facts `∀ j : Nat, … l[j]? …` (or `l[j]`) in a hypothesis and its
conjuncts, with their proofs and the list `l`. -/
partial def indexFacts (pf ty : Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``And 2 then
    return (← indexFacts (mkProj ``And 0 pf) (ty.getArg! 0)) ++
      (← indexFacts (mkProj ``And 1 pf) (ty.getArg! 1))
  let .forallE n dom body bi := ty | return #[]
  unless dom.isConstOf ``Nat do return #[]
  -- an access `l[j]?` / `l[j]` in the body, `l` not depending on `j`
  withLocalDecl n bi dom fun j => do
    let b := body.instantiate1 j
    let some acc := b.find? fun e =>
        (e.isAppOfArity ``GetElem?.getElem? 7 || e.isAppOfArity ``GetElem.getElem 8) &&
        (e.getArg! 0).isAppOfArity ``List 1 && e.getArg! 6 == j &&
        !(e.getArg! 5).hasLooseBVars && !(e.getArg! 5).containsFVar j.fvarId!
      | return #[]
    return #[(pf, ty, acc.getArg! 5)]

/-- Instantiate the facts `∀ j : Nat, … l[j]? …` of the hypotheses (loop
invariants: `∀ j < i, a[j]? = some …`) at every index `k` with an access
`l[k]` or `l[k]?` in the goal or the hypotheses. -/
elab "cir_inst_idx" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut facts : Array (Expr × Expr × Expr) := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      facts := facts ++ (← indexFacts d.toExpr (← instantiateMVars d.type))
    if facts.isEmpty then throwError "cir_inst_idx: no index fact"
    let r ← IO.mkRef (#[] : Array Expr)
    let collect (e : Expr) : MetaM Unit :=
      e.forEachWhere (fun t => isListGetElem t || isListGetElem? t) fun t =>
        r.modify fun a => if a.contains t then a else a.push t
    collect (← instantiateMVars (← g.getType))
    for d in ← getLCtx do
      unless d.isImplementationDetail do collect (← instantiateMVars d.type)
    let accs ← r.get
    let mut g := g
    let mut done : Array (Nat × Expr) := #[]
    for (pf, _, l) in facts do
      for (acc, ai) in accs.zipIdx do
        let _ := ai
        unless ← withReducible (isDefEq (acc.getArg! 5) l) do continue
        let k := acc.getArg! 6
        let fi := (facts.findIdx? (fun f => f.1 == pf)).getD 0
        if ← done.anyM (fun (i, k') => do return i == fi && (← withReducible (isDefEq k k'))) then continue
        done := done.push (fi, k)
        let inst := mkApp pf k
        let some ity ← observing? (do let t ← inferType inst; check inst; pure t) | continue
        -- discharge the premises that `omega` proves (the bound `k < l.length`
        -- by the proof carried by `l[k]`)
        let (inst, ity) ← g.withContext do
          let mut inst := inst
          let mut ity ← whnfR ity
          for _ in [0:4] do
            let .forallE _ dom _ _ := ity | break
            let some h ← (do
                if (acc.isAppOfArity ``GetElem.getElem 8) &&
                    (← withReducible (isDefEq dom (← inferType (acc.getArg! 7)))) then
                  return some (acc.getArg! 7)
                omegaProof? dom) | break
            inst := mkApp inst h
            ity ← whnfR (← inferType inst)
          return (inst, ity)
        let (_, g') ← (← g.assert `cirE ity inst).intro1P
        g := g'
    replaceMainGoal [g]

/-- For every element `l[i]` in the goal or the hypotheses: `l[i]? = some l[i]`
(so that `grind` can use facts stated with `l[j]?`, such as a loop
invariant's `∀ j < i, a[j]? = …`), and `P l[i]` for every hypothesis
`∀ x ∈ l, P x`. -/
elab "cir_elems" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    -- hypotheses `∀ x, x ∈ l → P x` (`x ∈ l` is `Membership.mem l x`)
    let mut alls : Array (Expr × Expr) := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let .forallE _ _ body _ := ty | continue
      let .forallE _ mem _ _ := body | continue
      unless mem.isAppOfArity ``Membership.mem 5 && mem.getArg! 4 == .bvar 0 do continue
      let l := mem.getArg! 3
      unless l.hasLooseBVars do alls := alls.push (d.toExpr, l)
    let mut terms : Array Expr ← listGetElems (← instantiateMVars (← g.getType)) #[]
    for d in lctx do
      unless d.isImplementationDetail do
        terms ← listGetElems (← instantiateMVars d.type) terms
    let mut g := g
    for t in terms do
      if let some pf ← observing? (mkAppM ``List.getElem?_eq_getElem #[t.getArg! 7]) then
        let (_, g') ← (← g.assert `cirE (← inferType pf) pf).intro1P
        g := g'
      for (h, l) in alls do
        unless ← withReducible (isDefEq (t.getArg! 5) l) do continue
        let some mem ← observing? (mkAppM ``List.getElem_mem #[t.getArg! 7]) | continue
        let pf := mkApp2 h t mem
        let some pty ← observing? (do let ty ← inferType pf; check pf; pure ty) | continue
        let (_, g') ← (← g.assert `cirE pty pf).intro1P
        g := g'
    replaceMainGoal [g]

/-- Split equations between integer types (`Ty.int true 32 = Ty.int s w`,
left by a load that cases on the type of the value) and substitute. -/
elab "cir_ty_inj" : tactic => do
  let findEq (g : MVarId) : MetaM (Option FVarId) := g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, l, r) := ty.eq? | continue
      if l.isAppOfArity ``CIR.Ty.int 2 && r.isAppOfArity ``CIR.Ty.int 2 then return some d.fvarId
    return none
  let mut g ← getMainGoal
  let mut n := 0
  while n < 8 do
    let some h ← findEq g | break
    match ← Lean.Meta.injection g h with
    | .solved => replaceMainGoal []; return
    | .subgoal g' _ _ => g := g'
    n := n + 1
  if n == 0 then throwError "cir_ty_inj: no equation between integer types"
  replaceMainGoal [g]
  evalTactic (← `(tactic| subst_vars))

/-- A witness for the bound variable (`bvar 0`) from an equation `f … a … =
f … x …` in `e` (under conjunctions): `a`. -/
partial def eqWitness? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``And 2 then (eqWitness? (e.getArg! 0)).orElse fun _ => eqWitness? (e.getArg! 1)
  else if e.isAppOfArity ``Eq 3 then
    let l := e.getArg! 1
    let r := e.getArg! 2
    let pick (x y : Expr) : Option Expr := Id.run do
      -- `x = f … a …`, `y = f … (bvar 0) …`
      unless x.getAppFn == y.getAppFn && x.getAppNumArgs == y.getAppNumArgs && x.getAppNumArgs > 0 do
        return none
      let xs := x.getAppArgs
      let ys := y.getAppArgs
      let mut w : Option Expr := none
      for i in [0:xs.size] do
        if ys[i]! == .bvar 0 && !xs[i]!.hasLooseBVars then w := some xs[i]!
        else if xs[i]! != ys[i]! then return none
      return w
    (pick l r).orElse fun _ => pick r l
  else none

/-- The term `a` at the positions where `y` has the variable `x` and `x`
equal elsewhere (`x` free in `y` only), if consistent. -/
partial def unifyWit (x : Expr) (a y : Expr) : StateT (Option Expr) MetaM Bool := do
  if y == x then
    if a.containsFVar x.fvarId! then return false
    match ← get with
    | some w => return w == a
    | none => set (some a); return true
  if !y.containsFVar x.fvarId! then
    if a == y then return true
    -- proofs are equal (bound proofs of `l[i]` built differently)
    if ← (do return (← isProp (← inferType a)) && (← isProp (← inferType y))) then return true
    return ← withReducible (isDefEq a y)
  match a, y with
  | .app f1 a1, .app f2 a2 => return (← unifyWit x f1 f2) && (← unifyWit x a1 a2)
  | .lam _ t1 b1 _, .lam _ t2 b2 _ => return (← unifyWit x t1 t2) && (← unifyWit x b1 b2)
  | .forallE _ t1 b1 _, .forallE _ t2 b2 _ => return (← unifyWit x t1 t2) && (← unifyWit x b1 b2)
  | .mdata _ a', _ => unifyWit x a' y
  | _, .mdata _ y' => unifyWit x a y'
  | _, _ => return false

/-- A witness for `x` from an equation between a term and the same term
with `x` in `e` (under conjunctions). -/
partial def eqWitnessFV? (x : Expr) (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity ``And 2 then
    if let some w ← eqWitnessFV? x (e.getArg! 0) then return some w
    return ← eqWitnessFV? x (e.getArg! 1)
  if e.isAppOfArity ``Eq 3 then
    let l := e.getArg! 1
    let r := e.getArg! 2
    for (a, y) in [(l, r), (r, l)] do
      if y.containsFVar x.fvarId! && !a.containsFVar x.fvarId! then
        let (ok, w) ← (unifyWit x a y).run none
        if ok then if let some w := w then return some w
  return none

/-- `∃ x, P x` with the witness of an equation `t a = t x` in `P` (an
invariant's existential re-established at the next element:
`listPtr bs (k + 1) = listPtr bs k'`, also with `listPtr` unfolded). -/
elab "cir_exists_inst" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    unless t.isAppOfArity ``Exists 2 do throwError "cir_exists_inst: not an existential"
    let .lam n ty body bi := t.getArg! 1 | throwError "cir_exists_inst: unexpected predicate"
    let w? ← withLocalDecl n bi ty fun x => do
      match ← eqWitnessFV? x (body.instantiate1 x) with
      | some w => return if w.containsFVar x.fvarId! then none else some w
      | none => return none
    let some w := w? | throwError "cir_exists_inst: no witness"
    let wS ← exprToSyntax w
    evalTactic (← `(tactic| refine ⟨$wS, ?_⟩))

macro "cir_unwrap" : tactic => `(tactic|
  simp (disch := first
      | omega
      | (simp only [CIR.intMin_s8, CIR.intMax_s8, CIR.intMin_s16, CIR.intMax_s16, CIR.intMin_s32,
          CIR.intMax_s32, CIR.intMin_s64, CIR.intMax_s64, CIR.intMin_u, CIR.intMax_u8, CIR.intMax_u16,
          CIR.intMax_u32, CIR.intMax_u64]; omega))
    only [CIR.wrap_of_bounds] at *)

end CIR.Tactic

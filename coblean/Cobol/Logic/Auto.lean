/-
# `cobol_auto`: symbolic execution with the facts of the context

`cobol_sym [h₁, …, hₙ]` needs every fact about the symbolic data in its list: the length of
each symbolic byte list, the contents of storage, the results of key lookups, the fields of
file states.  A missing fact leaves an `IF` undecided and can make symbolic execution very
slow (see the README, "How it scales").  `cobol_auto [extra]` is `cobol_sym` plus every
hypothesis of the local context that is a useful rewrite:

* an equation whose left-hand side is an application (`xs.length = 2`, `m.read 956 300 = bs`,
  `Sem.findKey k v l = some i`, `l.getD i [] = r`, `f.mode = some .input`, `rate a c = 0`, …);
  projections of structure literals in it are reduced first;
* a negated equation (`a ≠ b`, `¬ a = b`);
* for a fact `m.read o n = bs`, also `Mem.read_of_read_sub`: every read inside `o ..< o + n`;

and the usual list-length lemmas (`length_encodeNum`, `List.length_append`, `take`/`drop` of
appends).  Left out: quantified hypotheses (`∀ …`, implications) and equations whose left-hand
side is a variable (`accs = pre ++ cur :: post`): pass those explicitly when they are wanted.
Inequalities need no passing: the interval simprocs read them from the context.
-/
import Cobol.Logic.Eval

namespace Cobol
open Lean Meta Elab Tactic

/-- A hypothesis type worth giving to symbolic execution as a rewrite. -/
def autoFact (ty : Lean.Expr) : Bool :=
  if ty.isForall then false
  else
    match ty.eq? with
    | some (_, lhs, _) => lhs.isApp
    | none =>
      match ty.not? with
      | some p => p.isEq
      | none => ty.isAppOfArity ``Ne 3

/-- Reduce projections of structure literals (`{ mem := m, … }.mem` ↦ `m`). -/
def reduceProjs (e : Lean.Expr) : MetaM Lean.Expr := do
  let env ← getEnv
  Meta.transform e (post := fun x => do
    -- the projection function of a structure (not a class: `OfNat.ofNat` must stay) applied
    -- to a constructor application written out
    let .const f _ := x.getAppFn | return .continue
    let some info := env.getProjectionFnInfo? f | return .continue
    if info.fromClass then return .continue
    unless x.getAppNumArgs == info.numParams + 1 do return .continue
    let arg := x.appArg!
    unless arg.getAppFn.isConstOf info.ctorName do return .continue
    let some y ← Meta.reduceProjOf? x (fun _ => true) | return .continue
    let some z ← Meta.reduceProj? y | return .continue
    return .visit z)

/-- Debugging: a step limit for the simp calls of `cobol_auto`/`cobol_simp_facts` (0: their
own).  With `trace.Meta.Tactic.simp.rewrite`, a run that does not end shows what simp was doing
when it stopped. -/
register_option cobol.debugMaxSteps : Nat := {
  defValue := 0
  descr := "step limit for cobol_auto's simp (debugging; 0 = default)"
}

syntax "cobol_auto" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
/-- `cobol_auto` that reports the facts it used and those it left out. -/
syntax "cobol_auto?" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

/-- The simp call `stx` with the facts of the main goal's context added (`dropInner`: leave out
a fact whose left-hand side occurs inside another's; `normalize`: also add each equation with
its left-hand side simplified by the same simp set, so that facts and goal are in the same
normal form).  The result can be run on every goal with that context. -/
def factSimp (stx : Syntax) (dropInner report normalize : Bool) : TacticM MkSimpContextResult := do
  let stx ← liftMacroM <| expandMacros stx
  withMainContext do
  let r ← mkSimpContext stx (eraseLocal := false)
  let mut facts : Array (FVarId × Lean.Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    unless autoFact ty do continue
    facts := facts.push (d.fvarId, ← reduceProjs ty)
  -- a fact whose left-hand side occurs strictly inside another's would rewrite the other's
  -- pattern first (simp works bottom-up): keep the more specific one
  let lhsOf (t : Lean.Expr) : Lean.Expr := match t.eq? with
    | some (_, l, _) => l
    | none => t
  let mut thms := r.ctx.simpTheorems
  let mut used : Array Lean.Expr := #[]
  let mut dropped : Array Lean.Expr := #[]
  for (h, ty) in facts do
    let l := lhsOf ty
    if dropInner && l.isApp && facts.any (fun (h', ty') => h' != h && lhsOf ty' != l &&
        ((lhsOf ty').find? (· == l)).isSome) then
      dropped := dropped.push (mkFVar h)
      continue
    used := used.push (mkFVar h)
    -- unchanged types: the hypothesis itself (as `simp [h]` adds it)
    let mut pf ← if ty == (← instantiateMVars (← h.getType)) then pure (mkFVar h)
      else mkExpectedTypeHint (mkFVar h) ty
    thms ← thms.addTheorem (.fvar h) pf (config := r.ctx.indexConfig)
    -- the left-hand side in the simp set's normal form too (only the left-hand side: simplifying
    -- the whole fact can turn `l = []` into `∀ x ∈ l, …`, which rewrites nothing)
    if normalize then
      if let some (_, l, rhs) := ty.eq? then
        let (res, _) ← Meta.simp l r.ctx r.simprocs
        if let some p := res.proof? then
          unless res.expr == rhs do
            thms ← thms.addTheorem (.fvar h) (← mkEqTrans (← mkEqSymm p) pf)
              (config := r.ctx.indexConfig)
    if l.isAppOfArity ``Mem.read 3 then
      let sub ← mkAppM ``Mem.read_of_read_sub #[pf]
      thms ← thms.addTheorem (.fvar h) sub (config := r.ctx.indexConfig)
  if report then
    logInfo m!"cobol_auto uses {used}\nleaves out (inside another fact's left-hand side) {dropped}"
  let mut ctx := r.ctx.setSimpTheorems thms
  let steps := cobol.debugMaxSteps.get (← getOptions)
  if steps != 0 then
    ctx ← ctx.setConfig { ctx.config with maxSteps := steps }
  return { r with ctx }

/-- Run a `factSimp` result on the main goal. -/
def runFactSimp (r : MkSimpContextResult) : TacticM Unit := withMainContext do
  _ ← r.dischargeWrapper.with fun discharge? =>
    simpLocation r.ctx r.simprocs discharge? (Location.targets #[] true)

def simpLemmas (xs? : Option (Syntax.TSepArray ``Lean.Parser.Tactic.simpLemma ",")) :
    Array (TSyntax ``Lean.Parser.Tactic.simpLemma) :=
  match xs? with
  | some xs => xs.getElems
  | none => #[]

/-- `cobol_auto [l…]` as a `factSimp`. -/
def autoSimp (ls : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) (report : Bool := false) :
    TacticM MkSimpContextResult := do
  factSimp (← `(tactic| cobol_sym [length_encodeNum, List.length_append, List.take_append,
    List.drop_append, List.take_of_length_le, List.drop_of_length_le, $ls,*])) true report false

/-- `cobol_simp_facts [l…]` as a `factSimp`. -/
def factsSimp (ls : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) : TacticM MkSimpContextResult := do
  factSimp (← `(tactic| simp [-List.getD_eq_getElem?_getD, length_encodeNum, NumFmt.byteLen,
    Config.binBytes, List.length_append, List.take_append, List.drop_append, List.take_of_length_le,
    List.drop_of_length_le, $ls,*]))
    false false true

elab_rules : tactic
  | `(tactic| cobol_auto $[[$xs?,*]]?) => do runFactSimp (← autoSimp (simpLemmas xs?))
  | `(tactic| cobol_auto? $[[$xs?,*]]?) => do runFactSimp (← autoSimp (simpLemmas xs?) true)

/-- `simp [l…]` with every fact of the context (equations also with their left-hand side
simplified the same way), the list lemmas of `cobol_auto` (lengths, `take`/`drop` of appends:
both sides of a goal must reach the same normal form), and without
`List.getD_eq_getElem?_getD`: the symbolic states and the case facts use `List.getD` (the file
model reads records with it), and rewriting a goal's `getD` first would make those facts miss.
For the parts of a goal that symbolic execution leaves to general list reasoning (lengths,
`flatMap`, `filterMap`, `reverse`). -/
syntax "cobol_simp_facts" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cobol_simp_facts $[[$xs?,*]]?) => do runFactSimp (← factsSimp (simpLemmas xs?))

/-! ## `cobol_inv`: restating a loop invariant

After symbolic execution of one loop iteration, the goal is the invariant of the new state.
Most of it is mechanical: file states found by unification, counters and flags that simplify,
facts that are hypotheses.  `cobol_inv [l₁, …] with w₁, …, wₙ` splits the goal: a conjunction
into both parts, an existential into its body with the next witness `wᵢ` (in the order the
existentials occur; `_`, or no witness left, means a metavariable, assigned when a later part
is proved by `rfl`, as `st.files = [(1, f₁), …]` does), a disjunction into one side.  Each part
is reduced to the state component it is about (`dsimp only`), then closed by `rfl` or an
assumption (both with reducible transparency only: unfolding memory operations on symbolic
storage takes too long), `cobol_auto [l…]` (then `decide +kernel` if the goal left is ground),
`cobol_simp_facts [l…]` (then `omega`), or both in turn (then `omega`).  The two simp calls are
prepared once for all parts.  A side of a disjunction is refuted when one of its parts
simplifies to `False` (the rest of that side is then skipped); the side taken is the first one
whose parts all close, else the one not refuted, else the one with fewer parts left.  Parts that
do not close are left as goals, in order. -/

/-- `decide +kernel` on a goal without free variables or metavariables (fails otherwise). -/
elab "cobol_decide_ground" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  if t.hasFVar || t.hasMVar then throwError "cobol_decide_ground: the goal is not ground"
  evalTactic (← `(tactic| decide +kernel))

/-- The outcome of splitting: parts left open, witnesses not used, refuted. -/
abbrev InvOut := List MVarId × List Term × Bool

/-- Run `tac` on `g`; the goals it leaves, or `none` (state restored) if it fails. -/
def invTry (tac : TacticM Unit) (g : MVarId) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  try
    setGoals [g]
    tac
    return some (← getUnsolvedGoals)
  catch _ =>
    s.restore
    return none

/-- Close a part of an invariant; `([g], ws, true)` if it simplifies to `False`. -/
def invLeaf (auto facts : MkSimpContextResult) (g : MVarId) (ws : List Term) : TacticM InvOut := do
  let g ← match ← invTry (do evalTactic (← `(tactic| dsimp only))) g with
    | some [g'] => pure g'
    | some [] => return ([], ws, false)
    | _ => pure g
  let s0 ← saveState
  for tac in [← `(tactic| with_reducible rfl), ← `(tactic| with_reducible assumption)] do
    if let some [] ← invTry (evalTactic tac) g then return ([], ws, false)
    s0.restore
  let closes (tac : TacticM Unit) (g : MVarId) : TacticM Bool := do
    let s ← saveState
    if let some [] ← invTry tac g then return true
    s.restore
    return false
  let decideG ← `(tactic| cobol_decide_ground)
  let omegaT ← `(tactic| omega)
  -- symbolic execution
  let mut afterAuto : Option (MVarId × Tactic.SavedState) := none
  match ← invTry (runFactSimp auto) g with
  | some [] => return ([], ws, false)
  | some [g1] =>
    if ← closes (evalTactic decideG) g1 then return ([], ws, false)
    afterAuto := some (g1, ← saveState)
  | _ => pure ()
  s0.restore
  -- general simplification with the facts
  match ← invTry (runFactSimp facts) g with
  | some [] => return ([], ws, false)
  | some [g2] =>
    if (← instantiateMVars (← g2.getType)).isConstOf ``False then
      s0.restore
      return ([g], ws, true)
    if ← closes (evalTactic omegaT) g2 then return ([], ws, false)
  | _ => pure ()
  -- both in turn
  if let some (g1, s1) := afterAuto then
    s1.restore
    match ← invTry (runFactSimp facts) g1 with
    | some [] => return ([], ws, false)
    | some [g3] => if ← closes (evalTactic omegaT) g3 then return ([], ws, false)
    | _ => pure ()
  s0.restore
  return ([g], ws, false)

/-- Split an invariant goal, giving its existentials the witnesses `ws` in order, and close
its parts with `invLeaf`. -/
partial def invSplit (auto facts : MkSimpContextResult) (g : MVarId) (ws : List Term) :
    TacticM InvOut := do
  if ← g.isAssigned then return ([], ws, false)
  let ty ← g.withContext do whnfD (← instantiateMVars (← g.getType))
  let splitAll (gs : List MVarId) (ws : List Term) : TacticM InvOut := do
    let mut rest := []
    let mut ws := ws
    for g' in gs do
      let (r, ws', refuted) ← invSplit auto facts g' ws
      if refuted then return (rest ++ r, ws', true)
      rest := rest ++ r
      ws := ws'
    return (rest, ws, false)
  let intro (ws : List Term) : TacticM (List MVarId) := g.withContext do
    match ws with
    | w :: _ =>
      unless w.raw.isOfKind ``Lean.Parser.Term.hole do
        setGoals [g]
        evalTactic (← `(tactic| refine ⟨$w, ?_⟩))
        return ← getGoals
    | [] => pure ()
    g.apply (← mkConstWithFreshMVarLevels ``Exists.intro)
  if ty.isAppOfArity ``Exists 2 then
    splitAll (← intro ws) ws.tail
  else if ty.isAppOfArity ``And 2 then
    splitAll (← g.withContext do g.apply (mkConst ``And.intro)) ws
  else if ty.isAppOfArity ``Or 2 then
    let s0 ← saveState
    let mut outs : Array (InvOut × Tactic.SavedState) := #[]
    for side in [``Or.inl, ``Or.inr] do
      s0.restore
      let out ← try splitAll (← g.withContext do g.apply (mkConst side)) ws
        catch _ => pure ([g], ws, true)
      if out.1.isEmpty && !out.2.2 then return out
      outs := outs.push (out, ← saveState)
    let pick : Option (InvOut × Tactic.SavedState) :=
      match outs[0]?, outs[1]? with
      | some l, some r =>
        if l.1.2.2 && r.1.2.2 then none
        else if l.1.2.2 then some r
        else if r.1.2.2 then some l
        else if r.1.1.length < l.1.1.length then some r else some l
      | _, _ => none
    match pick with
    | some (out, st) => st.restore; return out
    | none => s0.restore; return ([g], ws, true)
  else
    invLeaf auto facts g ws

syntax "cobol_inv" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (" with " term,+)? : tactic

elab_rules : tactic
  | `(tactic| cobol_inv $[[$xs?,*]]? $[with $ws?,*]?) => withMainContext do
    let ls := simpLemmas xs?
    let ws : List Term := match ws? with
      | some ws => ws.getElems.toList
      | none => []
    let auto ← autoSimp ls
    let facts ← factsSimp ls
    let g :: gs ← getGoals | throwError "cobol_inv: no goals"
    let (rest, ws', _) ← invSplit auto facts g ws
    unless ws'.isEmpty do
      logWarning m!"cobol_inv: {ws'.length} witness(es) not used"
    setGoals (rest ++ gs)

end Cobol

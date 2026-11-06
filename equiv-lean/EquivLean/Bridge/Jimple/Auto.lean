import EquivLean.Bridge.Jimple.Align

/-!
# Jimple bridge: automatic relational products (Java ≡ Java)

Two tactics over the product of `Bridge/Jimple/Rel.lean`.

**`jprod_vc [defs]`** proves `ProdVC P₁ b₁ P₂ b₂ pairs R d fuel₁ fuel₂` from the pairs and their
couplings alone (`pairs` must unfold to an explicit list of `(pc₁, pc₂, J)`).  For each pair:
the coupling `J` is unfolded in the hypotheses only; the target body runs under `jvc` with the
source's halves (`tgtAssert …`, `tgtPost …`) left folded; each leaf of the target's symbolic
execution (one per pair and target path) is then a separate goal, the source's obligation for
that path over the pair's source frame and heap, executed existentially by `jvc` with
`jbodyEWP`.  `defs` are unfolded in the hypotheses and in the source goals (predicates used by
the couplings or the context, a user outcome relation).  Two measurements on `PrDiffStats`
fixed the design: unfolding the couplings in the target goal itself, where they also occur
inside `tgtAssert … pairs …`, made the target's execution about three times slower (this is
the slowdown the manual proofs avoided by generalizing `tgtAssert`/`tgtPost`; unfolding them in
the hypotheses only avoids it without generalizing); unfolding `IsWrong` in the main source
pass made kernel checking about twenty times slower, so it is unfolded only in the goals left
over that mention it.  The whole call runs with `jvc`'s heartbeat budget (`jimple.maxHeartbeats`,
unlimited by default), since the symbolic executions would otherwise use up the declaration's.

**`equiv_jimple [defs]`** proves `Sim R (Call.mk P₁ m₁ args σ) (Call.mk P₂ m₂ args σ)`, or
`Equiv R …` (both directions), for two methods whose loops correspond one to one, with nothing
written:
1. user predicates of the hypotheses (`userPredDefs`: definitions of the current file or of
   non-library modules, e.g. a precondition on the array argument) and `defs` are unfolded;
2. `Align.analyze` (compiled code, JimpleLean's interpreter) pairs the loop heads in order, runs
   both methods on sampled arguments and keeps the facts that hold at every aligned visit of the
   heads (`Bridge/Jimple/Align.lean`); samples whose visits do not align are left out, and
   samples on which the runs end differently are reported with a failure (as counterexamples
   when `R` is equality; only the first candidate is tried then);
3. the couplings: at entry `(0, 0)`, the calls' entry frames and their common entry state; at
   the k-th pair of loop heads,
   * `σ₁ = σ₂`, and `σ₁ = σ` (the entry state, so the hypotheses on it apply) when no statement
     up to and inside the loop writes the heap;
   * `fr.get x = some v` for entry values: an argument, a constant, or the length of an array
     argument `.ref a` as `.int (BitVec.ofNat 32 xs.length)`, with
     `σ₁.heap a = some (.array t xs)` bound outermost;
   * `∃ v, fr₁.get x₁ = some (.int v) ∧ fr₂.get x₂ = some (.int v)` for locals equal across the
     sides (`.long`, `.ref`, any value alike), with the bounds `0 ≤ v.toInt ≤ xs.length`;
   each coupling is an auxiliary definition `<theorem>._jcplN` over the context variables it
   mentions, so that it stays one constant inside `tgtAssert … pairs …`;
4. `sim_of_prodVC` with the analysis's exploration fuels and inlining depth, the entry coupling
   by `rfl`, the product by `jprod_vc`;
5. if the product is not closed, weaker candidates follow: without the bounds, then also
   without the constants of locals the loops assign.  Each attempt stops at its first open
   leaf, and each `jvc` call in it gets `jimple.maxHeartbeats` (400000 unless set; the calls of
   the demos use at most about 60000).

Limits: the same number of loops on both sides, paired in order and run in lockstep (the same
number of iterations); the same arguments and entry state on both sides; couplings within the
grammar above (a loop that writes the heap gets `σ₁ = σ₂` only, no facts on the heap's
contents); samples are not filtered by the statement's precondition; parameters of the types
`Align.sampleArg` supports.  `set_option equiv_jimple.trace true` logs the analysis and the
product goals (and stops at the first candidate).
-/

open Jimple

namespace EquivLean.Jimple

open Lean Meta Elab Tactic

/-! ## Stage 1: the product's verification conditions from given pairs and couplings -/

register_option equiv_jimple.trace : Bool := {
  defValue := false
  descr := "log the analysis and the product goals of equiv_jimple / jprod_vc" }

/-- The elements of `e` as an explicit list literal, unfolding head constants on the way (the
names unfolded are returned too). -/
partial def explicitList (e : Lean.Expr) (acc : Array Name := #[]) :
    MetaM (Option (Array Lean.Expr × Array Name)) := do
  let e := (← instantiateMVars e).headBeta.consumeMData
  if e.isAppOfArity ``List.nil 1 then return some (#[], acc)
  if e.isAppOfArity ``List.cons 3 then
    match ← explicitList e.appArg! acc with
    | some (xs, acc') => return some (#[e.appFn!.appArg!] ++ xs, acc')
    | none => return none
  match e.getAppFn with
  | .const c _ =>
    match ← unfoldDefinition? e with
    | some e' => explicitList e' (if acc.contains c then acc else acc.push c)
    | none => return none
  | _ => return none

/-- `simp only [names]` at every hypothesis that mentions one of `names` (never at the goal: in a
product goal the couplings also occur inside the source's `tgtAssert … pairs …`, where unfolding
them only slows symbolic execution down). -/
def unfoldInHyps (names : Array Name) : TacticM Unit := do
  if names.isEmpty then return
  let g ← getMainGoal
  let fvs ← g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ← isProp ty do continue
      if (ty.find? fun t => match t with | .const c _ => names.contains c | _ => false).isSome then
        out := out.push d.fvarId
    return out
  if fvs.isEmpty then return
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  let stx ← `(tactic| simp (config := { failIfUnchanged := false }) only [$lemmas,*])
  let r ← g.withContext do
    let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
    let (r, _) ← simpGoal g ctx simprocs (simplifyTarget := false) (fvarIdsToSimp := fvs)
    return r
  match r with
  | none => replaceMainGoal []
  | some (_, g') => replaceMainGoal [g']

/-- Split a goal that is a conjunction into its conjuncts (right-nested). -/
partial def splitAnds (g : MVarId) : MetaM (List MVarId) := do
  let t ← whnfR (← instantiateMVars (← g.getType))
  if t.isAppOfArity ``And 2 then
    let gs ← g.apply (mkConst ``And.intro)
    let mut out := []
    for g' in gs do out := out ++ (← splitAnds g')
    return out
  return [g]

/-- A target leaf that is the source's half of the product: `tgtAssert …` (the target reached a
cut point) or `tgtPost …` (the target finished). -/
def isSourceLeaf (g : MVarId) : MetaM Bool := do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  return t.isAppOf ``tgtAssert || t.isAppOf ``tgtPost

/-- Run a tactic on one goal; the goals it leaves. -/
def onGoal (g : MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  setGoals [g]
  tac
  getGoals

/-- Field lookups in literal field lists (objects described by a hypothesis), for `jvc`. -/
theorem fields_get_cons (k k' : FieldKey) (v : Value) (fs : List (FieldKey × Value)) :
    Fields.get ((k, v) :: fs) k' = if k' = k then some v else Fields.get fs k' := by
  simp only [Fields.get, List.lookup]
  split <;> simp_all

theorem fields_get_nil (k' : FieldKey) : Fields.get [] k' = none := rfl

/-- `jvc [ids]` on the main goal; with `equiv_jimple.trace`, the heartbeats it used are logged. -/
def jvcLogged (ids : Array Ident) (what : String) : TacticM Unit := do
  let h0 ← IO.getNumHeartbeats
  evalTactic (← `(tactic| jvc [$ids,*]))
  if equiv_jimple.trace.get (← getOptions) then
    logInfo m!"jprod_vc: {what}: {((← IO.getNumHeartbeats) - h0) / 1000} k heartbeats, {(← getGoals).length} goal(s) left"

/-- The product proof of one pair: target goal `bodyWP P₁ … (cuts of tgtAssert …) (tgtPost …)`
under the coupling `hJ`.  The target is executed by `jvc` with the source's halves left folded;
each leaf is then a separate goal, the source's obligation for that target path, executed
existentially by `jvc` with `jbodyEWP`.  Returns the goals left open; with `failFast`, throws
at the first one instead. -/
def jprodPair (g : MVarId) (unfold srcExtra : Array Name) (failFast : Bool) :
    TacticM (List MVarId) := do
  let (_, g) ← g.introN 5
  let fieldIds : Array Ident := #[mkCIdent ``fields_get_cons, mkCIdent ``fields_get_nil]
  let gs ← onGoal g do
    unfoldInHyps unfold
    if (← getGoals).isEmpty then return
    jvcLogged fieldIds "target"
  let srcIds : Array Ident := (#[``jbodyEWP, ``bodyEWPStep, ``ewpR_ret, ``srcCuts, ``PairRel,
    ``RelO, ``List.map_cons, ``List.map_nil, ``List.lookup, ``List.mem_cons,
    ``List.mem_nil_iff, ``fields_get_cons, ``fields_get_nil] ++ srcExtra).map mkCIdent
  let failOn (gs : List MVarId) (what : String) : TacticM Unit := do
    if failFast && !gs.isEmpty then
      throwError "jprod_vc: {what} not closed:\n{goalsToMessageData gs}"
  let mut out := []
  for g' in gs do
    unless ← isSourceLeaf g' do
      failOn [g'] "a target leaf"
      out := out ++ [g']
      continue
    let rest ← onGoal g' do
      evalTactic (← `(tactic| simp only [EquivLean.Jimple.tgtAssert, EquivLean.Jimple.tgtPost]))
      if (← getGoals).isEmpty then return
      jvcLogged srcIds "source"
    -- a source path that ends before the paired cut point: `IsWrong o` (unfolding `IsWrong`
    -- in the main pass makes the proof terms much harder for the kernel)
    for r in rest do
      let mentions := ((← instantiateMVars (← r.getType)).find? fun t =>
        t.isConstOf ``IsWrong).isSome
      let left ← if mentions then onGoal r do
          evalTactic (← `(tactic| simp only [EquivLean.Jimple.IsWrong]))
          if (← getGoals).isEmpty then return
          jvcLogged fieldIds "source end"
        else pure [r]
      failOn left "a source leaf"
      out := out ++ left
  return out

/-- The pairs of a `ProdVC` goal, its couplings (head constants) and the constants unfolded to
reach the explicit list. -/
def prodPairs (tgt : Lean.Expr) : MetaM (Array Lean.Expr × Array Name × Array Name) := do
  unless tgt.isAppOfArity ``ProdVC 9 do throwError "jprod_vc: the goal is not `ProdVC …`"
  let some (elems, pairsNames) ← explicitList (tgt.getArg! 4)
    | throwError "jprod_vc: the pairs do not unfold to an explicit list"
  let mut cpl : Array Name := #[]
  for el in elems do
    let el := el.consumeMData
    unless el.isAppOfArity ``Prod.mk 4 && el.appArg!.isAppOfArity ``Prod.mk 4 do
      throwError "jprod_vc: a pair is not an explicit triple (pc₁, pc₂, J): {el}"
    if let some c := el.appArg!.appArg!.getAppFn.constName? then
      unless cpl.contains c do cpl := cpl.push c
  return (elems, cpl, pairsNames)

/-- `jprod_vc [defs]`: prove `ProdVC P₁ b₁ P₂ b₂ pairs R d fuel₁ fuel₂` when `pairs` unfolds to
an explicit list of `(pc₁, pc₂, J)`.  The couplings `J` are unfolded in the hypotheses, `defs`
(predicates used by the couplings or the context, a user outcome relation) in the hypotheses and
in the source's goals.  Fails, listing the open goals, if a leaf is not closed (with
`failFast`, at the first one). -/
def jprodVC (defs : Array Name) (failFast : Bool := false) : TacticM Unit := do
  let g ← getMainGoal
  let (_, cpl, pairsNames) ← prodPairs (← instantiateMVars (← g.getType))
  -- (one array spliced whole: an empty splice inside a list breaks the lemmas after it)
  let lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    (#[``ProdVC] ++ pairsNames ++ #[``List.forall_mem_cons, ``List.not_mem_nil, ``false_implies,
      ``implies_true, ``and_true, ``tgtCuts, ``List.map_cons, ``List.map_nil]).mapM fun n =>
        `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  let gs ← onGoal g do
    evalTactic (← `(tactic| simp only [$lemmas,*]))
  if equiv_jimple.trace.get (← getOptions) then
    logInfo m!"jprod_vc: pairs split into\n{goalsToMessageData gs}"
  let mut open_ := []
  for g' in gs do
    for gp in ← splitAnds g' do
      open_ := open_ ++ (← jprodPair gp (cpl ++ defs) (cpl ++ defs ++ pairsNames) failFast)
  setGoals open_
  unless open_.isEmpty do
    throwError "jprod_vc: {open_.length} goal(s) not closed:\n{goalsToMessageData open_}"

/-- `jprod_vc [defs]`: prove a `ProdVC` goal from its pairs and couplings (module documentation). -/
syntax (name := jprodVCTac) "jprod_vc" (" [" ident,* "]")? : tactic

@[tactic jprodVCTac] def evalJprodVC : Tactic := fun stx => do
  let ids := Jimple.optIdents stx[1]
  let defs ← ids.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  -- the heartbeat budget of `jvc` (`jimple.maxHeartbeats`, default unlimited) for the whole call:
  -- the symbolic executions would otherwise exhaust the declaration's budget, and the glue code
  -- between them would time out
  withJimpleHeartbeats (jprodVC defs)

/-! ## Stage 2: generated pairs and couplings -/

unsafe def evalAnalysisImpl (e : Lean.Expr) : MetaM (Except String Align.Analysis) :=
  Meta.evalExpr (Except String Align.Analysis)
    (mkApp2 (mkConst ``Except [Level.zero, Level.zero]) (mkConst ``String) (mkConst ``Align.Analysis)) e

/-- Evaluate `Align.analyze …` (compiled code: JimpleLean's interpreter on sampled inputs). -/
@[implemented_by evalAnalysisImpl]
opaque evalAnalysis (e : Lean.Expr) : MetaM (Except String Align.Analysis)

/-- The body constant of a method reference: `m.decl.body` reduced to `some b`. -/
def methodBody (m : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnfD (mkApp (mkConst ``MethodDecl.body) (mkApp (mkConst ``MethodRef.decl) m))
  let e ← instantiateMVars e
  if e.isAppOfArity ``Option.some 2 then return e.appArg!
  throwError "equiv_jimple: cannot compute the body of {m}"

/-- Modules whose definitions are library, not user predicates. -/
def libraryRoots : List Name :=
  [`Init, `Lean, `Std, `Jimple, `Mathlib, `Aeneas, `Batteries, `Qq, `Aesop, `EquivLean.Core,
   `EquivLean.Repr, `EquivLean.Tactic, `EquivLean.Bridge]

/-- Head constants of hypotheses that are user predicates (Prop-valued definitions of the
current file or of a module outside `libraryRoots`, such as a precondition), to be unfolded
before the product is built. -/
def userPredDefs : TacticM (Array Name) := withMainContext do
  let env ← getEnv
  let mut out := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    for c in ty.getUsedConstants do
      if out.contains c then continue
      let user := match env.getModuleIdxFor? c with
        | none => true
        | some i =>
          let m := env.header.moduleNames[i.toNat]!
          !libraryRoots.any (·.isPrefixOf m)
      unless user do continue
      if let some (.defnInfo dv) := env.find? c then
        let isPred ← forallTelescopeReducing dv.type fun _ body => return body.isProp
        if isPred then out := out.push c
  return out

/-- A Nat literal as syntax. -/
def natStx (n : Nat) : Term := Syntax.mkNumLit (toString n)

/-- An `int`/`long`/`null` constant value as syntax (other constants are not generated). -/
def valueStx? (v : Value) : Option (TacticM Term) :=
  match v with
  | .int x => some do
    let i := x.toInt
    if i ≥ 0 then `(Jimple.Value.int (BitVec.ofInt 32 $(natStx i.toNat)))
    else `(Jimple.Value.int (BitVec.ofInt 32 (- $(natStx (-i).toNat))))
  | .long x => some do
    let i := x.toInt
    if i ≥ 0 then `(Jimple.Value.long (BitVec.ofInt 64 $(natStx i.toNat)))
    else `(Jimple.Value.long (BitVec.ofInt 64 (- $(natStx (-i).toNat))))
  | .null => some `(Jimple.Value.null)
  | _ => none

/-- The generated coupling of one pair of loop heads (see the module documentation). `args`
are the call's (common) arguments, `σE` its entry state. -/
def couplingStx (hf : Align.HeadFacts) (args : Array Lean.Expr) (σE : Lean.Expr) : TacticM Term := do
  let fr₁ := mkIdent `fr₁; let σ₁ := mkIdent `σ₁; let fr₂ := mkIdent `fr₂; let σ₂ := mkIdent `σ₂
  let frOf (side : Nat) : Ident := if side == 1 then fr₁ else fr₂
  let argStx (i : Nat) : TacticM (Option Term) := do
    match args[i]? with
    | some a => return some (← Term.exprToSyntax a)
    | none => return none
  -- the address of an array argument (`Value.ref A`)
  let addrOf (i : Nat) : TacticM (Option Term) := do
    match args[i]? with
    | some a =>
      let a := (← instantiateMVars a).consumeMData
      if a.isAppOfArity ``Value.ref 1 then return some (← Term.exprToSyntax a.appArg!)
      else return none
    | none => return none
  let xsOf (i : Nat) : Ident := mkIdent (Name.mkSimple s!"xs{i}")
  -- entry values: locals of both sides; an equality whose one side has an entry value gives the
  -- other side the same entry value
  let mut entries : Array (Nat × Nat × Align.Feature) := #[]
  for (x, f) in hf.entry₁ do entries := entries.push (1, x, f)
  for (x, f) in hf.entry₂ do entries := entries.push (2, x, f)
  for (x₁, x₂, _) in hf.eqs do
    match hf.entry₁.lookup x₁, hf.entry₂.lookup x₂ with
    | some f, none => entries := entries.push (2, x₂, f)
    | none, some f => entries := entries.push (1, x₁, f)
    | _, _ => pure ()
  let hasEntry (side x : Nat) : Bool := entries.any fun (s, y, _) => s == side && y == x
  -- arrays whose length is used
  let mut arrs : Array Nat := #[]
  for (_, _, f) in entries do
    if let .len i := f then unless arrs.contains i do arrs := arrs.push i
  for (_, _, i) in hf.bounds do unless arrs.contains i do arrs := arrs.push i
  let mut arrOk : Array Nat := #[]
  for i in arrs do
    if (← addrOf i).isSome then arrOk := arrOk.push i
  let mut facts : Array Term := #[← `($σ₁ = $σ₂)]
  if hf.heapEntry then facts := facts.push (← `($σ₁ = $(← Term.exprToSyntax σE)))
  for (side, x, f) in entries do
    let fr := frOf side
    match f with
    | .arg i =>
      if let some a ← argStx i then facts := facts.push (← `(Jimple.Frame.get $fr $(natStx x) = some $a))
    | .const v =>
      if let some mk := valueStx? v then facts := facts.push (← `(Jimple.Frame.get $fr $(natStx x) = some $(← mk)))
    | .len i =>
      if arrOk.contains i then
        facts := facts.push
          (← `(Jimple.Frame.get $fr $(natStx x) = some (Jimple.Value.int (BitVec.ofNat 32 (List.length $(xsOf i))))))
  -- the arrays bounding local `x` of `side`, and the bounds of a witness `v` by arrays `is`
  let boundArrs (side x : Nat) : List Nat :=
    hf.bounds.filterMap fun (s, y, i) => if s == side && y == x && arrOk.contains i then some i else none
  let boundsOf (is : List Nat) (v : Ident) : TacticM (Array Term) :=
    is.eraseDups.toArray.mapM fun i =>
      `(0 ≤ BitVec.toInt $v ∧ BitVec.toInt $v ≤ ((List.length $(xsOf i) : Nat) : Int))
  let conj (ts : Array Term) : TacticM Term := do
    if ts.isEmpty then return ← `(True)
    let mut acc := ts.back!
    for t in ts.pop.reverse do acc ← `($t ∧ $acc)
    return acc
  -- equalities across the sides (locals without entry values), with their bounds
  let mut nv := 0
  let mut bounded : Array (Nat × Nat) := #[]
  for (x₁, x₂, k) in hf.eqs do
    if hasEntry 1 x₁ || hasEntry 2 x₂ then continue
    let v := mkIdent (Name.mkSimple s!"v{nv}")
    nv := nv + 1
    let (ty, mk) ← match k with
      | .int => pure (← `(Jimple.I32), fun (v : Ident) => `(Jimple.Value.int $v))
      | .long => pure (← `(Jimple.I64), fun (v : Ident) => `(Jimple.Value.long $v))
      | .ref => pure (← `(Jimple.Addr), fun (v : Ident) => `(Jimple.Value.ref $v))
      | .any => pure (← `(Jimple.Value), fun (v : Ident) => `($v))
    let val ← mk v
    let bs ← if k == .int then boundsOf (boundArrs 1 x₁ ++ boundArrs 2 x₂) v else pure #[]
    if !bs.isEmpty then bounded := bounded ++ #[(1, x₁), (2, x₂)]
    let body ← conj (#[← `(Jimple.Frame.get $fr₁ $(natStx x₁) = some $val),
      ← `(Jimple.Frame.get $fr₂ $(natStx x₂) = some $val)] ++ bs)
    facts := facts.push (← `(∃ $v:ident : $ty, $body))
  -- bounds of the other `int` locals (no entry value, no partner)
  for (side, x, _) in hf.bounds do
    if hasEntry side x || bounded.contains (side, x) then continue
    let v := mkIdent (Name.mkSimple s!"v{nv}")
    nv := nv + 1
    bounded := bounded.push (side, x)
    let bs ← boundsOf (boundArrs side x) v
    if bs.isEmpty then continue
    let body ← conj (#[← `(Jimple.Frame.get $(frOf side) $(natStx x) = some (Jimple.Value.int $v))] ++ bs)
    facts := facts.push (← `(∃ $v:ident : Jimple.I32, $body))
  -- the arrays, outermost
  let mut body ← conj facts
  for i in arrOk.reverse do
    let some a ← addrOf i | continue
    let t := mkIdent (Name.mkSimple s!"t{i}")
    body ← `(∃ $t:ident : Jimple.JType, ∃ $(xsOf i):ident : List Jimple.Value,
      Jimple.State.heap $σ₁ $a = some (Jimple.Obj.array $t $(xsOf i)) ∧ $body)
  `(fun ($fr₁ : Jimple.Frame) ($σ₁ : Jimple.State) ($fr₂ : Jimple.Frame) ($σ₂ : Jimple.State) => $body)

/-- The entry coupling: the entry frames of the two calls and their (common) entry state. -/
def entryCouplingStx (s₁ s₂ : Bool) (args σE : Lean.Expr) : TacticM Term := do
  let b (s : Bool) : TacticM Term := if s then `(true) else `(false)
  let a ← Term.exprToSyntax args
  let σ ← Term.exprToSyntax σE
  `(fun (fr₁ : Jimple.Frame) (σ₁ : Jimple.State) (fr₂ : Jimple.Frame) (σ₂ : Jimple.State) =>
      fr₁ = Jimple.Frame.init $(← b s₁) $a ∧ fr₂ = Jimple.Frame.init $(← b s₂) $a ∧
        σ₁ = $σ ∧ σ₂ = $σ)

/-- A fresh name `base_jcplN` for an auxiliary definition. -/
def freshAuxName (base : Name) (suffix : String) : MetaM Name := do
  let env ← getEnv
  let mut i := 0
  while env.contains (base.appendCore (Name.mkSimple s!"_{suffix}{i}")) do i := i + 1
  return base.appendCore (Name.mkSimple s!"_{suffix}{i}")

/-- Elaborate a coupling and define it as an auxiliary definition (so that it stays one
constant inside the source's half of the product); returns it applied to the local variables it
mentions. -/
def defineCoupling (stx : Term) (suffix : String) : TacticM Lean.Expr := do
  let ty := mkConst ``Coupling
  let e ← Term.withoutErrToSorry <| Term.elabTermEnsuringType stx ty
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "equiv_jimple: the generated coupling has metavariables: {e}"
  let base := (← Term.getDeclName?).getD `equiv_jimple
  let n ← freshAuxName base suffix
  let r ← mkAuxDefinition n ty e (compile := false)
  -- `simp only [n]` needs its equation lemma, realized on demand
  enableRealizationsForConst n
  return r

/-- The candidates tried in turn: all facts kept by the analysis; without the bounds; without the
bounds and without the constants of locals the loops assign (the facts most likely to hold on
the samples only). -/
def candidateLadder : List (String × (Align.HeadFacts → Align.HeadFacts)) :=
  [("all facts", id),
   ("without bounds", fun hf => { hf with bounds := [] }),
   ("without bounds and constants of loop-assigned locals", fun hf =>
     { hf with bounds := [], entry₁ := hf.entry₁.filter (!hf.mod₁.contains ·.1),
               entry₂ := hf.entry₂.filter (!hf.mod₂.contains ·.1) })]

/-- The definition of a generated coupling, as text. -/
def couplingText (J : Lean.Expr) : MetaM String := do
  let c := J.getAppFn.constName!
  let some (.defnInfo d) := (← getEnv).find? c | return toString c
  return s!"{c} := {(← ppExpr d.value).pretty}"

/-- The product with the couplings of `heads`: couplings defined, `sim_of_prodVC` applied, the
entry coupling closed, the product proved by `jprodVC`.  Returns the couplings defined. -/
def jsimWith (an : Align.Analysis) (heads : List Align.HeadFacts) (defs : Array Name)
    (R b₁ b₂ args σE : Lean.Expr) (argEs : Array Lean.Expr) : TacticM (Array Lean.Expr) := do
  let J0 ← defineCoupling (← entryCouplingStx an.isStatic₁ an.isStatic₂ args σE) "jcpl"
  let mut pairs : Array Lean.Expr := #[← mkAppM ``Prod.mk #[mkNatLit 0, ← mkAppM ``Prod.mk #[mkNatLit 0, J0]]]
  let mut cpls : Array Lean.Expr := #[]
  for hf in heads do
    let J ← defineCoupling (← couplingStx hf argEs σE) "jcpl"
    cpls := cpls.push J
    pairs := pairs.push (← mkAppM ``Prod.mk #[mkNatLit hf.h₁, ← mkAppM ``Prod.mk #[mkNatLit hf.h₂, J]])
  let pairsE ← mkListLit (← mkAppM ``Prod #[mkConst ``Nat, ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Coupling]])
    pairs.toList
  let J0name := J0.getAppFn.constName!
  let st ← `(tactic| refine EquivLean.Jimple.sim_of_prodVC (b₁ := $(← Term.exprToSyntax b₁))
      (b₂ := $(← Term.exprToSyntax b₂)) (pairs := $(← Term.exprToSyntax pairsE))
      (R := $(← Term.exprToSyntax R)) (d := $(natStx an.depth)) (fuel₁ := $(natStx an.fuel₁))
      (fuel₂ := $(natStx an.fuel₂)) (J₀ := $(← Term.exprToSyntax J0)) rfl rfl ?_ List.mem_cons_self ?_)
  evalTactic st
  let gvc :: gJ0 :: rest ← getGoals | throwError "equiv_jimple: unexpected goals after sim_of_prodVC"
  -- the entry coupling holds at the calls' entry frames
  let r0 ← onGoal gJ0 do
    evalTactic (← `(tactic| delta $(mkCIdent J0name):ident))
    evalTactic (← `(tactic| exact ⟨rfl, rfl, rfl, rfl⟩))
  unless r0.isEmpty do throwError "equiv_jimple: entry coupling not closed"
  setGoals [gvc]
  if equiv_jimple.trace.get (← getOptions) then
    logInfo m!"equiv_jimple: product goal\n{goalsToMessageData [gvc]}"
    jprodVC defs
  else
    -- the couplings as text now (a failure restores the environment without them)
    let shown ← cpls.mapM fun J => (couplingText J : MetaM String)
    tryCatchRuntimeEx (jprodVC defs (failFast := true)) fun ex =>
      throwError "{String.intercalate "\n" shown.toList}\n{ex.toMessageData}"
  setGoals rest
  return cpls


/-- `Sim R (Call.mk P₁ m₁ args σ) (Call.mk P₂ m₂ args σ)` with the generated pairs and couplings. -/
def jsimAuto (defs : Array Name) (nSamples : Nat := 12) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  unless tgt.isAppOf ``Sim do throwError "equiv_jimple: the goal is not `Sim R t s`"
  let n := tgt.getAppNumArgs
  let R := tgt.getArg! (n - 3)
  let t := (tgt.getArg! (n - 2)).consumeMData
  let s := (tgt.getArg! (n - 1)).consumeMData
  unless t.isAppOfArity ``Call.mk 4 && s.isAppOfArity ``Call.mk 4 do
    throwError "equiv_jimple: the two sides must be explicit `Call.mk P m args σ`"
  let P₁ := t.getArg! 0; let m₁ := t.getArg! 1; let args := t.getArg! 2; let σE := t.getArg! 3
  let P₂ := s.getArg! 0; let m₂ := s.getArg! 1
  unless ← isDefEq args (s.getArg! 2) do
    throwError "equiv_jimple: the two calls must have the same arguments"
  unless ← isDefEq σE (s.getArg! 3) do
    throwError "equiv_jimple: the two calls must start from the same state"
  for e in [P₁, m₁, P₂, m₂] do
    if e.hasFVar || e.hasMVar then throwError "equiv_jimple: programs and methods must be closed terms"
  let some (argEs, _) ← explicitList args | throwError "equiv_jimple: the arguments are not an explicit list"
  -- the data: loop heads, aligned runs, candidate facts
  let an ← match ← evalAnalysis (mkAppN (mkConst ``Align.analyze)
      #[P₁, m₁, P₂, m₂, mkNatLit nSamples, mkNatLit 1]) with
    | .ok an => pure an
    | .error msg => throwError "equiv_jimple: {msg}"
  -- samples on which the outcomes differ refute `Sim (· = ·)` if they meet the precondition
  -- (which the samples do not know): then only the first candidate is tried, and its failure
  -- is reported with them
  let isEq ← withNewMCtxDepth do
    let ty := mkConst ``Out
    let eqR ← withLocalDeclD `x ty fun x => withLocalDeclD `y ty fun y => do
      mkLambdaFVars #[x, y] (← mkEq x y)
    let eqR' ← withLocalDeclD `x ty fun x => withLocalDeclD `y ty fun y => do
      mkLambdaFVars #[x, y] (← mkEq y x)
    return (← isDefEq R eqR) || (← isDefEq R eqR')
  let refuted := isEq && !an.diffs.isEmpty
  let notes : MessageData :=
    (if refuted then m!"\nthe two methods end differently on {an.diffs.length} of {an.samples} sampled inputs (a counterexample if it meets the precondition), e.g. {an.diffs.head!}" else m!"") ++
    (if an.dropped.isEmpty then m!"" else m!"\n{an.dropped.length} sample(s) left out, e.g. {an.dropped.head!}")
  let b₁ ← methodBody m₁
  let b₂ ← methodBody m₂
  if equiv_jimple.trace.get (← getOptions) then
    logInfo m!"equiv_jimple: analysis {repr an}"
    withJimpleHeartbeats do discard <| jsimWith an an.heads defs R b₁ b₂ args σE argEs
    return
  let mut errs : Array MessageData := #[]
  -- each `jvc` call of an attempt gets `jimple.maxHeartbeats` (default here: 400000, several
  -- times what the calls of the demos use), so that a candidate that does not close fails
  let opts ← getOptions
  let hb := jimple.maxHeartbeats.get opts
  let opts := jimple.maxHeartbeats.set opts (if hb == 0 then 400000 else hb)
  for (label, f) in (if refuted then candidateLadder.take 1 else candidateLadder) do
    let heads := an.heads.map f
    let s ← saveState
    -- (runtime exceptions such as heartbeat timeouts also move on to the next candidate)
    let r ← tryCatchRuntimeEx
      (withTheReader Core.Context (fun ctx => { ctx with options := opts }) <|
        withJimpleHeartbeats do discard <| jsimWith an heads defs R b₁ b₂ args σE argEs; pure none)
      (fun ex => pure (some ex))
    match r with
    | none => return
    | some ex =>
      errs := errs.push m!"attempt '{label}':\n{ex.toMessageData}"
      s.restore
  throwError "equiv_jimple: no generated coupling closes the product (analysis of {an.samples} runs, {an.visits} aligned loop-head visits; each jvc call bounded by jimple.maxHeartbeats = {jimple.maxHeartbeats.get opts}).{notes}\n{MessageData.joinSep errs.toList "\n\n"}"

/-- `equiv_jimple [defs]`: prove `Sim R (Call.mk P₁ m₁ args σ) (Call.mk P₂ m₂ args σ)` or
`Equiv R …` (both directions) for two methods whose loops correspond one to one, with NO pairs or
couplings written: loop heads paired in order, couplings generated from runs of both methods
(see the module documentation), then the product proved as by `jprod_vc`.  User predicates of
the hypotheses are unfolded; `defs` are further definitions to unfold (e.g. a user outcome
relation). -/
syntax (name := equivJimpleTac) "equiv_jimple" (" [" ident,* "]")? : tactic

@[tactic equivJimpleTac] def evalEquivJimple : Tactic := fun stx => withMainContext do
  let ids := Jimple.optIdents stx[1]
  let defs ← ids.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  -- unfold user predicates in the hypotheses (preconditions)
  let mut ds := defs
  for _ in [0:4] do
    let more ← userPredDefs
    let new := more.filter (!ds.contains ·)
    unfoldInHyps (ds ++ new)
    if new.isEmpty then break
    ds := ds ++ new
  let tgt := (← instantiateMVars (← getMainTarget)).consumeMData
  if tgt.isAppOf ``Equiv then
    let g :: others ← getGoals | throwError "equiv_jimple: no goal"
    let [g₁, g₂] ← onGoal g (evalTactic (← `(tactic| refine And.intro ?_ ?_)))
      | throwError "equiv_jimple: unexpected goals for `Equiv`"
    discard <| onGoal g₁ (jsimAuto defs)
    discard <| onGoal g₂ (jsimAuto defs)
    setGoals others
  else jsimAuto defs

end EquivLean.Jimple

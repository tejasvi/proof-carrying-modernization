import EquivLean.Bridge.Aeneas.Tactic

/-!
# Aeneas (Rust) bridge: generated couplings for lockstep loops

`equiv_aeneas [defs] (with [extra])?`, i.e. `equiv_aeneas` without `using`, generates the
coupling invariant of the two loops itself.  After unfolding `defs`, each side of the goal
`Equiv R t s` (or `Sim R t s`) must be one Aeneas `loop body init`.  The coupling is built from
the two loops:

* the loop variables are the components of the loop states (Aeneas packs them in a right-nested
  tuple).  They are paired by Rust name and type (the names are those of the parameters of the
  two `@[rust_loop]` definitions that form the initial states), the rest by type and position.
  When all variables pair up in order, this is `fun p q => p = q`; otherwise it is a conjunction
  of equalities of components, e.g. `p.1 = q.2 ∧ p.2 = q.1`;
* a variable without a partner keeps its value at loop entry (`p.1 = false`) when no iteration
  changes it (every `cont` of its loop body passes it on unchanged, or sets it back to its entry
  value); otherwise (a temporary that each iteration overwrites) it is left unconstrained;
* loop bounds: a scalar loop variable `i` that a body compares (`<`, `>`, `!=`, `==`, `=`, `≠`)
  with a value the loop does not modify (one that does not depend on the loop state) is bounded
  by that value: `i.val ≤ v.val.length` against `Slice.len v` or `Vec.len v`, `i.val ≤ n.val`
  against a scalar `n` (`n.val ≤ i.val` for `n < i`).  A source bound that follows from an
  equality with a target variable carrying the same bound is left out.

The coupling is tried first without, then with the loop bounds (e.g.
`fun p q => p = q ∧ p.2.val ≤ v.val.length` for `i != v.len()` against `i < v.len()`).  Each
attempt runs the pipeline of `equiv_aeneas [defs] using I with [extra]` (`aeneas_lockstep`) and
counts only if it closes the goal; otherwise the next attempt starts from the same state.  If no
attempt succeeds, the goal is left as it was and the tactic fails with the couplings it tried; a
coupling then has to be given with `using`.  Failed attempts count against the `maxHeartbeats` of
the declaration.

`equiv_aeneas? …` does the same and suggests `equiv_aeneas […] using fun p q => …` with the
coupling that closed the goal.

`equiv_aeneas … using I` (`Bridge/Aeneas/Tactic.lean`) is unchanged: the form without `using` is
a second syntax with the same keyword (Lean's longest match keeps `using I` on the first one),
and it was a parse error before, so no existing proof changes meaning.
-/

open Aeneas Aeneas.Std

namespace EquivLean.Aeneas

open Lean Meta Elab Tactic Parser.Tactic

/-- The pipeline of `equiv_aeneas [defs] using I with [extra]` after the unfolding of `defs`:
lockstep pairing of the two loops with the coupling `I`, symbolic execution of both bodies,
the leaves. -/
syntax (name := aeneasLockstep) "aeneas_lockstep" (" [" ident,* "]")? " using " term
  (" with" " [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| aeneas_lockstep $[[$defs,*]]? using $I $[with [$args,*]]?) => do
    let defs : Array Ident := (defs.map (·.getElems)).getD #[]
    let args : SimpArgs := (args.map (·.getElems)).getD #[]
    let defArgs : SimpArgs := defs.map identSimpArg
    `(tactic| (
      first
        | refine equiv_loop $I ?_ _ _ ?_
        | refine sim_loop' $I ?_ _ _ ?_
      · try simp only [Prod.forall]
        intros
        try simp only [Prod.mk.injEq] at *
        try casesm* _ ∧ _
        try subst_vars
        first | apply equiv_of_wp_staged | apply sim_of_wp_staged
        intro T hT
        try (aeneas_wp [$defArgs,*, $args,*] at ⊢)
        try split_ifs
        all_goals (subst hT)
        all_goals (try (aeneas_wp [$defArgs,*, $args,*] at *))
        all_goals (aeneas_leaves [$args,*])
      · aeneas_wp [$args,*]
        try simp_all
        try scalar_tac))

namespace AutoCouple

/-- The types of the loop variables of a loop state (Aeneas packs them in a right-nested
tuple). -/
partial def stateComps (σ : Expr) : MetaM (Array Expr) := do
  let σ' ← whnfR (← instantiateMVars σ)
  if σ'.isAppOfArity ``Prod 2 then
    return #[σ'.getArgD 0 σ'] ++ (← stateComps (σ'.getArgD 1 σ'))
  return #[σ]

/-- Loop variable `k` of a state `p` with `n` variables. -/
def stateProj (p : Expr) (n k : Nat) : MetaM Expr := do
  let mut e := p
  for _ in [0:k] do e ← mkAppM ``Prod.snd #[e]
  if k + 1 < n then e ← mkAppM ``Prod.fst #[e]
  return e

/-- The state made of the loop variables `cs`. -/
def stateTuple (cs : Array Expr) : MetaM Expr := do
  let some last := cs.back? | throwError "equiv_aeneas: empty loop state"
  cs.pop.foldrM (fun c e => mkAppM ``Prod.mk #[c, e]) last

/-- The components of an explicit tuple with `n` components. -/
partial def tupleComps? (x : Expr) (n : Nat) : Option (Array Expr) :=
  if n ≤ 1 then some #[x]
  else
    let x := x.cleanupAnnotations
    if x.isAppOfArity ``Prod.mk 4 then
      (tupleComps? (x.getArgD 3 x) (n - 1)).map (#[x.getArgD 2 x] ++ ·)
    else none

/-- The entry values of the loop variables: the components of the initial state. -/
def initComps (x : Expr) (n : Nat) : MetaM (Array Expr) := do
  if let some cs := tupleComps? x n then return cs
  (List.range n).toArray.mapM fun k => stateProj x n k

/-- Membership in a simp set (definitions to unfold). -/
def inSimpSet (ext : SimpExtension) (n : Name) : MetaM Bool := do
  let d ← ext.getTheorems
  return d.isDeclToUnfold n || d.toUnfoldThms.contains n

/-- A loop definition generated by Aeneas (`@[rust_loop]`). -/
def isLoopDecl (n : Name) : MetaM Bool := inSimpSet Aeneas.RustAttributes.rustLoopSimpExt n

/-- A loop body definition generated by Aeneas (`@[rust_loop_body]`). -/
def isLoopBodyDecl (n : Name) : MetaM Bool :=
  inSimpSet Aeneas.RustAttributes.rustLoopBodySimpExt n

/-- `loop body init`: the state type, the body and the initial state. -/
def loopOf? (e : Expr) : Option (Expr × Expr × Expr) :=
  let e := e.cleanupAnnotations
  if e.isAppOfArity ``Aeneas.Std.loop 4 then some (e.getArgD 0 e, e.getArgD 2 e, e.getArgD 3 e)
  else none

/-- The Rust names of the loop variables of the `@[rust_loop]` definition `n`: its parameters
that make up the initial state of its `loop` (`""` where the initial value is not a
parameter). -/
def loopDeclVarNames (n : Name) : MetaM (Array String) := do
  let some v := (← getConstInfo n).value? | return #[]
  lambdaTelescope v fun _ body => do
    let some (σ, _, x) := loopOf? body | return #[]
    let some xs := tupleComps? x (← stateComps σ).size | return #[]
    xs.mapM fun e => do
      if let .fvar id := e then return (← id.getUserName).toString else return ""

/-- The Rust names of the loop variables of a side of the goal before unfolding: from the loop
definition the side calls, or the one called in the body of the function it applies (a
function with one loop). -/
def sideVarNames (e : Expr) : MetaM (Array String) := do
  let .const f _ := e.cleanupAnnotations.getAppFn | return #[]
  if ← isLoopDecl f then return ← loopDeclVarNames f
  let some v := (← getConstInfo f).value? | return #[]
  match (← v.getUsedConstants.filterM isLoopDecl).toList.eraseDups with
  | [l] => loopDeclVarNames l
  | _ => return #[]

/-- Head normalisation for the scan of a loop body: β, `let`, annotations, projections of
tuples, and the loop body definitions of Aeneas. -/
partial def headNorm (e : Expr) (fuel : Nat := 64) : MetaM Expr := do
  if fuel = 0 then return e
  match e.headBeta with
  | .mdata _ b => headNorm b (fuel - 1)
  | .letE _ _ v b _ => headNorm (b.instantiate1 v) (fuel - 1)
  | .proj ``Prod i a =>
    let a ← headNorm a (fuel - 1)
    if a.isAppOfArity ``Prod.mk 4 then headNorm (a.getArgD (2 + i) a) (fuel - 1)
    else return .proj ``Prod i a
  | e =>
    let fst := e.isAppOfArity ``Prod.fst 3
    if fst || e.isAppOfArity ``Prod.snd 3 then
      let a ← headNorm e.appArg! (fuel - 1)
      if a.isAppOfArity ``Prod.mk 4 then
        return ← headNorm (a.getArgD (if fst then 2 else 3) a) (fuel - 1)
      return mkApp e.appFn! a
    if let .const n us := e.getAppFn then
      if ← isLoopBodyDecl n then
        let ci ← getConstInfo n
        if ci.hasValue then
          let v ← instantiateValueLevelParams ci us
          return ← headNorm (v.beta e.getAppArgs) (fuel - 1)
    return e

/-- The components of a tuple with `n` components, after head normalisation. -/
partial def tupleCompsN (x : Expr) (n : Nat) : MetaM (Option (Array Expr)) := do
  let x ← headNorm x
  if n ≤ 1 then return some #[x]
  if x.isAppOfArity ``Prod.mk 4 then
    let some rest ← tupleCompsN (x.getArgD 3 x) (n - 1) | return none
    return some (#[← headNorm (x.getArgD 2 x)] ++ rest)
  return none

/-- `a < b` (`.lt`), and `a ≠ b`, `a = b`, `a != b`, `a == b` (`.ne`). -/
inductive Cmp where
  | lt | ne
  deriving BEq, Inhabited

/-- The comparison at the head of `e`. -/
def cmpOf? (e : Expr) : Option (Expr × Cmp × Expr) :=
  if e.isAppOfArity ``LT.lt 4 then some (e.getArgD 2 e, .lt, e.getArgD 3 e)
  else if e.isAppOfArity ``GT.gt 4 then some (e.getArgD 3 e, .lt, e.getArgD 2 e)
  else if e.isAppOfArity ``bne 4 || e.isAppOfArity ``BEq.beq 4 then
    some (e.getArgD 2 e, .ne, e.getArgD 3 e)
  else if e.isAppOfArity ``Ne 3 || e.isAppOfArity ``Eq 3 then
    some (e.getArgD 1 e, .ne, e.getArgD 2 e)
  else none

/-- A loop bound: loop variable `comp` against the loop-invariant `rhs`, `comp ≤ rhs`
(`rhs ≤ comp` when `lower`). -/
structure Bound where
  comp : Nat
  lower : Bool
  rhs : Expr
  deriving Inhabited

/-- What the scan of a loop body collects: loop bounds and the states passed to `cont`. -/
structure Scan where
  bounds : Array Bound := #[]
  conts : Array Expr := #[]

/-- Scan a loop body applied to the loop variables `cs`. -/
partial def scan (cs : Array Expr) (fuel : Nat) (e : Expr) : StateT Scan MetaM Unit := do
  if fuel = 0 then return
  let e ← headNorm e
  if e.isAppOfArity ``ControlFlow.cont 3 then
    modify fun st => { st with conts := st.conts.push (e.getArgD 2 e) }
  if let some (a, k, b) := cmpOf? e then
    let a ← headNorm a
    let b ← headNorm b
    let inv (x : Expr) : Bool :=
      !x.hasLooseBVars && !cs.any fun c => (x.find? (· == c)).isSome
    if let some i := cs.findIdx? (· == a) then
      if inv b then modify fun st => { st with bounds := st.bounds.push ⟨i, false, b⟩ }
    else if let some i := cs.findIdx? (· == b) then
      if inv a then modify fun st => { st with bounds := st.bounds.push ⟨i, k == .lt, a⟩ }
  match e with
  | .app .. =>
    scan cs (fuel - 1) e.getAppFn
    for a in e.getAppArgs do scan cs (fuel - 1) a
  | .lam _ t b _ | .forallE _ t b _ => scan cs (fuel - 1) t; scan cs (fuel - 1) b
  | .proj _ _ b => scan cs (fuel - 1) b
  | _ => pure ()

/-- `x.val` for a Rust scalar `x`. -/
def scalarVal? (x : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR (← inferType x)
  if ty.isAppOfArity ``UScalar 1 then return some (← mkAppM ``UScalar.val #[x])
  if ty.isAppOfArity ``IScalar 1 then return some (← mkAppM ``IScalar.val #[x])
  return none

/-- The value of a bound: `v.val.length` for `Slice.len v` and `Vec.len v`, `n.val` for a
scalar `n`. -/
def boundVal? (b : Expr) : MetaM (Option Expr) := do
  let b := b.cleanupAnnotations
  if b.isAppOfArity ``Slice.len 2 then
    return some (← mkAppM ``List.length #[← mkAppM ``Slice.val #[b.appArg!]])
  if b.isAppOfArity ``alloc.vec.Vec.len 2 then
    return some (← mkAppM ``List.length #[← mkAppM ``alloc.vec.Vec.val #[b.appArg!]])
  scalarVal? b

/-- The fact of the bound `bd` for the loop variable `c`. -/
def boundFact? (c : Expr) (bd : Bound) : MetaM (Option Expr) := do
  let some cv ← scalarVal? c | return none
  let some bv ← boundVal? bd.rhs | return none
  unless ← withNewMCtxDepth (isDefEq (← inferType cv) (← inferType bv)) do return none
  some <$> if bd.lower then mkAppM ``LE.le #[bv, cv] else mkAppM ``LE.le #[cv, bv]

/-- One side of a loop pair: the state type; the types, Rust names (`""` if unknown) and entry
values of the loop variables; the loop bounds; which variables no iteration changes. -/
structure Side where
  σ : Expr
  comps : Array Expr
  names : Array String
  init : Array Expr
  bounds : Array Bound
  unchanged : Array Bool
  deriving Inhabited

/-- Analyse the loop `loop B x` with state type `σ` and the Rust names `names` of its loop
variables. -/
def side (σ B x : Expr) (names : Array String) : MetaM Side := do
  let comps ← stateComps σ
  let n := comps.size
  let init ← initComps x n
  let mut decls : Array (Name × Expr) := #[]
  for ty in comps do decls := decls.push (Name.mkSimple s!"c{decls.size}", ty)
  let (bounds, unchanged) ← withLocalDeclsDND decls fun cs => do
    let (_, st) ← (scan cs 512 (mkApp B (← stateTuple cs))).run {}
    let mut unchanged : Array Bool := #[]
    for k in [0:n] do
      let mut keep := true
      for v in st.conts do
        match ← tupleCompsN v n with
        | some vs =>
          -- passed on as it is, or set back to its entry value
          let w := vs.getD k v
          unless w == cs.getD k v || w == init.getD k v do keep := false
        | none => keep := false
      unchanged := unchanged.push keep
    return (st.bounds, unchanged)
  let mut uniq : Array Bound := #[]
  for bd in bounds do
    unless uniq.any (fun b => b.comp == bd.comp && b.lower == bd.lower && b.rhs == bd.rhs) do
      uniq := uniq.push bd
  let names := if names.size == n then names else (List.replicate n "").toArray
  return { σ, comps, names, init, bounds := uniq, unchanged }

/-- Pair the loop variables of the two sides: by Rust name and type, then by type and position.
The pairs are sorted by the target's variables. -/
def pairComps (t s : Side) : MetaM (Array (Nat × Nat)) := do
  let sameTy (i j : Nat) : MetaM Bool :=
    withNewMCtxDepth (isDefEq (t.comps.getD i default) (s.comps.getD j default))
  let mut pairs : Array (Nat × Nat) := #[]
  for i in [0:t.comps.size] do
    let nm := t.names.getD i ""
    if nm.isEmpty then continue
    for j in [0:s.comps.size] do
      if pairs.any (·.2 == j) then continue
      if s.names.getD j "" == nm && (← sameTy i j) then
        pairs := pairs.push (i, j)
        break
  for i in [0:t.comps.size] do
    if pairs.any (·.1 == i) then continue
    for j in [0:s.comps.size] do
      if pairs.any (·.2 == j) then continue
      if ← sameTy i j then
        pairs := pairs.push (i, j)
        break
  return pairs.qsort (·.1 < ·.1)

/-- The coupling: equalities of the paired variables (`p = q` when `useEq`), entry values of
the unpaired variables that no iteration changes, and the loop bounds when `bounds`. -/
def coupling (t s : Side) (pairs : Array (Nat × Nat)) (useEq bounds : Bool) : MetaM Expr :=
  withLocalDeclD `p t.σ fun p => withLocalDeclD `q s.σ fun q => do
    let nT := t.comps.size
    let nS := s.comps.size
    let mut facts : Array Expr := #[]
    if useEq then facts := facts.push (← mkEq p q)
    else
      for (i, j) in pairs do
        facts := facts.push (← mkEq (← stateProj p nT i) (← stateProj q nS j))
    for i in [0:nT] do
      if !pairs.any (·.1 == i) && t.unchanged.getD i false then
        facts := facts.push (← mkEq (← stateProj p nT i) (t.init.getD i p))
    for j in [0:nS] do
      if !pairs.any (·.2 == j) && s.unchanged.getD j false then
        facts := facts.push (← mkEq (← stateProj q nS j) (s.init.getD j q))
    if bounds then
      for bd in t.bounds do
        if let some f ← boundFact? (← stateProj p nT bd.comp) bd then facts := facts.push f
      for bd in s.bounds do
        let implied := pairs.any fun (i, j) => j == bd.comp &&
          t.bounds.any fun b => b.comp == i && b.lower == bd.lower && b.rhs == bd.rhs
        if implied then continue
        if let some f ← boundFact? (← stateProj q nS bd.comp) bd then facts := facts.push f
    mkLambdaFVars #[p, q] (mkAndN facts.toList)

/-- The generated couplings for the loop pair of the goal `Equiv R t s` / `Sim R t s` (after
unfolding), in the order in which they are tried; `namesT`, `namesS` are the Rust names of the
loop variables. -/
def couplings (g : MVarId) (namesT namesS : Array String) : MetaM (Array Expr) :=
  g.withContext do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations
  unless ty.isAppOfArity ``EquivLean.Equiv 9 || ty.isAppOfArity ``EquivLean.Sim 9 do
    throwError "equiv_aeneas: the goal is not `Equiv R t s` or `Sim R t s`"
  let some (σT, BT, xT) := loopOf? (ty.getArgD 7 ty)
    | throwError "equiv_aeneas: after unfolding, the target is not one `loop` (give the \
        functions, their `_loop` and `_loop.body` definitions)"
  let some (σS, BS, xS) := loopOf? (ty.getArgD 8 ty)
    | throwError "equiv_aeneas: after unfolding, the source is not one `loop` (give the \
        functions, their `_loop` and `_loop.body` definitions)"
  let t ← side σT BT xT namesT
  let s ← side σS BS xS namesS
  let pairs ← pairComps t s
  if pairs.isEmpty then
    throwError "equiv_aeneas: the two loops have no loop variables of the same type"
  let inOrder := t.comps.size == s.comps.size && pairs.size == t.comps.size &&
    pairs.all fun (i, j) => i == j
  let useEq := inOrder && (← withNewMCtxDepth (isDefEq σT σS))
  let mut out : Array Expr := #[← instantiateMVars (← coupling t s pairs useEq false)]
  if !t.bounds.isEmpty || !s.bounds.isEmpty then
    let I ← instantiateMVars (← coupling t s pairs useEq true)
    unless out.contains I do out := out.push I
  return out

end AutoCouple

/-- `equiv_aeneas [defs] (with [extra])?`: lockstep equivalence (or simulation) of two Aeneas
functions with one loop each, with a generated coupling invariant (see the module doc). -/
syntax (name := equivAeneasAuto) "equiv_aeneas" (" [" ident,* "]")?
  (" with" " [" simpArg,* "]")? : tactic

/-- `equiv_aeneas? [defs] (with [extra])?`: `equiv_aeneas` with a generated coupling, and the
suggestion `equiv_aeneas [defs] using I` for the coupling that closed the goal. -/
syntax (name := equivAeneasAutoShow) "equiv_aeneas?" (" [" ident,* "]")?
  (" with" " [" simpArg,* "]")? : tactic

/-- Try the generated couplings in order; return the one that closed the main goal. -/
def runAutoCouple (defs : Array Ident) (args : SimpArgs) : TacticM Expr := do
  let g0 ← getMainGoal
  let ty0 := (← instantiateMVars (← g0.getType)).cleanupAnnotations
  unless ty0.isAppOfArity ``EquivLean.Equiv 9 || ty0.isAppOfArity ``EquivLean.Sim 9 do
    throwError "equiv_aeneas: the goal is not `Equiv R t s` or `Sim R t s`"
  -- the Rust names of the loop variables, read before the loop definitions are unfolded
  let names (e : Expr) : TacticM (Array String) := do
    try g0.withContext (AutoCouple.sideVarNames e) catch _ => return #[]
  let namesT ← names (ty0.getArgD 7 ty0)
  let namesS ← names (ty0.getArgD 8 ty0)
  let s0 ← saveState
  let defArgs : SimpArgs := defs.map identSimpArg
  unless defs.isEmpty do evalTactic (← `(tactic| simp only [$defArgs,*]))
  let g ← getMainGoal
  let cands ← AutoCouple.couplings g namesT namesS
  let errors : TacticM Nat := do
    return (← Core.getMessageLog).toList.countP (·.severity == .error)
  let e1 ← errors
  let s1 ← saveState
  for I in cands do
    try
      -- no error recovery: a bullet that does not close its goal must fail, not admit it
      withoutRecover <| focus do
        let Is ← g.withContext (Term.exprToSyntax I)
        evalTactic (← `(tactic| aeneas_lockstep [$defs,*] using $Is with [$args,*]))
        done
      if (← instantiateMVars (mkMVar g)).hasSorry || (← errors) > e1 then
        throwError "equiv_aeneas: the attempt left an error"
      return I
    catch _ => s1.restore
  s0.restore
  g0.withContext do
    throwError "equiv_aeneas: no generated coupling closes this loop pair; tried{indentD
      (MessageData.joinSep (cands.toList.map MessageData.ofExpr) Format.line)}\n\
      give one with `equiv_aeneas [..] using fun p q => …`"

elab_rules : tactic
  | `(tactic| equiv_aeneas $[[$defs,*]]? $[with [$args,*]]?) => do
    let defs : Array Ident := (defs.map (·.getElems)).getD #[]
    let args : SimpArgs := (args.map (·.getElems)).getD #[]
    discard <| runAutoCouple defs args

/-- The coupling `I` as syntax that elaborates back to `I`: printed as usual, or else without
coercion arrows (`↑p.2 ≤ (↑v).length` does not elaborate; `UScalar.val p.2 ≤ v.val.length`
does). -/
def couplingSyntax (I : Expr) : TermElabM Term := do
  let ty ← inferType I
  for coe in [true, false] do
    let stx ← withOptions (fun o => o.setBool `pp.coercions coe) (PrettyPrinter.delab I)
    let ok ← withoutModifyingState do
      try
        let e ← Term.elabTerm stx (some ty)
        Term.synthesizeSyntheticMVarsNoPostponing
        isDefEq e I
      catch _ => pure false
    if ok then return stx
  withOptions (fun o => o.setBool `pp.coercions false) (PrettyPrinter.delab I)

elab_rules : tactic
  | `(tactic| equiv_aeneas? $[[$defs,*]]? $[with [$args,*]]?) => do
    let defs : Array Ident := (defs.map (·.getElems)).getD #[]
    let args : SimpArgs := (args.map (·.getElems)).getD #[]
    let g0 ← getMainGoal
    let I ← runAutoCouple defs args
    let Is ← g0.withContext (couplingSyntax I)
    let stx ← if args.isEmpty then `(tactic| equiv_aeneas [$defs,*] using $Is)
      else `(tactic| equiv_aeneas [$defs,*] using $Is with [$args,*])
    Meta.Tactic.TryThis.addSuggestion (← getRef) stx

end EquivLean.Aeneas

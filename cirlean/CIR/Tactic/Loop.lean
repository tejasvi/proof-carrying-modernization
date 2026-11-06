import CIR.Tactic.VCG
import CIR.Logic.Loops
import CIR.Tactic.Frame

/-!
  `cir_loop inv dec`: apply the loop rule with an invariant written over the
  C++ local variables the loop modifies.

  On a goal whose head is `evalFor` / `evalWhile` / `evalDo` at the loop-entry
  state `σ₀`, the tactic
  * finds the local variables (stack slots) the loop stores to, and their C++
    names (from the ghost `State.names` table);
  * matches them with the binder names of `inv` and `dec`, e.g.
    `cir_loop (fun i s => 0 ≤ i ∧ i ≤ n ∧ 2 * s = i * (i - 1)) (fun i s => n - i)`;
  * applies the loop rule with the invariant
      `LoopFrame σ₀ mods σ ∧ IntSlot σ b₁ ty₁ ∧ … ∧ inv (σ.intAt b₁) …`
    (environment, names and every other older block unchanged; each modified
    slot holds an integer; the user's property) and the variant
    `(dec (σ.intAt b₁) …).toNat`;
  * leaves the user's property at loop entry, and runs `cir_vcg` on one
    iteration from an arbitrary state satisfying the invariant.
-/

namespace CIR.Tactic

open Lean Meta Elab Tactic Term

/-- `(addr, ty)` of every `Op.store _ addr ty` occurring in `e`. -/
partial def collectStores (e : Expr) : MetaM (Array (Expr × Expr)) := do
  let e ← instantiateMVars e
  let rec go (e : Expr) (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
    let acc := if e.isAppOfArity ``CIR.Op.store 3 then acc.push (e.getArg! 1, e.getArg! 2) else acc
    match e with
    | .app f a => go a (← go f acc)
    | .lam _ t b _ => go b (← go t acc)
    | .forallE _ t b _ => go b (← go t acc)
    | .letE _ t v b _ => go b (← go v (← go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | .const n _ =>
      -- chunked op lists emitted by cir2lean are definitions: look inside them
      if (← getEnv).contains n && n.getPrefix != `CIR then
        match (← getConstInfo n) with
        | .defnInfo d => if (← isDefEq (← inferType e) (← mkAppM ``List #[mkConst ``CIR.Op])) then go d.value acc else pure acc
        | _ => pure acc
      else pure acc
    | _ => pure acc
  go e #[]

/-- `(addr, pointee type)` of every argument `addr` of pointer type `T*`
passed to a call in `e` (a variable whose address is passed may be modified
by the callee, e.g. the iterator of a range-`for`). -/
partial def collectCallArgs (e : Expr) : MetaM (Array (Expr × Expr)) := do
  let e ← instantiateMVars e
  let rec go (e : Expr) (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
    let mut acc := acc
    if e.isAppOfArity ``CIR.Op.call 7 then
      if let (some (_, args), some (_, tys)) := ((e.getArg! 3).listLit?, (e.getArg! 4).listLit?) then
        for (a, t) in args.zip tys do
          let t ← whnfR t
          if t.isAppOfArity ``CIR.Ty.ptr 1 then acc := acc.push (a, t.getArg! 0)
    match e with
    | .app f a => go a (← go f acc)
    | .lam _ t b _ => go b (← go t acc)
    | .forallE _ t b _ => go b (← go t acc)
    | .letE _ t v b _ => go b (← go v (← go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | .const n _ =>
      if (← getEnv).contains n && n.getPrefix != `CIR then
        match (← getConstInfo n) with
        | .defnInfo d => if (← isDefEq (← inferType e) (← mkAppM ``List #[mkConst ``CIR.Op])) then go d.value acc else pure acc
        | _ => pure acc
      else pure acc
    | _ => pure acc
  go e #[]

/-- How a loop variable is described in the invariant. -/
inductive SlotKind where
  /-- a signed integer variable: the invariant names its value (`Int`) -/
  | int
  /-- an unsigned integer variable (`size_t`, ...): the invariant names its
  value as a `Nat` -/
  | nat
  /-- a contiguous iterator: the invariant names its element index (`Nat`) -/
  | iter
  /-- a pointer variable into an array (`T*`): the invariant names its
  element index (`Nat`); the array is the one it points into at loop entry -/
  | ptr
  /-- assigned before use in every iteration: not in the invariant -/
  | scratch
  /-- a pointer variable to a container of `int`s that the loop modifies
  (`out.push_back(x)`): the invariant names the container's elements
  (`List Int`) -/
  | vec
  /-- an array the loop writes (a local array, or a global or function-local
  static one, named by its C name): the invariant names its elements
  (`List Val`) -/
  | arr
  /-- a pointer variable annotated `(p : Ptr)` (a loop over a linked
  structure): the invariant names its value (`Ptr`) -/
  | ptrv
  /-- the binder `(mem : Mem)`: the memory at the loop head; the invariant
  then describes the caller's blocks and the heap itself -/
  | mem
  deriving BEq, Inhabited

/-- The kind of a named loop variable of type `ty`. -/
def slotKindOf? (ty : Expr) : MetaM (Option SlotKind) := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``CIR.Ty.int 2 then
    return some (if (← whnfR (ty.getArg! 0)).isConstOf ``Bool.false then .nat else .int)
  if ty.isAppOfArity ``CIR.Ty.record 1 then
    if let .lit (.strVal n) ← whnfD (ty.getArg! 0) then
      if (n.splitOn "iter").length > 1 then return some .iter
  if ty.isAppOfArity ``CIR.Ty.ptr 1 then return some .ptr
  return none

/-- The block id `b` when `σ₀.env addr = some (ptr (loc b []))`. -/
def envSlot? (σ₀ addr : Expr) : MetaM (Option Expr) := do
  let e := mkApp (← mkAppM ``CIR.State.env #[σ₀]) addr
  let r ← whnfD e
  let_expr Option.some _ v := r | return none
  let v ← whnfD v
  let_expr CIR.Val.ptr p := v | return none
  let p ← whnfD p
  let_expr CIR.Ptr.loc blk path := p | return none
  let path ← whnfD path
  unless path.isAppOf ``List.nil do return none
  return some blk

/-- Projection functions in place of the primitive projections that `whnfR`
leaves on memories and states: `omega` takes `σ.mem.2` and `σ.mem.next` for
different numbers (the entry `next` of a second loop is the first loop's). -/
partial def unprojMem (e : Expr) : Expr :=
  e.replace fun e => match e with
    | .proj ``CIR.Mem 0 m => some (mkApp (mkConst ``CIR.Mem.blocks) (unprojMem m))
    | .proj ``CIR.Mem 1 m => some (mkApp (mkConst ``CIR.Mem.next) (unprojMem m))
    | .proj ``CIR.State 0 st => some (mkApp (mkConst ``CIR.State.mem) (unprojMem st))
    | .proj ``CIR.State 1 st => some (mkApp (mkConst ``CIR.State.env) (unprojMem st))
    | .proj ``CIR.State 2 st => some (mkApp (mkConst ``CIR.State.names) (unprojMem st))
    | _ => none

/-- The type of block `blk` in the state `σ₀`: from the last update of that
block in `σ₀`'s memory (a chain of `upd`, compared syntactically), through
scope exits (`killRange`, which keep the blocks below their range), and
behind an abstract memory through the hypotheses about it: an equation for a
state (`σ₀ = ⟨…⟩`, the entry state of an earlier loop), a lookup
(`σ.mem.blocks b = some ⟨_, _, ty, _⟩`, a slot of an earlier loop) or a frame
(`∀ b, … → σ.mem.blocks b = σ₀.mem.blocks b`; its premises are not checked:
the type only classifies the binder). Second loops of a function need this:
their variables were last written before the first loop. -/
partial def slotBlockTy? (σ₀ blk : Expr) : MetaM (Option Expr) := do
  let st ← whnfR σ₀
  let_expr CIR.State.mk mem _ _ := st | return none
  let mem ← whnfR mem
  let_expr CIR.Mem.mk blocks _ := mem | return none
  go (mkApp blocks blk) 0
where
  /-- The type of the block in the lookup `t` (`bs blk`). -/
  go (t : Expr) (depth : Nat) : MetaM (Option Expr) := do
    if depth > 24 then return none
    let t ← instantiateMVars t
    -- `upd f a v blk`
    if t.isAppOfArity ``CIR.upd 7 then
      if ← withReducible (isDefEq (t.getArg! 4) blk) then
        let v ← whnfR (t.getArg! 5)
        let_expr Option.some _ b := v | return none
        let b ← whnfR b
        let_expr CIR.MemBlock.mk _ _ ty _ := b | return none
        return some (← whnfR ty)
      return ← go (mkApp (t.getArg! 3) blk) (depth + 1)
    -- `killRange lo hi bs blk`
    if t.isAppOfArity ``CIR.killRange 4 then
      return ← go (mkApp (t.getArg! 2) blk) (depth + 1)
    -- `m.blocks blk` for an abstract memory (projection functions, or the
    -- primitive projections that `whnfR` leaves)
    let blocksOf? : Option Expr :=
      if t.isAppOfArity ``CIR.Mem.blocks 2 then some (t.getArg! 0)
      else match t with
        | .app (.proj ``CIR.Mem 0 m) _ => some m
        | _ => none
    let some m := blocksOf? | return none
    let stateOf? : Option Expr :=
      if m.isAppOfArity ``CIR.State.mem 1 then some (m.getArg! 0)
      else match m with
        | .proj ``CIR.State 0 st => some st
        | _ => none
    -- a literal memory (after a state equation)
    if m.isAppOfArity ``CIR.Mem.mk 2 then
      return ← go (mkApp (m.getArg! 0) blk) (depth + 1)
    -- `σ.mem` for a state with an equation `σ = ⟨…⟩`
    if let some σ := stateOf?.filter (·.isFVar) then
      let eqn? ← (← getLCtx).findDeclM? fun d => do
        if d.isImplementationDetail then return none
        let ty ← instantiateMVars d.type
        let some (_, lhs, rhs) := ty.eq? | return none
        if lhs == σ && rhs.isAppOf ``CIR.State.mk then return some rhs else return none
      if let some S := eqn? then
        let_expr CIR.State.mk mem' _ _ := S | return none
        let mem' ← whnfR mem'
        let_expr CIR.Mem.mk blocks' _ := mem' | return none
        return ← go (mkApp blocks' blk) (depth + 1)
    -- a hypothesis about this lookup: a slot (`= some ⟨_, _, ty, _⟩`) or a
    -- frame (`= m'.blocks blk`)
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless (ty.find? fun e => e.isAppOf ``CIR.Mem.blocks || (match e with
          | .proj ``CIR.Mem 0 _ => true
          | _ => false)).isSome do continue
      let r? ← withNewMCtxDepth do
        let (_, _, concl) ← forallMetaTelescope ty
        let some (_, lhs, rhs) := concl.eq? | return none
        unless lhs.isApp do return none
        unless ← withReducible (isDefEq lhs t) do return none
        let rhs ← instantiateMVars rhs
        if rhs.hasExprMVar then return none
        return some rhs
      let some rhs := r? | continue
      let rhs' ← whnfR rhs
      if rhs'.isAppOfArity ``Option.some 2 then
        let b ← whnfR (rhs'.getArg! 1)
        let_expr CIR.MemBlock.mk _ _ ty' _ := b | continue
        return some (← whnfR ty')
      if rhs != t then
        if let some ty' ← go rhs (depth + 1) then return some ty'
    return none

/-- The block of the global array named `name` (its symbol, or the part of
its symbol after the last `.`, as clang names function-local statics
`f.name`): from the module of a concrete context, or a hypothesis
`ctx.gaddr sym = some b`. -/
def globalArrBlock? (ctx : Expr) (name : String) : MetaM (Option Expr) := do
  let some gs ← listElems (← mkAppM ``CIR.Module.globals #[← mkAppM ``CIR.Ctx.mod #[ctx]]) | return none
  let mut found : Option String := none
  for g in gs do
    let some s ← strLit? (← mkAppM ``CIR.GlobalDecl.sym #[g]) | continue
    if s == name || s.endsWith ("." ++ name) then
      if found.isSome then return none   -- ambiguous
      found := some s
  let some sym := found | return none
  let look ← mkAppM ``CIR.Ctx.gaddr #[ctx, mkStrLit sym]
  if let some v ← lookupValue? look then
    let_expr Option.some _ b := v | return none
    return some b
  (← getLCtx).findDeclM? fun d => do
    if d.isImplementationDetail then return none
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | return none
    unless ← withReducible (isDefEq lhs look) do return none
    let_expr Option.some _ b := rhs | return none
    return some b

/-- The ghost table `σ₀.names` as a list of `(name, block)`. -/
partial def readNames (σ₀ : Expr) : MetaM (Array (String × Expr)) := do
  let rec go (l : Expr) (acc : Array (String × Expr)) : MetaM (Array (String × Expr)) := do
    let l ← whnfD l
    match_expr l with
    | List.cons _ hd tl =>
      let hd ← whnfD hd
      let_expr Prod.mk _ _ n b := hd | return acc
      let n ← whnfD n
      match n with
      | .lit (.strVal s) => go tl (acc.push (s, b))
      | _ => go tl acc
    | _ => return acc
  go (← mkAppM ``CIR.State.names #[σ₀]) #[]

/-- Binder names and body of `fun x y => …`; binders may carry a type,
`fun (x : Nat) (y z : Int) => …` (the type is the one `cir_loop` gives the
variable: `Int`, `Nat` or `List Int`, so it is not used). -/
partial def funBinders (stx : Term) : TacticM (Array Ident × Term) := do
  let err : TacticM (Array Ident × Term) :=
    throwError "cir_loop: expected `fun x y … => …` with the modified variables as binders"
  let raw := stx.raw
  if raw.isOfKind ``Lean.Parser.Term.paren then return ← funBinders ⟨raw[1]⟩
  unless raw.isOfKind ``Lean.Parser.Term.fun && raw[1].isOfKind ``Lean.Parser.Term.basicFun do
    return ← err
  let basic := raw[1]
  let mut xs : Array Ident := #[]
  for b in basic[0].getArgs do
    if b.isIdent then xs := xs.push ⟨b⟩
    else if b.isOfKind ``Lean.Parser.Term.typeAscription then
      let t := b[1]
      if t.isIdent then xs := xs.push ⟨t⟩
      else if t.isOfKind ``Lean.Parser.Term.app && t[0].isIdent && t[1].getArgs.all (·.isIdent) then
        xs := xs.push ⟨t[0]⟩
        for a in t[1].getArgs do xs := xs.push ⟨a⟩
      else return ← err
    else return ← err
  return (xs, ⟨basic[3]⟩)

partial def funBinderNames (stx : Term) : TacticM (Array Name) := do
  return (← funBinders stx).1.map (·.getId)

/-- The type annotation of each binder of `fun x (y : T) => …`, as written
(`none` without one). -/
partial def funBinderTypes (stx : Term) : TacticM (Array (Option Syntax)) := do
  let raw := stx.raw
  if raw.isOfKind ``Lean.Parser.Term.paren then return ← funBinderTypes ⟨raw[1]⟩
  unless raw.isOfKind ``Lean.Parser.Term.fun && raw[1].isOfKind ``Lean.Parser.Term.basicFun do
    return #[]
  let mut out : Array (Option Syntax) := #[]
  for b in raw[1][0].getArgs do
    if b.isIdent then out := out.push none
    else if b.isOfKind ``Lean.Parser.Term.typeAscription then
      let t := b[1]
      let ty : Option Syntax := if b[3].getNumArgs > 0 then some b[3][0] else none
      if t.isIdent then out := out.push ty
      else
        out := out.push ty
        for _ in t[1].getArgs do out := out.push ty
  return out

/-- Is the binder type annotation the identifier `n` (or `CIR.n`)? -/
def isTyAnn (t? : Option Syntax) (n : String) : Bool :=
  match t? with
  | some t => t.isIdent && (t.getId == Name.mkSimple n || t.getId == `CIR ++ Name.mkSimple n)
  | none => false

/-- `fun (x : Int) (y : Int) => body` from `fun x y => body`: the variables'
values are integers. -/
def intLambda (stx : Term) : TacticM Term := do
  let (xs, b) ← funBinders stx
  let mut body := b
  for x in xs.reverse do
    body ← `(fun ($x : Int) => $body)
  return body

/-- `fun (x : T₁) (y : T₂) => body` from `fun x y => body`. -/
def typedLambda (stx : Term) (tys : Array Term) : TacticM Term := do
  let (xs, b) ← funBinders stx
  let mut body := b
  for (x, t) in (xs.zip tys).reverse do
    body ← `(fun ($x : $t) => $body)
  return body

/-- The iteration goal of a loop rule (tagged `cir_step_goal`). -/
def stepGoal : TacticM MVarId := do
  for g in ← getGoals do
    if let .str _ t := (← g.getTag) then
      if t == "cir_step_goal" then return g
  getMainGoal

/-- Split the loop invariant's user part (`cirH_user`) in every goal:
conjunctions and existentials into hypotheses `cirU_k` (witnesses `cirW_k`),
disjunctions into cases; then substitute the parts `x = t` for a local `x`
(a pointer variable named by its value: `p = .loc b []`). -/
elab "cir_destruct_inv" : tactic => do
  let mut k := 0
  for _ in [0:200] do
    let gs ← getGoals
    let mut progress := false
    let mut out : List MVarId := []
    for g in gs do
      if ← g.isAssigned then continue
      let target? ← g.withContext do
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          let n := d.userName.toString
          unless n == "cirH_user" || n.startsWith "cirU_" do continue
          let ty ← whnfR (← instantiateMVars d.type)
          if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``Or 2 then
            return some (d.userName, ty.getAppFn.constName!)
        return none
      match target? with
      | none => out := out ++ [g]
      | some (hn, c) =>
        progress := true
        let h := mkIdent hn
        let a := mkIdent (Name.mkSimple s!"cirU_{k}")
        let b := mkIdent (Name.mkSimple s!"cirU_{k+1}")
        let w := mkIdent (Name.mkSimple s!"cirW_{k}")
        k := k + 2
        setGoals [g]
        if c == ``And then evalTactic (← `(tactic| obtain ⟨$a:ident, $b:ident⟩ := $h:ident))
        else if c == ``Exists then evalTactic (← `(tactic| obtain ⟨$w:ident, $b:ident⟩ := $h:ident))
        else evalTactic (← `(tactic| rcases $h:ident with $a:ident | $a:ident))
        out := out ++ (← getGoals)
    setGoals out
    unless progress do break
  -- substitute `x = t` parts
  let gs ← getGoals
  let mut out : List MVarId := []
  for g in gs do
    setGoals [g]
    let hs ← g.withContext do
      (← getLCtx).foldlM (init := #[]) fun acc d => do
        if d.isImplementationDetail || !d.userName.toString.startsWith "cirU_" then return acc
        let ty ← instantiateMVars d.type
        let some (α, l, r) := ty.eq? | return acc
        -- only pointers named by their value (an integer variable would get
        -- a `Nat` cast in the state, which the kernel then evaluates)
        unless α.isConstOf ``CIR.Ptr do return acc
        if (l.isFVar && !r.containsFVar l.fvarId!) || (r.isFVar && !l.containsFVar r.fvarId!) then
          return acc.push d.userName
        return acc
    for hn in hs do
      try evalTactic (← `(tactic| subst $(mkIdent hn):ident)) catch _ => pure ()
    out := out ++ (← getGoals)
  setGoals out

syntax (name := cirLoop) "cir_loop " term:max term:max : tactic

@[tactic cirLoop] def evalCirLoop : Tactic := fun stx => Lean.Core.withCurrHeartbeats do
  let invStx : Term := ⟨stx[1]⟩
  let decStx : Term := ⟨stx[2]⟩
  let g ← getMainGoal
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some x := holdsHead? t | throwError "cir_loop: goal is not `Res.holds _ _`"
  let x ← instantiateMVars x
  let (rule, regions, σ₀) ← match x.getAppFn.constName? with
    | some ``CIR.evalFor => pure (``CIR.holds_for, #[x.getArg! 1, x.getArg! 2, x.getArg! 3, x.getArg! 4], x.getArg! 5)
    | some ``CIR.evalWhile => pure (``CIR.holds_while, #[x.getArg! 1, x.getArg! 2, x.getArg! 3], x.getArg! 4)
    | some ``CIR.evalDo => pure (``CIR.holds_do, #[x.getArg! 1, x.getArg! 2], x.getArg! 3)
    | _ => throwError "cir_loop: the goal's head is not a loop (evalFor / evalWhile / evalDo)"
  let ctxE := x.getArg! 0
  -- stack slots the loop stores to, or passes by address to a call
  let mut stored : Array (Expr × Expr) := #[]
  let mut passed : Array (Expr × Expr) := #[]
  for r in regions do
    for (addr, ty) in ← collectStores r do
      if let some blk ← envSlot? σ₀ addr then
        unless ← stored.anyM (fun (b, _) => isDefEq b blk) do
          stored := stored.push (blk, ty)
    for (addr, ty) in ← collectCallArgs r do
      if let some blk ← envSlot? σ₀ addr then
        unless ← passed.anyM (fun (b, _) => isDefEq b blk) do
          passed := passed.push (blk, ty)
  let names ← readNames σ₀
  let nameOf (b : Expr) : MetaM (Option String) := do
    return (← names.findM? fun (_, b') => isDefEq b b').map (·.1)
  let binders ← funBinderNames invStx
  let binderAnns ← funBinderTypes invStx
  -- the user's binders, in order: each names a variable (by its C++ name; a
  -- binder that is not a variable name stands for the hidden iterator
  -- `__beginN` of a range-`for`)
  let mut ordered : Array (Expr × Expr × SlotKind) := #[]
  -- per `ordered` slot: the slot describes the target block of the pointer the
  -- variable holds (a container, an array written through a pointer
  -- parameter, or a pointer held by the caller and moved through a `T**`)
  let mut vias : Array Bool := #[]
  -- per binder: `inl i` (the `ordered` slot `i`) or `inr (g, k)` (member `k`
  -- of the struct of field group `g`)
  let mut binderInfo : Array (Sum Nat (Nat × Nat)) := #[]
  let mut fieldGroups : Array (Expr × Array Nat) := #[]
  for (bn, bix) in binders.zipIdx do
    let ann := binderAnns[bix]?.join
    if isTyAnn ann "Mem" then
      -- the memory at the loop head (no block)
      binderInfo := binderInfo.push (.inl ordered.size)
      ordered := ordered.push (mkNatLit 0, mkConst ``CIR.Ty.void, .mem)
      vias := vias.push false
      continue
    let byName ← (stored ++ passed).findM? fun (b, _) => do
      return (← nameOf b) == some (bn.toString (escape := false))
    let found ← match byName with
      | some sl => pure (some sl)
      | none => passed.findM? fun (b, ty) => do
          let some n ← nameOf b | return false
          return n.startsWith "__begin" && (← slotKindOf? ty) == some .iter &&
            !(← ordered.anyM fun (b', _, _) => isDefEq b b')
    let bnS := bn.toString (escape := false)
    match found with
    | some (blk, ty) =>
      let some k ← slotKindOf? ty |
        throwError "cir_loop: `{bn}`: unsupported variable type {ty} (integers, pointers and iterators)"
      -- a pointer annotated `(p : Ptr)`: named by its value, not an index
      let k := if k == .ptr && isTyAnn ann "Ptr" then SlotKind.ptrv else k
      binderInfo := binderInfo.push (.inl ordered.size)
      ordered := ordered.push (blk, ty, k)
      vias := vias.push false
    | none =>
      match names.find? (·.1 == bnS) with
      | some (_, blk) =>
        -- a variable the loop does not assign: an array whose elements it
        -- writes, or a pointer to a container that it modifies through it
        -- by the variable's type: `T[n]` an array; `T**` a pointer of the
        -- caller that the loop moves (`(*input)++`); a pointer to a
        -- `std::vector`/`std::string` a container; another `T*` an array
        -- written through the pointer
        let (kind, via) ← match ← slotBlockTy? σ₀ blk with
          | some ty =>
            if ty.isAppOfArity ``CIR.Ty.array 2 then pure (SlotKind.arr, false)
            else if ty.isAppOfArity ``CIR.Ty.ptr 1 then
              let t ← whnfR (ty.getArg! 0)
              if t.isAppOfArity ``CIR.Ty.ptr 1 then pure (SlotKind.ptr, true)
              else if t.isAppOfArity ``CIR.Ty.record 1 then
                match ← whnfD (t.getArg! 0) with
                | .lit (.strVal n) =>
                  if (n.splitOn "vector").length > 1 || (n.splitOn "basic_string").length > 1 then
                    pure (SlotKind.vec, true)
                  else pure (SlotKind.arr, true)
                | _ => pure (SlotKind.vec, true)
              else pure (SlotKind.arr, true)
            else pure (SlotKind.vec, true)
          | none => pure (SlotKind.vec, true)
        binderInfo := binderInfo.push (.inl ordered.size)
        ordered := ordered.push (blk, mkConst ``CIR.Ty.void, kind)
        vias := vias.push via
      | none =>
      match ← globalArrBlock? ctxE bnS with
      | some blk =>
        -- a global (or static) array the loop writes
        binderInfo := binderInfo.push (.inl ordered.size)
        ordered := ordered.push (blk, mkConst ``CIR.Ty.void, .arr)
        vias := vias.push false
      | none =>
        -- `p_k`: integer member `k` of the struct the pointer variable `p`
        -- points to
        let parts := bnS.splitOn "_"
        let kTxt := parts.getLastD ""
        let pName := "_".intercalate parts.dropLast
        let some (_, blk) := (if kTxt.toNat?.isSome then names.find? (·.1 == pName) else none) |
          throwError "cir_loop: `{bn}` is not a local variable modified by the loop; modified: {
            ← stored.filterMapM fun (b, _) => nameOf b}"
        let k := kTxt.toNat!
        let gi ← match ← fieldGroups.findIdxM? (fun (b, _) => isDefEq b blk) with
          | some gi => pure gi
          | none => do fieldGroups := fieldGroups.push (blk, #[]); pure (fieldGroups.size - 1)
        fieldGroups := fieldGroups.modify gi fun (b, ks) => (b, ks.push k)
        binderInfo := binderInfo.push (.inr (gi, k))
  -- other variables the loop assigns: assigned before use in each iteration
  let mut scratch : Array (Expr × Expr) := #[]
  for (b, ty) in stored do
    unless ← ordered.anyM (fun (b', _, _) => isDefEq b b') do
      scratch := scratch.push (b, ty)
  if !scratch.isEmpty then
    logInfo m!"cir_loop: not in the invariant (assigned before use in each iteration): {
      ← scratch.filterMapM fun (b, _) => nameOf b}"
  -- name the loop-entry state: `cirH_s0 : σ₀ = <state>` keeps hypotheses small
  let σ₀e ← exprToSyntax σ₀
  let σ₀s : Term := mkIdent (Name.mkSimple "σ₀")
  let hs0 := mkIdent (Name.mkSimple "cirH_s0")
  let hgen := mkIdent (Name.mkSimple "cirH_gen")
  -- the entry state's `next`, as an arithmetic fact for `omega`
  let nextE := unprojMem (← whnfR (← mkAppM ``CIR.Mem.next #[← whnfR (← mkAppM ``CIR.State.mem #[σ₀])]))
  let nextS ← exprToSyntax nextE
  evalTactic (← `(tactic| generalize $hgen:ident : $σ₀e = $(⟨σ₀s⟩):ident))
  evalTactic (← `(tactic| have $hs0:ident := ($hgen:ident).symm))
  evalTactic (← `(tactic| clear $hgen:ident))
  let hn0 := mkIdent (Name.mkSimple "cirH_n0")
  evalTactic (← `(tactic| have $hn0:ident : ($(⟨σ₀s⟩) : CIR.State).mem.next = $nextS := by
    subst $hs0:ident; rfl))
  let blkS ← ordered.mapM fun (b, _) => exprToSyntax b
  let tyS ← ordered.mapM fun (_, ty, _) => exprToSyntax ty
  let kinds := ordered.map (·.2.2)
  let scrBlkS ← scratch.mapM fun (b, _) => exprToSyntax b
  let scrTyS ← scratch.mapM fun (_, ty) => exprToSyntax ty
  -- invariant and variant
  let σId := mkIdent `σ
  -- the block each slot describes: for a container modified through a
  -- pointer variable, the pointer's target at loop entry
  let slotS : Array Term ← ((blkS.zip kinds).zip vias).mapM fun ((b, k), via) =>
    if k == SlotKind.vec || via then `(CIR.State.ptrTarget $σ₀s $b) else pure b
  let grpBlkS ← fieldGroups.mapM fun (b, _) => exprToSyntax b
  let grpTgtS : Array Term ← grpBlkS.mapM fun b => `(CIR.State.ptrTarget $σ₀s $b)
  let ordVals : Array Term ← (slotS.zip kinds).mapM fun (b, k) =>
    match k with
    | .mem => `(CIR.State.mem $σId)
    | .ptrv => `(CIR.State.ptrAt $σId $b)
    | .iter => `(CIR.State.iterAt $σId $b)
    | .ptr => `(CIR.State.ptrIdxAt $σId $b)
    | .arr => `(CIR.State.arrVals $σId $b)
    | .nat => `((CIR.State.intAt $σId $b).toNat)
    | .vec => `(CIR.State.vecInts $σId $b)
    | _ => `(CIR.State.intAt $σId $b)
  let ordTys : Array Term ← kinds.mapM fun k =>
    match k with
    | .int => `(Int)
    | .vec => `(List Int)
    | .arr => `(List CIR.Val)
    | .ptrv => `(CIR.Ptr)
    | .mem => `(CIR.Mem)
    | _ => `(Nat)
  let vals : Array Term ← binderInfo.mapM fun bi => match bi with
    | .inl i => pure ordVals[i]!
    | .inr (g, k) => `(CIR.State.fieldInt $σId $(grpTgtS[g]!) $(Syntax.mkNumLit (toString k)))
  let binderTys : Array Term ← binderInfo.mapM fun bi => match bi with
    | .inl i => pure ordTys[i]!
    | .inr _ => `(Int)
  let invFn ← typedLambda invStx binderTys
  let decFn ← typedLambda decStx binderTys
  let mut inv ← `(($invFn) $vals*)
  for g in (List.range fieldGroups.size).reverse do
    let ks : Array Term := fieldGroups[g]!.2.map fun k => Syntax.mkNumLit (toString k)
    inv ← `(CIR.FieldsSlot $σ₀s $σId $(grpTgtS[g]!) [$ks,*] ∧ $inv)
  for i in (List.range scratch.size).reverse do
    inv ← `(CIR.ScratchSlot $σId $(scrBlkS[i]!) $(scrTyS[i]!) ∧ $inv)
  for i in (List.range ordered.size).reverse do
    if kinds[i]! == SlotKind.mem then
      inv ← `(True ∧ $inv)
    else if kinds[i]! == SlotKind.ptrv then
      inv ← `(CIR.PtrValSlot $σId $(blkS[i]!) $(tyS[i]!) ∧ $inv)
    else if kinds[i]! == SlotKind.iter then
      inv ← `(CIR.IterSlot $σ₀s $σId $(blkS[i]!) ∧ $inv)
    else if kinds[i]! == SlotKind.ptr then
      inv ← `(CIR.PtrSlot $σ₀s $σId $(slotS[i]!) ∧ $inv)
    else if kinds[i]! == SlotKind.arr then
      inv ← `(CIR.ArrSlot $σ₀s $σId $(slotS[i]!) ∧ $inv)
    else if kinds[i]! == SlotKind.vec then
      inv ← `(CIR.VecSlot $σ₀s $σId $(slotS[i]!) ∧ $inv)
    else
      inv ← `(CIR.IntSlot $σId $(blkS[i]!) $(tyS[i]!) ∧ $inv)
  let hasMem := kinds.contains SlotKind.mem
  let ordBlk := ((slotS.zip kinds).filter (·.2 != SlotKind.mem)).map (·.1)
  let allBlk := ordBlk ++ scrBlkS ++ grpTgtS
  if hasMem then
    -- the function's own frame starts at its first local (the last name)
    let some (_, lo) := names.back? | throwError "cir_loop: no local variables for a `mem` binder"
    let loS ← exprToSyntax lo
    inv ← `(CIR.LoopFrameFrom $σ₀s $loS [$allBlk,*] $σId ∧ $inv)
  else if (← getOptions).getBool `cir.loopWF false then
    inv ← `(CIR.LoopFrameW $σ₀s [$allBlk,*] $σId ∧ $inv)
  else
    inv ← `(CIR.LoopFrame $σ₀s [$allBlk,*] $σId ∧ $inv)
  let useW := !hasMem && (← getOptions).getBool `cir.loopWF false
  let invFun ← `(fun ($σId : CIR.State) => $inv)
  let varFun ← `(fun ($σId : CIR.State) => ((($decFn) $vals*) : Int).toNat)
  let ruleId := mkIdent rule
  evalTactic (← `(tactic| refine $ruleId (Inv := $invFun) (V := $varFun) ?cir_step_goal $σ₀s ?cir_init_goal))
  -- the iteration: name the hypotheses (`cirH_…`) so that `cir_step` uses them
  let nm (s : String) : Ident := mkIdent (Name.mkSimple s)
  let σi := nm "σ"
  let hInv := nm "cirH_inv"
  let hEnv := nm "cirH_env"
  let hNames := nm "cirH_names"
  let hNext := nm "cirH_next"
  let hFrame := nm "cirH_frame"
  let hUser := nm "cirH_user"
  let nslots := ordered.size + scratch.size + fieldGroups.size
  let hRest0 := if nslots = 0 then hUser else nm "cirH_rest"
  if useW then
    let hLW := nm "cirH_loopwf"
    let hWF := nm "cirH_wf"
    evalTactic (← `(tactic| case' cir_step_goal =>
      intro $σi:ident $hInv:ident
      obtain ⟨⟨⟨$hEnv:ident, $hNames:ident, $hNext:ident, $hFrame:ident⟩, $hLW:ident⟩, $hRest0:ident⟩ :=
        $hInv:ident))
    -- the memory at the loop head is well formed when the entry memory is
    evalTactic (← `(tactic| case' cir_step_goal =>
      try (have $hWF:ident : ($σi:ident).mem.WF :=
        $hLW:ident (by first | assumption | cir_wf | (subst_vars; dsimp only; cir_wf)))))
  else
    evalTactic (← `(tactic| case' cir_step_goal =>
      intro $σi:ident $hInv:ident
      obtain ⟨⟨$hEnv:ident, $hNames:ident, $hNext:ident, $hFrame:ident⟩, $hRest0:ident⟩ := $hInv:ident))
  let mut cur := hRest0
  for i in [0:nslots] do
    let h := nm s!"cirH_slot{i}"
    let rest := if i + 1 = nslots then hUser else nm s!"cirH_rest{i}"
    if i ≥ ordered.size + scratch.size then
      evalTactic (← `(tactic| case' cir_step_goal => obtain ⟨$h:ident, $rest:ident⟩ := $cur:ident))
    else if i ≥ ordered.size then
      let v := nm s!"cir_scratch{i}"
      evalTactic (← `(tactic| case' cir_step_goal => obtain ⟨⟨$v:ident, $h:ident⟩, $rest:ident⟩ := $cur:ident))
    else if kinds[i]! == SlotKind.iter || kinds[i]! == SlotKind.ptr || kinds[i]! == SlotKind.ptrv ||
        kinds[i]! == SlotKind.mem then
      evalTactic (← `(tactic| case' cir_step_goal => obtain ⟨$h:ident, $rest:ident⟩ := $cur:ident))
    else if kinds[i]! == SlotKind.vec then
      let gn := nm s!"cir_gen{i}"
      evalTactic (← `(tactic| case' cir_step_goal => obtain ⟨⟨$gn:ident, $h:ident⟩, $rest:ident⟩ := $cur:ident))
    else if kinds[i]! == SlotKind.arr then
      let hl := nm s!"cirH_len{i}"
      evalTactic (← `(tactic| case' cir_step_goal => obtain ⟨⟨$h:ident, $hl:ident⟩, $rest:ident⟩ := $cur:ident))
    else
      let hr := nm s!"cirH_range{i}"
      evalTactic (← `(tactic| case' cir_step_goal => obtain ⟨⟨$h:ident, $hr:ident⟩, $rest:ident⟩ := $cur:ident))
      evalTactic (← `(tactic| case' cir_step_goal => simp only [CIR.fitsTy, CIR.inRange_eq_true_iff,
        CIR.intMin_s8, CIR.intMax_s8, CIR.intMin_s16, CIR.intMax_s16, CIR.intMin_s32, CIR.intMax_s32,
        CIR.intMin_s64, CIR.intMax_s64, CIR.intMin_u, CIR.intMax_u8, CIR.intMax_u16, CIR.intMax_u32,
        CIR.intMax_u64] at $hr:ident))
    cur := rest
  -- mined candidates (`Cand k p`) are plain facts in the hypothesis
  evalTactic (← `(tactic| case' cir_step_goal => try simp only [CIR.Cand] at $hUser:ident))
  -- the container blocks, as computed from the entry state (`bv`, not
  -- `σ₀.ptrTarget a`), everywhere: generalize, compute, substitute
  for i in [0:ordered.size] do
    if kinds[i]! == SlotKind.vec || vias[i]! then
      let t := nm s!"cir_tgt{i}"
      let ht := nm s!"cirH_tgt{i}"
      evalTactic (← `(tactic| case' cir_step_goal =>
        generalize $ht:ident : CIR.State.ptrTarget $σ₀s $(blkS[i]!) = $t:ident at *))
      evalTactic (← `(tactic| case' cir_step_goal => cir_simp_hyp $ht:ident))
      evalTactic (← `(tactic| case' cir_step_goal => subst $t:ident))
  for g in [0:fieldGroups.size] do
    let t := nm s!"cir_ftgt{g}"
    let ht := nm s!"cirH_ftgt{g}"
    evalTactic (← `(tactic| case' cir_step_goal =>
      generalize $ht:ident : CIR.State.ptrTarget $σ₀s $(grpBlkS[g]!) = $t:ident at *))
    evalTactic (← `(tactic| case' cir_step_goal => cir_simp_hyp $ht:ident))
    evalTactic (← `(tactic| case' cir_step_goal => subst $t:ident))
  -- bounds for fast key comparisons: the entry range lies below the current
  -- `next`, and so does every block bounded by a hypothesis `b < t`
  let hnx := nm "cirH_nx"
  evalTactic (← `(tactic| case' cir_step_goal =>
    have $hnx:ident : $nextS ≤ ($σi:ident).mem.next := $hn0:ident ▸ $hNext:ident))
  let g ← getMainGoal
  let bounds ← g.withContext do
    let mut out : Array Expr := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      if let some (_, _, lhs, _) := ty.app4? ``LT.lt then
        if lhs.isFVar && (← inferType lhs).isConstOf ``Nat then
          unless out.contains lhs do out := out.push lhs
    return out
  for (b, idx) in bounds.zipIdx do
    let bS ← exprToSyntax b
    let hb := nm s!"cirH_lt{idx}"
    evalTactic (← `(tactic| case' cir_step_goal =>
      try have $hb:ident : $bS < ($σi:ident).mem.next := by omega))
  -- struct members: their values to the user's names, then the struct's
  -- block from the entry state
  for (bi, bix) in binderInfo.zipIdx do
    let .inr (g, k) := bi | continue
    let j := ordered.size + scratch.size + g
    let gl ← stepGoal
    let tgt? ← gl.withContext do
      let some d := (← getLCtx).findFromUserName? (Name.mkSimple s!"cirH_slot{j}") | return none
      let ty ← instantiateMVars d.type
      let some (_, lhs, _) := ty.eq? | return none
      return some (lhs.getArg! 1)
    if let some tgt := tgt? then
      let tgtS ← exprToSyntax tgt
      let x := mkIdent binders[bix]!
      let hv := nm s!"cirH_fval{bix}"
      evalTactic (← `(tactic| case' cir_step_goal =>
        generalize $hv:ident : CIR.State.fieldInt $σi:ident $tgtS $(Syntax.mkNumLit (toString k)) = $x:ident at *))
  for g in [0:fieldGroups.size] do
    let h := nm s!"cirH_slot{ordered.size + scratch.size + g}"
    evalTactic (← `(tactic| case' cir_step_goal => cir_simp_hyp $h:ident))
  -- generalize the variables' values to the user's names
  for (bi, bix) in binderInfo.zipIdx do
    let .inl i := bi | continue
    let x := mkIdent binders[bix]!
    let hv := nm s!"cirH_val{i}"
    if kinds[i]! == SlotKind.vec then
      -- the container's elements; its block (generation, kind) from the entry state
      let h := nm s!"cirH_slot{i}"
      let g ← stepGoal
      let tgt? ← g.withContext do
        let some d := (← getLCtx).findFromUserName? (Name.mkSimple s!"cirH_slot{i}") | return none
        let ty ← instantiateMVars d.type
        let some (_, lhs, _) := ty.eq? | return none
        return some (lhs.getArg! 1)
      if let some tgt := tgt? then
        let tgtS ← exprToSyntax tgt
        evalTactic (← `(tactic| case' cir_step_goal =>
          generalize $hv:ident : CIR.State.vecInts $σi:ident $tgtS = $x:ident at *))
      evalTactic (← `(tactic| case' cir_step_goal => cir_simp_hyp $h:ident))
    else if kinds[i]! == SlotKind.iter then
      -- the iterator's value at the loop head, computed from its entry value
      let h := nm s!"cirH_slot{i}"
      evalTactic (← `(tactic| case' cir_step_goal => cir_simp_hyp $h:ident))
      evalTactic (← `(tactic| case' cir_step_goal =>
        generalize $hv:ident : CIR.State.iterAt $σi:ident $(blkS[i]!) = $x:ident at *))
    else if kinds[i]! == SlotKind.mem then
      -- the memory stays `σ.mem`: the invariant's facts are about it
      pure ()
    else if kinds[i]! == SlotKind.ptrv then
      let h := nm s!"cirH_slot{i}"
      evalTactic (← `(tactic| case' cir_step_goal => cir_simp_hyp $h:ident))
      evalTactic (← `(tactic| case' cir_step_goal =>
        generalize $hv:ident : CIR.State.ptrAt $σi:ident $(blkS[i]!) = $x:ident at *))
    else if kinds[i]! == SlotKind.arr || kinds[i]! == SlotKind.ptr then
      let h := nm s!"cirH_slot{i}"
      evalTactic (← `(tactic| case' cir_step_goal => cir_simp_hyp $h:ident))
      -- the block the slot describes (for a target of a pointer, as computed
      -- from the entry state above)
      let blkT ← if vias[i]! then do
          let g ← stepGoal
          let tgt? ← g.withContext do
            let some d := (← getLCtx).findFromUserName? (Name.mkSimple s!"cirH_slot{i}") | return none
            let ty ← instantiateMVars d.type
            let some (_, lhs, _) := ty.eq? | return none
            return some (lhs.getArg! 1)
          match tgt? with
          | some tgt => exprToSyntax tgt
          | none => pure blkS[i]!
        else pure blkS[i]!
      if kinds[i]! == SlotKind.arr then
        -- the array's elements at the loop head; its length from the entry state
        let hl := nm s!"cirH_len{i}"
        evalTactic (← `(tactic| case' cir_step_goal => cir_simp_hyp $hl:ident))
        evalTactic (← `(tactic| case' cir_step_goal =>
          generalize $hv:ident : CIR.State.arrVals $σi:ident $blkT = $x:ident at *))
      else
        -- the pointer's value at the loop head: its entry value moved to the
        -- element the invariant names
        evalTactic (← `(tactic| case' cir_step_goal =>
          generalize $hv:ident : CIR.State.ptrIdxAt $σi:ident $blkT = $x:ident at *))
    else if kinds[i]! == SlotKind.nat then
      -- an unsigned variable: its value `v` (an integer, so that the state
      -- stays free of `Nat` casts, which the kernel would evaluate against the
      -- type's bounds) is the natural number `x` of the invariant,
      -- `cir_nat : v = ↑x`; the leftover goals are stated over `x`
      let v := nm s!"cir_v{i}"
      evalTactic (← `(tactic| case' cir_step_goal =>
        generalize $hv:ident : CIR.State.intAt $σi:ident $(blkS[i]!) = $v:ident at *))
      let hx := nm s!"cir_nat{i}"
      evalTactic (← `(tactic| case' cir_step_goal =>
        obtain ⟨$x:ident, $hx:ident⟩ : ∃ n : Nat, $v:ident = (n : Int) := ⟨($v:ident).toNat, by omega⟩))
      evalTactic (← `(tactic| case' cir_step_goal =>
        try simp only [$hx:ident, Int.toNat_natCast] at $hUser:ident))
    else
      evalTactic (← `(tactic| case' cir_step_goal =>
        generalize $hv:ident : CIR.State.intAt $σi:ident $(blkS[i]!) = $x:ident at *))
  -- with a `mem` binder or a pointer named by its value, the invariant
  -- carries the memory facts and the pointers: split it so that its
  -- equations (`mem.blocks b = …`, `p = listPtr bs k`) are used
  if kinds.contains SlotKind.mem || kinds.contains SlotKind.ptrv then
    evalTactic (← `(tactic| case' cir_step_goal => cir_destruct_inv))

/-- Report on the goals left by symbolic execution with a mined invariant: a
goal `Cand k p` that `cir_close` cannot prove prints `@FAIL k` (the
candidate is not established or not preserved); any other goal prints
`@OTHER` and the goal. Every goal is then admitted: this is a diagnosis
step for invariant search (`tools/cirinv.py`), not part of a proof. -/
elab "cir_houdini_report" : tactic => do
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    let t ← instantiateMVars (← g.getType)
    if t.isAppOfArity ``CIR.Cand 2 then
      let k ← whnfD (t.getArg! 0)
      let kTxt := match k.rawNatLit? with
        | some n => toString n
        | none => (k.nat?.map toString).getD "?"
      let s ← saveState
      let ok ← (do
          evalTactic (← `(tactic| unfold CIR.Cand))
          evalTactic (← `(tactic| cir_close'))
          pure (← getGoals).isEmpty)
        <|> (do s.restore; pure false)
      unless ok do
        s.restore
        logInfo m!"@FAIL {kTxt}"
        admitGoal g
    else
      let fmt ← g.withContext do
        withOptions (fun o => o.setBool `pp.deepTerms false)
          (ppExpr t)
      logInfo m!"@OTHER {fmt}"
      admitGoal g
  setGoals []

/-- Print what `cir_loop` would use at the loop at the head of the goal: the
variables the loop assigns (`@STORED name:kind`), those whose address it
passes to calls (`@PASSED name:kind`), and all variables in scope
(`@SCOPE`). For invariant search tools. -/
elab "cir_loop_info" : tactic => do
  let g ← getMainGoal
  g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some x := holdsHead? t | throwError "cir_loop_info: goal is not `Res.holds _ _`"
  let x ← instantiateMVars x
  let (regions, σ₀) ← match x.getAppFn.constName? with
    | some ``CIR.evalFor => pure (#[x.getArg! 1, x.getArg! 2, x.getArg! 3, x.getArg! 4], x.getArg! 5)
    | some ``CIR.evalWhile => pure (#[x.getArg! 1, x.getArg! 2, x.getArg! 3], x.getArg! 4)
    | some ``CIR.evalDo => pure (#[x.getArg! 1, x.getArg! 2], x.getArg! 3)
    | _ => throwError "cir_loop_info: the goal's head is not a loop"
  let names ← readNames σ₀
  let nameOf (b : Expr) : MetaM (Option String) := do
    return (← names.findM? fun (_, b') => isDefEq b b').map (·.1)
  let kindTxt (ty : Expr) : MetaM String := do
    match ← slotKindOf? ty with
    | some .int => pure "int" | some .nat => pure "nat" | some .iter => pure "iter"
    | some .ptr => pure "ptr"
    | _ => pure "other"
  let mut stored : Array String := #[]
  let mut passed : Array String := #[]
  for r in regions do
    for (addr, ty) in ← collectStores r do
      if let some blk ← envSlot? σ₀ addr then
        if let some n ← nameOf blk then
          let e := n ++ ":" ++ (← kindTxt ty)
          unless stored.contains e do stored := stored.push e
    for (addr, ty) in ← collectCallArgs r do
      if let some blk ← envSlot? σ₀ addr then
        if let some n ← nameOf blk then
          let e := n ++ ":" ++ (← kindTxt ty)
          unless passed.contains e do passed := passed.push e
  logInfo m!"@STORED {" ".intercalate stored.toList}"
  logInfo m!"@PASSED {" ".intercalate passed.toList}"
  logInfo m!"@SCOPE {" ".intercalate (names.toList.map (·.1))}"

end CIR.Tactic

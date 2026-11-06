import EquivLean.Bridge.TS.AutoCouple
import EquivLean.Bridge.TS.Corr
import EquivLean.Bridge.Aeneas.AutoCouple

/-!
# TypeScript ↔ Rust: generated couplings for lockstep loops

`ts_rust_lockstep (with [lemmas…])?` pairs a TypeScript loop (`while`/`for` or `do … while`, in
the goal or in the source hypothesis `hs`) with an Aeneas `loop` (in the other one) in lockstep,
like `ts_lockstep_x J, R using …`, but generates `J` and `R` and closes the three goals.

The coupling `J` of a TypeScript loop state `(env, w)` and a Rust loop state (a tuple):
* the world is the one at loop entry (the TypeScript loop does not write the heap);
* the environment is the one at loop entry, except that each mutable slot paired with a Rust
  loop variable holds that variable as a `number`: `F64.ofNat x.val` for `usize`, `u8`, `u16`,
  `F64.ofUint32 x.bv` for `u32`, `F64.ofInt32 x.bv` for `i32` (and `.bool b` for a `bool`).
  The mutable slots are paired with the Rust loop variables in declaration order (the slots from
  the bottom of the environment, the components of the Rust state in order); a second attempt
  pairs them in the order of their first assignment in the two loop bodies;
* the loop bounds of the Rust loop (`i.val ≤ v.val.length` for `i < v.len()`, see
  `Bridge/Aeneas/AutoCouple.lean`), and the entry values of unpaired Rust variables that no
  iteration changes.

The loop-exit relation is not generated: `R o₁ o₂ := K₂ o₂ → K₁ o₁`, the implication between the
two continuations after the loops (as in `Bridge/TS/AutoCouple.lean`), so the `exit` goal is
trivial and the code after the loops is checked inside the step.  The step runs one iteration
of the TypeScript loop (`ts_auto_simp`, case splits on its conditions), then the Rust body
(`aeneas_wp`, `split_ifs`), and closes the leaves: contradictory branches by `omega` or
`scalar_tac`, the coupling after the iteration by `simp` with the `lemmas` (e.g. the int32
bridge of one iteration, `Bridge/TS/Corr.lean`, and the Rust `bv` lemmas, as step lemmas; facts
relating the inputs), the exit leaf by the continuations.  Each attempt either closes every goal
or is undone; if none succeeds the goal is left unchanged and the tactic fails with the couplings
it tried.

* `sim_ts_rust [defs…] (with [lemmas…])?` on `Sim R t s` (one side a TypeScript call, the other a
  Rust function): `ts_start [defs…]` (which also unfolds the Rust definitions among `defs`), then
  `ts_rust_lockstep`.
* `equiv_ts_rust [defs…] (with [lemmas…])?`: both directions of an `Equiv` goal.
* `ts_rust_lockstep! …` runs only the first attempt and reports its error (for debugging).

`bor_zero_add_ofInt32_ofNat` (`(y + n) | 0` on an int32 and a small natural number) completes
the int32 bridge of `Bridge/TS/Corr.lean` for step lemmas of hashes such as `h = (31 * h + b) | 0`.

Not covered: `for … of` loops on the TypeScript side, TypeScript loops that write the heap, Rust
loop variables without a `number`/`boolean` representation (`u64`, `i64`, `u128`, slices,
vectors), and couplings that relate loop variables to each other.  The arithmetic of one
iteration is not derived: it comes from the given lemmas.
-/

open _root_.Aeneas _root_.Aeneas.Std

namespace EquivLean.TS
open StrictTS Lean Elab Tactic Meta Parser.Tactic

/-- `(y + n) | 0` on an int32 `y` and a natural number `n ≤ 2^31` (e.g. a byte): the int32 sum
(the double sum is exact, `| 0` wraps it). -/
theorem bor_zero_add_ofInt32_ofNat (y : BitVec 32) {n : Nat} (h : n ≤ 2 ^ 31) :
    ((F64.ofInt32 y) + F64.ofNat n).bor (F64.ofNat 0) = F64.ofInt32 (y + BitVec.ofNat 32 n) := by
  have h1 := BitVec.toInt_lt (x := y)
  have h2 := BitVec.le_toInt y
  norm_num at h1 h2
  have hy : F64.Safe y.toInt := by simp only [F64.Safe]; omega
  have hn : F64.Safe (n : Int) := by simp only [F64.Safe]; omega
  have hs : F64.Safe (y.toInt + n) := by simp only [F64.Safe]; omega
  rw [F64.ofInt32_eq, F64.ofNat_eq_ofInt n, F64.add_ofInt hy hn hs]
  simp only [F64.bor, F64.toInt32_ofInt hs, toInt32_ofNat (n := 0) (by omega)]
  congr 1
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_natCast]
  simp

namespace AutoXLang

/-- A TypeScript loop run `wp (JS.exec L w) K`: the entry environment, the world, the
postcondition, and the blocks of the loop (body and step). -/
structure TsLoop where
  env : Expr
  w : Expr
  K : Expr
  blocks : Array Expr
  deriving Inhabited

/-- `wp (JS.exec L w) K` with `L` a `while`/`for` (`evalLoop`) or `do … while` (`evalDo`). -/
def tsLoop? (e : Expr) : MetaM (Option TsLoop) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  unless e.isAppOfArity ``EquivLean.wp 5 do return none
  let c := (e.getArgD 3 e).cleanupAnnotations
  unless c.isAppOfArity ``StrictTS.JS.exec 4 do return none
  let L := (c.getArgD 2 c).cleanupAnnotations
  -- evalLoop {TT} I P {Γ} {ρ} c body step env; evalDo {TT} I P {Γ} {ρ} body c env
  if L.isAppOfArity ``StrictTS.evalLoop 9 then
    return some ⟨L.getArgD 8 L, c.getArgD 3 c, e.getArgD 4 e, #[L.getArgD 6 L, L.getArgD 7 L]⟩
  if L.isAppOfArity ``StrictTS.evalDo 8 then
    return some ⟨L.getArgD 7 L, c.getArgD 3 c, e.getArgD 4 e, #[L.getArgD 5 L]⟩
  return none

/-- `wp (loop B x) K` (Aeneas): the state type, the body, the initial state, the
postcondition. -/
def rustLoop? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  unless e.isAppOfArity ``EquivLean.wp 5 do return none
  let some (σ, B, x) := EquivLean.Aeneas.AutoCouple.loopOf? (e.getArgD 3 e) | return none
  return some (σ, B, x, e.getArgD 4 e)

/-- The `Env.cons` cells of an explicit environment, top first, and its `Env.nil`. -/
partial def envCells (e : Expr) : MetaM (Option (Array Expr × Expr)) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  if e.isAppOfArity ``StrictTS.Env.cons 5 then
    let some (rest, nil) ← envCells (e.getArgD 4 e) | return none
    return some (#[e] ++ rest, nil)
  else if e.isAppOfArity ``StrictTS.Env.nil 1 then return some (#[], e)
  else return none

/-- The type and mutability of the slot of an environment cell. -/
def cellSlot (cell : Expr) : MetaM (Expr × Bool) := do
  let s := cell.getArgD 1 cell
  let ty ← whnfD (mkApp (mkConst ``StrictTS.Slot.ty) s)
  let m ← whnfD (mkApp (mkConst ``StrictTS.Slot.mutable) s)
  return (ty, m.isConstOf ``Bool.true)

/-- The environment of `cells` (ending in `nil`) with the values `vals` where given. -/
def rebuildEnv (cells : Array Expr) (nil : Expr) (vals : Array (Option Expr)) : Expr := Id.run do
  let mut acc := nil
  for k' in [0:cells.size] do
    let k := cells.size - 1 - k'
    let cell := cells.getD k nil
    let v := (vals.getD k none).getD (cell.getArgD 3 cell)
    acc := mkAppN cell.getAppFn #[cell.getArgD 0 cell, cell.getArgD 1 cell, cell.getArgD 2 cell, v, acc]
  return acc

/-- The index of an assignable variable `MVar.here`/`MVar.there …`. -/
partial def mvarIndex? (m : Expr) : Option Nat :=
  let m := m.cleanupAnnotations
  if m.isAppOfArity ``StrictTS.MVar.here 2 then some 0
  else if m.isAppOfArity ``StrictTS.MVar.there 4 then (mvarIndex? (m.getArgD 3 m)).map (· + 1)
  else none

/-- The environment positions (from the top, at loop entry) assigned by a block, in order of
first assignment; `depth` counts the declarations of the block around the statement. -/
partial def assignOrder (e : Expr) (depth : Nat) : StateM (Array Nat) Unit := do
  let e := e.cleanupAnnotations
  if e.isAppOfArity ``StrictTS.Stmt.assign 6 then
    if let some k := mvarIndex? (e.getArgD 4 e) then
      if k ≥ depth then
        unless (← get).contains (k - depth) do modify (·.push (k - depth))
  if e.isAppOfArity ``StrictTS.Block.decl 6 || e.isAppOfArity ``StrictTS.Block.await 6 then
    assignOrder (e.getArgD 4 e) depth
    assignOrder (e.getArgD 5 e) (depth + 1)
    return
  if e.isAppOfArity ``StrictTS.AltsS.cons 6 then
    assignOrder (e.getArgD 4 e) (depth + 1)
    assignOrder (e.getArgD 5 e) depth
    return
  match e with
  | .app .. => for a in e.getAppArgs do assignOrder a depth
  | .lam _ _ b _ => assignOrder b depth
  | _ => pure ()

/-- How a Rust loop variable of type `ty` is held by a TypeScript value: the value for the loop
variable `c` (`Val.num` of a double, `Val.bool`), when the type has a representation. -/
def reprVal? (TT ty c : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR (← instantiateMVars ty)
  let num (x : Expr) : Expr := mkApp2 (mkConst ``StrictTS.Val.num) TT x
  if ty.isConstOf ``Bool then return some (mkApp2 (mkConst ``StrictTS.Val.bool) TT c)
  if ty.isAppOfArity ``UScalar 1 then
    let k ← whnfD ty.appArg!
    if k.isConstOf ``UScalarTy.Usize || k.isConstOf ``UScalarTy.U8 || k.isConstOf ``UScalarTy.U16 then
      return some (num (mkApp (mkConst ``StrictTS.F64.ofNat) (← mkAppM ``UScalar.val #[c])))
    if k.isConstOf ``UScalarTy.U32 then
      return some (num (mkApp (mkConst ``StrictTS.F64.ofUint32) (mkApp (mkConst ``U32.bv) c)))
    return none
  if ty.isAppOfArity ``IScalar 1 then
    let k ← whnfD ty.appArg!
    if k.isConstOf ``IScalarTy.I32 then
      return some (num (mkApp (mkConst ``StrictTS.F64.ofInt32) (mkApp (mkConst ``I32.bv) c)))
  return none

/-- The order of first assignment of the variables of a Rust loop body: the components of the
first state passed to `cont`, the one bound first coming first; components passed on
unchanged last. -/
def rustAssignOrder (cs : Array Expr) (conts : Array Expr) : MetaM (Array Nat) := do
  let n := cs.size
  let some v := conts[0]? | return (List.range n).toArray
  let some vs ← EquivLean.Aeneas.AutoCouple.tupleCompsN v n | return (List.range n).toArray
  let key (k : Nat) : Int := match vs.getD k v with
    | .bvar j => j
    | _ => -1
  return (List.range n).toArray.qsort fun a b => key a > key b || (key a == key b && a < b)

/-- The generated coupling candidates for the TypeScript loop `ts` and the Rust loop
`loop B x` with state type `σ`; `tsTarget` when the TypeScript loop is the target. -/
def couplings (ts : TsLoop) (σ B x : Expr) (tsTarget : Bool) : MetaM (Array Expr) := do
  let some (cells, nil) ← envCells ts.env
    | throwError "ts_rust_lockstep: the TypeScript loop environment is not explicit"
  let TT := (cells[0]?.map fun c => c.getArgD 0 c).getD (nil.getArgD 0 nil)
  let mut slots : Array (Expr × Bool) := #[]
  for c in cells do slots := slots.push (← cellSlot c)
  let side ← EquivLean.Aeneas.AutoCouple.side σ B x #[]
  let n := side.comps.size
  -- TypeScript mutable slots: declaration order (from the bottom), first assignment order
  let decl := ((List.range cells.size).reverse.filter fun k => (slots.getD k default).2).toArray
  let (_, asg) := (ts.blocks.forM fun b => assignOrder b 0).run #[]
  let asg := asg.filter (decl.contains ·) ++ decl.filter fun k => !asg.contains k
  -- Rust loop variables: in order, and in the order of first assignment
  let mut decls : Array (Name × Expr) := #[]
  for ty in side.comps do decls := decls.push (Name.mkSimple s!"c{decls.size}", ty)
  let rOrder ← withLocalDeclsDND decls fun cs => do
    let (_, st) ← (EquivLean.Aeneas.AutoCouple.scan cs 512
      (mkApp B (← EquivLean.Aeneas.AutoCouple.stateTuple cs))).run {}
    rustAssignOrder cs st.conts
  let pairings : Array (Array (Nat × Nat)) :=
    let p₁ := (decl.zip (List.range n).toArray)
    let p₂ := (asg.zip rOrder)
    if p₂.toList.mergeSort (fun a b => a.1 ≤ b.1) == p₁.toList.mergeSort (fun a b => a.1 ≤ b.1)
    then #[p₁] else #[p₁, p₂]
  let σT ← inferType ts.env
  let tsσ ← mkAppM ``Prod #[σT, ← inferType ts.w]
  let mut out : Array Expr := #[]
  for pairs in pairings do
    let J? ← withLocalDeclD `s₁ (if tsTarget then tsσ else σ) fun s₁ =>
      withLocalDeclD `s₂ (if tsTarget then σ else tsσ) fun s₂ => do
        let (st, sr) := if tsTarget then (s₁, s₂) else (s₂, s₁)
        let mut vals : Array (Option Expr) := Array.replicate cells.size none
        for (k, j) in pairs do
          let some v ← reprVal? TT (side.comps.getD j default)
              (← EquivLean.Aeneas.AutoCouple.stateProj sr n j) | return none
          -- the slot type must be the one of the value
          let (sty, _) := slots.getD k default
          unless (sty.isConstOf ``StrictTS.Ty.num && v.isAppOf ``StrictTS.Val.num) ||
              (sty.isConstOf ``StrictTS.Ty.bool && v.isAppOf ``StrictTS.Val.bool) do return none
          vals := vals.set! k (some v)
        let mut facts : Array Expr := #[
          ← mkEq (← mkAppM ``Prod.snd #[st]) ts.w,
          ← mkEq (← mkAppM ``Prod.fst #[st]) (rebuildEnv cells nil vals)]
        for j in [0:n] do
          if !pairs.any (·.2 == j) && side.unchanged.getD j false then
            facts := facts.push (← mkEq (← EquivLean.Aeneas.AutoCouple.stateProj sr n j)
              (side.init.getD j sr))
        for bd in side.bounds do
          if let some f ← EquivLean.Aeneas.AutoCouple.boundFact?
              (← EquivLean.Aeneas.AutoCouple.stateProj sr n bd.comp) bd then
            facts := facts.push f
        return some (← mkLambdaFVars #[s₁, s₂] (mkAndN facts.toList))
    if let some J := J? then
      let J ← instantiateMVars J
      unless out.contains J do out := out.push J
  return out

/-- The `rintro` pattern of a Rust loop state with `n` variables. -/
def rustPat (n : Nat) : MacroM (TSyntax `rcasesPat) := do
  if n ≤ 1 then return ← `(rcasesPat| $(mkIdent `c0):ident)
  let ps ← (List.range n).toArray.mapM fun k =>
    `(rcasesPat| $(mkIdent (Name.mkSimple s!"c{k}")):ident)
  `(rcasesPat| ⟨$ps,*⟩)

/-- The number of conjuncts of a coupling `fun s₁ s₂ => a ∧ b ∧ …`. -/
def conjuncts (J : Expr) : Nat := Id.run do
  let mut b := J
  while b.isLambda do b := b.bindingBody!
  let mut k := 1
  while b.isAppOfArity ``And 2 do
    k := k + 1
    b := b.appArg!
  return k

end AutoXLang

/-- One iteration of both loops and the leaves (the `step` goal of `ts_rust_lockstep`): see the
module doc. -/
syntax (name := tsRustStep) "ts_rust_step" " [" ident,* "]" " [" simpArg,* "]" : tactic

/-- The leaf where both loops leave: from the source continuation to the target one. -/
syntax (name := tsRustExitLeaf) "ts_rust_exit_leaf" " [" simpArg,* "]" : tactic

macro_rules
  | `(tactic| ts_rust_exit_leaf [$args,*]) => do
    let args : EquivLean.Aeneas.SimpArgs := args.getElems
    `(tactic| (intro hq; simp only [ts_sym, EquivLean.wp_some, $args,*] at hq ⊢; refine ⟨_, hq, ?_⟩; first | (exact ⟨_, rfl, rfl⟩) | (simp; done)))

macro_rules
  | `(tactic| ts_rust_step [$defs,*] [$args,*]) => do
    let defArgs : EquivLean.Aeneas.SimpArgs := defs.getElems.map EquivLean.Aeneas.identSimpArg
    let args' : EquivLean.Aeneas.SimpArgs := args.getElems
    `(tactic| (
      (try ts_auto_simp)
      iterate 4 (all_goals (try (ts_split_if <;> (try ts_auto_simp))))
      all_goals (first | refine EquivLean.TS.sim_some_of_wp ?_ | rw [EquivLean.TS.sim_some_iff])
      all_goals (try (aeneas_wp [rust_loop_body, $defArgs,*]))
      all_goals (try split_ifs)
      all_goals (try simp only [EquivLean.StepRel, EquivLean.TS.stepCls_inr,
        EquivLean.TS.stepCls_inl, EquivLean.TS.stepCls_error, EquivLean.Aeneas.loopCls_cont,
        EquivLean.Aeneas.loopCls_done, EquivLean.Aeneas.loopCls_error])
      all_goals (try (exfalso; omega))
      all_goals (try (exfalso; scalar_tac))
      all_goals (try (simp (disch := omega) only [true_and, and_true, StrictTS.Env.cons.injEq,
        StrictTS.Val.num.injEq, StrictTS.Val.bool.injEq, UScalar.ofNatCore_val_eq, $args',*]))
      all_goals (try omega)
      all_goals (try (ts_rust_exit_leaf [$args,*]))))

/-- Lockstep of a TypeScript loop and an Aeneas `loop` with a generated coupling (see the module
doc); `defs` are unfolded in the Rust body, `args` are used to close the leaves. -/
syntax (name := tsRustLockstep) "ts_rust_lockstep" (" [" ident,* "]")?
  (" with" " [" simpArg,* "]")? : tactic

/-- Try the generated couplings in order on the main goal. -/
def runTsRustLockstep (defs : Array Ident) (args : EquivLean.Aeneas.SimpArgs)
    (debug : Bool := false) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
  let lctx ← getLCtx
  let some hd := lctx.findFromUserName? `hs
    | throwError "ts_rust_lockstep: no source hypothesis `hs`"
  let tgt ← instantiateMVars (← g.getType)
  let (tsTarget, ts, rust) ← do
    if let some ts ← AutoXLang.tsLoop? tgt then
      let some r ← AutoXLang.rustLoop? hd.type
        | throwError "ts_rust_lockstep: `hs` is not `wp (loop body init) K` (Aeneas)"
      pure (true, ts, r)
    else if let some ts ← AutoXLang.tsLoop? hd.type then
      let some r ← AutoXLang.rustLoop? tgt
        | throwError "ts_rust_lockstep: the goal is not `wp (loop body init) K` (Aeneas)"
      pure (false, ts, r)
    else throwError "ts_rust_lockstep: neither the goal nor `hs` is a TypeScript loop run"
  let (σ, B, x, Kr) := rust
  let cands ← AutoXLang.couplings ts σ B x tsTarget
  if cands.isEmpty then
    throwError "ts_rust_lockstep: no coupling: the Rust loop variables have no TypeScript \
      representation (usize, u8, u16, u32, i32, bool) or do not match the mutable slots"
  let (K₁, K₂) := if tsTarget then (ts.K, Kr) else (Kr, ts.K)
  let K₁s ← Term.exprToSyntax K₁
  let K₂s ← Term.exprToSyntax K₂
  let n := (← EquivLean.Aeneas.AutoCouple.stateComps σ).size
  let pR ← liftMacroM (AutoXLang.rustPat n)
  let errors : TacticM Nat := do
    return (← Core.getMessageLog).toList.countP (·.severity == .error)
  let e1 ← errors
  let s0 ← saveState
  for J in cands do
    try
      withoutRecover <| focus do
        let Js ← Term.exprToSyntax J
        let hJ : Array (TSyntax `rcasesPat) ← (List.range (AutoXLang.conjuncts J)).toArray.mapM
          fun k => `(rcasesPat| $(mkIdent (Name.mkSimple s!"hJ{k}")):ident)
        let pT ← `(rcasesPat| ⟨env, w'⟩)
        let (p₁, p₂) := if tsTarget then (pT, pR) else (pR, pT)
        let lockstep ← if tsTarget then
            `(tactic| ts_lockstep_x $Js, (fun o₁ o₂ => $K₂s o₂ → $K₁s o₁)
              using EquivLean.Aeneas.loop_shape _, EquivLean.Aeneas.loop_terminates _)
          else
            `(tactic| ts_lockstep_x $Js, (fun o₁ o₂ => $K₂s o₂ → $K₁s o₁)
              using EquivLean.Aeneas.loop_shape _)
        evalTactic lockstep
        evalTactic (← `(tactic| case exit => intro o₁ o₂ h hk; exact h hk))
        evalTactic (← `(tactic| case init =>
          (simp [StrictTS.F64.ofUint32_eq, StrictTS.F64.ofInt32_eq, StrictTS.F64.ofNat_eq_ofInt,
            $args,*]) <;> (try omega) <;> (try scalar_tac)))
        evalTactic (← `(tactic| case step =>
          clear $(mkIdent `hs)
          rintro $p₁ $p₂ ⟨$hJ,*⟩
          (try dsimp only at *)
          subst_vars
          ts_rust_step [$defs,*] [$args,*]))
        done
      if (← instantiateMVars (mkMVar g)).hasSorry || (← errors) > e1 then
        throwError "ts_rust_lockstep: the attempt left an error"
      return
    catch ex =>
      if debug then throw ex
      s0.restore
  throwError "ts_rust_lockstep: no generated coupling closes this loop pair; tried{indentD
    (MessageData.joinSep (cands.toList.map MessageData.ofExpr) Format.line)}\n\
    give one with `ts_lockstep_x J, R using …`"

elab_rules : tactic
  | `(tactic| ts_rust_lockstep $[[$defs,*]]? $[with [$args,*]]?) => do
    let defs : Array Ident := (defs.map (·.getElems)).getD #[]
    let args : EquivLean.Aeneas.SimpArgs := (args.map (·.getElems)).getD #[]
    runTsRustLockstep defs args

/-- Debugging: the first attempt of `ts_rust_lockstep`, with its error. -/
syntax (name := tsRustLockstepDbg) "ts_rust_lockstep!" (" [" ident,* "]")?
  (" with" " [" simpArg,* "]")? : tactic

elab_rules : tactic
  | `(tactic| ts_rust_lockstep! $[[$defs,*]]? $[with [$args,*]]?) => do
    let defs : Array Ident := (defs.map (·.getElems)).getD #[]
    let args : EquivLean.Aeneas.SimpArgs := (args.map (·.getElems)).getD #[]
    runTsRustLockstep defs args (debug := true)

/-- `Sim R t s` between a TypeScript call and a Rust function, each one loop: `ts_start [defs…]`,
then `ts_rust_lockstep`. -/
syntax (name := simTsRust) "sim_ts_rust" " [" simpLemma,* "]" (" with" " [" simpArg,* "]")? : tactic

/-- `equiv_ts_rust [defs…] (with [lemmas…])?`: `sim_ts_rust` on both directions of `Equiv`. -/
syntax (name := equivTsRust) "equiv_ts_rust" " [" simpLemma,* "]" (" with" " [" simpArg,* "]")? :
  tactic

macro_rules
  | `(tactic| sim_ts_rust [$ls,*] $[with [$args,*]]?) => do
    let args : EquivLean.Aeneas.SimpArgs := (args.map (·.getElems)).getD #[]
    `(tactic| (ts_start [$ls,*]; ts_rust_lockstep with [$args,*]))
  | `(tactic| equiv_ts_rust [$ls,*] $[with [$args,*]]?) => do
    let args : EquivLean.Aeneas.SimpArgs := (args.map (·.getElems)).getD #[]
    `(tactic| (refine ⟨?_, ?_⟩ <;> sim_ts_rust [$ls,*] with [$args,*]))

end EquivLean.TS

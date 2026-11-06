import CIR.Tactic.Focus
import CIR.Tactic.Options
import CIR.Tactic.Call
import CIR.Tactic.SimpSets
import CIR.Tactic.Nlin
import CIR.Tactic.Elems

/-!
  `cir_vcg`: symbolic execution of CIR code to verification conditions.

  On a goal `Res.holds X K` it repeatedly
  * applies a head-only structural lemma when `X` is a bind, `pure`/`ok`, an
    op list, a region or a block;
  * runs one focused `simp` when `X` is a single operation or a state/memory
    computation (the continuation `K` stays abstract);
  * splits on data-dependent branch conditions;
  * stops at loops (`evalFor`, `evalWhile`, `evalDo`) and calls (`evalCall`),
    which are handled by the loop and call rules.
  Remaining goals are pure verification conditions; `omega` is tried on each.
-/

namespace CIR.Tactic

open Lean Meta Elab Tactic

/-- The head computation `X` of a goal `Res.holds X K`. -/
def holdsHead? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``CIR.Res.holds 3 then some (e.getArg! 1) else none

/-- Local hypotheses named `cirH_…` (loop-head facts introduced by
`cir_loop`); they are used as rewrite rules during symbolic execution. -/
def cirHypsFV : TacticM (Array FVarId) := do
  let lctx := (← (← getMainGoal).getDecl).lctx
  let mut out := #[]
  for d in lctx do
    if d.isImplementationDetail || d.userName.hasMacroScopes then continue
    -- the user's invariant is not a rewrite rule: it would put its terms
    -- (e.g. `Nat` casts) into the symbolic state
    let named := d.userName.toString.startsWith "cirH_" && d.userName.toString != "cirH_user"
    -- facts about memory blocks and SSA values: `m.blocks b = …`, `σ.env v = …`;
    -- also quantified ones, `∀ k (h : k < bs.length), m.blocks bs[k] = …`
    -- (conditional rewrite rules, side conditions discharged by `cir_disch`)
    let concl := Id.run do
      let mut t := d.type.consumeMData
      for _ in [0:8] do
        match t with
        | .forallE _ _ b _ => t := b.consumeMData
        | _ => break
      return t
    let fact := match concl.eq? with
      | some (_, lhs, _) =>
        let f := lhs.getAppFn
        f.isConstOf ``CIR.Mem.blocks || f.isConstOf ``CIR.State.env || f.isConstOf ``CIR.Mem.next ||
          (lhs.isApp && (lhs.appFn!.getAppFn.isConstOf ``CIR.Mem.blocks ||
                         lhs.appFn!.getAppFn.isConstOf ``CIR.State.env)) ||
          -- lookups in an abstract context (`ctx.record? "R" = some r`, ...)
          f.isConstOf ``CIR.Module.findFunc? || f.isConstOf ``CIR.Module.findRecord? ||
          f.isConstOf ``CIR.Module.findGlobal? || f.isConstOf ``CIR.Ctx.record? ||
          f.isConstOf ``CIR.Ctx.gaddr ||
          -- elements of arrays at symbolic indices (`toks[i]? = some (.agg …)`)
          f.isConstOf ``GetElem?.getElem? ||
          -- a pointer into a list of blocks whose bound is known (`listPtr bs k = …`)
          f.isConstOf ``CIR.listPtr
      | none => false
    if named || fact then
      out := out.push d.fvarId
  return out

/-- `cirHypsFV` as simp arguments: by name, or for a hypothesis shadowed by a
later one of the same name (the facts of an earlier loop, when a second loop
introduces its own `cirH_frame`, `σ₀`, …) by the hypothesis itself. -/
def cirHypsExcept (except : Option FVarId := none) : TacticM (Array Term) := do
  let g ← getMainGoal
  let lctx := (← g.getDecl).lctx
  let mut out := #[]
  for fv in ← cirHypsFV do
    if except == some fv then continue
    let some d := lctx.find? fv | continue
    if (lctx.findFromUserName? d.userName).map (·.fvarId) == some fv then
      out := out.push (mkIdent d.userName : Term)
    else
      out := out.push (← g.withContext (Lean.Elab.Term.exprToSyntax (mkFVar fv)))
  return out

def cirHyps : TacticM (Array Term) := cirHypsExcept

/-- For each fact `l[i]? = some v` about a list among `cirHypsFV`, the rewrite
rule `∀ h : i < l.length, l[i] = v`. An element read produces `l[i]`
(`List.getElem?_eq_getElem` rewrites `l[i]?` before the fact can), so without
it the fact's value, and the range facts stated about it, never reach the
state or the discharger: every range check on the element is split. -/
def elemHypTerms : TacticM (Array Term) := do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let mut out : Array Term := #[]
    for fv in ← cirHypsFV do
      let some d := lctx.find? fv | continue
      let ty ← instantiateMVars d.type
      let some (_, lhs, rhs) := ty.eq? | continue
      unless lhs.isAppOfArity ``GetElem?.getElem? 7 && rhs.isAppOfArity ``Option.some 2 do continue
      unless (← whnfR (← inferType (lhs.getArg! 5))).isAppOfArity ``List 1 do continue
      let hS ← Lean.Elab.Term.exprToSyntax (mkFVar fv)
      out := out.push (← `(fun h => (List.getElem_eq_iff h).mpr $hS))
    return out

/-- `simp` lemma syntax for a list of names. -/
def simpArgs (names : Array Name) (extra : Array Term) :
    TacticM (Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ",") := do
  let mut out : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for n in names do
    out := out.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident))
  for h in extra do
    out := out.push (← `(Lean.Parser.Tactic.simpLemma| $h:term))
  return out

/-- `x >>= f` in `Res`, evaluated lazily (a pre-procedure): only `x` is
simplified; once it is `.ok a` the step continues with `f a`, once it is
`.ub m` / `.div` the continuation is dropped, otherwise `f` is left as it is.
`simp`'s default congruence would simplify `f`'s body first, with its
argument a variable: every branch of a `match` on it (the pointer cases of
`evalCmp`, `evalCast`, `loadTy`, with `Mem.read?`, `Mem.ptrEq?`, … on symbolic
blocks) is evaluated in vain, at every bind of every operation. -/
simproc_decl lazyBind (@Bind.bind CIR.Res _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``Bind.bind 6 do return .continue
  unless (e.getArg! 0).isConstOf ``CIR.Res do return .continue
  let fn := e.getAppFn
  let args := e.getAppArgs
  let x := args[4]!
  let f := args[5]!
  let r ← Simp.simp x
  let x' := r.expr
  let mkB (y : Expr) := mkAppN fn #[args[0]!, args[1]!, args[2]!, args[3]!, y, f]
  let p1? ← match r.proof? with
    | none => pure none
    | some p => do
      let lam := Lean.mkLambda `y .default (← inferType x) (mkB (.bvar 0))
      pure (some (← mkCongrArg lam p))
  let trans (p2 : Expr) : MetaM Expr := match p1? with
    | none => pure p2
    | some p1 => mkEqTrans p1 p2
  if x'.isAppOfArity ``CIR.Res.ok 2 then
    let a := x'.appArg!
    let e2 := (mkApp f a).headBeta
    let p2 ← mkAppM ``CIR.Res.ok_bind #[a, f]
    let pf ← mkExpectedTypeHint (← trans p2) (← mkEq e e2)
    return .visit { expr := e2, proof? := some pf }
  if x'.isAppOfArity ``CIR.Res.ub 2 then
    let e2 ← mkAppOptM ``CIR.Res.ub #[args[3]!, x'.appArg!]
    let p2 ← mkAppOptM ``CIR.Res.ub_bind #[args[2]!, args[3]!, x'.appArg!, f]
    return .done { expr := e2, proof? := some (← trans p2) }
  if x'.isAppOfArity ``CIR.Res.div 1 then
    let e2 ← mkAppOptM ``CIR.Res.div #[args[3]!]
    let p2 ← mkAppOptM ``CIR.Res.div_bind #[args[2]!, args[3]!, f]
    return .done { expr := e2, proof? := some (← trans p2) }
  return .done { expr := mkB x', proof? := p1? }

/-- `simpArgs` with `lazyBind` as a pre-procedure. -/
def simpArgsLazy (names : Array Name) (extra : Array Term) :
    TacticM (Syntax.TSepArray `Lean.Parser.Tactic.simpLemma ",") := do
  let mut out : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for n in names do
    out := out.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident))
  out := out.push (← `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent ``CIR.Tactic.lazyBind):ident))
  for h in extra do
    out := out.push (← `(Lean.Parser.Tactic.simpLemma| $h:term))
  return out

/-- Pointer offsets by literals, `(↑n + 2).toNat = n + 2` (with `Int.add_zero`
for `↑n + 0`): element indices `l[(↑k + 2).toNat]` become `l[k + 2]`. -/
theorem _root_.CIR.natCast_add_ofNat_toNat (n m : Nat) :
    ((n : Int) + (no_index (OfNat.ofNat m : Int))).toNat = n + OfNat.ofNat m := rfl

def execNames : Array Name := #[`cir_exec, ``CIR.Tactic.reduceUpd, ``CIR.Tactic.reduceKillRange,
  -- small memory terms (`cir.normMem`)
  ``CIR.Tactic.normKillRange, ``CIR.Tactic.collapseUpd,
  ``CIR.Tactic.reduceCtxRecord, ``CIR.Tactic.reduceCtxGaddr, ``CIR.Tactic.reduceFindRecord,
  ``CIR.Tactic.reduceFindFunc, ``CIR.Tactic.reduceFindGlobal, ``CIR.Tactic.reduceBasePath,
  ``CIR.Tactic.reducePtrBytes,
  ``CIR.Tactic.reduceVptrPath, ``CIR.recordName?, ``CIR.isClassOrBase, `String.reduceBEq,
  `String.reduceEq, ``List.length_cons, ``List.length_nil, ``List.take_zero, ``List.drop_zero,
  ``List.take_succ_cons, ``List.drop_succ_cons, ``beq_self_eq_true,
  `reduceCtorEq, `Nat.reduceAdd, `Nat.reduceSub, `Nat.reduceMul, `Nat.reducePow, `Nat.reduceEqDiff,
  -- concrete pointer offsets (`(↑0 + 1).toNat`)
  ``Int.cast_ofNat_Int, `Int.reduceAdd, `Int.reduceToNat, `Nat.reduceLT,
  -- record layouts (sizeAlign) on known types
  `Nat.reduceDiv, `Nat.reduceMod, `Nat.reduceLeDiff, ``ge_iff_le, ``Nat.max_def,
  `Nat.reduceLeDiff, `Int.reduceAdd, `Int.reduceSub, `Int.reduceMul, `Int.reduceNeg, `Int.reducePow,
  `Int.reduceLT, `Int.reduceLE, `Int.reduceEq, `Int.reduceNe,
  -- comparisons of integer literals as booleans (`0 != 0`)
  `Int.reduceBEq, `Int.reduceBNe, `Nat.reduceBEq, `Nat.reduceBNe,
  -- element indices (`(↑k + 0).toNat`, `(↑k + 2).toNat`)
  ``Int.add_zero, ``CIR.natCast_add_ofNat_toNat]

/-- `holds_ofOption` turns `holds (ofOption msg o) K` into `∃ a, o = some a ∧ …`.
It is only a fallback: in the main set it would fire inside the continuation
of a bind before the option's arguments are known (`stride? p n` with `p`
still bound), and the partial operation could then no longer be evaluated
and split at the head. -/
def fallbackNames : Array Name := execNames ++ #[``CIR.upd_apply, ``CIR.killRange_apply,
  ``CIR.ite_pos', ``CIR.ite_neg', ``CIR.dite_pos', ``CIR.dite_neg', ``CIR.Res.holds_ofOption,
  ``List.Nodup.getElem_inj]

def pureNames : Array Name := #[`cir_pure] ++ execNames

def pureFallbackNames : Array Name := #[`cir_pure] ++ fallbackNames

/-- Functions of element pointer arithmetic (`cir_iter` simp set). -/
def iterConsts : Array Name := #[``CIR.Std.validIter, ``CIR.Mem.stride?, ``CIR.Mem.ptrEq?,
  ``CIR.Mem.ptrLt?, ``CIR.Mem.diff?, ``CIR.Mem.isPastEnd, ``CIR.Mem.elemPos?, ``CIR.splitLast,
  -- operations that unfold to them within the same step
  ``CIR.Op.ptrStride, ``CIR.Op.ptrDiff, ``CIR.Std.readCStr, ``CIR.Std.readCStrN]

/-- `names`, plus the `cir_iter` set when the main goal mentions element
pointer arithmetic (keeps it out of the way of all other steps). -/
def withIter (names : Array Name) : TacticM (Array Name) := do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let uses := (t.find? fun x => x.isConst && iterConsts.contains x.constName!).isSome
  return if uses then names.push `cir_iter else names

/-- One focused simplification of the head computation. -/
elab "cir_exec_head" : tactic => do
  let args ← simpArgsLazy (← withIter execNames) ((← cirHyps) ++ (← elemHypTerms))
  evalTactic (← `(tactic| cir_head (simp (disch := cir_disch) only [$args,*])))

/-- Fallback when keys cannot be compared syntactically (e.g. a caller's
block against a local one): expose the comparison as an `if` and decide it
arithmetically. -/
elab "cir_exec_fallback" : tactic => do
  let args ← simpArgsLazy (← withIter fallbackNames) ((← cirHyps) ++ (← elemHypTerms))
  evalTactic (← `(tactic| cir_head (simp (disch := cir_disch) only [$args,*])))

/-- Simplify a pure goal (matches on known constructors, decided conditions);
the eager `upd`/`killRange` unfolding is only a fallback. -/
elab "cir_exec_pure" : tactic => do
  let args ← simpArgs (← withIter pureNames) (← cirHyps)
  let fargs ← simpArgs (← withIter pureFallbackNames) (← cirHyps)
  evalTactic (← `(tactic| first
    | simp (config := {decide := true}) (disch := cir_disch) only [$args,*]
    | simp (config := {decide := true}) (disch := cir_disch) only [$fargs,*]))

/-- `cir_exec_pure` without the eager fallback. -/
elab "cir_exec_pure_main" : tactic => do
  let args ← simpArgs (← withIter pureNames) (← cirHyps)
  evalTactic (← `(tactic| simp (config := {decide := true}) (disch := cir_disch) only [$args,*]))

/-- The eager fallback of `cir_exec_pure` (unfolds `upd`/`killRange` into
`if`s decided arithmetically): expensive, tried last. -/
elab "cir_exec_pure_fallback" : tactic => do
  let fargs ← simpArgs (← withIter pureFallbackNames) (← cirHyps)
  evalTactic (← `(tactic| simp (config := {decide := true}) (disch := cir_disch) only [$fargs,*]))

/-- Simplify a hypothesis with the pure simp set and the other `cirH_…`
facts. -/
elab "cir_simp_hyp " h:ident : tactic => do
  let fv ← (← getMainGoal).withContext (getFVarId h)
  let hyps ← cirHypsExcept (some fv)
  let args ← simpArgs pureNames hyps
  evalTactic (← `(tactic| simp (config := {decide := true}) (disch := cir_disch) only [$args,*] at $h:ident))

/-- A lookup `upd f k v b` whose keys cannot be compared (typically the
arbitrary block `b` of a frame obligation against a block the iteration
modified and restored): case on `b = k`; when equal, substitute. -/
elab "cir_upd_cases" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some e := t.find? fun e => e.isAppOfArity ``CIR.upd 7 && (e.getArg! 6).isFVar &&
        !(e.getArg! 6) == (e.getArg! 4) | throwError "cir_upd_cases: no undecided lookup"
    let x := e.getArg! 6
    let k := e.getArg! 4
    let xS ← Lean.Elab.Term.exprToSyntax x
    let kS ← Lean.Elab.Term.exprToSyntax k
    let n := (← getLCtx).foldl (init := 0) fun acc d =>
      if d.userName.toString.startsWith "cirH_eq" then acc + 1 else acc
    let h := mkIdent (Name.mkSimple s!"cirH_eq{n}")
    evalTactic (← `(tactic| by_cases $h:ident : $xS = $kS))
    -- positive case: substitute the key
    evalTactic (← `(tactic| case' pos => subst $h:ident))

/-- Enter the block at a literal index `i` of a literal block list (after a
jump or a `goto`): `holds_evalBlock_at`, with the block computed here. -/
elab "cir_block_at" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    let some x := holdsHead? t | throwError "cir_block_at: goal is not `Res.holds _ _`"
    let x ← instantiateMVars x
    unless x.isAppOfArity ``CIR.evalBlock 5 do throwError "cir_block_at: no block at the head"
    let ctx := x.getArg! 0
    let blocks := x.getArg! 1
    let i := x.getArg! 2
    let args := x.getArg! 3
    let σ := x.getArg! 4
    let Q := t.getArg! 2
    let some elems ← listElems blocks | throwError "cir_block_at: the block list is not literal"
    let some iv ← (do let i' ← whnfD i; pure (i'.rawNatLit? <|> i'.nat?))
      | throwError "cir_block_at: the block index is not a literal"
    let some blk := elems[iv]? | throwError "cir_block_at: branch to a missing block"
    let blk ← whnfD blk
    unless blk.isAppOfArity ``CIR.Block.mk 2 do throwError "cir_block_at: block is not literal"
    let params := blk.getArg! 0
    let ops := blk.getArg! 1
    -- `blocks[i]? = some blk`, checked by the kernel
    let lhs ← mkAppOptM ``GetElem?.getElem? #[none, none, none, none, none, blocks, i]
    let rhs ← mkAppM ``Option.some #[blk]
    let hb ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)
    let lem ← mkConstWithFreshMVarLevels ``CIR.holds_evalBlock_at
    let pre := mkAppN lem #[ctx, blocks, i, params, ops, args, σ, Q, hb]
    let hTy ← instantiateForall (← inferType pre) #[]
    let .forallE _ hTy _ _ := hTy | throwError "cir_block_at: unexpected lemma shape"
    let hg ← mkFreshExprSyntheticOpaqueMVar hTy (← g.getTag)
    g.assign (mkApp pre hg)
    replaceMainGoal [hg.mvarId!]

/-- The propositions of the main goal's hypotheses (conditions already split
on are not split again). -/
def knownProps : TacticM (Array Expr) := do
  (← getMainGoal).withContext do
    let mut out := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      out := out.push (← instantiateMVars d.type)
    return out

/-- `p` or `¬p` is among `known`. -/
def isKnown (known : Array Expr) (p : Expr) : Bool :=
  known.contains p || known.contains (mkNot p)

/-- The bound `k < l.length` of a pointer `listPtr l k`. -/
def listPtrBound (e : Expr) : Expr :=
  mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) (e.getArg! 1)
    (mkApp2 (mkConst ``List.length [0]) (mkConst ``Nat) (e.getArg! 0))

/-- A pointer `listPtr l k` into a symbolic list of blocks (a symbolic
position, or a symbolic list such as an item's children) whose bound is not
yet known. -/
def isOpenListPtr (known : Array Expr) (e : Expr) : Bool :=
  e.isAppOfArity ``CIR.listPtr 2 && !e.hasLooseBVars && e.hasFVar && !isKnown known (listPtrBound e)

/-- An `if` on data whose condition is not yet known (not a type test kept
folded while its block is looked up, `hasFoldedTypeTest`: the fallback unfolds
it). -/
def isOpenIte (known : Array Expr) (e : Expr) : Bool :=
  (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) && !e.hasLooseBVars && (e.getArg! 1).hasFVar &&
    !isKnown known (e.getArg! 1) && !hasFoldedTypeTest (e.getArg! 1)

/-- A `decide p` on data whose proposition is not yet known (as `isOpenIte`). -/
def isOpenDecide (known : Array Expr) (e : Expr) : Bool :=
  e.isAppOfArity ``Decidable.decide 2 && !e.hasLooseBVars && (e.getArg! 0).hasFVar &&
    !isKnown known (e.getArg! 0) && !hasFoldedTypeTest (e.getArg! 0)

/-- The number `N` of the next case-split hypothesis `cirH_brN` of the main
goal (counted in the goal's own context, so that names never repeat). -/
def nextBranchNum : TacticM Nat := do
  return (← (← getMainGoal).getDecl).lctx.foldl (init := 0) fun acc d =>
    if d.userName.toString.startsWith "cirH_br" then acc + 1 else acc

/-- Case on a condition `p` (hypothesis `cirH_brN`). -/
def splitOnCond (p : Expr) : TacticM Unit := do
  let pS ← (← getMainGoal).withContext (Lean.Elab.Term.exprToSyntax p)
  let h := mkIdent (Name.mkSimple s!"cirH_br{← nextBranchNum}")
  evalTactic (← `(tactic| by_cases $h:ident : $pS))

/-- Case on the bound of a pointer `listPtr l k`; each branch gets the
pointer's value as a ground rewrite rule `cirH_lpN` (`listPtr_of_lt`,
`listPtr_of_ge`). -/
def splitOnListPtr (e : Expr) : TacticM Unit := do
  let (pS, eS) ← (← getMainGoal).withContext do
    return (← Lean.Elab.Term.exprToSyntax (listPtrBound e), ← Lean.Elab.Term.exprToSyntax e)
  let n ← nextBranchNum
  let h := mkIdent (Name.mkSimple s!"cirH_br{n}")
  let hl := mkIdent (Name.mkSimple s!"cirH_lp{n}")
  -- (and the bound stated over the list itself, `k < l.length` for a list
  -- `l.map f` of blocks, as `omega` and the facts quantified over `l` see it;
  -- the original stays, to recognise the split as done)
  let hb := mkIdent (Name.mkSimple s!"cirH_bn{n}")
  evalTactic (← `(tactic| by_cases $h:ident : $pS <;> first
    | (have $hl:ident : $eS = _ := CIR.listPtr_of_lt $h:ident
       have $hb:ident := $h:ident
       try simp only [List.length_map] at $hb:ident)
    | (have $hl:ident : $eS = _ := CIR.listPtr_of_ge (Nat.le_of_not_lt $h:ident)
       have $hb:ident := $h:ident
       try simp only [List.length_map] at $hb:ident)))

/-- A pointer `listPtr l k` with unknown bound that a match in `t` is stuck on:
an argument of the matcher, not a value merely stored in the state (a pointer
written to a variable is not split on until it is used). -/
def stuckListPtr? (known : Array Expr) (t : Expr) : TacticM (Option Expr) := do
  let isLP := isOpenListPtr known
  let env ← getEnv
  let r ← IO.mkRef (none : Option Expr)
  t.forEachWhere (fun e => match e.getAppFn.constName? with
      | some c => (Lean.Meta.Match.Extension.getMatcherInfo? env c).isSome && e.getAppArgs.any isLP
      | none => false)
    fun e => r.modify fun o => o.orElse fun _ => e.getAppArgs.find? isLP
  r.get

/-- A case split on the bound of a pointer `listPtr l k` that a match is stuck
on. -/
def splitListPtr? (t : Expr) : TacticM Bool := do
  let g ← getMainGoal
  let some e ← g.withContext do stuckListPtr? (← knownProps) t | return false
  splitOnListPtr e
  return true

/-- One symbolic execution step. Fails when no step applies. -/
def cirStepImpl : TacticM Unit := do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  -- (an existential first looks for its witness, with `listPtr` still folded)
  if !(← whnfR t).isAppOfArity ``Exists 2 then
    if ← splitListPtr? t then return
  let t ← whnfR t
  match holdsHead? t with
  | none =>
    -- a pure goal: split conjunctions and implications, reduce matches
    if t.isAppOfArity ``And 2 then evalTactic (← `(tactic| constructor))
    else if t.isAppOfArity ``CIR.Frame 3 then evalTactic (← `(tactic| unfold CIR.Frame))
    else if t.isForall && (t.bindingDomain!.isAppOfArity ``Not 1) &&
        (t.bindingBody!.isConstOf ``False ||
         (t.bindingBody!.isAppOfArity ``CIR.Res.holds 3 &&
          (t.bindingBody!.getArg! 1).isAppOf ``CIR.Res.ub)) then
      -- a failed check `¬c → False`: ask for `c` itself, as arithmetic bounds
      evalTactic (← `(tactic| refine fun h => h ?_))
      evalTactic (← `(tactic| try simp only [inRange_eq_true_iff, inRange_eq_false_iff, Bool.not_eq_true,
        Bool.not_eq_false, intMin_s8, intMax_s8, intMin_s16, intMax_s16, intMin_s32, intMax_s32,
        intMin_s64, intMax_s64, intMin_u, intMax_u8, intMax_u16, intMax_u32, intMax_u64]))
    else if t.isForall then
      -- introduce, and state list non-membership as disequalities for `omega`
      let h := mkIdent (← mkFreshUserName `cirI)
      -- a premise about the state (a loop invariant's `∀ j, j < σ₀.intAt b → …`
      -- at loop entry) is evaluated like the goal
      let aboutState := (t.bindingDomain!.find? fun e =>
        e.isConst && e.constName!.getPrefix == ``CIR.State).isSome
      evalTactic (← `(tactic| intro $h:ident))
      evalTactic (← `(tactic| try simp only [List.mem_cons, List.not_mem_nil, not_or, ne_eq,
        or_false, not_false_eq_true, and_true, inRange_eq_true_iff, inRange_eq_false_iff,
        Bool.not_eq_true, Bool.not_eq_false, intMin_s8, intMax_s8, intMin_s16, intMax_s16,
        intMin_s32, intMax_s32, intMin_s64, intMax_s64, intMin_u, intMax_u8, intMax_u16, intMax_u32,
        intMax_u64, Int.reduceBEq, Int.reduceBNe, Nat.reduceBEq, Nat.reduceBNe, Bool.false_eq_true,
        Bool.true_eq_false] at $h:ident))
      if aboutState then evalTactic (← `(tactic| try cir_simp_hyp $h:ident))
    else if t.isAppOfArity ``True 0 then evalTactic (← `(tactic| trivial))
    else if t.isAppOfArity ``Exists 2 && (← (do
        let s ← saveState
        try evalTactic (← `(tactic| cir_exists_inst)); pure true
        catch _ => s.restore; splitListPtr? t)) then
      -- an invariant's existential: its witness from an equation, then the
      -- rest (else a stuck pointer into a list of blocks: case on its bound)
      pure ()
    else if t.isAppOfArity ``Exists 2 && (t.find? (isOpenIte (← knownProps))).isSome then
      -- `∃ a, (if c then … else …) = some a ∧ …` (a partial operation with a
      -- data-dependent definedness condition): split on the condition (never
      -- twice on the same one)
      let some e := t.find? (isOpenIte (← knownProps)) | unreachable!
      splitOnCond (e.getArg! 1)
    else if t.isAppOfArity ``Eq 3 && t.hasExprMVar then
      -- a precondition of a callee specification with a ghost value: find the
      -- value by unification once the known side is computed
      evalTactic (← `(tactic| first
        | with_reducible rfl
        | cir_exec_pure_main
        | cir_upd_cases
        | cir_exec_pure_fallback))
    -- a lookup at an arbitrary block whose key cannot be compared (a frame
    -- obligation) is split before the expensive fallback is tried
    else evalTactic (← `(tactic| first | cir_exec_pure_main | cir_upd_cases | cir_exec_pure_fallback))
  | some x =>
    let x ← instantiateMVars x
    let f := x.getAppFn
    -- a `match` on constructors at the head (on the step result `(s, σ)`, …):
    -- reduced definitionally, not by a `simp` over the block's remaining
    -- operations
    if let some c := f.constName? then
      if ← Lean.Meta.isMatcher c then
        let g ← getMainGoal
        let x'? ← g.withContext do
          try
            match ← Lean.Meta.reduceMatcher? x with
            | .reduced x' => pure (some x'.headBeta)
            | _ => pure none
          catch _ => pure none
        let t := t.consumeMData
        if let some x' := x'? then
          if t.isAppOfArity ``CIR.Res.holds 3 then
            replaceMainGoal [← g.replaceTargetDefEq (mkApp3 t.getAppFn (t.getArg! 0) x' (t.getArg! 2))]
            return
    match f.constName? with
    | some ``CIR.Res.ok => evalTactic (← `(tactic| (cir_apply CIR.holds_ok_intro; try dsimp only)))
    | some ``Pure.pure => evalTactic (← `(tactic| (cir_apply CIR.holds_pure_intro; try dsimp only)))
    | some ``Bind.bind => evalTactic (← `(tactic| cir_apply CIR.holds_bind_intro))
    | some ``ite =>
      -- a data-dependent value inside the condition (`fitsTy ty (if c then …)`)
      -- is split first: both branches then decide the condition
      -- (conditions already split on are skipped: splitting again would loop)
      let known ← knownProps
      let cond := x.getArg! 1
      let inner? := (← (← getMainGoal).withContext (stuckListPtr? known cond)).orElse fun _ =>
        cond.find? fun e => isOpenIte known e || (isOpenDecide known e && e != cond)
      let s ← saveState
      try evalTactic (← `(tactic| cir_exec_head))
      catch _ =>
        s.restore
        match inner? with
        | some e =>
          if e.isAppOf ``CIR.listPtr then splitOnListPtr e
          else splitOnCond (if e.isAppOf ``ite || e.isAppOf ``dite then e.getArg! 1 else e.getArg! 0)
        | none => evalTactic (← `(tactic| cir_apply CIR.holds_ite_intro))
    | some ``CIR.evalOps => evalTactic (← `(tactic| first
        | cir_apply CIR.holds_evalOps_cons
        | cir_apply CIR.holds_evalOps_nil
        | cir_exec_head))
    | some ``CIR.evalRegion => evalTactic (← `(tactic| first
        | cir_apply CIR.holds_evalRegion_nil
        | cir_apply CIR.holds_evalRegion_cons))
    | some ``CIR.evalBlock => evalTactic (← `(tactic| first
        | cir_apply CIR.holds_evalBlock_zero
        | cir_block_at))
    | some ``CIR.evalFor =>
      if (← getOptions).getBool `cir.unroll false then evalTactic (← `(tactic| cir_apply CIR.holds_evalFor_unroll))
      else throwError "cir_step: reached a cir.for loop (use cir_loop)"
    | some ``CIR.forIter | some ``CIR.whileIter | some ``CIR.doIter
    | some ``CIR.forIter.forStepIter | some ``CIR.doIter.doCondIter
    | some ``CIR.evalIterCleanup => evalTactic (← `(tactic| cir_exec_head))
    | some ``CIR.evalWhile =>
      if (← getOptions).getBool `cir.unroll false then evalTactic (← `(tactic| cir_apply CIR.holds_evalWhile_unroll))
      else throwError "cir_step: reached a cir.while loop (use cir_loop)"
    | some ``CIR.evalDo =>
      if (← getOptions).getBool `cir.unroll false then evalTactic (← `(tactic| cir_apply CIR.holds_evalDo_unroll))
      else throwError "cir_step: reached a cir.do loop (use cir_loop)"
    | some ``CIR.loopCont => evalTactic (← `(tactic| cir_exec_head))
    | some ``CIR.evalCall => evalTactic (← `(tactic| first | cir_call_spec | cir_call_inline))
    | some ``CIR.Std.runModel => evalTactic (← `(tactic| cir_model_unfold))
    | _ =>
      -- a data-dependent branch `… decide p …` stuck at the head: case on `p`
      -- (or an `if` on data, e.g. a value chosen by `cir.select`)
      -- a pointer into a list of blocks at a symbolic position first (case on
      -- the bound): it is what keeps the other conditions undecided
      let known ← knownProps
      let dec? := (← (← getMainGoal).withContext (stuckListPtr? known x)).orElse fun _ =>
        (x.find? (isOpenDecide known)).orElse fun _ => x.find? (isOpenIte known)
      let tryCases : TacticM Bool := do
        let some d := dec? | return false
        let s ← saveState
        try
          if d.isAppOf ``CIR.listPtr then splitOnListPtr d
          else splitOnCond (if d.isAppOf ``ite || d.isAppOf ``dite then d.getArg! 1 else d.getArg! 0)
          return true
        catch _ =>
          s.restore
          return false
      let progressed ← (do
          let s ← saveState
          try evalTactic (← `(tactic| first | cir_exec_head | cir_exec_fallback)); return true
          catch _ => s.restore; return false)
      if progressed then return
      if ← tryCases then return
      if (← getOptions).getBool `cir.nosplit false then
        evalTactic (← `(tactic| first | cir_exec_head | cir_exec_fallback))
      else
      evalTactic (← `(tactic| first
        | cir_exec_head
        | cir_exec_fallback
        | (split <;> (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true,
            Bool.not_eq_false, Exit.cond.injEq, Exit.yield.injEq, Exit.ret.injEq, Exit.exn.injEq,
            Step.exit.injEq, Step.jump.injEq, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
            Option.some.injEq, MemBlock.mk.injEq, reduceCtorEq, and_false, false_and,
            Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true, and_true,
            true_and] at *))))

/-- One symbolic execution step (see `cirStepImpl`). With
`set_option cir.traceSteps true`, steps slower than 200 ms are logged. -/
elab "cir_step" : tactic => Lean.Core.withCurrHeartbeats do
  if !(← getOptions).getBool `cir.traceSteps false then
    cirStepImpl
    return
  let t0 ← IO.monoMsNow
  let g0 ← getMainGoal
  let head ← g0.withContext do
    let t ← whnfR (← instantiateMVars (← g0.getType))
    match holdsHead? t with
    | some x => return s!"{(← instantiateMVars x).getAppFn.constName?}"
    | none => return s!"pure {t.getAppFn.constName?}"
  try cirStepImpl
  finally
    let dt := (← IO.monoMsNow) - t0
    if dt ≥ 200 then logInfo m!"cir_step {dt}ms {head}"

/-- Remove metadata annotations (left by some tactics) that hide arithmetic
from `omega`. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun e => match e with
    | .mdata _ b => some (stripMData b)
    | _ => none

elab "cir_strip_mdata" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut g := g
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t := stripMData (← instantiateMVars d.type)
      if t != d.type then g ← g.replaceLocalDeclDefEq d.fvarId t
    let t ← instantiateMVars (← g.getType)
    replaceMainGoal [← g.replaceTargetDefEq (stripMData t)]

/-- `e` mentions a machine state: a variable of `stateVars`, or a `State` /
`Mem` function. The bound proof of an element access `xs[i]` is skipped: it
may have been derived from state facts, which does not make `xs[i] = k` a
state fact. -/
partial def mentionsState (stateVars : Array FVarId) (e : Expr) : Bool :=
  match e with
  | .fvar id => stateVars.contains id
  | .const n _ => n.getPrefix == ``CIR.State || n.getPrefix == ``CIR.Mem || n == ``CIR.Mem.blocks
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let skip := fn.isConstOf ``GetElem.getElem && args.size == 8
    mentionsState stateVars fn ||
      (List.range args.size).any fun i => !(skip && i == 7) && mentionsState stateVars args[i]!
  | .lam _ t b _ | .forallE _ t b _ => mentionsState stateVars t || mentionsState stateVars b
  | .letE _ t v b _ => mentionsState stateVars t || mentionsState stateVars v || mentionsState stateVars b
  | .mdata _ b | .proj _ _ b => mentionsState stateVars b
  | _ => false

/-- Clear hypotheses about machine states (they mention states, memories or
values, directly or through variables of those types): they are irrelevant to
the arithmetic / list goals left at the end and slow down `grind`. -/
elab "cir_clear_state" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let isStateTy (t : Expr) : Bool :=
      t.isConstOf ``CIR.State || t.isConstOf ``CIR.Mem || t.isConstOf ``CIR.Val ||
        t.isConstOf ``CIR.Ptr || t.isConstOf ``CIR.Exit || t.isConstOf ``CIR.Step
    -- free variables of state-like types
    let mut stateVars : Array FVarId := #[]
    for d in lctx do
      if d.isImplementationDetail then continue
      if isStateTy (← whnfR d.type) then stateVars := stateVars.push d.fvarId
    let mentions (e : Expr) : Bool := mentionsState stateVars e
    let mut g := g
    for d in lctx.decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail then continue
      if stateVars.contains d.fvarId || mentions (← instantiateMVars d.type) then
        try g ← g.clear d.fvarId catch _ => pure ()
    replaceMainGoal [g]

/-- Clear universally quantified hypotheses (instantiating them can mislead
`grind` on goals that do not need them). -/
elab "cir_clear_foralls" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut g := g
    for d in (← getLCtx).decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail then continue
      if (← whnfR d.type).isForall && (← isProp d.type) then
        try g ← g.clear d.fvarId catch _ => pure ()
    replaceMainGoal [g]

/-- In a leftover goal, replace the integer value `v` of an unsigned loop
variable by the natural number of the invariant (`cir_nat : v = ↑x`). -/
elab "cir_subst_nat" : tactic => do
  let g ← getMainGoal
  let hs := (← g.getDecl).lctx.foldl (init := #[]) fun acc d =>
    if d.userName.toString.startsWith "cir_nat" then acc.push d.userName else acc
  if hs.isEmpty then return
  for h in hs do
    try evalTactic (← `(tactic| subst $(mkIdent h):ident)) catch _ => pure ()
  evalTactic (← `(tactic| try simp only [Int.toNat_natCast, CIR.natCast_add_one_toNat] at *))

/-- Close a leftover goal: arithmetic, or a contradictory case split. -/
macro "cir_close" : tactic => `(tactic| first
  | (cir_strip_mdata; omega)
  | (simp only [inRange_eq_true_iff, inRange_eq_false_iff, Bool.not_eq_true, Bool.not_eq_false,
      intMin_s8, intMax_s8, intMin_s16, intMax_s16, intMin_s32, intMax_s32, intMin_s64, intMax_s64,
      intMin_u, intMax_u8, intMax_u16, intMax_u32, intMax_u64] at *; cir_strip_mdata; omega)
  | omega
  | (try simp only [inRange_eq_true_iff, inRange_eq_false_iff, Bool.not_eq_true, Bool.not_eq_false,
      intMin_s8, intMax_s8, intMin_s16, intMax_s16, intMin_s32, intMax_s32, intMin_s64, intMax_s64,
      intMin_u, intMax_u8, intMax_u16, intMax_u32, intMax_u64] at *
     cir_strip_mdata; cir_nlin; omega)
  | (cir_strip_mdata; cir_clear_state; grind)
  | (cir_strip_mdata; cir_clear_state; cir_clear_foralls; grind)
  | (simp only [inRange_eq_true_iff, inRange_eq_false_iff, Bool.not_eq_true, Bool.not_eq_false,
      intMin_s8, intMax_s8, intMin_s16, intMax_s16, intMin_s32, intMax_s32, intMin_s64, intMax_s64,
      intMin_u, intMax_u8, intMax_u16, intMax_u32, intMax_u64] at *; cir_strip_mdata; cir_clear_state; grind)
  -- facts about the list elements read (`∀ x ∈ xs, …` at each `xs[i]`)
  | (cir_strip_mdata; cir_elems; (try cir_unwrap); omega)
  | (cir_strip_mdata; cir_elems; (try cir_unwrap); cir_clear_state
     grind [wrap_s8_self, wrap_s16_self, wrap_s32_self, wrap_s64_self, wrap_u8_self, wrap_u16_self,
       wrap_u32_self, wrap_u64_self])
  -- invariant facts `∀ j, … a[j]? …` at the indices read
  | (cir_strip_mdata; cir_elems; cir_inst_idx; (try cir_unwrap); cir_clear_state
     grind [wrap_s8_self, wrap_s16_self, wrap_s32_self, wrap_s64_self, wrap_u8_self, wrap_u16_self,
       wrap_u32_self, wrap_u64_self])
  -- a load split on the value read (`a[3] = Val.int x`) and on its integer
  -- type (`Ty.int true 32 = Ty.int s w`): substitute both everywhere
  | (cir_strip_mdata; cir_clear_state; cir_ty_inj
     (try simp_all only [inRange_eq_true_iff, inRange_eq_false_iff, Bool.not_eq_true,
      Bool.not_eq_false, Bool.not_true, Bool.not_false, intMin_s8, intMax_s8, intMin_s16,
      intMax_s16, intMin_s32, intMax_s32, intMin_s64, intMax_s64, intMin_u, intMax_u8, intMax_u16,
      intMax_u32, intMax_u64])
     first
       | done
       | (cir_elems; (try cir_inst_idx); (try cir_unwrap)
          grind [wrap_s8_self, wrap_s16_self, wrap_s32_self, wrap_s64_self, wrap_u8_self,
            wrap_u16_self, wrap_u32_self, wrap_u64_self]))
  -- an existential over values left by the loop rule at entry
  | (cir_strip_mdata; cir_clear_state; simp_all; done)
  -- an invariant's existential at the next element (`listPtr bs (k + 1)`)
  | (cir_strip_mdata; cir_exists_inst; cir_clear_state; first | omega | grind | (simp_all; done))
  -- a memory fact by cases on the block just written (`if j = k then … else
  -- σ.mem.blocks bs[j]`), with the invariant's facts about the memory (kept)
  | (cir_strip_mdata; split <;> first
      | (subst_vars; rfl)
      | (cir_inst_idx; first | assumption | (simp_all; done) | (cir_elems; grind)))
  | contradiction
  | (simp only [reduceCtorEq, Exit.cond.injEq, Bool.true_eq_false, Bool.false_eq_true,
      decide_eq_true_eq, decide_eq_false_iff_not] at *; done)
  | (exfalso; omega))

/-- Run symbolic execution as far as possible, then try to close the pure
goals that remain. -/
syntax "cir_vcg" : tactic

/-- `cir_close` with its own heartbeat budget. -/
elab "cir_close'" : tactic => Lean.Core.withCurrHeartbeats do
  let s ← saveState
  tryCatchRuntimeEx (evalTactic (← `(tactic| cir_close))) fun e => do
    s.restore
    if e.isRuntime then
      logWarning m!"cir_close: exceeded a resource limit (goal left open): {e.toMessageData}"
      throwError "cir_close: resource limit"
    throw e

/-! ### Natural-number ghosts of specifications

A specification over `(off : Nat)` with a member `.int off` meets the value
`.int (↑o + 1)` at a call: the precondition leaves `↑?off = ↑o + 1`, which
`cir_ghost_nat` settles with `?off := o + 1` (callers then go on). -/

/-- `e : Int` as a natural number when it is a sum of casts and literals. -/
partial def natOfInt? (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``Nat.cast 3 then return some (e.getArg! 2)
  if e.isAppOfArity ``Int.ofNat 1 then return some (e.getArg! 0)
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let some n := (e.getArg! 1).rawNatLit? then return some (mkNatLit n)
    return none
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let some x ← natOfInt? (e.getArg! 4) | return none
    let some y ← natOfInt? (e.getArg! 5) | return none
    return some (← mkAppM ``HAdd.hAdd #[x, y])
  return none

/-- The unassigned natural-number metavariable `?n` of `↑?n`, if any. -/
def castGhost? (e : Expr) : MetaM (Option MVarId) := do
  let e ← instantiateMVars e
  unless e.isAppOfArity ``Nat.cast 3 do return none
  let a := e.getArg! 2
  unless a.isMVar do return none
  let m := a.mvarId!
  if ← m.isAssigned then return none
  return some m

/-- Close a precondition `↑?n = e` (or `e = ↑?n`) whose ghost `?n : Nat` is
still unknown, with `?n := e` as a natural number. -/
-- (in the goal's context: `mkAppM` infers the types of its local variables)
elab "cir_ghost_nat" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some (_, lhs, rhs) := t.eq? | throwError "cir_ghost_nat: not an equation"
  for (side, other) in [(lhs, rhs), (rhs, lhs)] do
    if let some m ← castGhost? side then
      if (← instantiateMVars other).hasExprMVar then continue
      -- a sum of casts and literals: `?n := ` that sum; any other integer
      -- `e` known nonnegative: `?n := e.toNat`
      let e' ← match ← natOfInt? other with
        | some e' => pure e'
        | none => mkAppM ``Int.toNat #[other]
      let s ← saveState
      m.assign e'
      try
        evalTactic (← `(tactic| (cir_strip_mdata; omega)))
        return
      catch _ => s.restore
  throwError "cir_ghost_nat: no unknown natural-number ghost"

/-- In a stuck goal `Res.holds …`, split the latest disjunctive callee
postcondition `cirH_post…` (e.g. "null or a fresh item", "returns 0 or 1"):
each case is split into named facts as a postcondition is (`splitFact`: the
result variable is substituted), and implications whose premise compares
literals are simplified. -/
elab "cir_split_post_or" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  if (holdsHead? t).isNone then throwError "cir_split_post_or: not a `Res.holds` goal"
  let mut target : Option LocalDecl := none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    unless d.userName.toString.startsWith "cirH_post" do continue
    if (← whnfR (← instantiateMVars d.type)).isAppOfArity ``Or 2 then target := some d
  let some d := target | throwError "cir_split_post_or: no disjunctive postcondition"
  let h := mkIdent d.userName
  evalTactic (← `(tactic| rcases $h:ident with $h:ident | $h:ident))
  let mut out := #[]
  for g in ← getGoals do
    setGoals [g]
    splitFact d.userName
    for g' in ← getGoals do
      setGoals [g']
      let names ← g'.withContext do
        let mut ns := #[]
        for d in (← getLCtx) do
          if d.isImplementationDetail then continue
          if (← instantiateMVars d.type).isArrow && d.userName.toString.startsWith "cirH_post" then
            ns := ns.push d.userName
        pure ns
      for n in names do
        try evalTactic (← `(tactic| simp only [Option.some.injEq, Val.int.injEq, Int.reduceEq,
            reduceCtorEq, false_implies, true_implies, forall_const] at $(mkIdent n):ident))
        catch _ => pure ()
      out := out ++ (← getGoals)
  setGoals out.toList

/-- Worklist driver: step every goal until it is closed or stuck; a stuck goal
is never retried (stepping all goals in rounds would retry them). -/
elab "cir_run" : tactic => do
  let mut work := (← getGoals)
  let mut stuck : Array MVarId := #[]
  -- goals stuck on a not yet known (ghost) value are retried once at the end
  let mut deferred : Array MVarId := #[]
  let mut retried := false
  let mut fuel := (← getOptions).get `cir.fuel (100000 : Nat)
  while (!work.isEmpty || (!deferred.isEmpty && !retried)) && fuel > 0 do
    fuel := fuel - 1
    if work.isEmpty then
      work := deferred.toList
      deferred := #[]
      retried := true
    let g := work.head!
    work := work.tail!
    if ← g.isAssigned then continue
    -- a value to be found by unification (ghost argument of a specification)
    if !(← isProp (← g.getType)) then
      stuck := stuck.push g
      continue
    setGoals [g]
    let s ← saveState
    -- a step that fails, or hits a resource limit, leaves its goal stuck; each
    -- step has its own heartbeat budget (a long run is not one budget)
    let budget := (← getOptions).get `cir.stepHeartbeats (0 : Nat)
    let ok ← withTheReader Core.Context
        (fun c => if budget == 0 then c else { c with maxHeartbeats := budget * 1000 }) <|
      Lean.Core.withCurrHeartbeats <| tryCatchRuntimeEx (do
        evalTactic (← `(tactic| cir_step))
        pure true)
      fun e => do
        s.restore
        if e.isRuntime then
          logWarning m!"cir_run: a step exceeded a resource limit (goal left stuck): {e.toMessageData}"
        pure false
    if ok then
      work := (← getGoals) ++ work
    else
      -- a natural-number ghost of a specification fixed by this precondition
      setGoals [g]
      let s2 ← saveState
      let solved ← tryCatchRuntimeEx (do evalTactic (← `(tactic| cir_ghost_nat)); pure true)
        fun _ => do s2.restore; pure false
      -- (opt-in) a callee's disjunctive postcondition decides the next step
      let split ← if solved || !(← getOptions).getBool `cir.splitOr false then pure false else do
        setGoals [g]
        let s3 ← saveState
        tryCatchRuntimeEx (do evalTactic (← `(tactic| cir_split_post_or)); pure true)
          fun _ => do s3.restore; pure false
      if solved then
        -- goals waiting for this value go on
        work := deferred.toList ++ work
        deferred := #[]
      else if split then
        work := (← getGoals) ++ work
      else if !retried && (← instantiateMVars (← g.getType)).hasExprMVar then
        deferred := deferred.push g
      else
        stuck := stuck.push g
  setGoals (stuck.toList ++ deferred.toList ++ work)

macro_rules
  | `(tactic| cir_vcg) => `(tactic| (cir_run; all_goals (try cir_subst_nat); all_goals (try cir_close')))

/-- Concrete execution: `cir_vcg` that runs loops iteration by iteration
(each condition must evaluate to a literal), within `cir.fuel` steps. -/
macro "cir_eval" : tactic => `(tactic| set_option cir.unroll true in cir_vcg)

end CIR.Tactic

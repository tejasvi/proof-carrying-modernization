import CIR.Logic.Exec
import CIR.Tactic.Simprocs
import CIR.Logic.Loops
import CIR.Logic.CJTree
import CIR.Tactic.Attr

/-! Membership of the `cir_exec` and `cir_pure` simp sets. -/

namespace CIR

theorem natCast_add_one_toNat (n : Nat) : ((n : Int) + 1).toNat = n + 1 := by omega

/-- The whole block (a typed range for `memset`/`memcpy`). -/
theorem splitLast_nil : splitLast [] = none := rfl

/-- Pointer paths are compared structurally (`Mem.ptrEq?`). -/
theorem path_beq (p q : List PathElem) : (p == q) = decide (p = q) := Bool.beq_eq_decide_eq p q

attribute [cir_exec]
  Int.add_sub_cancel Int.sub_add_cancel
  List.map_cons List.map_nil List.zip_cons_cons List.zip_nil_left List.zip_nil_right
  List.getElem?_cons_zero List.getElem?_cons_succ List.set_cons_zero List.set_cons_succ
  Int.add_assoc
  List.nil_append List.cons_append List.append_nil List.getElem?_eq_getElem
  Option.toList_some Option.toList_none
  List.length_map List.getElem?_map Option.map_some Option.bind_some
  Std.fresh Std.readVal Std.writeVal Std.storeEnd Std.storeGuard Std.readVec Std.writeVec Std.ensureVec Std.elemPtr
  Std.fieldPtr
  Std.contPtr
  Std.retv Std.retVoid Std.sizeVal Std.readBoxedPtr Std.throwLib Std.strChars Std.readCStr
  Std.readCStrN Std.isNulVal Std.isIntVal
  Std.allocHeap Std.freeHeap heapKind? Ctx.sizeAlign Ctx.zeroVal Std.arrTail Std.strncmpVals activeMember
  punScalar Option.getD_none Option.getD_some Ctx.fromActive Ctx.reinterpAt Ctx.reinterpScalar Ctx.scalarAt Ctx.memberOffsets Ty.beq
  Ctx.byteAt Ctx.composeAt scalarOfBytes
  noUndefAlong Ctx.unionView? Ctx.unionActivate? Ctx.viewVal? Ctx.activateVal? Ctx.unionOnPath
  Ctx.viewValIn? Ctx.activateValIn?
  Ctx.viewVal?_eq_none_of_noUndefAlong Ctx.activateVal?_eq_none_of_noUndefAlong
  Ctx.viewValIn?_eq_none_of_noUndefAlong Ctx.activateValIn?_eq_none_of_noUndefAlong
  Std.memsetModel Std.memcpyModel Std.validMemArg Std.typedRange? Std.rangeWrite Std.rangeVals Ctx.typeAt splitLast_nil
  Std.memcpyOverlap Std.rangesOverlap Std.strArgsOverlap Std.sprintfStrArgs Std.inSlice Std.idxAfter?
  Std.commonPath Std.unionSplit List.isPrefixOf List.any_cons List.any_nil
  List.replicate_one List.mapM_cons List.mapM_nil Option.bind_eq_bind Option.pure_def
  Mem.free? List.getLast?_concat List.dropLast_concat List.getElem?_range List.length_range
  loopCont
  forIter forIter.forStepIter whileIter doIter doIter.doCondIter evalIterCleanup.eq_1 loopPost
  LoopFrame LoopFrameW IntSlot State.intAt_mk List.mem_cons List.not_mem_nil not_or
  ScratchSlot IterSlot State.iterAt_mk iterIdx_agg iterMove_agg lastIndex movePath
  PtrSlot State.ptrIdxAt_mk ptrIdx_ptr ptrMove_ptr ArrSlot State.arrVals_mk
  Int.tmod_eq_emod_of_nonneg Int.tdiv_eq_ediv_of_nonneg
  LoopFrameFrom PtrValSlot State.ptrAt_mk dite_true dite_false ptrValid
  listIdx_listPtr listIdx_loc listIdx_loc_map cjRec ostr List.getElem_map List.length_map
  cjFields_get0 cjFields_get1 cjFields_get2 cjFields_get3 cjFields_get4 cjFields_get5 cjFields_get6
  cjFields_get7 cjFields_length
  PathElem.index PathElem.withIndex MemBlock.mk.injEq exists_eq exists_eq'
  VecSlot State.ptrTarget_mk State.vecInts_mk filterMap_intOf_map_int List.filterMap_append
  FieldsSlot State.fieldInt_mk setFields List.foldl_cons List.foldl_nil Option.getD_some
  List.filterMap_cons List.filterMap_nil intOf List.map_append Val.vec.injEq
  adjustThis adjustThisIndirect loadPtr_loc loadPtr_null loadPtr_fn loadPtr_vtable Ctx.vtableSlot?
  vtableRead Ctx.vptrClass?
  findHandler isFundamentalTypeinfo labelBlock? switchStart List.findIdx?_cons List.findIdx?_nil int_beq_eq_decide
  missingAggCheck endLifetime
  evalCases_nil evalCases_case evalCases_yield List.contains_cons List.contains_nil
  List.head?_cons List.getElem?_set_self' List.set_set Option.map_eq_map Function.const_apply
  Int.toNat_natCast natCast_add_one_toNat Res.ofOption_ite wrap_of_bounds inRange_wrap inRange_bitwise Ctx.symAddr? List.all_nil
  List.all_cons
  killRange_self
  State.set_eq State.withMem_eq Mem.setBlock_eq Mem.endScope_eq Exit.leaveMem
  Res.holds_ok Res.holds_ub Res.holds_div Res.holds_pure Res.holds_bind
  Res.pure_eq Res.ok_bind Res.ub_bind Res.div_bind Res.ofOption_some Res.ofOption_none evalOp
  evalSimple finishRegion runsCleanup State.get_eq State.getPtr_eq State.getInt_eq
  State.getBool_eq State.set_env State.set_mem State.withMem_mem State.withMem_env State.mk_mem
  State.mk_env State.mk_names State.set_names State.withMem_names State.bindArgs_nil State.bindArgs_cons State.bindArgs_extra
  List.lookup_cons List.lookup_nil List.getLast?_singleton List.getLast?_cons_cons
  List.dropLast_singleton List.dropLast_cons_cons State.setResults_none State.setResults_some
  List.getElem?_replicate List.length_replicate List.length_set List.getElem?_set
   Option.map_some Option.map_none Mem.alloc_eq
  Mem.setBlock_blocks Mem.setBlock_next Mem.mk_blocks Mem.mk_next Mem.endScope_next
  Mem.endScope_blocks Mem.live?_eq Mem.read?_loc Mem.write?_loc Mem.read?_null
  Mem.write?_null Val.get? Val.set? Val.holds Val.holdsAny Val.initBy Val.fillsOver
  Val.fillsOverAll Option.all_some Option.all_none
  loadTy storeTy fitsTy Ty.isScalar Mem.punnedAccess Ty.atPath
  Ty.accessCompatible Ctx.punnedMember Ctx.typedLoad Ctx.typedStore inRange_of_bounds
  Ty.isChar Ty.isVoid Ty.hasBytes Ty.isAggregate Ctx.reachIn Ctx.reach? byteOf setByte setByteRepr
  splitByte Ctx.reachTypeNone Ctx.reachNone
  byteLoadOf byteStoreOf byteLoad byteStore splitLast Ctx.stride? Ctx.diff? Ctx.sameUnits Ctx.elemTyOf?
  Option.isSome_some Option.isSome_none
  Ptr.isByteView Ctx.evalCmpB Ctx.convertPath isClassOrBase Ctx.memberPath Ctx.ptrEq?
  Ctx.memberRelated
  Ctx.sameArray Ptr.sameParent Ctx.castAligned Ctx.castCheck
  intMin_s8 intMax_s8 intMin_s16 intMax_s16 intMin_s32 intMax_s32 intMin_s64
  intMax_s64 intMin_u intMax_u8 intMax_u16 intMax_u32 intMax_u64 evalBinop evalUnop evalShift
  cmpInt evalCmp Ctx.cmpXchgEq evalCast castVal decayOne Ctx.convertPtr caseMatches Ctx.initVal Ctx.constVal
  evalRegion_ite
  Nat.add_assoc
  nat_self_eq_add nat_add_eq_self nat_add_le_self nat_self_le_add nat_not_add_lt_self
  nat_self_lt_add Nat.add_left_cancel_iff List.mapM_cons List.mapM_nil Option.some.injEq ite_true_inst
  ite_false_inst decide_eq_true_eq decide_true decide_false Bool.and_true
  Bool.true_and Bool.and_false Bool.false_and Bool.not_true Bool.not_false ne_eq not_false_eq_true
  not_true_eq_false true_and and_true false_and and_false implies_true Prod.mk.injEq
  exists_eq_left' exists_eq_left exists_eq_right Exit.yield.injEq Exit.ret.injEq Step.exit.injEq
  Val.int.injEq Val.bool.injEq Val.ptr.injEq Ptr.loc.injEq List.cons.injEq Val.agg.injEq Bool.true_or
  Bool.false_or Bool.or_true Bool.or_false Bool.not_eq_true' Bool.not_eq_false'

attribute [cir_iter]
  Std.validIter Mem.elemPos? splitLast Mem.stride? Mem.isPastEnd Mem.ptrEq? Mem.diff? Mem.ptrLt?
  path_beq PathElem.vel.injEq PathElem.idx.injEq Option.isSome_some Option.isSome_none

attribute [cir_pure]
  Int.add_sub_cancel Int.sub_add_cancel
  loopPost LoopFrame LoopFrameW IntSlot State.intAt_mk List.mem_cons List.not_mem_nil not_or
  ScratchSlot IterSlot State.iterAt_mk iterIdx_agg iterMove_agg lastIndex movePath
  PtrSlot State.ptrIdxAt_mk ptrIdx_ptr ptrMove_ptr ArrSlot State.arrVals_mk
  Int.tmod_eq_emod_of_nonneg Int.tdiv_eq_ediv_of_nonneg
  LoopFrameFrom PtrValSlot State.ptrAt_mk dite_true dite_false ptrValid
  listIdx_listPtr listIdx_loc listIdx_loc_map cjRec ostr List.getElem_map List.length_map
  cjFields_get0 cjFields_get1 cjFields_get2 cjFields_get3 cjFields_get4 cjFields_get5 cjFields_get6
  cjFields_get7 cjFields_length
  PathElem.index PathElem.withIndex MemBlock.mk.injEq exists_eq exists_eq'
  VecSlot State.ptrTarget_mk State.vecInts_mk filterMap_intOf_map_int List.filterMap_append
  FieldsSlot State.fieldInt_mk setFields List.foldl_cons List.foldl_nil Option.getD_some
  List.filterMap_cons List.filterMap_nil intOf List.map_append Val.vec.injEq
  Option.some.injEq ite_true_inst ite_false_inst decide_eq_true_eq ne_eq not_false_eq_true
  not_true_eq_false true_and and_true false_and and_false implies_true Prod.mk.injEq
  exists_eq_left' exists_eq_left exists_eq_right Exit.yield.injEq Exit.ret.injEq Step.exit.injEq
  Val.int.injEq Val.bool.injEq Val.ptr.injEq Ptr.loc.injEq List.cons.injEq Val.agg.injEq

open Lean Meta Simp in
/-- `lhs = rhs` from simplifying `lhs` (`rhs` without metadata). -/
def simpEqOf (lhs : Expr) : SimpM (Expr × Expr) := do
  let r ← Simp.simp lhs
  let rhs := (← instantiateMVars r.expr).consumeMData
  let pf ← mkExpectedTypeHint (← match r.proof? with | some pr => pure pr | none => mkEqRefl rhs)
    (← mkEq lhs rhs)
  return (rhs, pf)

theorem upd_apply_of_eq {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) (x : α)
    (h : x = k) : upd f k v x = v := by subst h; exact upd_apply_same f x v

theorem upd_apply_of_ne {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) (x : α)
    (h : ¬x = k) : upd f k v x = f x := upd_apply_ne h

open Lean Meta Simp in
/-- The simp theorems with the context's type facts as further rewrite rules:
the local hypotheses named `cirR_…`, such as the record type of the items of a
list that a specification leaves open (`CJ.rt`, fixed by a printability
predicate), which a proof script states for symbolic execution; and the head
constants of their left-hand sides (none: no such facts). They evaluate the
functions of a block's type (`reduceTyArg…`) and decide the type tests of
`Ctx.reachIn` and `Ctx.memberPath` (`decideTo`), without rewriting the
symbolic state. -/
def typeFactTheorems : SimpM (SimpTheoremsArray × Array Name) := do
  let mut thms : SimpTheoremsArray ← Simp.getSimpTheorems
  let mut heads : Array Name := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless d.userName.toString.startsWith "cirR_" do continue
    thms ← thms.addTheorem (.fvar d.fvarId) d.toExpr
    let mut c := (← instantiateMVars d.type).consumeMData
    while c.isForall do c := c.bindingBody!
    if let some (_, lhs, _) := c.eq? then
      if let some n := lhs.getAppFn.constName? then
        unless heads.contains n do heads := heads.push n
  return (thms, heads)

open Lean Meta Simp in
/-- `simpEqOf` with the simp theorems `thms`, with an empty cache, so that no
result found without them is reused and none found with them is kept. -/
def simpEqWith (thms : SimpTheoremsArray) (lhs : Expr) : SimpM (Expr × Expr) := do
  let saved := (← get).cache
  modify fun s => { s with cache := {} }
  try Simp.withSimpTheorems thms (simpEqOf lhs)
  finally modify fun s => { s with cache := saved }

open Lean Meta Simp in
/-- `.done` (the term stays folded) when `e` mentions a variable bound inside
the term simp visits (a local declaration made after simp started: a match
alternative's variable, such as the block of a pointer not yet known), whose
test is decided once the variable is instantiated; otherwise `.continue`, and
the definition unfolds. -/
def keepUnderBinder (e : Expr) : SimpM Lean.Meta.Simp.Step := do
  let n := (← readThe Simp.Context).lctxInitIndices
  let lctx ← getLCtx
  let inner := e.find? fun x => x.isFVar &&
    match lctx.find? x.fvarId! with
    | some d => d.index ≥ n
    | none => false
  return if inner.isSome then .done { expr := e } else .continue

open Lean Meta Simp in
/-- A function of a block's type (argument `i` of `e`) where the type is left
open in the symbolic state but the context's type facts give it (an item's
`CJ.rt`, `typeFactTheorems`): the function at the type they give, so that it
evaluates. The state, where the type stays as it is, is not rewritten.
Otherwise `.continue`. Before the function's equations (`↓`): `Ctx.typeAt t []`
is `some t` for every `t`, which would leave the type in a `match`. -/
def reduceTyArgImpl (i : Nat) (e : Expr) : SimpM Lean.Meta.Simp.Step := do
  let args := e.getAppArgs
  unless i < args.size do return .continue
  let t := args[i]!
  if t.hasLooseBVars || (← isConstructorApp t) then return .continue
  -- the type of a block bound inside the visited term (a lookup's `some blk`): kept for
  -- when the block is known, not `Ctx.typeAt blk.ty [] = some blk.ty` under the binder
  if let .done _ ← keepUnderBinder t then return .done { expr := e }
  let (thms, heads) ← typeFactTheorems
  unless (t.find? fun s => heads.any (s.isAppOf ·)).isSome do return .continue
  let (t', pf) ← simpEqWith thms t
  unless ← isConstructorApp t' do return .continue
  let f ← withLocalDeclD `x (← inferType t) fun x =>
    mkLambdaFVars #[x] (mkAppN e.getAppFn (args.modify i fun _ => x))
  return .visit { expr := mkAppN e.getAppFn (args.modify i fun _ => t'),
                  proof? := some (← mkCongrArg f pf) }

simproc ↓ [cir_exec] reduceTyArgAtPath (Ty.atPath _ _) := reduceTyArgImpl 0

simproc ↓ [cir_exec] reduceTyArgTypeAt (Ctx.typeAt _ _ _) := reduceTyArgImpl 1

simproc ↓ [cir_exec] reduceTyArgSizeAlign (Ctx.sizeAlign _ _ _) := reduceTyArgImpl 2

simproc ↓ [cir_exec] reduceTyArgSameArray (Ctx.sameArray _ _ _ _) := reduceTyArgImpl 1

simproc ↓ [cir_exec] reduceTyArgConvertPath (Ctx.convertPath _ _ _ _) := reduceTyArgImpl 1

/-- The union decision of a typed access (`Ctx.viewVal?` / `Ctx.activateVal?`
match on it) at the type the context's type facts give: `false` for an item's
`CJ.rt`, a record without unions. -/
simproc ↓ [cir_exec] reduceTyArgUnionOnPath (Ctx.unionOnPath _ _ _ _) := reduceTyArgImpl 2

/-- `e` waits on a lookup that cases on a point update's key cannot decide: a
range kill or a memory's blocks applied to a block (left for the lookups of
symbolic execution). -/
def blockedElsewhere (e : Lean.Expr) : Bool :=
  (e.find? fun x => x.isAppOfArity ``killRange 4 || x.isAppOfArity ``Mem.blocks 2).isSome

open Lean Meta Simp in
/-- Whether simp runs as symbolic execution's fallback (`upd_apply` among its
lemmas: `cir_exec_fallback`, `cir_exec_pure_fallback`). -/
def inFallback : SimpM Bool :=
  return (← Simp.getSimpTheorems).any fun s => s.lemmaNames.contains (.decl ``upd_apply)

/-- Whether `e` still looks a block up: a memory's blocks applied to a block
(`Mem.blocks`, a point update or a range kill applied). -/
def hasLookup (e : Lean.Expr) : Bool :=
  (e.find? fun x => x.isAppOfArity ``Mem.blocks 2 || x.isAppOfArity ``upd 7 ||
    x.isAppOfArity ``killRange 4 ||
    match x.getAppFn with
    | .proj n _ _ => n == ``Mem && x.isApp
    | _ => false).isSome

/-- The type tests that symbolic execution keeps folded while their block is
looked up (`reduceTypeTestImpl`): not conditions to case on. -/
def hasFoldedTypeTest (e : Lean.Expr) : Bool :=
  (e.find? fun x => x.isAppOf ``Ctx.punnedMember || x.isAppOf ``Ctx.reachTypeNone ||
    x.isAppOf ``Ctx.memberRelated).isSome

/-- `r` is the constant `target` (`true`, `false`, `none`), up to universe
levels and type arguments. -/
def isConstLike (r target : Lean.Expr) : Bool :=
  match r.getAppFn, target.getAppFn with
  | .const n _, .const n' _ => n == n' && r.getAppNumArgs == target.getAppNumArgs
  | _, _ => false

/-- A comparison of natural numbers or integers, or a conjunction or negation of
them: the facts given to `omega` by `keysDistinct`. -/
partial def isArithFact (e : Lean.Expr) : Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then isArithFact (e.getArg! 0) && isArithFact (e.getArg! 1)
  else if e.isAppOfArity ``Not 1 then isArithFact (e.getArg! 0)
  else
    (e.isAppOfArity ``LT.lt 4 || e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``GT.gt 4 ||
      e.isAppOfArity ``GE.ge 4 || e.isAppOfArity ``Eq 3 || e.isAppOfArity ``Ne 3) &&
    ((e.getArg! 0).consumeMData.isConstOf ``Nat || (e.getArg! 0).consumeMData.isConstOf ``Int)

open Lean Meta in
/-- The context's facts `∀ x, x ∈ CJ.forestBlocks ts → …` at the root block of
the item `ts[j]` that `key` is (`(ts[j]).b`): the bounds of a list's blocks, for
`omega` (as `pa_inst_terms` states them after a step). -/
def itemBlockFacts (key : Lean.Expr) : MetaM (List Lean.Expr) := do
  let key := key.consumeMData
  unless key.isAppOfArity ``CJ.b 1 do return []
  let t := (key.getArg! 0).consumeMData
  unless t.isAppOfArity ``GetElem.getElem 8 do return []
  let ts := t.getArg! 5
  let mut out := []
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.isForall do continue
    let ok ← forallBoundedTelescope ty (some 2) fun xs _ => do
      if xs.size < 2 then return false
      let t1 ← instantiateMVars (← inferType xs[1]!)
      return t1.isAppOfArity ``Membership.mem 5 &&
        (t1.getArg! 3).isAppOfArity ``CJ.forestBlocks 1 && (t1.getArg! 3).getArg! 0 == ts
    unless ok do continue
    try
      let mem ← mkAppM ``CJ.mem_forestBlocks #[t.getArg! 7, ← mkAppM ``CJ.root_mem_blocks #[t]]
      let pf := mkApp2 d.toExpr key mem
      if isArithFact (← instantiateMVars (← inferType pf)) then out := pf :: out
    catch _ => pure ()
  return out

open Lean Meta in
/-- A proof of `x ≠ k` for block keys, by `omega` over the context's arithmetic
facts and the bounds of the blocks of the lists the keys are items of
(`itemBlockFacts`), as symbolic execution's lookups decide them, or `none`. -/
def keysDistinct (x k : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let s ← saveState
  try
    let g ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Ne #[x, k])
    let extra := (← itemBlockFacts x) ++ (← itemBlockFacts k)
    match ← g.mvarId!.falseOrByContra with
    | some g' => g'.withContext do
      -- (in the goal's context: with the hypothesis `x = k` of the contradiction)
      let facts ← (← getLCtx).foldlM (init := extra) fun acc d => do
        if d.isImplementationDetail then return acc
        return if isArithFact (← instantiateMVars d.type) then d.toExpr :: acc else acc
      Lean.Elab.Tactic.Omega.omega facts g' {}
    | none => pure ()
    return some (← instantiateMVars g)
  catch _ =>
    s.restore
    return none

open Lean Meta in
/-- A lookup of `e` through a point update whose key `omega` cannot tell from
the block looked up (`keysDistinct`): the same block may be reached by two
pointers. -/
def hasAliasedLookup (e : Lean.Expr) : MetaM Bool := do
  let mut seen : Array Lean.Expr := #[]
  for _ in [0:8] do
    let some u := e.find? fun t =>
        t.isAppOfArity ``upd 7 && !t.hasLooseBVars && t.getArg! 4 != t.getArg! 6 && !seen.contains t
      | return false
    seen := seen.push u
    if (← keysDistinct (u.getArg! 6) (u.getArg! 4)).isNone then return true
  return false

open Lean Meta Simp in
/-- A proof of `rhs = target` (a constant: `true`, `false`, `none`), for a
term `rhs` left open on a block looked up through a point update,
`upd f k v x`: with `x ≠ k` by `omega` (`keysDistinct`), `upd f k v x`
rewritten to `f x`; with `x = k` undecided (the same block reached by two
pointers, such as the first and the last item of a list), by cases on `x = k`,
`rhs` simplified in each case with `upd f k v x` rewritten to `v` or to `f x`,
nested up to `depth` times. -/
partial def decideByUpdCases (thms : SimpTheoremsArray) (rhs target : Expr) (depth : Nat) :
    SimpM (Option Expr) := do
  if depth == 0 then return none
  let some u := rhs.find? fun t =>
      t.isAppOfArity ``upd 7 && !t.hasLooseBVars && t.getArg! 4 != t.getArg! 6
    | return none
  let a := u.getAppArgs
  let p ← mkEq a[6]! a[4]!
  -- `rhs` with the lookup `u` abstracted: each case rewrites it directly and simplifies the
  -- new term with the results simp has (valid under the case's hypothesis), dropping what it
  -- adds under the hypothesis afterwards
  let motive ← kabstract rhs u
  let fn := Expr.lam `z (← inferType u) motive .default
  if let some hne ← keysDistinct a[6]! a[4]! then
    let eq ← mkAppOptM ``upd_apply_of_ne ((a.extract 0 7).map some ++ #[some hne])
    let rhs' := motive.instantiate1 (mkApp a[3]! a[6]!)
    let pr0 ← mkExpectedTypeHint (← mkCongrArg fn eq) (← mkEq rhs rhs')
    let (r, pr1) ← simpEqOf rhs'
    let pr ← mkEqTrans pr0 pr1
    if isConstLike r target then return some pr
    if blockedElsewhere r then return none
    let some pr' ← decideByUpdCases thms r target depth | return none
    return some (← mkEqTrans pr pr')
  let byCase (pos : Bool) : SimpM (Option Expr) :=
    withLocalDeclD `h (if pos then p else mkNot p) fun h => do
      let eq ← mkAppOptM (if pos then ``upd_apply_of_eq else ``upd_apply_of_ne)
        ((a.extract 0 7).map some ++ #[some h])
      let rhs' := motive.instantiate1 (if pos then a[5]! else mkApp a[3]! a[6]!)
      let pr0 ← mkExpectedTypeHint (← mkCongrArg fn eq) (← mkEq rhs rhs')
      let saved := (← get).cache
      let (r, pr1) ← try simpEqOf rhs' finally modify fun s => { s with cache := saved }
      let pr ← mkEqTrans pr0 pr1
      let pr? ← if isConstLike r target then pure (some pr)
        else match ← decideByUpdCases thms r target (depth - 1) with
          | some pr' => some <$> mkEqTrans pr pr'
          | none => pure none
      pr?.mapM (mkLambdaFVars #[h] ·)
  let some h1 ← byCase true | return none
  let some h2 ← byCase false | return none
  some <$> mkAppOptM ``Decidable.byCases
    #[some p, some (← mkEq rhs target), some (mkApp2 a[2]! a[6]! a[4]!), some h1, some h2]

open Lean Meta Simp in
/-- A proof of `lhs = target` (a constant: `true`, `false`, `none`), from
`lhs` simplified (`first`, or simplified here), then by cases on an undecided
block of a point update (`decideByUpdCases`). `none`: not decided `target`. -/
def decideTo (lhs target : Expr) (first : Option (Expr × Expr) := none) :
    SimpM (Option Expr) := do
  let (tv, ht) ← match first with | some r => pure r | none => simpEqOf lhs
  if isConstLike tv target then return some ht
  if (← isConstructorApp tv) || blockedElsewhere tv then return none
  let some hc ← decideByUpdCases (← Simp.getSimpTheorems) tv target 2 | return none
  some <$> mkEqTrans ht hc

open Lean Meta Simp in
/-- A type test of a block (`Ctx.reachTypeNone`, `Ctx.memberRelated`,
`Ctx.punnedMember`) decided: its definition unfolded and simplified (the
functions of a block's type at the type the context's type facts give,
`reduceTyArg…`, which keep a function of a block bound inside the visited term
for when the block is known: a block reached through a pointer computed in the
same step has its facts only after it), then by cases on an undecided block key
of a point update (`decideByUpdCases`) towards the outcome `expected` of the
ordinary access (no other lookup pending: `blockedElsewhere`). Undecided, the
simplified definition, or the test itself under a binder. -/
def reduceTypeTestImpl (expected : Bool) (e : Expr) : SimpM Lean.Meta.Simp.Step := do
  let some body ← unfoldDefinition? e (ignoreTransparency := true) | return .continue
  let (tv, ht) ← simpEqOf body
  let ht ← mkExpectedTypeHint ht (← mkEq e tv)
  let res ← if tv.isConstOf ``Bool.true || tv.isConstOf ``Bool.false then pure (some (tv, ht))
    else if blockedElsewhere tv then pure none else
      let target := mkConst (if expected then ``Bool.true else ``Bool.false)
      match ← decideByUpdCases (← Simp.getSimpTheorems) tv target 2 with
      | some hc => pure (some (target, ← mkEqTrans ht hc))
      | none => pure none
  let some (v, pf) := res |
    if let .done _ ← keepUnderBinder e then return .done { expr := e }
    -- its block possibly reached by two pointers (`hasAliasedLookup`) and no other lookup
    -- pending: folded until that is decided (symbolic execution does not case on a folded
    -- test, `isOpenIte`; the fallback unfolds it); a lookup left to symbolic execution's
    -- lookups (`blockedElsewhere`, keys `omega` tells apart) is unfolded, for them to see it
    else if !blockedElsewhere tv && !(← inFallback) && (← hasAliasedLookup tv) then
      return .done { expr := e }
    else return .done { expr := tv, proof? := some ht }
  return .done { expr := v, proof? := some pf }

simproc ↓ [cir_exec] reduceReachTypeNone (Ctx.reachTypeNone _ _ _ _) := reduceTypeTestImpl true

simproc ↓ [cir_exec] reduceMemberRelated (Ctx.memberRelated _ _ _ _ _) := reduceTypeTestImpl true

simproc ↓ [cir_exec] reducePunnedMember (Ctx.punnedMember _ _ _ _) := reduceTypeTestImpl false

open Lean Meta Simp in
/-- `ctx.typedLoad m ty p` (`load := true`) or `ctx.typedStore m ty p v`
once it is known to be the ordinary access at its pointer: the union members on
the path decided (the view of a load, `Ctx.unionView?`, or the activation of a
store, `Ctx.unionActivate?`: `none` when nothing changes), then `Ctx.reach?`
`none` in the memory the access sees (no byte access, no scalar access at an
aggregate's path, no record access at another record type) and its record
member check decided: all are simplified first, in the same simp run (`decideTo`,
where the block is looked up through a point update), and the access becomes
`loadTy` / `storeTy` on that memory (or undefined), so symbolic execution meets
the same terms as without them when no union member changes, not an extra
`match` and `if` (whose branches simp would visit under their conditions).
Undecided, or another access: `.continue`, and the definition unfolds. -/
def reduceTypedAccess (load : Bool) (e : Expr) : SimpM Lean.Meta.Simp.Step := do
  let n := if load then 4 else 5
  unless e.getAppNumArgs == n do return .continue
  let a := e.getAppArgs
  -- the union members on the path: unchanged (`none`), or the memory the access sees; an
  -- undecided block of a point update cased on towards `none`, as for `Ctx.reach?` below
  let uv ← mkAppM (if load then ``Ctx.unionView? else ``Ctx.unionActivate?) #[a[0]!, a[1]!, a[3]!]
  let (o, hu) ← simpEqOf uv
  let (o, hu) ← if o.isAppOfArity ``Option.none 1 || o.isAppOfArity ``Option.some 2 then pure (o, hu) else
    let none' ← mkAppOptM ``Option.none #[(← inferType uv).appArg!]
    let some hu ← decideTo uv none' (o, hu)
      | return (← keepUnderBinder e)
    pure (none', hu)
  let m ← mkAppM ``Option.getD #[o, a[1]!]
  let reach ← mkAppM ``Ctx.reach? #[a[0]!, m, a[2]!, a[3]!]
  let (bv, h0) ← simpEqOf reach
  let h0 ← if bv.isAppOfArity ``Option.none 1 then pure h0 else
    let some h0 ← decideTo reach (← mkAppOptM ``Option.none #[(← inferType reach).appArg!]) (bv, h0)
      | return (← keepUnderBinder e)
    pure h0
  let punned ← mkAppM ``Ctx.punnedMember #[a[0]!, m, a[2]!, a[3]!]
  let (v, h) ← simpEqOf punned
  let (lem, h) ← if v.isConstOf ``Bool.false then
      pure (if load then ``Ctx.typedLoad_eq_loadTy else ``Ctx.typedStore_eq_storeTy, h)
    else if v.isConstOf ``Bool.true then
      pure (if load then ``Ctx.typedLoad_eq_ub else ``Ctx.typedStore_eq_ub, h)
    else
      let some h ← decideTo punned (mkConst ``Bool.false) (v, h) | return (← keepUnderBinder e)
      pure (if load then ``Ctx.typedLoad_eq_loadTy else ``Ctx.typedStore_eq_storeTy, h)
  let pf ← if load then mkAppM lem #[hu, h0, h]
    else mkAppOptM lem #[none, none, none, none, some a[4]!, none, some hu, some h0, some h]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .visit { expr := rhs, proof? := some pf }

simproc ↓ [cir_exec] reduceTypedLoad (Ctx.typedLoad _ _ _ _) := reduceTypedAccess true

simproc ↓ [cir_exec] reduceTypedStore (Ctx.typedStore _ _ _ _ _) := reduceTypedAccess false

open Lean Meta Simp in
/-- `ctx.reachIn blk ty path` is `none` when the type of the object at the
path decides it (`Ctx.reachTypeNone`, `decideTo`), so that symbolic
execution meets neither the slow cases' definitions nor an `if` on a type it
cannot decide. Otherwise `.continue`, and the definition unfolds. -/
def reduceReachInImpl (e : Expr) : SimpM Lean.Meta.Simp.Step := do
  unless e.getAppNumArgs == 4 do return .continue
  let a := e.getAppArgs
  let lhs ← mkAppM ``Ctx.reachTypeNone #[a[0]!, a[1]!, a[2]!, a[3]!]
  let some ht ← decideTo lhs (mkConst ``Bool.true) | keepUnderBinder e
  let pf ← mkAppM ``Ctx.reachIn_of_typeNone #[ht]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .done { expr := rhs, proof? := some pf }

simproc ↓ [cir_exec] reduceReachIn (Ctx.reachIn _ _ _ _) := reduceReachInImpl

open Lean Meta Simp in
/-- `ctx.memberPath m b path rt i` is member `i` of the object at `path` when
its type shows a record of a related type (`Ctx.memberRelated`), decided as in
`reduceReachInImpl`. Otherwise `.continue`. -/
def reduceMemberPathImpl (e : Expr) : SimpM Lean.Meta.Simp.Step := do
  unless e.getAppNumArgs == 6 do return .continue
  let a := e.getAppArgs
  let lhs ← mkAppM ``Ctx.memberRelated #[a[0]!, a[1]!, a[2]!, a[3]!, a[4]!]
  let some ht ← decideTo lhs (mkConst ``Bool.true) | keepUnderBinder e
  let pf ← mkAppOptM ``Ctx.memberPath_of_related #[none, none, none, none, none, some a[5]!, some ht]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  return .visit { expr := rhs, proof? := some pf }

simproc ↓ [cir_exec] reduceMemberPath (Ctx.memberPath _ _ _ _ _ _) := reduceMemberPathImpl

end CIR

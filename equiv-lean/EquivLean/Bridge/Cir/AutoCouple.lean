import EquivLean.Bridge.Cir.Tactic

/-!
# Generated coupling invariants for loop pairs of the same shape

`equiv_cir` (no `using`) on two CIR functions with loops first tries a coupling invariant it
generates itself from the loop slots of both sides (`loopSlots`):

* the variables both loops modify are paired by C name and kind (`int`, `size_t`, the
  iterator of a range-`for`), the rest by position (same kind): `x = x'`;
* a variable only one loop modifies keeps its value at loop entry (`r = -1` for a result
  variable assigned only on the iteration that leaves the loop), when that value computes;
  a second attempt leaves such variables unconstrained (assigned before use);
* a third attempt adds the loop bounds: `x ≤ y` (`y ≤ x`) for a counter `x` that a loop
  condition compares by `<`, `≠` (`>`) with a variable `y` the loop does not modify (entry
  value of `y`, on both sides), e.g. `i ≤ n` for `i < n` against `i != n`;
* a fourth attempt also pairs a range-`for` iterator with a `size_t` index by position (both
  are element positions, `Nat`) and bounds the paired `size_t` counters and iterator positions by
  the length of a caller's vector (`it ≤ L.length` for each hypothesis
  `m.blocks b = some ⟨_, _, _, .vec g L⟩` in context), the other variables unconstrained, e.g. a
  range-`for` over a `std::vector` against an index loop up to `v.size()`
  (`Demo/Cir/AutoVector.lean`);

i.e. what one would write as `equiv_cir using (fun x y x' y' => x = x' ∧ y = y')`.  Each
attempt must close every goal; otherwise `equiv_cir` falls back to its previous behaviour and
a coupling has to be given with `equiv_cir using inv`.  Loops in sequence are paired
automatically one after the other.
-/

namespace EquivLean.Cir.Tactic

open Lean Meta Elab Tactic
open CIR.Tactic (holdsHead?)

/-- The value of the `int` slot `b` in the explicit state `σ₀`, when the lookup computes. -/
def entryIntValue? (σ₀ b : Expr) : TacticM (Option Expr) := do
  let lhs ← mkAppM ``CIR.State.intAt #[σ₀, b]
  let v ← mkFreshExprMVar (mkConst ``Int)
  let g ← mkFreshExprMVar (← mkEq lhs v)
  let saved ← getGoals
  try
    setGoals [g.mvarId!]
    evalTactic (← `(tactic| simp only [CIR.State.intAt_mk, CIR.Mem.mk_blocks, CIR.Tactic.reduceUpd]))
    unless (← getGoals).isEmpty do evalTactic (← `(tactic| rfl))
    let v ← instantiateMVars v
    if v.hasExprMVar || (v.find? fun e => e.isConstOf ``CIR.State.intAt || e.isConstOf ``CIR.upd).isSome
    then return none
    return some v
  catch _ => return none
  finally setGoals saved

/-- A loop variable of one side: block, C name, kind. -/
structure AutoVar where
  blk : Expr
  name : String
  kind : CIR.Tactic.SlotKind
  deriving Inhabited

/-- The variables a loop modifies that a coupling can talk about: named `int`/`size_t` slots
it stores to, and the hidden iterator of a range-`for`. -/
def autoVars (side : LoopSide) : TacticM (Array AutoVar) := do
  let (stored, passed) ← loopSlots side
  let mut out : Array AutoVar := #[]
  for (b, ty, n) in stored do
    -- compiler slots (`__retval`, …) are assigned before use: not coupled
    if n.isEmpty || n.startsWith "__" then continue
    match ← CIR.Tactic.slotKindOf? ty with
    | some .int => out := out.push ⟨b, n, .int⟩
    | some .nat => out := out.push ⟨b, n, .nat⟩
    | _ => pure ()
  for (b, ty, n) in passed do
    if n.startsWith "__begin" && (← CIR.Tactic.slotKindOf? ty) == some .iter then
      unless ← out.anyM (fun v => isDefEq v.blk b) do out := out.push ⟨b, n, .iter⟩
  return out

/-- The comparisons `x OP y` of a loop's condition region whose operands are loaded from two
slots of the loop-entry state: `(block of x, kind, block of y)`. -/
def condCompares (side : LoopSide) : MetaM (Array (Expr × Name × Expr)) := do
  let cond := if side.shape == ``EquivLean.Cir.loopShape_do then side.args[2]! else side.args[1]!
  let cond ← whnfD cond
  unless cond.isAppOfArity ``CIR.Region.mk 1 do return #[]
  let some blocks ← CIR.Tactic.listElems cond.appArg! | return #[]
  let mut loads : Array (Nat × Expr) := #[]
  let mut out : Array (Expr × Name × Expr) := #[]
  for blk in blocks do
    let blk ← whnfD blk
    unless blk.isAppOfArity ``CIR.Block.mk 2 do continue
    let some ops ← CIR.Tactic.listElems blk.appArg! | continue
    for op in ops do
      let op ← whnfD op
      if op.isAppOfArity ``CIR.Op.load 3 then
        if let (some r, some b) := (← evalNat (op.getArg! 0), ← CIR.Tactic.envSlot? side.σ₀ (op.getArg! 1)) then
          loads := loads.push (r, b)
      else if op.isAppOfArity ``CIR.Op.cmp 5 then
        let k ← whnfD (op.getArg! 1)
        let some kn := k.constName? | continue
        let (some a, some b) := (← evalNat (op.getArg! 2), ← evalNat (op.getArg! 3)) | continue
        if let (some (_, ba), some (_, bb)) := (loads.find? (·.1 == a), loads.find? (·.1 == b)) then
          out := out.push (ba, kn, bb)
  return out

/-- `cir_auto_pair h k`: `cir_loop_pair h inv` with a generated coupling `inv` (pairs by name and
kind, then by position; with `k = 1, 2` the other variables keep their entry values; with `k = 2`
also the bounds `x ≤ y` (`y ≤ x`) of the counters compared by `<`, `≠` (`>`) with a variable
the loop does not modify, on both sides; with `k = 3` an iterator may also be paired with a
`size_t` index, and the paired counters and iterator positions are bounded by the length of each
caller vector in context, the other variables unconstrained). -/
elab "cir_auto_pair " h:ident k:num : tactic => do
  let withEntry := k.getNat == 1 || k.getNat == 2
  let withBounds := k.getNat == 2
  let withContainers := k.getNat == 3
  let g ← getMainGoal
  let inv ← g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    let some x := holdsHead? t | throwError "cir_auto_pair: the goal is not `Res.holds _ _`"
    let some sT := loopSide? (← instantiateMVars x)
      | throwError "cir_auto_pair: the head of the goal is not a loop"
    let some (y, _) ← hypHolds? h.getId | throwError "cir_auto_pair: {h} is not `Res.holds _ _`"
    let some sS := loopSide? y | throwError "cir_auto_pair: the head of {h} is not a loop"
    let vT ← autoVars sT
    let vS ← autoVars sS
    if !withContainers && (vT.any (·.kind == .iter) || vS.any (·.kind == .iter)) then
      throwError "cir_auto_pair: range-for iterator requires k = 3"
    -- pair by name and kind, then the rest by position (same kind)
    let mut pairs : Array (Nat × Nat) := #[]
    let mut usedS : Array Nat := #[]
    for i in [0:vT.size] do
      if let some j := (List.range vS.size).find? fun j =>
          !usedS.contains j && vS[j]!.name == vT[i]!.name && vS[j]!.kind == vT[i]!.kind then
        pairs := pairs.push (i, j); usedS := usedS.push j
    for i in [0:vT.size] do
      if pairs.any (·.1 == i) then continue
      if let some j := (List.range vS.size).find? fun j =>
          !usedS.contains j && vS[j]!.kind == vT[i]!.kind then
        pairs := pairs.push (i, j); usedS := usedS.push j
    -- with `k = 3`: an iterator position against a `size_t` index (range-`for` against an index
    -- loop; both `Nat`)
    for i in [0:vT.size] do
      unless withContainers do break
      if pairs.any (·.1 == i) then continue
      let natLike (k : CIR.Tactic.SlotKind) := k == .iter || k == .nat
      if let some j := (List.range vS.size).find? fun j =>
          !usedS.contains j && natLike vS[j]!.kind && natLike vT[i]!.kind then
        pairs := pairs.push (i, j); usedS := usedS.push j
    -- binder names: `x` for the target's variable `x`, `x'` for the source's; an iterator is
    -- named by a non-variable name (`cir_loop_pair` maps it to the hidden `__begin`)
    let bT (i : Nat) : Name :=
      if vT[i]!.kind == CIR.Tactic.SlotKind.iter then Name.mkSimple s!"cirIterT{i}" else Name.mkSimple vT[i]!.name
    let bS (j : Nat) : Name :=
      if vS[j]!.kind == CIR.Tactic.SlotKind.iter then Name.mkSimple s!"cirIterS{j}'" else Name.mkSimple (vS[j]!.name ++ "'")
    let mut binders : Array Ident := #[]
    let mut facts : Array Term := #[]
    for (i, j) in pairs do
      let a := mkIdent (bT i)
      let b := mkIdent (bS j)
      binders := binders.push a |>.push b
      facts := facts.push (← `($a = $b))
    if withEntry then
      for i in [0:vT.size] do
        if pairs.any (·.1 == i) || vT[i]!.kind == CIR.Tactic.SlotKind.iter then continue
        if let some v ← entryIntValue? sT.σ₀ vT[i]!.blk then
          let a := mkIdent (bT i)
          binders := binders.push a
          let vS ← Lean.Elab.Term.exprToSyntax v
          facts := facts.push (← if vT[i]!.kind == CIR.Tactic.SlotKind.nat then `(($a : Int) = $vS) else `($a = $vS))
      for j in [0:vS.size] do
        if usedS.contains j || vS[j]!.kind == CIR.Tactic.SlotKind.iter then continue
        if let some v ← entryIntValue? sS.σ₀ vS[j]!.blk then
          let b := mkIdent (bS j)
          binders := binders.push b
          let vS' ← Lean.Elab.Term.exprToSyntax v
          facts := facts.push (← if vS[j]!.kind == CIR.Tactic.SlotKind.nat then `(($b : Int) = $vS') else `($b = $vS'))
    if withBounds then
      -- bounds of the counters in the loop conditions, against unmodified variables
      let (storedT, _) ← loopSlots sT
      let (storedS, _) ← loopSlots sS
      for (side, vs, stored, isSrc) in [(sT, vT, storedT, false), (sS, vS, storedS, true)] do
        for (bx, kn, byy) in ← condCompares side do
          if ← stored.anyM (fun (b, _, _) => isDefEq b byy) then continue
          let some i ← (List.range vs.size).findM? fun i => isDefEq vs[i]!.blk bx | continue
          unless binders.any (·.getId == (if isSrc then bS i else bT i)) do continue
          if vs[i]!.kind == CIR.Tactic.SlotKind.iter then continue
          let some y ← entryIntValue? side.σ₀ byy | continue
          let yS ← Lean.Elab.Term.exprToSyntax y
          let x := mkIdent (if isSrc then bS i else bT i)
          let xI ← if vs[i]!.kind == CIR.Tactic.SlotKind.nat then `(($x : Int)) else `($x)
          if kn == ``CIR.CmpKind.lt || kn == ``CIR.CmpKind.ne then facts := facts.push (← `($xI ≤ $yS))
          else if kn == ``CIR.CmpKind.gt then facts := facts.push (← `($yS ≤ $xI))
    if withContainers then
      -- container bounds: a target counter or iterator position paired with the other side is at
      -- most the length of the element list of a vector block of the caller (a hypothesis
      -- `m.blocks b = some ⟨k, alive, ty, .vec g L⟩` in context)
      let mut lists : Array Expr := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        let some (_, _, rhs) := ty.eq? | continue
        let rhs := rhs.consumeMData
        unless rhs.isAppOfArity ``Option.some 2 do continue
        let blk := rhs.appArg!.consumeMData
        unless blk.isAppOfArity ``CIR.MemBlock.mk 4 do continue
        let v := (blk.getArg! 3).consumeMData
        unless v.isAppOfArity ``CIR.Val.vec 2 do continue
        -- `List.map f xs` (e.g. `xs.map .int`): bound by `xs.length`, the form cirlean's
        -- closers relate to hypotheses about the elements of `xs`
        let mut l := (v.getArg! 1).consumeMData
        while l.isAppOfArity ``List.map 4 do l := (l.getArg! 3).consumeMData
        lists := lists.push l
      for (i, _) in pairs do
        unless vT[i]!.kind == CIR.Tactic.SlotKind.iter || vT[i]!.kind == CIR.Tactic.SlotKind.nat do
          continue
        for L in lists do
          let LS ← Lean.Elab.Term.exprToSyntax L
          let x := mkIdent (bT i)
          facts := facts.push (← `($x ≤ List.length $LS))
    if facts.isEmpty then throwError "cir_auto_pair: no loop variables to couple"
    let mut body : Term := facts.back!
    for f in facts.pop.reverse do
      body ← `($f ∧ $body)
    `(fun $binders* => $body)
  evalTactic (← `(tactic| cir_loop_pair $h $inv))

/-- The continuation leaf of `cir_pair_step_auto`: a further pair of loops is coupled
automatically. -/
syntax "cir_pair_cont_auto" : tactic
/-- `cir_pair_step` whose continuations pair further loops automatically. -/
syntax "cir_pair_step_auto" : tactic

macro_rules
  | `(tactic| cir_pair_cont_auto) => `(tactic| (
      cir_is_cont_goal
      intro hk
      try dsimp only at hk
      cir_hrun hk
      all_goals (try subst hk)
      all_goals (try cir_vcg)
      all_goals (try cir_obs_close)
      all_goals (try (cir_auto_pair hk 1
                      all_goals (first | (cir_is_sim_goal; cir_pair_step_auto) | cir_vcg)))))

macro_rules
  | `(tactic| cir_pair_step_auto) => `(tactic| (
      rw [EquivLean.Cir.sim_res_res]
      intro os hsi
      cir_hrun hsi
      all_goals (try subst hsi)
      all_goals (try cir_vcg_tgt)
      all_goals (try simp only [EquivLean.StepRel, EquivLean.Cir.loopCls, id])
      all_goals (first | cir_pair_cont_auto | (try cir_vcg))))

/-- `Sim R t s` between two CIR computations with loops, coupled by generated invariants
(first with entry values for unpaired variables, then without); fails unless every goal
closes. -/
syntax "cir_sim_loop_auto" : tactic
macro_rules
  | `(tactic| cir_sim_loop_auto) => `(tactic| (
      rw [EquivLean.Cir.sim_res_res]
      intro os hs
      cir_hrun hs
      all_goals (try cir_call_inline)
      all_goals (try cir_vcg)
      all_goals (first
        | (cir_auto_pair hs 1
           all_goals (first | (cir_is_sim_goal; cir_pair_step_auto) | cir_vcg)
           done)
        | (cir_auto_pair hs 0
           all_goals (first | (cir_is_sim_goal; cir_pair_step_auto) | cir_vcg)
           done)
        | (cir_auto_pair hs 2
           all_goals (first | (cir_is_sim_goal; cir_pair_step_auto) | cir_vcg)
           done)
        | (cir_auto_pair hs 3
           all_goals (first | (cir_is_sim_goal; cir_pair_step_auto) | cir_vcg)
           done))))

/-- Straight-line code (`cir_sim`), or loops with generated couplings; fails unless every
goal closes. -/
macro "cir_sim_auto" : tactic => `(tactic| first
  | (cir_sim; done)
  | cir_sim_loop_auto
  | fail "equiv_cir: no generated coupling closes this loop pair; give one with `equiv_cir using (fun x y x' y' => …)`")

/-- `equiv_cir` first tries the generated couplings for loops (`cir_sim_auto`, both
directions); if that fails, the previous `equiv_cir` (which leaves loop goals open). -/
macro_rules
  | `(tactic| equiv_cir) => `(tactic| (
      try cir_equivOn_intro
      first
      | (refine ⟨?_, ?_⟩
         · cir_sim_auto
         · (try rw [EquivLean.Cir.obsEq_flip]); cir_sim_auto)
      | cir_sim_auto))

end EquivLean.Cir.Tactic

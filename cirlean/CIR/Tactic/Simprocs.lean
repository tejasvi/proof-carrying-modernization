import Lean
import Lean.Elab.Tactic.Omega
import CIR.Logic.Exec
import CIR.Tactic.Options
import CIR.Tactic.Lookup

/-!
  Simprocs that evaluate lookups in symbolic states.

  SSA environments and memory are chains of `upd f a b`. A lookup
  `upd f a b x` is decided one layer at a time, top-down, by comparing the keys
  `x` and `a` syntactically: both natural literals, or both of the form
  `t + k` (block ids `next + k`) with the same `t`. No `if` is created, so the
  cost of a lookup is linear in the depth of the key in the chain.
-/

namespace CIR

theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : upd f a b a = b := by
  simp [upd]

theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) (h : x ≠ a) :
    upd f a b x = f x := by
  simp [upd, h]

theorem nat_offset_ne (t : Nat) {j k : Nat} (h : j ≠ k) : t + j ≠ t + k := by omega
theorem nat_ne_offset_of_lt {b t : Nat} (k : Nat) (h : b < t) : b ≠ t + k := by omega
theorem nat_offset_ne_offset_of_le {t u : Nat} {k c : Nat} (j : Nat) (h : t + c ≤ u) (hk : k < c) :
    t + k ≠ u + j := by omega
theorem nat_offset_lt_offset_of_le {t u : Nat} {k c : Nat} (j : Nat) (h : t + c ≤ u) (hk : k < c) :
    t + k < u + j := by omega
theorem nat_offset_ne_of_lt {b t : Nat} (k : Nat) (h : b < t) : t + k ≠ b := by omega
theorem nat_lt_offset_of_lt {b t : Nat} (k : Nat) (h : b < t) : b < t + k := by omega
theorem nat_self_ne_offset (t : Nat) {k : Nat} (h : k ≠ 0) : t ≠ t + k := by omega
theorem nat_offset_ne_self (t : Nat) {k : Nat} (h : k ≠ 0) : t + k ≠ t := by omega
theorem nat_lit_ne_offset {n k : Nat} (t : Nat) (h : n < k) : n ≠ t + k := by omega
/-- A block with contents in a well-formed memory lies below its `next`. -/
theorem lt_next_of_blocks_some {m : Mem} {b : Nat} {v : MemBlock} (hwf : m.WF) (h : m.blocks b = some v) :
    b < m.next := by
  apply Nat.lt_of_not_le; intro hle; rw [hwf b hle] at h; cases h
theorem ne_offset_of_lt_next {m : Mem} {b k : Nat} (h : b < m.next) : b ≠ m.next + k := by omega
theorem ne_offset_of_lt_le {b n t k : Nat} (h : b < n) (hn : n ≤ t) : b ≠ t + k := by omega
theorem nat_offset_ne_lit {n k : Nat} (t : Nat) (h : n < k) : t + k ≠ n := by omega

theorem killRange_lt (lo hi : Nat) (bs : Nat → Option MemBlock) (b : Nat) (h : b < lo) :
    killRange lo hi bs b = bs b := by
  simp only [killRange]; split <;> first | omega | rfl

theorem killRange_ge (lo hi : Nat) (bs : Nat → Option MemBlock) (b : Nat) (h : hi ≤ b) :
    killRange lo hi bs b = bs b := by
  simp only [killRange]; split <;> first | omega | rfl

theorem killRange_in (lo hi : Nat) (bs : Nat → Option MemBlock) (b : Nat) (h₁ : lo ≤ b) (h₂ : b < hi) :
    killRange lo hi bs b = (match bs b with
       | some blk => if blk.kind = .stack then none else some blk
       | none => none) := by
  simp only [killRange]; split <;> first | rfl | omega

namespace Tactic
open Lean Meta Simp

/-- Syntactic offset form of a natural-number key: a literal `n`, or `t + n`
with a literal `n` (block ids `next + k` are kept in this form by
`Nat.add_assoc` and literal folding), or an atom `t` (offset 0). -/
inductive Key where
  | lit (n : Nat)
  | off (t : Expr) (k : Nat) (kE : Expr)
  | atom (t : Expr)

def toKey (e : Expr) : MetaM Key := do
  let e ← instantiateMVars e
  if let some n := e.nat? then return .lit n
  if let some n := e.rawNatLit? then return .lit n
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let k := e.getArg! 5
    if let some kn := k.nat? then return .off (e.getArg! 4) kn k
  return .atom e

def sameBase (t u : Expr) : MetaM Bool :=
  if t == u then return true else withReducible (isDefEq t u)

/-- A hypothesis `h : b < t` in the local context (e.g. a caller's block id
below the current `next`). -/
def findLtHyp (b t : Expr) : MetaM (Option Expr) := do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.app4? ``LT.lt |>.map (fun (a, _, l, r) => (a, l, r)) | continue
    if lhs == b && rhs == t then return some d.toExpr
    if (← withReducible (isDefEq lhs b)) && (← withReducible (isDefEq rhs t)) then return some d.toExpr
  return none

/-- Instances of the hypotheses `∀ k (h : k < l.length), Q k` (facts about
the elements of a list, e.g. the nodes of a linked list given as a list of
blocks: `∀ k h, bs[k] < m.next`) at the elements `l[i]` of `e`, with the
bound proof that `l[i]` carries. -/
def idxInstances (e : Expr) : MetaM (Array Expr) := do
  let mut hyps : Array (Expr × Expr) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let .forallE _ dom body _ := ty | continue
    unless dom.isConstOf ``Nat do continue
    let .forallE _ hb _ _ := body | continue
    -- `k < List.length l`
    unless hb.isAppOfArity ``LT.lt 4 do continue
    let len := hb.getArg! 3
    unless len.isAppOfArity ``List.length 2 && hb.getArg! 2 == .bvar 0 do continue
    let l := len.getArg! 1
    if l.hasLooseBVars then continue
    hyps := hyps.push (d.toExpr, l)
  if hyps.isEmpty then return #[]
  let r ← IO.mkRef (#[] : Array Expr)
  e.forEachWhere (fun t => t.isAppOfArity ``GetElem.getElem 8 && !t.hasLooseBVars &&
      (t.getArg! 0).isAppOfArity ``List 1) fun t => r.modify fun a => if a.contains t then a else a.push t
  let mut out := #[]
  for t in ← r.get do
    for (h, l) in hyps do
      unless ← withReducible (isDefEq (t.getArg! 5) l) do continue
      let inst := mkApp2 h (t.getArg! 6) (t.getArg! 7)
      if (← observing? (do let _ ← inferType inst; check inst)).isSome then out := out.push inst
  return out

/-- Prove a linear arithmetic fact `p` from the local context with `omega`
(the general path, used when keys cannot be compared syntactically). -/
def omegaProof? (p : Expr) : MetaM (Option Expr) := do
  if (← getOptions).getBool `cir.traceOmega false then
    logInfo m!"cir omega: {p}"
  let g ← mkFreshExprMVar p
  let s ← saveState
  try
    -- facts about the list elements in `p` first
    let mut mid := g.mvarId!
    for inst in ← idxInstances p do
      let (_, m') ← (← mid.assert `cirIdx (← inferType inst) inst).intro1P
      mid := m'
    let (gs, _) ← Lean.Elab.runTactic mid (← `(tactic| omega))
    if gs.isEmpty then return some (← instantiateMVars g)
    s.restore; return none
  catch _ =>
    s.restore; return none

/-- Close a goal `¬ p` / `a ∉ l` / `a ∈ l` from a quantified hypothesis
(`∀ j (h : j < ts.length), ts[j].b ∉ CJ.forestBlocks ts[j].child`): the
hypothesis's conclusion is unified with the goal, its remaining premises are
closed by assumption or `omega`. -/
elab_rules : tactic
  | `(tactic| cir_hyp_apply) => do
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
    let t ← instantiateMVars (← g.getType)
    let isTarget := t.isAppOfArity ``Not 1 || t.isAppOfArity ``Ne 3 || t.isAppOfArity ``Membership.mem 5
    unless isTarget do throwError "cir_hyp_apply: not a negation or membership goal"
    -- `¬a = b` (`a ≠ b`) also from a fact `¬b = a`
    let tSym? : Option Expr := Id.run do
      if t.isAppOfArity ``Ne 3 then
        return some (mkApp3 t.getAppFn (t.getArg! 0) (t.getArg! 2) (t.getArg! 1))
      unless t.isAppOfArity ``Not 1 do return none
      let e := t.getArg! 0
      unless e.isAppOfArity ``Eq 3 do return none
      return some (mkNot (mkApp3 e.getAppFn (e.getArg! 0) (e.getArg! 2) (e.getArg! 1)))
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ty.isForall || ty.isAppOf ``Not || ty.isAppOf ``Ne do continue
      let s ← saveState
      try
        -- the premises as written (not unfolding `¬`, `≠`, `∉` into `→ False`)
        let (xs, _, concl) ← forallMetaTelescope ty
        -- (a cheap test before unification: the same kind of proposition)
        let shapeOk := if t.isAppOfArity ``Membership.mem 5 then concl.isAppOf ``Membership.mem
          else concl.isAppOf ``Not || concl.isAppOf ``Ne
        unless shapeOk do s.restore; continue
        let direct ← isDefEq concl t
        let sym ← if direct then pure false else
          match tSym? with
          | some ts => isDefEq concl ts
          | none => pure false
        unless direct || sym do s.restore; continue
        let mut ok := true
        for mv in xs do
          if (← instantiateMVars mv).isMVar then
            let pty ← instantiateMVars (← inferType mv)
            unless ← isProp pty do ok := false; break
            match ← ((← getLCtx).findDeclM? fun d' => do
                if ← isDefEq (← instantiateMVars d'.type) pty then return some d'.toExpr else return none) with
            | some pf => mv.mvarId!.assign pf
            | none =>
              match ← omegaProof? pty with
              | some pf => mv.mvarId!.assign pf
              | none => ok := false; break
        unless ok do s.restore; continue
        let pf ← instantiateMVars (mkAppN d.toExpr xs)
        g.assign (← if sym then mkAppM ``Ne.symm #[pf] else pure pf)
        Lean.Elab.Tactic.replaceMainGoal []
        return
      catch _ => s.restore
    throwError "cir_hyp_apply: no hypothesis applies"

/-- `omega` after the facts about the list elements in the goal
(`idxInstances`): a discharger for bounds of `bs[k]`. -/
elab_rules : tactic
  | `(tactic| cir_idx_omega) => do
    let g ← Lean.Elab.Tactic.getMainGoal
    let insts ← g.withContext do idxInstances (← instantiateMVars (← g.getType))
    if insts.isEmpty then throwError "cir_idx_omega: no list element facts"
    let mut mid := g
    for inst in insts do
      let (_, m') ← (← mid.withContext do mid.assert `cirIdx (← inferType inst) inst).intro1P
      mid := m'
    Lean.Elab.Tactic.replaceMainGoal [mid]
    Lean.Elab.Tactic.evalTactic (← `(tactic| omega))

/-- A hypothesis `h : t + c ≤ u` (or `t ≤ u`, as `c = 0`) with `c > k`:
everything allocated from `t` below offset `c` lies below `u`. Returns `h`,
`c` and its literal. -/
def findOffsetLe (t : Expr) (k : Nat) (u : Expr) : MetaM (Option (Expr × Expr)) := do
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, _, lhs, rhs) := ty.app4? ``LE.le | continue
    unless ← sameBase rhs u do continue
    match ← toKey lhs with
    | .off t' c cE => if c > k && (← sameBase t' t) then return some (d.toExpr, cE)
    | _ => continue
  return none

/-- Syntactic (and hypothesis-bound) decision of `x = a` for natural-number
keys. -/
def decideNatKeySyn (x a : Expr) : MetaM (Option (Expr ⊕ Expr)) := do
  -- blocks of an older allocation range below the base of a newer one
  -- (an atom `t` is the offset `t + 0`)
  let asOff (k : Key) : Option (Expr × Nat × Expr) := match k with
    | .off t k kE => some (t, k, kE)
    | .atom t => some (t, 0, mkNatLit 0)
    | .lit _ => none
  if let (some (t, k, kE), some (u, j, jE)) := (asOff (← toKey x), asOff (← toKey a)) then
    if !(← sameBase t u) then
      if let some (h, cE) ← findOffsetLe t k u then
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, cE])
        let p := mkAppN (mkConst ``nat_offset_ne_offset_of_le) #[t, u, kE, cE, jE, h, hk]
        return some (.inr (← mkExpectedTypeHint p (← mkAppM ``Ne #[x, a])))
      if let some (h, cE) ← findOffsetLe u j t then
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[jE, cE])
        let p := mkAppN (mkConst ``nat_offset_ne_offset_of_le) #[u, t, jE, cE, kE, h, hk]
        return some (.inr (← mkExpectedTypeHint (← mkAppM ``Ne.symm #[p]) (← mkAppM ``Ne #[x, a])))
  -- an atom below the base of a fresh block: `b < t` gives `b ≠ t + k`
  match ← toKey x, ← toKey a with
  | .atom b, .off t k kE =>
    if let some h ← findLtHyp b t then
      return some (.inr (mkApp4 (mkConst ``nat_ne_offset_of_lt) b t kE h))
  | .off t k kE, .atom b =>
    if let some h ← findLtHyp b t then
      return some (.inr (mkApp4 (mkConst ``nat_offset_ne_of_lt) b t kE h))
  | .atom u, .atom v =>
    -- two atoms ordered by a hypothesis: `u < v` or `v < u`
    if !(← sameBase u v) then
      if let some h ← findLtHyp u v then
        return some (.inr (← mkAppM ``Nat.ne_of_lt #[h]))
      if let some h ← findLtHyp v u then
        return some (.inr (← mkAppM ``Nat.ne_of_gt #[h]))
  | _, _ => pure ()
  match ← toKey x, ← toKey a with
  | .lit n, .lit k =>
    if n == k then return some (.inl (← mkEqRefl x))
    return some (.inr (← mkDecideProof (← mkAppM ``Ne #[x, a])))
  | .off t j jE, .off u k kE =>
    unless ← sameBase t u do return none
    if j == k then return some (.inl (← mkEqRefl x))
    let h ← mkDecideProof (← mkAppM ``Ne #[jE, kE])
    return some (.inr (mkApp4 (mkConst ``nat_offset_ne) t jE kE h))
  | .atom t, .off u k kE =>
    unless ← sameBase t u do return none
    if k == 0 then return none
    let h ← mkDecideProof (← mkAppM ``Ne #[kE, mkNatLit 0])
    return some (.inr (mkApp3 (mkConst ``nat_self_ne_offset) t kE h))
  | .off t j jE, .atom u =>
    unless ← sameBase t u do return none
    if j == 0 then return none
    let h ← mkDecideProof (← mkAppM ``Ne #[jE, mkNatLit 0])
    return some (.inr (mkApp3 (mkConst ``nat_offset_ne_self) t jE h))
  | .atom t, .atom u =>
    if ← sameBase t u then return some (.inl (← mkEqRefl x)) else return none
  -- a literal block (a global) against a fresh block `t + k` with `k > n`
  | .lit n, .off t k kE =>
    if n < k then
      let h ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit n, kE])
      return some (.inr (mkApp4 (mkConst ``nat_lit_ne_offset) (mkNatLit n) kE t h))
    return none
  | .off t k kE, .lit n =>
    if n < k then
      let h ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit n, kE])
      return some (.inr (mkApp4 (mkConst ``nat_offset_ne_lit) (mkNatLit n) kE t h))
    return none
  | _, _ => return none

/-- A proof of `x < m.next` from a well-formed memory `hwf : m.WF` and a fact
giving `m.blocks x = some _`: a hypothesis, or an instance of a quantified
one (`∀ j (h : j < ts.length), m.blocks ts[j].b = …`) whose premises are
assumptions or follow by `omega`. -/
def blockLtNext? (x : Expr) : MetaM (Option (Expr × Expr)) := do
  let lctx ← getLCtx
  for dw in lctx do
    if dw.isImplementationDetail then continue
    let wty ← instantiateMVars dw.type
    unless wty.isAppOfArity ``CIR.Mem.WF 1 do continue
    let m := wty.getArg! 0
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      -- cheap filter: the conclusion is `m.blocks _ = some _`
      let concl := Id.run do
        let mut c := ty
        for _ in [0:6] do
          match c with
          | .forallE _ _ b _ => c := b
          | _ => break
        return c
      let some (_, lhs0, rhs0) := concl.eq? | continue
      unless lhs0.isAppOfArity ``CIR.Mem.blocks 2 && rhs0.isAppOfArity ``Option.some 2 do continue
      unless (lhs0.getArg! 0) == m || !(lhs0.getArg! 0).hasLooseBVars do continue
      let s ← saveState
      try
        let (xs, _, body) ← forallMetaTelescopeReducing ty (some 4)
        let some (_, lhs, _) := body.eq? | s.restore; continue
        unless lhs.isAppOfArity ``CIR.Mem.blocks 2 do s.restore; continue
        unless ← isDefEq (lhs.getArg! 0) m do s.restore; continue
        unless ← isDefEq (lhs.getArg! 1) x do s.restore; continue
        -- the remaining premises (bounds) by assumption or `omega`
        let mut ok := true
        for mv in xs do
          if (← instantiateMVars mv).isMVar then
            let pty ← instantiateMVars (← inferType mv)
            if ← isProp pty then
              match ← (lctx.findDeclM? fun d' => do
                  if (← isDefEq (← instantiateMVars d'.type) pty) then return some d'.toExpr else return none) with
              | some pf => mv.mvarId!.assign pf
              | none =>
                match ← omegaProof? pty with
                | some pf => mv.mvarId!.assign pf
                | none => ok := false
            else ok := false
        unless ok do s.restore; continue
        let hfact ← instantiateMVars (mkAppN d.toExpr xs)
        let some (_, _, rhs) := (← inferType hfact).eq? | s.restore; continue
        let_expr Option.some _ v := rhs | s.restore; continue
        let pf ← mkAppOptM ``lt_next_of_blocks_some #[m, x, v, dw.toExpr, hfact]
        return some (pf, m)
      catch _ => s.restore
  return none

/-- Decide `x = a` for natural-number keys, with a proof whose type is
literally `x = a` (`Sum.inl`) or `x ≠ a` (`Sum.inr`). -/
def decideNatKey (x a : Expr) : MetaM (Option (Expr ⊕ Expr)) := do
  match ← decideNatKeySyn x a with
  | some r => return some r
  | none =>
    -- a caller's block (with contents) against a block allocated since the
    -- call (`m.next + k`): below `m.next` in a well-formed memory
    let ak ← toKey a
    let xk ← toKey x
    if !(xk matches .off _ _ _) then
      -- `t` is the `next` of a memory at or after the well-formed one
      let fresh (t kE : Expr) : MetaM (Option Expr) := do
        unless t.isAppOfArity ``CIR.Mem.next 1 do return none
        let some (h, m) ← blockLtNext? x | return none
        let n ← mkAppM ``CIR.Mem.next #[m]
        if ← isDefEq t n then return some (← mkAppOptM ``ne_offset_of_lt_next #[m, x, kE, h])
        let some hn ← omegaProof? (← mkAppM ``LE.le #[n, t]) | return none
        return some (← mkAppOptM ``ne_offset_of_lt_le #[x, n, t, kE, h, hn])
      match ak with
      | .off t _ kE => if let some p ← fresh t kE then return some (.inr p)
      | .atom t =>
        if let some p ← fresh t (mkNatLit 0) then
          -- `x ≠ t + 0` is `x ≠ t`
          return some (.inr (← mkExpectedTypeHint p (← mkAppM ``Ne #[x, a])))
      | _ => pure ()
    -- different bases: try `x ≠ a` by linear arithmetic over the hypotheses
    -- (a literal against a literal is decided above)
    if (← toKey x) matches .lit _ then
      if (← toKey a) matches .lit _ then return none
    match ← omegaProof? (← mkAppM ``Ne #[x, a]) with
    | some h => return some (.inr h)
    | none => return none

/-- Evaluate `upd f a b x` when the keys can be compared. -/
simproc_decl reduceUpd (upd _ _ _ _) := fun e => do
  unless e.isAppOfArity ``upd 7 do return .continue
  let α := e.getArg! 0
  unless (← withReducible (isDefEq α (mkConst ``Nat))) do return .continue
  let f := e.getArg! 3
  let a := e.getArg! 4
  let b := e.getArg! 5
  let x := e.appArg!
  match ← decideNatKey x a with
  | some (.inl _) =>
    let pf ← mkAppM ``upd_same #[f, a, b]
    return .visit { expr := b, proof? := some pf }
  | some (.inr hne) =>
    let pf ← mkAppM ``upd_ne #[f, a, b, x, hne]
    return .visit { expr := mkApp f x, proof? := some pf }
  | none => return .continue

/-- Decide `n ≤ b` for keys `t + j`, `t + k` (or literals), with a proof of
`n ≤ b` (`Sum.inl`) or of `b < n` (`Sum.inr`) whose type is literally that. -/
def decideNatLeSyn (n b : Expr) : MetaM (Option (Expr ⊕ Expr)) := do
  -- `b = t + k` from an older range below `n = u + j`: `b < n`
  let asOff (k : Key) : Option (Expr × Nat × Expr) := match k with
    | .off t k kE => some (t, k, kE)
    | .atom t => some (t, 0, mkNatLit 0)
    | .lit _ => none
  if let (some (u, j, jE), some (t, k, kE)) := (asOff (← toKey n), asOff (← toKey b)) then
    if !(← sameBase t u) then
      if let some (h, cE) ← findOffsetLe t k u then
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, cE])
        let p := mkAppN (mkConst ``nat_offset_lt_offset_of_le) #[t, u, kE, cE, jE, h, hk]
        return some (.inr (← mkExpectedTypeHint p (← mkAppM ``LT.lt #[b, n])))
  let offs (e : Expr) : MetaM (Option (Expr × Nat × Expr)) := do
    match ← toKey e with
    | .off t k kE => return some (t, k, kE)
    | .atom t => return some (t, 0, mkNatLit 0)
    | .lit _ => return none
  match ← toKey n, ← toKey b with
  | .lit kn, .lit kb =>
    if kn ≤ kb then return some (.inl (← mkDecideProof (← mkAppM ``LE.le #[n, b])))
    else return some (.inr (← mkDecideProof (← mkAppM ``LT.lt #[b, n])))
  | .atom t, .atom bb =>
    -- `b < t`: below the range
    if !(← sameBase t bb) then
      if let some h ← findLtHyp bb t then return some (.inr h)
    if ← sameBase t bb then
      return some (.inl (← mkAppM ``Nat.le_refl #[t]))
    return none
  | .off t k kE, .atom bb =>
    -- `b < t` gives `b < t + k`
    if let some h ← findLtHyp bb t then
      return some (.inr (mkApp4 (mkConst ``nat_lt_offset_of_lt) bb t kE h))
    let some (t', kn, knE) ← offs n | return none
    let some (u, kb, kbE) ← offs b | return none
    unless ← sameBase t' u do return none
    if kn ≤ kb then
      let h ← mkDecideProof (← mkAppM ``LE.le #[knE, kbE])
      return some (.inl (← mkExpectedTypeHint (← mkAppM ``Nat.add_le_add_left #[h, t']) (← mkAppM ``LE.le #[n, b])))
    else
      let h ← mkDecideProof (← mkAppM ``LT.lt #[kbE, knE])
      return some (.inr (← mkExpectedTypeHint (← mkAppM ``Nat.add_lt_add_left #[h, t']) (← mkAppM ``LT.lt #[b, n])))
  | _, _ =>
    let some (t, kn, knE) ← offs n | return none
    let some (u, kb, kbE) ← offs b | return none
    unless ← sameBase t u do return none
    -- `t + kn ≤ t + kb` or `t + kb < t + kn`, stated on the keys themselves
    if kn ≤ kb then
      let h ← mkDecideProof (← mkAppM ``LE.le #[knE, kbE])
      let p ← mkAppM ``Nat.add_le_add_left #[h, t]
      return some (.inl (← mkExpectedTypeHint p (← mkAppM ``LE.le #[n, b])))
    else
      let h ← mkDecideProof (← mkAppM ``LT.lt #[kbE, knE])
      let p ← mkAppM ``Nat.add_lt_add_left #[h, t]
      return some (.inr (← mkExpectedTypeHint p (← mkAppM ``LT.lt #[b, n])))

/-- Decide `n ≤ b`: syntactically when possible, else by `omega` over the
hypotheses. -/
def decideNatLe (n b : Expr) : MetaM (Option (Expr ⊕ Expr)) := do
  match ← decideNatLeSyn n b with
  | some r => return some r
  | none =>
    if let some h ← omegaProof? (← mkAppM ``LT.lt #[b, n]) then return some (.inr h)
    if let some h ← omegaProof? (← mkAppM ``LE.le #[n, b]) then return some (.inl h)
    return none

/-- Evaluate `killRange lo hi bs b` when the position of `b` can be decided. -/
simproc_decl reduceKillRange (killRange _ _ _ _) := fun e => do
  unless e.isAppOfArity ``killRange 4 do return .continue
  let lo := e.getArg! 0
  let hi := e.getArg! 1
  let bs := e.getArg! 2
  let b := e.getArg! 3
  -- b < lo ?
  match ← decideNatLe lo b with
  | some (.inr hlt) =>
    let pf ← mkAppM ``killRange_lt #[lo, hi, bs, b, hlt]
    return .visit { expr := mkApp bs b, proof? := some pf }
  | some (.inl hle) =>
    match ← decideNatLe hi b with
    | some (.inl hge) =>
      let pf ← mkAppM ``killRange_ge #[lo, hi, bs, b, hge]
      return .visit { expr := mkApp bs b, proof? := some pf }
    | some (.inr hlt) =>
      let pf ← mkAppM ``killRange_in #[lo, hi, bs, b, hle, hlt]
      let some (_, _, rhs) := (← inferType pf).eq? | return .continue
      return .visit { expr := rhs, proof? := some pf }
    | none => return .continue
  | none => return .continue

/-! ### Small memory terms

A region exit leaves `killRange lo hi F` in the state, and a slot written
twice keeps both writes; every later lookup and frame closer passes through
them. `normKillRange` pushes an exit into the writes of `F`
(`killRange_upd_*`: a write to a dead stack block is forgotten, other writes
stay) and removes it below a well-formed memory (`killRange_base`);
`collapseUpd` removes a forgotten write to a block that is not there
(`upd_none_eq`) and a write that a later write to the same block overwrites
(`upd_upd_same`, `upd_comm`). Keys are compared syntactically (literals,
offsets of one base), so both are cheap enough to run at every step. -/

/-- The memory whose blocks are `bs`, with a hypothesis `Mem.WF m`. -/
def findWFFor? (bs : Expr) : MetaM (Option (Expr × Expr)) := do
  let m? : Option Expr := if bs.isAppOfArity ``CIR.Mem.blocks 1 then some (bs.getArg! 0)
    else match bs with
      | .proj ``CIR.Mem 0 m => some m
      | _ => none
  let some m := m? | return none
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``CIR.Mem.WF 1 then
      let a := ty.getArg! 0
      if a == m || (← withReducible (isDefEq a m)) then return some (m, d.toExpr)
  return none

/-- A proof of `k ≠ k'` for keys that differ syntactically: two literals, or
offsets of one base. -/
def keysNe? (k k' : Expr) : MetaM (Option Expr) := do
  let rflF := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.false)
  match ← toKey k, ← toKey k' with
  | .lit a, .lit b =>
    if a == b then return none
    return some (mkApp3 (mkConst ``Nat.ne_of_beq_eq_false) k k' rflF)
  | .off t a aE, .off u b bE =>
    if a == b || !(← sameBase t u) then return none
    return some (mkApp4 (mkConst ``CIR.add_ne_add_of_beq) t aE bE rflF)
  | .atom t, .off u b bE =>
    if b == 0 || !(← sameBase t u) then return none
    return some (mkApp3 (mkConst ``CIR.self_ne_add_of_beq) t bE rflF)
  | .off t a aE, .atom u =>
    if a == 0 || !(← sameBase t u) then return none
    return some (mkApp3 (mkConst ``CIR.add_ne_self_of_beq) t aE rflF)
  | _, _ => return none

/-- One write under a scope exit: `killRange lo hi (upd G k v) = upd (killRange
lo hi G) k v'` (the value `v'` and the proof), or `none`. -/
def stepKillRangeUpd (lo hi G k v : Expr) : MetaM (Option (Expr × Expr)) := do
  let v' ← whnfR v
  if v'.isAppOfArity ``Option.none 1 then
    return some (v, ← mkAppOptM ``CIR.killRange_upd_none #[some lo, some hi, some k, some G])
  unless v'.isAppOfArity ``Option.some 2 do return none
  let blk ← whnfR (v'.getArg! 1)
  unless blk.isAppOfArity ``CIR.MemBlock.mk 4 do return none
  let kd := blk.getArg! 0
  let a := blk.getArg! 1
  let t := blk.getArg! 2
  let x := blk.getArg! 3
  if kd.isConstOf ``CIR.BlockKind.stack then
    match ← decideNatLeSyn lo k with
    | some (.inr h1) =>
      return some (v, ← mkAppOptM ``CIR.killRange_upd_old #[some lo, some hi, some k, some G, some v, some h1])
    | some (.inl h1) =>
      match ← decideNatLeSyn hi k with
      | some (.inr h2) =>
        let none' := mkApp (mkConst ``Option.none [levelZero]) (mkConst ``CIR.MemBlock)
        return some (none', ← mkAppOptM ``CIR.killRange_upd_stack
          #[some lo, some hi, some k, some G, some a, some t, some x, some h1, some h2])
      | some (.inl h2) =>
        return some (v, ← mkAppOptM ``CIR.killRange_upd_hi #[some lo, some hi, some k, some G, some v, some h2])
      | none => return none
    | none => return none
  else if kd.isConst then
    let hk ← mkDecideProof (mkNot (← mkEq kd (mkConst ``CIR.BlockKind.stack)))
    return some (v, ← mkAppOptM ``CIR.killRange_upd_keep
      #[some lo, some hi, some k, some G, some kd, some a, some t, some x, some hk])
  else return none

/-- `killRange lo hi F` normalized (the result and a proof of the equation), or
`none` when nothing changes. -/
partial def normKR (lo hi F : Expr) : MetaM (Option (Expr × Expr)) := do
  let F ← instantiateMVars F
  if F.isAppOfArity ``CIR.upd 6 then
    let G := F.getArg! 3
    let k := F.getArg! 4
    let v := F.getArg! 5
    let some (v', pStep) ← stepKillRangeUpd lo hi G k v | return none
    let krG := mkApp3 (mkConst ``CIR.killRange) lo hi G
    let (G', pG) ← match ← normKR lo hi G with
      | some r => pure r
      | none => pure (krG, ← mkEqRefl krG)
    let fn := F.getAppFn
    let lam := Lean.mkLambda `g .default (← inferType G)
      (mkAppN fn #[F.getArg! 0, F.getArg! 1, F.getArg! 2, .bvar 0, k, v'])
    return some (mkAppN fn #[F.getArg! 0, F.getArg! 1, F.getArg! 2, G', k, v'],
      ← mkEqTrans pStep (← mkCongrArg lam pG))
  let some (m, hwf) ← findWFFor? F | return none
  match ← decideNatLeSyn (← mkAppM ``CIR.Mem.next #[m]) lo with
  | some (.inl hle) =>
    let pf ← mkAppOptM ``CIR.killRange_base #[some m, some lo, some hi, some hwf, some hle]
    return some (F, ← mkExpectedTypeHint pf (← mkEq (mkApp3 (mkConst ``CIR.killRange) lo hi F) F))
  | _ => return none

simproc_decl normKillRange (killRange _ _ _) := fun e => do
  unless e.isAppOfArity ``CIR.killRange 3 do return .continue
  unless (← getOptions).getBool `cir.normMem true do return .continue
  let some (res, pf) ← normKR (e.getArg! 0) (e.getArg! 1) (e.getArg! 2) | return .continue
  return .visit { expr := res, proof? := some pf }

/-- A proof of `F k = none`: no write to `k` in `F` (the other keys differ
syntactically) down to a well-formed memory whose `next` is at most `k`. -/
partial def lookupNone? (F k : Expr) (fuel : Nat := 64) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let F ← instantiateMVars F
  if F.isAppOfArity ``CIR.upd 6 then
    let G := F.getArg! 3
    let k' := F.getArg! 4
    let v := F.getArg! 5
    if k' == k then
      unless (← whnfR v).isAppOfArity ``Option.none 1 do return none
      return some (← mkAppM ``CIR.upd_apply_same #[G, k, v])
    let some hne ← keysNe? k k' | return none
    let some pG ← lookupNone? G k (fuel - 1) | return none
    let p1 ← mkAppOptM ``CIR.upd_apply_ne #[none, none, none, some G, some k, some k', some v, some hne]
    return some (← mkEqTrans p1 pG)
  let some (m, hwf) ← findWFFor? F | return none
  match ← decideNatLeSyn (← mkAppM ``CIR.Mem.next #[m]) k with
  | some (.inl hle) => return some (mkApp2 hwf k hle)
  | _ => return none

/-- `upd F k y = upd F' k y` where `F'` is `F` without its latest write to
`k` (found below writes to keys that differ syntactically), or `none`. -/
partial def dropShadowed? (F k y : Expr) (fuel : Nat := 64) : MetaM (Option (Expr × Expr)) := do
  if fuel == 0 then return none
  let F ← instantiateMVars F
  unless F.isAppOfArity ``CIR.upd 6 do return none
  let G := F.getArg! 3
  let k1 := F.getArg! 4
  let v1 := F.getArg! 5
  if k1 == k then
    return some (G, ← mkAppM ``CIR.upd_upd_same #[G, k, v1, y])
  let some hne ← keysNe? k k1 | return none
  let some (G', pG) ← dropShadowed? G k y (fuel - 1) | return none
  -- upd (upd G k1 v1) k y = upd (upd G k y) k1 v1 = upd (upd G' k y) k1 v1
  --   = upd (upd G' k1 v1) k y
  let fn := F.getAppFn
  let α := F.getArg! 0
  let β := F.getArg! 1
  let inst := F.getArg! 2
  let mk (f a b : Expr) := mkAppN fn #[α, β, inst, f, a, b]
  let p1 ← mkAppOptM ``CIR.upd_comm #[none, none, none, some G, some k, some k1, some v1, some y, some hne]
  let lam := Lean.mkLambda `g .default (← inferType G) (mk (.bvar 0) k1 v1)
  let p2 ← mkCongrArg lam pG
  let hne' ← mkAppM ``Ne.symm #[hne]
  let p3 ← mkAppOptM ``CIR.upd_comm #[none, none, none, some G', some k1, some k, some y, some v1, some hne']
  let G'' := mk G' k1 v1
  return some (G'', ← mkEqTrans p1 (← mkEqTrans p2 p3))

simproc_decl collapseUpd (upd _ _ _) := fun e => do
  unless e.isAppOfArity ``CIR.upd 6 do return .continue
  unless (← getOptions).getBool `cir.normMem true do return .continue
  unless (e.getArg! 0).isConstOf ``Nat do return .continue
  let F := e.getArg! 3
  let k := e.getArg! 4
  let v := e.getArg! 5
  if (e.getArg! 1) == mkApp (mkConst ``Option [levelZero]) (mkConst ``CIR.MemBlock) &&
      (← whnfR v).isAppOfArity ``Option.none 1 then
    if let some h ← lookupNone? F k then
      return .visit { expr := F, proof? := some (← mkAppOptM ``CIR.upd_none_eq #[some F, some k, some h]) }
  let some (F', pf) ← dropShadowed? F k v | return .continue
  return .visit { expr := mkAppN e.getAppFn #[e.getArg! 0, e.getArg! 1, e.getArg! 2, F', k, v], proof? := some pf }

/-- Evaluate a lookup in the module context with a literal key
(`ctx.record? "Counter"`, `ctx.gaddr "g"`, `M.findFunc? "f"`, ...) by
computation; the result is checked by the kernel (`rfl`). This keeps the
module definition out of the goal. -/
def evalCtxLookup (e : Expr) : SimpM Simp.Step := do
  -- names compared natively (see `CIR.Tactic.Lookup`)
  if let some v ← lookupValue? e then
    let v ← if v.isAppOfArity ``Option.some 2 && v.appArg!.getAppFn.isConst then do
        let x ← whnfD v.appArg!
        pure (mkApp v.appFn! x)
      else pure v
    let pf ← mkExpectedTypeHint (← mkEqRefl v) (← mkEq e v)
    return .done { expr := v, proof? := some pf }
  let r ← whnfD e
  -- expose the declaration (a structure literal) instead of its constant name
  let r ← if r.isAppOfArity ``Option.some 2 && r.appArg!.getAppFn.isConst then do
      let x ← whnfD r.appArg!
      pure (mkApp r.appFn! x)
    else pure r
  -- accept only fully evaluated results
  let ok := r.isAppOfArity ``Option.none 1 ||
    (r.isAppOfArity ``Option.some 2 && !(r.appArg!.hasLooseBVars))
  unless ok do return .continue
  if r == e then return .continue
  let pf ← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)
  return .done { expr := r, proof? := some pf }

simproc_decl reduceCtxRecord (Ctx.record? _ _) := fun e => do
  unless e.isAppOfArity ``Ctx.record? 2 do return .continue
  unless (e.getArg! 1).isStringLit do return .continue
  evalCtxLookup e

simproc_decl reduceCtxGaddr (Ctx.gaddr _ _) := fun e => do
  unless e.isAppOfArity ``Ctx.gaddr 2 do return .continue
  unless (e.getArg! 1).isStringLit do return .continue
  evalCtxLookup e

simproc_decl reduceFindRecord (Module.findRecord? _ _) := fun e => do
  unless e.isAppOfArity ``Module.findRecord? 2 do return .continue
  unless (e.getArg! 1).isStringLit do return .continue
  evalCtxLookup e

/-- Evaluate a closed term (no free or meta variables) by full reduction,
when the result is a closed constructor term; checked by the kernel (`rfl`).
Used for class layout computations (`Ctx.basePath`, ...), whose arguments are
literals taken from the program. -/
def evalClosed (e : Expr) : SimpM Simp.Step := do
  if e.hasFVar || e.hasMVar then return .continue
  let r ← withTheReader Core.Context (fun c => { c with maxRecDepth := 20000 }) <|
    withTransparency .all <| Meta.reduce e (skipTypes := true)
  -- accept only data built from constructors and literals
  let ok := !(r.find? fun x => match x with
    | .const n _ => !(n.isPrefixOf ``Option.some || n == ``Option.some || n == ``Option.none ||
        n == ``List.cons || n == ``List.nil || n == ``Prod.mk || n == ``Nat || n == ``String ||
        n == ``Bool.true || n == ``Bool.false || n == ``List || n == ``Prod || n == ``Bool ||
        n == ``Option)
    | .fvar _ | .mvar _ | .lam .. | .forallE .. | .letE .. => true
    | _ => false).isSome
  unless ok do return .continue
  if r == e then return .continue
  let pf ← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)
  return .done { expr := r, proof? := some pf }

simproc_decl reduceBasePath (Ctx.basePath _ _ _ _ _) := evalClosed
simproc_decl reduceVptrPath (Ctx.vptrPath _ _ _) := evalClosed

simproc_decl reduceFindGlobal (Module.findGlobal? _ _) := fun e => do
  unless e.isAppOfArity ``Module.findGlobal? 2 do return .continue
  unless (e.getArg! 1).isStringLit do return .continue
  evalCtxLookup e

simproc_decl reduceFindFunc (Module.findFunc? _ _) := fun e => do
  unless e.isAppOfArity ``Module.findFunc? 2 do return .continue
  unless (e.getArg! 1).isStringLit do return .continue
  evalCtxLookup e

/-- The pointer size of a closed module (`ctx.mod` of a generated context):
its literal (`Ctx.sizeAlign` reads it on pointers, e.g. in the heap typing of
a cast); checked by the kernel (`rfl`). -/
simproc_decl reducePtrBytes (Module.ptrBytes _) := fun e => do
  unless e.isAppOfArity ``Module.ptrBytes 1 do return .continue
  if e.hasFVar || e.hasMVar then return .continue
  let r ← whnfD e
  let some n := r.rawNatLit? <|> r.nat? | return .continue
  let v := mkNatLit n
  let pf ← mkExpectedTypeHint (← mkEqRefl v) (← mkEq e v)
  return .done { expr := v, proof? := some pf }

/-- A chunk of a long operation list (`fn_x_opsK`, emitted by cir2lean as an
`abbrev`). -/
def isOpsChunk (n : Name) : Bool :=
  match n with
  | .str _ s =>
    match s.splitOn "_ops" with
    | [_, k] => !k.isEmpty && k.all Char.isDigit
    | _ => false
  | _ => false

/-- `e` with its operation-list chunks replaced by their definitions. -/
def unfoldOpsChunks (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e (pre := fun x => do
    if let .const n us := x then
      if isOpsChunk n then
        if let some (.defnInfo d) := env.find? n then
          return .visit (d.value.instantiateLevelParams d.levelParams us)
    return .continue)

/-- `switchStart`, `labelBlock?` and `++` scan operation lists: unfold the
chunks they are applied to (cir2lean splits long lists into `abbrev`s). -/
def chunkStep (e : Expr) : SimpM Simp.DStep := do
  let e' ← unfoldOpsChunks e
  if e' == e then return .continue
  return .visit e'

dsimproc_decl reduceSwitchChunks (switchStart _ _) := chunkStep
dsimproc_decl reduceAppendChunks ((_ : List Op) ++ _) := chunkStep

end Tactic
end CIR

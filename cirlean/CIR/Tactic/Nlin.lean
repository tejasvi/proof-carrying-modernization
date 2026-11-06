import Lean
import CIR.Tactic.Simprocs

/-!
  `cir_nlin`: bounds for non-linear products, so that `omega` can close
  overflow conditions such as `x * x ≤ 2147483647` under `0 ≤ x ≤ 1023`.

  For every product `a * b` of two non-numeral integer terms in the goal, the
  tightest bounds `la ≤ a ≤ ua`, `lb ≤ b ≤ ub` among a ladder of constants
  (±2^k, ±(2^k - 1), the literals of the context) are found by `omega`, and
  the corner bounds of the product are added as hypotheses
  (`mul_le_of_bounds`, `le_mul_of_bounds`). `omega` treats the product as an
  atom.
-/

namespace CIR

theorem mul_le_of_bounds {a b la ua lb ub : Int} (h1 : la ≤ a) (h2 : a ≤ ua) (h3 : lb ≤ b) (h4 : b ≤ ub) :
    a * b ≤ max (max (la * lb) (la * ub)) (max (ua * lb) (ua * ub)) := by
  rcases Int.le_total 0 b with hb | hb
  · have e1 : a * b ≤ ua * b := Int.mul_le_mul_of_nonneg_right h2 hb
    rcases Int.le_total 0 ua with hu | hu
    · have e2 : ua * b ≤ ua * ub := Int.mul_le_mul_of_nonneg_left h4 hu
      omega
    · have e2 : ua * b ≤ ua * lb := Int.mul_le_mul_of_nonpos_left hu h3
      omega
  · have e1 : a * b ≤ la * b := Int.mul_le_mul_of_nonpos_right h1 hb
    rcases Int.le_total 0 la with hl | hl
    · have e2 : la * b ≤ la * ub := Int.mul_le_mul_of_nonneg_left h4 hl
      omega
    · have e2 : la * b ≤ la * lb := Int.mul_le_mul_of_nonpos_left hl h3
      omega

theorem le_mul_of_bounds {a b la ua lb ub : Int} (h1 : la ≤ a) (h2 : a ≤ ua) (h3 : lb ≤ b) (h4 : b ≤ ub) :
    min (min (la * lb) (la * ub)) (min (ua * lb) (ua * ub)) ≤ a * b := by
  rcases Int.le_total 0 b with hb | hb
  · have e1 : la * b ≤ a * b := Int.mul_le_mul_of_nonneg_right h1 hb
    rcases Int.le_total 0 la with hl | hl
    · have e2 : la * lb ≤ la * b := Int.mul_le_mul_of_nonneg_left h3 hl
      omega
    · have e2 : la * ub ≤ la * b := Int.mul_le_mul_of_nonpos_left hl h4
      omega
  · have e1 : ua * b ≤ a * b := Int.mul_le_mul_of_nonpos_right h2 hb
    rcases Int.le_total 0 ua with hu | hu
    · have e2 : ua * lb ≤ ua * b := Int.mul_le_mul_of_nonneg_left h3 hu
      omega
    · have e2 : ua * ub ≤ ua * b := Int.mul_le_mul_of_nonpos_left hu h4
      omega

open Lean Meta Elab Tactic

/-- Products `a * b` over `Int` in `e` whose factors are both non-numerals. -/
partial def intProducts (e : Expr) (acc : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
  let mut acc := acc
  if e.isAppOfArity ``HMul.hMul 6 && e.getArg! 0 == mkConst ``Int then
    let a := e.getArg! 4
    let b := e.getArg! 5
    if (← getIntValue? a).isNone && (← getIntValue? b).isNone && !acc.contains (a, b) then
      acc := acc.push (a, b)
  for x in e.getAppArgs do
    acc ← intProducts x acc
  return acc

/-- Integer literals in `e`. -/
partial def intLits (e : Expr) (acc : Array Int) : MetaM (Array Int) := do
  if let some v ← getIntValue? e then
    return if acc.contains v then acc else acc.push v
  let mut acc := acc
  for x in e.getAppArgs do
    acc ← intLits x acc
  return acc

/-- Candidate bounds: ±2^k, ±(2^k - 1) for k ≤ 64, and the literals ± 1. -/
def boundCands (lits : Array Int) : Array Int := Id.run do
  let mut cs : Array Int := #[0]
  for k in [0:65] do
    let p : Int := 2 ^ k
    cs := cs ++ #[p, p - 1, -p, -(p - 1)]
  for l in lits do
    cs := cs ++ #[l - 1, l, l + 1]
  return (cs.qsort (· < ·)).toList.eraseDups.toArray

/-- The smallest candidate `c` with `t ≤ c` (`upper`) or the largest with
`c ≤ t`, and its proof, by binary search with `omega` (`cs` is sorted). -/
def findBound (t : Expr) (cs : Array Int) (upper : Bool) : MetaM (Option (Int × Expr)) := do
  let fact (c : Int) : MetaM Expr :=
    if upper then mkAppM ``LE.le #[t, toExpr c] else mkAppM ``LE.le #[toExpr c, t]
  let n := cs.size
  if upper then
    -- provable from some index on; cs[hi] is provable
    let some p ← omegaProof? (← fact cs[n - 1]!) | return none
    let mut best := (cs[n - 1]!, p)
    let mut lo := 0
    let mut hi := n - 1
    while lo < hi do
      let mid := (lo + hi) / 2
      match ← omegaProof? (← fact cs[mid]!) with
      | some p => best := (cs[mid]!, p); hi := mid
      | none => lo := mid + 1
    return some best
  else
    -- provable up to some index; cs[lo] is provable
    let some p ← omegaProof? (← fact cs[0]!) | return none
    let mut best := (cs[0]!, p)
    let mut lo := 0
    let mut hi := n - 1
    while lo < hi do
      let mid := (lo + hi + 1) / 2
      match ← omegaProof? (← fact cs[mid]!) with
      | some p => best := (cs[mid]!, p); lo := mid
      | none => hi := mid - 1
    return some best

/-- Add corner bounds for the non-linear products of the main goal (at most
`max` products). Fails if there are none. -/
elab "cir_nlin" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let mut prods ← intProducts tgt #[]
    -- products in the hypotheses too (e.g. a callee's postcondition `2 * s = n * (n + 1)`)
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        if (← isProp d.type) then prods ← intProducts (← instantiateMVars d.type) prods
    if prods.isEmpty then throwError "cir_nlin: no non-linear product"
    let mut lits ← intLits tgt #[]
    for d in (← getLCtx) do
      unless d.isImplementationDetail do
        if (← isProp d.type) then lits ← intLits (← instantiateMVars d.type) lits
    let cs := boundCands lits
    let mut g := g
    for (a, b) in prods.toList.take 4 do
      let some (_, h1) ← findBound a cs false | continue
      let some (_, h2) ← findBound a cs true | continue
      let some (_, h3) ← findBound b cs false | continue
      let some (_, h4) ← findBound b cs true | continue
      for thm in [``mul_le_of_bounds, ``le_mul_of_bounds] do
        let pf ← mkAppM thm #[h1, h2, h3, h4]
        let ty ← instantiateMVars (← inferType pf)
        let (_, g') ← (← g.assert `cir_nl ty pf).intro1P
        g := g'
    replaceMainGoal [g]

end CIR

/-
# Value ranges: discharging truncation automatically

Symbolic execution produces `Sem.fitNum c f v` at every store (high-order truncation and the
SIZE ERROR test) and `decodeNum c f (encodeNum c f v)` at every read after a write.  When `v`
provably fits the item, both are the identity:

  `Sem.fitNum c f v = (false, v)`,   `decodeNum c f (encodeNum c f v) = some v`.

The simprocs `reduceFitNumRange` / `reduceDecodeEncodeRange` prove the premise `f.Holds c v`
by interval arithmetic over the structure of `v`: literals, atoms with range hypotheses in
the context (`cobol_ranges` adds them for every input field), `+`, `-`, `*`, `if`, and stored
values `(Sem.fitNum c f x).2` (always within the capacity of `f`).  Every step is a lemma
application with literal side conditions checked by `decide`, so the kernel re-checks the
whole argument.

Effect: values of merged `IF`s stay small (`if c then v + 1 else v`, no truncation wrapper),
SIZE ERROR branches that cannot be taken disappear during symbolic execution, and the COBOL
side becomes syntactically the arithmetic of a faithful rewrite, so equivalence is closed by
congruence instead of case splits.

Conditions of enclosing `IF`s are not used (path-insensitive): a store that only fits because
of a test (e.g. `IF X < 100 ADD 1 TO X`) keeps its `fitNum`, which `cobol_grind` handles.
-/
import Cobol.Logic.Basic
import Cobol.Logic.Attr

namespace Cobol

/-- `lo ≤ x ≤ hi`. -/
def InRange (lo hi x : Int) : Prop := lo ≤ x ∧ x ≤ hi

namespace InRange

theorem lit (n : Int) : InRange n n n := ⟨Int.le_refl n, Int.le_refl n⟩

theorem weaken {lo hi lo' hi' x : Int} (h : InRange lo hi x) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
    InRange lo' hi' x := ⟨Int.le_trans h1 h.1, Int.le_trans h.2 h2⟩

theorem add {la ha lb hb a b : Int} (h1 : InRange la ha a) (h2 : InRange lb hb b) :
    InRange (la + lb) (ha + hb) (a + b) := by
  unfold InRange at *; omega

theorem sub {la ha lb hb a b : Int} (h1 : InRange la ha a) (h2 : InRange lb hb b) :
    InRange (la - hb) (ha - lb) (a - b) := by
  unfold InRange at *; omega

theorem neg {la ha a : Int} (h : InRange la ha a) : InRange (-ha) (-la) (-a) := by
  unfold InRange at *; omega

theorem mul_nonneg_right {la ha a k : Int} (h : InRange la ha a) (hk : 0 ≤ k) :
    InRange (la * k) (ha * k) (a * k) :=
  ⟨Int.mul_le_mul_of_nonneg_right h.1 hk, Int.mul_le_mul_of_nonneg_right h.2 hk⟩

theorem mul_nonpos_right {la ha a k : Int} (h : InRange la ha a) (hk : k ≤ 0) :
    InRange (ha * k) (la * k) (a * k) :=
  ⟨Int.mul_le_mul_of_nonpos_right h.2 hk, Int.mul_le_mul_of_nonpos_right h.1 hk⟩

theorem mul_nonneg_left {la ha a k : Int} (h : InRange la ha a) (hk : 0 ≤ k) :
    InRange (k * la) (k * ha) (k * a) := by
  rw [Int.mul_comm k la, Int.mul_comm k ha, Int.mul_comm k a]; exact mul_nonneg_right h hk

theorem mul_nonpos_left {la ha a k : Int} (h : InRange la ha a) (hk : k ≤ 0) :
    InRange (k * ha) (k * la) (k * a) := by
  rw [Int.mul_comm k la, Int.mul_comm k ha, Int.mul_comm k a]; exact mul_nonpos_right h hk

/-- Product of two bounded values: `|a| ≤ A`, `|b| ≤ B` give `|a * b| ≤ A * B`. -/
theorem mul {la ha lb hb a b A B : Int} (h1 : InRange la ha a) (h2 : InRange lb hb b)
    (hA : -A ≤ la ∧ ha ≤ A) (hB : -B ≤ lb ∧ hb ≤ B) : InRange (-(A * B)) (A * B) (a * b) := by
  unfold InRange at *
  have hA0 : 0 ≤ A := by omega
  have hB0 : 0 ≤ B := by omega
  have ha' : a.natAbs ≤ A.toNat := by omega
  have hb' : b.natAbs ≤ B.toNat := by omega
  have hm := Nat.mul_le_mul ha' hb'
  rw [← Int.natAbs_mul] at hm
  have e : ((A.toNat * B.toNat : Nat) : Int) = A * B := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg hA0, Int.toNat_of_nonneg hB0]
  omega

theorem ite {la ha lb hb a b lo hi : Int} (c : Prop) [Decidable c] (h1 : InRange la ha a)
    (h2 : InRange lb hb b) (hlo : lo ≤ la ∧ lo ≤ lb) (hhi : ha ≤ hi ∧ hb ≤ hi) :
    InRange lo hi (if c then a else b) := by
  split
  · exact weaken h1 hlo.1 hhi.1
  · exact weaken h2 hlo.2 hhi.2

theorem of_natAbs_lt {x : Int} {K : Nat} (h : x.natAbs < K) :
    InRange (-(K : Int) + 1) ((K : Int) - 1) x := by
  unfold InRange; omega

theorem refine_lo {lo hi l x : Int} (h : InRange lo hi x) (h' : l ≤ x) (_hl : lo ≤ l) :
    InRange l hi x := ⟨h', h.2⟩

theorem refine_hi {lo hi u x : Int} (h : InRange lo hi x) (h' : x ≤ u) (_hu : u ≤ hi) :
    InRange lo u x := ⟨h.1, h'⟩

theorem natCast_lt {n K : Nat} (h : n < K) : InRange 0 ((K : Int) - 1) (n : Int) := by
  unfold InRange; omega

theorem ediv {lo hi n d : Int} (h : InRange lo hi n) (hd : 0 < d) :
    InRange (lo / d) (hi / d) (n / d) :=
  ⟨Int.ediv_le_ediv hd h.1, Int.ediv_le_ediv hd h.2⟩

theorem natAbs {lo hi n : Int} (h : InRange lo hi n) (A : Int) (hA : -A ≤ lo ∧ hi ≤ A) :
    InRange 0 A (n.natAbs : Int) := by
  unfold InRange at *; omega

theorem divRound {lo hi n d : Int} (m : RoundingMode) (h : InRange lo hi n) (hd : 0 < d) :
    InRange (Cobol.divRound m lo d) (Cobol.divRound m hi d) (Cobol.divRound m n d) :=
  ⟨divRound_mono m hd h.1, divRound_mono m hd h.2⟩

/-- A value satisfying `f.Holds c` lies between the item's smallest and largest values. -/
theorem of_holds_dec {c : Config} {f : NumFmt} {x : Int} (h : f.Holds c x)
    (hb : f.fullBinary c = false) :
    InRange (-((10 : Int) ^ f.digits) + 1) ((10 : Int) ^ f.digits - 1) x := by
  unfold NumFmt.Holds at h
  simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
  have e : ((10 ^ f.digits : Nat) : Int) = (10 : Int) ^ f.digits := by simp
  unfold InRange; omega

theorem of_holds_bin {c : Config} {f : NumFmt} {x : Int} (h : f.Holds c x)
    (hb : f.fullBinary c = true) :
    InRange (-(binHalf (c.binBytes f.digits) : Int)) ((binMod (c.binBytes f.digits) : Int) - 1) x := by
  unfold NumFmt.Holds at h
  simp only [hb, ↓reduceIte] at h
  have hpos := binBytes_pos c f.digits
  have h2 : binMod (c.binBytes f.digits) = 2 * binHalf (c.binBytes f.digits) :=
    binMod_eq_two_mul hpos
  unfold InRange
  split at h <;> omega

/-- `f.Holds c` is an interval condition: it holds between two values where it holds. -/
theorem holds {c : Config} {f : NumFmt} {lo hi x : Int} (h : InRange lo hi x)
    (h1 : f.Holds c lo) (h2 : f.Holds c hi) : f.Holds c x := by
  unfold InRange at h
  unfold NumFmt.Holds at *
  split
  · rename_i hb
    simp only [hb, ↓reduceIte] at h1 h2
    split <;> rename_i hs <;> simp only [hs, ↓reduceIte, Bool.false_eq_true] at h1 h2 <;> omega
  · rename_i hb
    simp only [hb, ↓reduceIte, Bool.false_eq_true] at h1 h2
    refine ⟨by omega, fun hs => by have := h1.2 hs; omega⟩

end InRange

/-- A value that fits is stored unchanged, without size error. -/
theorem fitNum_of_holds {c : Config} {f : NumFmt} {v : Int} (h : f.Holds c v) :
    Sem.fitNum c f v = (false, v) := by
  unfold NumFmt.Holds at h
  unfold Sem.fitNum
  cases hb : f.fullBinary c <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · cases hs : f.signed <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at h ⊢
    · have h0 : 0 ≤ v := h.2 (by simp)
      have e : ((v.natAbs : Nat) : Int) = v := Int.natAbs_of_nonneg h0
      rw [e]; unfold Sem.fitDec; simp only [h.1, ↓reduceIte]
    · unfold Sem.fitDec; simp only [h.1, ↓reduceIte]
  · unfold Sem.fitBin Sem.inBinRange
    cases hs : f.signed <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at h ⊢
    · have e : ((v.natAbs : Nat) : Int) = v := Int.natAbs_of_nonneg h.1
      rw [e]; simp [h.1, h.2]
    · simp [h.1, h.2]

/-- The value read back after storing a value that fits. -/
theorem decodeNum_encodeNum_of_holds {c : Config} {f : NumFmt} {v : Int} (hd : 0 < f.digits)
    (hd18 : f.digits ≤ 18) (h : f.Holds c v) : decodeNum c f (encodeNum c f v) = some v :=
  decodeNum_encodeNum c f v hd hd18 h

/-! ## Interval computation -/

open Lean Meta Simp

/-- Bounds `lo ≤ x ≤ hi` with a proof of `InRange lo hi x` (`lo`, `hi` as literals). -/
structure Range where
  lo : Int
  hi : Int
  proof : Lean.Expr
  deriving Inhabited

/-- `decide p` for a closed proposition, by evaluation; the proof is checked by the kernel. -/
def decideClosed? (p : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if p.hasFVar || p.hasMVar then return none
  let d ← mkDecide p
  let ok ← try unsafe evalExpr Bool (mkConst ``Bool) d catch _ => pure false
  if ok then return some (← mkDecideProof p) else return none

private def leProof (a b : Int) : MetaM Lean.Expr := do
  let some p ← decideClosed? (← mkAppM ``LE.le #[toExpr a, toExpr b])
    | throwError "Bounds: {a} ≤ {b} is false"
  return p

/-- Restate `InRange (lo-expression) (hi-expression) x` with literal bounds `lo`, `hi`. -/
private def normalize (lo hi : Int) (pf : Lean.Expr) : MetaM Range := do
  let ty ← inferType pf
  let_expr InRange loE hiE _ := ty | throwError "Bounds: not an InRange proof"
  let p1 ← mkDecideProof (← mkAppM ``LE.le #[toExpr lo, loE])
  let p2 ← mkDecideProof (← mkAppM ``LE.le #[hiE, toExpr hi])
  return { lo, hi, proof := ← mkAppM ``InRange.weaken #[pf, p1, p2] }

private def intLit? (e : Lean.Expr) : MetaM (Option Int) := do
  if e.hasFVar || e.hasMVar then return none
  getIntValue? e

/-- Range facts of the local context, by atom: `x.natAbs < K`, `l ≤ x`, `x ≤ u`, `x < u`,
`InRange lo hi x`, and conjunctions of those.  Only declarations with index `< maxIdx` are
used: inside simp, hypotheses introduced by congruence lemmas (the conditions of enclosing
`if`s) must not be, since simp caches results across those contexts. -/
partial def collectFacts (maxIdx : Nat) : MetaM (Lean.ExprMap Range) := do
  let mut m : Lean.ExprMap Range := {}
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail || ldecl.index ≥ maxIdx then continue
    m ← addFact m (← instantiateMVars ldecl.type) ldecl.toExpr
  return m
where
  addFact (m : Lean.ExprMap Range) (ty pf : Lean.Expr) : MetaM (Lean.ExprMap Range) := do
    match_expr ty with
    | And a b =>
      let m ← addFact m a (← mkAppM ``And.left #[pf])
      addFact m b (← mkAppM ``And.right #[pf])
    | LT.lt α _ l r =>
      if α.isConstOf ``Nat then
        let some k ← getNatValue? r | return m
        if let some x := l.app1? ``Int.natAbs then
          let r0 ← normalize (-(k : Int) + 1) ((k : Int) - 1) (← mkAppM ``InRange.of_natAbs_lt #[pf])
          return meet m x r0
        else
          -- `n < K` for a natural number: a fact about `(n : Int)`
          let x ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, l]
          let r0 ← normalize 0 ((k : Int) - 1) (← mkAppM ``InRange.natCast_lt #[pf])
          return meet m x r0
      else if α.isConstOf ``Int then
        if let some u ← intLit? r then
          -- x < u  ⇒  x ≤ u - 1
          let h ← mkAppM ``Int.le_sub_one_of_lt #[pf]
          refineHi m l (u - 1) h
        else if let some lv ← intLit? l then
          let h ← mkAppM ``Int.add_one_le_of_lt #[pf]
          refineLo m r (lv + 1) h
        else return m
      else return m
    | LE.le α _ l r =>
      if α.isConstOf ``Int then
        if let some u ← intLit? r then refineHi m l u pf
        else if let some lv ← intLit? l then refineLo m r lv pf
        else return m
      else return m
    | InRange lo hi x =>
      let some l ← intLit? lo | return m
      let some h ← intLit? hi | return m
      return meet m x { lo := l, hi := h, proof := pf }
    | _ => return m
  meet (m : Lean.ExprMap Range) (x : Lean.Expr) (r : Range) : Lean.ExprMap Range :=
    match m.get? x with
    | some old => if r.hi - r.lo < old.hi - old.lo then m.insert x r else m
    | none => m.insert x r
  -- one-sided facts refine an existing two-sided range (applied when encountered in order;
  -- `cobol_ranges` puts the `natAbs` bound before the sign fact)
  refineHi (m : Lean.ExprMap Range) (x : Lean.Expr) (u : Int) (h : Lean.Expr) : MetaM (Lean.ExprMap Range) := do
    let some old := m.get? x | return m
    if u ≥ old.hi then return m
    if u < old.lo then return m
    let pf ← mkAppM ``InRange.refine_hi #[old.proof, h, ← leProof u old.hi]
    return m.insert x { lo := old.lo, hi := u, proof := pf }
  refineLo (m : Lean.ExprMap Range) (x : Lean.Expr) (l : Int) (h : Lean.Expr) : MetaM (Lean.ExprMap Range) := do
    let some old := m.get? x | return m
    if l ≤ old.lo then return m
    if l > old.hi then return m
    let pf ← mkAppM ``InRange.refine_lo #[old.proof, h, ← leProof old.lo l]
    return m.insert x { lo := l, hi := old.hi, proof := pf }

/-- Interval of an integer term, or `none`. -/
partial def bounds (facts : Lean.ExprMap Range) (e : Lean.Expr) :
    StateRefT (Lean.ExprMap (Option Range)) MetaM (Option Range) := do
  if let some r := (← get).get? e then return r
  let r ← go e
  modify (·.insert e r)
  return r
where
  go (e : Lean.Expr) : StateRefT (Lean.ExprMap (Option Range)) MetaM (Option Range) := do
    if let some n ← intLit? e then
      return some { lo := n, hi := n, proof := mkApp (mkConst ``InRange.lit) (toExpr n) }
    if let some r := facts.get? e then return some r
    match_expr e with
    | HAdd.hAdd _ _ _ _ a b =>
      let some ra ← bounds facts a | return none
      let some rb ← bounds facts b | return none
      normalize (ra.lo + rb.lo) (ra.hi + rb.hi) (← mkAppM ``InRange.add #[ra.proof, rb.proof])
    | HSub.hSub _ _ _ _ a b =>
      let some ra ← bounds facts a | return none
      let some rb ← bounds facts b | return none
      normalize (ra.lo - rb.hi) (ra.hi - rb.lo) (← mkAppM ``InRange.sub #[ra.proof, rb.proof])
    | Neg.neg _ _ a =>
      let some ra ← bounds facts a | return none
      normalize (-ra.hi) (-ra.lo) (← mkAppM ``InRange.neg #[ra.proof])
    | HMul.hMul _ _ _ _ a b =>
      if let some k ← intLit? b then
        let some ra ← bounds facts a | return none
        if 0 ≤ k then
          normalize (ra.lo * k) (ra.hi * k)
            (← mkAppM ``InRange.mul_nonneg_right #[ra.proof, ← leProof 0 k])
        else
          normalize (ra.hi * k) (ra.lo * k)
            (← mkAppM ``InRange.mul_nonpos_right #[ra.proof, ← leProof k 0])
      else if let some k ← intLit? a then
        let some rb ← bounds facts b | return none
        if 0 ≤ k then
          normalize (k * rb.lo) (k * rb.hi)
            (← mkAppM ``InRange.mul_nonneg_left #[rb.proof, ← leProof 0 k])
        else
          normalize (k * rb.hi) (k * rb.lo)
            (← mkAppM ``InRange.mul_nonpos_left #[rb.proof, ← leProof k 0])
      else
        let some ra ← bounds facts a | return none
        let some rb ← bounds facts b | return none
        let A := max ra.lo.natAbs ra.hi.natAbs
        let B := max rb.lo.natAbs rb.hi.natAbs
        let hA ← mkAppM ``And.intro #[← leProof (-(A : Int)) ra.lo, ← leProof ra.hi A]
        let hB ← mkAppM ``And.intro #[← leProof (-(B : Int)) rb.lo, ← leProof rb.hi B]
        let pf ← mkAppOptM ``InRange.mul #[none, none, none, none, none, none, toExpr (A : Int),
          toExpr (B : Int), ra.proof, rb.proof, hA, hB]
        normalize (-((A * B : Nat) : Int)) ((A * B : Nat) : Int) pf
    | ite _ c inst a b =>
      let some ra ← bounds facts a | return none
      let some rb ← bounds facts b | return none
      let lo := min ra.lo rb.lo
      let hi := max ra.hi rb.hi
      let hlo ← mkAppM ``And.intro #[← leProof lo ra.lo, ← leProof lo rb.lo]
      let hhi ← mkAppM ``And.intro #[← leProof ra.hi hi, ← leProof rb.hi hi]
      let pf ← mkAppOptM ``InRange.ite #[none, none, none, none, none, none, toExpr lo, toExpr hi,
        c, inst, ra.proof, rb.proof, hlo, hhi]
      return some { lo, hi, proof := pf }
    | Prod.snd _ _ p =>
      let_expr Sem.fitNum c f v := p | return none
      if c.hasFVar || f.hasFVar then return none
      let hh ← mkAppM ``fitNum_holds #[c, f, v]
      let fb ← mkAppM ``NumFmt.fullBinary #[c, f]
      let isBin ← try unsafe evalExpr Bool (mkConst ``Bool) fb catch _ => return none
      let hb ← mkDecideProof (← mkEq fb (toExpr isBin))
      let pf ← mkAppM (if isBin then ``InRange.of_holds_bin else ``InRange.of_holds_dec) #[hh, hb]
      let ty ← inferType pf
      let_expr InRange loE hiE _ := ty | return none
      let some lo ← evalInt? loE | return none
      let some hi ← evalInt? hiE | return none
      normalize lo hi pf
    | HDiv.hDiv _ _ _ _ n d =>
      let some dv ← intLit? d | return none
      unless 0 < dv do return none
      unless (← inferType n).isConstOf ``Int do return none
      let some rn ← bounds facts n | return none
      let hd ← mkDecideProof (← mkAppM ``LT.lt #[toExpr (0 : Int), d])
      normalize (rn.lo / dv) (rn.hi / dv) (← mkAppM ``InRange.ediv #[rn.proof, hd])
    | Cobol.divRound m n d =>
      if m.hasFVar || m.hasMVar then return none
      let some dv ← intLit? d | return none
      unless 0 < dv do return none
      let some rn ← bounds facts n | return none
      let hd ← mkDecideProof (← mkAppM ``LT.lt #[toExpr (0 : Int), d])
      let pf ← mkAppM ``InRange.divRound #[m, rn.proof, hd]
      let some lo ← evalInt? (← mkAppM ``Cobol.divRound #[m, toExpr rn.lo, d]) | return none
      let some hi ← evalInt? (← mkAppM ``Cobol.divRound #[m, toExpr rn.hi, d]) | return none
      normalize lo hi pf
    | Nat.cast _ _ n =>
      if let some k ← getNatValue? n then
        normalize k k (mkApp (mkConst ``InRange.lit) e)
      else
        let_expr Int.natAbs x := n | return none
        let some rx ← bounds facts x | return none
        let A : Int := max rx.lo.natAbs rx.hi.natAbs
        let hA ← mkAppM ``And.intro #[← leProof (-A) rx.lo, ← leProof rx.hi A]
        normalize 0 A (← mkAppM ``InRange.natAbs #[rx.proof, toExpr A, hA])
    | _ => return none
  evalInt? (e : Lean.Expr) : MetaM (Option Int) := do
    if e.hasFVar || e.hasMVar then return none
    try some <$> unsafe evalExpr Int (mkConst ``Int) e catch _ => return none

/-- Facts and intervals already computed, for one local context (identified by `key`): a
merged value contains the previous one, so without the cache every store would recompute
the bounds of the whole history. -/
structure BoundsCache where
  key : UInt64 := 0
  facts : Lean.ExprMap Range := {}
  ranges : Lean.ExprMap (Option Range) := {}
  deriving Inhabited

initialize boundsCacheRef : IO.Ref BoundsCache ← IO.mkRef {}

/-- Identifies the local declarations usable as facts (index `< maxIdx`). -/
def contextKey (maxIdx : Nat) : MetaM UInt64 := do
  let mut h : UInt64 := hash maxIdx
  for ldecl in ← getLCtx do
    if ldecl.index < maxIdx then h := mixHash h (hash ldecl.fvarId)
  return h

/-- Interval of `v` in the current simp context (facts of the initial local context), cached. -/
def boundsOf? (v : Lean.Expr) : SimpM (Option Range) := do
  let maxIdx := (← getContext).lctxInitIndices
  -- a failure to find bounds is never an error: the term is just left alone
  try
    let key ← contextKey maxIdx
    let cache ← boundsCacheRef.get
    let (facts, ranges) ← if cache.key == key then pure (cache.facts, cache.ranges)
      else pure (← collectFacts maxIdx, {})
    let (r, ranges) ← (bounds facts v).run ranges
    boundsCacheRef.set { key, facts, ranges := if ranges.size > 200000 then {} else ranges }
    return r
  catch _ => return none

/-- The bounds of `v` show `f.Holds c v`: a proof, or `none`. -/
def holdsByBounds? (c f v : Lean.Expr) : SimpM (Option Lean.Expr) := do
  if c.hasFVar || f.hasFVar || c.hasMVar || f.hasMVar then return none
  let some r ← boundsOf? v | return none
  try
    let some h1 ← decideClosed? (← mkAppM ``NumFmt.Holds #[c, f, toExpr r.lo]) | return none
    let some h2 ← decideClosed? (← mkAppM ``NumFmt.Holds #[c, f, toExpr r.hi]) | return none
    return some (← mkAppM ``InRange.holds #[r.proof, h1, h2])
  catch _ => return none

/-- `Sem.fitNum c f v = (false, v)` when `v` provably fits `f`. -/
simproc_decl reduceFitNumRange (Sem.fitNum _ _ _) := fun e => do
  let_expr Sem.fitNum c f v := e | return .continue
  let some hv ← holdsByBounds? c f v | return .continue
  let e' ← mkAppM ``Prod.mk #[mkConst ``Bool.false, v]
  return .done { expr := e', proof? := some (← mkAppM ``fitNum_of_holds #[hv]) }

/-- `decodeNum c f (encodeNum c f v) = some v` when `v` provably fits `f`. -/
simproc_decl reduceDecodeEncodeRange (decodeNum _ _ (encodeNum _ _ _)) := fun e => do
  let_expr decodeNum c f bs := e | return .continue
  let_expr encodeNum c' f' v := bs | return .continue
  unless (← isDefEq c c') && (← isDefEq f f') do return .continue
  let some hd ← decideClosed? (← mkAppM ``LT.lt #[mkNatLit 0, ← mkAppM ``NumFmt.digits #[f]])
    | return .continue
  let some hd18 ← decideClosed? (← mkAppM ``LE.le #[← mkAppM ``NumFmt.digits #[f], mkNatLit 18])
    | return .continue
  let some hv ← holdsByBounds? c f v | return .continue
  let e' ← mkAppM ``Option.some #[v]
  return .done { expr := e', proof? := some (← mkAppM ``decodeNum_encodeNum_of_holds #[hd, hd18, hv]) }

/-- `(Int64.ofInt x).toInt = x` (`as i64` / `(long)` of a value that fits). -/
simproc_decl reduceInt64ToIntOfInt (Int64.toInt (Int64.ofInt _)) := fun e => do
  let_expr Int64.toInt y := e | return .continue
  let_expr Int64.ofInt x := y | return .continue
  let some r ← boundsOf? x | return .continue
  let lo : Int := -(2 ^ 63)
  let hi : Int := 2 ^ 63
  unless lo ≤ r.lo && r.hi < hi do return .continue
  let h1 ← mkAppM ``Int.le_trans #[← leProof lo r.lo, ← mkAppM ``And.left #[r.proof]]
  let h2 ← mkAppM ``Int.lt_of_le_of_lt #[← mkAppM ``And.right #[r.proof],
    ← mkDecideProof (← mkAppM ``LT.lt #[toExpr r.hi, toExpr hi])]
  let pf ← mkAppM ``Int64.toInt_ofInt_of_le #[h1, h2]
  return .done { expr := x, proof? := some pf }

/-! ## Comparisons decided by bounds

Overflow checks of target-language code (`checked_mul`, `Math.multiplyExact`, range tests)
compare a nonlinear term with a literal; its interval often decides the comparison. -/

namespace InRange
theorem le_true {lo hi x k : Int} (h : InRange lo hi x) (hk : k ≤ lo) : (k ≤ x) = True :=
  eq_true (Int.le_trans hk h.1)
theorem le_false {lo hi x k : Int} (h : InRange lo hi x) (hk : hi < k) : (k ≤ x) = False :=
  eq_false (by unfold InRange at h; omega)
theorem ge_true {lo hi x k : Int} (h : InRange lo hi x) (hk : hi ≤ k) : (x ≤ k) = True :=
  eq_true (Int.le_trans h.2 hk)
theorem ge_false {lo hi x k : Int} (h : InRange lo hi x) (hk : k < lo) : (x ≤ k) = False :=
  eq_false (by unfold InRange at h; omega)
theorem lt_true {lo hi x k : Int} (h : InRange lo hi x) (hk : k < lo) : (k < x) = True :=
  eq_true (by unfold InRange at h; omega)
theorem lt_false {lo hi x k : Int} (h : InRange lo hi x) (hk : hi ≤ k) : (k < x) = False :=
  eq_false (by unfold InRange at h; omega)
theorem gt_true {lo hi x k : Int} (h : InRange lo hi x) (hk : hi < k) : (x < k) = True :=
  eq_true (by unfold InRange at h; omega)
theorem gt_false {lo hi x k : Int} (h : InRange lo hi x) (hk : k ≤ lo) : (x < k) = False :=
  eq_false (by unfold InRange at h; omega)
end InRange

/-- `k ≤ x`, `x ≤ k`, `k < x`, `x < k` (`k` a literal) decided by the interval of `x`. -/
simproc_decl reduceIntCmpRange ((_ : Int) ≤ _) := fun e => do
  let_expr LE.le α _ a b := e | return .continue
  unless α.isConstOf ``Int do return .continue
  if let some k ← intLit? a then
    if (← intLit? b).isSome then return .continue
    let some r ← boundsOf? b | return .continue
    if k ≤ r.lo then
      let pf ← mkAppM ``InRange.le_true #[r.proof, ← leProof k r.lo]
      return .done { expr := mkConst ``True, proof? := some pf }
    if r.hi < k then
      let hk ← mkDecideProof (← mkAppM ``LT.lt #[toExpr r.hi, toExpr k])
      return .done { expr := mkConst ``False, proof? := some (← mkAppM ``InRange.le_false #[r.proof, hk]) }
    return .continue
  else if let some k ← intLit? b then
    let some r ← boundsOf? a | return .continue
    if r.hi ≤ k then
      let pf ← mkAppM ``InRange.ge_true #[r.proof, ← leProof r.hi k]
      return .done { expr := mkConst ``True, proof? := some pf }
    if k < r.lo then
      let hk ← mkDecideProof (← mkAppM ``LT.lt #[toExpr k, toExpr r.lo])
      return .done { expr := mkConst ``False, proof? := some (← mkAppM ``InRange.ge_false #[r.proof, hk]) }
    return .continue
  else return .continue

/-- The strict comparisons. -/
simproc_decl reduceIntLtRange ((_ : Int) < _) := fun e => do
  let_expr LT.lt α _ a b := e | return .continue
  unless α.isConstOf ``Int do return .continue
  if let some k ← intLit? a then
    if (← intLit? b).isSome then return .continue
    let some r ← boundsOf? b | return .continue
    if k < r.lo then
      let hk ← mkDecideProof (← mkAppM ``LT.lt #[toExpr k, toExpr r.lo])
      return .done { expr := mkConst ``True, proof? := some (← mkAppM ``InRange.lt_true #[r.proof, hk]) }
    if r.hi ≤ k then
      let pf ← mkAppM ``InRange.lt_false #[r.proof, ← leProof r.hi k]
      return .done { expr := mkConst ``False, proof? := some pf }
    return .continue
  else if let some k ← intLit? b then
    let some r ← boundsOf? a | return .continue
    if r.hi < k then
      let hk ← mkDecideProof (← mkAppM ``LT.lt #[toExpr r.hi, toExpr k])
      return .done { expr := mkConst ``True, proof? := some (← mkAppM ``InRange.gt_true #[r.proof, hk]) }
    if k ≤ r.lo then
      let pf ← mkAppM ``InRange.gt_false #[r.proof, ← leProof k r.lo]
      return .done { expr := mkConst ``False, proof? := some pf }
    return .continue
  else return .continue

/-- Distinct valid values have distinct encodings (decoding inverts encoding). -/
theorem encodeNum_beq_of_holds {c : Config} {f : NumFmt} {a b : Int} (hd : 0 < f.digits)
    (hd18 : f.digits ≤ 18) (ha : f.Holds c a) (hb : f.Holds c b) :
    (encodeNum c f a == encodeNum c f b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : encodeNum c f a ≠ encodeNum c f b := by
      intro he
      have h1 := decodeNum_encodeNum_of_holds hd hd18 ha
      have h2 := decodeNum_encodeNum_of_holds hd hd18 hb
      rw [he, h2] at h1
      exact h (Option.some.inj h1).symm
    simp [h, hne]

/-- `encodeNum c f a == encodeNum c f' b` (`f`, `f'` the same format, e.g. a key field and the
record's field) is `decide (a = b)` when both values provably fit: comparing keys by value. -/
simproc_decl reduceEncodeNumBEq (_ == _) := fun e => do
  let_expr BEq.beq _ _ l r := e | return .continue
  let_expr encodeNum c f a := l | return .continue
  let_expr encodeNum c' f' b := r | return .continue
  unless ← isDefEq c c' do return .continue
  unless ← isDefEq f f' do return .continue
  let some ha ← holdsByBounds? c f a | return .continue
  let some hb ← holdsByBounds? c f b | return .continue
  let some hd ← decideClosed? (← mkAppM ``LT.lt #[mkNatLit 0, ← mkAppM ``NumFmt.digits #[f]])
    | return .continue
  let some hd18 ← decideClosed? (← mkAppM ``LE.le #[← mkAppM ``NumFmt.digits #[f], mkNatLit 18])
    | return .continue
  let pf ← mkAppM ``encodeNum_beq_of_holds #[hd, hd18, ha, hb]
  let rhs ← mkDecide (← mkEq a b)
  let pf ← mkExpectedTypeHint pf (← mkEq e rhs)
  return .visit { expr := rhs, proof? := some pf }

end Cobol

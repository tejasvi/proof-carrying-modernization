import EquivLean.Bridge.Cir.AutoCouple
import EquivLean.Bridge.Cir.Congr

/-!
# Pointer arguments

A pointer argument `x : Ptr` of the caller is only meaningful with a bound on its block:
`hx : ∀ b p, x = .loc b p → b < m.next` (the caller's blocks; a block at or above `m.next` would be
one of the callee's own locals, which the two versions allocate differently).  With such a
hypothesis in context, `equiv_cir` marks the pointer (`cir_ptr_intro`: `hx` becomes `cirP_ptrN`)
and the source's symbolic execution splits it where it is first inspected (`splitPtrVar`):

* `null`, `fn s`, `vtable s i k`, an integer address `addr a`: accesses through it are undefined
  behaviour, or compute (`ptrValid`, comparisons with `null`, `ptrToBool`);
* `loc b p`: `cirH_ltN : b < m.next` (so the callee's allocations `m.next + k` are decided apart
  from `b`), the tag `IsCaller b`, and a case split `cirH_blkN : m.blocks b = none` /
  `= some ⟨kind, alive, ty, val⟩` (a second pointer into the same block shares it).

The source's reads through the pointer (and the steps of `a[i]`: the path's last step, the
parent array, the bounds) become case splits named `cirH_rdN`/`cirH_brN`, which cirlean's
`cir_vcg` uses on the target's identical terms.  A value read is split on its constructor before
its typed-load check, and an integer of unknown range is one path: in the range of the type or
read through the signed/unsigned counterpart (cirlean's `loadTy`), the value is `wrap s w x`
(`load_int_merge_s`/`_u`, rewrite rules `cirH_ldS`/`cirH_ldU` of both programs).  Writes in another
order are matched by `cir_ptr_saturate` (`Val.set?_swap`), and `cir_obs_close` compares the caller
blocks both calls wrote case by case.
-/

namespace EquivLean.Cir.Tactic

open Lean Meta Elab Tactic

/-- Mark the pointer arguments that have a caller-block bound `∀ b p, x = .loc b p → b < m.next`
(the bound is renamed `cirP_ptrN`); fails if there is none. -/
elab "cir_ptr_intro" : tactic => do
  let g ← getMainGoal
  let hs ← g.withContext do
    let mut out := #[]
    for d in (← getLCtx) do
      if d.isImplementationDetail || d.userName.toString.startsWith "cirP_ptr" then continue
      if (← ptrBoundOf? (← instantiateMVars d.type)).isSome then out := out.push d.fvarId
    return out
  if hs.isEmpty then
    throwError "cir_ptr_intro: no pointer argument with a bound `∀ b p, x = .loc b p → b < m.next`"
  let n := (← g.getDecl).lctx.foldl (init := 0) fun acc d =>
    if d.userName.toString.startsWith "cirP_ptr" then acc + 1 else acc
  let mut g := g
  for (h, i) in hs.zipIdx do
    g ← g.rename h (Name.mkSimple s!"cirP_ptr{n + i}")
  replaceMainGoal [g]
  -- typed `int` loads of caller integers on one path: rewrite rules of both programs' symbolic
  -- execution (`cirH_…` facts are passed to their `simp` calls)
  unless (← g.getDecl).lctx.any (·.userName == `cirH_ldS) do
    evalTactic (← `(tactic| have $(mkIdent `cirH_ldS):ident := @EquivLean.Cir.load_int_merge_s))
    evalTactic (← `(tactic| have $(mkIdent `cirH_ldU):ident := @EquivLean.Cir.load_int_merge_u))

/-- `equiv_cir` with pointer arguments: mark them (`cir_ptr_intro`), then `equiv_cir`.  Without a
bounded pointer argument, the previous `equiv_cir`. -/
macro_rules
  | `(tactic| equiv_cir) => `(tactic| (
      try cir_equivOn_intro
      cir_ptr_intro
      equiv_cir))

end EquivLean.Cir.Tactic

namespace EquivLean.Cir
open CIR Lean Meta Simp

attribute [cir_exec] loadPtr.eq_5 loadPtr.eq_6
attribute [-cir_exec] reducePunnedMember reduceTypedLoad reduceTypedStore

@[cir_exec] theorem ptr_bne_null_loc (b : Nat) (p : List PathElem) : (Ptr.loc b p != Ptr.null) = true := rfl
@[cir_exec] theorem ptr_bne_null_null : (Ptr.null != Ptr.null) = false := rfl
@[cir_exec] theorem ptr_bne_null_fn (s : String) : (Ptr.fn s != Ptr.null) = true := rfl
@[cir_exec] theorem ptr_bne_null_vtable (v : String) (i k : Nat) : (Ptr.vtable v i k != Ptr.null) = true := rfl
@[cir_exec] theorem ptr_bne_null_addr (a : Int) : (Ptr.addr a != Ptr.null) = true := rfl
@[cir_exec] theorem ptr_bne_null_label (f l : String) : (Ptr.label f l != Ptr.null) = true := rfl

@[cir_exec] theorem initBy_int (a : Int) (w : Val) : (Val.int a).initBy w = false := by
  unfold Val.initBy Val.holds
  cases w <;> simp only [Val.fillsOver, Bool.not_true, Bool.false_or] <;> try rfl
  split <;> rfl

@[cir_exec] theorem fillsOver_int_eq_some_true (a : Int) (w : Val) :
    ((Val.int a).fillsOver w == some true) = false := by
  cases w <;> simp only [Val.fillsOver] <;> try rfl
  split <;> rfl

@[cir_exec] theorem ite_some_false_none_beq_some_true (p : Prop) [Decidable p] :
    ((if p then some false else none) == some true) = false := by
  split <;> rfl

@[cir_exec] theorem ofOption_map {α β : Type} (msg : String) (o : Option α) (f : α → β) :
    Res.ofOption msg (o.map f) = match o with | some x => .ok (f x) | none => .ub msg := by
  cases o <;> rfl

@[cir_exec] theorem lensStride?_vtable_eq (ctx : Ctx) (m : Mem) (vt : String) (j k : Nat) (n : Int) (e : Nat) :
    ctx.lensStride? m (.vtable vt j k) n e =
      (if n = 0 then some k
       else let s : Int := ctx.mod.ptrBytes
         if s ≠ 0 ∧ (n * e) % s = 0 ∧ 0 ≤ k + (n * e) / s then some (k + (n * e) / s).toNat else none).map
      (Ptr.vtable vt j) := by
  unfold Ctx.lensStride? Ctx.vtableStride?
  dsimp only
  split <;> first | rfl | (split <;> rfl)

@[cir_exec] theorem lensStride?_fn (ctx : Ctx) (m : Mem) (s : String) (n : Int) (e : Nat) :
    ctx.lensStride? m (.fn s) n e = none := by unfold Ctx.lensStride? Ctx.lens?; split <;> rfl
@[cir_exec] theorem lensStride?_addr (ctx : Ctx) (m : Mem) (a : Int) (n : Int) (e : Nat) :
    ctx.lensStride? m (.addr a) n e = none := by unfold Ctx.lensStride? Ctx.lens?; split <;> rfl
@[cir_exec] theorem lensStride?_label (ctx : Ctx) (m : Mem) (f l : String) (n : Int) (e : Nat) :
    ctx.lensStride? m (.label f l) n e = none := by unfold Ctx.lensStride? Ctx.lens?; split <;> rfl

simproc ↓ [cir_exec] reducePunnedMemberNoRecords2 (Ctx.punnedMember _ _ _ _) := fun e => do
  unless e.isAppOfArity ``Ctx.punnedMember 4 do return .continue
  let ctx := e.getArg! 0
  let lhs ← mkAppM ``CIR.Module.records #[← mkAppM ``Ctx.mod #[ctx]]
  let recs ← whnfD lhs
  unless recs.isAppOfArity ``List.nil 1 do return .continue
  let h ← mkExpectedTypeHint (← mkEqRefl recs) (← mkEq lhs recs)
  let pf ← mkAppOptM ``punnedMember_of_records_nil
    #[some ctx, some (e.getArg! 1), some (e.getArg! 2), some (e.getArg! 3), some h]
  return .done { expr := mkConst ``Bool.false, proof? := some pf }

simproc ↓ [cir_exec] reducePunnedMemberDefault (Ctx.punnedMember _ _ _ _) := reduceTypeTestImpl false

def emptyMod : CIR.Module := { name := "", records := [], globals := [], funcs := [] }
def emptyCtx : Ctx := Ctx.ofModule emptyMod

theorem emptyCtx_record? (name : String) : emptyCtx.record? name = none := rfl

theorem setChild_opt (o : Option Val) (e : PathElem) (c' : Val) :
    ∃ o', Val.setChild (.opt o) e c' = .opt o' := by
  cases o <;> cases e <;> try exact ⟨_, rfl⟩
  rename_i w i; cases i <;> exact ⟨_, rfl⟩

theorem Val.shaped_of_isLeaf {v : Val} (hv : v.IsLeaf) (t : Ty) :
    Val.shaped t v = t.isScalar := by
  cases t <;> cases v <;> first | exact False.elim hv | rfl

theorem Val.shaped_setChild {v : Val} (e : PathElem) (c' : Val) (t : Ty) :
    Val.shaped t (Val.setChild v e c') = Val.shaped t v := by
  cases v with
  | opt o =>
    obtain ⟨o', ho'⟩ := setChild_opt o e c'
    rw [ho']; cases t <;> rfl
  | _ => cases t <;> cases e <;> rfl

theorem Val.shaped_of_set_leaf {v0 w1 a x : Val} {q : List PathElem}
    (hg : v0.get? q = some a) (ha : a.IsLeaf) (hx : x.IsLeaf) (hs : v0.set? q x = some w1) (t : Ty) :
    Val.shaped t w1 = Val.shaped t v0 := by
  cases q with
  | nil =>
    cases hg; cases hs
    rw [Val.shaped_of_isLeaf hx, Val.shaped_of_isLeaf ha]
  | cons e q' =>
    rw [Val.set?_cons] at hs
    obtain ⟨c, _, hs'⟩ := Option.bind_eq_some_iff.mp hs
    obtain ⟨c', _, rfl⟩ := Option.map_eq_some_iff.mp hs'
    exact Val.shaped_setChild e c' t

theorem scalarIn_of_isLeaf (fuel : Nat) (t : Ty) {v : Val} (hv : v.IsLeaf) (path : List PathElem) (k : Nat) :
    emptyCtx.scalarIn fuel t v path k =
      match fuel with
      | 0 => none
      | _ + 1 => if t.isScalar then some (path, t, k) else none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    unfold Ctx.scalarIn
    split
    · rfl
    · cases t <;> cases v <;> first | exact False.elim hv | rfl

theorem scalarIn_setChild_non_arr {fuel : Nat} {t : Ty} {v0 : Val} (h : ∀ xs, v0 ≠ .arr xs)
    (e : PathElem) (c' : Val) (path : List PathElem) (k : Nat) :
    emptyCtx.scalarIn (fuel + 1) t (Val.setChild v0 e c') path k =
      emptyCtx.scalarIn (fuel + 1) t v0 path k := by
  cases v0 with
  | arr xs => exact False.elim (h xs rfl)
  | opt o =>
    obtain ⟨o', ho'⟩ := setChild_opt o e c'
    rw [ho']; unfold Ctx.scalarIn; split <;> first | rfl | (cases t <;> rfl)
  | agg fs =>
    unfold Ctx.scalarIn; split <;> first | rfl | (cases t <;> cases e <;> simp only [Val.setChild, emptyCtx_record?])
  | vec g xs =>
    unfold Ctx.scalarIn; split <;> first | rfl | (cases t <;> cases e <;> rfl)
  | _ =>
    unfold Ctx.scalarIn; split <;> first | rfl | (cases t <;> cases e <;> rfl)

theorem scalarIn_of_set_leaf :
    ∀ (fuel : Nat) {v0 w1 a x : Val} {q : List PathElem},
      v0.get? q = some a → a.IsLeaf → x.IsLeaf → v0.set? q x = some w1 →
      ∀ (t : Ty) (path : List PathElem) (k : Nat),
        emptyCtx.scalarIn fuel t w1 path k = emptyCtx.scalarIn fuel t v0 path k
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, v0, w1, a, x, [], hg, ha, hx, hs, t, path, k => by
    cases hg; cases hs
    rw [scalarIn_of_isLeaf (fuel + 1) t hx, scalarIn_of_isLeaf (fuel + 1) t ha]
  | fuel + 1, v0, w1, a, x, e :: q', hg, ha, hx, hs, t, path, k => by
    rw [Val.get?_cons] at hg
    obtain ⟨c, hc, hca⟩ := Option.bind_eq_some_iff.mp hg
    rw [Val.set?_cons, hc, Option.bind_some] at hs
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hs
    cases v0 with
    | arr xs =>
      cases e with
      | idx i =>
        simp only [Val.child?] at hc
        unfold Ctx.scalarIn
        split
        · rfl
        · cases t with
          | array elem len =>
            simp only [Val.setChild]
            rcases emptyCtx.sizeAlign 32 elem with _ | ⟨s, al⟩ <;> try rfl
            simp only
            split
            · rfl
            · by_cases hik : k / s = i
              · subst hik
                rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hc).1, hc]
                exact scalarIn_of_set_leaf fuel hca ha hx hc' elem (path ++ [.idx (k / s)]) (k % s)
              · rw [List.getElem?_set_ne (Ne.symm hik)]
          | _ => rfl
      | _ => cases hc
    | _ =>
      exact scalarIn_setChild_non_arr (by intro _ h; cases h) e c' path k

theorem Val.child?_setChild_eq_of_ne {v c c' : Val} {e e0 : PathElem}
    (hc : Val.child? v e = some c) (hne : e ≠ e0) :
    Val.child? (Val.setChild v e c') e0 = Val.child? v e0 := by
  cases hd : Val.child? v e0 with
  | some d => exact Val.child?_setChild_ne hc hd hne
  | none =>
    cases v with
    | agg fs =>
      cases e <;> try cases hc
      cases e0 <;> try rfl
      rename_i i j
      have hij : i ≠ j := fun h => hne (h ▸ rfl)
      simp only [Val.child?, Val.setChild] at hd ⊢
      rw [List.getElem?_set_ne hij]; exact hd
    | arr xs =>
      cases e <;> try cases hc
      cases e0 <;> try rfl
      rename_i i j
      have hij : i ≠ j := fun h => hne (h ▸ rfl)
      simp only [Val.child?, Val.setChild] at hd ⊢
      rw [List.getElem?_set_ne hij]; exact hd
    | vec g xs =>
      cases e <;> try cases hc
      cases e0 <;> try rfl
      rename_i g1 i g2 j
      simp only [Val.child?, Val.setChild] at hc hd ⊢
      by_cases hg1 : g = g1
      · by_cases hg2 : g = g2
        · subst hg1; subst hg2
          have hij : i ≠ j := fun h => hne (h ▸ rfl)
          rw [ite_eq_left rfl] at hd ⊢
          rw [List.getElem?_set_ne hij]; exact hd
        · rw [ite_eq_right hg2] at hd ⊢
      · rw [ite_eq_right hg1] at hc; cases hc
    | opt o =>
      cases o with
      | none => cases e <;> cases hc
      | some w =>
        cases e <;> try cases hc
        rename_i i; cases i <;> try cases hc
        cases e0 <;> try rfl
        rename_i j; cases j with
        | zero => exact absurd rfl hne
        | succ _ => rfl
    | _ => cases e <;> cases hc

theorem get?_of_set_leaf :
    ∀ (p0 : List PathElem) {v0 w1 a x : Val} {q : List PathElem},
      v0.get? q = some a → a.IsLeaf → x.IsLeaf → v0.set? q x = some w1 →
      w1.get? p0 = v0.get? p0 ∨
        ∃ u0 u1 r, v0.get? p0 = some u0 ∧ w1.get? p0 = some u1 ∧
          u0.get? r = some a ∧ u0.set? r x = some u1
  | [], v0, w1, a, x, q, hg, _, _, hs => Or.inr ⟨v0, w1, q, rfl, rfl, hg, hs⟩
  | e0 :: p', v0, w1, a, x, [], hg, ha, hx, hs => by
    cases hg; cases hs
    rw [Val.get?_leaf_cons hx, Val.get?_leaf_cons ha]
    exact Or.inl rfl
  | e0 :: p', v0, w1, a, x, e :: q', hg, ha, hx, hs => by
    rw [Val.get?_cons] at hg
    obtain ⟨c, hc, hca⟩ := Option.bind_eq_some_iff.mp hg
    rw [Val.set?_cons, hc, Option.bind_some] at hs
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp hs
    rw [Val.get?_cons, Val.get?_cons]
    by_cases hee : e = e0
    · subst hee
      rw [Val.child?_setChild_self hc, hc, Option.bind_some, Option.bind_some]
      exact get?_of_set_leaf p' hca ha hx hc'
    · rw [Val.child?_setChild_eq_of_ne hc hee]
      exact Or.inl rfl

theorem reachScalarAt_of_set_leaf {v0 w1 a x : Val} {q : List PathElem}
    (hg : v0.get? q = some a) (ha : a.IsLeaf) (hx : x.IsLeaf) (hs : v0.set? q x = some w1)
    (kind : BlockKind) (alive : Bool) (bty ty : Ty) (p0 : List PathElem) (k : Nat) (t : Ty) :
    emptyCtx.reachScalarAt ⟨kind, alive, bty, w1⟩ ty p0 k t =
      emptyCtx.reachScalarAt ⟨kind, alive, bty, v0⟩ ty p0 k t := by
  unfold Ctx.reachScalarAt
  split
  · cases alive
    · rfl
    · simp only [↓reduceIte]
      rcases get?_of_set_leaf p0 hg ha hx hs with heq | ⟨u0, u1, r, hu0, hu1, hga, hsu⟩
      · rw [heq]
      · rw [hu0, hu1]
        simp only [Val.shaped_of_set_leaf hga ha hx hsu, scalarIn_of_set_leaf 32 hga ha hx hsu]
  · rfl

theorem reachIn_of_set_leaf {v0 w1 a x : Val} {q : List PathElem}
    (hg : v0.get? q = some a) (ha : a.IsLeaf) (hx : x.IsLeaf) (hs : v0.set? q x = some w1)
    {ty : Ty} (hty : ty.isScalar = true)
    (kind : BlockKind) (alive : Bool) (bty : Ty) (path : List PathElem) :
    emptyCtx.reachIn ⟨kind, alive, bty, w1⟩ ty path =
      emptyCtx.reachIn ⟨kind, alive, bty, v0⟩ ty path := by
  have hagg : ty.isAggregate = false := by cases ty <;> first | rfl | cases hty
  unfold Ctx.reachIn Ctx.reachTypeNone Ctx.reachSlow
  simp only [hty, hagg, ite_true, Bool.false_eq_true, ite_false]
  rcases emptyCtx.typeAt bty (splitByte path).1 with _ | t <;> try rfl
  dsimp only
  rw [reachScalarAt_of_set_leaf hg ha hx hs]

def reachPath? (bty : Ty) (bval : Val) (ty : Ty) (path : List PathElem) : Option (List PathElem) :=
  match emptyCtx.reachIn ⟨.stack, true, bty, bval⟩ ty path with
  | none => some path
  | some (.obj p') => some p'
  | _ => none

theorem reachPath?_of_set_int {v0 w1 : Val} {q : List PathElem} {x y : Int}
    (hg : v0.get? q = some (.int x)) (hs : v0.set? q (.int y) = some w1)
    {ty : Ty} (hty : ty.isScalar = true) (bty : Ty) (path : List PathElem) :
    reachPath? bty w1 ty path = reachPath? bty v0 ty path := by
  have ha : (Val.int x).IsLeaf := trivial
  have hx : (Val.int y).IsLeaf := trivial
  unfold reachPath?
  rw [reachIn_of_set_leaf hg ha hx hs hty]

theorem reachIn_alive_kind_irrel (ctx : Ctx) (k₁ k₂ : BlockKind) (bty : Ty) (bval : Val) (ty : Ty) (path : List PathElem) :
    ctx.reachIn ⟨k₁, true, bty, bval⟩ ty path = ctx.reachIn ⟨k₂, true, bty, bval⟩ ty path := rfl

theorem reachScalar_ne_external (ty : Ty) (k0 : Nat) (r : List PathElem × Ty × Nat) :
    reachScalar ty k0 r ≠ .external := by
  rcases r with ⟨p1, t1, k1⟩; dsimp only [reachScalar]
  by_cases hc1 : ty.isChar = true
  · rw [ite_eq_left hc1]; by_cases hc2 : t1.isChar = true
    · rw [ite_eq_left hc2]; by_cases hk : k1 = 0 <;> (first | rw [ite_eq_left hk] | rw [ite_eq_right hk]) <;> intro h <;> cases h
    · rw [ite_eq_right hc2]; intro h; cases h
  · rw [ite_eq_right hc1]
    by_cases hk : ((decide (k0 = 0) && decide (k1 = 0) && t1.accessCompatible ty) = true) <;>
      (first | rw [ite_eq_left hk] | rw [ite_eq_right hk]) <;> intro h <;> cases h

theorem reachScalarAt_ne_external (ctx : Ctx) (blk : MemBlock) (ty : Ty) (p0 : List PathElem) (k : Nat) (t : Ty) :
    ctx.reachScalarAt blk ty p0 k t ≠ some .external := by
  unfold Ctx.reachScalarAt; split
  · rcases (if blk.alive then blk.val.get? p0 else none) with _ | v
    · intro h; cases h
    · simp only; split
      · rcases ctx.scalarIn 32 t v p0 k with _ | r
        · intro h; cases h
        · intro h; exact reachScalar_ne_external ty k r (Option.some.inj h)
      · intro h; cases h
  · intro h; cases h

theorem reachIn_alive_ne_external (ctx : Ctx) (kind : BlockKind) (bty : Ty) (bval : Val) (s : Bool) (w : Nat) (path : List PathElem) :
    ctx.reachIn ⟨kind, true, bty, bval⟩ (.int s w) path ≠ some .external := by
  have hagg : (Ty.int s w).isAggregate = false := rfl
  unfold Ctx.reachIn Ctx.reachSlow; split
  · intro h; cases h
  · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
    rcases ctx.typeAt bty (splitByte path).1 with _ | t
    · simp only [hagg, Bool.false_eq_true, ite_false]; intro h; cases h
    · exact reachScalarAt_ne_external ctx _ (.int s w) _ _ t

theorem reachScalar_ne_spread (ty : Ty) (k0 : Nat) (r : List PathElem × Ty × Nat) (p' : List PathElem) (t' : Ty) :
    reachScalar ty k0 r ≠ .spread p' t' := by
  rcases r with ⟨p1, t1, k1⟩; dsimp only [reachScalar]
  by_cases hc1 : ty.isChar = true
  · rw [ite_eq_left hc1]; by_cases hc2 : t1.isChar = true
    · rw [ite_eq_left hc2]; by_cases hk : k1 = 0 <;> (first | rw [ite_eq_left hk] | rw [ite_eq_right hk]) <;> intro h <;> cases h
    · rw [ite_eq_right hc2]; intro h; cases h
  · rw [ite_eq_right hc1]
    by_cases hk : ((decide (k0 = 0) && decide (k1 = 0) && t1.accessCompatible ty) = true) <;>
      (first | rw [ite_eq_left hk] | rw [ite_eq_right hk]) <;> intro h <;> cases h

theorem reachScalarAt_ne_spread (ctx : Ctx) (blk : MemBlock) (ty : Ty) (p0 : List PathElem) (k : Nat) (t : Ty)
    (p' : List PathElem) (t' : Ty) :
    ctx.reachScalarAt blk ty p0 k t ≠ some (.spread p' t') := by
  unfold Ctx.reachScalarAt; split
  · rcases (if blk.alive then blk.val.get? p0 else none) with _ | v
    · intro h; cases h
    · simp only; split
      · rcases ctx.scalarIn 32 t v p0 k with _ | r
        · intro h; cases h
        · intro h; exact reachScalar_ne_spread ty k r p' t' (Option.some.inj h)
      · intro h; cases h
  · intro h; cases h

theorem reachIn_int_ne_spread (ctx : Ctx) (blk : MemBlock) (s : Bool) (w : Nat) (path : List PathElem)
    (p' : List PathElem) (t' : Ty) :
    ctx.reachIn blk (.int s w) path ≠ some (.spread p' t') := by
  have hagg : (Ty.int s w).isAggregate = false := rfl
  unfold Ctx.reachIn Ctx.reachSlow; split
  · intro h; cases h
  · split
    · intro h; cases h
    · rcases ctx.typeAt blk.ty (splitByte path).1 with _ | t
      · simp only [hagg, Bool.false_eq_true, ite_false]; intro h; cases h
      · exact reachScalarAt_ne_spread ctx blk (.int s w) _ _ t p' t'

theorem viewValIn?_eq_none_of_records_nil {ctx : Ctx} (h : ctx.mod.records = []) :
    ∀ t v p, ctx.viewValIn? t v p = none
  | _, _, [] => by simp [Ctx.viewValIn?]
  | t, v, e :: p => by
    cases e <;> cases t <;> cases v <;> simp only [Ctx.viewValIn?, Ctx.record?, CIR.Module.findRecord?, h, List.find?_nil] <;> try rfl
    case idx.array.arr k elem n xs =>
      cases p with
      | nil => rfl
      | cons e2 p2 =>
        cases xs[k]? with
        | none => rfl
        | some x => simp [viewValIn?_eq_none_of_records_nil h elem x (e2 :: p2)]

theorem activateValIn?_eq_none_of_records_nil {ctx : Ctx} (h : ctx.mod.records = []) :
    ∀ t v p, ctx.activateValIn? t v p = none
  | _, _, [] => by simp [Ctx.activateValIn?]
  | t, v, e :: p => by
    cases e <;> cases t <;> cases v <;> simp only [Ctx.activateValIn?, Ctx.record?, CIR.Module.findRecord?, h, List.find?_nil] <;> try rfl
    case idx.array.arr k elem n xs =>
      cases p with
      | nil => rfl
      | cons e2 p2 =>
        cases xs[k]? with
        | none => rfl
        | some x => simp [activateValIn?_eq_none_of_records_nil h elem x (e2 :: p2)]

theorem unionView?_of_records_nil {ctx : Ctx} {m : Mem} {p : Ptr} (h : ctx.mod.records = []) :
    ctx.unionView? m p = none := by
  cases p <;> simp only [Ctx.unionView?]
  case loc b path =>
    cases m.blocks b <;> simp only [Option.map_eq_none_iff, Ctx.viewVal?]
    split
    · exact viewValIn?_eq_none_of_records_nil h _ _ _
    · rfl

theorem activateVal?_of_records_nil {ctx : Ctx} {t : Ty} {v : Val} {p : List PathElem}
    (h : ctx.mod.records = []) : ctx.activateVal? t v p = none := by
  unfold Ctx.activateVal?
  split
  · exact activateValIn?_eq_none_of_records_nil h _ _ _
  · rfl

theorem unionActivate?_of_records_nil {ctx : Ctx} {m : Mem} {p : Ptr} (h : ctx.mod.records = []) :
    ctx.unionActivate? m p = none := by
  cases p <;> simp only [Ctx.unionActivate?]
  case loc b path =>
    cases m.blocks b <;> simp only [activateVal?_of_records_nil h]

theorem typedLoad_int32_alive_of_records_nil {ctx : Ctx} {m : Mem} {s : Bool} {b : Nat} {path : List PathElem}
    {kind : BlockKind} {bty : Ty} {bval : Val}
    (h : ctx.mod.records = []) (hp : ctx.mod.ptrBytes = 8)
    (hblk : m.blocks b = some ⟨kind, true, bty, bval⟩) :
    ctx.typedLoad m (.int s 32) (.loc b path) =
      match reachPath? bty bval (.int s 32) path with
      | some q => loadTy m (.int s 32) (.loc b q)
      | none => .ub "type-punned access (byte-level access not modelled)" := by
  have hr : ∀ name, ctx.record? name = emptyCtx.record? name := by
    intro name
    have h1 : ctx.record? name = none := by simp [Ctx.record?, CIR.Module.findRecord?, h]
    have h2 : emptyCtx.record? name = none := rfl
    rw [h1, h2]
  have hp' : ctx.mod.ptrBytes = emptyCtx.mod.ptrBytes := hp
  unfold Ctx.typedLoad reachPath?
  simp only [unionView?_of_records_nil h, Option.getD_none, punnedMember_of_records_nil h,
    Bool.false_eq_true, ite_false, Ctx.reach?, hblk, reachIn_congr hr hp',
    reachIn_alive_kind_irrel emptyCtx kind .stack]
  rcases hri : emptyCtx.reachIn ⟨.stack, true, bty, bval⟩ (.int s 32) path with _ | r
  · rfl
  · cases r with
    | byte p' t' k' => rfl
    | obj p' => simp only [Option.map_some]
    | punned => rfl
    | spread p' t' => exact absurd hri (reachIn_int_ne_spread emptyCtx _ s 32 path p' t')
    | external => exact absurd hri (reachIn_alive_ne_external emptyCtx .stack bty bval s 32 path)

theorem typedStore_int32_alive_of_records_nil {ctx : Ctx} {m : Mem} {s : Bool} {b : Nat} {path : List PathElem} {v : Val}
    {kind : BlockKind} {bty : Ty} {bval : Val}
    (h : ctx.mod.records = []) (hp : ctx.mod.ptrBytes = 8)
    (hblk : m.blocks b = some ⟨kind, true, bty, bval⟩) :
    ctx.typedStore m (.int s 32) (.loc b path) v =
      match reachPath? bty bval (.int s 32) path with
      | some q => storeTy m (.int s 32) (.loc b q) v
      | none => .ub "type-punned access (byte-level access not modelled)" := by
  have hr : ∀ name, ctx.record? name = emptyCtx.record? name := by
    intro name
    have h1 : ctx.record? name = none := by simp [Ctx.record?, CIR.Module.findRecord?, h]
    have h2 : emptyCtx.record? name = none := rfl
    rw [h1, h2]
  have hp' : ctx.mod.ptrBytes = emptyCtx.mod.ptrBytes := hp
  unfold Ctx.typedStore reachPath?
  simp only [unionActivate?_of_records_nil h, Option.getD_none, punnedMember_of_records_nil h,
    Bool.false_eq_true, ite_false, Ctx.reach?, hblk, reachIn_congr hr hp',
    reachIn_alive_kind_irrel emptyCtx kind .stack]
  rcases hri : emptyCtx.reachIn ⟨.stack, true, bty, bval⟩ (.int s 32) path with _ | r
  · rfl
  · cases r with
    | byte p' t' k' => rfl
    | obj p' => simp only [Option.map_some]
    | punned => rfl
    | spread p' t' => exact absurd hri (reachIn_int_ne_spread emptyCtx _ s 32 path p' t')
    | external => exact absurd hri (reachIn_alive_ne_external emptyCtx .stack bty bval s 32 path)

theorem typedStore_int32_alive_set_of_records_nil {ctx : Ctx} {m : Mem} {s : Bool} {b : Nat} {path : List PathElem} {v : Val}
    {kind : BlockKind} {bty : Ty} {v0 w1 : Val} {q0 : List PathElem} {x y : Int}
    (h : ctx.mod.records = []) (hp : ctx.mod.ptrBytes = 8)
    (hblk : m.blocks b = some ⟨kind, true, bty, w1⟩)
    (hg : v0.get? q0 = some (.int x)) (hs : v0.set? q0 (.int y) = some w1) :
    ctx.typedStore m (.int s 32) (.loc b path) v =
      match reachPath? bty v0 (.int s 32) path with
      | some q => storeTy m (.int s 32) (.loc b q) v
      | none => .ub "type-punned access (byte-level access not modelled)" := by
  rw [typedStore_int32_alive_of_records_nil h hp hblk, reachPath?_of_set_int hg hs rfl]

def deadLoadUbMsg (kind : BlockKind) (bty : Ty) (bval : Val) (s : Bool) (path : List PathElem) : String :=
  match emptyCtx.reachIn ⟨kind, false, bty, bval⟩ (.int s 32) path with
  | some .external => "external object without a model"
  | some (.byte ..) | some .punned => "type-punned access (byte-level access not modelled)"
  | some (.obj p') => if punnedAt bty (.int s 32) p' then "type-punned access (byte-level access not modelled)" else "invalid memory read"
  | _ => if punnedAt bty (.int s 32) path then "type-punned access (byte-level access not modelled)" else "invalid memory read"

theorem typedLoad_int32_dead_of_records_nil {ctx : Ctx} {m : Mem} {s : Bool} {b : Nat} {path : List PathElem}
    {kind : BlockKind} {bty : Ty} {bval : Val}
    (h : ctx.mod.records = []) (hp : ctx.mod.ptrBytes = 8)
    (hblk : m.blocks b = some ⟨kind, false, bty, bval⟩) :
    ctx.typedLoad m (.int s 32) (.loc b path) = .ub (deadLoadUbMsg kind bty bval s path) := by
  have hr : ∀ name, ctx.record? name = emptyCtx.record? name := by
    intro name
    have h1 : ctx.record? name = none := by simp [Ctx.record?, CIR.Module.findRecord?, h]
    have h2 : emptyCtx.record? name = none := rfl
    rw [h1, h2]
  have hp' : ctx.mod.ptrBytes = emptyCtx.mod.ptrBytes := hp
  unfold Ctx.typedLoad deadLoadUbMsg
  simp only [unionView?_of_records_nil h, Option.getD_none, punnedMember_of_records_nil h,
    Bool.false_eq_true, ite_false, Ctx.reach?, hblk, reachIn_congr hr hp']
  rcases hri : emptyCtx.reachIn ⟨kind, false, bty, bval⟩ (.int s 32) path with _ | r
  · simp only [Option.map_none, loadTy_loc_eq hblk, Bool.false_eq_true, ite_false, loadValOf]
    cases punnedAt bty (.int s 32) path <;> rfl
  · cases r with
    | byte p' t' k' => rfl
    | obj p' =>
      simp only [Option.map_some, loadTy_loc_eq hblk, Bool.false_eq_true, ite_false, loadValOf]
      cases punnedAt bty (.int s 32) p' <;> rfl
    | punned => rfl
    | spread p' t' => exact absurd hri (reachIn_int_ne_spread emptyCtx _ s 32 path p' t')
    | external => rfl

def deadStoreUbMsg (kind : BlockKind) (bty : Ty) (bval : Val) (s : Bool) (path : List PathElem) (v : Val) : String :=
  match emptyCtx.reachIn ⟨kind, false, bty, bval⟩ (.int s 32) path with
  | some .external => "external object without a model"
  | some (.byte ..) | some .punned => "type-punned access (byte-level access not modelled)"
  | some (.obj p') =>
    if punnedAt bty (.int s 32) p' then "type-punned access (byte-level access not modelled)"
    else if !fitsTy (.int s 32) v then "ill-typed store" else "invalid memory write"
  | _ =>
    if punnedAt bty (.int s 32) path then "type-punned access (byte-level access not modelled)"
    else if !fitsTy (.int s 32) v then "ill-typed store" else "invalid memory write"

theorem typedStore_int32_dead_of_records_nil {ctx : Ctx} {m : Mem} {s : Bool} {b : Nat} {path : List PathElem} {v : Val}
    {kind : BlockKind} {bty : Ty} {bval : Val}
    (h : ctx.mod.records = []) (hp : ctx.mod.ptrBytes = 8)
    (hblk : m.blocks b = some ⟨kind, false, bty, bval⟩) :
    ctx.typedStore m (.int s 32) (.loc b path) v = .ub (deadStoreUbMsg kind bty bval s path v) := by
  have hr : ∀ name, ctx.record? name = emptyCtx.record? name := by
    intro name
    have h1 : ctx.record? name = none := by simp [Ctx.record?, CIR.Module.findRecord?, h]
    have h2 : emptyCtx.record? name = none := rfl
    rw [h1, h2]
  have hp' : ctx.mod.ptrBytes = emptyCtx.mod.ptrBytes := hp
  unfold Ctx.typedStore deadStoreUbMsg
  simp only [unionActivate?_of_records_nil h, Option.getD_none, punnedMember_of_records_nil h,
    Bool.false_eq_true, ite_false, Ctx.reach?, hblk, reachIn_congr hr hp']
  rcases hri : emptyCtx.reachIn ⟨kind, false, bty, bval⟩ (.int s 32) path with _ | r
  · simp only [Option.map_none, storeTy_loc_eq hblk, storeAt, Ty.isScalar, Bool.true_and, Bool.false_eq_true, ite_false]
    cases punnedAt bty (.int s 32) path <;> (simp only [Bool.false_eq_true, ↓reduceIte]; try (split <;> rfl))
  · cases r with
    | byte p' t' k' => rfl
    | obj p' =>
      simp only [Option.map_some, storeTy_loc_eq hblk, storeAt, Ty.isScalar, Bool.true_and, Bool.false_eq_true, ite_false]
      cases punnedAt bty (.int s 32) p' <;> (simp only [Bool.false_eq_true, ↓reduceIte]; try (split <;> rfl))
    | punned => rfl
    | spread p' t' => exact absurd hri (reachIn_int_ne_spread emptyCtx _ s 32 path p' t')
    | external => rfl

def stridePath? (b : Nat) (blk : MemBlock) (path : List PathElem) (n : Int) (elemTy : Ty) : Option (List PathElem) :=
  match emptyCtx.stride? (Mem.empty.setBlock b blk) (.loc b path) n elemTy with
  | some (.loc _ q) => some q
  | _ => none

theorem mem_live?_eq_of_blocks_eq {m₁ m₂ : Mem} {b : Nat} (hb : m₁.blocks b = m₂.blocks b) :
    m₁.live? b = m₂.live? b := by simp only [Mem.live?, hb]

theorem mem_read?_loc_eq_of_blocks_eq {m₁ m₂ : Mem} {b : Nat} (hb : m₁.blocks b = m₂.blocks b)
    (path : List PathElem) : m₁.read? (.loc b path) = m₂.read? (.loc b path) := by
  simp only [Mem.read?, mem_live?_eq_of_blocks_eq hb]

theorem mem_elemPos?_loc_eq_of_blocks_eq {m₁ m₂ : Mem} {b : Nat} (hb : m₁.blocks b = m₂.blocks b)
    (path : List PathElem) : m₁.elemPos? (.loc b path) = m₂.elemPos? (.loc b path) := by
  simp only [Mem.elemPos?]
  rcases splitLast path with _ | ⟨pre, last⟩ <;> try rfl
  cases last <;> simp only [mem_read?_loc_eq_of_blocks_eq hb]

theorem mem_elemPos?_loc_fst {m : Mem} {b : Nat} {path : List PathElem}
    {b' : Nat} {pre : List PathElem} {last : PathElem} {len : Nat}
    (h : m.elemPos? (.loc b path) = some (b', pre, last, len)) : b' = b := by
  simp only [Mem.elemPos?] at h
  rcases hsp : splitLast path with _ | ⟨p0, l0⟩
  · rw [hsp] at h; cases h
  · rw [hsp] at h
    cases l0 <;> simp only at h
    · rcases hmr : m.read? (.loc b p0) with _ | v
      · rw [hmr] at h; cases h
      · rw [hmr] at h; cases v <;> first | exact ((Prod.mk.inj (Option.some.inj h)).1).symm | cases h
    · rcases hmr : m.read? (.loc b p0) with _ | v
      · rw [hmr] at h; cases h
      · rw [hmr] at h; cases v <;> try cases h
        simp only at h
        split at h <;> first | exact ((Prod.mk.inj (Option.some.inj h)).1).symm | cases h
    · cases h

theorem mem_stride?_loc_eq_of_blocks_eq {m₁ m₂ : Mem} {b : Nat} (hb : m₁.blocks b = m₂.blocks b)
    (path : List PathElem) (n : Int) : m₁.stride? (.loc b path) n = m₂.stride? (.loc b path) n := by
  unfold Mem.stride?; simp only [mem_elemPos?_loc_eq_of_blocks_eq hb]

theorem mem_stride?_loc_is_loc {m : Mem} {b : Nat} {path : List PathElem} {n : Int} {p' : Ptr}
    (h : m.stride? (.loc b path) n = some p') : ∃ q, p' = .loc b q := by
  unfold Mem.stride? at h
  rcases hep : m.elemPos? (.loc b path) with _ | ⟨b', pre, last, len⟩
  · rw [hep] at h; simp only at h
    split at h <;> first | exact ⟨path, (Option.some.inj h).symm⟩ | cases h
  · have hb' := mem_elemPos?_loc_fst hep; subst hb'
    rw [hep] at h; simp only at h
    split at h <;> first | exact ⟨_, (Option.some.inj h).symm⟩ | cases h

theorem lens?_loc_eq_of_blocks_eq {ctx : Ctx} {m₁ m₂ : Mem} {b : Nat} (hb : m₁.blocks b = m₂.blocks b)
    (e : Nat) (path : List PathElem) : ctx.lens? m₁ e (.loc b path) = ctx.lens? m₂ e (.loc b path) := by
  simp only [Ctx.lens?, hb]

theorem lens?_loc_fst {ctx : Ctx} {m : Mem} {e : Nat} {b : Nat} {path : List PathElem}
    {b' : Nat} {l : Lens} (h : ctx.lens? m e (.loc b path) = some (b', l)) : b' = b := by
  simp only [Ctx.lens?] at h
  rcases hmb : m.blocks b with _ | blk
  · rw [hmb] at h; cases h
  · rw [hmb] at h; simp only at h
    have finish (h0 : (match ctx.typeAt blk.ty path with
      | some t =>
        match ctx.sizedAt 32 t path e with
        | some pT => if (ctx.elemOf? blk.ty pT).isSome = true then some (b, Lens.elem pT) else some (b, Lens.one pT 0)
        | none =>
          match ctx.elemOf? blk.ty path with
          | some (base, s, len, i) => some (b, Lens.bytes base s len (i * s))
          | none => some (b, Lens.one path 0)
      | none => none) = some (b', l)) : b' = b := by
      rcases hta : ctx.typeAt blk.ty path with _ | t
      · rw [hta] at h0; cases h0
      · rw [hta] at h0; simp only at h0
        rcases hsa : ctx.sizedAt 32 t path e with _ | pT
        · rw [hsa] at h0; simp only at h0
          rcases heo : ctx.elemOf? blk.ty path with _ | ⟨base, s, len, i⟩ <;>
            (rw [heo] at h0; exact ((Prod.mk.inj (Option.some.inj h0)).1).symm)
        · rw [hsa] at h0; simp only at h0
          split at h0 <;> exact ((Prod.mk.inj (Option.some.inj h0)).1).symm
    rcases hsp : splitLast path with _ | ⟨pre, last⟩
    · rw [hsp] at h; exact finish h
    · rw [hsp] at h
      cases last with
      | idx _ => exact finish h
      | vel _ _ => exact finish h
      | byte k =>
        simp only at h
        rcases heo : ctx.elemOf? blk.ty pre with _ | ⟨base, s, len, i⟩ <;>
          (rw [heo] at h; simp only at h; split at h <;> first | exact ((Prod.mk.inj (Option.some.inj h)).1).symm | cases h)

theorem lensStride?_loc_eq_of_blocks_eq {ctx : Ctx} {m₁ m₂ : Mem} {b : Nat} (hb : m₁.blocks b = m₂.blocks b)
    (path : List PathElem) (n : Int) (e : Nat) :
    ctx.lensStride? m₁ (.loc b path) n e = ctx.lensStride? m₂ (.loc b path) n e := by
  unfold Ctx.lensStride?; split
  · rfl
  · simp only [lens?_loc_eq_of_blocks_eq hb]
    rcases hl : ctx.lens? m₂ e (.loc b path) with _ | ⟨b', l⟩ <;> try rfl
    have hb' := lens?_loc_fst hl; subst hb'
    cases l <;> simp only [mem_stride?_loc_eq_of_blocks_eq hb]

theorem stride?_loc_eq_of_blocks_eq {ctx : Ctx} {m₁ m₂ : Mem} {b : Nat} (hb : m₁.blocks b = m₂.blocks b)
    (path : List PathElem) (n : Int) (elemTy : Ty) :
    ctx.stride? m₁ (.loc b path) n elemTy = ctx.stride? m₂ (.loc b path) n elemTy := by
  unfold Ctx.stride? Ctx.sameUnits Ctx.elemTyOf? Ctx.charStride?
  simp only [hb, mem_stride?_loc_eq_of_blocks_eq hb, lensStride?_loc_eq_of_blocks_eq hb]

theorem stride?_loc_is_loc {ctx : Ctx} {m : Mem} {b : Nat} {path : List PathElem} {n : Int} {elemTy : Ty} {p' : Ptr}
    (h : ctx.stride? m (.loc b path) n elemTy = some p') : ∃ q, p' = .loc b q := by
  unfold Ctx.stride? at h; dsimp only at h
  generalize (if elemTy.isVoid = true then Ty.int false 8 else elemTy) = et at h
  split at h
  · exact mem_stride?_loc_is_loc h
  · split at h
    · unfold Ctx.charStride? at h; split at h
      · exact ⟨path, (Option.some.inj h).symm⟩
      · simp only at h
        rcases hmb : m.blocks b with _ | blk
        · rw [hmb] at h; cases h
        · rw [hmb] at h; simp only at h
          rcases hap : ctx.absPos? blk.ty path with _ | q0
          · rw [hap] at h; cases h
          · rw [hap] at h
            rcases hsa : ctx.sizeAlign 32 blk.ty with _ | ⟨s, al⟩
            · rw [hsa] at h; cases h
            · rw [hsa] at h; simp only at h
              split at h <;> first | exact ⟨_, (Option.some.inj h).symm⟩ | cases h
    · rcases hsa : ctx.sizeAlign 32 et with _ | ⟨e, al⟩
      · rw [hsa] at h; cases h
      · rw [hsa] at h; simp only at h
        unfold Ctx.lensStride? at h; split at h
        · exact ⟨path, (Option.some.inj h).symm⟩
        · rcases hl : ctx.lens? m e (.loc b path) with _ | ⟨b', l⟩
          · rw [hl] at h; cases h
          · have hb' := lens?_loc_fst hl; subst hb'
            rw [hl] at h
            cases l <;> simp only at h
            · exact mem_stride?_loc_is_loc h
            · split at h
              · exact ⟨_, (Option.some.inj h).symm⟩
              · split at h <;> first | exact ⟨_, (Option.some.inj h).symm⟩ | cases h
            · split at h <;> first | exact ⟨_, (Option.some.inj h).symm⟩ | cases h

theorem stride?_loc_of_records_nil {ctx : Ctx} {m : Mem} {b : Nat} {blk : MemBlock}
    (h : ctx.mod.records = []) (hp : ctx.mod.ptrBytes = 8)
    (hblk : m.blocks b = some blk) (path : List PathElem) (n : Int) (elemTy : Ty) :
    ctx.stride? m (.loc b path) n elemTy = (stridePath? b blk path n elemTy).map (Ptr.loc b) := by
  have hr : ∀ name, ctx.record? name = emptyCtx.record? name := by
    intro name
    have h1 : ctx.record? name = none := by simp [Ctx.record?, CIR.Module.findRecord?, h]
    have h2 : emptyCtx.record? name = none := rfl
    rw [h1, h2]
  have hp' : ctx.mod.ptrBytes = emptyCtx.mod.ptrBytes := hp
  rw [stride?_congr hr hp']
  have hb : m.blocks b = (Mem.empty.setBlock b blk).blocks b := by
    rw [hblk, Mem.setBlock_blocks_same]
  rw [stride?_loc_eq_of_blocks_eq hb]
  unfold stridePath?
  rcases hs : emptyCtx.stride? (Mem.empty.setBlock b blk) (.loc b path) n elemTy with _ | p'
  · rfl
  · obtain ⟨q, rfl⟩ := stride?_loc_is_loc hs
    rfl

def hasStridePathHyp (b blk path n elemTy : Expr) : MetaM Bool := do
  let target ← mkAppM ``stridePath? #[b, blk, path, n, elemTy]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some (_, lhs, _) := (← instantiateMVars d.type).eq? then
      if lhs.consumeMData == target then return true
  return false

simproc ↓ [cir_exec] reduceStrideCaller (Ctx.stride? _ _ (Ptr.loc _ _) _ _) := fun e => do
  unless e.isAppOfArity ``Ctx.stride? 5 do return .continue
  let a := e.getAppArgs
  let ctx := a[0]!; let m := a[1]!; let p := a[2]!; let n := a[3]!; let elemTy := a[4]!
  unless p.isAppOfArity ``Ptr.loc 2 do return .continue
  let b := p.getArg! 0; let path := p.getArg! 1
  unless b.isFVar do return .continue
  let lctx ← getLCtx
  let isCaller := lctx.any fun d =>
    !d.isImplementationDetail && d.userName.toString.startsWith "cirH_caller" &&
      d.type.consumeMData.isAppOfArity ``IsCaller 1 && d.type.consumeMData.appArg! == b
  unless isCaller do return .continue
  let lhsRec ← mkAppM ``CIR.Module.records #[← mkAppM ``Ctx.mod #[ctx]]
  let recs ← whnfD lhsRec
  unless recs.isAppOfArity ``List.nil 1 do return .continue
  let lhsPb ← mkAppM ``CIR.Module.ptrBytes #[← mkAppM ``Ctx.mod #[ctx]]
  let pb ← whnfD lhsPb
  unless pb.rawNatLit? == some 8 || pb.nat? == some 8 do return .continue
  let mb ← mkAppM ``Mem.blocks #[m, b]
  let (mbVal, hblk) ← simpEqOf mb
  unless mbVal.isAppOfArity ``Option.some 2 do return .continue
  let blk := mbVal.appArg!.consumeMData
  let hRec ← mkExpectedTypeHint (← mkEqRefl recs) (← mkEq lhsRec recs)
  let hPb ← mkExpectedTypeHint (← mkEqRefl pb) (← mkEq lhsPb pb)
  let pf ← mkAppOptM ``stride?_loc_of_records_nil
    #[some ctx, some m, some b, some blk, some hRec, some hPb, some hblk, some path, some n, some elemTy]
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  if ← hasStridePathHyp b blk path n elemTy then
    return .visit { expr := rhs, proof? := some pf }
  else
    return .done { expr := rhs, proof? := some pf }

def findPriorSetInt? (bval : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr × Expr)) := do
  let lctx ← getLCtx
  let mut setHyp : Option (Expr × Expr × Expr × Expr) := none
  for d in lctx do
    if d.isImplementationDetail then continue
    let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | continue
    let (lhs, rhs) := (lhs.consumeMData, rhs.consumeMData)
    unless rhs.isAppOfArity ``Option.some 2 && rhs.appArg!.consumeMData == bval do continue
    unless lhs.isAppOfArity ``Val.set? 3 do continue
    let w := (lhs.getArg! 2).consumeMData
    unless w.isAppOfArity ``Val.int 1 do continue
    setHyp := some (lhs.getArg! 0, lhs.getArg! 1, w.appArg!, d.toExpr)
    break
  let some (v0, q0, y, hs) := setHyp | return none
  for d in lctx do
    if d.isImplementationDetail then continue
    let some (_, lhs, rhs) := (← instantiateMVars d.type).eq? | continue
    let (lhs, rhs) := (lhs.consumeMData, rhs.consumeMData)
    unless lhs.isAppOfArity ``Val.get? 2 && lhs.getArg! 0 == v0 && lhs.getArg! 1 == q0 do continue
    unless rhs.isAppOfArity ``Option.some 2 do continue
    let a := rhs.appArg!.consumeMData
    unless a.isAppOfArity ``Val.int 1 do continue
    return some (v0, q0, a.appArg!, y, d.toExpr, hs)
  return none

def hasReachPathHyp (bty bval ty path : Expr) : MetaM Bool := do
  let target ← mkAppM ``reachPath? #[bty, bval, ty, path]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some (_, lhs, _) := (← instantiateMVars d.type).eq? then
      if lhs.consumeMData == target then return true
  return false

def reduceTypedAccessCaller (load : Bool) (e : Expr) : SimpM Lean.Meta.Simp.Step := do
  let n := if load then 4 else 5
  unless e.getAppNumArgs == n do return .continue
  let a := e.getAppArgs
  let ctx := a[0]!; let m := a[1]!; let ty := a[2]!; let p := a[3]!
  unless ty.isAppOfArity ``Ty.int 2 && p.isAppOfArity ``Ptr.loc 2 do
    return ← CIR.reduceTypedAccess load e
  let w := ty.getArg! 1
  unless w.rawNatLit? == some 32 || w.nat? == some 32 do
    return ← CIR.reduceTypedAccess load e
  let b := p.getArg! 0; let path := p.getArg! 1
  unless b.isFVar do return ← CIR.reduceTypedAccess load e
  let lctx ← getLCtx
  let isCaller := lctx.any fun d =>
    !d.isImplementationDetail && d.userName.toString.startsWith "cirH_caller" &&
      d.type.consumeMData.isAppOfArity ``IsCaller 1 && d.type.consumeMData.appArg! == b
  unless isCaller do return ← CIR.reduceTypedAccess load e
  let lhsRec ← mkAppM ``CIR.Module.records #[← mkAppM ``Ctx.mod #[ctx]]
  let recs ← whnfD lhsRec
  unless recs.isAppOfArity ``List.nil 1 do return ← CIR.reduceTypedAccess load e
  let lhsPb ← mkAppM ``CIR.Module.ptrBytes #[← mkAppM ``Ctx.mod #[ctx]]
  let pb ← whnfD lhsPb
  unless pb.rawNatLit? == some 8 || pb.nat? == some 8 do return ← CIR.reduceTypedAccess load e
  let mb ← mkAppM ``Mem.blocks #[m, b]
  let (mbVal, hblk) ← simpEqOf mb
  unless mbVal.isAppOfArity ``Option.some 2 do return ← CIR.reduceTypedAccess load e
  let blk := mbVal.appArg!.consumeMData
  unless blk.isAppOfArity ``MemBlock.mk 4 do return ← CIR.reduceTypedAccess load e
  let kind := blk.getArg! 0; let alive := blk.getArg! 1; let bty := blk.getArg! 2; let bval := blk.getArg! 3
  let hRec ← mkExpectedTypeHint (← mkEqRefl recs) (← mkEq lhsRec recs)
  let hPb ← mkExpectedTypeHint (← mkEqRefl pb) (← mkEq lhsPb pb)
  let s := ty.getArg! 0
  let mut baseVal := bval
  let pf ← if alive.isConstOf ``Bool.true then
      if load then
        mkAppOptM ``typedLoad_int32_alive_of_records_nil
          #[some ctx, some m, some s, some b, some path, some kind, some bty, some bval,
            some hRec, some hPb, some hblk]
      else
        if let some (v0, q0, x, y, hg, hs) ← findPriorSetInt? bval then
          baseVal := v0
          mkAppOptM ``typedStore_int32_alive_set_of_records_nil
            #[some ctx, some m, some s, some b, some path, some a[4]!, some kind, some bty,
              some v0, some bval, some q0, some x, some y, some hRec, some hPb, some hblk, some hg, some hs]
        else
          mkAppOptM ``typedStore_int32_alive_of_records_nil
            #[some ctx, some m, some s, some b, some path, some a[4]!, some kind, some bty, some bval,
              some hRec, some hPb, some hblk]
    else if alive.isConstOf ``Bool.false then
      if load then
        mkAppOptM ``typedLoad_int32_dead_of_records_nil
          #[some ctx, some m, some s, some b, some path, some kind, some bty, some bval,
            some hRec, some hPb, some hblk]
      else
        mkAppOptM ``typedStore_int32_dead_of_records_nil
          #[some ctx, some m, some s, some b, some path, some a[4]!, some kind, some bty, some bval,
            some hRec, some hPb, some hblk]
    else return ← CIR.reduceTypedAccess load e
  let some (_, _, rhs) := (← inferType pf).eq? | return .continue
  if alive.isConstOf ``Bool.true && (← hasReachPathHyp bty baseVal ty path) then
    return .visit { expr := rhs, proof? := some pf }
  else
    return .done { expr := rhs, proof? := some pf }

simproc ↓ [cir_exec] reduceTypedLoadCaller (Ctx.typedLoad _ _ _ _) := reduceTypedAccessCaller true
simproc ↓ [cir_exec] reduceTypedStoreCaller (Ctx.typedStore _ _ _ _ _) := reduceTypedAccessCaller false

end EquivLean.Cir

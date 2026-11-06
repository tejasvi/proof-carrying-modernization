import EquivLean.Bridge.Jimple.SpecAuto

/-!
# Calls in Java spec proofs

Additions to `SpecAuto.lean` for methods that call helpers (the CardDemo translations: `run`
calls a record formatter, which calls `zeroPad`/`fmtNum`, `fix`/`fit`, `spaces`):

* **Allocation-only callees.** A helper that builds its result in fresh objects leaves the
  caller's state as it was plus objects at the end of the heap: `σ' = allocs σ os`
  (`AllocOnly σ σ'`). Its exact form `strOut σ o t` (one scratch object `o`, then the result
  string `t` at `σ.next + 1`) keeps the caller's state explicit, so that the VC generator computes
  the caller's heap lookups after the call; `alloc_setObj_next`/`setObj_setObj` normalize a
  helper's own loop state to that form. A contract proved with a hidden `AllocOnly` frame gives
  the callers' `Grows`/`inits`/`statics` frame (`grows_of_allocOnly`, `inits_of_allocOnly`, …).
* **Closers.** `jclose [lemmas]` on the goals `jvc` leaves: the frame facts (`Grows`, `InitMono`,
  `AllocOnly`, also through `allocs`; compared syntactically, never by unifying state terms, which
  is slow on long allocation chains), a call's precondition, heap lookups after an
  allocation-only call, index arithmetic, then `simp` with the extra lemmas (side conditions by
  `jomega`).

Contracts of static helpers: JimpleLean's `jcontract_ok [h]`.
-/
open Jimple

namespace EquivLean.Jimple.Spec

/-! ## Callees that only allocate

A helper that builds its result in fresh objects (a `StringBuilder`, a `char[]`, the result
string) leaves the caller's state as it was, plus objects at the end of the heap: its contract
says `AllocOnly σ σ'`, i.e. `σ' = allocs σ os`. After the call, the caller's heap lookups of older
objects compute (`heap_allocs_lt`), and its frame facts follow (`grows_allocs_of`, …). -/

/-- `σ` with the objects `os` allocated, in order. -/
def allocs (σ : State) (os : List Obj) : State := os.foldl (fun σ o => (σ.alloc o).2) σ

@[simp] theorem allocs_nil (σ : State) : allocs σ [] = σ := rfl
theorem allocs_cons (σ : State) (o : Obj) (os : List Obj) :
    allocs σ (o :: os) = allocs (σ.alloc o).2 os := rfl
theorem allocs_append (σ : State) (os ps : List Obj) :
    allocs σ (os ++ ps) = allocs (allocs σ os) ps := by
  simp [allocs, List.foldl_append]
theorem alloc_allocs (σ : State) (os : List Obj) (o : Obj) :
    ((allocs σ os).alloc o).2 = allocs σ (os ++ [o]) := by
  rw [allocs_append]; rfl
theorem allocs_eq (σ : State) (os : List Obj) :
    allocs σ os = { σ with mem := σ.mem ++ os.toArray } := by
  induction os generalizing σ with
  | nil => simp
  | cons o os ih =>
    rw [allocs_cons, ih]
    simp [State.alloc]
@[jsimp] theorem next_allocs (σ : State) (os : List Obj) : (allocs σ os).next = σ.next + os.length := by
  rw [allocs_eq]; simp [State.next]
theorem heap_allocs_lt {σ : State} {x : Addr} (os : List Obj) (h : x < σ.next) :
    (allocs σ os).heap x = σ.heap x := by
  rw [allocs_eq]; simp only [State.heap, State.next] at *
  rw [Array.getElem?_append_left h]
@[jsimp] theorem initOf_allocs (σ : State) (os : List Obj) (c : ClassName) :
    (allocs σ os).initOf c = σ.initOf c := by
  rw [allocs_eq]; rfl
@[jsimp] theorem static_allocs (σ : State) (os : List Obj) (k : FieldKey) :
    (allocs σ os).static k = σ.static k := by
  rw [allocs_eq]; rfl
theorem allocs_setObj_of_le {σ : State} {os : List Obj} {a : Addr} {o : Obj} (ha : σ.next ≤ a) :
    (allocs σ os).setObj a o = allocs σ (os.set (a - σ.next) o) := by
  rw [allocs_eq, allocs_eq]
  simp only [State.setObj, State.next] at *
  congr 1
  apply Array.ext'
  simp only [Array.toList_setIfInBounds, Array.toList_append]
  rw [List.set_append_right _ _ (by simpa using ha)]
  simp

/-- Updating the object just allocated is allocating the update. -/
theorem alloc_setObj_next (σ : State) (o o' : Obj) :
    (σ.alloc o).2.setObj σ.next o' = (σ.alloc o').2 := by
  simp only [State.alloc, State.setObj, State.next]
  congr 1
  apply Array.ext'
  simp [Array.toList_setIfInBounds]

/-- The same, for the second object of two just allocated (the address in `jvc`'s normal form). -/
theorem alloc_alloc_setObj_next (σ : State) (o1 o2 o' : Obj) :
    ((σ.alloc o1).2.alloc o2).2.setObj (σ.next + 1) o' = ((σ.alloc o1).2.alloc o').2 := by
  rw [← State.next_alloc σ o1]; exact alloc_setObj_next _ _ _

theorem setObj_setObj (σ : State) (a : Addr) (o o' : Obj) :
    (σ.setObj a o).setObj a o' = σ.setObj a o' := by
  simp only [State.setObj]
  congr 1
  apply Array.ext'
  simp [Array.toList_setIfInBounds]

/-- The state after a helper that allocates one scratch object `o` (its `StringBuilder` or
`char[]`, in its final state) and then its result string `t` (at `σ.next + 1`): the exact
post-state of `spaces`/`fix`/`fmtNum`-like helpers, so that a caller's heap lookups compute. -/
def strOut (σ : State) (o : Obj) (t : JStr) : State := ((σ.alloc o).2.alloc (.str t)).2

/-- `σ'` is `σ` with objects allocated (no other change). -/
def AllocOnly (σ σ' : State) : Prop := ∃ os, σ' = allocs σ os

theorem allocOnly_refl (σ : State) : AllocOnly σ σ := ⟨[], rfl⟩
theorem allocOnly_alloc_of {σ0 σ : State} (o : Obj) (h : AllocOnly σ0 σ) :
    AllocOnly σ0 (σ.alloc o).2 := by
  obtain ⟨os, rfl⟩ := h; exact ⟨os ++ [o], alloc_allocs σ0 os o⟩
theorem allocOnly_allocs_of {σ0 σ : State} (ps : List Obj) (h : AllocOnly σ0 σ) :
    AllocOnly σ0 (allocs σ ps) := by
  obtain ⟨os, rfl⟩ := h; exact ⟨os ++ ps, (allocs_append σ0 os ps).symm⟩
theorem allocOnly_setObj_of {σ0 σ : State} {a : Addr} {o : Obj} (h : AllocOnly σ0 σ)
    (ha : σ0.next ≤ a) : AllocOnly σ0 (σ.setObj a o) := by
  obtain ⟨os, rfl⟩ := h; exact ⟨_, allocs_setObj_of_le ha⟩
theorem allocOnly_trans {σ1 σ2 σ3 : State} (h1 : AllocOnly σ1 σ2) (h2 : AllocOnly σ2 σ3) :
    AllocOnly σ1 σ3 := by
  obtain ⟨os, rfl⟩ := h1; obtain ⟨ps, rfl⟩ := h2; exact ⟨os ++ ps, (allocs_append σ1 os ps).symm⟩
theorem grows_of_allocOnly {σ σ' : State} (h : AllocOnly σ σ') : Grows σ σ' := by
  obtain ⟨os, rfl⟩ := h
  refine ⟨?_, fun x hx => heap_allocs_lt os hx⟩
  rw [next_allocs]; exact Nat.le_add_right _ _
theorem grows_allocs_of {σ0 σ : State} (os : List Obj) (h : Grows σ0 σ) : Grows σ0 (allocs σ os) :=
  grows_trans h (grows_of_allocOnly ⟨os, rfl⟩)
theorem strOfV_allocs_of {σ : State} {v : Value} {s : JStr} (os : List Obj)
    (h : strOfV σ v = some s) : strOfV (allocs σ os) v = some s := by
  cases v with
  | ref x =>
    simp only [strOfV] at h ⊢
    have hx : x < σ.next := by
      cases hh : σ.heap x with
      | none => rw [hh] at h; cases h
      | some o => exact State.lt_next_of_heap hh
    rw [heap_allocs_lt os hx]; exact h
  | _ => simp [strOfV] at h

theorem strsOf_allocs_of {σ : State} {vs : List Value} {ss : List JStr} (os : List Obj)
    (h : strsOf σ vs = some ss) : strsOf (allocs σ os) vs = some ss :=
  strsOf_mono (fun _ _ => strOfV_allocs_of os) h

theorem inits_of_allocOnly {σ σ' : State} (h : AllocOnly σ σ') : σ'.inits = σ.inits := by
  obtain ⟨os, rfl⟩ := h; rw [allocs_eq]

theorem statics_of_allocOnly {σ σ' : State} (h : AllocOnly σ σ') : σ'.statics = σ.statics := by
  obtain ⟨os, rfl⟩ := h; rw [allocs_eq]

theorem initMono_allocs_of {σ0 σ : State} (os : List Obj) (h : InitMono σ0 σ) :
    InitMono σ0 (allocs σ os) := fun c hc => by rw [initOf_allocs]; exact h c hc

theorem initMono_of_allocOnly {σ σ' : State} (h : AllocOnly σ σ') : InitMono σ σ' := by
  obtain ⟨os, rfl⟩ := h; exact initMono_allocs_of os (initMono_refl σ)

/-! ## Ranges of machine integers -/

theorem i32_toInt_le (x : I32) : x.toInt ≤ 2147483647 := by
  have := @BitVec.toInt_lt 32 x; simp at this; omega
theorem i32_toInt_ge (x : I32) : -2147483648 ≤ x.toInt := by
  have := @BitVec.le_toInt 32 x; simp at this; omega
theorem i64_toInt_le (x : I64) : x.toInt ≤ 9223372036854775807 := by
  have := @BitVec.toInt_lt 64 x; simp at this; omega
theorem i64_toInt_ge (x : I64) : -9223372036854775808 ≤ x.toInt := by
  have := @BitVec.le_toInt 64 x; simp at this; omega

open Lean Meta Elab Tactic in
/-- The ranges of the `int`/`long` variables of the context (`omega` does not know them). -/
elab "jbv_bounds" : tactic => withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    let w := if ty.isAppOfArity ``BitVec 1 then (ty.getArg! 0).nat? else none
    let lems := match w with
      | some 32 => [``i32_toInt_le, ``i32_toInt_ge]
      | some 64 => [``i64_toInt_le, ``i64_toInt_ge]
      | _ => []
    for l in lems do
      let pf := mkApp (mkConst l) d.toExpr
      let (_, g') ← (← g.assert `hbv (← inferType pf) pf).intro1P
      g := g'
  replaceMainGoal [g]

/-! ## Closers -/

open Lean Meta in
/-- `stateStep?`, and `allocs σ os`. -/
def stateStepA? (τ : Lean.Expr) : Option (Name × Lean.Expr) :=
  let τ := τ.consumeMData
  if τ.isAppOfArity ``allocs 2 then some (``allocs, τ.getArg! 0) else stateStep? τ

open Lean Meta in
/-- Close `g` with a hypothesis whose type is syntactically the goal, or with `refl` applied to a
goal `R σ σ` (no unification: unifying large state terms is slow). -/
def closeSyntactic (g : MVarId) (refl : Name) : MetaM Bool := g.withContext do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  if t.getAppNumArgs ≥ 2 && t.getArg! (t.getAppNumArgs - 2) == t.getArg! (t.getAppNumArgs - 1) then
    let x := t.getArg! (t.getAppNumArgs - 1)
    g.assign (← if refl == ``Eq.refl then mkEqRefl x
      else pure (mkApp (← mkConstWithFreshMVarLevels refl) x))
    return true
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).consumeMData == t then
      g.assign d.toExpr
      return true
  return false

open Lean Meta Elab Tactic in
/-- `jgrowsCore`, also through `allocs`. -/
partial def jgrowsCoreA (g : MVarId) : TacticM Unit := do
  setGoals [g]
  if ← closeSyntactic g ``grows_refl then return
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``Grows 2 do throwError "jgrowsA: not `Grows σ0 τ`: {t}"
  let next (lem : Name) : TacticM Unit := do
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels lem) | throwError "jgrowsA: {lem}"
    jgrowsCoreA g'
  match stateStepA? (t.getArg! 1) with
  | some (``State.alloc, _) => next ``grows_alloc_of
  | some (``allocs, _) => next ``grows_allocs_of
  | some (``State.setInit, _) => next ``grows_setInit_of
  | some (``State.setStatic, _) => next ``grows_setStatic_of
  | some (``State.setObj, _) =>
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``grows_setObj_of)
    let [gg, ghl] := gs | throwError "jgrowsA: setObj goals {gs.length}"
    setGoals [ghl]
    evalTactic (← `(tactic| first | jomega | (simp only [State.next_alloc, State.next_setObj,
      State.next_setInit, State.next_setStatic, next_allocs]; jomega)))
    jgrowsCoreA gg
  | _ => throwError "jgrowsA: no hypothesis for {t}"

open Lean Elab Tactic in
/-- `Grows σ0 τ` (`jgrowsCoreA`). -/
elab "jgrowsA" : tactic => do jgrowsCoreA (← getMainGoal)

open Lean Meta Elab Tactic in
/-- `jinitMonoCore`, also through `allocs`. -/
partial def jinitMonoCoreA (g : MVarId) : TacticM Unit := do
  setGoals [g]
  if ← closeSyntactic g ``initMono_refl then return
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``InitMono 2 do throwError "jinit_monoA: not `InitMono σ0 τ`: {t}"
  let next (lem : Name) : TacticM Unit := do
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels lem) | throwError "jinit_monoA: {lem}"
    jinitMonoCoreA g'
  match stateStepA? (t.getArg! 1) with
  | some (``State.alloc, _) => next ``initMono_alloc_of
  | some (``allocs, _) => next ``initMono_allocs_of
  | some (``State.setObj, _) => next ``initMono_setObj_of
  | some (``State.setStatic, _) => next ``initMono_setStatic_of
  | some (``State.setInit, _) => next ``initMono_setInit_done_of
  | _ => throwError "jinit_monoA: no hypothesis for {t}"

open Lean Elab Tactic in
/-- `InitMono σ0 τ` (`jinitMonoCoreA`). -/
elab "jinit_monoA" : tactic => do jinitMonoCoreA (← getMainGoal)

open Lean Meta Elab Tactic in
/-- `jstrsOfFrameCore`, also through `allocs`. -/
partial def jstrsOfFrameCoreA (g : MVarId) : TacticM Unit := do
  setGoals [g]
  if ← closeSyntactic g ``Eq.refl then return
  let t := (← instantiateMVars (← g.getType)).consumeMData
  let some τ := (do
      guard (t.isAppOfArity ``Eq 3)
      let l := t.getArg! 1
      guard (l.isAppOfArity ``strsOf 2)
      pure (l.getArg! 0)) | throwError "jstrs_frameA: not `strsOf σ vs = some ss`: {t}"
  let next (lem : Name) : TacticM Unit := do
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels lem) | throwError "jstrs_frameA: {lem}"
    jstrsOfFrameCoreA g'
  match stateStepA? τ with
  | some (``State.alloc, _) => next ``strsOf_alloc_of
  | some (``allocs, _) => next ``strsOf_allocs_of
  | some (``State.setInit, _) => next ``strsOf_setInit_of
  | some (``State.setObj, _) =>
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``strsOf_setObj_of)
    let [ghl, gh] := gs | throwError "jstrs_frameA: setObj goals {gs.length}"
    setGoals [ghl]
    evalTactic (← `(tactic| intro t))
    addrSide
    unless (← getGoals).isEmpty do throwError "jstrs_frameA: side condition not closed"
    jstrsOfFrameCoreA gh
  | _ => throwError "jstrs_frameA: no hypothesis for {t}"

open Lean Elab Tactic in
/-- `strsOf τ vs = some ss` (`jstrsOfFrameCoreA`). -/
elab "jstrs_frameA" : tactic => do jstrsOfFrameCoreA (← getMainGoal)

open Lean Meta Elab Tactic in
/-- `AllocOnly σ0 τ` from `AllocOnly σ0 σ` (a hypothesis) for `τ` built from `σ` by allocations
and updates of objects allocated after `σ0`. -/
partial def jallocOnlyCore (g : MVarId) : TacticM Unit := do
  setGoals [g]
  if ← closeSyntactic g ``allocOnly_refl then return
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``AllocOnly 2 do throwError "jalloc_only: not `AllocOnly σ0 τ`: {t}"
  match stateStepA? (t.getArg! 1) with
  | some (``State.alloc, _) =>
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``allocOnly_alloc_of) | throwError "jalloc_only: alloc"
    jallocOnlyCore g'
  | some (``allocs, _) =>
    let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``allocOnly_allocs_of) | throwError "jalloc_only: allocs"
    jallocOnlyCore g'
  | some (``State.setObj, _) =>
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``allocOnly_setObj_of)
    let [gg, ghl] := gs | throwError "jalloc_only: setObj goals {gs.length}"
    setGoals [ghl]
    evalTactic (← `(tactic| first | jomega | (simp only [State.next_alloc, State.next_setObj, next_allocs]; jomega)))
    jallocOnlyCore gg
  | _ => throwError "jalloc_only: no hypothesis for {t}"

open Lean Elab Tactic in
/-- `AllocOnly σ0 τ` (`jallocOnlyCore`). -/
elab "jalloc_only" : tactic => do jallocOnlyCore (← getMainGoal)

/-- The closers on the goals left by `jvc` in a helper's or a caller's proof (see the module
docstring); the extra lemmas are rewrites whose side conditions `jomega` closes. Goals it cannot
close are left for the caller. -/
syntax "jclose" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| jclose) => `(tactic| jclose [List.replicate_succ'])
  | `(tactic| jclose [$ls,*]) => `(tactic| (
    all_goals (try simp only [EquivLean.Jimple.Spec.hide_iff] at *)
    all_goals try first
      | done
      | exact True.intro
      | jgrowsA
      | jinit_monoA
      | jalloc_only
      | jomega
      | (simp (disch := (simp only [State.next_alloc, State.next_setObj,
            EquivLean.Jimple.Spec.next_allocs]; jomega)) only
          [EquivLean.Jimple.Spec.heap_allocs_lt, State.heap_alloc, State.heap_setObj,
           State.next_alloc, State.next_setObj, EquivLean.Jimple.Spec.next_allocs, ite_true,
           ite_false, eq_self_iff_true, Nat.lt_add_one, *]
         done)
      | (simp only [and_assoc, exists_eq_left', exists_eq_left, exists_and_left, exists_prop,
           true_and]
         simp (disch := jomega) [State.heap_alloc, State.heap_setObj, *]
         done)
      | (jbv_bounds
         simp (disch := jomega) only [Jimple.bmod32_of_bounds, Jimple.bmod64_of_bounds,
           Jimple.int_toNat_add_one, Jimple.bv32_toInt_ofNat_of_lt, List.append_assoc,
           dite_eq_ite, dite_eq_left, dite_eq_right, $ls,*]
         try jomega
         done)
      | (jbv_bounds
         simp (disch := jomega) only [Jimple.bmod32_of_bounds, Jimple.bmod64_of_bounds,
           Jimple.int_toNat_add_one, Jimple.bv32_toInt_ofNat_of_lt, $ls,*] at *
         jomega)
      | (simp_all; done)))

end EquivLean.Jimple.Spec

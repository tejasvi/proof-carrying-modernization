/-
StrictTS proof layer: what a caller observes.

The definitions and lemmas of this file are copied, with their names, from equiv-lean's
`EquivLean/Bridge/TS/Obs.lean` (stated there against StrictTS a15926a; `World` is unchanged
since), so that the two stay comparable; only `Sim`, `Equiv` and `EquivOn` are specialised from
equiv-lean's `Behaves` classes to runs `Option (Out TT α)` (equiv-lean's `Option` instance:
`Runs x o := x = some o`, `Safe x := x.isSome`; the formulas are the same).

`JS.exec m₁ w = JS.exec m₂ w` compares whole final worlds, allocation counter and unreachable
cells included. A caller observes less:

* `WorldObs n w₁ w₂`: the console output, every heap cell at an address below `n` (the caller's
  allocation counter `w.next` at the call: everything the caller can hold a reference to), and
  the positions of the three oracles (`OracleIdx`: how many answers of `Math.random()`,
  `Date.now()` and external calls were consumed). Cells at addresses `≥ n` were allocated by the
  callee and are invisible unless the result refers to them; `next` itself is not observable.
  Not compared: the asynchronous state (microtask queue, timers, unhandled rejections), so these
  relations are meant for callees that schedule no asynchronous work.
* `ObsEq n o₁ o₂`: equal completions (value, thrown exception, or panic) and `WorldObs n`; the
  right notion for results that carry no fresh reference.
* `ArrObs n o₁ o₂`, equivalence modulo fresh allocation for functions that return an array:
  `WorldObs n`, and the two results are the same caller array, or two fresh arrays (addresses
  `≥ n`, not necessarily equal) with equal contents. For element types without references it is
  an observational equivalence.

The `@[simp]` lemmas at the end (`equiv_some_some`, `obsEq_iff`, `worldObs_iff`,
`heapObs_insert_left`, …) reduce these relations on symbolic runs to equalities of values and of
caller cells, the form `ts_auto` closes.
-/
import StrictTS.Proof.Exec

namespace StrictTS.Obs
open StrictTS

variable {TT : TypeTable} {α β : Type}

/-- The outcome of a run: a completion and the final world. -/
abbrev Out (TT : TypeTable) (α : Type) := Except Exc α × World TT

/-! ## Runs as computations (equiv-lean `Sim` / `Equiv` / `EquivOn`, for `Option`) -/

/-- `t` simulates `s` up to `R`: if `s` finishes, `t` finishes, with a related outcome. -/
def Sim (R : Out TT α → Out TT β → Prop) (t : Option (Out TT α)) (s : Option (Out TT β)) : Prop :=
  s.isSome → t.isSome ∧ ∀ ot, t = some ot → ∃ os, s = some os ∧ R ot os

/-- Simulation in both directions: the same runs finish and the outcomes correspond. -/
def Equiv (R : Out TT α → Out TT β → Prop) (t : Option (Out TT α)) (s : Option (Out TT β)) : Prop :=
  Sim R t s ∧ Sim (fun os ot => R ot os) s t

/-- Equivalence on every input outside `Bad`. -/
def EquivOn {X : Type} (Bad : X → Prop) (R : Out TT α → Out TT β → Prop) (f : X → Option (Out TT α))
    (g : X → Option (Out TT β)) : Prop :=
  ∀ x, ¬ Bad x → Equiv R (f x) (g x)

@[simp] theorem equiv_some_some (R : Out TT α → Out TT β → Prop) (o₁ : Out TT α) (o₂ : Out TT β) :
    Equiv R (some o₁) (some o₂) ↔ R o₁ o₂ := by
  simp [Equiv, Sim]

@[simp] theorem equiv_none_none (R : Out TT α → Out TT β → Prop) :
    Equiv R (none : Option (Out TT α)) (none : Option (Out TT β)) := by
  simp [Equiv, Sim]

@[simp] theorem equiv_some_none (R : Out TT α → Out TT β → Prop) (o₁ : Out TT α) :
    Equiv R (some o₁) (none : Option (Out TT β)) ↔ False := by
  simp [Equiv, Sim]

@[simp] theorem equiv_none_some (R : Out TT α → Out TT β → Prop) (o₂ : Out TT β) :
    Equiv R (none : Option (Out TT α)) (some o₂) ↔ False := by
  simp [Equiv, Sim]

theorem Equiv.mono {R R' : Out TT α → Out TT β → Prop} {t : Option (Out TT α)} {s : Option (Out TT β)}
    (h : Equiv R t s) (hR : ∀ a b, R a b → R' a b) : Equiv R' t s := by
  rcases t with _ | a <;> rcases s with _ | b <;> simp_all

/-! ## Caller-visible state -/

/-- The worlds have consumed the same number of answers of each oracle (`Math.random()`,
`Date.now()`, external calls). The oracles answer by position, so this is what a caller sees
of them afterwards. -/
def OracleIdx (w₁ w₂ : World TT) : Prop :=
  w₁.randIdx = w₂.randIdx ∧ w₁.nowIdx = w₂.nowIdx ∧ w₁.extIdx = w₂.extIdx

theorem OracleIdx.refl (w : World TT) : OracleIdx w w := ⟨rfl, rfl, rfl⟩

theorem OracleIdx.symm {w₁ w₂ : World TT} (h : OracleIdx w₁ w₂) : OracleIdx w₂ w₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem OracleIdx.trans {w₁ w₂ w₃ : World TT} (h₁ : OracleIdx w₁ w₂) (h₂ : OracleIdx w₂ w₃) :
    OracleIdx w₁ w₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩

/-- The worlds agree on what a caller that allocated the addresses below `n` can observe. -/
def WorldObs (n : Nat) (w₁ w₂ : World TT) : Prop :=
  w₁.out = w₂.out ∧ (∀ k a, a < n → w₁.heap.get? (k, a) = w₂.heap.get? (k, a)) ∧
    OracleIdx w₁ w₂

theorem WorldObs.refl (n : Nat) (w : World TT) : WorldObs n w w :=
  ⟨rfl, fun _ _ _ => rfl, OracleIdx.refl w⟩

theorem WorldObs.symm {n : Nat} {w₁ w₂ : World TT} (h : WorldObs n w₁ w₂) : WorldObs n w₂ w₁ :=
  ⟨h.1.symm, fun k a ha => (h.2.1 k a ha).symm, h.2.2.symm⟩

theorem WorldObs.trans {n : Nat} {w₁ w₂ w₃ : World TT} (h₁ : WorldObs n w₁ w₂)
    (h₂ : WorldObs n w₂ w₃) : WorldObs n w₁ w₃ :=
  ⟨h₁.1.trans h₂.1, fun k a ha => (h₁.2.1 k a ha).trans (h₂.2.1 k a ha), h₁.2.2.trans h₂.2.2⟩

theorem WorldObs.mono {n m : Nat} {w₁ w₂ : World TT} (h : WorldObs n w₁ w₂) (hm : m ≤ n) :
    WorldObs m w₁ w₂ :=
  ⟨h.1, fun k a ha => h.2.1 k a (Nat.lt_of_lt_of_le ha hm), h.2.2⟩

/-- Allocating or writing at a fresh address is invisible. -/
theorem WorldObs.insert_fresh {n : Nat} {w₁ w₂ : World TT} (h : WorldObs n w₁ w₂) {k : HKind}
    {b : Nat} (c : k.Cell TT) (hb : n ≤ b) :
    WorldObs n { w₁ with heap := w₁.heap.insert (k, b) c } w₂ := by
  refine ⟨h.1, fun k' a ha => ?_, h.2.2⟩
  rw [JS.heap_get_insert_addr_ne _ _ _ _ (by omega)]
  exact h.2.1 k' a ha

/-- An external call made by both sides (the same answer is consumed). -/
theorem WorldObs.extIdx_succ {n : Nat} {w₁ w₂ : World TT} (h : WorldObs n w₁ w₂) :
    WorldObs n { w₁ with extIdx := w₁.extIdx + 1 } { w₂ with extIdx := w₂.extIdx + 1 } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, congrArg (· + 1) h.2.2.2.2⟩

/-- A different number of external calls is observable. -/
theorem WorldObs.extIdx_eq {n : Nat} {w₁ w₂ : World TT} (h : WorldObs n w₁ w₂) :
    w₁.extIdx = w₂.extIdx :=
  h.2.2.2.2

theorem WorldObs.next_irrel {n : Nat} {w₁ w₂ : World TT} (h : WorldObs n w₁ w₂) (m : Nat) :
    WorldObs n { w₁ with next := m } w₂ := h

/-! ## Outcomes without fresh references -/

/-- Same observable outcome: equal completion and caller-visible state. -/
def ObsEq (n : Nat) (o₁ o₂ : Out TT α) : Prop := o₁.1 = o₂.1 ∧ WorldObs n o₁.2 o₂.2

theorem ObsEq.of_eq {n : Nat} {o₁ o₂ : Out TT α} (h : o₁ = o₂) : ObsEq n o₁ o₂ :=
  h ▸ ⟨rfl, WorldObs.refl n o₁.2⟩

theorem ObsEq.symm {n : Nat} {o₁ o₂ : Out TT α} (h : ObsEq n o₁ o₂) : ObsEq n o₂ o₁ :=
  ⟨h.1.symm, h.2.symm⟩

/-- Equal outcomes are observably equal. -/
theorem Equiv.toObsEq {m₁ m₂ : JS TT α} {w₁ w₂ : World TT} (n : Nat)
    (h : Equiv (· = ·) (JS.exec m₁ w₁) (JS.exec m₂ w₂)) :
    Equiv (ObsEq n) (JS.exec m₁ w₁) (JS.exec m₂ w₂) :=
  h.mono fun _ _ e => ObsEq.of_eq e

/-! ## Equivalence modulo fresh allocation (array results) -/

/-- Two array results agree up to fresh allocation: equal caller-visible state, and the same
caller array, or two fresh arrays with equal contents. -/
def ArrObs (n : Nat) {t : Ty} (o₁ o₂ : Out TT (Val TT (.arr t))) : Prop :=
  WorldObs n o₁.2 o₂.2 ∧
    match o₁.1, o₂.1 with
    | .ok v₁, .ok v₂ =>
      (v₁.arrAddr = v₂.arrAddr ∧ v₁.arrAddr < n) ∨
      (n ≤ v₁.arrAddr ∧ n ≤ v₂.arrAddr ∧ ∃ xs,
        o₁.2.heap.get? (.arr t, v₁.arrAddr) = some xs ∧ o₂.2.heap.get? (.arr t, v₂.arrAddr) = some xs)
    | .error e₁, .error e₂ => e₁ = e₂
    | _, _ => False

theorem ArrObs.symm {n : Nat} {t : Ty} {o₁ o₂ : Out TT (Val TT (.arr t))} (h : ArrObs n o₁ o₂) :
    ArrObs n o₂ o₁ := by
  obtain ⟨hw, hr⟩ := h
  refine ⟨hw.symm, ?_⟩
  rcases o₁ with ⟨_ | v₁, w₁⟩ <;> rcases o₂ with ⟨_ | v₂, w₂⟩ <;> simp only at hr ⊢
  · exact hr.symm
  · rcases hr with ⟨he, hlt⟩ | ⟨h₁, h₂, xs, hx₁, hx₂⟩
    · exact .inl ⟨he.symm, he ▸ hlt⟩
    · exact .inr ⟨h₂, h₁, xs, hx₂, hx₁⟩

/-- Two runs that return fresh arrays with the same contents and leave the caller's cells and
console as in `w` are equivalent modulo fresh allocation (the usual way to prove `ArrObs`:
one functional specification per side). -/
theorem arrObs_of_specs {n : Nat} {t : Ty} {w : World TT} {a₁ a₂ : Nat} {w₁ w₂ : World TT}
    {xs : Array (Val TT t)} (hw₁ : WorldObs n w₁ w) (hw₂ : WorldObs n w₂ w) (h₁ : n ≤ a₁)
    (h₂ : n ≤ a₂) (hx₁ : w₁.heap.get? (.arr t, a₁) = some xs)
    (hx₂ : w₂.heap.get? (.arr t, a₂) = some xs) :
    ArrObs n ((.ok (.arr a₁), w₁) : Out TT (Val TT (.arr t))) (.ok (.arr a₂), w₂) :=
  ⟨hw₁.trans hw₂.symm, .inr ⟨h₁, h₂, xs, hx₁, hx₂⟩⟩

/-- `ArrObs` between two computations with known runs. -/
theorem equiv_arrObs_of_runs {t : Ty} {n : Nat} {m₁ m₂ : JS TT (Val TT (.arr t))}
    {w : World TT} {o₁ o₂ : Out TT (Val TT (.arr t))} (h₁ : JS.exec m₁ w = some o₁)
    (h₂ : JS.exec m₂ w = some o₂) (h : ArrObs n o₁ o₂) :
    Equiv (ArrObs n) (JS.exec m₁ w) (JS.exec m₂ w) := by
  rw [h₁, h₂]
  exact (equiv_some_some _ _ _).2 h

/-! ## Encoding-level `EquivOn` -/

/-- Two translated functions (of programs `P₁`, `P₂` over the same type table) are equivalent,
observed by a caller, on every input `(vs, w)` outside `Bad`. -/
def TSEquivOn (I : Impl) (P₁ P₂ : Program TT) {args : Tys} {ret : Ty} (f₁ f₂ : FunRef args ret)
    (Bad : Vals TT args.toList × World TT → Prop) : Prop :=
  ∀ vs w, ¬ Bad (vs, w) → Equiv (ObsEq w.next) (JS.exec (callFun I P₁ f₁ vs) w) (JS.exec (callFun I P₂ f₂ vs) w)

theorem tsEquivOn_of_equivOn (I : Impl) (P₁ P₂ : Program TT) {args : Tys} {ret : Ty}
    (f₁ f₂ : FunRef args ret) (Bad : Vals TT args.toList × World TT → Prop)
    (h : EquivOn Bad (· = ·) (fun x => JS.exec (callFun I P₁ f₁ x.1) x.2)
      (fun x => JS.exec (callFun I P₂ f₂ x.1) x.2)) :
    TSEquivOn I P₁ P₂ f₁ f₂ Bad :=
  fun vs w hb => Equiv.toObsEq w.next (h (vs, w) hb)

/-! ## `simp` normal forms (not in equiv-lean): the relations on symbolic runs

After symbolic execution both runs are `some (completion, world)`; these lemmas turn the
relations into equalities of completions and of the caller's cells. Writes at addresses at least
`n` (fresh cells) drop out of the comparison (`heapObs_insert_left` and `_right`, whose side
condition `n ≤ b` `simp` proves for `b = w.next + k`). -/

/-- The caller's cells: those below `n`. -/
def HeapObs (n : Nat) (h₁ h₂ : Heap TT) : Prop := ∀ k a, a < n → h₁.get? (k, a) = h₂.get? (k, a)

@[simp] theorem worldObs_iff (n : Nat) (w₁ w₂ : World TT) :
    WorldObs n w₁ w₂ ↔ w₁.out = w₂.out ∧ HeapObs n w₁.heap w₂.heap ∧
      (w₁.randIdx = w₂.randIdx ∧ w₁.nowIdx = w₂.nowIdx ∧ w₁.extIdx = w₂.extIdx) := Iff.rfl

@[simp] theorem heapObs_refl (n : Nat) (h : Heap TT) : HeapObs n h h ↔ True :=
  ⟨fun _ => trivial, fun _ _ _ _ => rfl⟩

@[simp] theorem heapObs_insert_left (n : Nat) (h₁ h₂ : Heap TT) {k : HKind} {b : Nat} (c : k.Cell TT)
    (hb : n ≤ b) : HeapObs n (h₁.insert (k, b) c) h₂ ↔ HeapObs n h₁ h₂ := by
  constructor
  · intro h k' a ha
    rw [← h k' a ha, JS.heap_get_insert_addr_ne _ _ _ _ (by omega)]
  · intro h k' a ha
    rw [JS.heap_get_insert_addr_ne _ _ _ _ (by omega)]
    exact h k' a ha

@[simp] theorem heapObs_insert_right (n : Nat) (h₁ h₂ : Heap TT) {k : HKind} {b : Nat} (c : k.Cell TT)
    (hb : n ≤ b) : HeapObs n h₁ (h₂.insert (k, b) c) ↔ HeapObs n h₁ h₂ := by
  constructor
  · intro h k' a ha
    rw [h k' a ha, JS.heap_get_insert_addr_ne _ _ _ _ (by omega)]
  · intro h k' a ha
    rw [JS.heap_get_insert_addr_ne _ _ _ _ (by omega)]
    exact h k' a ha

@[simp] theorem obsEq_iff (n : Nat) (o₁ o₂ : Out TT α) : ObsEq n o₁ o₂ ↔ o₁.1 = o₂.1 ∧ WorldObs n o₁.2 o₂.2 :=
  Iff.rfl

@[simp] theorem arrObs_ok_ok (n : Nat) {t : Ty} (a₁ a₂ : Nat) (w₁ w₂ : World TT) :
    ArrObs n ((.ok (.arr a₁), w₁) : Out TT (Val TT (.arr t))) (.ok (.arr a₂), w₂) ↔
      WorldObs n w₁ w₂ ∧ ((a₁ = a₂ ∧ a₁ < n) ∨ (n ≤ a₁ ∧ n ≤ a₂ ∧ ∃ xs,
        w₁.heap.get? (.arr t, a₁) = some xs ∧ w₂.heap.get? (.arr t, a₂) = some xs)) := Iff.rfl

@[simp] theorem arrObs_error_error (n : Nat) {t : Ty} (e₁ e₂ : Exc) (w₁ w₂ : World TT) :
    ArrObs n ((.error e₁, w₁) : Out TT (Val TT (.arr t))) (.error e₂, w₂) ↔ WorldObs n w₁ w₂ ∧ e₁ = e₂ :=
  Iff.rfl

end StrictTS.Obs

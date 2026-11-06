import EquivLean.Bridge.TS.Behaves

/-!
# StrictTS bridge: what a caller observes

`Equiv (· = ·)` on `JS.exec` compares whole final worlds, allocation counter and unreachable
cells included.  A caller observes less:

* `WorldObs n w₁ w₂`: the console output, every heap cell at an address below `n` (the
  caller's allocation counter `w.next` at the call: everything the caller can hold a reference
  to), and the positions of the three oracles (`OracleIdx`: how many answers of
  `Math.random()`, `Date.now()` and external calls were consumed).  Cells at addresses `≥ n`
  were allocated by the callee and are invisible unless the result refers to them; `next`
  itself is not observable.  The oracles answer by position, so a callee that makes one more
  external call (or one fewer, or draws one more random number) changes every later answer
  the caller gets: the positions are observable.  The oracle functions themselves are never
  changed by the interpreter.  Not compared: the asynchronous state (microtask queue, timers,
  unhandled rejections), so these relations are meant for callees that schedule no
  asynchronous work.
* `ObsEq n o₁ o₂`: equal completions (value, thrown exception, or panic) and `WorldObs n`.
  The right notion for results that carry no fresh reference (numbers, strings, booleans,
  records of those, references to caller cells).
* `ArrObs n o₁ o₂`, *equivalence modulo fresh allocation* for functions that return an array:
  `WorldObs n`, and the two results are the same caller array, or two fresh arrays (addresses
  `≥ n`, not necessarily equal) with equal contents.  This is what refactorings that allocate
  differently preserve, e.g. `xs.filter(p).map(f)` (two allocations, the result at `next + 1`)
  versus one loop pushing into a fresh array (one allocation, at `next`).  For element types
  without references (numbers, strings, booleans) it is an observational equivalence; for
  arrays of references (arrays, maps, objects, dictionaries, `unknown` values holding those),
  related fresh cells would have to be compared up to a renaming of fresh addresses (not
  formalised here).
* `TSEquivOn I P₁ P₂ f₁ f₂ Bad`: the encoding-level `EquivOn` statement (two translated
  functions, possibly of different programs, agree up to `ObsEq w.next` on every input
  `(vs, w)` outside `Bad`).  `ObsEq` depends on the input world through `w.next`, so it is
  stated pointwise; `tsEquivOn_of_equivOn` derives it from a core `EquivOn` with equal
  outcomes.
-/

namespace EquivLean.TS
open StrictTS

variable {TT : TypeTable} {α : Type}

/-! ## Caller-visible state -/

/-- The worlds have consumed the same number of answers of each oracle (`Math.random()`,
`Date.now()`, external calls).  The oracles answer by position, so this is what a caller sees
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
  exact ⟨(sim_some_some _ _).2 h, (sim_some_some _ _).2 h⟩

/-! ## Encoding-level `EquivOn` -/

/-- Two translated functions (of programs `P₁`, `P₂` over the same type table) are equivalent,
observed by a caller, on every input `(vs, w)` outside `Bad`. -/
def TSEquivOn (I : Impl) (P₁ P₂ : Program TT) {args : Tys} {ret : Ty} (f₁ f₂ : FunRef args ret)
    (Bad : Vals TT args.toList × World TT → Prop) : Prop :=
  ∀ vs w, ¬ Bad (vs, w) → Equiv (ObsEq w.next) (call I P₁ f₁ vs w) (call I P₂ f₂ vs w)

theorem tsEquivOn_of_equivOn (I : Impl) (P₁ P₂ : Program TT) {args : Tys} {ret : Ty}
    (f₁ f₂ : FunRef args ret) (Bad : Vals TT args.toList × World TT → Prop)
    (h : EquivOn Bad (· = ·) (fun x => call I P₁ f₁ x.1 x.2) (fun x => call I P₂ f₂ x.1 x.2)) :
    TSEquivOn I P₁ P₂ f₁ f₂ Bad :=
  fun vs w hb => Equiv.toObsEq w.next (h (vs, w) hb)

/-- The inputs on which two functions are observably different are bad inputs. -/
theorem TSEquivOn.changed_subset {I : Impl} {P₁ P₂ : Program TT} {args : Tys} {ret : Ty}
    {f₁ f₂ : FunRef args ret} {Bad : Vals TT args.toList × World TT → Prop}
    (h : TSEquivOn I P₁ P₂ f₁ f₂ Bad) (vs : Vals TT args.toList) (w : World TT)
    (hne : ¬ Equiv (ObsEq w.next) (call I P₁ f₁ vs w) (call I P₂ f₂ vs w)) : Bad (vs, w) :=
  Classical.byContradiction fun hb => hne (h vs w hb)

end EquivLean.TS

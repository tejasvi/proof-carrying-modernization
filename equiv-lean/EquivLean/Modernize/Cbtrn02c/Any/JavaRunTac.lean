import EquivLean.Modernize.Cbtrn02c.Any.JavaRunLib

/-!
# CBTRN02C → Java: tactics for the symbolic execution states

Heap reads through allocations, updates and callee post-states (`chain_simp`), frame reads
(`frame_simp`), heap growth (`grows_tac`), class state (`cls_simp`), field reads (`fget_simp`).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem addr_eq_false {a b : Nat} (h : a ≠ b) : (a = b) = False := eq_false h
theorem addr_lt_true {a b : Nat} (h : a < b) : (a < b) = True := eq_true h

/-- A heap read through allocations, updates and callee post-states (their frame facts as
hypotheses); address (dis)equalities by `jomega`. -/
macro "chain_simp" : tactic => `(tactic| (
  try simp only [State.next_alloc, State.next_setObj] at *
  simp (config := { decide := true }) (disch := jomega) only [State.heap_alloc, State.heap_setObj,
    State.next_alloc, State.next_setObj, ite_true, ite_false, reduceIte, addr_eq_false, addr_lt_true,
    jstrLitT, State.initOf_alloc, State.initOf_setObj, List.cons_append, List.nil_append,
    List.append_assoc, Frame.get_setLocal, *]
  try rfl))

/-- `fr'.get k = some v` for a frame built by `setLocal`s. -/
macro "frame_simp" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := { decide := true }) only [Frame.get_setLocal, ite_true, ite_false,
    reduceIte, $hs,*])

theorem grows_alloc' {σ0 σ : State} (h : Grows σ0 σ) (o : Obj) : Grows σ0 (σ.alloc o).2 :=
  grows_trans h (grows_alloc σ o)

theorem grows_setObj' {σ0 σ : State} {a : Addr} (h : Grows σ0 σ) (ha : σ0.next ≤ a) (o : Obj) :
    Grows σ0 (σ.setObj a o) :=
  grows_setObj h ha

theorem grows_post {σ0 σ σ' : State} (h : Grows σ0 σ) (h1 : σ.next ≤ σ'.next)
    (h2 : ∀ x, x < σ.next → σ'.heap x = σ.heap x) : Grows σ0 σ' :=
  grows_trans h ⟨h1, h2⟩

/-- `Grows σ0 σ` for `σ` built from `σ0` by allocations, writes to fresh objects and callee
post-states (their growth facts as hypotheses). -/
macro "grows_chain" : tactic => `(tactic| repeat (first
  | with_reducible exact grows_refl _
  | with_reducible assumption
  | (apply grows_alloc')
  | (refine grows_setObj' ?_ (by simp only [State.next_alloc, State.next_setObj] at *; jomega) _)
  | (refine grows_post ?_ ‹_› ‹_›)))

theorem inits_alloc (σ : State) (o : Obj) : (σ.alloc o).2.inits = σ.inits := rfl
theorem inits_setObj (σ : State) (a : Addr) (o : Obj) : (σ.setObj a o).inits = σ.inits := rfl
theorem statics_alloc (σ : State) (o : Obj) : (σ.alloc o).2.statics = σ.statics := rfl
theorem statics_setObj (σ : State) (a : Addr) (o : Obj) : (σ.setObj a o).statics = σ.statics := rfl

/-- `Fields.get` of an explicit field list built by `Fields.set`s. -/
macro "fget_simp" : tactic => `(tactic| simp (config := { decide := true }) only [Fields.get_set,
  fields_get_cons, fields_get_nil, ite_true, ite_false, reduceIte])

/-- `Grows σ0 σ'` for `σ'` built from `σ0` by allocations, writes to fresh objects and callee
post-states (their frame facts as hypotheses). -/
macro "grows_tac" : tactic => `(tactic| (
  refine ⟨?_, fun z hz => ?_⟩
  · simp only [State.next_alloc, State.next_setObj] at *
    jomega
  · chain_simp))

/-- The class state of a state built by allocations and writes. -/
macro "cls_simp" : tactic => `(tactic| (simp only [inits_alloc, inits_setObj, statics_alloc,
  statics_setObj, State.initOf_alloc, State.initOf_setObj]))

end EquivLean.Modernize.Cbtrn02c.Java

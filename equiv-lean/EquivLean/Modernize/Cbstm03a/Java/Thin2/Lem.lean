import EquivLean.Modernize.Cbstm03a.Java.RunTerm

/-!
# CBSTM03A → Java: helpers for `run`'s thin paths (cut points 117 … 179)

Elements of the text arrays (`TextsAt`'s `Forall2`), in the form the symbolic executor reads them (`xs[k]`, the
bound known).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Thin2

theorem forall2_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ k, k < xs.length →
      ∃ a b, xs[k]? = some a ∧ ys[k]? = some b ∧ R a b
  | [], [], .nil, _, hk => absurd hk (by simp)
  | a :: _, b :: _, .cons h _, 0, _ => ⟨a, b, rfl, rfl, h⟩
  | _ :: _, _ :: _, .cons _ hs, k + 1, hk => by
    simpa using forall2_getElem? hs k (by simpa using hk)

/-- A string element of a texts array. -/
theorem texts_elem {σ : State} {xs : List Value} {ts : List JStr} (h : Forall2 (JStrAt σ) xs ts)
    (k : Nat) (hk : k < xs.length) : ∃ x s, xs[k] = .ref x ∧ σ.heap x = some (.str s) := by
  obtain ⟨a, b, ha, -, x, rfl, hx⟩ := forall2_getElem? h k hk
  refine ⟨x, b, ?_, hx⟩
  rw [List.getElem?_eq_getElem hk] at ha
  exact Option.some.inj ha

/-- `σ.heap a = some o`, as a fact `jvc`'s forward instantiation produces (its conclusion is not an equation, so
it is not taken for a rewrite rule); it matches a callee's heap premise by unfolding. -/
def HeapIs (σ : State) (a : Addr) (o : Obj) : Prop := σ.heap a = some o

/-- A heap fact of `σ` in every state that agrees with `σ` below `σ.next` (a callee's `Grows`, unfolded). -/
theorem heapIs_of_agree {σ : State} {a : Addr} {o : Obj} (h : σ.heap a = some o) :
    ∀ σ' : State, (∀ x, x < σ.next → σ'.heap x = σ.heap x) → HeapIs σ' a o :=
  fun σ' hg => by unfold HeapIs; rw [hg a (State.lt_next_of_heap h)]; exact h

end EquivLean.Modernize.Cbstm03a.Java.Thin2

import EquivLean.Modernize.Cbstm03a.Java.RunTerm
import EquivLean.Modernize.Cbstm03a.Java.Run7.Lem2

/-!
# CBSTM03A → Java `run`'s thin VC at cut point 153: helpers

Elements of the text arrays in the form the executor reads them (after cbA-thin2's `Thin2.texts_elem`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg7

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

end EquivLean.Modernize.Cbstm03a.Java.Seg7

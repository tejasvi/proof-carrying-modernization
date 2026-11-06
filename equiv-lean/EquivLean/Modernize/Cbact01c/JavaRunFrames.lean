import EquivLean.Modernize.Cbact01c.JavaRunGlueLines

/-!
# CBACT01C → Java: frames

The record objects of the entry state `σ0` keep their fields and texts in every later state
whose heap grew from `σ0` (`Grows σ0 σ`); objects that are not lists are kept by a call that
changes list objects only.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

theorem heap_of_grows {σ0 σ : Jimple.State} {x : Addr} {o : Obj} (hg : Grows σ0 σ)
    (h : σ0.heap x = some o) : σ.heap x = some o := by
  rw [hg.2 x (State.lt_next_of_heap h), h]

theorem fieldOf_of_grows {σ0 σ : Jimple.State} {c : Addr} {fs : List (FieldKey × Value)}
    (hg : Grows σ0 σ) (hc : σ0.heap c = some (.plain acctCls fs)) (f : String) :
    fieldOf σ c f = fieldOf σ0 c f := by
  simp [fieldOf, heap_of_grows hg hc, hc]

theorem fieldLong_of_grows {σ0 σ : Jimple.State} {c : Addr} {fs : List (FieldKey × Value)}
    (hg : Grows σ0 σ) (hc : σ0.heap c = some (.plain acctCls fs)) (f : String) :
    fieldLong σ c f = fieldLong σ0 c f := by
  simp [fieldLong, fieldOf_of_grows hg hc]

/-- The texts of the record at `c` of `σ0`, in a state grown from `σ0`. -/
theorem texts_of_grows {σ0 σ : Jimple.State} {c : Addr} (hg : Grows σ0 σ) (hok : AcctOk σ0 c) :
    dispLinesJ σ c = dispLinesJ σ0 c ∧ acctTextJ σ c = acctTextJ σ0 c ∧ vb1J σ c = vb1J σ0 c ∧
      vb2J σ c = vb2J σ0 c ∧ (∀ f, fieldLong σ c f = fieldLong σ0 c f) := by
  have hok' := hok
  obtain ⟨fs, hc, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hok'
  have hL : ∀ f, fieldLong σ c f = fieldLong σ0 c f := fieldLong_of_grows hg hc
  have hS : ∀ f, StrField σ0 fs f → sfJ σ c f = sfJ σ0 c f := by
    intro f hf
    obtain ⟨x, s, hx, hxs, -⟩ := hf
    have e1 : fieldOf σ c f = .ref x := by simp only [fieldOf, heap_of_grows hg hc, hx]; rfl
    have e2 : fieldOf σ0 c f = .ref x := by simp only [fieldOf, hc, hx]; rfl
    rw [sfJ, sfJ, e1, e2]
    simp only [argText, strOf, heap_of_grows hg hxs, hxs]
  refine ⟨?_, ?_, ?_, ?_, hL⟩
  · simp only [dispLinesJ, zfJ, hL, hS _ h1, hS _ h5, hS _ h6, hS _ h7, hS _ h11]
  · simp only [acctTextJ, zfJ, hL, hS _ h1, hS _ h5, hS _ h6, hS _ h7, hS _ h10, hS _ h11, hS _ h12]
  · simp only [vb1J, zfJ, hL, hS _ h1]
  · simp only [vb2J, zfJ, hL, hS _ h7]

theorem sfJ_grows {σ0 σ : Jimple.State} {c : Addr} {fs : List (FieldKey × Value)} {f : String}
    (hg : Grows σ0 σ) (hc : σ0.heap c = some (.plain acctCls fs)) (hf : StrField σ0 fs f) :
    sfJ σ c f = sfJ σ0 c f := by
  obtain ⟨x, s, hx, hxs, -⟩ := hf
  have e1 : fieldOf σ c f = .ref x := by simp only [fieldOf, heap_of_grows hg hc, hx]; rfl
  have e2 : fieldOf σ0 c f = .ref x := by simp only [fieldOf, hc, hx]; rfl
  rw [sfJ, sfJ, e1, e2]
  simp only [argText, strOf, heap_of_grows hg hxs, hxs]

/-- The `OutAcctRec` built from the record at `c` of a state grown from `σ0`. -/
theorem outRecJ_of_grows {σ0 σ σ' : Jimple.State} {o c nb : Addr} {dt : JStr} {cd : I64}
    (hg : Grows σ0 σ) (hok : AcctOk σ0 c) (h : OutRecJ σ' o σ c dt cd nb) :
    OutRecJ σ' o σ0 c dt cd nb := by
  obtain ⟨fs, hc, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hok
  have hL := fieldLong_of_grows hg hc
  unfold OutRecJ at h ⊢
  simp only [hL, sfJ_grows hg hc h1, sfJ_grows hg hc h5, sfJ_grows hg hc h6,
    sfJ_grows hg hc h11] at h
  exact h

/-- The `ArrArrayRec` built from the record at `c` of a state grown from `σ0`. -/
theorem arrRecJ_of_grows {σ0 σ σ' : Jimple.State} {o c nb : Addr}
    (hg : Grows σ0 σ) (hok : AcctOk σ0 c) (h : ArrRecJ σ' o σ c nb) : ArrRecJ σ' o σ0 c nb := by
  obtain ⟨fs, hc, -⟩ := hok
  have hL := fieldLong_of_grows hg hc
  unfold ArrRecJ at h ⊢
  simp only [hL] at h
  exact h

/-- The record object with its strings below `B` (`AcctOkB`), from the entry state. -/
theorem acctOkB_of_grows {σ0 σ : Jimple.State} {c B : Addr} (hg : Grows σ0 σ) (hok : AcctOk σ0 c)
    (hB : σ0.next ≤ B) : AcctOkB σ c B := by
  obtain ⟨fs, hc, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hok
  have hS : ∀ f, StrField σ0 fs f → StrFieldB σ fs f B := by
    intro f hf
    obtain ⟨x, s, hx, hxs, hl⟩ := hf
    exact ⟨x, s, hx, Nat.lt_of_lt_of_le (State.lt_next_of_heap hxs) hB, heap_of_grows hg hxs, hl⟩
  exact ⟨fs, heap_of_grows hg hc, Nat.lt_of_lt_of_le (State.lt_next_of_heap hc) hB, h0, hS _ h1, h2, h3,
    h4, hS _ h5, hS _ h6, hS _ h7, h8, h9, hS _ h10, hS _ h11, hS _ h12⟩

theorem acctOk_of_okB {σ : Jimple.State} {c B : Addr} (h : AcctOkB σ c B) : AcctOk σ c := by
  obtain ⟨fs, hc, -, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hS : ∀ f, StrFieldB σ fs f B → StrField σ fs f := by
    intro f hf
    obtain ⟨x, s, hx, -, hxs, hl⟩ := hf
    exact ⟨x, s, hx, hxs, hl⟩
  exact ⟨fs, hc, h0, hS _ h1, h2, h3, h4, hS _ h5, hS _ h6, hS _ h7, h8, h9, hS _ h10, hS _ h11,
    hS _ h12⟩

theorem acctOk_of_grows {σ0 σ : Jimple.State} {c : Addr} (hg : Grows σ0 σ) (hok : AcctOk σ0 c) :
    AcctOk σ c :=
  acctOk_of_okB (acctOkB_of_grows hg hok (Nat.le_refl _))

end EquivLean.Modernize.Cbact01c.Java

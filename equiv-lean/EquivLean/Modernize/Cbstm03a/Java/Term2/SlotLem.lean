import EquivLean.Modernize.Cbstm03a.Java.Term2.Cut

/-!
# CBSTM03A → Java, termination: the slots array after a slot update

`StrKeep σ σ'`: every string of `σ` is still there in `σ'` (allocations, updates of non-strings, callee frames).
`slotOk_step`: after `slots[i] = c` with `c` the last allocated string, every slot is still `null` or a string.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Term2

/-- Every string of `σ` is a string of `σ'`. -/
def StrKeep (σ σ' : State) : Prop := ∀ y s, σ.heap y = some (.str s) → σ'.heap y = some (.str s)

theorem strKeep_refl (σ : State) : StrKeep σ σ := fun _ _ h => h

theorem strKeep_alloc {σ σ' : State} (h : StrKeep σ σ') (o : Obj) : StrKeep σ (σ'.alloc o).2 := by
  intro y s hy
  have h1 := h y s hy
  rw [State.heap_alloc_of_lt (State.lt_next_of_heap h1)]
  exact h1

theorem strKeep_of_frame {σ σ' : State} (h : ∀ x < σ.next, σ'.heap x = σ.heap x) : StrKeep σ σ' := by
  intro y s hy
  rw [h y (State.lt_next_of_heap hy)]
  exact hy

theorem lt_add4 {a b c : Nat} (h1 : a < b) (h2 : b ≤ c) : a < c + 1 + 1 + 1 + 1 := by omega

/-- After `slots[i] = c` (`c` the string just allocated): every slot is `null` or a string. -/
theorem slotOk_step {σ σ1 : State} {vs ws : List Value} {a c : Addr} {i : Nat} {t : JType} {s : JStr}
    (hok : SlotOk σ vs) (hav : σ.heap a = some (.array t ws)) (hk : StrKeep σ σ1) (ha1 : a < σ1.next)
    (hc : σ1.next = c) :
    SlotOk ((σ1.alloc (.str s)).2.setObj a (.array t (vs.set i (.ref c)))) (vs.set i (.ref c)) := by
  subst hc
  have hlt : a < (σ1.alloc (.str s)).2.next := by rw [State.next_alloc]; exact Nat.lt_succ_of_lt ha1
  intro v hv
  rcases List.mem_or_eq_of_mem_set hv with hv | rfl
  · rcases hok v hv with h | ⟨y, s', rfl, hy⟩
    · exact Or.inl h
    · refine Or.inr ⟨y, s', rfl, ?_⟩
      have hya : y ≠ a := by
        intro e; subst e; rw [hav] at hy; cases hy
      rw [State.heap_setObj_of_lt hlt, ite_eq_right_of_eq_false _ _ (eq_false hya)]
      have h1 := hk y s' hy
      rw [State.heap_alloc_of_lt (State.lt_next_of_heap h1)]
      exact h1
  · refine Or.inr ⟨σ1.next, s, rfl, ?_⟩
    rw [State.heap_setObj_of_lt hlt, ite_eq_right_of_eq_false _ _ (eq_false (Nat.ne_of_gt ha1)), State.heap_alloc,
      ite_eq_left_of_eq_true _ _ (eq_true rfl)]

theorem strKeep_setObj {σ σ' : State} (h : StrKeep σ σ') {b : Addr} (hb : ∀ s, σ.heap b ≠ some (.str s))
    (o : Obj) : StrKeep σ (σ'.setObj b o) := by
  intro y s hy
  have hyb : y ≠ b := by
    intro e; subst e; exact hb s hy
  rw [State.heap_setObj, ite_eq_right_of_eq_false _ _ (eq_false hyb)]
  exact h y s hy

theorem slotOk_keep {σ σ' : State} {vs : List Value} (hok : SlotOk σ vs) (hk : StrKeep σ σ') : SlotOk σ' vs := by
  intro v hv
  rcases hok v hv with h | ⟨y, s, rfl, hy⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, s, rfl, hk y s hy⟩

end EquivLean.Modernize.Cbstm03a.Java.Term2

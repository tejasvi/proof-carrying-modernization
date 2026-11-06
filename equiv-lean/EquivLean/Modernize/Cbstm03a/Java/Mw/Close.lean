import EquivLean.Modernize.Cbstm03a.Java.Mw.Defs

/-!
# CBSTM03A → Java: `memWrite`, the memory after a slot write

`memK_store`: slot `i` replaced by `c' = c[0, W) + t[P, P + K) + c[W + K, …)` (`c` the slot's text, the memory with
the first `P` characters of `t` written; `off + P = slotStart(i) + W`) holds the memory with the first `P + K`
characters written. `StepK` keeps the facts about `c` folded across the symbolic executor.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space keeps_trans keeps_setObj)

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

/-- Positions of another slot lie outside slot `i`. -/
theorem slot_disjoint {i i' w : Nat} (hi : i < 561) (hi' : i' < 561) (hne : i' ≠ i) (hw : w < slotLn i') :
    slotSt i' + w < slotSt i ∨ slotSt i + slotLn i ≤ slotSt i' + w := by
  rcases Nat.lt_or_ge (slotSt i' + w) (slotSt i) with h | h
  · exact Or.inl h
  · rcases Nat.lt_or_ge (slotSt i' + w) (slotSt i + slotLn i) with h2 | h2
    · exact absurd ((slotIdx_of_mem i' _ hi' (by omega) (by omega)).symm.trans (slotIdx_of_mem i _ hi h h2)) hne
    · exact Or.inr h2

theorem getD_append_left' {l l' : JStr} {n : Nat} (h : n < l.length) (d : JChar) :
    (l ++ l').getD n d = l.getD n d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {l l' : JStr} {n : Nat} (h : l.length ≤ n) (d : JChar) :
    (l ++ l').getD n d = l'.getD (n - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_drop' {l : JStr} (k n : Nat) (d : JChar) : (l.drop k).getD n d = l.getD (k + n) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The slots array with slot `i` replaced by a new string `q` holding `c'`. -/
theorem slotsAt_store {σ σ' : State} {a q : Addr} {M M' : Nat → JChar} {vs : List Value} {i : Nat} {c' : JStr}
    (h : SlotsAt σ a M) (ha : σ.heap a = some (.array (.cls "java.lang.String") vs)) (hi : i < 561)
    (ha' : σ'.heap a = some (.array (.cls "java.lang.String") (vs.set i (.ref q))))
    (hq : σ'.heap q = some (.str c')) (hcl : c'.length = slotLn i)
    (hc' : ∀ w, w < slotLn i → M' (slotSt i + w) = c'.getD w space)
    (hk : ∀ y o, σ.heap y = some o → y ≠ a → σ'.heap y = some o)
    (hM : ∀ j, j < 171156 → (j < slotSt i ∨ slotSt i + slotLn i ≤ j) → M' j = M j) :
    SlotsAt σ' a M' := by
  obtain ⟨vs', ha0, hl, hs⟩ := h
  rw [ha] at ha0
  cases ha0
  refine ⟨vs.set i (.ref q), ha', by rw [List.length_set]; exact hl, fun i' hi' => ?_⟩
  by_cases he : i' = i
  · subst he
    refine Or.inr ⟨q, c', ?_, hq, hcl, hc'⟩
    rw [List.getElem?_set, if_pos rfl, if_pos (by omega)]
  · rw [List.getElem?_set, if_neg (Ne.symm he)]
    have hd := fun w (hw : w < slotLn i') => slot_disjoint hi hi' he hw
    have he' := slot_end_le i' hi'
    rcases hs i' hi' with ⟨h1, h2⟩ | ⟨y, c, h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, fun w hw => by rw [hM _ (by omega) (hd w hw)]; exact h2 w hw⟩
    · refine Or.inr ⟨y, c, h1, hk y _ h2 ?_, h3, fun w hw => by rw [hM _ (by omega) (hd w hw)]; exact h4 w hw⟩
      intro hya
      rw [hya, ha] at h2
      cases h2

/-- What the closer of a slot write needs about the slot's text `c` and the new text `c'`. -/
@[irreducible] def StepK (σ0 : State) (a : Addr) (off : I64) (t c' : JStr) (i W K P : Nat) : Prop :=
  ∃ c : JStr, off.toInt + P = slotSt i + W ∧ W + K ≤ slotLn i ∧ P + K ≤ t.length ∧ c.length = slotLn i ∧
    (∀ m, SlotsAt σ0 a m → ∀ w, w < slotLn i → memWr m off.toInt (t.take P) (slotSt i + w) = c.getD w space) ∧
    c' = c.take W ++ ((t.take (P + K)).drop P ++ c.drop (W + K))

theorem stepK_intro {σ0 : State} {a : Addr} {off : I64} {t : JStr} {i W K P : Nat} (c : JStr)
    (hW : off.toInt + P = slotSt i + W) (hWK : W + K ≤ slotLn i) (hPK : P + K ≤ t.length) (hcl : c.length = slotLn i)
    (hcm : ∀ m, SlotsAt σ0 a m → ∀ w, w < slotLn i → memWr m off.toInt (t.take P) (slotSt i + w) = c.getD w space) :
    StepK σ0 a off t (c.take W ++ ((t.take (P + K)).drop P ++ c.drop (W + K))) i W K P := by
  unfold StepK
  exact ⟨c, hW, hWK, hPK, hcl, hcm, rfl⟩

/-- A slot write: the memory with `K` more characters of `t` written. -/
theorem memK_store {σ0 σ : State} {a q : Addr} {off : I64} {t c' : JStr} {vs : List Value} {i W K P : Nat}
    (hK : MemK σ0 σ a off t P) (hS : StepK σ0 a off t c' i W K P) (hi : i < 561)
    (ha : σ.heap a = some (.array (.cls "java.lang.String") vs)) (hq : σ.heap q = some (.str c')) :
    MemK σ0 (σ.setObj a (.array (.cls "java.lang.String") (vs.set i (.ref q)))) a off t (P + K) := by
  unfold MemK at hK ⊢
  unfold StepK at hS
  obtain ⟨hM, hk, hin, hst⟩ := hK
  obtain ⟨c, hW, hWK, hPK, hcl, hcm, hc'⟩ := hS
  have hlt : a < σ.next := State.lt_next_of_heap ha
  have hqa : q ≠ a := fun e => by rw [e, ha] at hq; cases hq
  have hk' : Keeps (· = a) σ (σ.setObj a (.array (.cls "java.lang.String") (vs.set i (.ref q)))) :=
    keeps_setObj _ rfl
  refine ⟨fun m hm => ?_, keeps_trans hk hk', hin, hst⟩
  have he := slot_end_le i hi
  have hl1 : (c.take W).length = W := by rw [List.length_take]; omega
  have hl2 : ((t.take (P + K)).drop P).length = K := by rw [List.length_drop, List.length_take]; omega
  apply slotsAt_store (hM m hm) ha hi
  · rw [State.heap_setObj_of_lt hlt, if_pos rfl]
  · rw [State.heap_setObj_of_lt hlt, if_neg hqa]; exact hq
  · rw [hc', List.length_append, List.length_append, hl1, hl2, List.length_drop]; omega
  · intro w hw
    rw [memWr_step m _ t P K hPK, hc']
    by_cases h1 : w < W
    · rw [if_neg (by omega), getD_append_left' (by omega), getD_take_of_lt h1]
      exact hcm m hm w hw
    · by_cases h2 : w < W + K
      · rw [if_pos ⟨by omega, by omega, by omega⟩, getD_append_right' (by omega), hl1,
          getD_append_left' (by omega), getD_drop', getD_take_of_lt (by omega)]
        congr 1
        omega
      · rw [if_neg (by omega), getD_append_right' (by omega), hl1, getD_append_right' (by omega), hl2,
          getD_drop', show W + K + (w - W - K) = w by omega]
        exact hcm m hm w hw
  · intro y o hy hya
    rw [State.heap_setObj_of_lt hlt, if_neg hya]
    exact hy
  · intro j hj hout
    rw [memWr_step m _ t P K hPK j, if_neg (by omega)]

end EquivLean.Modernize.Cbstm03a.Java.Mw

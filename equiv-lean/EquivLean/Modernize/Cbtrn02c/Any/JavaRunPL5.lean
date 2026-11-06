import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL4

/-!
# CBTRN02C → Java: the copy loops of `run`, as the symbolic execution states them
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem ResInit.setObj8 {σ0 σ : State} {a : Addr} {o : Obj} (h : ResInit σ0 σ)
    (ha : σ0.next + 8 ≤ a) : ResInit σ0 (σ.setObj a o) := by
  obtain ⟨fs, h1, h2⟩ := h
  exact ⟨fs, by rw [State.heap_setObj, if_neg (by jomega)]; exact h1, h2⟩

theorem ListsInit.setObj8 {σ0 σ : State} {a : Addr} {o : Obj} (h : ListsInit σ0 σ)
    (ha : σ0.next + 8 ≤ a) : ListsInit σ0 (σ.setObj a o) := by
  obtain ⟨⟨m1, h1⟩, h7, ⟨m2, h2⟩, ⟨m3, h3⟩, ⟨m4, h4⟩, ⟨m5, h5⟩, ⟨m6, h6⟩⟩ := h
  refine ⟨⟨m1, ?_⟩, ?_, ⟨m2, ?_⟩, ⟨m3, ?_⟩, ⟨m4, ?_⟩, ⟨m5, ?_⟩, ⟨m6, ?_⟩⟩ <;>
    (rw [State.heap_setObj, if_neg (by jomega)]; assumption)

/-- The table survives an update of a non-record, non-string object other than the table. -/
theorem TabInit.setObj_list {g : G} {σ0 σ : State} {n : Nat} {a : Addr} {o : Obj}
    (h : TabInit g σ0 σ n) (ha : σ0.next + 9 ≤ a) (hp : ∀ c fs, σ.heap a ≠ some (.plain c fs))
    (hs : ∀ t, σ.heap a ≠ some (.str t)) : TabInit g σ0 (σ.setObj a o) n := by
  obtain ⟨ys, h1, h2, h3⟩ := h
  exact ⟨ys, by rw [State.heap_setObj, if_neg (by jomega)]; exact h1,
    forall2_imp (fun _ _ h => jrecAt_setObj_nonplain h hp hs) h2, h3⟩

theorem replicate_set_zero {α : Type} (n : Nat) (v w : α) (h : 0 < n) :
    (List.replicate n v).set 0 w = w :: List.replicate (n - 1) v := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [List.replicate_succ]

/-- **One more account copied** (statements 14–17), in the form of the symbolic execution. -/
theorem tabInit_step2 {g : G} {σ0 σ σ1 : State} {n : Nat} {ys : List Value} {x y : Addr}
    {fs fs' : List (FieldKey × Value)}
    (hn : n < g.accts.length) (hys : ys.length = n)
    (hT : σ.heap (σ0.next + 8) =
      some (.array (.cls acCls) (ys ++ List.replicate (g.accts.length - n) .null)))
    (hF : Forall2 (JRecAt AccountRecord acCls σ) ys (g.accts.take n))
    (hB : ∀ v ∈ ys, ∀ a, v = .ref a → σ0.next + 9 ≤ a)
    (hy : JRecAt AccountRecord acCls σ (.ref y) g.accts[n]) (hyh : σ.heap y = some (.plain acCls fs))
    (hx : σ1.heap x = some (.plain acCls fs')) (hsame : SameFields (keysOf AccountRecord acCls) fs' fs)
    (hxn : σ.next ≤ x) (hnext : σ0.next + 9 ≤ σ.next) (hg : Grows σ σ1) :
    TabInit g σ0 (σ1.setObj (σ0.next + 8) (.array (.cls acCls)
      (ys ++ (List.replicate (g.accts.length - n) Value.null).set 0 (.ref x)))) (n + 1) := by
  have h := tabInit_step hn hys hT hF hB hy hyh hx hsame hxn hnext hg
  have e : (ys ++ List.replicate (g.accts.length - n) Value.null).set n (.ref x) =
      ys ++ (List.replicate (g.accts.length - n) Value.null).set 0 (.ref x) := by
    rw [← hys, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
  rw [e] at h
  exact h

end EquivLean.Modernize.Cbtrn02c.Java

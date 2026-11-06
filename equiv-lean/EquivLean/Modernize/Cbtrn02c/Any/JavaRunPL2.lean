import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL

/-!
# CBTRN02C → Java: the copy loops of `run`

One more account copied into the table (`tabInit_step`), one more category record appended to
the category list (`catList_step`); the list complete before the work-storage records
(`catDone_of`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- A copy holds the record of its source (fields `keysOf s cls`, strings unchanged). -/
theorem jrec_copy {s : Schema} {cls : ClassName} {σ σ1 : State} {x y : Addr}
    {fs fs' : List (FieldKey × Value)} {vals : List EquivLean.Cobol.Rec.FVal}
    (hy : JRecAt s cls σ (.ref y) vals) (hyh : σ.heap y = some (.plain cls fs))
    (hx : σ1.heap x = some (.plain cls fs')) (hsame : SameFields (keysOf s cls) fs' fs)
    (hg : Grows σ σ1) : JRecAt s cls σ1 (.ref x) vals :=
  jrecAt_copy hy hyh hx (fun f hf => hsame _ (List.mem_map.2 ⟨f, hf, rfl⟩))
    (fun _ _ h => jstrAt_grows h hg)

theorem take_succ_getElem {α : Type} (l : List α) {n : Nat} (hn : n < l.length) :
    l.take (n + 1) = l.take n ++ [l[n]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hn, Option.toList_some]

/-- **One more account copied** (statements 14–17). -/
theorem tabInit_step {g : G} {σ0 σ σ1 : State} {n : Nat} {ys : List Value} {x y : Addr}
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
      ((ys ++ List.replicate (g.accts.length - n) Value.null).set n (.ref x)))) (n + 1) := by
  have haD : σ1.heap (σ0.next + 8) = σ.heap (σ0.next + 8) := hg.2 _ (by jomega)
  have hnp : ∀ c fs, σ1.heap (σ0.next + 8) ≠ some (.plain c fs) := by
    intro c fs h; rw [haD, hT] at h; cases h
  have hns : ∀ t, σ1.heap (σ0.next + 8) ≠ some (.str t) := by
    intro t h; rw [haD, hT] at h; cases h
  have hsplit : g.accts.length - n = (g.accts.length - (n + 1)) + 1 := by jomega
  refine ⟨ys ++ [.ref x], ?_, ?_, ?_⟩
  · rw [State.heap_setObj, if_pos rfl, if_pos (State.lt_next_of_heap (by rw [haD]; exact hT)),
      hsplit, ← hys, set_fill]
  · rw [take_succ_getElem _ hn]
    refine forall2_append (jrecAt_setObj_nonplain (jrec_copy hy hyh hx hsame hg) hnp hns) ?_
    exact forall2_imp (fun _ _ h => jrecAt_setObj_nonplain (jrecAt_grows h hg) hnp hns) hF
  · intro v hv a hva
    rcases List.mem_append.1 hv with hv | hv
    · exact hB v hv a hva
    · simp only [List.mem_singleton] at hv
      subst hv
      cases hva
      jomega

/-- **One more category record appended** (statements 24–27). -/
theorem catList_step {g : G} {σ0 σ σ1 : State} {n : Nat} {c x y : Addr} {xs : List Value} {m : Nat}
    {fs fs' : List (FieldKey × Value)}
    (hn : n < g.cats.length)
    (hc : σ.heap c = some (.list .arrayList xs m))
    (hF : Forall2 (JRecAt TranCatBalRecord tcCls σ) xs (g.cats.take n))
    (hB : ∀ v ∈ xs, ∀ a, v = .ref a → σ0.next + 9 ≤ a)
    (hy : JRecAt TranCatBalRecord tcCls σ (.ref y) g.cats[n]) (hyh : σ.heap y = some (.plain tcCls fs))
    (hx : σ1.heap x = some (.plain tcCls fs'))
    (hsame : SameFields (keysOf TranCatBalRecord tcCls) fs' fs)
    (hxn : σ.next ≤ x) (hnext : σ0.next + 9 ≤ σ.next) (hg : Grows σ σ1) :
    ∃ xs' m', (σ1.setObj c (.list .arrayList (xs ++ [.ref x]) (m + 1))).heap c =
        some (.list .arrayList xs' m') ∧
      Forall2 (JRecAt TranCatBalRecord tcCls (σ1.setObj c (.list .arrayList (xs ++ [.ref x]) (m + 1))))
        xs' (g.cats.take (n + 1)) ∧
      ∀ v ∈ xs', ∀ a, v = .ref a → σ0.next + 9 ≤ a := by
  have hc1 : σ1.heap c = σ.heap c := hg.2 _ (State.lt_next_of_heap hc)
  have hnp : ∀ c' fs, σ1.heap c ≠ some (.plain c' fs) := by
    intro c' fs h; rw [hc1, hc] at h; cases h
  have hns : ∀ t, σ1.heap c ≠ some (.str t) := by
    intro t h; rw [hc1, hc] at h; cases h
  refine ⟨xs ++ [.ref x], m + 1, ?_, ?_, ?_⟩
  · rw [State.heap_setObj, if_pos rfl, if_pos (by rw [← hc1] at hc; exact State.lt_next_of_heap hc)]
  · rw [take_succ_getElem _ hn]
    refine forall2_append (jrecAt_setObj_nonplain (jrec_copy hy hyh hx hsame hg) hnp hns) ?_
    exact forall2_imp (fun _ _ h => jrecAt_setObj_nonplain (jrecAt_grows h hg) hnp hns) hF
  · intro v hv a hva
    rcases List.mem_append.1 hv with hv | hv
    · exact hB v hv a hva
    · simp only [List.mem_singleton] at hv
      subst hv
      cases hva
      jomega

/-- The category list complete: its records lie below the next allocation. -/
theorem catDone_of {g : G} {σ0 σ : State} {c : Addr}
    (h : ∃ xs m, σ.heap c = some (.list .arrayList xs m) ∧
      Forall2 (JRecAt TranCatBalRecord tcCls σ) xs (g.cats.take g.cats.length) ∧
      ∀ v ∈ xs, ∀ a, v = .ref a → σ0.next + 9 ≤ a) :
    CatDone g σ0 σ c σ.next := by
  obtain ⟨xs, m, h1, h2, h3⟩ := h
  rw [List.take_length] at h2
  exact ⟨xs, m, h1, h2, fun v hv a hva => ⟨h3 v hv a hva, rec_lt_next h2 v hv a hva⟩⟩

theorem TabInit.grows {g : G} {σ0 σ σ' : State} {n : Nat} (h : TabInit g σ0 σ n) (hg : Grows σ σ') :
    TabInit g σ0 σ' n := by
  obtain ⟨ys, h1, h2, h3⟩ := h
  exact ⟨ys, heap_of_grows hg h1, forall2_imp (fun _ _ h => jrecAt_grows h hg) h2, h3⟩

theorem toInt_succ32 {i : BitVec 32} (h0 : 0 ≤ i.toInt) (h : i.toInt < 2147483647) :
    (i + 1#32).toInt = i.toInt + 1 := by
  rw [BitVec.toInt_add, Int.bmod_def]
  have h1 : (1#32).toInt = 1 := by decide
  rw [h1]
  split <;> omega

theorem toNat_succ32 {i : BitVec 32} (h0 : 0 ≤ i.toInt) (h : i.toInt < 2147483647) :
    (i + 1#32).toInt.toNat = i.toInt.toNat + 1 := by
  rw [toInt_succ32 h0 h]
  omega

end EquivLean.Modernize.Cbtrn02c.Java

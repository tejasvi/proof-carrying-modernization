import EquivLean.Modernize.Cbtrn02c.Any.JavaRunLib

/-!
# CBTRN02C → Java: record facts across heap updates

`Forall2` lemmas, and the transport of `JStrAt` / `JRecAt` along `Grows`, along updates of objects
that are not strings (lists, arrays) or not the record, and to copies with the same fields.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-! ## `Forall2` -/

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → xs.length = ys.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [forall2_length h]

theorem forall2_get {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys →
      ∀ i (hi : i < xs.length) (hj : i < ys.length), R xs[i] ys[i]
  | _, _, .nil, i, hi, _ => by simp at hi
  | _, _, .cons h _, 0, _, _ => h
  | _, _, .cons _ h, i + 1, hi, hj => by
    simp only [List.getElem_cons_succ]
    exact forall2_get h i (by simp at hi; omega) (by simp at hj; omega)

theorem forall2_imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 S xs ys
  | _, _, .nil => .nil
  | _, _, .cons hr hs => .cons (h _ _ hr) (forall2_imp h hs)

theorem forall2_imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, (∀ a ∈ xs, ∀ b, R a b → S a b) → Forall2 R xs ys →
      Forall2 S xs ys
  | _, _, _, .nil => .nil
  | _, _, h, .cons hr hs =>
    .cons (h _ List.mem_cons_self _ hr)
      (forall2_imp_mem (fun a ha b => h a (List.mem_cons_of_mem _ ha) b) hs)

theorem forall2_append {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 R (xs ++ [a]) (ys ++ [b])
  | _, _, .nil => .cons hab .nil
  | _, _, .cons h hs => .cons h (forall2_append hab hs)

theorem forall2_set {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hab : R a b) :
    ∀ {xs : List α} {ys : List β} (i : Nat), Forall2 R xs ys → Forall2 R (xs.set i a) (ys.set i b)
  | _, _, _, .nil => by simp; exact .nil
  | _, _, 0, .cons _ hs => by simp; exact .cons hab hs
  | _, _, i + 1, .cons h hs => by simp; exact .cons h (forall2_set hab i hs)

/-! ## Strings -/

theorem jstrAt_grows {σ σ' : State} {v : Value} {s : JStr} (h : JStrAt σ v s) (hg : Grows σ σ') :
    JStrAt σ' v s := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, by rw [hg.2 x (State.lt_next_of_heap hx)]; exact hx⟩

theorem jstrAt_setObj {σ : State} {v : Value} {s : JStr} {a : Addr} {o : Obj} (h : JStrAt σ v s)
    (ha : ∀ t, σ.heap a ≠ some (.str t)) : JStrAt (σ.setObj a o) v s := by
  obtain ⟨x, rfl, hx⟩ := h
  refine ⟨x, rfl, ?_⟩
  have hne : x ≠ a := by rintro rfl; exact ha s hx
  rw [State.heap_setObj, if_neg hne]; exact hx

/-! ## Records -/

theorem jFieldAt_mono {σ σ' : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {val : EquivLean.Cobol.Rec.FVal} (hs : ∀ v s, JStrAt σ v s → JStrAt σ' v s)
    (h : jFieldAt σ cls fs f val) : jFieldAt σ' cls fs f val := by
  cases val with
  | num v => exact h
  | str bs =>
    obtain ⟨s, h1, h2⟩ := h
    exact ⟨s, h1, hs _ _ h2⟩

theorem jrecAt_grows {s : Schema} {cls : ClassName} {σ σ' : State} {v : Value}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecAt s cls σ v vals) (hg : Grows σ σ') :
    JRecAt s cls σ' v vals := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := h
  refine ⟨x, fs, rfl, by rw [hg.2 x (State.lt_next_of_heap hx)]; exact hx, ?_⟩
  exact forall2_imp (fun f val h => jFieldAt_mono (fun v s h' => jstrAt_grows h' hg) h) hf

/-- A record survives an update of another object that is not a string. -/
theorem jrecAt_setObj {s : Schema} {cls : ClassName} {σ : State} {x a : Addr} {o : Obj}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecAt s cls σ (.ref x) vals) (hxa : x ≠ a)
    (ha : ∀ t, σ.heap a ≠ some (.str t)) : JRecAt s cls (σ.setObj a o) (.ref x) vals := by
  obtain ⟨y, fs, hy, hx, hf⟩ := h
  cases hy
  refine ⟨x, fs, rfl, by rw [State.heap_setObj, if_neg hxa]; exact hx, ?_⟩
  exact forall2_imp (fun f val h => jFieldAt_mono (fun v s h' => jstrAt_setObj h' ha) h) hf

/-- A record survives an update of an object that is neither a record nor a string. -/
theorem jrecAt_setObj_nonplain {s : Schema} {cls : ClassName} {σ : State} {v : Value} {a : Addr}
    {o : Obj} {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecAt s cls σ v vals)
    (ha1 : ∀ c fs, σ.heap a ≠ some (.plain c fs)) (ha2 : ∀ t, σ.heap a ≠ some (.str t)) :
    JRecAt s cls (σ.setObj a o) v vals := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := h
  have hxa : x ≠ a := by rintro rfl; exact ha1 _ _ hx
  exact jrecAt_setObj ⟨x, fs, rfl, hx, hf⟩ hxa ha2

/-- A copy: an object with the same record fields (and the strings still there). -/
theorem jrecAt_copy {s : Schema} {cls : ClassName} {σ σ' : State} {a x : Addr}
    {fs fs' : List (FieldKey × Value)} {vals : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt s cls σ (.ref a) vals) (ha : σ.heap a = some (.plain cls fs))
    (hx : σ'.heap x = some (.plain cls fs'))
    (hk : ∀ f ∈ s.fields, Fields.get fs' (cls, f.jname) = Fields.get fs (cls, f.jname))
    (hs : ∀ v t, JStrAt σ v t → JStrAt σ' v t) : JRecAt s cls σ' (.ref x) vals := by
  obtain ⟨y, fs0, hy, hy0, hf⟩ := h
  cases hy
  rw [ha] at hy0; cases hy0
  refine ⟨x, fs', rfl, hx, ?_⟩
  refine forall2_imp_mem (fun f hf' val h => ?_) hf
  cases val with
  | num v => show Fields.get fs' _ = _; rw [hk f hf']; exact h
  | str bs =>
    obtain ⟨sv, h1, h2⟩ := h
    exact ⟨sv, by rw [hk f hf']; exact h1, hs _ _ h2⟩

/-- The fields of a record object are all present. -/
theorem jrecAt_isSome {s : Schema} {cls : ClassName} {σ : State} {a : Addr}
    {fs : List (FieldKey × Value)} {vals : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt s cls σ (.ref a) vals) (ha : σ.heap a = some (.plain cls fs)) :
    ∀ f ∈ s.fields, (Fields.get fs (cls, f.jname)).isSome := by
  obtain ⟨y, fs0, hy, hy0, hf⟩ := h
  cases hy
  rw [ha] at hy0; cases hy0
  intro f hf'
  have key : ∀ {fl : List Field} {vl : List EquivLean.Cobol.Rec.FVal},
      Forall2 (fun f val => jFieldAt σ cls fs f val) fl vl → f ∈ fl →
      (Fields.get fs (cls, f.jname)).isSome := by
    intro fl vl h2 hm
    induction h2 with
    | nil => cases hm
    | @cons f' val _ _ hr _ ih =>
      rcases List.mem_cons.mp hm with rfl | hm'
      · cases val with
        | num v => simp [show Fields.get fs (cls, f.jname) = _ from hr]
        | str bs => obtain ⟨sv, h1, _⟩ := hr; simp [h1]
      · exact ih hm'
  exact key hf hf'

end EquivLean.Modernize.Cbtrn02c.Java

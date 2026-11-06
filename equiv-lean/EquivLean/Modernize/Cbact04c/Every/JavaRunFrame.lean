import EquivLean.Modernize.Cbact04c.Every.JavaRunLib

/-!
# CBACT04C → Java: what a stretch of `run` leaves unchanged

`Agree σ σ' W`: the heap grew from `σ` to `σ'` and every object of `σ` outside `W` (the objects
the stretch writes: the result lists, the account table, the current account and transaction
objects) is unchanged. Strings and record objects outside `W` keep what they hold.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- The heap grew and the objects outside `W` are unchanged. -/
def Agree (σ σ' : State) (W : List Addr) : Prop :=
  σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → x ∉ W → σ'.heap x = σ.heap x

theorem agree_refl (σ : State) (W : List Addr) : Agree σ σ W := ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

theorem agree_of_grows {σ σ' : State} (W : List Addr) (h : Grows σ σ') : Agree σ σ' W :=
  ⟨h.1, fun x hx _ => h.2 x hx⟩

theorem agree_trans {σ1 σ2 σ3 : State} {W : List Addr} (h1 : Agree σ1 σ2 W) (h2 : Agree σ2 σ3 W) :
    Agree σ1 σ3 W :=
  ⟨Nat.le_trans h1.1 h2.1, fun x hx hw => by
    rw [h2.2 x (Nat.lt_of_lt_of_le hx h1.1) hw, h1.2 x hx hw]⟩

/-! ### One step from `σ`, after a stretch from `σ0` -/

theorem agree_alloc {σ0 σ : State} {W : List Addr} (h : Agree σ0 σ W) (o : Obj) :
    Agree σ0 (σ.alloc o).2 W :=
  agree_trans h (agree_of_grows W (grows_alloc σ o))

theorem agree_setObj_mem {σ0 σ : State} {W : List Addr} {a : Addr} (h : Agree σ0 σ W) (ha : a ∈ W)
    (o : Obj) : Agree σ0 (σ.setObj a o) W := by
  refine ⟨by rw [State.next_setObj]; exact h.1, fun x hx hw => ?_⟩
  have hxa : x ≠ a := by intro e; subst e; exact hw ha
  rw [State.heap_setObj, ite_eq_right hxa, h.2 x hx hw]

theorem agree_setObj_fresh {σ0 σ : State} {W : List Addr} {a : Addr} (h : Agree σ0 σ W)
    (ha : σ0.next ≤ a) (o : Obj) : Agree σ0 (σ.setObj a o) W := by
  refine ⟨by rw [State.next_setObj]; exact h.1, fun x hx hw => ?_⟩
  have hxa : x ≠ a := Nat.ne_of_lt (Nat.lt_of_lt_of_le hx ha)
  rw [State.heap_setObj, ite_eq_right hxa, h.2 x hx hw]

/-- A callee's post-state: the heap grew. -/
theorem agree_grows {σ0 σ σ' : State} {W : List Addr} (h : Agree σ0 σ W)
    (h1 : σ.next ≤ σ'.next) (h2 : ∀ x, x < σ.next → σ'.heap x = σ.heap x) : Agree σ0 σ' W :=
  agree_trans h (agree_of_grows W ⟨h1, h2⟩)

/-- A constructor's post-state: only the (fresh) object `a` changed. -/
theorem agree_ctor {σ0 σ σ' : State} {W : List Addr} {a : Addr} (h : Agree σ0 σ W)
    (ha : σ0.next ≤ a) (h1 : ∀ y, y ≠ a → σ'.heap y = σ.heap y) (h2 : σ'.next = σ.next) :
    Agree σ0 σ' W :=
  ⟨by rw [h2]; exact h.1, fun x hx hw => by
    rw [h1 x (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx ha)), h.2 x hx hw]⟩

/-! ### What `Agree` keeps -/

/-- None of the addresses of `W` holds a string. -/
def NoStr (σ : State) (W : List Addr) : Prop := ∀ w ∈ W, ∀ s, σ.heap w ≠ some (.str s)

theorem jstrAt_agree {σ σ' : State} {W : List Addr} {v : Value} {s : JStr} (h : JStrAt σ v s)
    (ha : Agree σ σ' W) (hw : NoStr σ W) : JStrAt σ' v s := by
  obtain ⟨x, rfl, hx⟩ := h
  refine ⟨x, rfl, ?_⟩
  have hxw : x ∉ W := fun hm => hw x hm s hx
  rw [ha.2 x (State.lt_next_of_heap hx) hxw, hx]

theorem jfieldAt_agree {σ σ' : State} {W : List Addr} {cls : ClassName}
    {fs : List (FieldKey × Value)} {f : Field} {v : EquivLean.Cobol.Rec.FVal}
    (h : jFieldAt σ cls fs f v) (ha : Agree σ σ' W) (hw : NoStr σ W) : jFieldAt σ' cls fs f v := by
  cases v with
  | num n => exact h
  | str bs =>
    obtain ⟨s, hs, hj⟩ := h
    exact ⟨s, hs, jstrAt_agree hj ha hw⟩

theorem forall2_mono {α β : Type} {R R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 R' xs ys
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (hR _ _ h) (forall2_mono hR hs)

theorem jrecAt_agree {σ σ' : State} {W : List Addr} {s : Schema} {cls : ClassName} {x : Addr}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecAt s cls σ (.ref x) vals) (ha : Agree σ σ' W)
    (hw : NoStr σ W) (hx : x ∉ W) : JRecAt s cls σ' (.ref x) vals := by
  obtain ⟨y, fs, hy, hheap, hf⟩ := h
  cases hy
  refine ⟨x, fs, rfl, ?_, forall2_mono (fun f v h => jfieldAt_agree h ha hw) hf⟩
  rw [ha.2 x (State.lt_next_of_heap hheap) hx, hheap]

/-- A list of record objects outside `W`. -/
theorem forall2_jrecAt_agree {σ σ' : State} {W : List Addr} {s : Schema} {cls : ClassName}
    (ha : Agree σ σ' W) (hw : NoStr σ W) :
    ∀ {xs : List Value} {vals : List (List EquivLean.Cobol.Rec.FVal)},
      Forall2 (JRecAt s cls σ) xs vals → (∀ v ∈ xs, ∀ a, v = .ref a → a ∉ W) →
      Forall2 (JRecAt s cls σ') xs vals
  | [], [], .nil, _ => .nil
  | v :: xs, _ :: _, .cons h hs, hW => by
    have h' := h
    obtain ⟨y, fs, rfl, -⟩ := h'
    exact .cons (jrecAt_agree h ha hw (hW _ (List.mem_cons_self ..) y rfl))
      (forall2_jrecAt_agree ha hw hs (fun v hv => hW v (List.mem_cons_of_mem _ hv)))

theorem forall2_jstrAt_agree {σ σ' : State} {W : List Addr} (ha : Agree σ σ' W) (hw : NoStr σ W) :
    ∀ {xs : List Value} {ss : List JStr}, Forall2 (JStrAt σ) xs ss → Forall2 (JStrAt σ') xs ss
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (jstrAt_agree h ha hw) (forall2_jstrAt_agree ha hw hs)

/-! ### Lists -/

theorem forall2_append {α β : Type} {R : α → β → Prop} {x : α} {y : β} (hxy : R x y) :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → Forall2 R (xs ++ [x]) (ys ++ [y])
  | [], [], .nil => .cons hxy .nil
  | _ :: _, _ :: _, .cons h hs => .cons h (forall2_append hxy hs)

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → xs.length = ys.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ hs => by simp [forall2_length hs]

theorem forall2_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (h : Forall2 R xs ys) (i : Nat) (hi : i < xs.length),
      R xs[i] (ys[i]'(by rw [← forall2_length h]; exact hi))
  | [], [], .nil, _, hi => absurd hi (by simp)
  | _ :: _, _ :: _, .cons h _, 0, _ => h
  | _ :: _, _ :: _, .cons _ hs, i + 1, hi => forall2_getElem hs i (by simpa using hi)

theorem set_append_replicate {α : Type} (xs : List α) (v d : α) (n : Nat) (hn : 0 < n) :
    (xs ++ List.replicate n d).set xs.length v = (xs ++ [v]) ++ List.replicate (n - 1) d := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction xs with
  | nil => simp [List.replicate_succ]
  | cons x xs ih => simp [ih]

theorem forall2_mem_rel {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ x ∈ xs, ∃ y, R x y
  | [], [], .nil, _, hx => by simp at hx
  | _ :: _, y :: _, .cons h hs, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hm
    · exact ⟨y, h⟩
    · exact forall2_mem_rel hs x hm

theorem forall2_set {α β : Type} {R : α → β → Prop} {x : α} {y : β} (hxy : R x y) :
    ∀ {xs : List α} {ys : List β} (i : Nat), Forall2 R xs ys → Forall2 R (xs.set i x) (ys.set i y)
  | [], [], _, .nil => .nil
  | _ :: _, _ :: _, 0, .cons _ hs => .cons hxy hs
  | _ :: _, _ :: _, i + 1, .cons h hs => .cons h (forall2_set hxy i hs)

end EquivLean.Modernize.Cbact04c.Java

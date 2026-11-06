import EquivLean.Demo.Jimple.Cbact04c.Model

/-! Helper lemmas for the Java proofs of CBACT04C. -/

open Jimple

namespace EquivLean.Demo.Cbact04c.Java

theorem jlong_cmp_eq_zero (a b : I64) : (JLong.cmp a b = 0) ↔ a = b := by
  unfold JLong.cmp
  by_cases h1 : a.slt b
  · have hne : a ≠ b := by
      intro h; subst h; simp [BitVec.slt, Int.lt_irrefl] at h1
    simp only [h1, ite_true, hne, iff_false]
    decide
  · simp only [h1]
    by_cases h2 : a = b
    · simp [h2]
    · simp only [h2, ite_false, iff_false]; decide

end EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c.Java

theorem jlong_cmp_eq_zero' (a b : I64) : (JLong.cmp a b = 0#32) ↔ a = b := jlong_cmp_eq_zero a b

/-- `i + 1` on `int` without overflow. -/
theorem i32_toInt_add_one (i : I32) (h0 : 0 ≤ i.toInt) (h1 : i.toInt < 2147483647) :
    (i + 1#32).toInt = i.toInt + 1 := by
  rw [BitVec.toInt_add]
  have : (1#32).toInt = 1 := by decide
  rw [this]
  rw [Int.bmod_def]; split <;> omega

theorem i32_toNat_eq (i : I32) (h0 : 0 ≤ i.toInt) : i.toNat = i.toInt.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at *
  split at h0 <;> omega

theorem i32_toNat_add_one (i : I32) (h0 : 0 ≤ i.toInt) (h1 : i.toInt < 2147483647) :
    (i + 1#32).toNat = i.toNat + 1 := by
  have h2 := i32_toInt_add_one i h0 h1
  rw [i32_toNat_eq i h0, i32_toNat_eq (i + 1#32) (by omega), h2]
  omega

theorem idOf_ref {σ : State} {x : Addr} {fs : List (FieldKey × Value)} {n : I64}
    (h1 : σ.heap x = some (.plain "Cbact04c$Account" fs))
    (h2 : Fields.get fs ("Cbact04c$Account", "id") = some (.long n)) :
    idOf σ (.ref x) = some n := by
  simp [idOf, h1, h2]

theorem idOf_of_acctAt {σ : State} {v : Value} {a : JAcct} (h : AcctAt σ v a) :
    idOf σ v = some a.id := by
  obtain ⟨x, fs, g, rfl, h1, h2, -⟩ := h
  exact idOf_ref h1 h2

theorem mem_take_succ {α : Type} {xs : List α} {n : Nat} (hn : n < xs.length) {x : α}
    (h : x ∈ xs.take (n + 1)) : x ∈ xs.take n ∨ x = xs[n] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hn] at h
  rcases List.mem_append.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

end EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c.Java

/-- A hypothesis hidden from the `jvc` preprocessing (destructuring, forward instantiation). -/
@[irreducible] def Hide (p : Prop) : Prop := p

theorem Hide.intro {p : Prop} (h : p) : Hide p := by unfold Hide; exact h
theorem Hide.elim {p : Prop} (h : Hide p) : p := by unfold Hide at h; exact h

end EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c.Java

theorem strAt_unique {σ : State} {v : Value} {s s' : JStr} (h1 : StrAt σ v s) (h2 : StrAt σ v s') :
    s = s' := by
  obtain ⟨x, rfl, hx⟩ := h1
  obtain ⟨y, hy, hy'⟩ := h2
  cases hy
  rw [hx] at hy'
  cases hy'
  rfl

theorem discAt_unique {σ : State} {v : Value} {d d' : JDisc} (h1 : DiscAt σ v d)
    (h2 : DiscAt σ v d') : d = d' := by
  obtain ⟨x, fs, g, t, rfl, hx, hg, hgs, ht, hts, hc, hr⟩ := h1
  obtain ⟨y, fs', g', t', hy, hy', hg', hgs', ht', hts', hc', hr'⟩ := h2
  cases hy
  rw [hx] at hy'
  cases hy'
  rw [hg] at hg'; cases hg'
  rw [ht] at ht'; cases ht'
  rw [hc] at hc'
  rw [hr] at hr'
  have e1 := strAt_unique hgs hgs'
  have e2 := strAt_unique hts hts'
  simp only [Option.some.injEq, Value.int.injEq, Value.long.injEq] at hc' hr'
  cases d; cases d'
  simp only at e1 e2 hc' hr' ⊢
  subst e1; subst e2; subst hc'; subst hr'
  rfl

theorem acctAt_unique {σ : State} {v : Value} {a a' : JAcct} (h1 : AcctAt σ v a)
    (h2 : AcctAt σ v a') : a = a' := by
  obtain ⟨x, fs, g, rfl, hx, hi, hb, hcc, hcd, hg, hgs⟩ := h1
  obtain ⟨y, fs', g', hy, hy', hi', hb', hcc', hcd', hg', hgs'⟩ := h2
  cases hy
  rw [hx] at hy'
  cases hy'
  rw [hg] at hg'; cases hg'
  rw [hi] at hi'
  rw [hb] at hb'
  rw [hcc] at hcc'
  rw [hcd] at hcd'
  have e1 := strAt_unique hgs hgs'
  simp only [Option.some.injEq, Value.long.injEq] at hi' hb' hcc' hcd'
  cases a; cases a'
  simp only at e1 hi' hb' hcc' hcd' ⊢
  subst e1; subst hi'; subst hb'; subst hcc'; subst hcd'
  rfl

/-- No record of `ys` has the key `(g, t, cat)`. -/
def NoKey (σ : State) (g t : JStr) (cat : I32) (ys : List Value) : Prop :=
  ∀ x ∈ ys, ∀ d, DiscAt σ x d → ¬(d.grp = g ∧ d.ty = t ∧ d.cat = cat)

theorem noKey_step {σ : State} {g t : JStr} {cat : I32} {xs : List Value} {n : Nat} {x : Addr}
    {d : JDisc} (hn : n < xs.length) (hx : xs[n] = .ref x) (hd : DiscAt σ (.ref x) d)
    (hne : ¬(d.grp = g ∧ d.ty = t ∧ d.cat = cat)) (h : NoKey σ g t cat (xs.take n)) :
    NoKey σ g t cat (xs.take (n + 1)) := by
  intro y hy d' hd'
  rcases mem_take_succ hn hy with hy | hy
  · exact h y hy d' hd'
  · rw [hy, hx] at hd'
    rw [← discAt_unique hd hd']
    exact hne

theorem noKey_absurd {σ : State} {g t : JStr} {cat : I32} {rate : I64} {xs : List Value}
    (h : NoKey σ g t cat xs) (hex : ∃ x ∈ xs, DiscAt σ x ⟨g, t, cat, rate⟩) : False := by
  obtain ⟨x, hx, hd⟩ := hex
  exact h x hx _ hd ⟨rfl, rfl, rfl⟩

end EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c.Java

theorem fields_get_cons (k k' : FieldKey) (v : Value) (fs : List (FieldKey × Value)) :
    Fields.get ((k, v) :: fs) k' = if k' = k then some v else Fields.get fs k' := by
  simp only [Fields.get, List.lookup]
  by_cases h : k' = k
  · subst h; simp
  · have : (k' == k) = false := by simp [h]
    simp [this, h]

theorem fields_get_nil (k' : FieldKey) : Fields.get [] k' = none := rfl

end EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c.Java

theorem pairs_length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Pairs R xs ys → xs.length = ys.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Pairs] at h; simp [pairs_length h.2]
  | [], _ :: _, h => by simp [Pairs] at h
  | _ :: _, [], h => by simp [Pairs] at h

theorem pairs_get {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (h : Pairs R xs ys) (n : Nat) (hn : n < xs.length),
      R xs[n] (ys[n]'(by rw [← pairs_length h]; exact hn))
  | [], [], _, n, hn => by simp at hn
  | x :: xs, y :: ys, h, 0, _ => by simp [Pairs] at h; simpa using h.1
  | x :: xs, y :: ys, h, n + 1, hn => by
      simp [Pairs] at h
      simpa using pairs_get h.2 n (by simpa using hn)
  | [], _ :: _, h, _, _ => by simp [Pairs] at h
  | _ :: _, [], h, _, _ => by simp [Pairs] at h

theorem pairs_mono {α β : Type} {R R' : α → β → Prop} (hR : ∀ x y, R x y → R' x y) :
    ∀ {xs : List α} {ys : List β}, Pairs R xs ys → Pairs R' xs ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨hR _ _ h.1, pairs_mono hR h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem pairs_append {α β : Type} {R : α → β → Prop} {x : α} {y : β} (hxy : R x y) :
    ∀ {xs : List α} {ys : List β}, Pairs R xs ys → Pairs R (xs ++ [x]) (ys ++ [y])
  | [], [], _ => ⟨hxy, trivial⟩
  | _ :: _, _ :: _, h => ⟨h.1, pairs_append hxy h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-! ### The heap grows -/

theorem grows_refl (σ : State) : Grows σ σ := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem grows_trans {σ1 σ2 σ3 : State} (h1 : Grows σ1 σ2) (h2 : Grows σ2 σ3) : Grows σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun x hx => by rw [h2.2 x (Nat.lt_of_lt_of_le hx h1.1), h1.2 x hx]⟩

theorem heap_of_grows {σ0 σ : State} {x : Addr} {o : Obj} (hg : Grows σ0 σ)
    (h : σ0.heap x = some o) : σ.heap x = some o := by
  rw [hg.2 x (State.lt_next_of_heap h), h]

theorem grows_setObj {σ0 σ : State} {l : Addr} {o : Obj} (hg : Grows σ0 σ) (hl : σ0.next ≤ l) :
    Grows σ0 (σ.setObj l o) := by
  refine ⟨by rw [State.next_setObj]; exact hg.1, fun x hx => ?_⟩
  have hxl : x ≠ l := by intro h; subst h; exact absurd hx (Nat.not_lt.mpr hl)
  rw [State.heap_setObj, ite_eq_right hxl, hg.2 x hx]

theorem strAt_of_grows {σ0 σ : State} {v : Value} {s : JStr} (hg : Grows σ0 σ)
    (h : StrAt σ0 v s) : StrAt σ v s := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, heap_of_grows hg hx⟩

theorem acctAt_of_grows {σ0 σ : State} {v : Value} {a : JAcct} (hg : Grows σ0 σ)
    (h : AcctAt σ0 v a) : AcctAt σ v a := by
  obtain ⟨x, fs, g, rfl, hx, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨x, fs, g, rfl, heap_of_grows hg hx, h1, h2, h3, h4, h5, strAt_of_grows hg h6⟩

theorem discAt_of_grows {σ0 σ : State} {v : Value} {d : JDisc} (hg : Grows σ0 σ)
    (h : DiscAt σ0 v d) : DiscAt σ v d := by
  obtain ⟨x, fs, g, t, rfl, hx, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨x, fs, g, t, rfl, heap_of_grows hg hx, h1, strAt_of_grows hg h2, h3,
    strAt_of_grows hg h4, h5, h6⟩

theorem catAt_of_grows {σ0 σ : State} {v : Value} {c : JCat} (hg : Grows σ0 σ)
    (h : CatAt σ0 v c) : CatAt σ v c := by
  obtain ⟨x, fs, t, rfl, hx, h1, h2, h3, h4, h5⟩ := h
  exact ⟨x, fs, t, rfl, heap_of_grows hg hx, h1, h2, strAt_of_grows hg h3, h4, h5⟩

theorem idOf_of_grows {σ0 σ : State} {v : Value} {b : JAcct} (hg : Grows σ0 σ)
    (h : AcctAt σ0 v b) : idOf σ v = idOf σ0 v := by
  obtain ⟨x, fs, g, rfl, hx, -⟩ := h
  simp only [idOf, heap_of_grows hg hx, hx]

/-- A list object is changed: strings and plain objects are not. -/
theorem strAt_setObj_list {σ : State} {l : Addr} {k : ListKind} {ys : List Value} {m : Nat}
    {o : Obj} {v : Value} {s : JStr} (hl : σ.heap l = some (.list k ys m)) (h : StrAt σ v s) :
    StrAt (σ.setObj l o) v s := by
  obtain ⟨x, rfl, hx⟩ := h
  have hxl : x ≠ l := by intro h; subst h; rw [hl] at hx; cases hx
  exact ⟨x, rfl, by rw [State.heap_setObj, ite_eq_right hxl, hx]⟩

theorem acctAt_setObj_list {σ : State} {l : Addr} {k : ListKind} {ys : List Value} {m : Nat}
    {o : Obj} {v : Value} {a : JAcct} (hl : σ.heap l = some (.list k ys m)) (h : AcctAt σ v a) :
    AcctAt (σ.setObj l o) v a := by
  obtain ⟨x, fs, g, rfl, hx, h1, h2, h3, h4, h5, h6⟩ := h
  have hxl : x ≠ l := by intro h; subst h; rw [hl] at hx; cases hx
  exact ⟨x, fs, g, rfl, by rw [State.heap_setObj, ite_eq_right hxl, hx], h1, h2, h3, h4, h5,
    strAt_setObj_list hl h6⟩

end EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c.Java

theorem grows_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 := by
  refine ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun x hx => ?_⟩
  rw [State.heap_alloc, ite_eq_right (Nat.ne_of_lt hx)]

theorem targets_static {P : Program} {sig : MethodSig} {m : MethodRef}
    (h : P.selectStatic sig = .jimple m) (hb : m.decl.body.isSome = true) : Targets P sig m :=
  ⟨Or.inl h, hb⟩

/-- `fr'.get k = some v` for a frame built by `setLocal`s, from facts about the old frame. -/
macro "frame_simp" " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := { decide := true }) only [Frame.get_setLocal, ite_true, ite_false,
    reduceIte, $hs,*])

end EquivLean.Demo.Cbact04c.Java

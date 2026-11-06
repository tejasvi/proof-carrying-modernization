import EquivLean.Demo.Jimple.Cbact04c.JavaLib
import EquivLean.Demo.Jimple.Cbact04c.Fixed.Model

/-!
# Helper lemmas for the Java proofs of the fixed port

The facts of `Cbact04c/JavaLib.lean` that mention the representation predicates, for the predicates of
any class names (`Cbact04c/Fixed/Model.lean`); the class-independent ones are used from `EquivLean.Demo.Cbact04c.Java`.
-/

open Jimple EquivLean.Demo.Cbact04c.Java

namespace EquivLean.Demo.Cbact04c.JavaF

theorem idOfC_ref {A : ClassName} {σ : State} {x : Addr} {fs : List (FieldKey × Value)} {n : I64}
    (h1 : σ.heap x = some (.plain A fs)) (h2 : Fields.get fs (A, "id") = some (.long n)) :
    idOfC A σ (.ref x) = some n := by
  simp [idOfC, h1, h2]

theorem idOfC_of_acctAt {A : ClassName} {σ : State} {v : Value} {a : JAcct}
    (h : AcctAtC A σ v a) : idOfC A σ v = some a.id := by
  obtain ⟨x, fs, g, rfl, h1, h2, -⟩ := h
  exact idOfC_ref h1 h2

theorem discAtC_unique {D : ClassName} {σ : State} {v : Value} {d d' : JDisc}
    (h1 : DiscAtC D σ v d) (h2 : DiscAtC D σ v d') : d = d' := by
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

/-- No record of `ys` has the key `(g, t, cat)`. -/
def NoKeyC (D : ClassName) (σ : State) (g t : JStr) (cat : I32) (ys : List Value) : Prop :=
  ∀ x ∈ ys, ∀ d, DiscAtC D σ x d → ¬(d.grp = g ∧ d.ty = t ∧ d.cat = cat)

theorem noKeyC_step {D : ClassName} {σ : State} {g t : JStr} {cat : I32} {xs : List Value}
    {n : Nat} {x : Addr} {d : JDisc} (hn : n < xs.length) (hx : xs[n] = .ref x)
    (hd : DiscAtC D σ (.ref x) d) (hne : ¬(d.grp = g ∧ d.ty = t ∧ d.cat = cat))
    (h : NoKeyC D σ g t cat (xs.take n)) : NoKeyC D σ g t cat (xs.take (n + 1)) := by
  intro y hy d' hd'
  rcases mem_take_succ hn hy with hy | hy
  · exact h y hy d' hd'
  · rw [hy, hx] at hd'
    rw [← discAtC_unique hd hd']
    exact hne

theorem noKeyC_absurd {D : ClassName} {σ : State} {g t : JStr} {cat : I32} {rate : I64}
    {xs : List Value} (h : NoKeyC D σ g t cat xs)
    (hex : ∃ x ∈ xs, DiscAtC D σ x ⟨g, t, cat, rate⟩) : False := by
  obtain ⟨x, hx, hd⟩ := hex
  exact h x hx _ hd ⟨rfl, rfl, rfl⟩

theorem acctAtC_of_grows {A : ClassName} {σ0 σ : State} {v : Value} {a : JAcct}
    (hg : Grows σ0 σ) (h : AcctAtC A σ0 v a) : AcctAtC A σ v a := by
  obtain ⟨x, fs, g, rfl, hx, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨x, fs, g, rfl, heap_of_grows hg hx, h1, h2, h3, h4, h5, strAt_of_grows hg h6⟩

theorem discAtC_of_grows {D : ClassName} {σ0 σ : State} {v : Value} {d : JDisc}
    (hg : Grows σ0 σ) (h : DiscAtC D σ0 v d) : DiscAtC D σ v d := by
  obtain ⟨x, fs, g, t, rfl, hx, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨x, fs, g, t, rfl, heap_of_grows hg hx, h1, strAt_of_grows hg h2, h3,
    strAt_of_grows hg h4, h5, h6⟩

theorem idOfC_of_grows {A : ClassName} {σ0 σ : State} {v : Value} {b : JAcct}
    (hg : Grows σ0 σ) (h : AcctAtC A σ0 v b) : idOfC A σ v = idOfC A σ0 v := by
  obtain ⟨x, fs, g, rfl, hx, -⟩ := h
  simp only [idOfC, heap_of_grows hg hx, hx]

theorem acctAtC_setObj_list {A : ClassName} {σ : State} {l : Addr} {k : ListKind}
    {ys : List Value} {m : Nat} {o : Obj} {v : Value} {a : JAcct}
    (hl : σ.heap l = some (.list k ys m)) (h : AcctAtC A σ v a) :
    AcctAtC A (σ.setObj l o) v a := by
  obtain ⟨x, fs, g, rfl, hx, h1, h2, h3, h4, h5, h6⟩ := h
  have hxl : x ≠ l := by intro h; subst h; rw [hl] at hx; cases hx
  exact ⟨x, fs, g, rfl, by rw [State.heap_setObj, ite_eq_right hxl, hx], h1, h2, h3, h4, h5,
    strAt_setObj_list hl h6⟩

end EquivLean.Demo.Cbact04c.JavaF

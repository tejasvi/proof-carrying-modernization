import EquivLean.Modernize.Cbstm03a.Java.Text.Lib

/-!
# CBSTM03A → Java: more lemmas for the output methods

The `Result` object rebuilt from its object and its three lists in a later state (`resAtL_of`); frames by a set of
updated addresses (`Keeps`): monotone in the set, strings stay when none of them is updated.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space Kept GrowsK grows_split Keeps
  keeps_refl keeps_trans keeps_setObj keeps_alloc keeps_of_grows keeps_setObj' keeps_alloc' keeps_grows'
  growsK_elim)

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

theorem resAtL_of {σ0 σ : State} {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool}
    {disp' st' ht' : List JStr} {ab' : Bool} {fs' : List (FieldKey × Value)}
    (hR : ResAtL σ0 res ld ls lh disp st ht ab) (hres : σ.heap res = some (.plain resC fs'))
    (gd : Fields.get fs' (resC, "displays") = some (.ref ld))
    (gs : Fields.get fs' (resC, "stmtFileWrites") = some (.ref ls))
    (gh : Fields.get fs' (resC, "htmlFileWrites") = some (.ref lh))
    (gab : Fields.get fs' (resC, "abended") = some (.int (if ab' then 1 else 0)))
    (Ld : ListAt σ ld disp') (Ls : ListAt σ ls st') (Lh : ListAt σ lh ht') :
    ResAtL σ res ld ls lh disp' st' ht' ab' := by
  obtain ⟨-, -, -, -, -, -, n1, n2, n3, -⟩ := hR
  exact ⟨fs', hres, gd, gs, gh, gab, n1, n2, n3, Ld, Ls, Lh⟩

theorem keeps_mono {A B : Addr → Prop} {σ σ' : State} (hAB : ∀ y, A y → B y) (h : Keeps A σ σ') :
    Keeps B σ σ' :=
  ⟨h.1, fun y hy hB => h.2 y hy (fun hA => hB (hAB y hA))⟩

theorem strMono_of_keeps {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ')
    (hA : ∀ y s, σ.heap y = some (.str s) → ¬ A y) : StrMono σ σ' :=
  fun y s hy => by rw [hk.2 y (State.lt_next_of_heap hy) (hA y s hy), hy]

theorem heap_of_keeps {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') {y : Addr} (hy : y < σ.next)
    (hA : ¬ A y) : σ'.heap y = σ.heap y :=
  hk.2 y hy hA

/-- The `Result` object and its display list. -/
def In2 (a b : Addr) (y : Addr) : Prop := y = a ∨ y = b

theorem in2_l {a b : Addr} : In2 a b a := Or.inl rfl
theorem in2_r {a b : Addr} : In2 a b b := Or.inr rfl

theorem inRes_of_in2 {res ld ls lh : Addr} : ∀ y, In2 res ld y → InRes res ld ls lh y := by
  rintro y (e | e)
  · exact Or.inl e
  · exact Or.inr (Or.inl e)

/-- No address of `In2 res ld` holds a string (the `Result` object, a list). -/
theorem not_in2_of_str {σ : State} {res ld : Addr} {fs : List (FieldKey × Value)} {xs : List Value} {m : Nat}
    (hres : σ.heap res = some (.plain resC fs)) (hld : σ.heap ld = some (.list .arrayList xs m)) :
    ∀ y s, σ.heap y = some (.str s) → ¬ In2 res ld y := by
  rintro y s hy (rfl | rfl)
  · rw [hres] at hy; cases hy
  · rw [hld] at hy; cases hy

/-- `Keeps (In2 a b)` of a state built by updates at `a`, `b`, allocations and callees (`GrowsK`). -/
macro "txt_keeps2" : tactic => `(tactic| repeat (first | (refine keeps_setObj' ?_ (by first | exact in2_l | exact in2_r)) | (refine keeps_alloc' ?_) | (refine keeps_grows' ?_ (growsK_elim (by assumption))) | exact keeps_refl _ _))

end EquivLean.Modernize.Cbstm03a.Java.Txt

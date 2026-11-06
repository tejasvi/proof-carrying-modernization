import EquivLean.Modernize.Cbstm03a.Java.Run7.Rep

/-!
# CBSTM03A → Java `run`, statement 52: heap frames (strings, text arrays, the `Result` object, records)

Copied from `CbARun1.Lem` (cbA-run1) into this namespace.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK growsK_elim
  grows_split grows_refl grows_trans keeps_trans keeps_of_grows keeps_setObj keeps_refl forall2_imp heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg7

theorem strMono_refl (σ : State) : StrMono σ σ := fun _ _ h => h

theorem strMono_trans {σ1 σ2 σ3 : State} (h1 : StrMono σ1 σ2) (h2 : StrMono σ2 σ3) : StrMono σ1 σ3 :=
  fun x s h => h2 x s (h1 x s h)

theorem strMono_of_grows {σ σ' : State} (h : Grows σ σ') : StrMono σ σ' := fun x s hx => by
  rw [h.2 x (State.lt_next_of_heap hx), hx]

theorem jstrAt_mono {σ σ' : State} {v : Value} {s : JStr} (h : JStrAt σ v s) (hm : StrMono σ σ') :
    JStrAt σ' v s := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, hm x s hx⟩

theorem forall2_jstr_mono {σ σ' : State} {xs : List Value} {ts : List JStr} (h : Forall2 (JStrAt σ) xs ts)
    (hm : StrMono σ σ') : Forall2 (JStrAt σ') xs ts :=
  forall2_imp (fun _ _ h => jstrAt_mono h hm) h

theorem textsAt_mono {σ σ' : State} {a : Addr} {ts : List JStr} {n : Nat} (h : TextsAt σ a ts n)
    (hm : StrMono σ σ') (ha : σ'.heap a = σ.heap a) : TextsAt σ' a ts n := by
  obtain ⟨xs, hx, hf⟩ := h
  exact ⟨xs, ha.trans hx, forall2_jstr_mono hf hm⟩

theorem listAt_nil_of_heap {σ σ' : State} {l : Addr} (h : ListAt σ l []) (he : σ'.heap l = σ.heap l) :
    ListAt σ' l [] := by
  obtain ⟨xs, m, hl, hf⟩ := h
  cases hf
  exact ⟨[], m, he.trans hl, .nil⟩

theorem resAtL_init_of_heap {σ σ' : State} {res ld ls lh : Addr} (h : ResAtL σ res ld ls lh [] [] [] false)
    (h1 : σ'.heap res = σ.heap res) (h2 : σ'.heap ld = σ.heap ld) (h3 : σ'.heap ls = σ.heap ls)
    (h4 : σ'.heap lh = σ.heap lh) : ResAtL σ' res ld ls lh [] [] [] false := by
  obtain ⟨fs, hr, g1, g2, g3, g4, n1, n2, n3, l1, l2, l3⟩ := h
  exact ⟨fs, h1.trans hr, g1, g2, g3, g4, n1, n2, n3, listAt_nil_of_heap l1 h2, listAt_nil_of_heap l2 h3,
    listAt_nil_of_heap l3 h4⟩

/-- `ResAtL` kept by a state whose heap agrees with `σ` on the objects that are not arrays. -/
theorem resAtL_of_agree {σ σ' : State} {res ld ls lh : Addr} {d s t : List JStr} {ab : Bool}
    (h : ResAtL σ res ld ls lh d s t ab)
    (hag : ∀ y o, σ.heap y = some o → (∀ et vs, o ≠ .array et vs) → σ'.heap y = some o) :
    ResAtL σ' res ld ls lh d s t ab := by
  obtain ⟨fs, hr, g1, g2, g3, g4, n1, n2, n3, ⟨x1, m1, e1, f1⟩, ⟨x2, m2, e2, f2⟩, ⟨x3, m3, e3, f3⟩⟩ := h
  have hsm : StrMono σ σ' := fun y s hy => hag y _ hy (fun _ _ e => by cases e)
  exact ⟨fs, hag _ _ hr (fun _ _ e => by cases e), g1, g2, g3, g4, n1, n2, n3,
    ⟨x1, m1, hag _ _ e1 (fun _ _ e => by cases e), forall2_jstr_mono f1 hsm⟩,
    ⟨x2, m2, hag _ _ e2 (fun _ _ e => by cases e), forall2_jstr_mono f2 hsm⟩,
    ⟨x3, m3, hag _ _ e3 (fun _ _ e => by cases e), forall2_jstr_mono f3 hsm⟩⟩

theorem sfld_mono {σ σ' : State} {c : ClassName} {fs : List (FieldKey × Value)} {f : String} {s : JStr}
    (h : SFld σ c fs f s) (hm : StrMono σ σ') : SFld σ' c fs f s := by
  obtain ⟨x, h1, h2, h3⟩ := h
  exact ⟨x, h1, hm x s h2, h3⟩

theorem acctAt_grows {σ σ' : State} {x : Addr} {t : AcctR} (h : AcctAt σ x t) (hg : Grows σ σ') :
    AcctAt σ' x t := by
  have hm := strMono_of_grows hg
  obtain ⟨fs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨fs, heap_grows hg h0, h1, sfld_mono h2 hm, h3, h4, h5, sfld_mono h6 hm, sfld_mono h7 hm,
    sfld_mono h8 hm, h9, h10, sfld_mono h11 hm, sfld_mono h12 hm, sfld_mono h13 hm⟩

/-- Record `k` of an input file: a reference to a record object holding `ts[k]`. -/
theorem recsAt_elem {α : Type} {R : State → Value → Option α → Prop} {σ : State} {xs : List Value} {ts : List α}
    (hf : Forall2 (fun v t => R σ v (some t)) xs ts) (k : Nat) (hk : k < ts.length) :
    ∃ hx : k < xs.length, R σ (xs[k]'hx) (some (ts[k]'hk)) := by
  have hx : k < xs.length := by rw [forall2_length hf]; exact hk
  exact ⟨hx, forall2_getElem hf k hx hk⟩

theorem grows_alloc_r {σ0 σ : State} (h : Grows σ0 σ) (o : Obj) : Grows σ0 (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ_of_le h.1, fun x hx => by
    rw [State.heap_alloc_of_lt (Nat.lt_of_lt_of_le hx h.1), h.2 x hx]⟩

theorem grows_setObj_r {σ0 σ : State} {a : Addr} (h : Grows σ0 σ) (ha : σ0.next ≤ a) (o : Obj) :
    Grows σ0 (σ.setObj a o) :=
  ⟨by rw [State.next_setObj]; exact h.1, fun x hx => by
    have hne : x ≠ a := fun e => Nat.lt_irrefl a (Nat.lt_of_lt_of_le (e ▸ hx) ha)
    rw [State.heap_setObj, if_neg hne, h.2 x hx]⟩

theorem initOf_of_inits {σ σ' : State} (h : σ'.inits = σ.inits) (c : ClassName) : σ'.initOf c = σ.initOf c := by
  unfold State.initOf; rw [h]

end EquivLean.Modernize.Cbstm03a.Java.Seg7

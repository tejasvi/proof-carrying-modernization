import EquivLean.Modernize.Cbstm03a.Java.Cs.Cut

/-!
# CBSTM03A → Java: `createStatement`, closing the cut points after a computation

`cutI_next`: a cut point after statements that only grow the heap (new strings, callees with `Grows`), from the
cut point before; `locsAt_frame`: the string locals still there. The texts of `Iface1`'s `para`/`star`
(`paraStr`, `starStr`) are `Iface3`'s (`paraT`, `starT`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

/-! ## Texts -/

theorem appStr_eq_appT (b : JStr) (cap : Int) (hc : 0 ≤ cap) (src : JStr) (d : Option JStr) :
    appStr b cap src d = appT b cap.toNat src d := by
  cases d <;>
  · simp only [appStr, appT, cutAt, cutAtT]
    split
    · next h =>
      have : cap.toNat - b.length = 0 := by omega
      rw [this, List.take_zero, List.append_nil]
    · next h =>
      have : (cap - (b.length : Int)).toNat = cap.toNat - b.length := by omega
      rw [this]

theorem appStr100 (b src : JStr) (d : Option JStr) : appStr b 100 src d = appT b 100 src d :=
  appStr_eq_appT b 100 (by decide) src d

theorem paraStr_eq (p f : JStr) : paraStr p f = paraT p f := by
  unfold paraStr paraT
  simp only [appStr100]
  rfl

theorem starStr_eq (p f : JStr) : starStr p f = starT p f := by
  unfold starStr starT
  simp only [appStr100]
  rfl

/-! ## Cut points after a computation -/

theorem locsAt_frame {σ σ' : State} {fr fr' : Frame} (hg : Grows σ σ') :
    ∀ {L : List (Nat × JStr)}, LocsAt σ fr L → (∀ i ∈ L.map Prod.fst, fr'.get i = fr.get i) → LocsAt σ' fr' L
  | [], _, _ => trivial
  | (i, s) :: rest, ⟨⟨x, h1, h2, h3⟩, h4⟩, hf => by
    simp only [List.map_cons, List.mem_cons, forall_eq_or_imp] at hf
    exact ⟨⟨x, by rw [hf.1, h1], by rw [hg.2 x (State.lt_next_of_heap h2), h2], h3⟩, locsAt_frame hg h4 hf.2⟩

/-- The cut point after a computation that only grows the heap. -/
theorem cutI_next {g : G} {ns nh : Nat} {L L' : List (Nat × JStr)} {bal bal' : Bool} {σ0 σ σ' : State}
    {fr fr' : Frame} (hI : CutI g ns nh L bal σ0 fr σ) (hg : Grows σ σ') (h22 : fr'.get 22 = fr.get 22)
    (hin : σ'.inits = σ.inits) (hst : σ'.statics = σ.statics) (hL : LocsAt σ' fr' L')
    (hb : bal' = true → fr'.get 0 = some (.long (BitVec.ofInt 64 (zonedVal (sub g.a 12 24))))) :
    CutI g ns nh L' bal' σ0 fr' σ' := by
  have hres := hI.1.1
  have hR := hI.1.2.1
  have hk0 := hI.1.2.2.1
  have hin0 := hI.1.2.2.2.1
  have hst0 := hI.1.2.2.2.2.1
  have hini := hI.1.2.2.2.2.2
  refine ⟨⟨by rw [h22, hres], resAtL_grows hR hg, keepsRes_trans hk0 (keepsRes_of_grows hg), by rw [hin, hin0],
    by rw [hst, hst0], ?_⟩, hL, hb⟩
  unfold State.initOf at hini ⊢
  rw [hin]
  exact hini

theorem grows_k {σ0 σ σ' : State} (h : Grows σ0 σ) (hk : GrowsK σ σ') : Grows σ0 σ' :=
  grows_trans h (growsK_elim hk)

theorem grows_al {σ0 σ : State} {o : Obj} (h : Grows σ0 σ) : Grows σ0 (σ.alloc o).2 :=
  grows_trans h (grows_alloc σ o)

/-- `Grows σ0 σ` for a state built from `σ0` by allocations and callees (`GrowsK`). -/
macro "grows_tac" : tactic => `(tactic| repeat (first | exact grows_refl _ | refine grows_al ?_ | refine grows_k ?_ (by assumption)))

end EquivLean.Modernize.Cbstm03a.Java.Cs

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

theorem locsAt_mem {σ : State} {fr : Frame} : ∀ {L : List (Nat × JStr)}, LocsAt σ fr L → ∀ {p}, p ∈ L →
    ∃ x, fr.get p.1 = some (.ref x) ∧ σ.heap x = some (.str p.2) ∧ p.2.length < 2147483648
  | [], _, _, h => by cases h
  | (_, _) :: _, ⟨h1, h2⟩, _, hp => by
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h1
    · exact locsAt_mem h2 hp

theorem locsAt_of_mem {σ : State} {fr : Frame} : ∀ {L : List (Nat × JStr)},
    (∀ p ∈ L, ∃ x, fr.get p.1 = some (.ref x) ∧ σ.heap x = some (.str p.2) ∧ p.2.length < 2147483648) →
    LocsAt σ fr L
  | [], _ => trivial
  | (_, _) :: _, h => ⟨h _ List.mem_cons_self, locsAt_of_mem fun p hp => h p (List.mem_cons_of_mem _ hp)⟩

theorem locsAt_sub {σ : State} {fr : Frame} {L L' : List (Nat × JStr)} (h : ∀ p ∈ L', p ∈ L)
    (hL : LocsAt σ fr L) : LocsAt σ fr L' :=
  locsAt_of_mem fun p hp => locsAt_mem hL (h p hp)

theorem sub_length_le (s : JStr) (b e : Nat) : (sub s b e).length ≤ e - b := by
  unfold sub
  simp only [List.length_drop, List.length_take]
  omega

theorem heap_str_eq {σ : State} {w : Addr} {s s' : JStr} (h : σ.heap w = some (.str s)) (e : s = s') :
    σ.heap w = some (.str s') := e ▸ h

theorem heap_alloc_str {σ : State} {a : Addr} {s s' : JStr} (ha : a = σ.next) (e : s = s') :
    (σ.alloc (.str s)).2.heap a = some (.str s') := by
  rw [State.heap_alloc, if_pos ha, e]

end EquivLean.Modernize.Cbstm03a.Java.Cs

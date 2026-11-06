import EquivLean.Modernize.Cbstm03a.Java.Cs.Base

/-!
# CBSTM03A → Java: `createStatement`, frame lemmas

Strings stay across heaps that only grow and across updates of the `Result` object and its lists; the `Result`
object after an allocation or a callee that only grows the heap; the cut-point invariant after a call of `stmt`
or `html` (`cutI_ht`, `cutI_st`). Some lemmas follow cbA-text's `CbAText.Lib`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

theorem grows_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun x hx => State.heap_alloc_of_lt hx o⟩

theorem strMono_of_grows {σ σ' : State} (h : Grows σ σ') : StrMono σ σ' :=
  fun x s hx => by rw [h.2 x (State.lt_next_of_heap hx), hx]

theorem forall2_jstr_mono {σ σ' : State} (h : StrMono σ σ') :
    ∀ {xs : List Value} {ss : List JStr}, Forall2 (JStrAt σ) xs ss → Forall2 (JStrAt σ') xs ss
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h1 h2 => .cons (by obtain ⟨x, rfl, hx⟩ := h1; exact ⟨x, rfl, h x _ hx⟩)
      (forall2_jstr_mono h h2)

theorem listAt_grows {σ σ' : State} {l : Addr} {ss : List JStr} (h : ListAt σ l ss) (hg : Grows σ σ') :
    ListAt σ' l ss := by
  obtain ⟨xs, m, h1, h2⟩ := h
  exact ⟨xs, m, by rw [hg.2 l (State.lt_next_of_heap h1), h1], forall2_jstr_mono (strMono_of_grows hg) h2⟩

theorem resAtL_grows {σ σ' : State} {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool}
    (h : ResAtL σ res ld ls lh disp st ht ab) (hg : Grows σ σ') : ResAtL σ' res ld ls lh disp st ht ab := by
  obtain ⟨fs, hres, gd, gs, gh, gab, n1, n2, n3, Ld, Ls, Lh⟩ := h
  exact ⟨fs, by rw [hg.2 res (State.lt_next_of_heap hres), hres], gd, gs, gh, gab, n1, n2, n3,
    listAt_grows Ld hg, listAt_grows Ls hg, listAt_grows Lh hg⟩

theorem resAtL_alloc {σ : State} {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool}
    (h : ResAtL σ res ld ls lh disp st ht ab) (o : Obj) : ResAtL (σ.alloc o).2 res ld ls lh disp st ht ab :=
  resAtL_grows h (grows_alloc σ o)

/-! ## `KeepsRes` -/

theorem keepsRes_trans {res ld ls lh : Addr} {σ1 σ2 σ3 : State} (h1 : KeepsRes res ld ls lh σ1 σ2)
    (h2 : KeepsRes res ld ls lh σ2 σ3) : KeepsRes res ld ls lh σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun y hy a b c d => by
    rw [h2.2 y (Nat.lt_of_lt_of_le hy h1.1) a b c d, h1.2 y hy a b c d]⟩

theorem keepsRes_of_grows {res ld ls lh : Addr} {σ σ' : State} (h : Grows σ σ') : KeepsRes res ld ls lh σ σ' :=
  ⟨h.1, fun y hy _ _ _ _ => h.2 y hy⟩

/-- A string of `σ` stays when the path keeps everything but the `Result` object and its lists. -/
theorem str_keepsRes {σ σ' : State} {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool}
    (hR : ResAtL σ res ld ls lh disp st ht ab) (hk : KeepsRes res ld ls lh σ σ') {x : Addr} {s : JStr}
    (hx : σ.heap x = some (.str s)) : σ'.heap x = some (.str s) := by
  obtain ⟨fs, hres, -, -, -, -, -, -, -, ⟨xd, md, hld, -⟩, ⟨xs, ms, hls, -⟩, ⟨xh, mh, hlh, -⟩⟩ := hR
  have ne : ∀ y (o : Obj), σ.heap y = some o → (∀ s, o ≠ .str s) → x ≠ y := by
    intro y o hy ho e
    subst e
    rw [hx] at hy
    exact ho s (Option.some.inj hy).symm
  rw [hk.2 x (State.lt_next_of_heap hx) (ne _ _ hres (fun _ h => by cases h))
    (ne _ _ hld (fun _ h => by cases h)) (ne _ _ hls (fun _ h => by cases h)) (ne _ _ hlh (fun _ h => by cases h)),
    hx]

theorem locsAt_keepsRes {σ σ' : State} {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool}
    (hR : ResAtL σ res ld ls lh disp st ht ab) (hk : KeepsRes res ld ls lh σ σ') {fr : Frame} :
    ∀ {L : List (Nat × JStr)}, LocsAt σ fr L → LocsAt σ' fr L
  | [], _ => trivial
  | (_, _) :: _, ⟨⟨x, h1, h2, h3⟩, h4⟩ => ⟨⟨x, h1, str_keepsRes hR hk h2, h3⟩, locsAt_keepsRes hR hk h4⟩

/-! ## The lines written so far -/

theorem take_push {base L : List JStr} {n : Nat} {line : JStr} (h : L[n]? = some line) :
    base ++ L.take n ++ [line] = base ++ L.take (n + 1) := by
  rw [List.take_succ, h, List.append_assoc]
  rfl

/-- After `html(res, s)` from a cut point (the argument allocated first or not: `σ ≤ σ1`), the next HTML line
written. -/
theorem cutI_ht {g : G} {ns nh : Nat} {L : List (Nat × JStr)} {bal : Bool} {σ0 σ σ1 σ' : State} {fr : Frame}
    {line : JStr} (hI : CutI g ns nh L bal σ0 fr σ) (h1 : Grows σ σ1)
    (hR : ResAtL σ' g.res g.ld g.ls g.lh g.disp (g.st ++ (jCreateStatement g.c g.a).1.take ns)
      (g.ht ++ (jCreateStatement g.c g.a).2.take nh ++ [line]) g.ab)
    (hk : KeepsRes g.res g.ld g.ls g.lh σ1 σ') (hin : σ'.inits = σ1.inits) (hst : σ'.statics = σ1.statics)
    (hin1 : σ1.inits = σ.inits) (hst1 : σ1.statics = σ.statics)
    (hline : (jCreateStatement g.c g.a).2[nh]? = some line) : CutI g ns (nh + 1) L bal σ0 fr σ' := by
  obtain ⟨⟨hres, hR0, hk0, hin0, hst0, hini⟩, hL, hb⟩ := hI
  have hk1 : KeepsRes g.res g.ld g.ls g.lh σ σ' := keepsRes_trans (keepsRes_of_grows h1) hk
  refine ⟨⟨hres, by rw [← take_push hline]; exact hR, keepsRes_trans hk0 hk1, by rw [hin, hin1, hin0],
    by rw [hst, hst1, hst0], ?_⟩, locsAt_keepsRes hR0 hk1 hL, hb⟩
  unfold State.initOf at hini ⊢
  rw [hin, hin1]
  exact hini

/-- After `stmt(res, s)` from a cut point, the next statement line written. -/
theorem cutI_st {g : G} {ns nh : Nat} {L : List (Nat × JStr)} {bal : Bool} {σ0 σ σ1 σ' : State} {fr : Frame}
    {line : JStr} (hI : CutI g ns nh L bal σ0 fr σ) (h1 : Grows σ σ1)
    (hR : ResAtL σ' g.res g.ld g.ls g.lh g.disp (g.st ++ (jCreateStatement g.c g.a).1.take ns ++ [line])
      (g.ht ++ (jCreateStatement g.c g.a).2.take nh) g.ab)
    (hk : KeepsRes g.res g.ld g.ls g.lh σ1 σ') (hin : σ'.inits = σ1.inits) (hst : σ'.statics = σ1.statics)
    (hin1 : σ1.inits = σ.inits) (hst1 : σ1.statics = σ.statics)
    (hline : (jCreateStatement g.c g.a).1[ns]? = some line) : CutI g (ns + 1) nh L bal σ0 fr σ' := by
  obtain ⟨⟨hres, hR0, hk0, hin0, hst0, hini⟩, hL, hb⟩ := hI
  have hk1 : KeepsRes g.res g.ld g.ls g.lh σ σ' := keepsRes_trans (keepsRes_of_grows h1) hk
  refine ⟨⟨hres, by rw [← take_push hline]; exact hR, keepsRes_trans hk0 hk1, by rw [hin, hin1, hin0],
    by rw [hst, hst1, hst0], ?_⟩, locsAt_keepsRes hR0 hk1 hL, hb⟩
  unfold State.initOf at hini ⊢
  rw [hin, hin1]
  exact hini

end EquivLean.Modernize.Cbstm03a.Java.Cs

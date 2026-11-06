import EquivLean.Modernize.Cbstm03a.Java.Iface3
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java: lemmas for the output methods

Strings stay (`StrMono`) across heaps that only grow and across updates of non-string objects; a list holding
some strings, after one more string object is appended to it (`listAt_push`); the `Result` object after an
append to one of its lists (`resAtL_push_st`, `resAtL_push_ht`); `KeepsRes` from the frames of a path
(`keepsRes_of_keeps` with `Keeps` of `Cbstm03bJava`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space Kept GrowsK grows_split Keeps
  keeps_refl keeps_trans keeps_setObj keeps_alloc keeps_of_grows keeps_setObj' keeps_alloc' keeps_grows'
  growsK_elim)

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

/-! ## Strings stay -/

theorem strMono_refl (σ : State) : StrMono σ σ := fun _ _ h => h

theorem strMono_trans {σ1 σ2 σ3 : State} (h1 : StrMono σ1 σ2) (h2 : StrMono σ2 σ3) : StrMono σ1 σ3 :=
  fun x s h => h2 x s (h1 x s h)

theorem strMono_of_grows {σ σ' : State} (h : Grows σ σ') : StrMono σ σ' :=
  fun x s hx => by rw [h.2 x (State.lt_next_of_heap hx), hx]

theorem strMono_setObj {σ : State} {l : Addr} {o : Obj} (hl : ∀ s, σ.heap l ≠ some (.str s)) :
    StrMono σ (σ.setObj l o) := by
  intro x s hx
  have hne : x ≠ l := fun e => hl s (e ▸ hx)
  rw [State.heap_setObj, if_neg hne, hx]

theorem strMono_alloc (σ : State) (o : Obj) : StrMono σ (σ.alloc o).2 :=
  fun x s hx => by rw [State.heap_alloc_of_lt (State.lt_next_of_heap hx), hx]

theorem jstrAt_mono {σ σ' : State} (h : StrMono σ σ') {v : Value} {s : JStr} (hv : JStrAt σ v s) :
    JStrAt σ' v s := by
  obtain ⟨x, rfl, hx⟩ := hv
  exact ⟨x, rfl, h x s hx⟩

theorem forall2_jstr_mono {σ σ' : State} (h : StrMono σ σ') :
    ∀ {xs : List Value} {ss : List JStr}, Forall2 (JStrAt σ) xs ss → Forall2 (JStrAt σ') xs ss
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h1 h2 => .cons (jstrAt_mono h h1) (forall2_jstr_mono h h2)

theorem forall2_snoc {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} {a : α} {b : β}, Forall2 R xs ys → R a b → Forall2 R (xs ++ [a]) (ys ++ [b])
  | [], [], _, _, .nil, h => .cons h .nil
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (forall2_snoc h2 h)

/-! ## Lists of strings -/

theorem listAt_mono {σ σ' : State} {l : Addr} {ss : List JStr} (h : ListAt σ l ss) (hl : σ'.heap l = σ.heap l)
    (hm : StrMono σ σ') : ListAt σ' l ss := by
  obtain ⟨xs, m, h1, h2⟩ := h
  exact ⟨xs, m, by rw [hl, h1], forall2_jstr_mono hm h2⟩

theorem listAt_heap {σ : State} {l : Addr} {ss : List JStr} (h : ListAt σ l ss) :
    ∃ xs m, σ.heap l = some (.list .arrayList xs m) := by
  obtain ⟨xs, m, h1, -⟩ := h
  exact ⟨xs, m, h1⟩

theorem listAt_lt {σ : State} {l : Addr} {ss : List JStr} (h : ListAt σ l ss) : l < σ.next := by
  obtain ⟨xs, m, h1, -⟩ := h
  exact State.lt_next_of_heap h1

theorem not_str_of_list {σ : State} {l : Addr} {xs : List Value} {m : Nat}
    (h : σ.heap l = some (.list .arrayList xs m)) : ∀ s, σ.heap l ≠ some (.str s) := by
  intro s hs
  rw [h] at hs
  cases hs

/-- The list at `l` after the string object at `w` is appended to it (in a state `σ1` that agrees with `σ0` on
`l` and keeps its strings). -/
theorem listAt_push {σ0 σ1 : State} {l : Addr} {ss : List JStr} {xs : List Value} {m : Nat} {w : Addr}
    {line : JStr} (hL : ListAt σ0 l ss) (hl : σ0.heap l = some (.list .arrayList xs m)) (hm : StrMono σ0 σ1)
    (hl1 : σ1.heap l = σ0.heap l) (hlt : l < σ1.next) (hw : σ1.heap w = some (.str line)) :
    ListAt (σ1.setObj l (.list .arrayList (xs ++ [.ref w]) (m + 1))) l (ss ++ [line]) := by
  obtain ⟨xs', m', h1, h2⟩ := hL
  rw [hl] at h1
  cases h1
  have hl1' : σ1.heap l = some (.list .arrayList xs m) := by rw [hl1, hl]
  have hm1 : StrMono σ1 (σ1.setObj l (.list .arrayList (xs ++ [.ref w]) (m + 1))) :=
    strMono_setObj (not_str_of_list hl1')
  exact ⟨xs ++ [.ref w], m + 1, by rw [State.heap_setObj_of_lt hlt, if_pos rfl],
    forall2_snoc (forall2_jstr_mono (strMono_trans hm hm1) h2) ⟨w, rfl, hm1 w line hw⟩⟩

/-- A lookup through an update of another object, in a heap grown from `σ0`. -/
theorem heap_setObj_grows {σ0 σ1 : State} {l y : Addr} {o : Obj} (hg : Grows σ0 σ1) (hne : y ≠ l)
    (hy : y < σ0.next) : (σ1.setObj l o).heap y = σ0.heap y := by
  rw [State.heap_setObj, if_neg hne, hg.2 y hy]

theorem ne_of_heap {σ : State} {x y : Addr} {o o' : Obj} (hx : σ.heap x = some o) (hy : σ.heap y = some o')
    (h : o ≠ o') : x ≠ y := by
  intro e
  rw [e, hy] at hx
  exact h (Option.some.inj hx).symm

/-! ## The `Result` object after an append -/

/-- `stmt`: a string appended to the statement list. -/
theorem resAtL_push_st {σ0 σ1 : State} {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool}
    {xs : List Value} {ms : Nat} {w : Addr} {line : JStr}
    (hR : ResAtL σ0 res ld ls lh disp st ht ab) (hls : σ0.heap ls = some (.list .arrayList xs ms))
    (hg : Grows σ0 σ1) (hw : σ1.heap w = some (.str line)) :
    ResAtL (σ1.setObj ls (.list .arrayList (xs ++ [.ref w]) (ms + 1))) res ld ls lh disp (st ++ [line]) ht ab := by
  obtain ⟨fs, hres, gd, gs, gh, gab, n1, n2, n3, Ld, Ls, Lh⟩ := hR
  have hlt := State.lt_next_of_heap hls
  have hm : StrMono σ0 (σ1.setObj ls (.list .arrayList (xs ++ [.ref w]) (ms + 1))) :=
    strMono_trans (strMono_of_grows hg)
      (strMono_setObj (by rw [hg.2 ls hlt]; exact not_str_of_list hls))
  have hrl : res ≠ ls := ne_of_heap hres hls (by intro h; cases h)
  refine ⟨fs, by rw [heap_setObj_grows hg hrl (State.lt_next_of_heap hres), hres], gd, gs, gh, gab, n1, n2, n3,
    listAt_mono Ld (heap_setObj_grows hg n1 (listAt_lt Ld)) hm,
    listAt_push Ls hls (strMono_of_grows hg) (hg.2 ls hlt) (Nat.lt_of_lt_of_le hlt hg.1) hw,
    listAt_mono Lh (heap_setObj_grows hg (Ne.symm n3) (listAt_lt Lh)) hm⟩

/-- `html`: a string appended to the HTML list. -/
theorem resAtL_push_ht {σ0 σ1 : State} {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool}
    {xs : List Value} {ms : Nat} {w : Addr} {line : JStr}
    (hR : ResAtL σ0 res ld ls lh disp st ht ab) (hlh : σ0.heap lh = some (.list .arrayList xs ms))
    (hg : Grows σ0 σ1) (hw : σ1.heap w = some (.str line)) :
    ResAtL (σ1.setObj lh (.list .arrayList (xs ++ [.ref w]) (ms + 1))) res ld ls lh disp st (ht ++ [line]) ab := by
  obtain ⟨fs, hres, gd, gs, gh, gab, n1, n2, n3, Ld, Ls, Lh⟩ := hR
  have hlt := State.lt_next_of_heap hlh
  have hm : StrMono σ0 (σ1.setObj lh (.list .arrayList (xs ++ [.ref w]) (ms + 1))) :=
    strMono_trans (strMono_of_grows hg)
      (strMono_setObj (by rw [hg.2 lh hlt]; exact not_str_of_list hlh))
  have hrl : res ≠ lh := ne_of_heap hres hlh (by intro h; cases h)
  refine ⟨fs, by rw [heap_setObj_grows hg hrl (State.lt_next_of_heap hres), hres], gd, gs, gh, gab, n1, n2, n3,
    listAt_mono Ld (heap_setObj_grows hg n2 (listAt_lt Ld)) hm,
    listAt_mono Ls (heap_setObj_grows hg n3 (listAt_lt Ls)) hm,
    listAt_push Lh hlh (strMono_of_grows hg) (hg.2 lh hlt) (Nat.lt_of_lt_of_le hlt hg.1) hw⟩

/-! ## Frames -/

/-- The addresses of the `Result` object and its lists. -/
def InRes (res ld ls lh : Addr) (y : Addr) : Prop := y = res ∨ y = ld ∨ y = ls ∨ y = lh

theorem keepsRes_of_keeps {res ld ls lh : Addr} {σ σ' : State} (h : Keeps (InRes res ld ls lh) σ σ') :
    KeepsRes res ld ls lh σ σ' :=
  ⟨h.1, fun y hy h1 h2 h3 h4 => h.2 y hy (by
    rintro (e | e | e | e)
    · exact h1 e
    · exact h2 e
    · exact h3 e
    · exact h4 e)⟩

theorem keeps_of_keepsRes {res ld ls lh : Addr} {σ σ' : State} (h : KeepsRes res ld ls lh σ σ') :
    Keeps (InRes res ld ls lh) σ σ' :=
  ⟨h.1, fun y hy hA => h.2 y hy (fun e => hA (Or.inl e)) (fun e => hA (Or.inr (Or.inl e)))
    (fun e => hA (Or.inr (Or.inr (Or.inl e)))) (fun e => hA (Or.inr (Or.inr (Or.inr e))))⟩

theorem keepsRes_trans {res ld ls lh : Addr} {σ1 σ2 σ3 : State} (h1 : KeepsRes res ld ls lh σ1 σ2)
    (h2 : KeepsRes res ld ls lh σ2 σ3) : KeepsRes res ld ls lh σ1 σ3 :=
  keepsRes_of_keeps (keeps_trans (keeps_of_keepsRes h1) (keeps_of_keepsRes h2))

theorem inRes_res {res ld ls lh : Addr} : InRes res ld ls lh res := Or.inl rfl
theorem inRes_ld {res ld ls lh : Addr} : InRes res ld ls lh ld := Or.inr (Or.inl rfl)
theorem inRes_ls {res ld ls lh : Addr} : InRes res ld ls lh ls := Or.inr (Or.inr (Or.inl rfl))
theorem inRes_lh {res ld ls lh : Addr} : InRes res ld ls lh lh := Or.inr (Or.inr (Or.inr rfl))

/-- `Keeps (InRes …)` of a state built from the entry state by updates of the `Result` and its lists,
allocations and callees (`GrowsK`). -/
macro "txt_keepsR" : tactic => `(tactic| repeat (first | (refine keeps_setObj' ?_ (by first | exact inRes_res | exact inRes_ld | exact inRes_ls | exact inRes_lh)) | (refine keeps_alloc' ?_) | (refine keeps_grows' ?_ (growsK_elim (by assumption))) | exact keeps_refl _ _))

end EquivLean.Modernize.Cbstm03a.Java.Txt

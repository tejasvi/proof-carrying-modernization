import EquivLean.Modernize.Cbstm03a.Java.RunInv
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java `run`, the text loops: shared lemmas of the segments `CbARun1.*`

Heap frames (`StrMono`, `Keeps (· = t)`), the `TextsAt` arrays under a store of the next text, the `Result`
object while its lists are empty, the input records (`TrnxAt` …) in a heap that only grows, and `int` index
arithmetic.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  grows_refl grows_trans keeps_trans keeps_of_grows keeps_setObj keeps_refl forall2_imp heap_grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg1

/-! ## `int` arithmetic -/

theorem i32_toInt_add_one {i n : I32} (h : i.toInt < n.toInt) : (i + 1).toInt = i.toInt + 1 := by
  have h1 := bv32_toInt_lt n
  have h2 := bv32_le_toInt i
  have h3 : (1 : I32).toInt = 1 := by decide
  rw [BitVec.toInt_add, h3]
  exact bmod32_of_bounds (by omega) (by omega)

theorem i32_zero_toInt : (0 : I32).toInt = 0 := by decide

/-! ## Lists -/

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → xs.length = ys.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [forall2_length h]

theorem forall2_append {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} {xs' : List α} {ys' : List β}, Forall2 R xs ys → Forall2 R xs' ys' →
      Forall2 R (xs ++ xs') (ys ++ ys')
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (forall2_append h2 h)

theorem forall2_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (_ : Forall2 R xs ys) (k : Nat) (hx : k < xs.length) (hy : k < ys.length),
      R (xs[k]'hx) (ys[k]'hy)
  | _ :: _, _ :: _, .cons h _, 0, _, _ => h
  | _ :: _, _ :: _, .cons _ h, k + 1, hx, hy =>
    forall2_getElem h k (Nat.lt_of_succ_lt_succ hx) (Nat.lt_of_succ_lt_succ hy)

theorem set_append_replicate {α : Type} (xs : List α) (v d : α) (m : Nat) :
    (xs ++ List.replicate (m + 1) d).set xs.length v = (xs ++ [v]) ++ List.replicate m d := by
  induction xs with
  | nil => simp [List.replicate_succ]
  | cons x xs ih => simp [ih]

theorem take_succ_getElem {α : Type} (T : List α) (k : Nat) (hk : k < T.length) :
    T.take (k + 1) = T.take k ++ [T[k]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  rfl

/-! ## Heaps -/

theorem strMono_refl (σ : State) : StrMono σ σ := fun _ _ h => h

theorem strMono_trans {σ1 σ2 σ3 : State} (h1 : StrMono σ1 σ2) (h2 : StrMono σ2 σ3) : StrMono σ1 σ3 :=
  fun x s h => h2 x s (h1 x s h)

theorem strMono_of_grows {σ σ' : State} (h : Grows σ σ') : StrMono σ σ' := fun x s hx => by
  rw [h.2 x (State.lt_next_of_heap hx), hx]

theorem strMono_of_keeps {σ σ' : State} {t : Addr} {et : JType} {vs : List Value} (h : Keeps (· = t) σ σ')
    (ht : σ.heap t = some (.array et vs)) : StrMono σ σ' := fun x s hx => by
  have hne : ¬ x = t := fun e => by rw [e, ht] at hx; cases hx
  rw [h.2 x (State.lt_next_of_heap hx) hne, hx]

theorem keeps_setObj_grows {σ σ1 : State} {t : Addr} (hg : Grows σ σ1) (o : Obj) :
    Keeps (· = t) σ (σ1.setObj t o) :=
  keeps_trans (keeps_of_grows hg) (keeps_setObj o rfl)

theorem heap_keeps_ne {σ σ' : State} {t x : Addr} {o : Obj} (h : Keeps (· = t) σ σ') (hx : σ.heap x = some o)
    (hne : x ≠ t) : σ'.heap x = some o := by
  rw [h.2 x (State.lt_next_of_heap hx) hne, hx]

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

/-- A text array kept by a path that writes only the array at `t`. -/
theorem textsAt_keeps {σ σ' : State} {a t : Addr} {et : JType} {vs : List Value} {ts : List JStr} {n : Nat}
    (h : TextsAt σ a ts n) (hk : Keeps (· = t) σ σ') (ht : σ.heap t = some (.array et vs)) (hne : a ≠ t) :
    TextsAt σ' a ts n := by
  obtain ⟨xs, hx, hf⟩ := h
  exact ⟨xs, heap_keeps_ne hk hx hne, forall2_jstr_mono hf (strMono_of_keeps hk ht)⟩

/-- The text array after the store of text `k` at index `k`. -/
theorem textsAt_store {σ σ' : State} {t y : Addr} {xs : List Value} {T : List JStr} {k c : Nat} {s : JStr}
    (hxs : Forall2 (JStrAt σ) xs (T.take k)) (hk : k < T.length) (hc : 0 < c) (hm : StrMono σ σ')
    (ht : σ'.heap t = some (.array (.cls "java.lang.String") ((xs ++ List.replicate c Value.null).set k (.ref y))))
    (hy : σ'.heap y = some (.str s)) (hs : s = T[k]) :
    TextsAt σ' t (T.take (k + 1)) (c - 1) := by
  have hl : xs.length = k := by
    rw [forall2_length hxs, List.length_take]; omega
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  rw [← hl, set_append_replicate] at ht
  refine ⟨xs ++ [.ref y], ?_, ?_⟩
  · rw [ht]; simp
  · rw [take_succ_getElem T k hk, ← hs]
    exact forall2_append (forall2_jstr_mono hxs hm) (.cons ⟨y, rfl, hy⟩ .nil)

/-- The same, in the form `jvc` leaves the stored array (`xs ++ (replicate c null).set 0 v`). -/
theorem textsAt_store0 {σ σ' : State} {t y : Addr} {xs : List Value} {T : List JStr} {k c : Nat} {s : JStr}
    (hxs : Forall2 (JStrAt σ) xs (T.take k)) (hk : k < T.length) (hc : 0 < c) (hm : StrMono σ σ')
    (ht : σ'.heap t = some (.array (.cls "java.lang.String") (xs ++ (List.replicate c Value.null).set 0 (.ref y))))
    (hy : σ'.heap y = some (.str s)) (hs : s = T[k]) :
    TextsAt σ' t (T.take (k + 1)) (c - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  refine ⟨xs ++ [.ref y], ?_, ?_⟩
  · rw [ht]; simp [List.replicate_succ]
  · rw [take_succ_getElem T k hk, ← hs]
    exact forall2_append (forall2_jstr_mono hxs hm) (.cons ⟨y, rfl, hy⟩ .nil)

/-- Reading back the element just stored (for `jvc`). -/
theorem getElem?_append_set0 {xs : List Value} {k c : Nat} {v : Value} (h : xs.length = k) (hc : 0 < c) :
    (xs ++ (List.replicate c Value.null).set 0 v)[k]? = some v := by
  subst h
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  simp only [List.replicate_succ, List.set_cons_zero]
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem getElem_append_set0 {xs : List Value} {k c : Nat} {v : Value} (h : xs.length = k) (hc : 0 < c)
    (hk : k < (xs ++ (List.replicate c Value.null).set 0 v).length) :
    (xs ++ (List.replicate c Value.null).set 0 v)[k]'hk = v := by
  have := getElem?_append_set0 (v := v) h hc
  rw [List.getElem?_eq_getElem hk] at this
  exact Option.some.inj this

/-- A new array of `n` `null`s: the texts `[]`, then `n` nulls. -/
theorem textsAt_new {σ : State} {t : Addr} {n : Nat}
    (ht : σ.heap t = some (.array (.cls "java.lang.String") (List.replicate n .null))) : TextsAt σ t [] n :=
  ⟨[], by rw [ht]; simp, .nil⟩

/-! ## The `Result` object while its lists are empty -/

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

theorem heap_eq_of_keeps {σ σ' : State} {t x : Addr} {o : Obj} (h : Keeps (· = t) σ σ') (hx : σ.heap x = some o)
    (hne : x ≠ t) : σ'.heap x = σ.heap x := by
  rw [h.2 x (State.lt_next_of_heap hx) hne]

/-- `RunBase` (lists empty) kept by a path that writes only the array at `t`, allocated after the entry. -/
theorem runBase_keeps {g : RunG} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh t : Addr} {et : JType}
    {vs : List Value} (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (hk : Keeps (· = t) σ σ')
    (ht : σ.heap t = some (.array et vs)) (ht0 : σ0.next ≤ t) (hi : σ'.inits = σ.inits)
    (hs : σ'.statics = σ.statics) (f10 : fr'.get 10 = fr.get 10) (f23 : fr'.get 23 = fr.get 23)
    (f9 : fr'.get 9 = fr.get 9) (f6 : fr'.get 6 = fr.get 6) (f7 : fr'.get 7 = fr.get 7) :
    RunBase g σ0 fr' σ' res ld ls lh JOut.init := by
  obtain ⟨g10, g23, g9, g6, g7, hR, r0, l0, s0, h0, hg, hi0, hs0⟩ := hb
  have hR' := hR
  obtain ⟨fs, hr, -, -, -, -, -, -, -, ⟨xd, md, hd, -⟩, ⟨xs', ms, hls, -⟩, ⟨xh, mh, hlh, -⟩⟩ := hR'
  have ne1 : res ≠ t := fun e => by rw [e, ht] at hr; cases hr
  have ne2 : ld ≠ t := fun e => by rw [e, ht] at hd; cases hd
  have ne3 : ls ≠ t := fun e => by rw [e, ht] at hls; cases hls
  have ne4 : lh ≠ t := fun e => by rw [e, ht] at hlh; cases hlh
  refine ⟨f10.trans g10, f23.trans g23, f9.trans g9, f6.trans g6, f7.trans g7,
    resAtL_init_of_heap hR (heap_eq_of_keeps hk hr ne1) (heap_eq_of_keeps hk hd ne2)
      (heap_eq_of_keeps hk hls ne3) (heap_eq_of_keeps hk hlh ne4), r0, l0, s0, h0,
    ⟨Nat.le_trans hg.1 hk.1, fun x hx => ?_⟩, hi.trans hi0, hs.trans hs0⟩
  have hxt : ¬ x = t := fun e => Nat.lt_irrefl t (Nat.lt_of_lt_of_le (e ▸ hx) ht0)
  rw [hk.2 x (Nat.lt_of_lt_of_le hx hg.1) hxt, hg.2 x hx]

/-- `RunBase` (lists empty) kept by an allocation. -/
theorem runBase_alloc {g : RunG} {σ0 σ : State} {fr fr' : Frame} {res ld ls lh : Addr}
    (hb : RunBase g σ0 fr σ res ld ls lh JOut.init) (o : Obj)
    (f10 : fr'.get 10 = fr.get 10) (f23 : fr'.get 23 = fr.get 23)
    (f9 : fr'.get 9 = fr.get 9) (f6 : fr'.get 6 = fr.get 6) (f7 : fr'.get 7 = fr.get 7) :
    RunBase g σ0 fr' (σ.alloc o).2 res ld ls lh JOut.init := by
  obtain ⟨g10, g23, g9, g6, g7, hR, r0, l0, s0, h0, hg, hi0, hs0⟩ := hb
  have hR' := hR
  obtain ⟨fs, hr, -, -, -, -, -, -, -, ⟨xd, md, hd, -⟩, ⟨xs', ms, hls, -⟩, ⟨xh, mh, hlh, -⟩⟩ := hR'
  exact ⟨f10.trans g10, f23.trans g23, f9.trans g9, f6.trans g6, f7.trans g7,
    resAtL_init_of_heap hR (State.heap_alloc_of_lt (State.lt_next_of_heap hr) o)
      (State.heap_alloc_of_lt (State.lt_next_of_heap hd) o) (State.heap_alloc_of_lt (State.lt_next_of_heap hls) o)
      (State.heap_alloc_of_lt (State.lt_next_of_heap hlh) o), r0, l0, s0, h0,
    ⟨by rw [State.next_alloc]; exact Nat.le_succ_of_le hg.1, fun x hx => by
      rw [State.heap_alloc_of_lt (Nat.lt_of_lt_of_le hx hg.1), hg.2 x hx]⟩, hi0, hs0⟩

/-- A full text array (the loop's exit) kept by an allocation. -/
theorem textsAt_alloc {σ : State} {a : Addr} {ts : List JStr} {n : Nat} (h : TextsAt σ a ts n) (o : Obj) :
    TextsAt (σ.alloc o).2 a ts n := by
  obtain ⟨xs, hx, hf⟩ := h
  refine ⟨xs, by rw [State.heap_alloc_of_lt (State.lt_next_of_heap hx)]; exact hx, forall2_jstr_mono hf ?_⟩
  intro y s hy
  rw [State.heap_alloc_of_lt (State.lt_next_of_heap hy)]; exact hy

/-- The loop's exit: all `len` texts stored. -/
theorem textsAt_full {σ : State} {a : Addr} {T : List JStr} {xs : List Value} {k len : Nat}
    (hxs : Forall2 (JStrAt σ) xs (T.take k)) (hT : T.length = len) (hk : k = len)
    (ha : σ.heap a = some (.array (.cls "java.lang.String") (xs ++ List.replicate (len - k) Value.null))) :
    TextsAt σ a T 0 := by
  subst hk
  refine ⟨xs, by rw [ha, Nat.sub_self], ?_⟩
  rw [← List.take_of_length_le (Nat.le_of_eq hT)]
  exact hxs

/-! ## The input records in a heap that only grows -/

theorem sfld_mono {σ σ' : State} {c : ClassName} {fs : List (FieldKey × Value)} {f : String} {s : JStr}
    (h : SFld σ c fs f s) (hm : StrMono σ σ') : SFld σ' c fs f s := by
  obtain ⟨x, h1, h2, h3⟩ := h
  exact ⟨x, h1, hm x s h2, h3⟩

theorem trnxAt_grows {σ σ' : State} {x : Addr} {t : TrnxR} (h : TrnxAt σ x t) (hg : Grows σ σ') :
    TrnxAt σ' x t := by
  have hm := strMono_of_grows hg
  obtain ⟨fs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨fs, heap_grows hg h0, sfld_mono h1 hm, sfld_mono h2 hm, sfld_mono h3 hm, h4, sfld_mono h5 hm,
    sfld_mono h6 hm, h7, h8, sfld_mono h9 hm, sfld_mono h10 hm, sfld_mono h11 hm, sfld_mono h12 hm,
    sfld_mono h13 hm, sfld_mono h14 hm⟩

theorem xrefAt_grows {σ σ' : State} {x : Addr} {t : XrefR} (h : XrefAt σ x t) (hg : Grows σ σ') :
    XrefAt σ' x t := by
  have hm := strMono_of_grows hg
  obtain ⟨fs, h0, h1, h2, h3, h4⟩ := h
  exact ⟨fs, heap_grows hg h0, sfld_mono h1 hm, h2, h3, sfld_mono h4 hm⟩

theorem custAt_grows {σ σ' : State} {x : Addr} {t : CustR} (h : CustAt σ x t) (hg : Grows σ σ') :
    CustAt σ' x t := by
  have hm := strMono_of_grows hg
  obtain ⟨fs, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨fs, heap_grows hg h0, h1, sfld_mono h2 hm, sfld_mono h3 hm, sfld_mono h4 hm, sfld_mono h5 hm,
    sfld_mono h6 hm, sfld_mono h7 hm, sfld_mono h8 hm, sfld_mono h9 hm, sfld_mono h10 hm, sfld_mono h11 hm,
    sfld_mono h12 hm, h13, sfld_mono h14 hm, sfld_mono h15 hm, sfld_mono h16 hm, sfld_mono h17 hm, h18,
    sfld_mono h19 hm⟩

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

/-! ## The entry: the new `Result`, heaps that grow -/

/-- The fields of a new `Result` object (`new` sets the defaults). -/
abbrev resF0 : List (FieldKey × Value) :=
  [((resC, "displays"), .null), ((resC, "stmtFileWrites"), .null), ((resC, "htmlFileWrites"), .null),
   ((resC, "abended"), .int 0)]

/-- The `Result` object after its constructor: three new empty lists. -/
theorem resAtL_ctor {σ : State} {res ld ls lh : Addr}
    (hr : σ.heap res = some (.plain resC (Fields.set (Fields.set (Fields.set resF0 (resC, "displays") (.ref ld))
      (resC, "stmtFileWrites") (.ref ls)) (resC, "htmlFileWrites") (.ref lh))))
    (hd : σ.heap ld = some (.list .arrayList [] 0)) (hs : σ.heap ls = some (.list .arrayList [] 0))
    (hh : σ.heap lh = some (.list .arrayList [] 0)) (n1 : ld ≠ ls) (n2 : ld ≠ lh) (n3 : ls ≠ lh) :
    ResAtL σ res ld ls lh [] [] [] false :=
  ⟨_, hr, by simp [Fields.get, Fields.set, List.lookup], by simp [Fields.get, Fields.set, List.lookup],
    by simp [Fields.get, Fields.set, List.lookup], by simp [Fields.get, Fields.set, List.lookup], n1, n2, n3,
    ⟨[], 0, hd, .nil⟩, ⟨[], 0, hs, .nil⟩, ⟨[], 0, hh, .nil⟩⟩

theorem grows_alloc_r {σ0 σ : State} (h : Grows σ0 σ) (o : Obj) : Grows σ0 (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ_of_le h.1, fun x hx => by
    rw [State.heap_alloc_of_lt (Nat.lt_of_lt_of_le hx h.1), h.2 x hx]⟩

theorem grows_setObj_r {σ0 σ : State} {a : Addr} (h : Grows σ0 σ) (ha : σ0.next ≤ a) (o : Obj) :
    Grows σ0 (σ.setObj a o) :=
  ⟨by rw [State.next_setObj]; exact h.1, fun x hx => by
    have hne : x ≠ a := fun e => Nat.lt_irrefl a (Nat.lt_of_lt_of_le (e ▸ hx) ha)
    rw [State.heap_setObj, if_neg hne, h.2 x hx]⟩

/-! ## Hiding facts from `jvc` -/

/-- A fact kept out of `jvc`'s reach (it rewrites with every hypothesis it can read). -/
@[irreducible] def Hid (p : Prop) : Prop := p

theorem hid_intro {p : Prop} (h : p) : Hid p := by unfold Hid; exact h
theorem hid_elim {p : Prop} (h : Hid p) : p := by unfold Hid at h; exact h

end EquivLean.Modernize.Cbstm03a.Java.Seg1

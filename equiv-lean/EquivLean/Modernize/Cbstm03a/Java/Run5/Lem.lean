import EquivLean.Modernize.Cbstm03a.Java.RunPure
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java, `run`'s segment 153 (the account search): shared facts

Lists of strings element by element, the lengths of the record texts, the customer text found, and the frame of
the paths: the `Result` object and its lists are neither strings nor arrays, so a callee that keeps every other
object (`KeepsRes`) keeps the strings and arrays the invariants talk about (`SAMono`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim fixStr_length zpadStr_length heap_grows grows_refl grows_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg5

/-! ## Lists of strings -/

theorem forall2_len {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 → l1.length = l2.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [forall2_len h]

theorem forall2_jstr_get {σ : State} :
    ∀ {xs : List Value} {ts : List JStr}, Forall2 (JStrAt σ) xs ts →
      ∀ k, k < ts.length → ∃ y, xs[k]? = some (.ref y) ∧ σ.heap y = some (.str (ts.getD k []))
  | [], [], .nil, k, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ :: _, .cons hx _, 0, _ => by
    obtain ⟨y, rfl, hy⟩ := hx
    exact ⟨y, rfl, hy⟩
  | _ :: _, _ :: _, .cons _ hr, k + 1, h => by
    obtain ⟨y, h1, h2⟩ := forall2_jstr_get hr k (by simp at h; omega)
    exact ⟨y, by simpa using h1, by simpa using h2⟩

theorem forall2_jstr_mono {σ σ' : State} (hm : StrMono σ σ') :
    ∀ {xs : List Value} {ts : List JStr}, Forall2 (JStrAt σ) xs ts → Forall2 (JStrAt σ') xs ts
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hx hr => by
    obtain ⟨y, rfl, hy⟩ := hx
    exact .cons ⟨y, rfl, hm y _ hy⟩ (forall2_jstr_mono hm hr)

theorem textsAt_get {σ : State} {a : Addr} {ts : List JStr} (h : TextsAt σ a ts 0) :
    ∃ xs, σ.heap a = some (.array (.cls "java.lang.String") xs) ∧ xs.length = ts.length ∧
      Forall2 (JStrAt σ) xs ts := by
  obtain ⟨xs, h1, h2⟩ := h
  refine ⟨xs, ?_, forall2_len h2, h2⟩
  simpa using h1

/-! ## The record texts -/

theorem zuI_length (v : Int) (n : Nat) : (zuI v n).length = n := zpadStr_length _ _

theorem zsI_length (v : Int) {n : Nat} (h : 1 ≤ n) : (zsI v n).length = n := by
  simp only [zsI, List.length_append, zpadStr_length, List.length_singleton]; omega

theorem custTextR_length (t : CustR) : (custTextR t).length = 500 := by
  simp only [custTextR, List.length_append, fixStr_length, zuI_length]

theorem acctTextR_length (t : AcctR) : (acctTextR t).length = 300 := by
  simp only [acctTextR, List.length_append, fixStr_length, zuI_length, zsI_length _ (by decide : 1 ≤ 12)]

theorem getD_map_len {α : Type} {f : α → JStr} {l : List α} {n k : Nat} (hf : ∀ a, (f a).length = n)
    (hk : k < l.length) : ((l.map f).getD k []).length = n := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  exact hf _

theorem T4_len (g : RunG) {k : Nat} (hk : k < g.T4.length) : (g.T4.getD k []).length = 300 := by
  have : k < g.ars.length := by simpa [RunG.T4] using hk
  exact getD_map_len acctTextR_length this

theorem mem_of_custFind {keys texts : List JStr} {k c : JStr} (h : custFind keys texts k = some c) :
    c ∈ texts := by
  unfold custFind at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (List.of_mem_zip (List.mem_of_find?_eq_some hp)).2

theorem crec_len {g : RunG} {k c : JStr} (h : custFind g.K3 g.T3 k = some c) : c.length = 500 := by
  have hm := mem_of_custFind h
  simp only [RunG.T3, List.mem_map] at hm
  obtain ⟨t, -, rfl⟩ := hm
  exact custTextR_length t

theorem drop_getD_cons {α : Type} {l : List α} {j : Nat} (d : α) (h : j < l.length) :
    l.drop j = l.getD j d :: l.drop (j + 1) := by
  rw [List.getD_eq_getElem _ _ h]; exact List.drop_eq_getElem_cons h

/-! ## Frames -/

/-- A string or an array. -/
def StrArr (o : Obj) : Prop := (∃ s, o = .str s) ∨ (∃ et vs, o = .array et vs)

/-- The strings and arrays of `σ` are unchanged in `σ'`. -/
def SAMono (σ σ' : State) : Prop := ∀ x o, σ.heap x = some o → StrArr o → σ'.heap x = some o

theorem saMono_of_grows {σ σ' : State} (hg : Grows σ σ') : SAMono σ σ' :=
  fun _ _ hx _ => heap_grows hg hx

theorem saMono_trans {σ1 σ2 σ3 : State} (h1 : SAMono σ1 σ2) (h2 : SAMono σ2 σ3) : SAMono σ1 σ3 :=
  fun x o hx ho => h2 x o (h1 x o hx ho) ho

theorem ne_of_plain {σ : State} {x a : Addr} {o : Obj} {c : ClassName} {fs : List (FieldKey × Value)}
    (hx : σ.heap x = some o) (ho : StrArr o) (ha : σ.heap a = some (.plain c fs)) : x ≠ a := by
  rintro rfl
  rw [ha] at hx
  rcases ho with ⟨s, rfl⟩ | ⟨et, vs, rfl⟩ <;> cases hx

theorem ne_of_list {σ : State} {x a : Addr} {o : Obj} {k : ListKind} {xs : List Value} {m : Nat}
    (hx : σ.heap x = some o) (ho : StrArr o) (ha : σ.heap a = some (.list k xs m)) : x ≠ a := by
  rintro rfl
  rw [ha] at hx
  rcases ho with ⟨s, rfl⟩ | ⟨et, vs, rfl⟩ <;> cases hx

theorem saMono_of_keepsRes {σ σ' : State} {res ld ls lh : Addr} {d st ht : List JStr} {ab : Bool}
    (hR : ResAtL σ res ld ls lh d st ht ab) (hk : KeepsRes res ld ls lh σ σ') : SAMono σ σ' := by
  intro x o hx ho
  obtain ⟨fs, hr, -, -, -, -, -, -, -, ⟨xd, md, hd, -⟩, ⟨xs, ms, hs, -⟩, ⟨xh, mh, hh, -⟩⟩ := hR
  rw [hk.2 x (State.lt_next_of_heap hx) (ne_of_plain hx ho hr) (ne_of_list hx ho hd) (ne_of_list hx ho hs)
    (ne_of_list hx ho hh), hx]

theorem strMono_of_sa {σ σ' : State} (h : SAMono σ σ') : StrMono σ σ' :=
  fun x s hx => h x _ hx (Or.inl ⟨s, rfl⟩)

theorem heap_str_sa {σ σ' : State} (h : SAMono σ σ') {x : Addr} {s : JStr} (hx : σ.heap x = some (.str s)) :
    σ'.heap x = some (.str s) := h x _ hx (Or.inl ⟨s, rfl⟩)

theorem heap_arr_sa {σ σ' : State} (h : SAMono σ σ') {x : Addr} {et : JType} {vs : List Value}
    (hx : σ.heap x = some (.array et vs)) : σ'.heap x = some (.array et vs) := h x _ hx (Or.inr ⟨et, vs, rfl⟩)

theorem textsAt_sa {σ σ' : State} {a : Addr} {ts : List JStr} {n : Nat} (h : TextsAt σ a ts n)
    (hs : SAMono σ σ') : TextsAt σ' a ts n := by
  obtain ⟨xs, hx, hf⟩ := h
  exact ⟨xs, heap_arr_sa hs hx, forall2_jstr_mono (strMono_of_sa hs) hf⟩

theorem slotsAt_sa {σ σ' : State} {a : Addr} {m : Nat → JChar} (h : SlotsAt σ a m) (hs : SAMono σ σ') :
    SlotsAt σ' a m := by
  obtain ⟨vs, hv, hl, hall⟩ := h
  refine ⟨vs, heap_arr_sa hs hv, hl, fun i hi => ?_⟩
  rcases hall i hi with h1 | ⟨x, t, h1, h2, h3, h4⟩
  · exact Or.inl h1
  · exact Or.inr ⟨x, t, h1, heap_str_sa hs h2, h3, h4⟩

theorem strLoc_sa {σ σ' : State} {fr fr' : Frame} {i : Nat} {s : JStr} (h : StrLoc σ fr i s) (hs : SAMono σ σ')
    (hf : fr'.get i = fr.get i) : StrLoc σ' fr' i s := by
  obtain ⟨x, h1, h2⟩ := h
  exact ⟨x, hf.trans h1, heap_str_sa hs h2⟩

theorem xrecLocs_sa {σ σ' : State} {fr fr' : Frame} {x : JStr} (h : XrecLocs σ fr x) (hs : SAMono σ σ')
    (h32 : fr'.get 32 = fr.get 32) (h34 : fr'.get 34 = fr.get 34) (h33 : fr'.get 33 = fr.get 33) :
    XrecLocs σ' fr' x :=
  ⟨strLoc_sa h.1 hs h32, strLoc_sa h.2.1 hs h34, strLoc_sa h.2.2 hs h33⟩

theorem keepsRes_of_grows {σ σ' : State} {res ld ls lh : Addr} (hg : Grows σ σ') : KeepsRes res ld ls lh σ σ' :=
  ⟨hg.1, fun y hy _ _ _ _ => hg.2 y hy⟩

theorem keepsRes_trans {σ1 σ2 σ3 : State} {res ld ls lh : Addr} (h1 : KeepsRes res ld ls lh σ1 σ2)
    (h2 : KeepsRes res ld ls lh σ2 σ3) : KeepsRes res ld ls lh σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun y hy a b c d => by
    rw [h2.2 y (Nat.lt_of_lt_of_le hy h1.1) a b c d, h1.2 y hy a b c d]⟩

theorem grows_keepsRes {σ0 σ σ' : State} {res ld ls lh : Addr} (hg : Grows σ0 σ) (hk : KeepsRes res ld ls lh σ σ')
    (h1 : σ0.next ≤ res) (h2 : σ0.next ≤ ld) (h3 : σ0.next ≤ ls) (h4 : σ0.next ≤ lh) : Grows σ0 σ' := by
  refine ⟨Nat.le_trans hg.1 hk.1, fun y hy => ?_⟩
  have n1 : y ≠ res := fun e => Nat.lt_irrefl res (Nat.lt_of_lt_of_le (e ▸ hy) h1)
  have n2 : y ≠ ld := fun e => Nat.lt_irrefl ld (Nat.lt_of_lt_of_le (e ▸ hy) h2)
  have n3 : y ≠ ls := fun e => Nat.lt_irrefl ls (Nat.lt_of_lt_of_le (e ▸ hy) h3)
  have n4 : y ≠ lh := fun e => Nat.lt_irrefl lh (Nat.lt_of_lt_of_le (e ▸ hy) h4)
  rw [hk.2 y (Nat.lt_of_lt_of_le hy hg.1) n1 n2 n3 n4, hg.2 y hy]

theorem listAt_grows {σ σ' : State} {l : Addr} {ss : List JStr} (h : ListAt σ l ss) (hg : Grows σ σ') :
    ListAt σ' l ss := by
  obtain ⟨xs, m, hl, hf⟩ := h
  exact ⟨xs, m, heap_grows hg hl, forall2_jstr_mono (strMono_of_sa (saMono_of_grows hg)) hf⟩

theorem resAtL_grows {σ σ' : State} {res ld ls lh : Addr} {d st ht : List JStr} {ab : Bool}
    (h : ResAtL σ res ld ls lh d st ht ab) (hg : Grows σ σ') : ResAtL σ' res ld ls lh d st ht ab := by
  obtain ⟨fs, hr, g1, g2, g3, g4, n1, n2, n3, l1, l2, l3⟩ := h
  exact ⟨fs, heap_grows hg hr, g1, g2, g3, g4, n1, n2, n3, listAt_grows l1 hg, listAt_grows l2 hg,
    listAt_grows l3 hg⟩

theorem grows_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun x hx => State.heap_alloc_of_lt hx o⟩

/-- The path wrote none of `run`'s locals but `$z5`, `crJmp`, `i#79`, `i#78`, `$r16`, `i#77`. -/
def FrOk (fr fr' : Frame) : Prop :=
  ∀ k, k ≠ 4 → k ≠ 17 → k ≠ 21 → k ≠ 26 → k ≠ 35 → k ≠ 38 → fr'.get k = fr.get k

theorem FrOk.get {fr fr' : Frame} (h : FrOk fr fr') (k : Nat) (h4 : k ≠ 4 := by decide)
    (h17 : k ≠ 17 := by decide) (h21 : k ≠ 21 := by decide) (h26 : k ≠ 26 := by decide)
    (h35 : k ≠ 35 := by decide) (h38 : k ≠ 38 := by decide) : fr'.get k = fr.get k :=
  h k h4 h17 h21 h26 h35 h38

theorem xctx_resAtL {g : RunG} {σ0 σ : State} {fr : Frame} {res ld ls lh : Addr} {o : JOut} {L : LdSt} {j' : Nat}
    (h : XCtx g σ0 fr σ res ld ls lh o L j') : ResAtL σ res ld ls lh o.disp o.stmt o.html o.ab := by
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, _, _, _, _, hR, _⟩, _⟩ := h
  exact hR

theorem xctx_ldBounded {g : RunG} {σ0 σ : State} {fr : Frame} {res ld ls lh : Addr} {o : JOut} {L : LdSt}
    {j' : Nat} (h : XCtx g σ0 fr σ res ld ls lh o L j') : LdBounded L := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLB⟩ := h
  exact hLB

/-- The cross-reference loop's state after a path that writes none of its locals, keeps every object but the
`Result` object and its lists, and leaves the `Result` holding `o'`. -/
theorem xctx_frame {g : RunG} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh : Addr} {o o' : JOut} {L : LdSt}
    {j' : Nat} (h : XCtx g σ0 fr σ res ld ls lh o L j') (hfr : FrOk fr fr')
    (hk : KeepsRes res ld ls lh σ σ') (hR : ResAtL σ' res ld ls lh o'.disp o'.stmt o'.html o'.ab)
    (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics) :
    XCtx g σ0 fr' σ' res ld ls lh o' L j' := by
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, hB, hT, hL, h2, hst2, o1, o2, o3, h5, h3, h18, hLB⟩ := h
  obtain ⟨b10, b23, b9, b6, b7, hR0, r0, l0, s0, h0, hg, hi0, hs0⟩ := hB
  obtain ⟨c11, c12, c13, c14, c15, ⟨n3, c27, e3⟩, ⟨n4, c28, e4⟩, x1, x2, x3k, x3, x4, q1, q2, q3, q4, q5⟩ := hT
  obtain ⟨d16, d24, hS, htr, hl51⟩ := hL
  have hsa := saMono_of_keepsRes hR0 hk
  exact ⟨t1, t2, t3k, t3, t4, mem, trct, st2,
    ⟨(hfr.get 10).trans b10, (hfr.get 23).trans b23, (hfr.get 9).trans b9, (hfr.get 6).trans b6,
      (hfr.get 7).trans b7, hR, r0, l0, s0, h0, grows_keepsRes hg hk r0 l0 s0 h0, hi.trans hi0, hs.trans hs0⟩,
    ⟨(hfr.get 11).trans c11, (hfr.get 12).trans c12, (hfr.get 13).trans c13, (hfr.get 14).trans c14,
      (hfr.get 15).trans c15, ⟨n3, (hfr.get 27).trans c27, e3⟩, ⟨n4, (hfr.get 28).trans c28, e4⟩,
      textsAt_sa x1 hsa, textsAt_sa x2 hsa, textsAt_sa x3k hsa, textsAt_sa x3 hsa, textsAt_sa x4 hsa,
      q1, q2, q3, q4, q5⟩,
    ⟨(hfr.get 16).trans d16, (hfr.get 24).trans d24, slotsAt_sa hS hsa, heap_arr_sa hsa htr, hl51⟩,
    (hfr.get 2).trans h2, heap_arr_sa hsa hst2, o1, o2, o3, (hfr.get 5).trans h5, (hfr.get 3).trans h3,
    (hfr.get 18).trans h18, hLB⟩

theorem resAtL_or {σ σ' : State} {res ld ls lh : Addr} {d st ht : List JStr} {ab : Bool}
    (h : ResAtL σ res ld ls lh d st ht ab) (hg : Grows σ σ') :
    ResAtL σ' res ld ls lh d st ht false ∨ ResAtL σ' res ld ls lh d st ht true := by
  cases ab
  · exact Or.inl (resAtL_grows h hg)
  · exact Or.inr (resAtL_grows h hg)

/-! ## `int` arithmetic -/

theorem i32_toInt_add_one {i n : I32} (h : i.toInt < n.toInt) : (i + 1).toInt = i.toInt + 1 := by
  have h1 := bv32_toInt_lt n
  have h2 := bv32_le_toInt i
  have h3 : (1 : I32).toInt = 1 := by decide
  rw [BitVec.toInt_add, h3]
  exact bmod32_of_bounds (by omega) (by omega)

/-! ## The two literals of `abend`'s call -/

theorem heap_alloc2_fst (σ : State) (a b : Obj) : ((σ.alloc a).2.alloc b).2.heap σ.next = some a := by
  rw [State.heap_alloc_of_lt (by rw [State.next_alloc]; exact Nat.lt_succ_self _), State.heap_alloc, if_pos rfl]

theorem heap_alloc2_snd (σ : State) (a b : Obj) : ((σ.alloc a).2.alloc b).2.heap (σ.next + 1) = some b := by
  rw [State.heap_alloc, if_pos (State.next_alloc σ a).symm]

theorem argText_alloc2_fst (σ : State) (s : JStr) (b : Obj) :
    argText ((σ.alloc (.str s)).2.alloc b).2 (.ref σ.next) = s := by
  simp only [argText, strOf, heap_alloc2_fst, Option.getD_some]

theorem argText_alloc2_snd (σ : State) (a : Obj) (s : JStr) :
    argText ((σ.alloc a).2.alloc (.str s)).2 (.ref (σ.next + 1)) = s := by
  simp only [argText, strOf, heap_alloc2_snd, Option.getD_some]

/-! ## The model's step for record `j` -/

theorem model_abend {g : RunG} {L : LdSt} {o : JOut} {j : Nat} {crec : JStr} (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F)
    (hcf : custFind g.K3 g.T3 (sub (fixStr (g.T2.getD j []) 1000) 16 25) = some crec)
    (haf : acctFind g.T4 (sub (fixStr (g.T2.getD j []) 1000) 25 36) = none) :
    g.F = o.abend (jl "ERROR READING ACCTFILE") (jl "23") := by
  rw [← hmodel, drop_getD_cons [] hj, xrefAll_cons]
  simp only [xrefStep, hcf, haf]

theorem xrefStep_found {keys texts acc : List JStr} {L : LdSt} {o : JOut} {x crec arec : JStr}
    (hc : custFind keys texts (sub (fixStr x 1000) 16 25) = some crec)
    (ha : acctFind acc (sub (fixStr x 1000) 25 36) = some arec) :
    xrefStep keys texts acc L o x =
      .ok (tailOf (cardsFrom L.m L.trct L.cr (sub (fixStr x 1000) 0 16) L.cr.toInt.toNat 1
          (o.add (jCreateStatement crec arec), 0)).1
        (cardsFrom L.m L.trct L.cr (sub (fixStr x 1000) 0 16) L.cr.toInt.toNat 1
          (o.add (jCreateStatement crec arec), 0)).2) := by
  unfold xrefStep
  simp only [hc, ha]

theorem argText_alloc_of {σ : State} {x : Addr} {s : JStr} (h : σ.heap x = some (.str s)) (o : Obj) :
    argText (σ.alloc o).2 (.ref x) = s := by
  simp only [argText, strOf, State.heap_alloc_of_lt (State.lt_next_of_heap h), h, Option.getD_some]

theorem get_setLocal_same (fr : Frame) (x : Nat) (v : Value) : (fr.setLocal x v).get x = some v := by
  rw [Frame.get_setLocal, if_pos rfl]

theorem get_setLocal_of_ne (fr : Frame) {x k : Nat} (v : Value) (h : k ≠ x) :
    (fr.setLocal x v).get k = fr.get k := by
  rw [Frame.get_setLocal, if_neg h]

theorem model_found {g : RunG} {L : LdSt} {o : JOut} {j : Nat} {crec arec : JStr} (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F)
    (hcf : custFind g.K3 g.T3 (sub (fixStr (g.T2.getD j []) 1000) 16 25) = some crec)
    (haf : acctFind g.T4 (sub (fixStr (g.T2.getD j []) 1000) 25 36) = some arec) :
    xrefAll g.K3 g.T3 g.T4 L
      (tailOf (cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) L.cr.toInt.toNat 1
          (o.add (jCreateStatement crec arec), 0)).1
        (cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) L.cr.toInt.toNat 1
          (o.add (jCreateStatement crec arec), 0)).2) (g.T2.drop (j + 1)) = g.F := by
  rw [← hmodel, drop_getD_cons [] hj, xrefAll_cons, xrefStep_found hcf haf]

/-! ## The cut points reached -/

/-- Back at statement 153 with the next text (`i + 1`): the heap only grew (the substring). -/
theorem close153 {g : RunG} {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh : Addr}
    {L : LdSt} {o : JOut} {j : Nat} {i n4 : I32} {crec : JStr}
    (hX : XCtx g σ0 fr σ res ld ls lh o L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F) (hxl : XrecLocs σ fr (g.T2.getD j []))
    (hcr : StrLoc σ fr 37 crec)
    (hcf : custFind g.K3 g.T3 (sub (fixStr (g.T2.getD j []) 1000) 16 25) = some crec)
    (hall : ∀ k, k < i.toInt.toNat → sub (g.T4.getD k []) 0 11 ≠ sub (fixStr (g.T2.getD j []) 1000) 25 36)
    (hm : sub (g.T4.getD i.toInt.toNat []) 0 11 ≠ sub (fixStr (g.T2.getD j []) 1000) 25 36)
    (hi0 : 0 ≤ i.toInt) (hlt : i.toInt < n4.toInt) (hn4 : n4.toInt = g.ars.length)
    (hfr : FrOk fr fr') (h38 : fr'.get 38 = some .null) (h26 : fr'.get 26 = some (.int (i + 1)))
    (hg : Grows σ σ') (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics) :
    inv153 g args σ0 fr' σ' := by
  have hsa := saMono_of_grows hg
  have hi1 := i32_toInt_add_one hlt
  refine ⟨res, ld, ls, lh, L, o, j, i + 1, crec,
    xctx_frame hX hfr (keepsRes_of_grows hg) (resAtL_grows (xctx_resAtL hX) hg) hi hs, hj, hmodel,
    xrecLocs_sa hxl hsa (hfr.get 32) (hfr.get 34) (hfr.get 33), strLoc_sa hcr hsa (hfr.get 37), hcf, h38, h26,
    by omega, by omega, ?_⟩
  intro k hk
  rcases Nat.lt_or_ge k i.toInt.toNat with h | h
  · exact hall k h
  · have e : k = i.toInt.toNat := by omega
    rw [e]; exact hm

/-- At statement 168 after `createStatement`: the cards loop of record `j` from card number 1, total 0. -/
theorem close168 {g : RunG} {args : List Value} {σ0 σ σ' : State} {fr fr' : Frame} {res ld ls lh : Addr}
    {L : LdSt} {o : JOut} {j : Nat} {crec arec : JStr}
    (hX : XCtx g σ0 fr σ res ld ls lh o L (j + 1)) (hj : j < g.T2.length)
    (hmodel : xrefAll g.K3 g.T3 g.T4 L o (g.T2.drop j) = g.F) (hxl : XrecLocs σ fr (g.T2.getD j []))
    (hcf : custFind g.K3 g.T3 (sub (fixStr (g.T2.getD j []) 1000) 16 25) = some crec)
    (haf : acctFind g.T4 (sub (fixStr (g.T2.getD j []) 1000) 25 36) = some arec)
    (hfr : FrOk fr fr') (h17 : fr'.get 17 = some (.long 1)) (h21 : fr'.get 21 = some (.long 0))
    (hk : KeepsRes res ld ls lh σ σ')
    (hR : ResAtL σ' res ld ls lh o.disp (o.stmt ++ (jCreateStatement crec arec).1)
      (o.html ++ (jCreateStatement crec arec).2) o.ab)
    (hi : σ'.inits = σ.inits) (hs : σ'.statics = σ.statics) :
    inv168 g args σ0 fr' σ' := by
  have hsa := saMono_of_keepsRes (xctx_resAtL hX) hk
  have hc0 : 0 ≤ L.cr.toInt := (xctx_ldBounded hX).1
  exact ⟨res, ld, ls, lh, L, o.add (jCreateStatement crec arec), j, 1, 0, L.cr.toInt.toNat,
    cardsFrom L.m L.trct L.cr (sub (fixStr (g.T2.getD j []) 1000) 0 16) L.cr.toInt.toNat 1
      (o.add (jCreateStatement crec arec), 0),
    xctx_frame hX hfr hk hR hi hs, hj, model_found hj hmodel hcf haf, strLoc_sa hxl.1 hsa (hfr.get 32), h17, h21,
    ⟨by decide, by decide⟩, by decide, by rw [i64_one_toInt]; omega, rfl⟩

end EquivLean.Modernize.Cbstm03a.Java.Seg5

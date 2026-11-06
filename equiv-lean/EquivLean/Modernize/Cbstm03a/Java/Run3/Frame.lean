import EquivLean.Modernize.Cbstm03a.Java.Run3.Common

/-!
# CBSTM03A → Java, `run`'s segments 117, 140, 153: the loop state across a path

`KeepsOn P σ σ'`: the objects of `σ` with property `P` are unchanged in `σ'`. A path that only allocates, calls
helpers that only allocate, and updates `xrefSt` (an `int[]`) keeps every object that is not an `int[]`
(`NotIntArr`); a path whose last call updates the `Result` object and its lists keeps every object that is
neither a plain object nor a list (`NotPL`). The loop state `XCtx` is carried across such paths
(`xctx_keeps_st2`, `xctx_keeps_res`), given the locals it names (`xLocals`) unchanged.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK grows_split
  growsK_elim forall2_imp)
open EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java.Seg3

/-- The objects of `σ` with property `P` are unchanged in `σ'`. -/
def KeepsOn (P : Obj → Prop) (σ σ' : State) : Prop :=
  σ.next ≤ σ'.next ∧ ∀ y o, σ.heap y = some o → P o → σ'.heap y = some o

theorem heap_on {P : Obj → Prop} {σ σ' : State} (hk : KeepsOn P σ σ') {y : Addr} {o : Obj}
    (hy : σ.heap y = some o) (hp : P o) : σ'.heap y = some o := hk.2 y o hy hp

/-- Not an `int[]`. -/
def NotIntArr (o : Obj) : Prop := ∀ v, o ≠ .array (.prim .int) v

/-- Neither a plain object nor a list. -/
def NotPL (o : Obj) : Prop := (∀ c fs, o ≠ .plain c fs) ∧ (∀ k xs m, o ≠ .list k xs m)

theorem keepsOn_of_keeps {σ σ' : State} {b : Addr} {vb : List Value} (hk : Keeps (· = b) σ σ')
    (hb : σ.heap b = some (.array (.prim .int) vb)) : KeepsOn NotIntArr σ σ' :=
  ⟨hk.1, fun y o hy hp => by
    have hne : ¬ y = b := by
      rintro rfl
      rw [hb] at hy
      exact hp vb (Option.some.inj hy).symm
    rw [hk.2 y (State.lt_next_of_heap hy) hne, hy]⟩

/-- The `Result` object and its lists, as the addresses a call may update. -/
def ResAddr (res ld ls lh : Addr) (y : Addr) : Prop := y = res ∨ y = ld ∨ y = ls ∨ y = lh

theorem keeps_of_keepsRes {res ld ls lh : Addr} {σ σ' : State} (h : KeepsRes res ld ls lh σ σ') :
    Keeps (ResAddr res ld ls lh) σ σ' :=
  ⟨h.1, fun y hy hA => h.2 y hy (fun e => hA (Or.inl e)) (fun e => hA (Or.inr (Or.inl e)))
    (fun e => hA (Or.inr (Or.inr (Or.inl e)))) (fun e => hA (Or.inr (Or.inr (Or.inr e))))⟩

theorem keepsOn_of_keepsRes {σ σ' : State} {res ld ls lh : Addr} {d s h : List JStr} {ab : Bool}
    (hk : Keeps (ResAddr res ld ls lh) σ σ') (hr : ResAtL σ res ld ls lh d s h ab) : KeepsOn NotPL σ σ' :=
  ⟨hk.1, fun y o hy hp => by
    obtain ⟨fs, h1, -, -, -, -, -, -, -, ⟨xd, md, hd, -⟩, ⟨xs, ms, hs, -⟩, ⟨xh, mh, hh, -⟩⟩ := hr
    have hne : ¬ ResAddr res ld ls lh y := by
      rintro (rfl | rfl | rfl | rfl)
      · rw [h1] at hy; exact hp.1 _ _ (Option.some.inj hy).symm
      · rw [hd] at hy; exact hp.2 _ _ _ (Option.some.inj hy).symm
      · rw [hs] at hy; exact hp.2 _ _ _ (Option.some.inj hy).symm
      · rw [hh] at hy; exact hp.2 _ _ _ (Option.some.inj hy).symm
    rw [hk.2 y (State.lt_next_of_heap hy) hne, hy]⟩

/-! ## The parts of the loop state -/

section
variable {P : Obj → Prop} {σ σ' : State}

theorem jstrAt_on (hk : KeepsOn P σ σ') (hPs : ∀ s, P (.str s)) {v : Value} {s : JStr}
    (h : JStrAt σ v s) : JStrAt σ' v s := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, heap_on hk hx (hPs s)⟩

theorem forall2_on (hk : KeepsOn P σ σ') (hPs : ∀ s, P (.str s)) {xs : List Value} {ts : List JStr}
    (h : Forall2 (JStrAt σ) xs ts) : Forall2 (JStrAt σ') xs ts :=
  forall2_imp (fun _ _ h => jstrAt_on hk hPs h) h

theorem textsAt_on (hk : KeepsOn P σ σ') (hPs : ∀ s, P (.str s))
    (hPa : ∀ xs, P (.array (.cls "java.lang.String") xs)) {a : Addr} {ts : List JStr} {n : Nat}
    (h : TextsAt σ a ts n) : TextsAt σ' a ts n := by
  obtain ⟨xs, h1, h2⟩ := h
  exact ⟨xs, heap_on hk h1 (hPa _), forall2_on hk hPs h2⟩

theorem slotsAt_on (hk : KeepsOn P σ σ') (hPs : ∀ s, P (.str s))
    (hPa : ∀ xs, P (.array (.cls "java.lang.String") xs)) {a : Addr} {m : Nat → JChar}
    (h : SlotsAt σ a m) : SlotsAt σ' a m := by
  obtain ⟨vs, h1, h2, h3⟩ := h
  refine ⟨vs, heap_on hk h1 (hPa _), h2, fun i hi => ?_⟩
  rcases h3 i hi with ⟨hn, hm⟩ | ⟨x, t, hx, hxt, htl, hm⟩
  · exact Or.inl ⟨hn, hm⟩
  · exact Or.inr ⟨x, t, hx, heap_on hk hxt (hPs t), htl, hm⟩

theorem listAt_on (hk : KeepsOn P σ σ') (hPs : ∀ s, P (.str s))
    (hPl : ∀ xs m, P (.list .arrayList xs m)) {l : Addr} {ss : List JStr} (h : ListAt σ l ss) :
    ListAt σ' l ss := by
  obtain ⟨xs, m, h1, h2⟩ := h
  exact ⟨xs, m, heap_on hk h1 (hPl _ _), forall2_on hk hPs h2⟩

theorem resAtL_on (hk : KeepsOn P σ σ') (hPs : ∀ s, P (.str s)) (hPl : ∀ xs m, P (.list .arrayList xs m))
    (hPp : ∀ fs, P (.plain resC fs)) {res ld ls lh : Addr} {d s h : List JStr} {ab : Bool}
    (hr : ResAtL σ res ld ls lh d s h ab) : ResAtL σ' res ld ls lh d s h ab := by
  obtain ⟨fs, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hr
  exact ⟨fs, heap_on hk h1 (hPp _), h2, h3, h4, h5, h6, h7, h8, listAt_on hk hPs hPl h9,
    listAt_on hk hPs hPl h10, listAt_on hk hPs hPl h11⟩

theorem strLoc_on (hk : KeepsOn P σ σ') (hPs : ∀ s, P (.str s)) {fr fr' : Frame} {i : Nat} {s : JStr}
    (h : StrLoc σ fr i s) (he : fr'.get i = fr.get i) : StrLoc σ' fr' i s := by
  obtain ⟨x, h1, h2⟩ := h
  exact ⟨x, he.trans h1, heap_on hk h2 (hPs s)⟩

end

theorem notIntArr_str (s : JStr) : NotIntArr (.str s) := fun _ h => by cases h
theorem notIntArr_arrS (xs : List Value) : NotIntArr (.array (.cls "java.lang.String") xs) := fun _ h => by cases h
theorem notIntArr_arrL (xs : List Value) : NotIntArr (.array (.prim .long) xs) := fun _ h => by cases h
theorem notIntArr_list (xs : List Value) (m : Nat) : NotIntArr (.list .arrayList xs m) := fun _ h => by cases h
theorem notIntArr_plain (fs : List (FieldKey × Value)) : NotIntArr (.plain resC fs) := fun _ h => by cases h
theorem notPL_str (s : JStr) : NotPL (.str s) := ⟨fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
theorem notPL_arr (t : JType) (xs : List Value) : NotPL (.array t xs) :=
  ⟨fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩

/-- The locals the loop state names. -/
def xLocals : List Nat := [10, 23, 9, 6, 7, 11, 12, 13, 14, 15, 27, 28, 16, 24, 2, 5, 3, 18]

/-- The loop state across a path that keeps every object but `xrefSt` (`b`), whose new contents is given. -/
theorem xctx_keeps_st2 {g : RunG} {σ0 : State} {fr fr' : Frame} {σ σ' : State} {res ld ls lh : Addr}
    {o : JOut} {L : LdSt} {j j' : Nat} {b : Addr}
    (hX : XCtx g σ0 fr σ res ld ls lh o L j) (hf2 : fr.get 2 = some (.ref b)) (hk : Keeps (· = b) σ σ')
    (hb : σ'.heap b = some (.array (.prim .int) [.int (BitVec.ofNat 32 j'), .int 0]))
    (hfr : ∀ k, k ∈ xLocals → fr'.get k = fr.get k) (hin : σ'.inits = σ.inits)
    (hstat : σ'.statics = σ.statics) :
    XCtx g σ0 fr' σ' res ld ls lh o L j' := by
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, ⟨h10, h23, h9, h6, h7, hres, hr0, hl0, hs0, hh0, hg0, hin0, hst0⟩,
    ⟨h11, h12, h13, h14, h15, ⟨n3, h27, hn3⟩, ⟨n4, h28, hn4⟩, hT1, hT2, hT3k, hT3, hT4, o1, o2, o3, o4, o5⟩,
    ⟨h16, h24, hS, htr, htrl⟩, h2, hst2, o6, o7, o8, h5, h3, h18, hLB⟩ := hX
  have hb2 : st2 = b := by rw [h2] at hf2; exact Value.ref.inj (Option.some.inj hf2)
  subst hb2
  have hko := keepsOn_of_keeps hk hst2
  have hlt0 : σ0.next ≤ st2 :=
    Nat.le_of_lt (Nat.lt_of_le_of_lt o1 (Nat.lt_trans o2 (Nat.lt_trans o3 (Nat.lt_trans o4
      (Nat.lt_trans o5 (Nat.lt_trans o6 (Nat.lt_trans o7 o8)))))))
  have hg0' : Grows σ0 σ' := ⟨Nat.le_trans hg0.1 hk.1, fun x hx => by
    rw [hk.2 x (Nat.lt_of_lt_of_le hx hg0.1) (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx hlt0)), hg0.2 x hx]⟩
  have e : ∀ k, k ∈ xLocals → fr'.get k = fr.get k := hfr
  refine ⟨t1, t2, t3k, t3, t4, mem, trct, st2, ⟨?_, ?_, ?_, ?_, ?_, ?_, hr0, hl0, hs0, hh0, hg0', ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ⟨n3, ?_, hn3⟩, ⟨n4, ?_, hn4⟩, ?_, ?_, ?_, ?_, ?_, o1, o2, o3, o4, o5⟩,
    ⟨?_, ?_, ?_, ?_, htrl⟩, ?_, hb, o6, o7, o8, ?_, ?_, ?_, hLB⟩
  · rw [e 10 (by decide)]; exact h10
  · rw [e 23 (by decide)]; exact h23
  · rw [e 9 (by decide)]; exact h9
  · rw [e 6 (by decide)]; exact h6
  · rw [e 7 (by decide)]; exact h7
  · exact resAtL_on hko notIntArr_str notIntArr_list notIntArr_plain hres
  · rw [hin, hin0]
  · rw [hstat, hst0]
  · rw [e 11 (by decide)]; exact h11
  · rw [e 12 (by decide)]; exact h12
  · rw [e 13 (by decide)]; exact h13
  · rw [e 14 (by decide)]; exact h14
  · rw [e 15 (by decide)]; exact h15
  · rw [e 27 (by decide)]; exact h27
  · rw [e 28 (by decide)]; exact h28
  · exact textsAt_on hko notIntArr_str notIntArr_arrS hT1
  · exact textsAt_on hko notIntArr_str notIntArr_arrS hT2
  · exact textsAt_on hko notIntArr_str notIntArr_arrS hT3k
  · exact textsAt_on hko notIntArr_str notIntArr_arrS hT3
  · exact textsAt_on hko notIntArr_str notIntArr_arrS hT4
  · rw [e 16 (by decide)]; exact h16
  · rw [e 24 (by decide)]; exact h24
  · exact slotsAt_on hko notIntArr_str notIntArr_arrS hS
  · exact heap_on hko htr (notIntArr_arrL _)
  · rw [e 2 (by decide)]; exact h2
  · rw [e 5 (by decide)]; exact h5
  · rw [e 3 (by decide)]; exact h3
  · rw [e 18 (by decide)]; exact h18

/-- The loop state across a path whose last call updates the `Result` object (its new contents given). -/
theorem xctx_keeps_res {g : RunG} {σ0 : State} {fr fr' : Frame} {σ σ' : State} {res ld ls lh : Addr}
    {o o' : JOut} {L : LdSt} {j : Nat}
    (hX : XCtx g σ0 fr σ res ld ls lh o L j) (hk : Keeps (ResAddr res ld ls lh) σ σ')
    (hres' : ResAtL σ' res ld ls lh o'.disp o'.stmt o'.html o'.ab)
    (hfr : ∀ k, k ∈ xLocals → fr'.get k = fr.get k) (hin : σ'.inits = σ.inits)
    (hstat : σ'.statics = σ.statics) :
    XCtx g σ0 fr' σ' res ld ls lh o' L j := by
  obtain ⟨t1, t2, t3k, t3, t4, mem, trct, st2, ⟨h10, h23, h9, h6, h7, hres, hr0, hl0, hs0, hh0, hg0, hin0, hst0⟩,
    ⟨h11, h12, h13, h14, h15, ⟨n3, h27, hn3⟩, ⟨n4, h28, hn4⟩, hT1, hT2, hT3k, hT3, hT4, o1, o2, o3, o4, o5⟩,
    ⟨h16, h24, hS, htr, htrl⟩, h2, hst2, o6, o7, o8, h5, h3, h18, hLB⟩ := hX
  have hko := keepsOn_of_keepsRes hk hres
  have hg0' : Grows σ0 σ' := ⟨Nat.le_trans hg0.1 hk.1, fun x hx => by
    have hA : ¬ ResAddr res ld ls lh x := by
      rintro (rfl | rfl | rfl | rfl)
      · exact absurd hr0 (Nat.not_le.2 hx)
      · exact absurd hl0 (Nat.not_le.2 hx)
      · exact absurd hs0 (Nat.not_le.2 hx)
      · exact absurd hh0 (Nat.not_le.2 hx)
    rw [hk.2 x (Nat.lt_of_lt_of_le hx hg0.1) hA, hg0.2 x hx]⟩
  have e : ∀ k, k ∈ xLocals → fr'.get k = fr.get k := hfr
  refine ⟨t1, t2, t3k, t3, t4, mem, trct, st2, ⟨?_, ?_, ?_, ?_, ?_, hres', hr0, hl0, hs0, hh0, hg0', ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ⟨n3, ?_, hn3⟩, ⟨n4, ?_, hn4⟩, ?_, ?_, ?_, ?_, ?_, o1, o2, o3, o4, o5⟩,
    ⟨?_, ?_, ?_, ?_, htrl⟩, ?_, ?_, o6, o7, o8, ?_, ?_, ?_, hLB⟩
  · rw [e 10 (by decide)]; exact h10
  · rw [e 23 (by decide)]; exact h23
  · rw [e 9 (by decide)]; exact h9
  · rw [e 6 (by decide)]; exact h6
  · rw [e 7 (by decide)]; exact h7
  · rw [hin, hin0]
  · rw [hstat, hst0]
  · rw [e 11 (by decide)]; exact h11
  · rw [e 12 (by decide)]; exact h12
  · rw [e 13 (by decide)]; exact h13
  · rw [e 14 (by decide)]; exact h14
  · rw [e 15 (by decide)]; exact h15
  · rw [e 27 (by decide)]; exact h27
  · rw [e 28 (by decide)]; exact h28
  · exact textsAt_on hko notPL_str (notPL_arr _) hT1
  · exact textsAt_on hko notPL_str (notPL_arr _) hT2
  · exact textsAt_on hko notPL_str (notPL_arr _) hT3k
  · exact textsAt_on hko notPL_str (notPL_arr _) hT3
  · exact textsAt_on hko notPL_str (notPL_arr _) hT4
  · rw [e 16 (by decide)]; exact h16
  · rw [e 24 (by decide)]; exact h24
  · exact slotsAt_on hko notPL_str (notPL_arr _) hS
  · exact heap_on hko htr (notPL_arr _ _)
  · rw [e 2 (by decide)]; exact h2
  · exact heap_on hko hst2 (notPL_arr _ _)
  · rw [e 5 (by decide)]; exact h5
  · rw [e 3 (by decide)]; exact h3
  · rw [e 18 (by decide)]; exact h18

/-- `fr'` keeps the locals `xLocals` of `fr` (a frame built by `setLocal`s at other indices). -/
macro "seg3_fr_tac" : tactic => `(tactic| (intro k hk; simp only [xLocals, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (subst h; simp (config := {decide := true}) only [Frame.get_setLocal, ↓reduceIte])))

/-! ## Heap lookups after allocations and callees -/

theorem heap_alloc_eq {σ : State} {o : Obj} {a : Addr} {v : Option Obj} (ha : a < σ.next) (h : σ.heap a = v) :
    (σ.alloc o).2.heap a = v := by rw [State.heap_alloc_of_lt ha, h]

theorem heap_alloc_at {σ : State} {o o' : Obj} {a : Addr} (ha : a = σ.next) (ho : o = o') :
    (σ.alloc o).2.heap a = some o' := by rw [State.heap_alloc, if_pos ha, ho]

theorem heap_growsK_eq {σ σ' : State} {a : Addr} {v : Option Obj} (hg : GrowsK σ σ') (ha : a < σ.next)
    (h : σ.heap a = v) : σ'.heap a = v := by rw [(growsK_elim hg).2 a ha, h]

theorem heap_keepsK_eq {σ σ' : State} {a b : Addr} {v : Option Obj} (hk : KeepsK (· = b) σ σ')
    (ha : a < σ.next) (hab : a ≠ b) (h : σ.heap a = v) : σ'.heap a = v := by
  rw [(keepsK_elim hk).2 a ha hab, h]

end EquivLean.Modernize.Cbstm03a.Java.Seg3

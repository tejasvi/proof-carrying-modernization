import EquivLean.Modernize.Cbstm03a.Java.Run2.Defs

/-!
# CBSTM03A → Java `run`, the load loop: frames and the load step's facts

`ArrOnly A σ`: the addresses of `A` hold arrays in `σ`, so strings, plain objects and lists are outside `A`; a
relation over such objects carries over a `Keeps A`. The load step keeps the counters' bounds; the remaining load
from record `k` is one step, then the load from `k + 1`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space GrowsK growsK_elim
  grows_split keeps_refl keeps_trans keeps_of_grows Kept msb_false_of_toInt_nonneg heap_growsK_lt)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

/-! ## Frames -/

/-- The addresses of `A` hold arrays in `σ`. -/
def ArrOnly (A : Addr → Prop) (σ : State) : Prop := ∀ y, A y → ∃ et vs, σ.heap y = some (.array et vs)

theorem heap_keeps' {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') {y : Addr} {o : Obj}
    (hy : σ.heap y = some o) (hA : ¬ A y) : σ'.heap y = some o := by
  rw [hk.2 y (State.lt_next_of_heap hy) hA, hy]

theorem not_A_of_nonarr {A : Addr → Prop} {σ : State} (hn : ArrOnly A σ) {y : Addr} {o : Obj}
    (hy : σ.heap y = some o) (ho : ∀ et vs, o ≠ .array et vs) : ¬ A y := fun hA => by
  obtain ⟨et, vs, h⟩ := hn y hA
  rw [hy] at h
  exact ho et vs (Option.some.inj h)

theorem str_keeps {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') (hn : ArrOnly A σ) {y : Addr} {s : JStr}
    (hy : σ.heap y = some (.str s)) : σ'.heap y = some (.str s) :=
  heap_keeps' hk hy (not_A_of_nonarr hn hy (fun _ _ e => by cases e))

theorem jstrAt_keeps' {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') (hn : ArrOnly A σ) {v : Value}
    {s : JStr} (h : JStrAt σ v s) : JStrAt σ' v s := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, str_keeps hk hn hx⟩

theorem forall2_jstr_keeps {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') (hn : ArrOnly A σ) :
    ∀ {xs : List Value} {ts : List JStr}, Forall2 (JStrAt σ) xs ts → Forall2 (JStrAt σ') xs ts
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (jstrAt_keeps' hk hn h) (forall2_jstr_keeps hk hn hs)

theorem textsAt_keeps {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') (hn : ArrOnly A σ) {a : Addr}
    {ts : List JStr} {n : Nat} (h : TextsAt σ a ts n) (ha : ¬ A a) : TextsAt σ' a ts n := by
  obtain ⟨xs, h1, h2⟩ := h
  exact ⟨xs, heap_keeps' hk h1 ha, forall2_jstr_keeps hk hn h2⟩

theorem strLoc_keeps {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') (hn : ArrOnly A σ) {fr fr' : Frame}
    {i : Nat} {s : JStr} (h : StrLoc σ fr i s) (hf : fr'.get i = fr.get i) : StrLoc σ' fr' i s := by
  obtain ⟨x, h1, h2⟩ := h
  exact ⟨x, hf.trans h1, str_keeps hk hn h2⟩

theorem listAt_keeps {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') (hn : ArrOnly A σ) {l : Addr}
    {ss : List JStr} (h : ListAt σ l ss) : ListAt σ' l ss := by
  obtain ⟨xs, m, h1, h2⟩ := h
  exact ⟨xs, m, heap_keeps' hk h1 (not_A_of_nonarr hn h1 (fun _ _ e => by cases e)), forall2_jstr_keeps hk hn h2⟩

theorem resAtL_keeps {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') (hn : ArrOnly A σ)
    {res ld ls lh : Addr} {disp st ht : List JStr} {ab : Bool} (h : ResAtL σ res ld ls lh disp st ht ab) :
    ResAtL σ' res ld ls lh disp st ht ab := by
  obtain ⟨fs, hr, f1, f2, f3, f4, d1, d2, d3, l1, l2, l3⟩ := h
  exact ⟨fs, heap_keeps' hk hr (not_A_of_nonarr hn hr (fun _ _ e => by cases e)), f1, f2, f3, f4, d1, d2, d3,
    listAt_keeps hk hn l1, listAt_keeps hk hn l2, listAt_keeps hk hn l3⟩

theorem slotsAt_keeps {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') (hn : ArrOnly A σ) {a : Addr}
    {m : Nat → JChar} (h : SlotsAt σ a m) (ha : ¬ A a) : SlotsAt σ' a m := by
  obtain ⟨vs, h1, h2, h3⟩ := h
  refine ⟨vs, heap_keeps' hk h1 ha, h2, fun i hi => ?_⟩
  rcases h3 i hi with h | ⟨x, t, e1, e2, e3, e4⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, t, e1, str_keeps hk hn e2, e3, e4⟩

theorem grows_keeps {A : Addr → Prop} {σ0 σ σ' : State} (hg : Grows σ0 σ) (hk : Keeps A σ σ')
    (hA : ∀ y, A y → σ0.next ≤ y) : Grows σ0 σ' :=
  ⟨Nat.le_trans hg.1 hk.1, fun x hx => by
    rw [hk.2 x (Nat.lt_of_lt_of_le hx hg.1) (fun h => absurd (hA x h) (Nat.not_le.2 hx)), hg.2 x hx]⟩

theorem keeps_mono {A B : Addr → Prop} {σ σ' : State} (h : Keeps A σ σ') (hAB : ∀ y, A y → B y) :
    Keeps B σ σ' :=
  ⟨h.1, fun y hy hB => h.2 y hy (fun hA => hB (hAB y hA))⟩

theorem keeps_alloc2 {A : Addr → Prop} {σ0 σ : State} (h : Keeps A σ0 σ) (o : Obj) :
    Keeps A σ0 (σ.alloc o).2 :=
  keeps_trans h (keeps_of_grows ⟨by rw [State.next_alloc]; exact Nat.le_succ _,
    fun _ hy => State.heap_alloc_of_lt hy o⟩)

theorem keeps_growsK {A : Addr → Prop} {σ0 σ σ' : State} (h : Keeps A σ0 σ) (hg : GrowsK σ σ') :
    Keeps A σ0 σ' :=
  keeps_trans h (keeps_of_grows (growsK_elim hg))

theorem keeps_keepsK {A B : Addr → Prop} {σ0 σ σ' : State} (h : Keeps A σ0 σ) (hk : KeepsK B σ σ')
    (hBA : ∀ y, B y → A y) : Keeps A σ0 σ' :=
  keeps_trans h (keeps_mono (keepsK_elim hk) hBA)

/-- `Keeps A σ0 σ'` for a state built from `σ0` by allocations and callees (`GrowsK`, `KeepsK`). -/
macro "keeps_peel" : tactic => `(tactic| repeat (first
  | exact keeps_refl _ _
  | refine keeps_alloc2 ?_ _
  | refine keeps_growsK ?_ (by assumption)
  | refine keeps_keepsK ?_ (by assumption) (by intro y hy; first | exact hy | exact Or.inl hy | exact Or.inr (Or.inl hy) | exact Or.inr (Or.inr hy))))

theorem heap_keepsK_lt {A : Addr → Prop} {σ σ' : State} (h : KeepsK A σ σ') {x : Addr} (hx : x < σ.next)
    (hA : ¬ A x) : σ'.heap x = σ.heap x :=
  (keepsK_elim h).2 x hx hA

open Lean Meta Elab Tactic in
/-- Rewrite a lookup `σ'.heap x` of the goal to `σ.heap x` with a hypothesis `GrowsK σ σ'` or `KeepsK A σ σ'`
(side conditions by `jdisch`). -/
elab "frameK_rw" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let lem? : Option Name :=
        if ty.isAppOfArity ``GrowsK 2 then some ``heap_growsK_lt
        else if ty.isAppOfArity ``KeepsK 3 then some ``heap_keepsK_lt
        else none
      let some lem := lem? | continue
      let s ← saveState
      try
        let e ← mkAppM lem #[d.toExpr]
        let r ← g.rewrite (← g.getType) e
        let g' ← g.replaceTargetEq r.eNew r.eqProof
        for m in r.mvarIds do
          unless ← m.isAssigned do
            let gs ← Tactic.run m (evalTactic (← `(tactic| first | jdisch | (simp only; jdisch) | (intro h; subst h; jdisch))))
            unless gs.isEmpty do throwError "frameK_rw: side condition left"
        replaceMainGoal [g']
        return
      catch _ => s.restore
    throwError "frameK_rw: no frame hypothesis rewrites the goal"

/-- Heap lookups through allocations and callees (`GrowsK`, `KeepsK`). -/
macro "hsimpF" : tactic => `(tactic| repeat (first | (simp (disch := jdisch) only [State.heap_setObj_of_lt, State.heap_alloc, State.next_alloc, State.next_setObj, ↓reduceIte, ite_nat_ne, eq_self_iff_true, if_true]) | frameK_rw))

/-! ## The load step -/

theorem trctSet_lengthR (vs : List Value) (cr v : I64) : (trctSet vs cr v).length = vs.length := by
  unfold trctSet; split <;> simp

theorem trctSet_bounded {vs : List Value} {cr v : I64}
    (hvs : ∀ w ∈ vs, ∃ c : I64, w = .long c ∧ 0 ≤ c.toInt ∧ c.toInt < 10000) (hv : 0 ≤ v.toInt ∧ v.toInt < 10000) :
    ∀ w ∈ trctSet vs cr v, ∃ c : I64, w = .long c ∧ 0 ≤ c.toInt ∧ c.toInt < 10000 := by
  unfold trctSet
  split
  · intro w hw
    rcases List.mem_or_eq_of_mem_set hw with h | h
    · exact hvs w h
    · exact ⟨v, h, hv⟩
  · exact hvs

theorem toInt_eq_toNat_of_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) :
    l.toInt = l.toNat ∧ 2 * l.toNat < 2 ^ 64 := by
  have hc := BitVec.toInt_eq_toNat_cond l
  have hl := l.isLt
  by_cases hq : 2 * l.toNat < 2 ^ 64
  · rw [if_pos hq] at hc; exact ⟨hc, hq⟩
  · rw [if_neg hq] at hc; omega

theorem toInt_of_toNat_small (l : BitVec 64) (h : 2 * l.toNat < 2 ^ 64) : l.toInt = l.toNat := by
  rw [BitVec.toInt_eq_toNat_cond, if_pos h]

/-- `(c + 1) % 10000` of a counter in `0 … 9999` stays in `0 … 9999`. -/
theorem succ_srem_bound (c : I64) (h0 : 0 ≤ c.toInt) (h1 : c.toInt < 10000) :
    0 ≤ ((c + 1).srem 10000).toInt ∧ ((c + 1).srem 10000).toInt < 10000 := by
  obtain ⟨hc, hq⟩ := toInt_eq_toNat_of_nonneg c h0
  have h1n : (1 : BitVec 64).toNat = 1 := rfl
  have hn : (c + 1).toNat = c.toNat + 1 := by
    rw [BitVec.toNat_add, h1n]; omega
  have hpos : 0 ≤ (c + 1).toInt := by
    rw [toInt_of_toNat_small _ (by omega)]; omega
  have hmsb := msb_false_of_toInt_nonneg (c + 1) hpos
  have h10 : (10000 : BitVec 64).msb = false := by decide
  have he : (c + 1).srem 10000 = (c + 1) % 10000 := by
    rw [BitVec.srem_eq, hmsb, h10]
  have h10n : (10000 : BitVec 64).toNat = 10000 := rfl
  have hu : ((c + 1) % 10000).toNat = (c.toNat + 1) % 10000 := by
    rw [BitVec.toNat_umod, hn, h10n]
  rw [he, toInt_of_toNat_small _ (by omega)]
  omega

theorem ldStep_same {s : LdSt} {rec : JStr} (h : s.save = sub rec 0 16) :
    ldStep s rec = ⟨memWr (memWr (memWr s.m (cardOffJ s.cr).toInt (sub rec 0 16))
        (tranOffJ s.cr ((s.tr + 1).srem 10000)).toInt (sub rec 16 32))
        (tranOffJ s.cr ((s.tr + 1).srem 10000) + 16).toInt (sub rec 32 350),
      s.trct, s.cr, (s.tr + 1).srem 10000, sub rec 0 16⟩ := by
  simp only [ldStep, h, ↓reduceIte]

theorem ldStep_diff {s : LdSt} {rec : JStr} (h : ¬ s.save = sub rec 0 16) :
    ldStep s rec = ⟨memWr (memWr (memWr s.m (cardOffJ ((s.cr + 1).srem 10000)).toInt (sub rec 0 16))
        (tranOffJ ((s.cr + 1).srem 10000) 1).toInt (sub rec 16 32))
        (tranOffJ ((s.cr + 1).srem 10000) 1 + 16).toInt (sub rec 32 350),
      trctSet s.trct s.cr s.tr, (s.cr + 1).srem 10000, 1, sub rec 0 16⟩ := by
  simp only [ldStep, h, ↓reduceIte]

theorem ldStep_bounded {s : LdSt} (rec : JStr) (hb : LdBounded s) : LdBounded (ldStep s rec) := by
  obtain ⟨c0, c1, t0, t1, hv⟩ := hb
  by_cases h : s.save = sub rec 0 16
  · rw [ldStep_same h]
    have := succ_srem_bound s.tr t0 t1
    exact ⟨c0, c1, this.1, this.2, hv⟩
  · rw [ldStep_diff h]
    have := succ_srem_bound s.cr c0 c1
    have h1i : (1 : I64).toInt = 1 := by decide
    exact ⟨this.1, this.2, by dsimp only; rw [h1i]; omega, by dsimp only; rw [h1i]; omega,
      trctSet_bounded hv ⟨t0, t1⟩⟩

theorem ldFin_bounded {s : LdSt} (hb : LdBounded s) : LdBounded (ldFin s) := by
  obtain ⟨c0, c1, t0, t1, hv⟩ := hb
  exact ⟨c0, c1, t0, t1, trctSet_bounded hv ⟨t0, t1⟩⟩

theorem ldAll_drop_succ (s : LdSt) (rs : List JStr) (k : Nat) (hk : k < rs.length) :
    ldAll s (rs.drop k) = ldAll (ldStep s (rs.getD k [])) (rs.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons hk, List.getD_eq_getElem _ _ hk]
  rfl

theorem ldAll_drop_last (s : LdSt) (rs : List JStr) (k : Nat) (hk : k + 1 = rs.length) :
    ldAll s (rs.drop k) = ldStep s (rs.getD k []) := by
  rw [ldAll_drop_succ s rs k (by omega), List.drop_eq_nil_of_le (by omega)]
  rfl

end EquivLean.Modernize.Cbstm03a.Java.Seg2

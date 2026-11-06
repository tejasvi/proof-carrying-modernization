import EquivLean.Modernize.Cbstm03b.Java.Base
import EquivLean.Modernize.Cbstm03b.Java.AcctKey

/-!
# CBSTM03B → Java, `acctProc`: the final states

`acctProc` writes four objects: the State object, the ACCTFILE object, the area and (a keyed read) the FD record
object in place; everything else it allocates. `AccA st o4 q fdr` is that set of addresses; a final state keeps
every other object (`Keeps`, `keeps_tac`). From the written objects' fields the postcondition follows:
`acctFile_fin` (the ACCTFILE object), `state_fin` (`StateAtM`), `sepM_fin` (`SepM`), `area_fin` (the area).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

/-- The objects `acctProc` writes: the State object, the ACCTFILE object, the area, the FD record object. -/
def AccA (st o4 q fdr : Addr) (y : Addr) : Prop := y = st ∨ y = o4 ∨ y = q ∨ y = fdr

/-! ## Final states keep the other objects -/

theorem keeps_set_in {A : Addr → Prop} {σ0 σ : State} (h : Keeps A σ0 σ) {a : Addr} (o : Obj) (ha : A a) :
    Keeps A σ0 (σ.setObj a o) := keeps_trans h (keeps_setObj o ha)

theorem keeps_set_new {A : Addr → Prop} {σ0 σ : State} (h : Keeps A σ0 σ) {a : Addr} (o : Obj)
    (ha : σ0.next ≤ a) : Keeps A σ0 (σ.setObj a o) :=
  ⟨by rw [State.next_setObj]; exact h.1, fun y hy hA => by
    rw [State.heap_setObj, if_neg (Nat.ne_of_lt (Nat.lt_of_lt_of_le hy ha))]; exact h.2 y hy hA⟩

theorem keeps_alloc' {A : Addr → Prop} {σ0 σ : State} (h : Keeps A σ0 σ) (o : Obj) :
    Keeps A σ0 (σ.alloc o).2 := keeps_trans h (keeps_alloc A σ o)

/-- Address side conditions (`x < σ.next`, `σ0.next ≤ x`, `x ≠ y`) without `decide` (which would evaluate the
heap). -/
syntax "hdisch" : tactic
macro_rules
  | `(tactic| hdisch) => `(tactic| first
      | assumption
      | jomega_rel
      | (simp only [State.next_alloc, State.next_setObj]; jomega_rel)
      | jne_heap)

/-- `Keeps (AccA …) σ0 σ'` for a state built from `σ0` by allocations and writes (to `AccA` or fresh objects). -/
syntax "keeps_tac" : tactic
macro_rules
  | `(tactic| keeps_tac) => `(tactic| first
      | with_reducible exact keeps_refl _ _
      | with_reducible assumption
      | ((with_reducible refine keeps_alloc' ?_ _); keeps_tac)
      | ((with_reducible refine keeps_set_in ?_ _ (by simp only [AccA, eq_self_iff_true, true_or, or_true]));
          keeps_tac)
      | ((with_reducible refine keeps_set_new ?_ _ (by hdisch)); keeps_tac))

theorem accA_away {σ : State} {st o4 q fdr : Addr} {fsS fs4 fsq fsr : List (FieldKey × Value)}
    (hst : σ.heap st = some (.plain "Cbstm03b$State" fsS))
    (h4 : σ.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4))
    (hq : σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq))
    (hr : σ.heap fdr = some (.plain "Cbstm03b$FdAcctfileRec" fsr)) (cs : List ClassName)
    (hcs : "Cbstm03b$State" ∉ cs ∧ "Cbstm03b$AcctFile" ∉ cs ∧ "Cbstm03b$LkM03bArea" ∉ cs ∧
      "Cbstm03b$FdAcctfileRec" ∉ cs) :
    Away (AccA st o4 q fdr) σ cs := by
  rintro y (rfl | rfl | rfl | rfl)
  · exact ⟨_, _, hst, hcs.1⟩
  · exact ⟨_, _, h4, hcs.2.1⟩
  · exact ⟨_, _, hq, hcs.2.2.1⟩
  · exact ⟨_, _, hr, hcs.2.2.2⟩

theorem jRecAt_keeps_at {A : Addr → Prop} {σ σ' : State} {cls : ClassName} (hk : Keeps A σ σ')
    (ha : Away A σ []) {S : Schema} {y : Addr} {vals : List EquivLean.Cobol.Rec.FVal} (hy : ¬ A y)
    (h : JRecAt S cls σ (.ref y) vals) : JRecAt S cls σ' (.ref y) vals := by
  obtain ⟨x, fs, e, hx, hf⟩ := h
  cases e
  exact ⟨_, fs, rfl, heap_keeps hk hx hy, forall2_imp (fun _ _ h => jFieldAt_keeps hk ha h) hf⟩

/-- A record object that is itself unchanged (its strings are never written). -/
theorem jRecAt_same {A : Addr → Prop} {σ σ' : State} {cls : ClassName} (hk : Keeps A σ σ')
    (ha : Away A σ []) {S : Schema} {y : Addr} {vals : List EquivLean.Cobol.Rec.FVal}
    (hy : σ'.heap y = σ.heap y) (h : JRecAt S cls σ (.ref y) vals) : JRecAt S cls σ' (.ref y) vals := by
  obtain ⟨x, fs, e, hx, hf⟩ := h
  cases e
  exact ⟨_, fs, rfl, by rw [hy, hx], forall2_imp (fun _ _ h => jFieldAt_keeps hk ha h) hf⟩

theorem ne_of_cls {σ : State} {x y : Addr} {c c' : ClassName} {fs fs' : List (FieldKey × Value)}
    (hx : σ.heap x = some (.plain c fs)) (hy : σ.heap y = some (.plain c' fs')) (hc : c ≠ c') : x ≠ y := by
  rintro rfl
  rw [hx] at hy
  cases hy
  exact hc rfl

theorem get_set_eq (fs : List (FieldKey × Value)) (k : FieldKey) (v : Value) :
    Fields.get (Fields.set fs k v) k = some v := by
  rw [Fields.get_set, if_pos rfl]

theorem get_set_ne {fs : List (FieldKey × Value)} {k k' : FieldKey} (v : Value) (h : k' ≠ k) :
    Fields.get (Fields.set fs k v) k' = Fields.get fs k' := by
  rw [Fields.get_set, if_neg h]

theorem add_eq_false {a n : Nat} (k : Nat) (h : a < n) : (n + k = a) = False := by
  apply propext; constructor
  · intro e; omega
  · intro e; exact e.elim

theorem eq_add_false {a n : Nat} (k : Nat) (h : a < n) : (a = n + k) = False := by
  apply propext; constructor
  · intro e; omega
  · intro e; exact e.elim

theorem eq_lt_false {a n : Nat} (h : a < n) : (a = n) = False :=
  eq_false (Nat.ne_of_lt h)

theorem lt_eq_false {a n : Nat} (h : a < n) : (n = a) = False :=
  eq_false (Nat.ne_of_gt h)

/-- A state that only allocated: the objects below `σ0.next` are unchanged. -/
theorem keeps_of_heap {A : Addr → Prop} {σ0 σ1 : State} (hn : σ0.next ≤ σ1.next)
    (h : ∀ x, x < σ0.next → σ1.heap x = σ0.heap x) : Keeps A σ0 σ1 :=
  ⟨hn, fun x hx _ => h x hx⟩

theorem gr_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun x hx => State.heap_alloc_of_lt hx o⟩

theorem gr_trans {σ1 σ2 σ3 : State} (h1 : Grows σ1 σ2) (h2 : Grows σ2 σ3) : Grows σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun x hx => by rw [h2.2 x (Nat.lt_of_lt_of_le hx h1.1), h1.2 x hx]⟩

/-- Two allocations, by a callee contract (`Grows` unfolded). -/
theorem heap_of_alloc2 {σ0 σ1 : State} {o o' : Obj}
    (hh : ∀ x, x < σ0.next + 1 + 1 →
      σ1.heap x = if x = σ0.next + 1 then some o' else if x = σ0.next then some o else σ0.heap x) :
    ∀ x, x < σ0.next → σ1.heap x = σ0.heap x := fun x hx => by
  have h1 : x ≠ σ0.next + 1 := fun e => by
    rw [e] at hx; exact Nat.lt_irrefl _ (Nat.lt_trans (Nat.lt_succ_self _) hx)
  rw [hh x (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hx)), if_neg h1, if_neg (Nat.ne_of_lt hx)]

/-- One allocation, by a callee contract (`Grows` unfolded). -/
theorem heap_of_alloc1 {σ0 σ1 : State} {o : Obj}
    (hh : ∀ x, x < σ0.next + 1 → σ1.heap x = if x = σ0.next then some o else σ0.heap x) :
    ∀ x, x < σ0.next → σ1.heap x = σ0.heap x := fun x hx => by
  rw [hh x (Nat.lt_succ_of_lt hx), if_neg (Nat.ne_of_lt hx)]

/-- Heap reads in a final state: `hsimp [facts]` (address comparisons by `omega` from `x < σ0.next` facts). -/
syntax "hsimp" : tactic
syntax "hsimp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| hsimp) =>
    `(tactic| simp (disch := hdisch) only
      [State.heap_setObj_of_lt, State.heap_alloc_of_lt, State.heap_alloc, State.next_setObj, State.next_alloc,
        add_eq_false, eq_add_false, eq_lt_false, lt_eq_false, Fields.get_set, eq_self_iff_true, if_true, if_false, ite_true,
        ite_false,
        Nat.add_right_cancel_iff, Nat.succ_ne_self])
  | `(tactic| hsimp [$ts,*]) =>
    `(tactic| simp (disch := hdisch) only
      [State.heap_setObj_of_lt, State.heap_alloc_of_lt, State.heap_alloc, State.next_setObj, State.next_alloc,
        add_eq_false, eq_add_false, eq_lt_false, lt_eq_false, Fields.get_set, eq_self_iff_true, if_true, if_false, ite_true,
        ite_false,
        Nat.add_right_cancel_iff, Nat.succ_ne_self, $ts,*])

theorem forall2_imp_mem {α β : Type} {R R' : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, (∀ a ∈ l1, ∀ b, R a b → R' a b) → Forall2 R l1 l2 → Forall2 R' l1 l2
  | [], [], _, .nil => .nil
  | _ :: _, _ :: _, h, .cons h1 hs =>
    .cons (h _ (List.mem_cons_self ..) _ h1) (forall2_imp_mem (fun a ha => h a (List.mem_cons_of_mem _ ha)) hs)

/-! ## The ACCTFILE object -/

theorem acctFile_fin {σ0 σ' : State} {st o4 q fdr : Addr} {fsS fs4 fsq fsr fs4' : List (FieldKey × Value)}
    {f f' : Model.FileM}
    (hf : FileAtM "Cbstm03b$AcctFile" "Cbstm03b$FdAcctfileRec" Model.FdAcctfileRec σ0 (.ref o4) f)
    (hnr : NotRecOf σ0 "Cbstm03b$AcctFile" (.ref fdr) (.ref o4))
    (hst : σ0.heap st = some (.plain "Cbstm03b$State" fsS))
    (h4 : σ0.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4))
    (hq : σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq))
    (hr : σ0.heap fdr = some (.plain "Cbstm03b$FdAcctfileRec" fsr))
    (hk : Keeps (AccA st o4 q fdr) σ0 σ') (h4' : σ'.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4'))
    (hrecs : Fields.get fs4' ("Cbstm03b$AcctFile", "recs") = Fields.get fs4 ("Cbstm03b$AcctFile", "recs"))
    (hopen : Fields.get fs4' ("Cbstm03b$AcctFile", "open") = some (.ofBool f'.isOpen))
    (hpos : Fields.get fs4' ("Cbstm03b$AcctFile", "pos") = some (.int (BitVec.ofNat 32 f'.pos)))
    (heof : Fields.get fs4' ("Cbstm03b$AcctFile", "eof") = some (.ofBool f'.eof))
    (hr' : f'.recs = f.recs) (hp : f'.pos < 2147483648) :
    FileAtM "Cbstm03b$AcctFile" "Cbstm03b$FdAcctfileRec" Model.FdAcctfileRec σ' (.ref o4) f' := by
  have ha : Away (AccA st o4 q fdr) σ0 [] := accA_away hst h4 hq hr [] (by simp)
  obtain ⟨o, fs, l, et, xs, e, ho, -, h2, hl, hlen, hrs, -, -, -⟩ := hf
  cases e
  rw [h4] at ho
  cases ho
  refine ⟨o4, fs4', l, et, xs, rfl, h4', hopen, by rw [hrecs]; exact h2, ?_, hlen, ?_, hp, hpos, heof⟩
  · exact heap_keeps hk hl (not_A_of_heap ha hl (fun _ _ e => by cases e))
  · rw [hr']
    refine forall2_imp_mem (fun x hx vals h => ?_) hrs
    obtain ⟨y, fsy, rfl, hy, -⟩ := id h
    refine jRecAt_keeps_at hk ha ?_ h
    rintro (e | e | e | e) <;> subst e
    · rw [hst] at hy; simp at hy
    · rw [h4] at hy; simp at hy
    · rw [hq] at hy; simp at hy
    · exact hnr o4 fs4 l et xs rfl h4 h2 hl hx

/-! ## The State object -/

/-- The classes of the other three files' objects. -/
def restCls : List ClassName :=
  ["Cbstm03b$TrnxFile", "Cbstm03b$FdTrnxfileRec", "Cbstm03b$XrefFile", "Cbstm03b$FdXreffileRec",
    "Cbstm03b$CustFile", "Cbstm03b$FdCustfileRec"]

theorem state_fin {σ0 σ' : State} {st o4 q fdr : Addr} {s : Model.StM}
    {fs fs' fs4 fsq fsr : List (FieldKey × Value)} {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal}
    {c' : List Nat} (hs : StateAtM σ0 st s) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (h4 : σ0.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4))
    (hq : σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq))
    (hr : σ0.heap fdr = some (.plain "Cbstm03b$FdAcctfileRec" fsr))
    (hk : Keeps (AccA st o4 q fdr) σ0 σ') (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (hrest : ∀ k, k ≠ "acctFile" → k ≠ "fdAcctfileRec" → k ≠ "acctfileStatus" →
      Fields.get fs' ("Cbstm03b$State", k) = Fields.get fs ("Cbstm03b$State", k))
    (hA : PartA σ' fs' f' r' c') :
    StateAtM σ' st { s with acct := f', acctRec := r', acctSt := c' } := by
  obtain ⟨fs0, hst0, pT, pX, pC, -⟩ := stateAtM_iff.1 hs
  rw [hst] at hst0
  cases hst0
  have ha : Away (AccA st o4 q fdr) σ0 restCls := accA_away hst h4 hq hr _ (by decide)
  refine stateAtM_iff.2 ⟨fs', hst', ?_, ?_, ?_, hA⟩
  · exact (pT.keeps hk (ha.mono (by decide))).fields (hrest _ (by decide) (by decide) (by decide))
      (hrest _ (by decide) (by decide) (by decide)) (hrest _ (by decide) (by decide) (by decide))
  · exact (pX.keeps hk (ha.mono (by decide))).fields (hrest _ (by decide) (by decide) (by decide))
      (hrest _ (by decide) (by decide) (by decide)) (hrest _ (by decide) (by decide) (by decide))
  · exact (pC.keeps hk (ha.mono (by decide))).fields (hrest _ (by decide) (by decide) (by decide))
      (hrest _ (by decide) (by decide) (by decide)) (hrest _ (by decide) (by decide) (by decide))

/-! ## Separation -/

theorem sepM_fin {σ0 σ' : State} {st o4 q fdr fdr' : Addr} {s : Model.StM}
    {fs fs' fs4 fs4' fsq fsr : List (FieldKey × Value)} (hs : StateAtM σ0 st s) (hsep : SepM σ0 st)
    (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (h4 : σ0.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4))
    (hq : σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq))
    (hr : σ0.heap fdr = some (.plain "Cbstm03b$FdAcctfileRec" fsr))
    (g4 : Fields.get fs ("Cbstm03b$State", "acctFile") = some (.ref o4))
    (gr : Fields.get fs ("Cbstm03b$State", "fdAcctfileRec") = some (.ref fdr))
    (hk : Keeps (AccA st o4 q fdr) σ0 σ') (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (hrest : ∀ k, k ≠ "acctFile" → k ≠ "fdAcctfileRec" → k ≠ "acctfileStatus" →
      Fields.get fs' ("Cbstm03b$State", k) = Fields.get fs ("Cbstm03b$State", k))
    (g4' : Fields.get fs' ("Cbstm03b$State", "acctFile") = some (.ref o4))
    (gr' : Fields.get fs' ("Cbstm03b$State", "fdAcctfileRec") = some (.ref fdr'))
    (hfdr : fdr' = fdr ∨ σ0.next ≤ fdr')
    (h4' : σ'.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4'))
    (hrecs : Fields.get fs4' ("Cbstm03b$AcctFile", "recs") = Fields.get fs4 ("Cbstm03b$AcctFile", "recs")) :
    SepM σ' st := by
  obtain ⟨fs0, hst0, -, -, ⟨⟨y3, g3, m3⟩, -, -⟩, ⟨⟨y4, g4a, m4⟩, -, -⟩⟩ := stateAtM_iff.1 hs
  rw [hst] at hst0
  cases hst0
  rw [g4] at g4a
  cases g4a
  obtain ⟨fs0, hst0, c1, c2⟩ := hsep
  rw [hst] at hst0
  cases hst0
  have ha : Away (AccA st o4 q fdr) σ0 restCls := accA_away hst h4 hq hr _ (by decide)
  have ha0 : Away (AccA st o4 q fdr) σ0 [] := accA_away hst h4 hq hr [] (by simp)
  refine ⟨fs', hst', fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · rw [hrest _ (by decide) (by decide) (by decide)] at hx hy
    rw [g3] at hy
    cases hy
    exact notRecOf_keeps hk (ha.mono (by decide)) m3 (c1 x y3 hx g3)
  · rw [gr'] at hx
    rw [g4'] at hy
    cases hx
    cases hy
    obtain ⟨o, fsa, l, et, xs, e, ho, -, h2, hl, -, hrs, -⟩ := m4
    cases e
    rw [h4] at ho
    cases ho
    intro o' fs'' l' et' xs' e ho' hl' hlh'
    cases e
    rw [h4'] at ho'
    cases ho'
    rw [hrecs, h2] at hl'
    cases hl'
    rw [heap_keeps hk hl (not_A_of_heap ha0 hl (fun _ _ e => by cases e))] at hlh'
    cases hlh'
    rcases hfdr with e | hnew
    · subst e
      exact c2 (.ref fdr') (.ref o4) gr g4 o4 fs4 l et xs rfl h4 h2 hl
    · intro hm
      have key : ∀ (ys : List Value) (rs : List (List EquivLean.Cobol.Rec.FVal)),
          Forall2 (fun x vals => JRecAt Model.FdAcctfileRec "Cbstm03b$FdAcctfileRec" σ0 x vals) ys rs →
          Value.ref fdr' ∉ ys := by
        intro ys rs h
        induction h with
        | nil => exact List.not_mem_nil
        | cons h1 _ ih =>
          intro hm'
          rcases List.mem_cons.1 hm' with e | hm''
          · obtain ⟨y, fsy, e', hy, -⟩ := h1
            rw [← e] at e'
            cases e'
            exact absurd (State.lt_next_of_heap hy) (Nat.not_lt.2 hnew)
          · exact ih hm''
      exact key xs _ hrs hm

/-! ## The area -/

theorem area_fin {σ0 σ' : State} {q : Addr} {A : Addr → Prop} {fsq fsq' : List (FieldKey × Value)}
    {dd op key rc' fldt' : List UInt8} {kl : Int} {sdd sop skey src' sfl' : Value}
    (hk : Keeps A σ0 σ') (ha : Away A σ0 [])
    (hq' : σ'.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq'))
    (g1 : Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bDd") = some sdd) (j1 : JStrAt σ0 sdd (cp037Str dd))
    (g2 : Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bOper") = some sop) (j2 : JStrAt σ0 sop (cp037Str op))
    (g4 : Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bKey") = some skey) (j4 : JStrAt σ0 skey (cp037Str key))
    (g5 : Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bKeyLn") = some (.long (BitVec.ofInt 64 kl)))
    (e1 : Fields.get fsq' ("Cbstm03b$LkM03bArea", "lkM03bDd") = Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bDd"))
    (e2 : Fields.get fsq' ("Cbstm03b$LkM03bArea", "lkM03bOper") =
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bOper"))
    (e4 : Fields.get fsq' ("Cbstm03b$LkM03bArea", "lkM03bKey") = Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bKey"))
    (e5 : Fields.get fsq' ("Cbstm03b$LkM03bArea", "lkM03bKeyLn") =
      Fields.get fsq ("Cbstm03b$LkM03bArea", "lkM03bKeyLn"))
    (g3' : Fields.get fsq' ("Cbstm03b$LkM03bArea", "lkM03bRc") = some src') (j3' : JStrAt σ' src' (cp037Str rc'))
    (g6' : Fields.get fsq' ("Cbstm03b$LkM03bArea", "lkM03bFldt") = some sfl') (j6' : JStrAt σ' sfl' (cp037Str fldt')) :
    JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ' (.ref q)
      [.str dd, .str op, .str rc', .str key, .num kl, .str fldt'] :=
  areaAt_mk hq' (by rw [e1, g1]) (jstrAt_keeps hk ha j1) (by rw [e2, g2]) (jstrAt_keeps hk ha j2) g3' j3'
    (by rw [e4, g4]) (jstrAt_keeps hk ha j4) (by rw [e5, g5]) g6' j6'

/-! ## Texts of the literals -/

theorem lit_texts : JStr.ofString "00" = stChars 0 ∧ JStr.ofString "41" = stChars 41 ∧
    JStr.ofString "42" = stChars 42 ∧ JStr.ofString "47" = stChars 47 ∧ JStr.ofString "23" = stChars 23 := by
  decide +kernel

end EquivLean.Modernize.Cbstm03b.Java.AcctP

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

/-! ## The model, for ACCTFILE -/

theorem call_acct {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    (hdd : Model.aDd a = ddAcct) :
    Model.call oeM s a =
      ({ s with
          acct := (Model.keyStep (oeM 4) Model.FdAcctfileRec
            (fun rec => rec.set 0 (.num (Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat)))
            (fun x => Model.numOf (x.getD 0 default) == Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat)
            (Model.aOp a) s.acct s.acctRec s.acctSt a).1,
          acctRec := (Model.keyStep (oeM 4) Model.FdAcctfileRec
            (fun rec => rec.set 0 (.num (Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat)))
            (fun x => Model.numOf (x.getD 0 default) == Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat)
            (Model.aOp a) s.acct s.acctRec s.acctSt a).2.1,
          acctSt := (Model.keyStep (oeM 4) Model.FdAcctfileRec
            (fun rec => rec.set 0 (.num (Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat)))
            (fun x => Model.numOf (x.getD 0 default) == Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat)
            (Model.aOp a) s.acct s.acctRec s.acctSt a).2.2.1 },
        (Model.keyStep (oeM 4) Model.FdAcctfileRec
            (fun rec => rec.set 0 (.num (Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat)))
            (fun x => Model.numOf (x.getD 0 default) == Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat)
            (Model.aOp a) s.acct s.acctRec s.acctSt a).2.2.2) := by
  unfold Model.call
  simp only [hdd]
  rw [if_neg (show ddAcct ≠ ddTrnx by decide), if_neg (show ddAcct ≠ ddXref by decide),
    if_neg (show ddAcct ≠ ddCust by decide), if_pos trivial]

theorem call_close_open {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    (hdd : Model.aDd a = ddAcct) (hop : Model.aOp a = opClose) (ho : s.acct.isOpen = true) :
    Model.call oeM s a =
      ({ s with acct := { s.acct with isOpen := false }, acctRec := s.acctRec, acctSt := Model.stCp 0 },
        Model.setRc a (stBytes 0)) := by
  rw [call_acct hdd, hop]
  simp [Model.keyStep, Model.closeM, ho, show opClose ≠ opOpen by decide, show opClose ≠ opReadK by decide]

theorem call_close_shut {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    (hdd : Model.aDd a = ddAcct) (hop : Model.aOp a = opClose) (ho : s.acct.isOpen = false) :
    Model.call oeM s a =
      ({ s with acct := s.acct, acctRec := s.acctRec, acctSt := Model.stCp 42 }, Model.setRc a (stBytes 42)) := by
  rw [call_acct hdd, hop]
  simp [Model.keyStep, Model.closeM, ho, show opClose ≠ opOpen by decide, show opClose ≠ opReadK by decide]

theorem call_open_open {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    (hdd : Model.aDd a = ddAcct) (hop : Model.aOp a = opOpen) (ho : s.acct.isOpen = true) :
    Model.call oeM s a =
      ({ s with acct := s.acct, acctRec := s.acctRec, acctSt := Model.stCp 41 }, Model.setRc a (stBytes 41)) := by
  rw [call_acct hdd, hop]
  simp [Model.keyStep, Model.openM, ho]

theorem call_open_err {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal} {c : Nat}
    (hdd : Model.aDd a = ddAcct) (hop : Model.aOp a = opOpen) (ho : s.acct.isOpen = false) (hc : oeM 4 = some c) :
    Model.call oeM s a =
      ({ s with acct := s.acct, acctRec := s.acctRec, acctSt := Model.stCp c }, Model.setRc a (stBytes c)) := by
  rw [call_acct hdd, hop]
  simp [Model.keyStep, Model.openM, ho, hc]

theorem call_open_ok {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    (hdd : Model.aDd a = ddAcct) (hop : Model.aOp a = opOpen) (ho : s.acct.isOpen = false) (hc : oeM 4 = none) :
    Model.call oeM s a =
      ({ s with
          acct := { s.acct with isOpen := true, pos := 0, eof := false }
          acctRec := s.acctRec
          acctSt := Model.stCp 0 }, Model.setRc a (stBytes 0)) := by
  rw [call_acct hdd, hop]
  simp [Model.keyStep, Model.openM, ho, hc]

theorem call_other {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    (hdd : Model.aDd a = ddAcct) (h1 : Model.aOp a ≠ opOpen) (h2 : Model.aOp a ≠ opReadK)
    (h3 : Model.aOp a ≠ opClose) :
    Model.call oeM s a =
      ({ s with acct := s.acct, acctRec := s.acctRec, acctSt := s.acctSt },
        Model.setRc a (s.acctSt.map ebcdicOfLatin1)) := by
  rw [call_acct hdd]
  simp [Model.keyStep, h1, h2, h3]

theorem call_key_shut {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}
    (hdd : Model.aDd a = ddAcct) (hop : Model.aOp a = opReadK) (ho : s.acct.isOpen = false) :
    Model.call oeM s a =
      ({ s with
          acct := s.acct
          acctRec := s.acctRec.set 0 (.num (Model.acctVal (Model.aKey a) (Model.aKeyLn a).toNat))
          acctSt := Model.stCp 47 }, Model.setRc a (stBytes 47)) := by
  rw [call_acct hdd, hop]
  simp [Model.keyStep, Model.keyReadM, ho, show opReadK ≠ opOpen by decide]

/-! ## Machine arithmetic of the key loop -/

theorem umod_eq_mod {w : Nat} (x y : BitVec w) : x.umod y = x % y := rfl

theorem jstep_bv (V d : Nat) (hV : V < 100000000000) (hd : d < 10) :
    BitVec.srem (BitVec.ofNat 64 V * 10#64 + BitVec.ofNat 64 d) 100000000000#64 =
      BitVec.ofNat 64 ((V * 10 + d) % 100000000000) := by
  have e1 : (BitVec.ofNat 64 V * 10#64 + BitVec.ofNat 64 d).toNat = V * 10 + d := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [BitVec.toNat_ofNat]
    omega
  have hm : (BitVec.ofNat 64 V * 10#64 + BitVec.ofNat 64 d).msb = false := by
    rw [BitVec.msb_eq_decide, e1]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  have hm2 : (100000000000#64).msb = false := by decide
  simp only [BitVec.srem, hm, hm2, umod_eq_mod]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, e1]
  simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem toLong_zero : JInt.toLong 0#32 = BitVec.ofNat 64 0 := by decide

theorem toLong_digit (c : JChar) (h1 : 48 ≤ c.toNat) (h2 : c.toNat ≤ 57) :
    JInt.toLong (BitVec.setWidth 32 c - 48#32) = BitVec.ofNat 64 (c.toNat - 48) := by
  have e : (BitVec.setWidth 32 c - 48#32).toNat = c.toNat - 48 := by
    rw [BitVec.toNat_sub, BitVec.toNat_setWidth]
    simp only [BitVec.toNat_ofNat]
    have := c.isLt
    omega
  have hm : (BitVec.setWidth 32 c - 48#32).msb = false := by
    rw [BitVec.msb_eq_decide, e]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  unfold JInt.toLong
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp only [hm, e, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.false_eq_true, if_false]
  omega

theorem ofNat_succ32 (i : Nat) : BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem toInt32_ofNat {n : Nat} (h : n < 2147483648) : (BitVec.ofNat 32 n).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  have : n % 2 ^ 32 = n := Nat.mod_eq_of_lt (by omega)
  rw [this]
  split <;> omega

theorem jdig_lt (c : JChar) : jdig c < 10 := by
  unfold jdig; split <;> omega

theorem jdig_low {c : JChar} (h : c.toNat < 48) : jdig c = 0 := by
  unfold jdig; rw [if_neg (by omega)]

theorem jdig_high {c : JChar} (h : 57 < c.toNat) : jdig c = 0 := by
  unfold jdig; rw [if_neg (by omega)]

theorem jdig_mid {c : JChar} (h1 : ¬ c.toNat < 48) (h2 : ¬ 57 < c.toNat) : jdig c = c.toNat - 48 := by
  unfold jdig; rw [if_pos (by omega)]

/-- One iteration of the key loop on the machine. -/
theorem jkey_succ_bv (kt : JStr) (i : Nat) (c : JChar) (hc : kt[i]? = some c) (X : BitVec 64)
    (hX : X = BitVec.ofNat 64 (jdig c)) :
    BitVec.srem (BitVec.ofNat 64 (jkey (kt.take i)) * 10#64 + X) 100000000000#64 =
      BitVec.ofNat 64 (jkey (kt.take (i + 1))) := by
  rw [hX, jstep_bv _ _ (jkey_lt _) (jdig_lt c), List.take_succ, hc, Option.toList_some, jkey_append]

end EquivLean.Modernize.Cbstm03b.Java.AcctP

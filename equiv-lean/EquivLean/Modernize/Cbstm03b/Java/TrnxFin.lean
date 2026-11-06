import EquivLean.Modernize.Cbstm03b.Java.Base

/-!
# CBSTM03B → Java: the end of a file procedure's path

What a path of a file procedure leaves in the heap, against the model's call: the State object's fields and the
area's fields that the path wrote, the file object's fields, and the objects it allocated; every other object of
the entry heap is unchanged (`Keeps`, the updated objects being the file, the State object and the area).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

theorem get_set_other {fs : List (FieldKey × Value)} {k k' : FieldKey} {v : Value} (h : k' ≠ k) :
    Fields.get (Fields.set fs k v) k' = Fields.get fs k' := by
  rw [Fields.get_set, if_neg h]

theorem get_set_same {fs : List (FieldKey × Value)} {k : FieldKey} {v : Value} :
    Fields.get (Fields.set fs k v) k = some v := by
  rw [Fields.get_set, if_pos rfl]

/-! ## The area -/

/-- The area after a path that wrote its return code (the other fields kept). -/
theorem area_rc {σ0 σ' : State} {q : Addr} {a : List EquivLean.Cobol.Rec.FVal}
    {fsq fsq' : List (FieldKey × Value)} {A : Addr → Prop} {cs : List ClassName} {v : Value} {bs : List UInt8}
    (hA : JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a) (hVa : Model.LkM03bArea.Valid a)
    (hq : σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq)) (hk : Keeps A σ0 σ') (ha : Away A σ0 cs)
    (hq' : σ'.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq'))
    (hkeep : ∀ k, k ≠ ("Cbstm03b$LkM03bArea", "lkM03bRc") → Fields.get fsq' k = Fields.get fsq k)
    (hrc : Fields.get fsq' ("Cbstm03b$LkM03bArea", "lkM03bRc") = some v) (hv : JStrAt σ' v (cp037Str bs)) :
    JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ' (.ref q) (Model.setRc a bs) := by
  obtain ⟨q', fs0, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq0, rfl, -, -, -, -, -, -, -,
    gdd, jdd, gop, jop, grc, jrc, gkey, jkey, gkl, gfl, jfl⟩ := areaAt_of hA hVa
  cases hqq
  rw [hq] at hq0
  cases hq0
  exact areaAt_mk hq' (by rw [hkeep _ (by decide), gdd]) (jstrAt_keeps hk ha jdd)
    (by rw [hkeep _ (by decide), gop]) (jstrAt_keeps hk ha jop) hrc hv
    (by rw [hkeep _ (by decide), gkey]) (jstrAt_keeps hk ha jkey) (by rw [hkeep _ (by decide), gkl])
    (by rw [hkeep _ (by decide), gfl]) (jstrAt_keeps hk ha jfl)

/-- The area after a path that read a record into its buffer and wrote its return code. -/
theorem area_rc_fldt {σ0 σ' : State} {q : Addr} {a : List EquivLean.Cobol.Rec.FVal}
    {fsq fsq' : List (FieldKey × Value)} {A : Addr → Prop} {cs : List ClassName} {v w : Value}
    {bs rb : List UInt8}
    (hA : JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a) (hVa : Model.LkM03bArea.Valid a)
    (hq : σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq)) (hk : Keeps A σ0 σ') (ha : Away A σ0 cs)
    (hq' : σ'.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq'))
    (hkeep : ∀ k, k ≠ ("Cbstm03b$LkM03bArea", "lkM03bRc") → k ≠ ("Cbstm03b$LkM03bArea", "lkM03bFldt") →
      Fields.get fsq' k = Fields.get fsq k)
    (hrc : Fields.get fsq' ("Cbstm03b$LkM03bArea", "lkM03bRc") = some v) (hv : JStrAt σ' v (cp037Str bs))
    (hfl : Fields.get fsq' ("Cbstm03b$LkM03bArea", "lkM03bFldt") = some w)
    (hw : JStrAt σ' w (cp037Str (intoBuf rb))) :
    JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ' (.ref q) (Model.setFldt (Model.setRc a bs) rb) := by
  obtain ⟨q', fs0, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq0, rfl, -, -, -, -, -, -, -,
    gdd, jdd, gop, jop, grc, jrc, gkey, jkey, gkl, gfl, jfl⟩ := areaAt_of hA hVa
  cases hqq
  rw [hq] at hq0
  cases hq0
  exact areaAt_mk hq' (by rw [hkeep _ (by decide) (by decide), gdd]) (jstrAt_keeps hk ha jdd)
    (by rw [hkeep _ (by decide) (by decide), gop]) (jstrAt_keeps hk ha jop) hrc hv
    (by rw [hkeep _ (by decide) (by decide), gkey]) (jstrAt_keeps hk ha jkey)
    (by rw [hkeep _ (by decide) (by decide), gkl]) hfl hw

/-! ## The TRNXFILE part of the state -/

/-- The file object at `o1` after a path that kept its records array and wrote its flags. -/
theorem fileAtM_upd {σ0 σ' : State} {o1 : Addr} {cls rcls : ClassName} {S : Schema} {f : Model.FileM}
    {fs1 fs1' : List (FieldKey × Value)} {A : Addr → Prop} {b' e' : Bool} {p' : Nat}
    (hf : FileAtM cls rcls S σ0 (.ref o1) f) (ho1 : σ0.heap o1 = some (.plain cls fs1)) (hk : Keeps A σ0 σ')
    (ha : Away A σ0 [rcls]) (ho1' : σ'.heap o1 = some (.plain cls fs1'))
    (hrecs : Fields.get fs1' (cls, "recs") = Fields.get fs1 (cls, "recs"))
    (hopen : Fields.get fs1' (cls, "open") = some (.ofBool b'))
    (hpos : Fields.get fs1' (cls, "pos") = some (.int (BitVec.ofNat 32 p'))) (hp : p' < 2147483648)
    (heof : Fields.get fs1' (cls, "eof") = some (.ofBool e')) :
    FileAtM cls rcls S σ' (.ref o1) { f with isOpen := b', pos := p', eof := e' } := by
  obtain ⟨o, fs, l, et, xs, ho, hoo, -, hl, hlh, hlen, hr, -, -, -⟩ := hf
  cases ho
  rw [ho1] at hoo
  cases hoo
  exact ⟨o1, fs1', l, et, xs, rfl, ho1', hopen, by rw [hrecs, hl],
    heap_keeps hk hlh (not_A_of_heap ha hlh (fun _ _ e => by cases e)), hlen,
    forall2_imp (fun _ _ h => jRecAt_keeps hk ha h) hr, hp, hpos, heof⟩

/-- The classes of the parts of the state other than TRNXFILE's. -/
abbrev otherT : List ClassName := ["Cbstm03b$XrefFile", "Cbstm03b$FdXreffileRec", "Cbstm03b$CustFile",
  "Cbstm03b$FdCustfileRec", "Cbstm03b$AcctFile", "Cbstm03b$FdAcctfileRec"]

/-- **The state after a TRNXFILE path**: the State object's other fields are kept, its TRNXFILE parts hold the
new values. -/
theorem finT {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs fs' : List (FieldKey × Value)} {A : Addr → Prop}
    {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal} {c' : List Nat}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps A σ0 σ') (ha : Away A σ0 otherT)
    (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (hkeep : ∀ k, k ≠ ("Cbstm03b$State", "trnxfileStatus") → k ≠ ("Cbstm03b$State", "fdTrnxfileRec") →
      Fields.get fs' k = Fields.get fs k)
    (hpart : PartT σ' fs' f' r' c') :
    StateAtM σ' st { s with trnx := f', trnxRec := r', trnxSt := c' } ∧ SepM σ' st := by
  obtain ⟨fs0, hst0, -, pX, pC, pA⟩ := stateAtM_iff.1 hs
  rw [hst] at hst0
  cases hst0
  refine ⟨stateAtM_iff.2 ⟨fs', hst', hpart, ?_, ?_, ?_⟩, ?_⟩
  · exact (pX.fields (hkeep _ (by decide) (by decide)) (hkeep _ (by decide) (by decide))
      (hkeep _ (by decide) (by decide))).keeps hk (ha.mono (by decide))
  · exact (pC.fields (hkeep _ (by decide) (by decide)) (hkeep _ (by decide) (by decide))
      (hkeep _ (by decide) (by decide))).keeps hk (ha.mono (by decide))
  · exact (pA.fields (hkeep _ (by decide) (by decide)) (hkeep _ (by decide) (by decide))
      (hkeep _ (by decide) (by decide))).keeps hk (ha.mono (by decide))
  · exact sepM_keeps hs hsep hk (ha.mono (by decide)) hst'
      (fun fs0 h0 => by
        rw [hst] at h0
        cases h0
        exact ⟨hkeep _ (by decide) (by decide), hkeep _ (by decide) (by decide), hkeep _ (by decide) (by decide),
          hkeep _ (by decide) (by decide)⟩)

theorem finT_state {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs fs' : List (FieldKey × Value)} {A : Addr → Prop}
    {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal} {c' : List Nat}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps A σ0 σ') (ha : Away A σ0 otherT)
    (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (hkeep : ∀ k, k ≠ ("Cbstm03b$State", "trnxfileStatus") → k ≠ ("Cbstm03b$State", "fdTrnxfileRec") →
      Fields.get fs' k = Fields.get fs k)
    (hpart : PartT σ' fs' f' r' c') :
    StateAtM σ' st { s with trnx := f', trnxRec := r', trnxSt := c' } :=
  (finT hs hsep hst hk ha hst' hkeep hpart).1

theorem finT_sep {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs fs' : List (FieldKey × Value)} {A : Addr → Prop}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps A σ0 σ') (ha : Away A σ0 otherT)
    (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (hkeep : ∀ k, k ≠ ("Cbstm03b$State", "trnxfileStatus") → k ≠ ("Cbstm03b$State", "fdTrnxfileRec") →
      Fields.get fs' k = Fields.get fs k) :
    SepM σ' st :=
  sepM_keeps hs hsep hk (ha.mono (by decide)) hst'
    (fun fs0 h0 => by
      rw [hst] at h0
      cases h0
      exact ⟨hkeep _ (by decide) (by decide), hkeep _ (by decide) (by decide), hkeep _ (by decide) (by decide),
        hkeep _ (by decide) (by decide)⟩)

/-- The objects a TRNXFILE path may update: the State object, the area, the file (by class). -/
def ChgT (σ0 : State) (x : Addr) : Prop :=
  ∃ c fs, σ0.heap x = some (.plain c fs) ∧ c ∈ ["Cbstm03b$State", "Cbstm03b$LkM03bArea", "Cbstm03b$TrnxFile"]

theorem away_chgT (σ0 : State) : Away (ChgT σ0) σ0 (otherT ++ ["Cbstm03b$FdTrnxfileRec"]) := by
  rintro y ⟨c, fs, h, hc⟩
  have hd : ∀ c ∈ ["Cbstm03b$State", "Cbstm03b$LkM03bArea", "Cbstm03b$TrnxFile"],
      c ∉ otherT ++ ["Cbstm03b$FdTrnxfileRec"] := by decide
  exact ⟨c, fs, h, hd c hc⟩

theorem chgT_of {σ0 : State} {x : Addr} {c : ClassName} {fs : List (FieldKey × Value)}
    (h : σ0.heap x = some (.plain c fs))
    (hc : c ∈ ["Cbstm03b$State", "Cbstm03b$LkM03bArea", "Cbstm03b$TrnxFile"] := by decide) : ChgT σ0 x :=
  ⟨c, fs, h, hc⟩

theorem ne_of_cls {σ : State} {x y : Addr} {c d : ClassName} {fs gs : List (FieldKey × Value)}
    (hx : σ.heap x = some (.plain c fs)) (hy : σ.heap y = some (.plain d gs)) (h : c ≠ d) : x ≠ y := by
  intro e
  rw [e, hy] at hx
  injection hx with hx
  injection hx with hx
  exact h hx.symm

/-- `finT_state` and `finT_sep` with the new State field list as a witness. -/
theorem finT_ex {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs : List (FieldKey × Value)}
    {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal} {c' : List Nat}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps (ChgT σ0) σ0 σ')
    (h : ∃ fs', σ'.heap st = some (.plain "Cbstm03b$State" fs') ∧
      (∀ k, k ≠ ("Cbstm03b$State", "trnxfileStatus") → k ≠ ("Cbstm03b$State", "fdTrnxfileRec") →
        Fields.get fs' k = Fields.get fs k) ∧ PartT σ' fs' f' r' c') :
    StateAtM σ' st { s with trnx := f', trnxRec := r', trnxSt := c' } ∧ SepM σ' st := by
  obtain ⟨fs', h1, h2, h3⟩ := h
  exact finT hs hsep hst hk ((away_chgT σ0).mono (by decide)) h1 h2 h3

/-- A fact kept from the symbolic executor (it does not unfold it). -/
@[irreducible] def Kept (p : Prop) : Prop := p

theorem Kept.intro {p : Prop} (h : p) : Kept p := by unfold Kept; exact h
theorem Kept.elim {p : Prop} (h : Kept p) : p := by unfold Kept at h; exact h

/-- A file object the path did not write. -/
theorem fileAtM_same {σ0 σ' : State} {o1 : Addr} {cls rcls : ClassName} {S : Schema} {f : Model.FileM}
    {A : Addr → Prop} (hf : FileAtM cls rcls S σ0 (.ref o1) f) (hk : Keeps A σ0 σ') (ha : Away A σ0 [rcls])
    (ho : σ'.heap o1 = σ0.heap o1) : FileAtM cls rcls S σ' (.ref o1) f := by
  obtain ⟨o, fs, l, et, xs, hoo, ho1, h1, h2, hl, hlen, hr, hp, h3, h4⟩ := hf
  cases hoo
  exact ⟨o1, fs, l, et, xs, rfl, by rw [ho, ho1], h1, h2,
    heap_keeps hk hl (not_A_of_heap ha hl (fun _ _ e => by cases e)), hlen,
    forall2_imp (fun _ _ h => jRecAt_keeps hk ha h) hr, hp, h3, h4⟩

theorem st_lits : JStr.ofString "00" = stChars 0 ∧ JStr.ofString "41" = stChars 41 ∧
    JStr.ofString "47" = stChars 47 ∧ JStr.ofString "46" = stChars 46 ∧ JStr.ofString "10" = stChars 10 ∧
    JStr.ofString "42" = stChars 42 := by
  decide +kernel

theorem addr_lt_succ {a b : Addr} (h : a < b) : a < b + 1 := Nat.lt_succ_of_lt h
theorem addr_ne_of_lt {a b : Addr} (h : a < b) : b ≠ a := Nat.ne_of_gt h

macro "lt_close" : tactic => `(tactic| first | assumption | exact Nat.lt_succ_self _ | exact Nat.lt_succ_of_lt (Nat.lt_succ_self _) | (apply addr_lt_succ; assumption) | (apply addr_lt_succ; apply addr_lt_succ; assumption) | (apply addr_lt_succ; apply addr_lt_succ; apply addr_lt_succ; assumption) | (apply addr_lt_succ; apply addr_lt_succ; apply addr_lt_succ; apply addr_lt_succ; assumption) | (apply addr_lt_succ; apply addr_lt_succ; apply addr_lt_succ; apply addr_lt_succ; apply addr_lt_succ; assumption))

macro "ne_close" : tactic => `(tactic| first | assumption | (apply Ne.symm; assumption) | (apply addr_ne_of_lt; lt_close) | (apply Ne.symm; apply addr_ne_of_lt; lt_close))

macro "next_lt" : tactic => `(tactic| ((try simp only [State.next_alloc, State.next_setObj]) <;> first | lt_close | ne_close))

/-- Heap lookups in a state built from `σ0` by allocations and updates of existing objects. -/

theorem keeps_setObj' {A : Addr → Prop} {σ0 σ : State} {a : Addr} {o : Obj} (h : Keeps A σ0 σ) (ha : A a) :
    Keeps A σ0 (σ.setObj a o) := keeps_trans h (keeps_setObj o ha)
theorem keeps_alloc' {A : Addr → Prop} {σ0 σ : State} {o : Obj} (h : Keeps A σ0 σ) :
    Keeps A σ0 (σ.alloc o).2 := keeps_trans h (keeps_alloc A σ o)
theorem keeps_grows' {A : Addr → Prop} {σ0 σ σ' : State} (h : Keeps A σ0 σ) (hg : Grows σ σ') :
    Keeps A σ0 σ' := keeps_trans h (keeps_of_grows hg)


theorem keeps_of_agree {A : Addr → Prop} {σ0 σ : State} (h : Agree σ0 σ) (hle : σ0.next ≤ σ.next) :
    Keeps A σ0 σ := ⟨hle, fun y hy _ => h y hy⟩

/-- A callee's `Grows`, kept folded across the symbolic executor. -/
@[irreducible] def GrowsK (σ σ' : State) : Prop := Grows σ σ'

theorem growsK_elim {σ σ' : State} (h : GrowsK σ σ') : Grows σ σ' := by unfold GrowsK at h; exact h

/-- `Grows` for the executor: a folded copy, and the facts it unfolds to. -/
theorem grows_split (σ σ' : State) :
    Grows σ σ' ↔ GrowsK σ σ' ∧ σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → σ'.heap x = σ.heap x := by
  constructor
  · intro h; exact ⟨by unfold GrowsK; exact h, h.1, h.2⟩
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩

/-- The objects a path that keeps the file object may update: the State object and the area (by class). -/
def ChgS (σ0 : State) (x : Addr) : Prop :=
  ∃ c fs, σ0.heap x = some (.plain c fs) ∧ c ∈ ["Cbstm03b$State", "Cbstm03b$LkM03bArea"]

theorem away_chgS (σ0 : State) :
    Away (ChgS σ0) σ0 (otherT ++ ["Cbstm03b$TrnxFile", "Cbstm03b$FdTrnxfileRec"]) := by
  rintro y ⟨c, fs, h, hc⟩
  have hd : ∀ c ∈ ["Cbstm03b$State", "Cbstm03b$LkM03bArea"],
      c ∉ otherT ++ ["Cbstm03b$TrnxFile", "Cbstm03b$FdTrnxfileRec"] := by decide
  exact ⟨c, fs, h, hd c hc⟩

theorem chgS_of {σ0 : State} {x : Addr} {c : ClassName} {fs : List (FieldKey × Value)}
    (h : σ0.heap x = some (.plain c fs)) (hc : c ∈ ["Cbstm03b$State", "Cbstm03b$LkM03bArea"] := by decide) :
    ChgS σ0 x :=
  ⟨c, fs, h, hc⟩

theorem finS_ex {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs : List (FieldKey × Value)}
    {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal} {c' : List Nat}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps (ChgS σ0) σ0 σ')
    (h : ∃ fs', σ'.heap st = some (.plain "Cbstm03b$State" fs') ∧
      (∀ k, k ≠ ("Cbstm03b$State", "trnxfileStatus") → k ≠ ("Cbstm03b$State", "fdTrnxfileRec") →
        Fields.get fs' k = Fields.get fs k) ∧ PartT σ' fs' f' r' c') :
    StateAtM σ' st { s with trnx := f', trnxRec := r', trnxSt := c' } ∧ SepM σ' st := by
  obtain ⟨fs', h1, h2, h3⟩ := h
  exact finT hs hsep hst hk ((away_chgS σ0).mono (by decide)) h1 h2 h3


theorem keeps_setObj_fresh {A : Addr → Prop} {σ0 σ : State} {a : Addr} {o : Obj} (h : Keeps A σ0 σ)
    (ha : σ0.next ≤ a) : Keeps A σ0 (σ.setObj a o) := by
  refine ⟨by rw [State.next_setObj]; exact h.1, fun y hy hA => ?_⟩
  have hne : y ≠ a := fun e => absurd (show a < σ0.next by rw [← e]; exact hy) (Nat.not_lt.2 ha)
  rw [State.heap_setObj, if_neg hne, h.2 y hy hA]

macro "keepsT_tac" : tactic => `(tactic| repeat (first | exact keeps_refl _ _ | (refine keeps_setObj' ?_ (chgT_of (by assumption))) | (refine keeps_setObj_fresh ?_ (by jdisch)) | (refine keeps_alloc' ?_) | (refine keeps_grows' ?_ (growsK_elim (by assumption)))))

macro "keepsS_tac" : tactic => `(tactic| repeat (first | exact keeps_refl _ _ | (refine keeps_setObj' ?_ (chgS_of (by assumption))) | (refine keeps_alloc' ?_) | (refine keeps_grows' ?_ (growsK_elim (by assumption)))))

/-- Heap lookups in a state built from the entry state by allocations, updates and callees. -/
macro "hsimp" : tactic => `(tactic| simp (disch := jdisch) only [State.heap_setObj_of_lt, State.heap_alloc, State.next_alloc, State.next_setObj, ↓reduceIte, ite_nat_ne, eq_self_iff_true, if_true])

theorem fileAtM_keeps' {A : Addr → Prop} {σ σ' : State} {cls rcls : ClassName} {S : Schema} {v : Value}
    {f : Model.FileM} (h : FileAtM cls rcls S σ v f) (hk : Keeps A σ σ') (ha : Away A σ [cls, rcls]) :
    FileAtM cls rcls S σ' v f := fileAtM_keeps hk ha h

theorem jRecAt_keeps' {A : Addr → Prop} {σ σ' : State} {cls : ClassName} {S : Schema} {v : Value}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecAt S cls σ v vals) (hk : Keeps A σ σ') (ha : Away A σ [cls]) :
    JRecAt S cls σ' v vals := jRecAt_keeps hk ha h

theorem fileAtM_upd' {σ0 σ' : State} {o1 : Addr} {cls rcls : ClassName} {S : Schema} {f : Model.FileM}
    {fs1 fs1' : List (FieldKey × Value)} {A : Addr → Prop} {b' e' : Bool} {p' : Nat}
    (hf : FileAtM cls rcls S σ0 (.ref o1) f) (ho1 : σ0.heap o1 = some (.plain cls fs1)) (hk : Keeps A σ0 σ')
    (ha : Away A σ0 [rcls]) (ho1' : σ'.heap o1 = some (.plain cls fs1'))
    (hrecs : Fields.get fs1' (cls, "recs") = Fields.get fs1 (cls, "recs"))
    (hopen : Fields.get fs1' (cls, "open") = some (.ofBool b'))
    (hpos : Fields.get fs1' (cls, "pos") = some (.int (BitVec.ofNat 32 p'))) (hp : p' < 2147483648)
    (heof : Fields.get fs1' (cls, "eof") = some (.ofBool e')) :
    FileAtM cls rcls S σ' (.ref o1) { f with isOpen := b', pos := p', eof := e' } :=
  fileAtM_upd hf ho1 hk ha ho1' hrecs hopen hpos hp heof

/-- The flags of a file object, from `FileAtM`. -/
theorem fileAtM_flags {σ : State} {o1 : Addr} {cls rcls : ClassName} {S : Schema} {f : Model.FileM}
    {fs1 : List (FieldKey × Value)} (hf : FileAtM cls rcls S σ (.ref o1) f)
    (ho1 : σ.heap o1 = some (.plain cls fs1)) :
    Fields.get fs1 (cls, "open") = some (.ofBool f.isOpen) ∧
      Fields.get fs1 (cls, "pos") = some (.int (BitVec.ofNat 32 f.pos)) ∧ f.pos < 2147483648 ∧
      Fields.get fs1 (cls, "eof") = some (.ofBool f.eof) := by
  obtain ⟨o, fs, l, et, xs, hoo, hoo', h1, -, -, -, -, hp, h3, h4⟩ := hf
  cases hoo
  rw [ho1] at hoo'
  cases hoo'
  exact ⟨h1, h3, hp, h4⟩

macro "status_close" : tactic => `(tactic| first | (simp only [st_lits]) | assumption | rfl)

macro "closeS_state" : tactic => `(tactic| (refine (finS_ex (by assumption) (by assumption) (by assumption) (by keepsS_tac) ?_).1; hsimp; refine ⟨_, rfl, fun k h1 h2 => get_set_other h1, ⟨_, (get_set_other (by decide)).trans (by assumption), fileAtM_keeps' (by assumption) (by keepsS_tac) ((away_chgS _).mono (by decide))⟩, ⟨_, (get_set_other (by decide)).trans (by assumption), jRecAt_keeps' (by assumption) (by keepsS_tac) ((away_chgS _).mono (by decide))⟩, ⟨_, get_set_same, _, rfl, ?_⟩⟩; rw [status_text]; hsimp; status_close))

macro "closeS_sep" : tactic => `(tactic| exact finT_sep (by assumption) (by assumption) (by assumption) (by keepsS_tac) ((away_chgS _).mono (by decide)) (by hsimp; try rfl) (fun k h1 h2 => by simp only [Fields.get_set, if_neg h1, if_neg h2]))

macro "closeS_area" : tactic => `(tactic| (refine area_rc (by assumption) (by assumption) (by assumption) (by keepsS_tac) (away_chgS _) (by hsimp; try rfl) (fun k h => get_set_other h) get_set_same ⟨_, rfl, ?_⟩; rw [stBytes_text]; hsimp; status_close))

macro "fields_close" : tactic => `(tactic| ((try simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte, Value.ofBool, JInt.ofBool, BitVec.ofNat_add_ofNat]) <;> first | rfl | exact (fileAtM_flags (by assumption) (by assumption)).1 | exact (fileAtM_flags (by assumption) (by assumption)).2.1 | exact (fileAtM_flags (by assumption) (by assumption)).2.2.2 | simp [Value.ofBool, JInt.ofBool]))

macro "closeT_state" : tactic => `(tactic| (refine (finT_ex (by assumption) (by assumption) (by assumption) (by keepsT_tac) ?_).1; hsimp; refine ⟨_, rfl, fun k h1 h2 => get_set_other h1, ⟨_, (get_set_other (by decide)).trans (by assumption), fileAtM_upd' (by assumption) (by assumption) (by keepsT_tac) ((away_chgT _).mono (by decide)) (by hsimp; try rfl) (by fields_close) (by fields_close) (by fields_close) (by first | decide | exact (fileAtM_flags (by assumption) (by assumption)).2.2.1) (by fields_close)⟩, ⟨_, (get_set_other (by decide)).trans (by assumption), jRecAt_keeps' (by assumption) (by keepsT_tac) ((away_chgT _).mono (by decide))⟩, ⟨_, get_set_same, _, rfl, ?_⟩⟩; rw [status_text]; hsimp; status_close))

macro "closeT_sep" : tactic => `(tactic| exact finT_sep (by assumption) (by assumption) (by assumption) (by keepsT_tac) ((away_chgT _).mono (by decide)) (by hsimp; try rfl) (fun k h1 h2 => by simp only [Fields.get_set, if_neg h1, if_neg h2]))

macro "closeT_area" : tactic => `(tactic| (refine area_rc (by assumption) (by assumption) (by assumption) (by keepsT_tac) (away_chgT _) (by hsimp; try rfl) (fun k h => get_set_other h) get_set_same ⟨_, rfl, ?_⟩; rw [stBytes_text]; hsimp; status_close))

theorem op_ne_text {b o : UInt8} (h : ¬ b = o) : ¬ (cp037Str [b] = cp037Str [o]) := fun e =>
  h (List.cons.inj (cp037Str_inj e)).1

/-- The state, the State object unchanged. -/
theorem stateAtM_keepS {σ0 σ' : State} {st : Addr} {s : Model.StM} (hs : StateAtM σ0 st s)
    (hk : Keeps (ChgS σ0) σ0 σ') (hst' : σ'.heap st = σ0.heap st) : StateAtM σ' st s := by
  obtain ⟨fs, hst, p1, p2, p3, p4⟩ := stateAtM_iff.1 hs
  exact stateAtM_iff.2 ⟨fs, by rw [hst', hst], p1.keeps hk ((away_chgS σ0).mono (by decide)),
    p2.keeps hk ((away_chgS σ0).mono (by decide)), p3.keeps hk ((away_chgS σ0).mono (by decide)),
    p4.keeps hk ((away_chgS σ0).mono (by decide))⟩

theorem sepM_keepS {σ0 σ' : State} {st : Addr} {s : Model.StM} (hs : StateAtM σ0 st s) (hsep : SepM σ0 st)
    (hk : Keeps (ChgS σ0) σ0 σ') (hst' : σ'.heap st = σ0.heap st) : SepM σ' st := by
  obtain ⟨fs, hst, -⟩ := id hs
  exact sepM_keeps hs hsep hk ((away_chgS σ0).mono (by decide)) (by rw [hst', hst])
    (fun fs0 h0 => by rw [hst] at h0; cases h0; exact ⟨rfl, rfl, rfl, rfl⟩)

/-- The record buffer after a TRNXFILE read: the record's text, space-padded to 1000. -/
theorem trnx_fldt {c i d : List UInt8} (hc : c.length = 16) (hi : i.length = 16) (hd : d.length = 318) :
    fixStr (fixStr (cp037Str c) 16 ++ (fixStr (cp037Str i) 16 ++ fixStr (cp037Str d) 318)) 1000 =
      cp037Str (intoBuf (Model.FdTrnxfileRec.encode [.str c, .str i, .str d])) := by
  have he : Model.FdTrnxfileRec.encode [.str c, .str i, .str d] = c ++ (i ++ d) := by
    simp [Schema.encode, Field.encode]
  rw [he, intoBuf_text (by simp [hc, hi, hd]), fixStr_eq_self (s := cp037Str c) (n := 16) (by rw [cp037Str_length, hc]),
    fixStr_eq_self (s := cp037Str i) (n := 16) (by rw [cp037Str_length, hi]), fixStr_eq_self (s := cp037Str d) (n := 318) (by rw [cp037Str_length, hd]), cp037Str_append,
    cp037Str_append]


theorem heap_growsK_lt {σ σ' : State} (h : GrowsK σ σ') {x : Addr} (hx : x < σ.next) : σ'.heap x = σ.heap x :=
  (growsK_elim h).2 x hx

open Lean Meta Elab Tactic in
/-- Rewrite a lookup `σ'.heap x` of the goal to `σ.heap x` with a hypothesis `GrowsK σ σ'` (`x < σ.next` by
`jdisch`). -/
elab "growsK_rw" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    for d in lctx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ty.isAppOfArity ``GrowsK 2 do continue
      let s ← saveState
      try
        let e ← mkAppM ``heap_growsK_lt #[d.toExpr]
        let r ← g.rewrite (← g.getType) e
        let g' ← g.replaceTargetEq r.eNew r.eqProof
        for m in r.mvarIds do
          unless ← m.isAssigned do
            let gs ← Tactic.run m (evalTactic (← `(tactic| jdisch)))
            unless gs.isEmpty do throwError "growsK_rw: side condition left"
        replaceMainGoal [g']
        return
      catch _ => s.restore
    throwError "growsK_rw: no GrowsK hypothesis rewrites the goal"

/-- Heap lookups through allocations, updates and callees (`GrowsK`). -/
macro "hsimpK" : tactic => `(tactic| repeat (first | (simp (disch := jdisch) only [State.heap_setObj_of_lt, State.heap_alloc, State.next_alloc, State.next_setObj, ↓reduceIte, ite_nat_ne, eq_self_iff_true, if_true]) | growsK_rw))

end EquivLean.Modernize.Cbstm03b.Java

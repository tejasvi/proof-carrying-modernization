import EquivLean.Modernize.Cbstm03b.Java.CustBase

/-!
# CBSTM03B → Java: the end of a path of `custProc`

What a path leaves in the heap, against the model's call. The objects a path may update are the State object,
the area, the CUSTFILE file object and the FD record object (`A4`); the file's record objects are not among them
(the FD record object is not one of them, `SepM`), so the file's records are kept.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.CustP

/-- The objects a path of `custProc` may update. -/
def A4 (st q c xr : Addr) (y : Addr) : Prop := y = st ∨ y = q ∨ y = c ∨ y = xr

theorem away4 {σ : State} {st q c xr : Addr} {f1 f2 f3 f4 : List (FieldKey × Value)} {cs : List ClassName}
    (h1 : σ.heap st = some (.plain "Cbstm03b$State" f1)) (h2 : σ.heap q = some (.plain "Cbstm03b$LkM03bArea" f2))
    (h3 : σ.heap c = some (.plain "Cbstm03b$CustFile" f3))
    (h4 : σ.heap xr = some (.plain "Cbstm03b$FdCustfileRec" f4))
    (hcs : "Cbstm03b$State" ∉ cs ∧ "Cbstm03b$LkM03bArea" ∉ cs ∧ "Cbstm03b$CustFile" ∉ cs ∧
      "Cbstm03b$FdCustfileRec" ∉ cs) :
    Away (A4 st q c xr) σ cs := by
  rintro y (rfl | rfl | rfl | rfl)
  · exact ⟨_, _, h1, hcs.1⟩
  · exact ⟨_, _, h2, hcs.2.1⟩
  · exact ⟨_, _, h3, hcs.2.2.1⟩
  · exact ⟨_, _, h4, hcs.2.2.2⟩

theorem keeps_setObj' {A : Addr → Prop} {σ0 σ : State} {a : Addr} {o : Obj} (h : Keeps A σ0 σ) (ha : A a) :
    Keeps A σ0 (σ.setObj a o) := keeps_trans h (keeps_setObj o ha)
theorem keeps_alloc' {A : Addr → Prop} {σ0 σ : State} {o : Obj} (h : Keeps A σ0 σ) :
    Keeps A σ0 (σ.alloc o).2 := keeps_trans h (keeps_alloc A σ o)
theorem keeps_grows' {A : Addr → Prop} {σ0 σ σ' : State} (h : Keeps A σ0 σ) (hg : Grows σ σ') :
    Keeps A σ0 σ' := keeps_trans h (keeps_of_grows hg)

/-- An update of a new object keeps the entry heap. -/
theorem keeps_setObj_fresh {A : Addr → Prop} {σ0 σ : State} {a : Addr} {o : Obj} (h : Keeps A σ0 σ)
    (ha : σ0.next ≤ a) : Keeps A σ0 (σ.setObj a o) :=
  ⟨by rw [State.next_setObj]; exact h.1, fun y hy hA => by
    rw [State.heap_setObj, if_neg (show ¬ (y = a) from fun e => absurd (e ▸ hy) (Nat.not_lt.2 ha)), h.2 y hy hA]⟩

/-- The entry heap kept but for the FD record object (a loop invariant's frame). -/
theorem keeps_of_frame {st q c xr : Addr} {σ0 σ : State} (hn : σ0.next ≤ σ.next)
    (hf : ∀ y, y < σ0.next → y ≠ xr → σ.heap y = σ0.heap y) : Keeps (A4 st q c xr) σ0 σ :=
  ⟨hn, fun y hy hA => hf y hy (fun e => hA (Or.inr (Or.inr (Or.inr e))))⟩

theorem mem_forall2 {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 → ∀ {x : α}, x ∈ l1 → ∃ y, R x y
  | [], [], .nil, _, h => by simp at h
  | _ :: _, _ :: _, .cons h0 hs, _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, h0⟩
    · exact mem_forall2 hs h

theorem jRecAt_same {σ0 σ' : State} {A : Addr → Prop} {S : Schema} {cls : ClassName} {x : Addr}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecAt S cls σ0 (.ref x) vals) (hx : σ'.heap x = σ0.heap x)
    (hk : Keeps A σ0 σ') (ha : Away A σ0 []) : JRecAt S cls σ' (.ref x) vals := by
  obtain ⟨x', fs, hxx, hxh, hfs⟩ := h
  cases hxx
  exact ⟨x, fs, rfl, by rw [hx, hxh], forall2_imp (fun _ _ h => jFieldAt_keeps hk ha h) hfs⟩

/-- The CUSTFILE file object after a path that kept its records array (and its record objects: none of the updated
objects is one of them) and wrote its flags. -/
theorem fileC {σ0 σ' : State} {o1 : Addr} {f : Model.FileM} {fs1 fs1' : List (FieldKey × Value)}
    {A : Addr → Prop} {b' e' : Bool} {p' : Nat}
    (hf : FileAtM "Cbstm03b$CustFile" "Cbstm03b$FdCustfileRec" FdCustfileRec σ0 (.ref o1) f)
    (ho1 : σ0.heap o1 = some (.plain "Cbstm03b$CustFile" fs1)) (hk : Keeps A σ0 σ') (ha : Away A σ0 [])
    (hrec : ∀ y, A y → NotRecOf σ0 "Cbstm03b$CustFile" (.ref y) (.ref o1) ∨
      ∃ c fs, σ0.heap y = some (.plain c fs) ∧ c ≠ "Cbstm03b$FdCustfileRec")
    (ho1' : σ'.heap o1 = some (.plain "Cbstm03b$CustFile" fs1'))
    (hrecs : Fields.get fs1' ("Cbstm03b$CustFile", "recs") = Fields.get fs1 ("Cbstm03b$CustFile", "recs"))
    (hopen : Fields.get fs1' ("Cbstm03b$CustFile", "open") = some (.ofBool b'))
    (hpos : Fields.get fs1' ("Cbstm03b$CustFile", "pos") = some (.int (BitVec.ofNat 32 p'))) (hp : p' < 2147483648)
    (heof : Fields.get fs1' ("Cbstm03b$CustFile", "eof") = some (.ofBool e')) :
    FileAtM "Cbstm03b$CustFile" "Cbstm03b$FdCustfileRec" FdCustfileRec σ' (.ref o1)
      { f with isOpen := b', pos := p', eof := e' } := by
  obtain ⟨o, fs, l, et, xs, hoo, hoo', -, hl0, hlh, hlen, hr, -, -, -⟩ := hf
  cases hoo
  rw [ho1] at hoo'
  cases hoo'
  have hlA : ¬ A l := fun hA => by
    obtain ⟨c, fs, h, -⟩ := ha l hA
    rw [hlh] at h
    cases h
  refine ⟨o1, fs1', l, et, xs, rfl, ho1', hopen, by rw [hrecs, hl0], heap_keeps hk hlh hlA, hlen,
    forall2_imp_mem (fun x hx vals h => ?_) hr, hp, hpos, heof⟩
  obtain ⟨r, fsr, hrr, hrh, hfs⟩ := h
  subst hrr
  have hrA : ¬ A r := fun hA => by
    rcases hrec r hA with hn | ⟨c, fs, h1, h2⟩
    · exact hn o1 fs1 l et xs rfl ho1 hl0 hlh hx
    · rw [hrh] at h1
      cases h1
      exact h2 rfl
  exact ⟨r, fsr, rfl, heap_keeps hk hrh hrA, forall2_imp (fun _ _ h => jFieldAt_keeps hk ha h) hfs⟩

/-- The FD record object is not one of the file's record objects, after a path that kept the records array. -/
theorem notRecOf_tr {σ0 σ' : State} {x : Value} {c l : Addr} {fs1 fs1' : List (FieldKey × Value)}
    (ho : σ0.heap c = some (.plain "Cbstm03b$CustFile" fs1))
    (ho' : σ'.heap c = some (.plain "Cbstm03b$CustFile" fs1'))
    (hr : Fields.get fs1' ("Cbstm03b$CustFile", "recs") = Fields.get fs1 ("Cbstm03b$CustFile", "recs"))
    (hl : Fields.get fs1 ("Cbstm03b$CustFile", "recs") = some (.ref l)) (hl' : σ'.heap l = σ0.heap l)
    (h : NotRecOf σ0 "Cbstm03b$CustFile" x (.ref c)) : NotRecOf σ' "Cbstm03b$CustFile" x (.ref c) := by
  intro o fs l' et xs hy ho1 hl1 hlh
  cases hy
  rw [ho'] at ho1
  cases ho1
  rw [hr, hl] at hl1
  cases hl1
  rw [hl'] at hlh
  exact h c fs1 l et xs rfl ho hl hlh

/-- A new object is not one of the file's record objects. -/
theorem notRecOf_fresh {σ0 σ' : State} {c l xn : Addr} {fs1 fs1' : List (FieldKey × Value)} {f : Model.FileM}
    (hf : FileAtM "Cbstm03b$CustFile" "Cbstm03b$FdCustfileRec" FdCustfileRec σ0 (.ref c) f)
    (ho : σ0.heap c = some (.plain "Cbstm03b$CustFile" fs1))
    (ho' : σ'.heap c = some (.plain "Cbstm03b$CustFile" fs1'))
    (hr : Fields.get fs1' ("Cbstm03b$CustFile", "recs") = Fields.get fs1 ("Cbstm03b$CustFile", "recs"))
    (hl : Fields.get fs1 ("Cbstm03b$CustFile", "recs") = some (.ref l)) (hl' : σ'.heap l = σ0.heap l)
    (hn : σ0.next ≤ xn) : NotRecOf σ' "Cbstm03b$CustFile" (.ref xn) (.ref c) := by
  obtain ⟨o, fs, l0, et, xs, hoo, hoo', -, hl0, hlh, -, hrF, -⟩ := hf
  cases hoo
  rw [ho] at hoo'
  cases hoo'
  rw [hl] at hl0
  cases hl0
  intro o' fs' l' et' xs' hy ho1 hl1 hlh' hmem
  cases hy
  rw [ho'] at ho1
  cases ho1
  rw [hr, hl] at hl1
  cases hl1
  rw [hl', hlh] at hlh'
  cases hlh'
  obtain ⟨vals, x', fsx, hxx, hxh, -⟩ := mem_forall2 hrF hmem
  cases hxx
  exact absurd (State.lt_next_of_heap hxh) (Nat.not_lt.2 hn)

abbrev otherC : List ClassName := ["Cbstm03b$TrnxFile", "Cbstm03b$FdTrnxfileRec", "Cbstm03b$XrefFile",
  "Cbstm03b$FdXreffileRec", "Cbstm03b$AcctFile", "Cbstm03b$FdAcctfileRec"]

/-- **The state after a CUSTFILE path**: the State object's other fields are kept, its CUSTFILE parts hold the
new values. -/
theorem finC {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs fs' : List (FieldKey × Value)} {A : Addr → Prop}
    {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal} {c' : List Nat}
    (hs : StateAtM σ0 st s) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps A σ0 σ') (ha : Away A σ0 otherC)
    (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (hkeep : ∀ k, k ≠ ("Cbstm03b$State", "custfileStatus") → k ≠ ("Cbstm03b$State", "fdCustfileRec") →
      Fields.get fs' k = Fields.get fs k)
    (hpart : PartC σ' fs' f' r' c') :
    StateAtM σ' st { s with cust := f', custRec := r', custSt := c' } := by
  obtain ⟨fs0, hst0, pT, pX, -, pA⟩ := stateAtM_iff.1 hs
  rw [hst] at hst0
  cases hst0
  refine stateAtM_iff.2 ⟨fs', hst', ?_, ?_, hpart, ?_⟩
  · exact (pT.fields (hkeep _ (by decide) (by decide)) (hkeep _ (by decide) (by decide))
      (hkeep _ (by decide) (by decide))).keeps hk (ha.mono (by decide))
  · exact (pX.fields (hkeep _ (by decide) (by decide)) (hkeep _ (by decide) (by decide))
      (hkeep _ (by decide) (by decide))).keeps hk (ha.mono (by decide))
  · exact (pA.fields (hkeep _ (by decide) (by decide)) (hkeep _ (by decide) (by decide))
      (hkeep _ (by decide) (by decide))).keeps hk (ha.mono (by decide))

/-- `SepM` after a CUSTFILE path: ACCTFILE's part kept, the FD record object of CUSTFILE not a record object. -/
theorem sepC {σ0 σ' : State} {st : Addr} {s : Model.StM} {A : Addr → Prop} {fs fs' : List (FieldKey × Value)}
    (hs : StateAtM σ0 st s) (hsep : SepM σ0 st) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps A σ0 σ') (ha : Away A σ0 ["Cbstm03b$AcctFile"])
    (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (e3 : Fields.get fs' ("Cbstm03b$State", "fdAcctfileRec") = Fields.get fs ("Cbstm03b$State", "fdAcctfileRec"))
    (e4 : Fields.get fs' ("Cbstm03b$State", "acctFile") = Fields.get fs ("Cbstm03b$State", "acctFile"))
    (hc : ∀ x y, Fields.get fs' ("Cbstm03b$State", "fdCustfileRec") = some x →
      Fields.get fs' ("Cbstm03b$State", "custFile") = some y → NotRecOf σ' "Cbstm03b$CustFile" x y) :
    SepM σ' st := by
  obtain ⟨fs0, hst0, -, -, -, ⟨⟨y4, g4, m4⟩, -, -⟩⟩ := stateAtM_iff.1 hs
  obtain ⟨fs1, hst1, -, c2⟩ := hsep
  rw [hst] at hst0 hst1
  cases hst0
  cases hst1
  refine ⟨fs', hst', hc, fun x y hx hy => ?_⟩
  rw [e3] at hx
  rw [e4, g4] at hy
  cases hy
  exact notRecOf_keeps hk ha m4 (c2 x y4 hx g4)

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

theorem encode_cust (id data : List UInt8) : Model.FdCustfileRec.encode [.str id, .str data] = id ++ data := by
  simp [Schema.encode, Field.encode, Model.FdCustfileRec, FdCustfileRec]

/-- `finC` with the new State field list as a witness. -/
theorem finC_ex {σ0 σ' : State} {st : Addr} {s : Model.StM} {fs : List (FieldKey × Value)} {A : Addr → Prop}
    {f' : Model.FileM} {r' : List EquivLean.Cobol.Rec.FVal} {c' : List Nat}
    (hs : StateAtM σ0 st s) (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (hk : Keeps A σ0 σ') (ha : Away A σ0 otherC)
    (h : ∃ fs', σ'.heap st = some (.plain "Cbstm03b$State" fs') ∧
      (∀ k, k ≠ ("Cbstm03b$State", "custfileStatus") → k ≠ ("Cbstm03b$State", "fdCustfileRec") →
        Fields.get fs' k = Fields.get fs k) ∧ PartC σ' fs' f' r' c') :
    StateAtM σ' st { s with cust := f', custRec := r', custSt := c' } := by
  obtain ⟨fs', h1, h2, h3⟩ := h
  exact finC hs hst hk ha h1 h2 h3

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

/-- The CUSTFILE file object, not written by the path. -/
theorem fileC_same {σ0 σ' : State} {o1 : Addr} {f : Model.FileM} {fs1 : List (FieldKey × Value)}
    {A : Addr → Prop}
    (hf : FileAtM "Cbstm03b$CustFile" "Cbstm03b$FdCustfileRec" FdCustfileRec σ0 (.ref o1) f)
    (ho1 : σ0.heap o1 = some (.plain "Cbstm03b$CustFile" fs1)) (hk : Keeps A σ0 σ') (ha : Away A σ0 [])
    (hrec : ∀ y, A y → NotRecOf σ0 "Cbstm03b$CustFile" (.ref y) (.ref o1) ∨
      ∃ c fs, σ0.heap y = some (.plain c fs) ∧ c ≠ "Cbstm03b$FdCustfileRec")
    (ho1' : σ'.heap o1 = σ0.heap o1) :
    FileAtM "Cbstm03b$CustFile" "Cbstm03b$FdCustfileRec" FdCustfileRec σ' (.ref o1) f := by
  obtain ⟨g1, g2, g3, g4⟩ := fileAtM_flags hf ho1
  exact fileC hf ho1 hk ha hrec (by rw [ho1', ho1]) rfl g1 g2 g3 g4

/-- The updated objects are not record objects of the file: the FD record object by `SepM`, the others by
class. -/
theorem rec4 {σ0 : State} {st q c xr : Addr} {f1 f2 f3 : List (FieldKey × Value)}
    (h1 : σ0.heap st = some (.plain "Cbstm03b$State" f1)) (h2 : σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" f2))
    (h3 : σ0.heap c = some (.plain "Cbstm03b$CustFile" f3))
    (hnr : NotRecOf σ0 "Cbstm03b$CustFile" (.ref xr) (.ref c)) :
    ∀ y, A4 st q c xr y → NotRecOf σ0 "Cbstm03b$CustFile" (.ref y) (.ref c) ∨
      ∃ c' fs, σ0.heap y = some (.plain c' fs) ∧ c' ≠ "Cbstm03b$FdCustfileRec" := by
  rintro y (rfl | rfl | rfl | rfl)
  · exact Or.inr ⟨_, _, h1, by decide⟩
  · exact Or.inr ⟨_, _, h2, by decide⟩
  · exact Or.inr ⟨_, _, h3, by decide⟩
  · exact Or.inl hnr

theorem nr_of_sep {σ0 : State} {st c xr : Addr} {fs : List (FieldKey × Value)} (hsep : SepM σ0 st)
    (hst : σ0.heap st = some (.plain "Cbstm03b$State" fs))
    (g1 : Fields.get fs ("Cbstm03b$State", "custFile") = some (.ref c))
    (k1 : Fields.get fs ("Cbstm03b$State", "fdCustfileRec") = some (.ref xr)) :
    NotRecOf σ0 "Cbstm03b$CustFile" (.ref xr) (.ref c) := by
  obtain ⟨fs0, hst0, c1, -⟩ := hsep
  rw [hst] at hst0
  cases hst0
  exact c1 _ _ k1 g1

/-- The record objects of the file are not the FD record object. -/
theorem ne_xr_of_mem {σ0 : State} {c xr l rx : Addr} {fs1 : List (FieldKey × Value)} {et : JType}
    {xs : List Value} (hnr : NotRecOf σ0 "Cbstm03b$CustFile" (.ref xr) (.ref c))
    (ho : σ0.heap c = some (.plain "Cbstm03b$CustFile" fs1))
    (hl : Fields.get fs1 ("Cbstm03b$CustFile", "recs") = some (.ref l)) (hlh : σ0.heap l = some (.array et xs))
    (hm : Value.ref rx ∈ xs) : rx ≠ xr := by
  rintro rfl
  exact hnr c fs1 l et xs rfl ho hl hlh hm

/-- `fit(keySub(area), 9)`'s result is not an object of the entry heap that is not a string: it is new, or it is
`keySub`'s result, a string (of the heap after `keySub`, which kept the entry heap's objects). -/
theorem k9_ne {σ0 σ1 : State} {x w y : Addr} {t : JStr} {c : ClassName} {fs : List (FieldKey × Value)}
    (hy : σ0.heap y = some (.plain c fs))
    (h01 : ∀ z, z < σ0.next + 1 + 1 → σ1.heap z =
      if z = σ0.next + 1 then some (Obj.str (JStr.ofString "K"))
      else if z = σ0.next then some (Obj.str (JStr.ofString "O")) else σ0.heap z)
    (hle : σ0.next + 1 + 1 ≤ σ1.next) (hx : σ1.heap x = some (.str t)) (hw : σ1.next ≤ w ∨ x = w) :
    w ≠ y := by
  have hy0 := State.lt_next_of_heap hy
  have hy2 : y < σ0.next + 1 + 1 := Nat.lt_of_lt_of_le hy0 (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
  rcases hw with hw | rfl
  · intro e
    rw [e] at hw
    exact absurd (Nat.lt_of_lt_of_le hy2 hle) (Nat.not_lt.2 hw)
  · intro e
    subst e
    have h := h01 x hy2
    rw [if_neg (Nat.ne_of_lt (Nat.lt_of_lt_of_le hy0 (Nat.le_succ _))), if_neg (Nat.ne_of_lt hy0), hy, hx] at h
    cases h

theorem argText_ref {σ : State} {x : Addr} {t : JStr} (h : σ.heap x = some (.str t)) :
    argText σ (.ref x) = t := by
  simp [argText, strOf, h]

theorem st_lits' : JStr.ofString "00" = stChars 0 ∧ JStr.ofString "41" = stChars 41 ∧
    JStr.ofString "47" = stChars 47 ∧ JStr.ofString "23" = stChars 23 ∧ JStr.ofString "42" = stChars 42 :=
  st_lits

/-- The updated objects of a path: the State object, the area, the file and the FD record object. -/
macro "keeps4_tac" : tactic => `(tactic| repeat (first | exact keeps_refl _ _ | assumption | (refine keeps_setObj' ?_ (by simp [A4])) | (refine keeps_setObj_fresh ?_ (by jdisch)) | (refine keeps_alloc' ?_) | (refine keeps_grows' ?_ (growsK_elim (by assumption)))))

/-- Heap lookups in a state built from the entry state by allocations, updates and callees. -/
macro "chsimp" : tactic => `(tactic| simp (disch := jdisch) only [State.heap_setObj_of_lt, State.heap_alloc, State.next_alloc, State.next_setObj, ↓reduceIte, ite_nat_ne, eq_self_iff_true, if_true])

macro "cstatus_close" : tactic => `(tactic| first | (simp only [st_lits]) | assumption | rfl)

macro "cfields_close" : tactic => `(tactic| ((try simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte, Value.ofBool, JInt.ofBool]) <;> first | rfl | assumption | exact (fileAtM_flags (by assumption) (by assumption)).1 | exact (fileAtM_flags (by assumption) (by assumption)).2.1 | exact (fileAtM_flags (by assumption) (by assumption)).2.2.2 | simp [Value.ofBool, JInt.ofBool]))

end EquivLean.Modernize.Cbstm03b.Java.CustP

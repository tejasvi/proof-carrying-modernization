import EquivLean.Modernize.Cbstm03b.Java.Base

/-!
# CBSTM03B → Java: `custProc` (CUSTFILE), the definitions and lemmas of its proof

* the model's CUSTFILE call, case by case (`callC_*`);
* the key `custProc` stores (`fit(keySub(area), 9)`) against the model's `custKey` (`fit_key9`);
* the symbolic-execution goal of the method (`custWP`) and the two loop invariants: at the loop head (`Inv49`) and
  at the record load (`Inv53`); both state the current heap against the entry heap (the objects other than the FD
  record object are unchanged) and the records searched so far (`NoMatch`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.CustP

theorem get_set_other {fs : List (FieldKey × Value)} {k k' : FieldKey} {v : Value} (h : k' ≠ k) :
    Fields.get (Fields.set fs k v) k' = Fields.get fs k' := by
  rw [Fields.get_set, if_neg h]

theorem get_set_same {fs : List (FieldKey × Value)} {k : FieldKey} {v : Value} :
    Fields.get (Fields.set fs k v) k = some v := by
  rw [Fields.get_set, if_pos rfl]

/-- A fact kept from the symbolic executor (it does not unfold it). -/
@[irreducible] def Kept (p : Prop) : Prop := p

theorem Kept.intro {p : Prop} (h : p) : Kept p := by unfold Kept; exact h
theorem Kept.elim {p : Prop} (h : Kept p) : p := by unfold Kept at h; exact h

/-- A callee's `Grows`, kept folded across the symbolic executor. -/
@[irreducible] def GrowsK (σ σ' : State) : Prop := Grows σ σ'

theorem growsK_elim {σ σ' : State} (h : GrowsK σ σ') : Grows σ σ' := by unfold GrowsK at h; exact h

/-- `Grows` for the executor: a folded copy, and the facts it unfolds to. -/
theorem grows_split (σ σ' : State) :
    Grows σ σ' ↔ GrowsK σ σ' ∧ σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → σ'.heap x = σ.heap x := by
  constructor
  · intro h; exact ⟨by unfold GrowsK; exact h, h.1, h.2⟩
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩

theorem grows_alloc (σ : State) (o : Obj) : Grows σ (σ.alloc o).2 :=
  ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun _ hy => State.heap_alloc_of_lt hy o⟩

theorem ne_of_cls {σ : State} {x y : Addr} {c d : ClassName} {fs gs : List (FieldKey × Value)}
    (hx : σ.heap x = some (.plain c fs)) (hy : σ.heap y = some (.plain d gs)) (h : c ≠ d) : x ≠ y := by
  intro e
  rw [e, hy] at hx
  injection hx with hx
  injection hx with hx
  exact h hx.symm

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 → l1.length = l2.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [forall2_length h]

/-- The `i`-th pair of a `Forall2`. -/
theorem forall2_get {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 → ∀ {i : Nat} {x : α} {y : β}, l1[i]? = some x →
      l2[i]? = some y → R x y
  | [], [], .nil, _, _, _, h, _ => by simp at h
  | _ :: _, _ :: _, .cons h0 _, 0, _, _, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1; subst h2; exact h0
  | _ :: _, _ :: _, .cons _ hs, i + 1, _, _, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    exact forall2_get hs h1 h2

theorem forall2_imp_mem {α β : Type} {R R' : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, (∀ a ∈ l1, ∀ b, R a b → R' a b) → Forall2 R l1 l2 → Forall2 R' l1 l2
  | [], [], _, .nil => .nil
  | _ :: _, _ :: _, hR, .cons h hs =>
    .cons (hR _ (List.mem_cons_self ..) _ h) (forall2_imp_mem (fun a ha b => hR a (List.mem_cons_of_mem _ ha) b) hs)

/-! ## The model's CUSTFILE call, case by case -/

section model

variable {oeM : Model.OpenErrs} {s : Model.StM} {a : List EquivLean.Cobol.Rec.FVal}

theorem ddCust_ne_trnx : ddCust ≠ ddTrnx := by decide
theorem ddCust_ne_xref : ddCust ≠ ddXref := by decide

/-- The key `custProc` stores in the FD record (`FD-CUST-ID`). -/
def key9 (a : List EquivLean.Cobol.Rec.FVal) : List UInt8 := Model.custKey (Model.aKey a) (Model.aKeyLn a).toNat

/-- A file just opened: at its first record, not at the end. -/
def openedF (f : Model.FileM) : Model.FileM := { f with isOpen := true, pos := 0, eof := false }

/-- A closed file. -/
def closedF (f : Model.FileM) : Model.FileM := { f with isOpen := false }

/-- The file after a keyed read of record `i`. -/
def foundF (f : Model.FileM) (i : Nat) : Model.FileM := { f with pos := i + 1, eof := false }

set_option maxHeartbeats 400000

theorem callC_open41 (hd : Model.aDd a = ddCust) (ho : Model.aOp a = opOpen) (hb : s.cust.isOpen = true) :
    Model.call oeM s a = ({ s with custSt := Model.stCp 41 }, Model.setRc a (stBytes 41)) := by
  simp only [Model.call, hd, ho, ddCust_ne_trnx, ddCust_ne_xref, ↓reduceIte, Model.keyStep, Model.openM, hb]

theorem callC_openErr {c : Nat} (hd : Model.aDd a = ddCust) (ho : Model.aOp a = opOpen)
    (hb : s.cust.isOpen = false) (he : oeM 3 = some c) :
    Model.call oeM s a = ({ s with custSt := Model.stCp c }, Model.setRc a (stBytes c)) := by
  simp only [Model.call, hd, ho, ddCust_ne_trnx, ddCust_ne_xref, ↓reduceIte, Model.keyStep, Model.openM, hb, he,
    Bool.false_eq_true]

theorem callC_open00 (hd : Model.aDd a = ddCust) (ho : Model.aOp a = opOpen) (hb : s.cust.isOpen = false)
    (he : oeM 3 = none) :
    Model.call oeM s a = ({ s with cust := openedF s.cust, custSt := Model.stCp 0 }, Model.setRc a (stBytes 0)) := by
  simp only [Model.call, hd, ho, ddCust_ne_trnx, ddCust_ne_xref, ↓reduceIte, Model.keyStep, Model.openM, hb, he,
    Bool.false_eq_true, openedF]

theorem callC_read47 (hd : Model.aDd a = ddCust) (ho : Model.aOp a = opReadK) (hb : s.cust.isOpen = false) :
    Model.call oeM s a = ({ s with custRec := s.custRec.set 0 (.str (key9 a)), custSt := Model.stCp 47 },
      Model.setRc a (stBytes 47)) := by
  simp only [Model.call, hd, ho, ddCust_ne_trnx, ddCust_ne_xref, ↓reduceIte, Model.keyStep, Model.keyReadM, hb,
    opReadK, opOpen, Bool.not_false, key9]
  try rfl

theorem callC_read23 (hd : Model.aDd a = ddCust) (ho : Model.aOp a = opReadK) (hb : s.cust.isOpen = true)
    (hf : s.cust.recs.findIdx? (fun x => Model.strOf (x.getD 0 default) == key9 a) = none) :
    Model.call oeM s a = ({ s with custRec := s.custRec.set 0 (.str (key9 a)), custSt := Model.stCp 23 },
      Model.setRc a (stBytes 23)) := by
  simp only [key9] at hf
  simp only [Model.call, hd, ho, ddCust_ne_trnx, ddCust_ne_xref, ↓reduceIte, Model.keyStep, Model.keyReadM, hb,
    opReadK, opOpen, Bool.not_true, hf, key9]
  try rfl

theorem callC_read00 {i : Nat} (hd : Model.aDd a = ddCust) (ho : Model.aOp a = opReadK) (hb : s.cust.isOpen = true)
    (hf : s.cust.recs.findIdx? (fun x => Model.strOf (x.getD 0 default) == key9 a) = some i) :
    Model.call oeM s a =
      ({ s with cust := foundF s.cust i, custRec := s.cust.recs.getD i [], custSt := Model.stCp 0 },
        Model.setFldt (Model.setRc a (stBytes 0)) (Model.FdCustfileRec.encode (s.cust.recs.getD i []))) := by
  simp only [key9] at hf
  simp only [Model.call, hd, ho, ddCust_ne_trnx, ddCust_ne_xref, ↓reduceIte, Model.keyStep, Model.keyReadM, hb,
    opReadK, opOpen, Bool.not_true, hf, foundF]
  try rfl

theorem callC_close42 (hd : Model.aDd a = ddCust) (ho : Model.aOp a = opClose) (hb : s.cust.isOpen = false) :
    Model.call oeM s a = ({ s with custSt := Model.stCp 42 }, Model.setRc a (stBytes 42)) := by
  simp only [Model.call, hd, ho, ddCust_ne_trnx, ddCust_ne_xref, ↓reduceIte, Model.keyStep, Model.closeM, hb,
    opClose, opReadK, opOpen]
  try rfl

theorem callC_close00 (hd : Model.aDd a = ddCust) (ho : Model.aOp a = opClose) (hb : s.cust.isOpen = true) :
    Model.call oeM s a = ({ s with cust := closedF s.cust, custSt := Model.stCp 0 }, Model.setRc a (stBytes 0)) := by
  simp only [Model.call, hd, ho, ddCust_ne_trnx, ddCust_ne_xref, ↓reduceIte, Model.keyStep, Model.closeM, hb,
    opClose, opReadK, opOpen, closedF]
  try rfl

theorem callC_other (hd : Model.aDd a = ddCust) (h1 : Model.aOp a ≠ opOpen) (h2 : Model.aOp a ≠ opReadK)
    (h3 : Model.aOp a ≠ opClose) :
    Model.call oeM s a = (s, Model.setRc a (s.custSt.map ebcdicOfLatin1)) := by
  simp only [Model.call, hd, ddCust_ne_trnx, ddCust_ne_xref, ↓reduceIte, Model.keyStep, h1, h2, h3]

/-- The records before `i` do not match the key. -/
def NoMatch (recs : List (List EquivLean.Cobol.Rec.FVal)) (key : List UInt8) (i : Nat) : Prop :=
  ∀ j, j < i → Model.strOf ((recs.getD j []).getD 0 default) ≠ key

theorem getD_rec {recs : List (List EquivLean.Cobol.Rec.FVal)} {j : Nat} (hj : j < recs.length) :
    recs.getD j [] = recs[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

theorem findIdx_none {recs : List (List EquivLean.Cobol.Rec.FVal)} {key : List UInt8}
    (h : NoMatch recs key recs.length) :
    recs.findIdx? (fun x => Model.strOf (x.getD 0 default) == key) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := h j hj
  rw [getD_rec hj] at this
  simpa using this

theorem findIdx_some {recs : List (List EquivLean.Cobol.Rec.FVal)} {key : List UInt8} {i : Nat}
    (h : NoMatch recs key i) (hi : i < recs.length)
    (hm : Model.strOf ((recs.getD i []).getD 0 default) = key) :
    recs.findIdx? (fun x => Model.strOf (x.getD 0 default) == key) = some i := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hi, ?_, fun j hj => ?_⟩
  · rw [getD_rec hi] at hm
    simpa using hm
  · have := h j hj
    rw [getD_rec (Nat.lt_trans hj hi)] at this
    simpa using this

theorem noMatch_zero {recs : List (List EquivLean.Cobol.Rec.FVal)} {key : List UInt8} : NoMatch recs key 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem noMatch_succ {recs : List (List EquivLean.Cobol.Rec.FVal)} {key : List UInt8} {i : Nat}
    (h : NoMatch recs key i) (hm : Model.strOf ((recs.getD i []).getD 0 default) ≠ key) :
    NoMatch recs key (i + 1) := fun j hj => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · exact h j hj
  · exact hm

end model

/-! ## Texts -/

/-- `fit(keySub(area), 9)`: the key the model stores. -/
theorem fit_key9 {a : List EquivLean.Cobol.Rec.FVal} (hk : (Model.aKey a).length = 25) (h1 : 1 ≤ Model.aKeyLn a)
    (h2 : Model.aKeyLn a ≤ 25) :
    fixStr (cp037Str ((Model.aKey a).take (Model.aKeyLn a).toNat)) 9 = cp037Str (key9 a) := by
  have hk25 : (Model.aKeyLn a).toNat ≤ 25 := by omega
  unfold key9 Model.custKey
  generalize Model.aKey a = key at hk ⊢
  generalize (Model.aKeyLn a).toNat = k at hk25 ⊢
  have hl : (key.take k).length = k := by rw [List.length_take, hk]; omega
  rcases Nat.lt_or_ge 9 k with h | h
  · rw [fixStr_eq_take (by rw [cp037Str_length, hl]; omega), show 9 - k = 0 by omega, List.replicate_zero,
      List.append_nil]
    simp only [cp037Str_take]
  · have e : (List.take k key ++ List.replicate (9 - k) 64).take 9 = List.take k key ++ List.replicate (9 - k) 64 :=
      List.take_of_length_le (by simp only [List.length_append, List.length_replicate, hl]; omega)
    rw [fixStr_eq_append (by rw [cp037Str_length, hl]; exact h), cp037Str_length, hl, e, cp037Str_append,
      cp037_replicate_space]

theorem st_lits : JStr.ofString "00" = stChars 0 ∧ JStr.ofString "41" = stChars 41 ∧
    JStr.ofString "47" = stChars 47 ∧ JStr.ofString "23" = stChars 23 ∧ JStr.ofString "42" = stChars 42 := by
  decide +kernel

/-! ## The callee contracts

`status2` and `fit` with fresh results (`HFresh.lean`'s `status2SpecF` and `fitSpecF`, copied): the returned string
is a new object (for `fit`: or the argument itself). -/

def status2SpecF : Spec := Spec.of
  (fun args _ => ∃ c : I32, args = [.int c] ∧ 0 ≤ c.toInt ∧ c.toInt < 100)
  (fun args σ r σ' => ∀ c : I32, args = [.int c] →
     ∃ x, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str (stChars c.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def fitSpecF : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrOk σ sv ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ (σ.next ≤ x ∨ sv = .ref x) ∧
       σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- The callee contracts `custProc` is verified against. -/
def custCalleesF : Contracts :=
  [(status2Sig, status2SpecF), (fitSig, fitSpecF), (keySubSig, keySubSpec), (spacesSig, spacesSpec)]

/-! ## The method's goal and its invariants -/

/-- At the loop head (`label07`, statement 49): `i5 = i`, `$i0 = -1`; the heap is the entry heap but for the FD
record object `xr`, whose `fdCustId` holds the key; the records before `i` do not match it. -/
@[irreducible] def Inv49 (st q : Addr) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal) (_args : List Value)
    (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (fs : List (FieldKey × Value)) (c xr k9 : Addr) (fsX : List (FieldKey × Value)) (i : Nat),
    σ0.heap st = some (.plain "Cbstm03b$State" fs) ∧
    Fields.get fs ("Cbstm03b$State", "custFile") = some (.ref c) ∧
    Fields.get fs ("Cbstm03b$State", "fdCustfileRec") = some (.ref xr) ∧
    σ0.heap xr = some (.plain "Cbstm03b$FdCustfileRec" fsX) ∧
    fr.get 0 = some (.ref q) ∧ fr.get 1 = some (.ref c) ∧ fr.get 3 = some (.ref st) ∧
    fr.get 6 = some (.int (BitVec.ofInt 32 (-1))) ∧ fr.get 8 = some (.int (BitVec.ofNat 32 i)) ∧
    σ0.next ≤ σ.next ∧ (∀ y, y < σ0.next → y ≠ xr → σ.heap y = σ0.heap y) ∧
    σ.heap xr = some (.plain "Cbstm03b$FdCustfileRec"
      (Fields.set fsX ("Cbstm03b$FdCustfileRec", "fdCustId") (.ref k9))) ∧
    σ.heap k9 = some (.str (cp037Str (key9 a))) ∧ σ.inits = σ0.inits ∧
    i ≤ s.cust.recs.length ∧ NoMatch s.cust.recs (key9 a) i ∧ Model.aOp a = opReadK ∧ s.cust.isOpen = true

/-- At the record load (statement 53): as at the loop head, with `i` below the number of records and `$r15` the
records array. -/
@[irreducible] def Inv53 (st q : Addr) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal) (_args : List Value)
    (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (fs : List (FieldKey × Value)) (c xr k9 : Addr) (fsX fsC : List (FieldKey × Value)) (l : Addr) (i : Nat),
    σ0.heap st = some (.plain "Cbstm03b$State" fs) ∧
    Fields.get fs ("Cbstm03b$State", "custFile") = some (.ref c) ∧
    Fields.get fs ("Cbstm03b$State", "fdCustfileRec") = some (.ref xr) ∧
    σ0.heap xr = some (.plain "Cbstm03b$FdCustfileRec" fsX) ∧
    σ0.heap c = some (.plain "Cbstm03b$CustFile" fsC) ∧
    Fields.get fsC ("Cbstm03b$CustFile", "recs") = some (.ref l) ∧
    fr.get 0 = some (.ref q) ∧ fr.get 1 = some (.ref c) ∧ fr.get 3 = some (.ref st) ∧
    fr.get 6 = some (.int (BitVec.ofInt 32 (-1))) ∧ fr.get 8 = some (.int (BitVec.ofNat 32 i)) ∧
    fr.get 13 = some (.ref l) ∧
    σ0.next ≤ σ.next ∧ (∀ y, y < σ0.next → y ≠ xr → σ.heap y = σ0.heap y) ∧
    σ.heap xr = some (.plain "Cbstm03b$FdCustfileRec"
      (Fields.set fsX ("Cbstm03b$FdCustfileRec", "fdCustId") (.ref k9))) ∧
    σ.heap k9 = some (.str (cp037Str (key9 a))) ∧ σ.inits = σ0.inits ∧
    i < s.cust.recs.length ∧ NoMatch s.cust.recs (key9 a) i ∧ Model.aOp a = opReadK ∧ s.cust.isOpen = true

/-- The fields of a new `FdCustfileRec` object. -/
def newRecFields : List (FieldKey × Value) :=
  [(("Cbstm03b$FdCustfileRec", "fdCustId"), .null), (("Cbstm03b$FdCustfileRec", "fdCustData"), .null)]

/-- After the record `i` that matched was copied (statement 80): the file's position and end flag, the State
object's FD record (a new object holding the record's two strings) and the status text `"00"` are written; the
rest of the entry heap is unchanged but for the old FD record object. -/
@[irreducible] def Inv80 (st q : Addr) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal) (_args : List Value)
    (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (fs fs1 fsq fsr : List (FieldKey × Value)) (c xr rx xn x00 xid xdat : Addr) (i : Nat) (rid rdat : List UInt8),
    σ0.heap st = some (.plain "Cbstm03b$State" fs) ∧
    Fields.get fs ("Cbstm03b$State", "custFile") = some (.ref c) ∧
    Fields.get fs ("Cbstm03b$State", "fdCustfileRec") = some (.ref xr) ∧
    σ0.heap c = some (.plain "Cbstm03b$CustFile" fs1) ∧
    σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) ∧
    σ0.heap rx = some (.plain "Cbstm03b$FdCustfileRec" fsr) ∧
    Fields.get fsr ("Cbstm03b$FdCustfileRec", "fdCustId") = some (.ref xid) ∧
    Fields.get fsr ("Cbstm03b$FdCustfileRec", "fdCustData") = some (.ref xdat) ∧
    σ0.heap xid = some (.str (cp037Str rid)) ∧ σ0.heap xdat = some (.str (cp037Str rdat)) ∧
    rx ≠ xr ∧ rid.length = 9 ∧ rdat.length = 491 ∧
    s.cust.recs.getD i [] = [.str rid, .str rdat] ∧ i < s.cust.recs.length ∧
    s.cust.recs.findIdx? (fun x => Model.strOf (x.getD 0 default) == key9 a) = some i ∧
    Model.aOp a = opReadK ∧ s.cust.isOpen = true ∧
    fr.get 0 = some (.ref q) ∧ fr.get 3 = some (.ref st) ∧ fr.get 5 = some (.ref rx) ∧
    fr.get 9 = some (.ref x00) ∧
    σ0.next ≤ x00 ∧ x00 < xn ∧ xn < σ.next ∧
    (∀ y, y < σ0.next → y ≠ xr → y ≠ c → y ≠ st → σ.heap y = σ0.heap y) ∧
    σ.heap st = some (.plain "Cbstm03b$State" (Fields.set fs ("Cbstm03b$State", "fdCustfileRec") (.ref xn))) ∧
    σ.heap c = some (.plain "Cbstm03b$CustFile" (Fields.set (Fields.set fs1 ("Cbstm03b$CustFile", "pos")
      (.int (BitVec.ofNat 32 i + 1#32))) ("Cbstm03b$CustFile", "eof") (.int 0#32))) ∧
    σ.heap xn = some (.plain "Cbstm03b$FdCustfileRec" (Fields.set (Fields.set newRecFields
      ("Cbstm03b$FdCustfileRec", "fdCustId") (.ref xid)) ("Cbstm03b$FdCustfileRec", "fdCustData") (.ref xdat))) ∧
    σ.heap x00 = some (.str (JStr.ofString "00")) ∧ σ.inits = σ0.inits

def custInvG (st q : Addr) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal) : Invariants :=
  [(49, Inv49 st q s a), (53, Inv53 st q s a), (80, Inv80 st q s a)]

/-- The goal of a path of `custProc` from statement `pc`. -/
@[irreducible] def custWP (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) :
    Prop :=
  bodyWP Gen.prog (callWP Gen.prog custCalleesF.env 1)
    Gen.Cbstm03b.«custProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»
    (Invariants.inst (custInvG st q s a) args σ0) ((procSpecG ddCust oe st q opv oeM s a).post args σ0) 200 pc fr σ

theorem custWP_def (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) :
    custWP oe st q opv oeM s a args σ0 pc fr σ =
      bodyWP Gen.prog (callWP Gen.prog custCalleesF.env 1)
        Gen.Cbstm03b.«custProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»
        (Invariants.inst (custInvG st q s a) args σ0) ((procSpecG ddCust oe st q opv oeM s a).post args σ0) 200
        pc fr σ := by
  unfold custWP; rfl

end EquivLean.Modernize.Cbstm03b.Java.CustP

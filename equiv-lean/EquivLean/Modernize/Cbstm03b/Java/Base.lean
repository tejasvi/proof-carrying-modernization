import EquivLean.Modernize.Cbstm03b.Java.Iface

/-!
# CBSTM03B → Java: shared facts

* texts: the lemmas of JimpleLean's CardDemo examples about `fixStr`, `zpadStr` and the digit loop;
* CP037: the code page is injective (`cp037Str_inj`), digits, letters and the space; the status and DD texts;
* schemas: each record object's fields, explicitly (`areaAt_iff`, `trnxRecAt_iff`, …);
* heaps: the model relations are kept by a heap that only grows (`StateAtM.grows`, …).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-! ## Texts -/

@[simp] theorem fixStr_length (s : JStr) : ∀ n, (fixStr s n).length = n
  | 0 => rfl
  | n + 1 => by simp [fixStr, fixStr_length s n]

theorem fixStr_eq_map (s : JStr) : ∀ n, fixStr s n = (List.range n).map (fun i => s.getD i space)
  | 0 => rfl
  | n + 1 => by rw [fixStr, fixStr_eq_map s n, List.range_succ, List.map_append]; rfl

/-- A text of the field's length is displayed as it is. -/
theorem fixStr_eq_self {s : JStr} {n : Nat} (h : s.length = n) : fixStr s n = s := by
  subst h
  rw [fixStr_eq_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [h2]

/-- A text at least as long as the field is cut to the field's width. -/
theorem fixStr_eq_take {s : JStr} {n : Nat} (h : n ≤ s.length) : fixStr s n = s.take n := by
  rw [fixStr_eq_map]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  simp at h1
  simp [List.getElem?_eq_getElem (show i < s.length by omega)]

/-- Past the text, the field is padded with spaces. -/
theorem fixStr_succ_of_ge {s : JStr} {k : Nat} (h : s.length ≤ k) :
    fixStr s (k + 1) = fixStr s k ++ [space] := by
  rw [fixStr]
  congr 2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- A shorter text, padded: the text, then spaces. -/
theorem fixStr_eq_append {s : JStr} {n : Nat} (h : s.length ≤ n) :
    fixStr s n = s ++ List.replicate (n - s.length) space := by
  rw [fixStr_eq_map]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < s.length
  · rw [List.getElem_append_left hi]
    simp [List.getElem?_eq_getElem hi]
  · rw [List.getElem_append_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : s.length ≤ i)]

theorem jstr_empty : JStr.ofString "" = [] := rfl

theorem max_zero_of_nonneg {a : Int} (h : 0 ≤ a) : max a 0 = a := by omega

theorem msb_false_of_toInt_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) : l.msb = false := by
  have := BitVec.toInt_eq_toNat_cond l
  have hl := l.isLt
  rw [BitVec.msb_eq_decide]
  simp only [decide_eq_false_iff_not, Nat.not_le]
  by_cases hc : 2 * l.toNat < 2 ^ 64
  · omega
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' hc)] at this
    · omega

theorem srem10_of_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) :
    l.srem 10#64 = BitVec.ofNat 64 (l.toNat % 10) := by
  have hmsb := msb_false_of_toInt_nonneg l h
  have h10 : (10#64).msb = false := by decide
  rw [BitVec.srem_eq, hmsb, h10]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : l.toNat % 10 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]

theorem sdiv10_toNat_of_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) :
    (l.sdiv 10#64).toNat = l.toNat / 10 := by
  have hmsb := msb_false_of_toInt_nonneg l h
  have h10 : (10#64).msb = false := by decide
  rw [BitVec.sdiv_eq, hmsb, h10]
  simp [BitVec.toNat_udiv]

theorem sdiv10_nonneg (l : BitVec 64) (h : 0 ≤ l.toInt) : 0 ≤ (l.sdiv 10#64).toInt := by
  have hn := sdiv10_toNat_of_nonneg l h
  have hc := BitVec.toInt_eq_toNat_cond (l.sdiv 10#64)
  have hl := l.isLt
  by_cases hq : 2 * (l.sdiv 10#64).toNat < 2 ^ 64
  · rw [ite_eq_left_iff.mpr (fun h' => absurd hq h')] at hc; omega
  · rw [hn] at hq; omega

/-- The character `zeroPad` stores: `(char) ('0' + (int) (l % 10))`. -/
theorem digit_char (l : BitVec 64) (h : 0 ≤ l.toInt) :
    (JInt.toChar (48#32 + JLong.toInt (l.srem 10#64))).setWidth 16 = digitChar (l.toNat % 10) := by
  rw [srem10_of_nonneg l h]
  apply BitVec.eq_of_toNat_eq
  simp only [digitChar, JInt.toChar, JLong.toInt, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

theorem drop_set_self {α : Type} : ∀ (xs : List α) (k : Nat) (e : α), k < xs.length →
    (xs.set k e).drop k = e :: xs.drop (k + 1)
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => rfl
  | _ :: xs, k + 1, e, h => by
    simp only [List.set_cons_succ, List.drop_succ_cons]
    exact drop_set_self xs k e (by simpa using h)

theorem zpadStr_length (c : Nat) : ∀ m, (zpadStr c m).length = m
  | 0 => rfl
  | m + 1 => by simp [zpadStr, zpadStr_length (c / 10) m]

/-! ## Heaps that only grow -/

theorem grows_refl (σ : State) : Grows σ σ := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem grows_trans {σ1 σ2 σ3 : State} (h1 : Grows σ1 σ2) (h2 : Grows σ2 σ3) : Grows σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun x hx => by rw [h2.2 x (Nat.lt_of_lt_of_le hx h1.1), h1.2 x hx]⟩

theorem heap_grows {σ σ' : State} {x : Addr} {o : Obj} (hg : Grows σ σ') (h : σ.heap x = some o) :
    σ'.heap x = some o := by
  rw [hg.2 x (State.lt_next_of_heap h), h]

/-! ## Heaps: what a run keeps

`Keeps A σ σ'`: the objects of `σ` at addresses outside `A` are unchanged in `σ'`. A heap that only grows keeps
everything; an update of an object at an address in `A` keeps the rest. A relation whose objects are outside `A`
holds in `σ'` when it holds in `σ`. `A` is given by classes (the objects a procedure updates in place are of
classes no other relation uses), possibly with single addresses added. -/

/-- The objects of `σ` at addresses outside `A` are unchanged in `σ'`. -/
def Keeps (A : Addr → Prop) (σ σ' : State) : Prop :=
  σ.next ≤ σ'.next ∧ ∀ y, y < σ.next → ¬ A y → σ'.heap y = σ.heap y

theorem keeps_of_grows {A : Addr → Prop} {σ σ' : State} (h : Grows σ σ') : Keeps A σ σ' :=
  ⟨h.1, fun y hy _ => h.2 y hy⟩

theorem keeps_refl (A : Addr → Prop) (σ : State) : Keeps A σ σ := ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

theorem keeps_trans {A : Addr → Prop} {σ1 σ2 σ3 : State} (h1 : Keeps A σ1 σ2) (h2 : Keeps A σ2 σ3) :
    Keeps A σ1 σ3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun y hy hA => by
    rw [h2.2 y (Nat.lt_of_lt_of_le hy h1.1) hA, h1.2 y hy hA]⟩

theorem keeps_setObj {A : Addr → Prop} {σ : State} {a : Addr} (o : Obj) (ha : A a) :
    Keeps A σ (σ.setObj a o) :=
  ⟨Nat.le_of_eq (State.next_setObj σ a o).symm, fun y _ hy => by
    have hne : y ≠ a := fun e => hy (by rw [e]; exact ha)
    rw [State.heap_setObj, if_neg hne]⟩

theorem keeps_alloc (A : Addr → Prop) (σ : State) (o : Obj) : Keeps A σ (σ.alloc o).2 :=
  keeps_of_grows ⟨by rw [State.next_alloc]; exact Nat.le_succ _, fun y hy => State.heap_alloc_of_lt hy o⟩

/-- No address of `A` holds, in `σ`, an object of class `c` or a non-plain object. -/
def Away (A : Addr → Prop) (σ : State) (cs : List ClassName) : Prop :=
  ∀ y, A y → ∃ c fs, σ.heap y = some (.plain c fs) ∧ c ∉ cs

theorem Away.mono {A : Addr → Prop} {σ : State} {cs cs' : List ClassName} (h : Away A σ cs)
    (hs : ∀ c ∈ cs', c ∈ cs) : Away A σ cs' := fun y hy => by
  obtain ⟨c, fs, h1, h2⟩ := h y hy
  exact ⟨c, fs, h1, fun hc => h2 (hs c hc)⟩

theorem not_A_of_heap {A : Addr → Prop} {σ : State} {cs : List ClassName} (h : Away A σ cs) {y : Addr}
    {o : Obj} (hy : σ.heap y = some o) (ho : ∀ c fs, o = .plain c fs → c ∈ cs) : ¬ A y := fun hA => by
  obtain ⟨c, fs, h1, h2⟩ := h y hA
  rw [hy] at h1
  exact h2 (ho c fs (Option.some.inj h1))

theorem heap_keeps {A : Addr → Prop} {σ σ' : State} (hk : Keeps A σ σ') {y : Addr} {o : Obj}
    (hy : σ.heap y = some o) (hA : ¬ A y) : σ'.heap y = some o := by
  rw [hk.2 y (State.lt_next_of_heap hy) hA, hy]

theorem jstrAt_keeps {A : Addr → Prop} {σ σ' : State} {cs : List ClassName} (hk : Keeps A σ σ')
    (ha : Away A σ cs) {v : Value} {s : JStr} (h : JStrAt σ v s) : JStrAt σ' v s := by
  obtain ⟨x, rfl, hx⟩ := h
  exact ⟨x, rfl, heap_keeps hk hx (not_A_of_heap ha hx (fun _ _ e => by cases e))⟩

theorem jFieldAt_keeps {A : Addr → Prop} {σ σ' : State} {cs : List ClassName} (hk : Keeps A σ σ')
    (ha : Away A σ cs) {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field} {v : EquivLean.Cobol.Rec.FVal}
    (h : jFieldAt σ cls fs f v) : jFieldAt σ' cls fs f v := by
  cases v with
  | num n => exact h
  | str bs => obtain ⟨s, h1, h2⟩ := h; exact ⟨s, h1, jstrAt_keeps hk ha h2⟩

theorem forall2_imp {α β : Type} {R R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b) :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 → Forall2 R' l1 l2
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (hR _ _ h) (forall2_imp hR hs)

theorem jRecAt_keeps {A : Addr → Prop} {σ σ' : State} {cls : ClassName} (hk : Keeps A σ σ')
    (ha : Away A σ [cls]) {S : Schema} {v : Value} {vals : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt S cls σ v vals) : JRecAt S cls σ' v vals := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := h
  exact ⟨x, fs, rfl, heap_keeps hk hx (not_A_of_heap ha hx (fun _ _ e => by cases e; exact List.mem_singleton_self _)),
    forall2_imp (fun _ _ h => jFieldAt_keeps hk ha h) hf⟩

theorem fileAtM_keeps {A : Addr → Prop} {σ σ' : State} {cls rcls : ClassName} (hk : Keeps A σ σ')
    (ha : Away A σ [cls, rcls]) {S : Schema} {v : Value} {f : Model.FileM}
    (h : FileAtM cls rcls S σ v f) : FileAtM cls rcls S σ' v f := by
  obtain ⟨o, fs, l, et, xs, rfl, ho, h1, h2, hl, hlen, hr, hp, h3, h4⟩ := h
  refine ⟨o, fs, l, et, xs, rfl,
    heap_keeps hk ho (not_A_of_heap ha ho (fun _ _ e => by cases e; simp)), h1, h2,
    heap_keeps hk hl (not_A_of_heap ha hl (fun _ _ e => by cases e)), hlen,
    forall2_imp (fun _ _ h => jRecAt_keeps hk (ha.mono (fun c hc => by simp at hc; simp [hc])) h) hr,
    hp, h3, h4⟩

theorem envAtM_keeps {A : Addr → Prop} {σ σ' : State} {cs : List ClassName} (hk : Keeps A σ σ')
    (ha : Away A σ cs) {oe : Addr} {oeM : Model.OpenErrs} (h : EnvAtM σ oe oeM) : EnvAtM σ' oe oeM := by
  obtain ⟨et, xs, hoe, hlen, hx⟩ := h
  refine ⟨et, xs, heap_keeps hk hoe (not_A_of_heap ha hoe (fun _ _ e => by cases e)), hlen, fun i hi => ?_⟩
  rcases hx i hi with h | ⟨o, c, h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr ⟨o, c, h1, heap_keeps hk h2 (not_A_of_heap ha h2 (fun _ _ e => by cases e)), h3, h4⟩

theorem notRecOf_keeps {A : Addr → Prop} {σ σ' : State} {k rcls : ClassName} (hk : Keeps A σ σ')
    (ha : Away A σ [k]) {S : Schema} {f : Model.FileM} {x y : Value} (hf : FileAtM k rcls S σ y f)
    (h : NotRecOf σ k x y) : NotRecOf σ' k x y := by
  obtain ⟨o, fs, l, et, xs, rfl, ho, -, h2, hl, -⟩ := hf
  intro o' fs' l' et' xs' hy ho' hl' hlh'
  cases hy
  rw [heap_keeps hk ho (not_A_of_heap ha ho (fun _ _ e => by cases e; simp))] at ho'
  cases ho'
  rw [h2] at hl'
  cases hl'
  rw [heap_keeps hk hl (not_A_of_heap ha hl (fun _ _ e => by cases e))] at hlh'
  cases hlh'
  exact h o fs l et xs rfl ho h2 hl

/-! ## The state object, one file at a time -/

/-- The parts of `StateAtM` for one file: the file (field `fk` of the State object), its FD record area (field
`rk`), its status (field `sk`). -/
def Part (fk rk sk : String) (fcls rcls : ClassName) (S : Schema) (σ : State) (fs : List (FieldKey × Value))
    (f : Model.FileM) (r : List EquivLean.Cobol.Rec.FVal) (c : List Nat) : Prop :=
  (∃ x, Fields.get fs ("Cbstm03b$State", fk) = some x ∧ FileAtM fcls rcls S σ x f) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", rk) = some x ∧ JRecAt S rcls σ x r) ∧
    (∃ x, Fields.get fs ("Cbstm03b$State", sk) = some x ∧ JStrAt σ x (cp037Str (c.map ebcdicOfLatin1)))

abbrev PartT := Part "trnxFile" "fdTrnxfileRec" "trnxfileStatus" "Cbstm03b$TrnxFile" "Cbstm03b$FdTrnxfileRec"
  FdTrnxfileRec
abbrev PartX := Part "xrefFile" "fdXreffileRec" "xreffileStatus" "Cbstm03b$XrefFile" "Cbstm03b$FdXreffileRec"
  FdXreffileRec
abbrev PartC := Part "custFile" "fdCustfileRec" "custfileStatus" "Cbstm03b$CustFile" "Cbstm03b$FdCustfileRec"
  FdCustfileRec
abbrev PartA := Part "acctFile" "fdAcctfileRec" "acctfileStatus" "Cbstm03b$AcctFile" "Cbstm03b$FdAcctfileRec"
  FdAcctfileRec

theorem stateAtM_iff {σ : State} {st : Addr} {s : Model.StM} :
    StateAtM σ st s ↔ ∃ fs, σ.heap st = some (.plain "Cbstm03b$State" fs) ∧
      PartT σ fs s.trnx s.trnxRec s.trnxSt ∧ PartX σ fs s.xref s.xrefRec s.xrefSt ∧
      PartC σ fs s.cust s.custRec s.custSt ∧ PartA σ fs s.acct s.acctRec s.acctSt := by
  constructor
  · rintro ⟨fs, hst, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4⟩
    exact ⟨fs, hst, ⟨a1, b1, c1⟩, ⟨a2, b2, c2⟩, ⟨a3, b3, c3⟩, ⟨a4, b4, c4⟩⟩
  · rintro ⟨fs, hst, ⟨a1, b1, c1⟩, ⟨a2, b2, c2⟩, ⟨a3, b3, c3⟩, ⟨a4, b4, c4⟩⟩
    exact ⟨fs, hst, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4⟩

/-- A part read from another field list that agrees on the part's three keys. -/
theorem Part.fields {fk rk sk : String} {fcls rcls : ClassName} {S : Schema} {σ : State}
    {fs fs' : List (FieldKey × Value)} {f : Model.FileM} {r : List EquivLean.Cobol.Rec.FVal} {c : List Nat}
    (h : Part fk rk sk fcls rcls S σ fs f r c)
    (h1 : Fields.get fs' ("Cbstm03b$State", fk) = Fields.get fs ("Cbstm03b$State", fk))
    (h2 : Fields.get fs' ("Cbstm03b$State", rk) = Fields.get fs ("Cbstm03b$State", rk))
    (h3 : Fields.get fs' ("Cbstm03b$State", sk) = Fields.get fs ("Cbstm03b$State", sk)) :
    Part fk rk sk fcls rcls S σ fs' f r c := by
  obtain ⟨⟨x1, g1, m1⟩, ⟨x2, g2, m2⟩, ⟨x3, g3, m3⟩⟩ := h
  exact ⟨⟨x1, by rw [h1, g1], m1⟩, ⟨x2, by rw [h2, g2], m2⟩, ⟨x3, by rw [h3, g3], m3⟩⟩

/-- A part in a heap that keeps its objects (none of the updated objects is of the part's classes). -/
theorem Part.keeps {fk rk sk : String} {fcls rcls : ClassName} {S : Schema} {σ σ' : State}
    {fs : List (FieldKey × Value)} {f : Model.FileM} {r : List EquivLean.Cobol.Rec.FVal} {c : List Nat}
    {A : Addr → Prop} (hk : Keeps A σ σ') (ha : Away A σ [fcls, rcls])
    (h : Part fk rk sk fcls rcls S σ fs f r c) : Part fk rk sk fcls rcls S σ' fs f r c := by
  obtain ⟨⟨x1, g1, m1⟩, ⟨x2, g2, m2⟩, ⟨x3, g3, m3⟩⟩ := h
  exact ⟨⟨x1, g1, fileAtM_keeps hk ha m1⟩,
    ⟨x2, g2, jRecAt_keeps hk (ha.mono (fun c hc => by simp at hc; simp [hc])) m2⟩,
    ⟨x3, g3, jstrAt_keeps hk ha m3⟩⟩

theorem Part.grows {fk rk sk : String} {fcls rcls : ClassName} {S : Schema} {σ σ' : State}
    {fs : List (FieldKey × Value)} {f : Model.FileM} {r : List EquivLean.Cobol.Rec.FVal} {c : List Nat}
    (hg : Grows σ σ') (h : Part fk rk sk fcls rcls S σ fs f r c) : Part fk rk sk fcls rcls S σ' fs f r c :=
  Part.keeps (A := fun _ => False) (keeps_of_grows hg) (fun _ h => h.elim) h

theorem stateAtM_grows {σ σ' : State} {st : Addr} {s : Model.StM} (h : StateAtM σ st s) (hg : Grows σ σ') :
    StateAtM σ' st s := by
  obtain ⟨fs, hst, p1, p2, p3, p4⟩ := stateAtM_iff.1 h
  exact stateAtM_iff.2 ⟨fs, heap_grows hg hst, p1.grows hg, p2.grows hg, p3.grows hg, p4.grows hg⟩

theorem jRecAt_grows {σ σ' : State} {S : Schema} {cls : ClassName} {v : Value}
    {vals : List EquivLean.Cobol.Rec.FVal} (h : JRecAt S cls σ v vals) (hg : Grows σ σ') :
    JRecAt S cls σ' v vals :=
  jRecAt_keeps (A := fun _ => False) (keeps_of_grows hg) (fun _ h => h.elim) h

theorem jstrAt_grows {σ σ' : State} {v : Value} {s : JStr} (h : JStrAt σ v s) (hg : Grows σ σ') :
    JStrAt σ' v s :=
  jstrAt_keeps (A := fun _ => False) (cs := []) (keeps_of_grows hg) (fun _ h => h.elim) h

theorem envAtM_grows {σ σ' : State} {oe : Addr} {oeM : Model.OpenErrs} (h : EnvAtM σ oe oeM)
    (hg : Grows σ σ') : EnvAtM σ' oe oeM :=
  envAtM_keeps (A := fun _ => False) (cs := []) (keeps_of_grows hg) (fun _ h => h.elim) h

/-- `SepM` in a heap that keeps the files of CUSTFILE and ACCTFILE, for a State field list that agrees on the four
keys `SepM` reads. -/
theorem sepM_keeps {σ σ' : State} {st : Addr} {s : Model.StM} {A : Addr → Prop} {fs' : List (FieldKey × Value)}
    (hs : StateAtM σ st s) (hsep : SepM σ st) (hk : Keeps A σ σ')
    (ha : Away A σ ["Cbstm03b$CustFile", "Cbstm03b$AcctFile"])
    (hst' : σ'.heap st = some (.plain "Cbstm03b$State" fs'))
    (hfs : ∀ fs, σ.heap st = some (.plain "Cbstm03b$State" fs) →
      Fields.get fs' ("Cbstm03b$State", "fdCustfileRec") = Fields.get fs ("Cbstm03b$State", "fdCustfileRec") ∧
      Fields.get fs' ("Cbstm03b$State", "custFile") = Fields.get fs ("Cbstm03b$State", "custFile") ∧
      Fields.get fs' ("Cbstm03b$State", "fdAcctfileRec") = Fields.get fs ("Cbstm03b$State", "fdAcctfileRec") ∧
      Fields.get fs' ("Cbstm03b$State", "acctFile") = Fields.get fs ("Cbstm03b$State", "acctFile")) :
    SepM σ' st := by
  obtain ⟨fs, hst, -, -, ⟨⟨y3, g3, m3⟩, -, -⟩, ⟨⟨y4, g4, m4⟩, -, -⟩⟩ := stateAtM_iff.1 hs
  obtain ⟨fs0, hst0, c1, c2⟩ := hsep
  rw [hst] at hst0
  cases hst0
  obtain ⟨e1, e2, e3, e4⟩ := hfs fs hst
  refine ⟨fs', hst', fun x y hx hy => ?_, fun x y hx hy => ?_⟩
  · rw [e1] at hx
    rw [e2] at hy
    rw [g3] at hy
    cases hy
    exact notRecOf_keeps hk (ha.mono (fun c hc => by simp at hc; simp [hc])) m3 (c1 x y3 hx g3)
  · rw [e3] at hx
    rw [e4] at hy
    rw [g4] at hy
    cases hy
    exact notRecOf_keeps hk (ha.mono (fun c hc => by simp at hc; simp [hc])) m4 (c2 x y4 hx g4)

theorem sepM_grows {σ σ' : State} {st : Addr} {s : Model.StM} (hs : StateAtM σ st s) (hsep : SepM σ st)
    (hg : Grows σ σ') : SepM σ' st := by
  obtain ⟨fs, hst, -⟩ := id hs
  exact sepM_keeps (A := fun _ => False) hs hsep (keeps_of_grows hg) (fun _ h => h.elim) (heap_grows hg hst)
    (fun fs0 h0 => by rw [hst] at h0; cases h0; exact ⟨rfl, rfl, rfl, rfl⟩)

/-! ## CP037 -/

theorem latin_lt_fin : ∀ n : Fin 256, latin1OfEbcdic (UInt8.ofNat n.val) < 256 := by decide +kernel

theorem latin_lt (b : UInt8) : latin1OfEbcdic b < 256 := by
  have h := latin_lt_fin ⟨b.toNat, b.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at h
  exact h

theorem cp037Unit_eq (b : UInt8) : cp037Unit b = BitVec.ofNat 16 (latin1OfEbcdic b) := rfl

/-- CP037 is injective. -/
theorem cp037Unit_inj {b b' : UInt8} (h : cp037Unit b = cp037Unit b') : b = b' := by
  have h1 := latin_lt b
  have h2 := latin_lt b'
  have e := congrArg BitVec.toNat h
  rw [cp037Unit_eq, cp037Unit_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at e
  have e' : latin1OfEbcdic b = latin1OfEbcdic b' := by omega
  rw [← latin_rt b, ← latin_rt b', e']

theorem cp037Str_inj : ∀ {bs bs' : List UInt8}, cp037Str bs = cp037Str bs' → bs = bs'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [cp037Str] at h
  | _ :: _, [], h => by simp [cp037Str] at h
  | b :: bs, b' :: bs', h => by
    simp only [cp037Str, List.map_cons, List.cons.injEq] at h
    rw [cp037Unit_inj h.1, cp037Str_inj (bs := bs) (bs' := bs') h.2]

theorem cp037Str_eq_iff {bs bs' : List UInt8} : cp037Str bs = cp037Str bs' ↔ bs = bs' :=
  ⟨cp037Str_inj, fun h => h ▸ rfl⟩

theorem cp037Str_length (bs : List UInt8) : (cp037Str bs).length = bs.length := List.length_map _

theorem cp037Str_append (bs bs' : List UInt8) : cp037Str (bs ++ bs') = cp037Str bs ++ cp037Str bs' :=
  List.map_append

theorem cp037Str_take (bs : List UInt8) (k : Nat) : cp037Str (bs.take k) = (cp037Str bs).take k :=
  List.map_take

theorem cp037_digit_fin : ∀ d : Fin 10, cp037Unit (UInt8.ofNat (240 + d.val)) = digitChar d.val := by
  decide +kernel

theorem cp037_digit {d : Nat} (h : d < 10) : cp037Unit (UInt8.ofNat (240 + d)) = digitChar d :=
  cp037_digit_fin ⟨d, h⟩

theorem cp037_space : cp037Unit 64 = space := by decide +kernel

theorem cp037_replicate_space (n : Nat) : cp037Str (List.replicate n 64) = List.replicate n space := by
  simp only [cp037Str, List.map_replicate]
  rw [cp037_space]

/-- The text of a status's bytes: its two digits. -/
theorem stBytes_text (c : Nat) : cp037Str (stBytes c) = stChars c := by
  simp only [stBytes, cp037Str, List.map_cons, List.map_nil, stChars]
  rw [cp037_digit (Nat.mod_lt _ (by decide)), cp037_digit (Nat.mod_lt _ (by decide))]

/-- The text of a status item (code points mapped to EBCDIC): its two digits. -/
theorem status_text (c : Nat) : cp037Str ((Model.stCp c).map ebcdicOfLatin1) = stChars c := by
  rw [Glue.stCp_map, stBytes_text]

theorem dd_texts : cp037Str ddTrnx = JStr.ofString "TRNXFILE" ∧ cp037Str ddXref = JStr.ofString "XREFFILE" ∧
    cp037Str ddCust = JStr.ofString "CUSTFILE" ∧ cp037Str ddAcct = JStr.ofString "ACCTFILE" := by
  decide +kernel

theorem op_texts : cp037Str [opOpen] = JStr.ofString "O" ∧ cp037Str [opRead] = JStr.ofString "R" ∧
    cp037Str [opReadK] = JStr.ofString "K" ∧ cp037Str [opClose] = JStr.ofString "C" := by
  decide +kernel

/-- `intoBuf`'s text: the record's text, space-padded to 1000. -/
theorem intoBuf_text {bs : List UInt8} (h : bs.length ≤ 1000) :
    cp037Str (intoBuf bs) = fixStr (cp037Str bs) 1000 := by
  rw [fixStr_eq_append (by rw [cp037Str_length]; exact h), intoBuf, cp037Str_append, cp037_replicate_space,
    cp037Str_length]

/-! ## Record objects, field by field -/

theorem forall2_cons_left {α β : Type} {R : α → β → Prop} {a : α} {al : List α} {l : List β}
    (h : Forall2 R (a :: al) l) : ∃ b bs, l = b :: bs ∧ R a b ∧ Forall2 R al bs := by
  cases h with
  | cons h1 h2 => exact ⟨_, _, rfl, h1, h2⟩

theorem forall2_nil_left {α β : Type} {R : α → β → Prop} {l : List β} (h : Forall2 R ([] : List α) l) :
    l = [] := by
  cases h
  rfl

theorem forall2_cons_inv {α β : Type} {R : α → β → Prop} {a : α} {al : List α} {b : β} {bs : List β}
    (h : Forall2 R (a :: al) (b :: bs)) : R a b ∧ Forall2 R al bs := by
  cases h with
  | cons h1 h2 => exact ⟨h1, h2⟩

theorem str_field_of {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {v : EquivLean.Cobol.Rec.FVal} (hk : ∃ j, f.desc.kind = .alnum j) (hv : f.Valid v)
    (h : jFieldAt σ cls fs f v) :
    ∃ bs s, v = .str bs ∧ bs.length = f.desc.len ∧ Fields.get fs (cls, f.jname) = some s ∧
      JStrAt σ s (cp037Str bs) := by
  cases v with
  | num n =>
    obtain ⟨fmt, hk', -⟩ := hv
    obtain ⟨j, hj⟩ := hk
    rw [hj] at hk'
    cases hk'
  | str bs =>
    obtain ⟨-, hl⟩ := hv
    obtain ⟨s, h1, h2⟩ := h
    exact ⟨bs, s, rfl, hl, h1, h2⟩

theorem num_field_of {σ : State} {cls : ClassName} {fs : List (FieldKey × Value)} {f : Field}
    {fmt : Cobol.NumFmt} {v : EquivLean.Cobol.Rec.FVal} (hk : f.desc.kind = .num fmt) (hv : f.Valid v)
    (h : jFieldAt σ cls fs f v) :
    ∃ n, v = .num n ∧ fmt.Holds {} n ∧ Fields.get fs (cls, f.jname) = some (.long (BitVec.ofInt 64 n)) := by
  cases v with
  | num n =>
    obtain ⟨fmt', hk', -, -, hh, -⟩ := hv
    rw [hk] at hk'
    cases hk'
    exact ⟨n, rfl, hh, h⟩
  | str bs =>
    obtain ⟨⟨j, hj⟩, -⟩ := hv
    rw [hk] at hj
    cases hj

theorem holds_display {d : Nat} {s : Bool} {n : Int}
    (h : Cobol.NumFmt.Holds {} ⟨d, 0, s, .display, false, false⟩ n) :
    (n.natAbs : Int) < 10 ^ d ∧ (s = false → 0 ≤ n) := by
  simp only [Cobol.NumFmt.Holds, Cobol.NumFmt.fullBinary, Bool.false_eq_true, if_false] at h
  exact ⟨by exact_mod_cast h.1, h.2⟩

/-- A TRNXFILE record object. -/
theorem trnxRecAt_of {σ : State} {v : Value} {r : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt Model.FdTrnxfileRec "Cbstm03b$FdTrnxfileRec" σ v r) (hv : Model.FdTrnxfileRec.Valid r) :
    ∃ x fs c i d sc si sd, v = .ref x ∧ σ.heap x = some (.plain "Cbstm03b$FdTrnxfileRec" fs) ∧
      r = [.str c, .str i, .str d] ∧ c.length = 16 ∧ i.length = 16 ∧ d.length = 318 ∧
      Fields.get fs ("Cbstm03b$FdTrnxfileRec", "fdTrnxCard") = some sc ∧ JStrAt σ sc (cp037Str c) ∧
      Fields.get fs ("Cbstm03b$FdTrnxfileRec", "fdTrnxId") = some si ∧ JStrAt σ si (cp037Str i) ∧
      Fields.get fs ("Cbstm03b$FdTrnxfileRec", "fdAcctData") = some sd ∧ JStrAt σ sd (cp037Str d) := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := h
  obtain ⟨b1, l1, rfl, h1, hf⟩ := forall2_cons_left hf
  obtain ⟨b2, l2, rfl, h2, hf⟩ := forall2_cons_left hf
  obtain ⟨b3, l3, rfl, h3, hf⟩ := forall2_cons_left hf
  cases forall2_nil_left hf
  obtain ⟨v1, hv⟩ := forall2_cons_inv hv
  obtain ⟨v2, hv⟩ := forall2_cons_inv hv
  obtain ⟨v3, hv⟩ := forall2_cons_inv hv
  obtain ⟨c, sc, rfl, hc, g1, j1⟩ := str_field_of ⟨_, rfl⟩ v1 h1
  obtain ⟨i, si, rfl, hi, g2, j2⟩ := str_field_of ⟨_, rfl⟩ v2 h2
  obtain ⟨d, sd, rfl, hd, g3, j3⟩ := str_field_of ⟨_, rfl⟩ v3 h3
  exact ⟨x, fs, c, i, d, sc, si, sd, rfl, hx, rfl, hc, hi, hd, g1, j1, g2, j2, g3, j3⟩

/-- An XREFFILE record object. -/
theorem xrefRecAt_of {σ : State} {v : Value} {r : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt Model.FdXreffileRec "Cbstm03b$FdXreffileRec" σ v r) (hv : Model.FdXreffileRec.Valid r) :
    ∃ x fs c d sc sd, v = .ref x ∧ σ.heap x = some (.plain "Cbstm03b$FdXreffileRec" fs) ∧
      r = [.str c, .str d] ∧ c.length = 16 ∧ d.length = 34 ∧
      Fields.get fs ("Cbstm03b$FdXreffileRec", "fdXrefCardNum") = some sc ∧ JStrAt σ sc (cp037Str c) ∧
      Fields.get fs ("Cbstm03b$FdXreffileRec", "fdXrefData") = some sd ∧ JStrAt σ sd (cp037Str d) := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := h
  obtain ⟨b1, l1, rfl, h1, hf⟩ := forall2_cons_left hf
  obtain ⟨b2, l2, rfl, h2, hf⟩ := forall2_cons_left hf
  cases forall2_nil_left hf
  obtain ⟨v1, hv⟩ := forall2_cons_inv hv
  obtain ⟨v2, hv⟩ := forall2_cons_inv hv
  obtain ⟨c, sc, rfl, hc, g1, j1⟩ := str_field_of ⟨_, rfl⟩ v1 h1
  obtain ⟨d, sd, rfl, hd, g2, j2⟩ := str_field_of ⟨_, rfl⟩ v2 h2
  exact ⟨x, fs, c, d, sc, sd, rfl, hx, rfl, hc, hd, g1, j1, g2, j2⟩

/-- A CUSTFILE record object. -/
theorem custRecAt_of {σ : State} {v : Value} {r : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt Model.FdCustfileRec "Cbstm03b$FdCustfileRec" σ v r) (hv : Model.FdCustfileRec.Valid r) :
    ∃ x fs c d sc sd, v = .ref x ∧ σ.heap x = some (.plain "Cbstm03b$FdCustfileRec" fs) ∧
      r = [.str c, .str d] ∧ c.length = 9 ∧ d.length = 491 ∧
      Fields.get fs ("Cbstm03b$FdCustfileRec", "fdCustId") = some sc ∧ JStrAt σ sc (cp037Str c) ∧
      Fields.get fs ("Cbstm03b$FdCustfileRec", "fdCustData") = some sd ∧ JStrAt σ sd (cp037Str d) := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := h
  obtain ⟨b1, l1, rfl, h1, hf⟩ := forall2_cons_left hf
  obtain ⟨b2, l2, rfl, h2, hf⟩ := forall2_cons_left hf
  cases forall2_nil_left hf
  obtain ⟨v1, hv⟩ := forall2_cons_inv hv
  obtain ⟨v2, hv⟩ := forall2_cons_inv hv
  obtain ⟨c, sc, rfl, hc, g1, j1⟩ := str_field_of ⟨_, rfl⟩ v1 h1
  obtain ⟨d, sd, rfl, hd, g2, j2⟩ := str_field_of ⟨_, rfl⟩ v2 h2
  exact ⟨x, fs, c, d, sc, sd, rfl, hx, rfl, hc, hd, g1, j1, g2, j2⟩

/-- An ACCTFILE record object: `fdAcctId` a `long` holding `0 ≤ n < 10 ^ 11`. -/
theorem acctRecAt_of {σ : State} {v : Value} {r : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt Model.FdAcctfileRec "Cbstm03b$FdAcctfileRec" σ v r) (hv : Model.FdAcctfileRec.Valid r) :
    ∃ x fs n d sd, v = .ref x ∧ σ.heap x = some (.plain "Cbstm03b$FdAcctfileRec" fs) ∧
      r = [.num n, .str d] ∧ 0 ≤ n ∧ n < 100000000000 ∧ d.length = 289 ∧
      Fields.get fs ("Cbstm03b$FdAcctfileRec", "fdAcctId") = some (.long (BitVec.ofInt 64 n)) ∧
      Fields.get fs ("Cbstm03b$FdAcctfileRec", "fdAcctData") = some sd ∧ JStrAt σ sd (cp037Str d) := by
  obtain ⟨x, fs, rfl, hx, hf⟩ := h
  obtain ⟨b1, l1, rfl, h1, hf⟩ := forall2_cons_left hf
  obtain ⟨b2, l2, rfl, h2, hf⟩ := forall2_cons_left hf
  cases forall2_nil_left hf
  obtain ⟨v1, hv⟩ := forall2_cons_inv hv
  obtain ⟨v2, hv⟩ := forall2_cons_inv hv
  obtain ⟨n, rfl, hn, g1⟩ := num_field_of rfl v1 h1
  obtain ⟨d, sd, rfl, hd, g2, j2⟩ := str_field_of ⟨_, rfl⟩ v2 h2
  obtain ⟨hn1, hn2⟩ := holds_display hn
  have hn3 := hn2 rfl
  exact ⟨x, fs, n, d, sd, rfl, hx, rfl, by omega, by omega, hd, g1, g2, j2⟩

/-- The area object: its six fields. -/
theorem areaAt_of {σ : State} {v : Value} {a : List EquivLean.Cobol.Rec.FVal}
    (h : JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ v a) (hv : Model.LkM03bArea.Valid a) :
    ∃ q fs dd op rc key kl fldt sdd sop src skey sfl, v = .ref q ∧
      σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fs) ∧
      a = [.str dd, .str op, .str rc, .str key, .num kl, .str fldt] ∧
      dd.length = 8 ∧ op.length = 1 ∧ rc.length = 2 ∧ key.length = 25 ∧ -10000 < kl ∧ kl < 10000 ∧
      fldt.length = 1000 ∧
      Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bDd") = some sdd ∧ JStrAt σ sdd (cp037Str dd) ∧
      Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bOper") = some sop ∧ JStrAt σ sop (cp037Str op) ∧
      Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bRc") = some src ∧ JStrAt σ src (cp037Str rc) ∧
      Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bKey") = some skey ∧ JStrAt σ skey (cp037Str key) ∧
      Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bKeyLn") = some (.long (BitVec.ofInt 64 kl)) ∧
      Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bFldt") = some sfl ∧ JStrAt σ sfl (cp037Str fldt) := by
  obtain ⟨q, fs, rfl, hq, hf⟩ := h
  obtain ⟨b1, l1, rfl, h1, hf⟩ := forall2_cons_left hf
  obtain ⟨b2, l2, rfl, h2, hf⟩ := forall2_cons_left hf
  obtain ⟨b3, l3, rfl, h3, hf⟩ := forall2_cons_left hf
  obtain ⟨b4, l4, rfl, h4, hf⟩ := forall2_cons_left hf
  obtain ⟨b5, l5, rfl, h5, hf⟩ := forall2_cons_left hf
  obtain ⟨b6, l6, rfl, h6, hf⟩ := forall2_cons_left hf
  cases forall2_nil_left hf
  obtain ⟨v1, hv⟩ := forall2_cons_inv hv
  obtain ⟨v2, hv⟩ := forall2_cons_inv hv
  obtain ⟨v3, hv⟩ := forall2_cons_inv hv
  obtain ⟨v4, hv⟩ := forall2_cons_inv hv
  obtain ⟨v5, hv⟩ := forall2_cons_inv hv
  obtain ⟨v6, hv⟩ := forall2_cons_inv hv
  obtain ⟨dd, sdd, rfl, l1, g1, j1⟩ := str_field_of ⟨_, rfl⟩ v1 h1
  obtain ⟨op, sop, rfl, l2, g2, j2⟩ := str_field_of ⟨_, rfl⟩ v2 h2
  obtain ⟨rc, src, rfl, l3, g3, j3⟩ := str_field_of ⟨_, rfl⟩ v3 h3
  obtain ⟨key, skey, rfl, l4, g4, j4⟩ := str_field_of ⟨_, rfl⟩ v4 h4
  obtain ⟨kl, rfl, hn, g5⟩ := num_field_of rfl v5 h5
  obtain ⟨fldt, sfl, rfl, l6, g6, j6⟩ := str_field_of ⟨_, rfl⟩ v6 h6
  obtain ⟨hn1, hn2⟩ := holds_display hn
  exact ⟨q, fs, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, rfl, hq, rfl, l1, l2, l3, l4,
    by omega, by omega, l6, g1, j1, g2, j2, g3, j3, g4, j4, g5, g6, j6⟩

/-- An area object from its six fields. -/
theorem areaAt_mk {σ : State} {q : Addr} {fs : List (FieldKey × Value)} {dd op rc key fldt : List UInt8}
    {kl : Int} {sdd sop src skey sfl : Value} (hq : σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fs))
    (g1 : Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bDd") = some sdd) (j1 : JStrAt σ sdd (cp037Str dd))
    (g2 : Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bOper") = some sop) (j2 : JStrAt σ sop (cp037Str op))
    (g3 : Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bRc") = some src) (j3 : JStrAt σ src (cp037Str rc))
    (g4 : Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bKey") = some skey) (j4 : JStrAt σ skey (cp037Str key))
    (g5 : Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bKeyLn") = some (.long (BitVec.ofInt 64 kl)))
    (g6 : Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bFldt") = some sfl) (j6 : JStrAt σ sfl (cp037Str fldt)) :
    JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ (.ref q) [.str dd, .str op, .str rc, .str key, .num kl, .str fldt] :=
  ⟨q, fs, rfl, hq, .cons ⟨sdd, g1, j1⟩ (.cons ⟨sop, g2, j2⟩ (.cons ⟨src, g3, j3⟩ (.cons ⟨skey, g4, j4⟩
    (.cons g5 (.cons ⟨sfl, g6, j6⟩ .nil)))))⟩

theorem trnxRecAt_mk {σ : State} {x : Addr} {fs : List (FieldKey × Value)} {c i d : List UInt8}
    {sc si sd : Value} (hx : σ.heap x = some (.plain "Cbstm03b$FdTrnxfileRec" fs))
    (g1 : Fields.get fs ("Cbstm03b$FdTrnxfileRec", "fdTrnxCard") = some sc) (j1 : JStrAt σ sc (cp037Str c))
    (g2 : Fields.get fs ("Cbstm03b$FdTrnxfileRec", "fdTrnxId") = some si) (j2 : JStrAt σ si (cp037Str i))
    (g3 : Fields.get fs ("Cbstm03b$FdTrnxfileRec", "fdAcctData") = some sd) (j3 : JStrAt σ sd (cp037Str d)) :
    JRecAt Model.FdTrnxfileRec "Cbstm03b$FdTrnxfileRec" σ (.ref x) [.str c, .str i, .str d] :=
  ⟨x, fs, rfl, hx, .cons ⟨sc, g1, j1⟩ (.cons ⟨si, g2, j2⟩ (.cons ⟨sd, g3, j3⟩ .nil))⟩

theorem xrefRecAt_mk {σ : State} {x : Addr} {fs : List (FieldKey × Value)} {c d : List UInt8}
    {sc sd : Value} (hx : σ.heap x = some (.plain "Cbstm03b$FdXreffileRec" fs))
    (g1 : Fields.get fs ("Cbstm03b$FdXreffileRec", "fdXrefCardNum") = some sc) (j1 : JStrAt σ sc (cp037Str c))
    (g2 : Fields.get fs ("Cbstm03b$FdXreffileRec", "fdXrefData") = some sd) (j2 : JStrAt σ sd (cp037Str d)) :
    JRecAt Model.FdXreffileRec "Cbstm03b$FdXreffileRec" σ (.ref x) [.str c, .str d] :=
  ⟨x, fs, rfl, hx, .cons ⟨sc, g1, j1⟩ (.cons ⟨sd, g2, j2⟩ .nil)⟩

theorem custRecAt_mk {σ : State} {x : Addr} {fs : List (FieldKey × Value)} {c d : List UInt8}
    {sc sd : Value} (hx : σ.heap x = some (.plain "Cbstm03b$FdCustfileRec" fs))
    (g1 : Fields.get fs ("Cbstm03b$FdCustfileRec", "fdCustId") = some sc) (j1 : JStrAt σ sc (cp037Str c))
    (g2 : Fields.get fs ("Cbstm03b$FdCustfileRec", "fdCustData") = some sd) (j2 : JStrAt σ sd (cp037Str d)) :
    JRecAt Model.FdCustfileRec "Cbstm03b$FdCustfileRec" σ (.ref x) [.str c, .str d] :=
  ⟨x, fs, rfl, hx, .cons ⟨sc, g1, j1⟩ (.cons ⟨sd, g2, j2⟩ .nil)⟩

theorem acctRecAt_mk {σ : State} {x : Addr} {fs : List (FieldKey × Value)} {n : Int} {d : List UInt8}
    {sd : Value} (hx : σ.heap x = some (.plain "Cbstm03b$FdAcctfileRec" fs))
    (g1 : Fields.get fs ("Cbstm03b$FdAcctfileRec", "fdAcctId") = some (.long (BitVec.ofInt 64 n)))
    (g2 : Fields.get fs ("Cbstm03b$FdAcctfileRec", "fdAcctData") = some sd) (j2 : JStrAt σ sd (cp037Str d)) :
    JRecAt Model.FdAcctfileRec "Cbstm03b$FdAcctfileRec" σ (.ref x) [.num n, .str d] :=
  ⟨x, fs, rfl, hx, .cons g1 (.cons ⟨sd, g2, j2⟩ .nil)⟩

/-! ## Contracts with the ghost values as parameters

`procSpec` and `runSpec` quantify their ghost values existentially in the precondition and universally in the
postcondition. Proving the contract for every fixed choice of ghost values (`procSpecG`, `runSpecG`) gives it: the
postcondition for another choice whose facts hold is that choice's contract. -/

/-- `procSpec dd` for fixed ghost values. -/
def procSpecG (dd : List UInt8) (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) : Spec := Spec.of
  (fun args σ => args = [.ref oe, .ref st, .ref q, opv] ∧ EnvAtM σ oe oeM ∧ StateAtM σ st s ∧ SepM σ st ∧
     JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ (.ref q) a ∧ Glue.ValidSt s ∧ Model.LkM03bArea.Valid a ∧
     Glue.KeyOk a ∧ Model.aDd a = dd ∧ OpAt σ q opv ∧ InitsDone σ)
  (fun _ _ r σ' => r = none ∧ StateAtM σ' st (Model.call oeM s a).1 ∧ SepM σ' st ∧
     JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ' (.ref q) (Model.call oeM s a).2)

theorem procSpec_of_ghost {P : Program} {m : MethodRef} {dd : List UInt8}
    (h : ∀ oe st q opv oeM s a, Sat P m (procSpecG dd oe st q opv oeM s a)) : Sat P m (procSpec dd) := by
  intro args σ o hpre hm
  obtain ⟨oe, st, q, opv, oeM, s, a, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpre
  cases o with
  | normal r σ' =>
    intro oe' st' q' opv' oeM' s' a' g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10
    exact h oe' st' q' opv' oeM' s' a' args σ (.normal r σ') ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ hm
  | exc e σ' =>
    exact (h oe st q opv oeM s a args σ (.exc e σ') ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ hm).elim
  | wrong msg =>
    exact (h oe st q opv oeM s a args σ (.wrong msg) ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ hm).elim

/-- `runSpec` for fixed ghost values. -/
def runSpecG (oe st q : Addr) (oeM : Model.OpenErrs) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal) :
    Spec := Spec.of
  (fun args σ => args = [.ref oe, .ref st, .ref q] ∧ EnvAtM σ oe oeM ∧ StateAtM σ st s ∧ SepM σ st ∧
     JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ (.ref q) a ∧ Glue.ValidSt s ∧ Model.LkM03bArea.Valid a ∧
     Glue.KeyOk a ∧ InitsDone σ)
  (fun _ _ r σ' => r = none ∧ StateAtM σ' st (Model.call oeM s a).1 ∧ SepM σ' st ∧
     JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ' (.ref q) (Model.call oeM s a).2)

theorem runSpec_of_ghost {P : Program} {m : MethodRef}
    (h : ∀ oe st q oeM s a, Sat P m (runSpecG oe st q oeM s a)) : Sat P m runSpec := by
  intro args σ o hpre hm
  obtain ⟨oe, st, q, oeM, s, a, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hpre
  cases o with
  | normal r σ' =>
    intro oe' st' q' oeM' s' a' g0 g1 g2 g3 g4 g5 g6 g7 g8
    exact h oe' st' q' oeM' s' a' args σ (.normal r σ') ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ hm
  | exc e σ' =>
    exact (h oe st q oeM s a args σ (.exc e σ') ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ hm).elim
  | wrong msg =>
    exact (h oe st q oeM s a args σ (.wrong msg) ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ hm).elim

/-- A contract from a stronger one (consequence rule). -/
theorem sat_conseq {P : Program} {m : MethodRef} {S S' : Spec} (h : Sat P m S)
    (hpre : ∀ args σ, S'.pre args σ → S.pre args σ)
    (hpost : ∀ args σ o, S'.pre args σ → S.post args σ o → S'.post args σ o) : Sat P m S' :=
  fun args σ o hp hm => hpost args σ o hp (h args σ o (hpre args σ hp) hm)

end EquivLean.Modernize.Cbstm03b.Java

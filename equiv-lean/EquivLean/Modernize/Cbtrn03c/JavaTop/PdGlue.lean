import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib2
import EquivLean.Modernize.Cbtrn03c.JavaTop.Glue1

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processDetail`, the model facts behind its cuts

The keyed lookups' indices (`findIdx`) against `List.find?`; the record objects of the input
files at an index; the model's `tranStep` along each path of `processDetail`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-! ## Indices of the keyed lookups -/

theorem findIdx_cases {α : Type} (p : α → Bool) (l : List α) :
    findIdx p l = -1 ∨ ∃ i : Nat, findIdx p l = (i : Int) := by
  unfold findIdx
  cases l.findIdx? p with
  | none => exact Or.inl rfl
  | some i => exact Or.inr ⟨i, rfl⟩

theorem findIdx_neg {α : Type} {p : α → Bool} {l : List α} (h : findIdx p l = -1) :
    l.find? p = none := by
  unfold findIdx at h
  cases hf : l.findIdx? p with
  | none =>
    rw [List.findIdx?_eq_none_iff] at hf
    rw [List.find?_eq_none]
    intro x hx
    simp [hf x hx]
  | some i =>
    rw [hf] at h
    dsimp only at h
    omega

theorem findIdx_nat {α : Type} {p : α → Bool} {l : List α} {i : Nat} (h : findIdx p l = (i : Int)) :
    ∃ hi : i < l.length, l.find? p = some (l[i]'hi) := by
  unfold findIdx at h
  cases hf : l.findIdx? p with
  | none =>
    rw [hf] at h
    dsimp only at h
    omega
  | some j =>
    rw [hf] at h
    dsimp only at h
    have hji : j = i := by omega
    subst hji
    rw [List.findIdx?_eq_some_iff_findIdx_eq] at hf
    obtain ⟨hlt, heq⟩ := hf
    refine ⟨hlt, ?_⟩
    rw [List.find?_eq_getElem?_findIdx, heq, List.getElem?_eq_getElem hlt]

/-! ## The record objects of the input files -/

/-- `Forall2` at an index. -/
theorem forall2_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ (i : Nat) (hx : i < xs.length)
      (hy : i < ys.length), R (xs[i]'hx) (ys[i]'hy)
  | [], [], .nil, _, hx, _ => absurd hx (by simp)
  | _ :: _, _ :: _, .cons h _, 0, _, _ => h
  | _ :: _, _ :: _, .cons _ hs, i + 1, hx, hy =>
    forall2_getElem hs i (by simpa using hx) (by simpa using hy)

/-- The cross-reference record object at index `i` of the file `a`, and its account id. -/
theorem xref_elem {σ : State} {a : Addr} {xs : Recs} (hf : XrefFileAt σ a xs)
    (hv : ∀ v ∈ xs, CardXrefRecord.Valid v) {i : Nat} (hi : i < xs.length) :
    ∃ et es e fs, σ.heap a = some (.array et es) ∧ es.length < 2147483648 ∧ i < es.length ∧
      es[i]? = some (.ref e) ∧ σ.heap e = some (.plain "Cbtrn03c$CardXrefRecord" fs) ∧
      Fields.get fs ("Cbtrn03c$CardXrefRecord", "xrefAcctId") =
        some (.long (BitVec.ofInt 64 (Model.xAcct (xs[i]'hi)))) := by
  obtain ⟨et, es, ha, hlen, h2⟩ := hf
  have hie : i < es.length := h2.length_eq ▸ hi
  obtain ⟨e, fs, he, hobj, hfs⟩ := forall2_getElem h2 i hie hi
  obtain ⟨card, cust, acct, fill, hx, -⟩ := Glue.xref_shape (hv _ (List.getElem_mem hi))
  refine ⟨et, es, e, fs, ha, hlen, hie, ?_, hobj, ?_⟩
  · rw [List.getElem?_eq_getElem hie, he]
  · rw [hx] at hfs ⊢
    obtain _ | ⟨-, _ | ⟨-, _ | ⟨h3, -⟩⟩⟩ := hfs
    exact h3

/-- The transaction type record object at index `i` of the file `a`, and its description. -/
theorem type_elem {σ : State} {a : Addr} {ys : Recs} (hf : TrantypeFileAt σ a ys)
    (hv : ∀ v ∈ ys, TranTypeRecord.Valid v) {i : Nat} (hi : i < ys.length) :
    ∃ et es e fs, σ.heap a = some (.array et es) ∧ es.length < 2147483648 ∧ i < es.length ∧
      es[i]? = some (.ref e) ∧ σ.heap e = some (.plain "Cbtrn03c$TranTypeRecord" fs) ∧
      SFld σ "Cbtrn03c$TranTypeRecord" fs "tranTypeDesc" (Model.yDesc (ys[i]'hi)) := by
  obtain ⟨et, es, ha, hlen, h2⟩ := hf
  have hie : i < es.length := h2.length_eq ▸ hi
  obtain ⟨e, fs, he, hobj, hfs⟩ := forall2_getElem h2 i hie hi
  obtain ⟨ty, desc, fill, hy, -⟩ := Glue.type_shape (hv _ (List.getElem_mem hi))
  refine ⟨et, es, e, fs, ha, hlen, hie, ?_, hobj, ?_⟩
  · rw [List.getElem?_eq_getElem hie, he]
  · rw [hy] at hfs ⊢
    obtain _ | ⟨-, _ | ⟨h1, -⟩⟩ := hfs
    obtain ⟨v, hget, x, rfl, hx⟩ := h1
    exact ⟨x, hget, hx⟩

/-- The category record object at index `j` of the file `a`, and its description. -/
theorem cat_elem {σ : State} {a : Addr} {cs : Recs} (hf : TrancatgFileAt σ a cs)
    (hv : ∀ v ∈ cs, TranCatRecord.Valid v) {j : Nat} (hj : j < cs.length) :
    ∃ et es e fs, σ.heap a = some (.array et es) ∧ es.length < 2147483648 ∧ j < es.length ∧
      es[j]? = some (.ref e) ∧ σ.heap e = some (.plain "Cbtrn03c$TranCatRecord" fs) ∧
      SFld σ "Cbtrn03c$TranCatRecord" fs "tranCatTypeDesc" (Model.cDesc (cs[j]'hj)) := by
  obtain ⟨et, es, ha, hlen, h2⟩ := hf
  have hje : j < es.length := h2.length_eq ▸ hj
  obtain ⟨e, fs, he, hobj, hfs⟩ := forall2_getElem h2 j hje hj
  obtain ⟨ty, cat, desc, fill, hc, -⟩ := Glue.catg_shape (hv _ (List.getElem_mem hj))
  refine ⟨et, es, e, fs, ha, hlen, hje, ?_, hobj, ?_⟩
  · rw [List.getElem?_eq_getElem hje, he]
  · rw [hc] at hfs ⊢
    obtain _ | ⟨-, _ | ⟨-, _ | ⟨h2, -⟩⟩⟩ := hfs
    obtain ⟨v, hget, x, rfl, hx⟩ := h2
    exact ⟨x, hget, hx⟩

/-- The files' lengths are `int`s. -/
theorem xref_len {σ : State} {a : Addr} {xs : Recs} (hf : XrefFileAt σ a xs) :
    xs.length < 2147483648 := by
  obtain ⟨et, es, -, hlen, h2⟩ := hf
  rw [← h2.length_eq]
  exact hlen
theorem type_len {σ : State} {a : Addr} {ys : Recs} (hf : TrantypeFileAt σ a ys) :
    ys.length < 2147483648 := by
  obtain ⟨et, es, -, hlen, h2⟩ := hf
  rw [← h2.length_eq]
  exact hlen
theorem cat_len {σ : State} {a : Addr} {cs : Recs} (hf : TrancatgFileAt σ a cs) :
    cs.length < 2147483648 := by
  obtain ⟨et, es, -, hlen, h2⟩ := hf
  rw [← h2.length_eq]
  exact hlen

theorem tcat_bound {t : Rec} (ht : TranRecord.Valid t) : (Model.tCat t).natAbs < 10000 := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, -, -,
    h3, -⟩ := Glue.tran_shape ht
  simpa [Model.tCat, Model.numOf] using h3

/-! ## `tranStep` along the paths of `processDetail` -/

/-- No cross-reference for a new card: the abend. -/
theorem tranStep_xref_none {xs ys cs : Recs} {d t : Rec} {s : Model.St}
    (hcard : (pdS0 s t).card ≠ Model.tCard t) (h : xrefIdx xs (Model.tCard t) = -1) :
    Model.tranStep xs ys cs d s t =
      .error (Model.abend23 (pdS1c s t) (Model.txt "INVALID CARD NUMBER : " ++ Model.cps (Model.tCard t))) := by
  have hn := findIdx_neg h
  have e : Model.cardStep xs (pdS0 s t) t =
      .error (Model.abend23 (pdS1c s t)
        (Model.txt "INVALID CARD NUMBER : " ++ Model.cps (Model.tCard t))) := by
    unfold Model.cardStep
    simp only [hcard, ↓reduceIte, hn]
    rfl
  have e' : Model.cardStep xs (Model.dsp s (Model.TranRecord.textS t)) t = _ := e
  unfold Model.tranStep
  rw [e']

/-- The cross-reference of a new card found at index `i`. -/
theorem cardStep_xref {xs : Recs} {t : Rec} {s : Model.St} (hcard : (pdS0 s t).card ≠ Model.tCard t)
    {i : Nat} (h : xrefIdx xs (Model.tCard t) = (i : Int)) (hi : i < xs.length) :
    cardOk xs s t = { pdS1c s t with xref := xs[i]'hi } ∧
      Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t) := by
  obtain ⟨_, hfind⟩ := findIdx_nat h
  have e : Model.cardStep xs (pdS0 s t) t = .ok { pdS1c s t with xref := xs[i]'hi } := by
    unfold Model.cardStep
    simp only [hcard, ↓reduceIte, hfind]
    rfl
  have e2 : cardOk xs s t = { pdS1c s t with xref := xs[i]'hi } := by
    unfold cardOk
    rw [e]
    rfl
  exact ⟨e2, by rw [e, e2]⟩

/-- No type record: the abend. -/
theorem tranStep_type_none {xs ys cs : Recs} {d t : Rec} {s : Model.St}
    (hcs : Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t))
    (h : typeIdx ys (Model.tType t) = -1) :
    Model.tranStep xs ys cs d s t =
      .error (Model.abend23 (cardOk xs s t)
        (Model.txt "INVALID TRANSACTION TYPE : " ++ Model.cps (Model.tType t))) := by
  have hn := findIdx_neg h
  have hcs' : Model.cardStep xs (Model.dsp s (Model.TranRecord.textS t)) t = .ok (cardOk xs s t) :=
    hcs
  unfold Model.tranStep
  rw [hcs']
  simp only [hn]

/-- No category record: the abend. -/
theorem tranStep_cat_none {xs ys cs : Recs} {d t : Rec} {s : Model.St}
    (hcs : Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t))
    {i : Nat} (hty : typeIdx ys (Model.tType t) = (i : Int))
    (h : catIdx cs (Model.tType t) (Model.tCat t) = -1) :
    Model.tranStep xs ys cs d s t =
      .error (Model.abend23 (cardOk xs s t)
        (Model.txt "INVALID TRAN CATG KEY : " ++ Model.cps (Model.tType t) ++
          Model.digs 4 (Model.tCat t))) := by
  obtain ⟨_, hfy⟩ := findIdx_nat hty
  have hn := findIdx_neg h
  have hcs' : Model.cardStep xs (Model.dsp s (Model.TranRecord.textS t)) t = .ok (cardOk xs s t) :=
    hcs
  unfold Model.tranStep
  rw [hcs']
  simp only [hfy, hn]

/-- Both records found (at `i`, `j`): the report lines. -/
theorem tranStep_report {xs ys cs : Recs} {d t : Rec} {s : Model.St}
    (hcs : Model.cardStep xs (pdS0 s t) t = .ok (cardOk xs s t))
    {i j : Nat} (hty : typeIdx ys (Model.tType t) = (i : Int))
    (hca : catIdx cs (Model.tType t) (Model.tCat t) = (j : Int)) :
    Model.tranStep xs ys cs d s t =
      .ok (Model.report d (cardOk xs s t) t (tyOf ys t) (caOf cs t)) ∧
    ∃ (hi : i < ys.length) (hj : j < cs.length), tyOf ys t = ys[i]'hi ∧ caOf cs t = cs[j]'hj := by
  obtain ⟨hi, hfy⟩ := findIdx_nat hty
  obtain ⟨hj, hfc⟩ := findIdx_nat hca
  have hcs' : Model.cardStep xs (Model.dsp s (Model.TranRecord.textS t)) t = .ok (cardOk xs s t) :=
    hcs
  have ety : tyOf ys t = ys[i]'hi := by
    unfold tyOf
    rw [hfy]
    rfl
  have eca : caOf cs t = cs[j]'hj := by
    unfold caOf
    rw [hfc]
    rfl
  refine ⟨?_, hi, hj, ety, eca⟩
  unfold Model.tranStep
  rw [hcs', ety, eca]
  simp only [hfy, hfc]

end EquivLean.Modernize.Cbtrn03c.Java.Top

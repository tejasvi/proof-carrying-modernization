import EquivLean.Modernize.Cbtrn03c.JavaTop.CalFind

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: the keyed lookups on the model's records

`findFrom` over the key texts of the array's elements is the model's `findIdx` over the file's
records: the elements are the records (`XrefFileAt`, …), their key texts the CP037 texts of the
model's keys (`Glue.xref_shape`, …), and CP037 is injective (`cp037Str_inj`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

/-! ## `findFrom` as `findIdx?` -/

theorem findFrom_drop {α : Type} [DecidableEq α] [Inhabited α] (ks : List α) (k : α) (i : Nat) :
    findFrom ks k i = (match (ks.drop i).findIdx? (fun x => decide (x = k)) with
      | some j => ((i + j : Nat) : Int)
      | none => -1) := by
  rw [findFrom]
  by_cases h : i < ks.length
  · rw [dif_pos h, List.drop_eq_getElem_cons h, List.findIdx?_cons]
    by_cases he : ks[i] = k
    · simp [he]
    · rw [if_neg he, findFrom_drop ks k (i + 1)]
      have hd : decide (ks[i] = k) = false := by simp [he]
      simp only [hd, Bool.false_eq_true, ↓reduceIte]
      cases hf : (ks.drop (i + 1)).findIdx? (fun x => decide (x = k)) with
      | none => rfl
      | some j =>
        show ((i + 1 + j : Nat) : Int) = ((i + (j + 1) : Nat) : Int)
        rw [show i + 1 + j = i + (j + 1) by omega]
  · rw [dif_neg h, List.drop_of_length_le (by omega)]
    rfl
termination_by ks.length - i
decreasing_by omega

theorem findIdx?_map' {α β : Type} (g : β → α) (p : α → Bool) :
    ∀ l : List β, (l.map g).findIdx? p = l.findIdx? (fun b => p (g b))
  | [] => rfl
  | b :: l => by
    simp only [List.map_cons, List.findIdx?_cons, findIdx?_map' g p l]

theorem findIdx?_congr' {β : Type} (p q : β → Bool) :
    ∀ l : List β, (∀ b ∈ l, p b = q b) → l.findIdx? p = l.findIdx? q
  | [], _ => rfl
  | b :: l, h => by
    simp only [List.findIdx?_cons, h b List.mem_cons_self,
      findIdx?_congr' p q l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem findFrom_map {α β : Type} [DecidableEq α] [Inhabited α] (g : β → α) (l : List β) (k : α)
    (p : β → Bool) (hp : ∀ b ∈ l, decide (g b = k) = p b) :
    findFrom (l.map g) k 0 = findIdx p l := by
  rw [findFrom_drop, List.drop_zero, findIdx?_map', findIdx?_congr' _ p l hp]
  unfold findIdx
  cases l.findIdx? p <;> simp

/-! ## The elements of the files -/

theorem xref_elem_str {σ : State} {e : Value} {x : Rec}
    (h : JRecAt CardXrefRecord "Cbtrn03c$CardXrefRecord" σ e x) (hv : CardXrefRecord.Valid x) :
    fieldStr σ xrefCls "xrefCardNum" e = cp037Str (Model.xCard x) ∧
      StrFieldOk σ xrefCls "xrefCardNum" e := by
  obtain ⟨z, fs, rfl, hz, hf⟩ := h
  obtain ⟨card, cust, acct, fill, rfl, -⟩ := Glue.xref_shape hv
  obtain _ | ⟨h0, -⟩ := hf
  obtain ⟨s, hs, w, rfl, hw⟩ := h0
  refine ⟨?_, ⟨z, fs, w, _, rfl, hz, hs, hw⟩⟩
  simp only [fieldStr, xrefCls, hz]
  rw [show Fields.get fs ("Cbtrn03c$CardXrefRecord", "xrefCardNum") = some (.ref w) from hs]
  simp [argText, strOf, hw, Model.xCard, Model.strOf]

theorem xref_elems {σ : State} :
    ∀ {es : List Value} {xs : Recs}, Forall2 (JRecAt CardXrefRecord "Cbtrn03c$CardXrefRecord" σ) es xs →
      (∀ v ∈ xs, CardXrefRecord.Valid v) →
      es.map (fieldStr σ xrefCls "xrefCardNum") = xs.map (fun x => cp037Str (Model.xCard x)) ∧
        ∀ v ∈ es, StrFieldOk σ xrefCls "xrefCardNum" v
  | [], [], .nil, _ => ⟨rfl, by simp⟩
  | _ :: _, _ :: _, .cons h hs, hv => by
    obtain ⟨e1, e2⟩ := xref_elem_str h (hv _ List.mem_cons_self)
    obtain ⟨r1, r2⟩ := xref_elems hs (fun v hm => hv v (List.mem_cons_of_mem _ hm))
    refine ⟨by simp only [List.map_cons, e1, r1], ?_⟩
    intro v hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact e2
    · exact r2 v hm

theorem type_elem_str {σ : State} {e : Value} {y : Rec}
    (h : JRecAt TranTypeRecord "Cbtrn03c$TranTypeRecord" σ e y) (hv : TranTypeRecord.Valid y) :
    fieldStr σ typeCls "tranType" e = cp037Str (Model.yType y) ∧
      StrFieldOk σ typeCls "tranType" e := by
  obtain ⟨z, fs, rfl, hz, hf⟩ := h
  obtain ⟨ty, desc, fill, rfl, -⟩ := Glue.type_shape hv
  obtain _ | ⟨h0, -⟩ := hf
  obtain ⟨s, hs, w, rfl, hw⟩ := h0
  refine ⟨?_, ⟨z, fs, w, _, rfl, hz, hs, hw⟩⟩
  simp only [fieldStr, typeCls, hz]
  rw [show Fields.get fs ("Cbtrn03c$TranTypeRecord", "tranType") = some (.ref w) from hs]
  simp [argText, strOf, hw, Model.yType, Model.strOf]

theorem type_elems {σ : State} :
    ∀ {es : List Value} {ys : Recs}, Forall2 (JRecAt TranTypeRecord "Cbtrn03c$TranTypeRecord" σ) es ys →
      (∀ v ∈ ys, TranTypeRecord.Valid v) →
      es.map (fieldStr σ typeCls "tranType") = ys.map (fun y => cp037Str (Model.yType y)) ∧
        ∀ v ∈ es, StrFieldOk σ typeCls "tranType" v
  | [], [], .nil, _ => ⟨rfl, by simp⟩
  | _ :: _, _ :: _, .cons h hs, hv => by
    obtain ⟨e1, e2⟩ := type_elem_str h (hv _ List.mem_cons_self)
    obtain ⟨r1, r2⟩ := type_elems hs (fun v hm => hv v (List.mem_cons_of_mem _ hm))
    refine ⟨by simp only [List.map_cons, e1, r1], ?_⟩
    intro v hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact e2
    · exact r2 v hm

theorem cat_elem_key {σ : State} {e : Value} {c : Rec}
    (h : JRecAt TranCatRecord "Cbtrn03c$TranCatRecord" σ e c) (hv : TranCatRecord.Valid c) :
    catKey σ e = (cp037Str (Model.cType c), BitVec.ofInt 64 (Model.cCat c)) ∧ CatOk σ e ∧
      (Model.cCat c).natAbs < 10000 := by
  obtain ⟨z, fs, rfl, hz, hf⟩ := h
  obtain ⟨ty, cat, desc, fill, rfl, -, hcat, -⟩ := Glue.catg_shape hv
  obtain _ | ⟨h0, _ | ⟨h1, -⟩⟩ := hf
  obtain ⟨s, hs, w, rfl, hw⟩ := h0
  have h1' : Fields.get fs ("Cbtrn03c$TranCatRecord", "tranCatCd") =
      some (.long (BitVec.ofInt 64 cat)) := h1
  refine ⟨?_, ⟨z, fs, w, _, _, rfl, hz, hs, hw, h1'⟩, by simpa [Model.cCat, Model.numOf] using hcat⟩
  simp only [catKey, fieldStr, fieldLongV, catCls, hz]
  rw [show Fields.get fs ("Cbtrn03c$TranCatRecord", "tranTypeCd") = some (.ref w) from hs, h1']
  simp [argText, strOf, hw, Model.cType, Model.cCat, Model.strOf, Model.numOf]

theorem cat_elems {σ : State} :
    ∀ {es : List Value} {cs : Recs}, Forall2 (JRecAt TranCatRecord "Cbtrn03c$TranCatRecord" σ) es cs →
      (∀ v ∈ cs, TranCatRecord.Valid v) →
      es.map (catKey σ) = cs.map (fun c => (cp037Str (Model.cType c), BitVec.ofInt 64 (Model.cCat c))) ∧
        ∀ v ∈ es, CatOk σ v
  | [], [], .nil, _ => ⟨rfl, by simp⟩
  | _ :: _, _ :: _, .cons h hs, hv => by
    obtain ⟨e1, e2, -⟩ := cat_elem_key h (hv _ List.mem_cons_self)
    obtain ⟨r1, r2⟩ := cat_elems hs (fun v hm => hv v (List.mem_cons_of_mem _ hm))
    refine ⟨by simp only [List.map_cons, e1, r1], ?_⟩
    intro v hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact e2
    · exact r2 v hm

/-- A small category code as a `long`, compared with `v`. -/
theorem ofInt64_eq_iff {z : Int} (hz : z.natAbs < 10000) (v : I64) :
    BitVec.ofInt 64 z = v ↔ z = v.toInt := by
  constructor
  · rintro rfl
    rw [BitVec.toInt_ofInt, Int.bmod_def]
    have h2 : ((2 : Nat) ^ 64 : Nat) = 18446744073709551616 := by decide
    simp only [h2]
    split <;> omega
  · rintro rfl
    exact BitVec.ofInt_toInt

/-! ## The contracts -/

theorem findXrefT_sat : Sat Gen.prog findXrefRef findXrefSpecT := by
  intro args σ o hp hx
  obtain ⟨a, y, xs, k, rfl, hf, hv, hy⟩ := hp
  obtain ⟨et, es, ha, hlen, h2⟩ := hf
  have ho := findXref_vc.sat _ σ o ⟨a, y, cp037Str k, et, es, rfl, hy, ha, hlen,
    (xref_elems h2 hv).2⟩ hx
  cases o with
  | normal r σ' =>
    intro a' y' xs' k' heq hf' hv' hy'
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨et', es', ha', -, h2'⟩ := hf'
    obtain ⟨hr, hs⟩ := ho a y (cp037Str k') et' es' rfl hy' ha'
    refine ⟨?_, hs⟩
    rw [hr, (xref_elems h2' hv').1, findFrom_map _ xs' (cp037Str k') (fun x => Model.xCard x == k')]
    · rfl
    · intro b _
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, cp037Str_inj, beq_iff_eq]
  | exc e σ' => exact ho
  | wrong m => exact ho

theorem findTranTypeT_sat : Sat Gen.prog findTranTypeRef findTranTypeSpecT := by
  intro args σ o hp hx
  obtain ⟨a, y, ys, k, rfl, hf, hv, hy⟩ := hp
  obtain ⟨et, es, ha, hlen, h2⟩ := hf
  have ho := findTranType_vc.sat _ σ o ⟨a, y, cp037Str k, et, es, rfl, hy, ha, hlen,
    (type_elems h2 hv).2⟩ hx
  cases o with
  | normal r σ' =>
    intro a' y' ys' k' heq hf' hv' hy'
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨et', es', ha', -, h2'⟩ := hf'
    obtain ⟨hr, hs⟩ := ho a y (cp037Str k') et' es' rfl hy' ha'
    refine ⟨?_, hs⟩
    rw [hr, (type_elems h2' hv').1, findFrom_map _ ys' (cp037Str k') (fun y => Model.yType y == k')]
    · rfl
    · intro b _
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, cp037Str_inj, beq_iff_eq]
  | exc e σ' => exact ho
  | wrong m => exact ho

theorem findTranCatT_sat : Sat Gen.prog findTranCatRef findTranCatSpecT := by
  intro args σ o hp hx
  obtain ⟨a, y, cs, k, v, rfl, hf, hv, hy, -⟩ := hp
  obtain ⟨et, es, ha, hlen, h2⟩ := hf
  have ho := findTranCat_vc.sat _ σ o ⟨a, y, cp037Str k, v, et, es, rfl, hy, ha, hlen,
    (cat_elems h2 hv).2⟩ hx
  cases o with
  | normal r σ' =>
    intro a' y' cs' k' v' heq hf' hv' hy'
    simp only [List.cons.injEq, Value.ref.injEq, Value.long.injEq, and_true] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    obtain ⟨et', es', ha', -, h2'⟩ := hf'
    obtain ⟨hr, hs⟩ := ho a y (cp037Str k') v et' es' rfl hy' ha'
    refine ⟨?_, hs⟩
    rw [hr, (cat_elems h2' hv').1, findFrom_map _ cs' (cp037Str k', v)
      (fun c => Model.cType c == k' && Model.cCat c == v.toInt)]
    · rfl
    · intro b hb
      have hbound : (Model.cCat b).natAbs < 10000 := by
        obtain ⟨ty, cat, desc, fill, hbe, -, hcat, -⟩ := Glue.catg_shape (hv' b hb)
        rw [hbe]; simpa [Model.cCat, Model.numOf] using hcat
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, Prod.mk.injEq, cp037Str_inj, ofInt64_eq_iff hbound,
        Bool.and_eq_true, beq_iff_eq]
  | exc e σ' => exact ho
  | wrong m => exact ho

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

set_option maxHeartbeats 0 in
theorem findXref_ok : ContractOK Gen.prog findXrefSig findXrefSpecT := by
  jcontract_ok [Cal.findXrefT_sat]

set_option maxHeartbeats 0 in
theorem findTranType_ok : ContractOK Gen.prog findTranTypeSig findTranTypeSpecT := by
  jcontract_ok [Cal.findTranTypeT_sat]

set_option maxHeartbeats 0 in
theorem findTranCat_ok : ContractOK Gen.prog findTranCatSig findTranCatSpecT := by
  jcontract_ok [Cal.findTranCatT_sat]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.findXref_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.findTranType_ok
#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.findTranCat_ok

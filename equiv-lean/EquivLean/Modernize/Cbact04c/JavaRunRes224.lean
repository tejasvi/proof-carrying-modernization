import EquivLean.Modernize.Cbact04c.JavaRunRes210

/-!
# CBACT04C → Java, `run`: closing the cut at 232 (merchant name, city, zip; card number)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

theorem xrefs_valid_of_pre {g : G} {args : List Value} {σ0 : State} (h : RunPreG g args σ0) :
    ∀ v ∈ g.xrefs, CardXrefRecord.Valid v := by
  obtain ⟨-, ⟨b1, b2, b3, b4, q1, c1, -, -, -, -, -, -, -, -, -, hv2, -, -, -, -⟩, -⟩ := h
  exact hv2

/-- The cross-reference of an account that has one is a record of the file. -/
theorem findXref_valid {g : G} (hv : ∀ v ∈ g.xrefs, CardXrefRecord.Valid v) {id : Int}
    (hex : ∃ x ∈ g.xrefs, Model.xAcct x = id) :
    CardXrefRecord.Valid (Model.findXref g.xrefs id) := by
  obtain ⟨x, hx, hxa⟩ := hex
  unfold Model.findXref
  cases hf : g.xrefs.find? (fun x => Model.xAcct x == id) with
  | none => exact absurd (List.find?_eq_none.1 hf x hx) (by simp [hxa])
  | some y => exact hv y (List.mem_of_find?_eq_some hf)

/-- The cut at 232 from three callee post-states (`spaces`) and the writes to `T`. -/
theorem j232_core {g : G} {σ0 σ σa σb σc σ2 : State} {fr' : Frame} {i : I32} {hp : Hp}
    {tcbV acctV xrefV lastV : Value} {fsT : List (FieldKey × Value)} {a1 a2 a3 cs : Addr}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some tcbV)
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f11 : fr'.get 11 = some (.long (BitVec.ofInt 64 (amtOf g i.toInt.toNat))))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64 (totOf g i.toInt.toNat))))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (kOf g i.toInt.toNat))))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV)
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ tcbV
      (g.trec i.toInt.toNat)))
    (hheap : Hide (LoopHeap g σ0 σ hp (sel g i.toInt.toNat) acctV xrefV lastV))
    (hrate : rateOf g i.toInt.toNat ≠ 0)
    (hset : Hide (TranSet σ hp.T 7 (tvals g i.toInt.toNat)))
    (hT : σ.heap hp.T = some (.plain "Cbact04c$TranRecord" fsT))
    (hcs : σ.heap cs = some (.str (cp037Str (Model.xCard (sel g i.toInt.toNat).xref))))
    (h1h : σa.heap a1 = some (.str (spJ 50))) (h1n : σ.next ≤ σa.next)
    (h1f : ∀ x, x < σ.next → σa.heap x = σ.heap x)
    (h2h : σb.heap a2 = some (.str (spJ 50))) (h2n : σa.next ≤ σb.next)
    (h2f : ∀ x, x < σa.next → σb.heap x = if x = hp.T then some (.plain "Cbact04c$TranRecord"
      (Fields.set fsT ("Cbact04c$TranRecord", "tranMerchantName") (.ref a1))) else σa.heap x)
    (h3h : σc.heap a3 = some (.str (spJ 10))) (h3n : σb.next ≤ σc.next)
    (h3f : ∀ x, x < σb.next → σc.heap x = if x = hp.T then some (.plain "Cbact04c$TranRecord"
      (Fields.set (Fields.set fsT ("Cbact04c$TranRecord", "tranMerchantName") (.ref a1))
        ("Cbact04c$TranRecord", "tranMerchantCity") (.ref a2))) else σb.heap x)
    (hT2 : σ2.heap hp.T = some (.plain "Cbact04c$TranRecord"
      (Fields.set (Fields.set (Fields.set (Fields.set fsT
        ("Cbact04c$TranRecord", "tranMerchantName") (.ref a1))
        ("Cbact04c$TranRecord", "tranMerchantCity") (.ref a2))
        ("Cbact04c$TranRecord", "tranMerchantZip") (.ref a3))
        ("Cbact04c$TranRecord", "tranCardNum") (.ref cs))))
    (hH : ∀ x, x ≠ hp.T → σ2.heap x = σc.heap x) (hn2 : σ2.next = σc.next)
    (hi2 : σ2.inits = σ.inits) :
    J232 g g.args σ0 fr' σ2 := by
  have hTn : hp.T < σ.next := State.lt_next_of_heap hT
  have hTa : σa.heap hp.T = some (.plain "Cbact04c$TranRecord" fsT) := by rw [h1f _ hTn, hT]
  have hTb := h2f hp.T (by jomega)
  rw [if_pos rfl] at hTb
  have hTc := h3f hp.T (by jomega)
  rw [if_pos rfl] at hTc
  have ha1T : a1 ≠ hp.T := by intro e; rw [e, hTa] at h1h; cases h1h
  have ha2T : a2 ≠ hp.T := by intro e; rw [e, hTb] at h2h; cases h2h
  have ha3T : a3 ≠ hp.T := by intro e; rw [e, hTc] at h3h; cases h3h
  have hcsT : cs ≠ hp.T := by intro e; rw [e, hT] at hcs; cases hcs
  have hag : Agree σ σ2 [hp.T] := by
    refine ⟨by rw [hn2]; jomega, fun x hx hw => ?_⟩
    have hxT : x ≠ hp.T := fun e => hw (List.mem_singleton.2 e)
    rw [hH x hxT, h3f x (by jomega), if_neg hxT, h2f x (by jomega), if_neg hxT, h1f x hx]
  have h2a1 : σ2.heap a1 = some (.str (spJ 50)) := by
    have := State.lt_next_of_heap h1h
    rw [hH a1 ha1T, h3f a1 (by jomega), if_neg ha1T, h2f a1 this, if_neg ha1T, h1h]
  have h2a2 : σ2.heap a2 = some (.str (spJ 50)) := by
    have := State.lt_next_of_heap h2h
    rw [hH a2 ha2T, h3f a2 this, if_neg ha2T, h2h]
  have h2a3 : σ2.heap a3 = some (.str (spJ 10)) := by rw [hH a3 ha3T, h3h]
  have h2cs : σ2.heap cs = some (.str (cp037Str (Model.xCard (sel g i.toInt.toNat).xref))) := by
    rw [hag.2 cs (State.lt_next_of_heap hcs) (fun hm => hcsT (List.mem_singleton.1 hm)), hcs]
  have hL := Hide.elim hheap
  obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := hL.1
  have hTstr : ∀ x s, σ.heap x = some (.str s) → x ∉ [hp.T] := by
    intro x s hx hm; rw [List.mem_singleton] at hm; subst hm; rw [hT] at hx; cases hx
  have hok2 : TranOk σ2 hp.T := by
    obtain ⟨fs0, h1, h2, ⟨d, s, h3, h4, h5, h6⟩, ⟨f, h7, h8⟩⟩ := htr
    rw [hT] at h1
    cases h1
    refine ⟨_, hT2, fun k hk => ?_, ⟨d, s, ?_, ?_, h5, h6⟩, ⟨f, ?_, ?_⟩⟩
    · simp only [fields_get_set]
      split
      · exact ⟨_, rfl⟩
      split
      · exact ⟨_, rfl⟩
      split
      · exact ⟨_, rfl⟩
      split
      · exact ⟨_, rfl⟩
      · exact h2 k hk
    · simp only [fields_get_set]; simpa using h3
    · rw [hag.2 d (State.lt_next_of_heap h4) (hTstr d _ h4), h4]
    · simp only [fields_get_set]; simpa using h7
    · rw [hag.2 f (State.lt_next_of_heap h8) (hTstr f _ h8), h8]
  have hL2 := loopHeap_agreeT hL hT hag hok2 hi2
  have hn2' : NoStr σ [hp.T] := fun w hw' st hst => hTstr w st hst hw'
  have htcb2 : JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ2 tcbV (g.trec i.toInt.toNat) := by
    have hr := Hide.elim htcb
    obtain ⟨x, fsx, hx, hxh, -⟩ := id hr
    subst hx
    exact jrecAt_agree hr hag hn2' (not_T_of_cls hT hxh (by decide))
  have hk7 : (TranRecord.fields.take 7).map (·.jname) =
      ["tranId", "tranTypeCd", "tranCatCd", "tranSource", "tranDesc", "tranAmt",
        "tranMerchantId"] := by decide
  have hs7 := tranSet_agree (Hide.elim hset) hT hag hT2 (by
    rw [hk7]
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [fields_get_set])
  have hl := tvals_length g i.toInt.toNat
  have hs8 := tranSet_extend hs7 hT2 (by decide) hl (by
    refine ⟨.ref a1, by simp [fields_get_set], a1, rfl, ?_⟩
    try simp only [tvals, Model.tranVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [cp037Str_sp, h2a1])
  have hs9 := tranSet_extend hs8 hT2 (by decide) hl (by
    refine ⟨.ref a2, by simp [fields_get_set], a2, rfl, ?_⟩
    try simp only [tvals, Model.tranVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [cp037Str_sp, h2a2])
  have hs10 := tranSet_extend hs9 hT2 (by decide) hl (by
    refine ⟨.ref a3, by simp [fields_get_set], a3, rfl, ?_⟩
    try simp only [tvals, Model.tranVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [cp037Str_sp, h2a3])
  have hs11 := tranSet_extend hs10 hT2 (by decide) hl (by
    refine ⟨.ref cs, by simp [fields_get_set], cs, rfl, ?_⟩
    try simp only [tvals, Model.tranVals, List.getD_cons_succ, List.getD_cons_zero]
    exact h2cs)
  exact ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, Hide.intro htcb2⟩, f3,
    f11, f12, f14, f25, f16, f17, Hide.intro hL2, hrate⟩, Hide.intro hs11⟩

/-- `j232_core` for the state `jvc` leaves: the last two writes to `T` after the third call. -/
theorem j232_of {g : G} {σ0 σ σa σb σc : State} {fr' : Frame} {i : I32} {hp : Hp}
    {tcbV acctV xrefV lastV : Value} {fsT : List (FieldKey × Value)} {a1 a2 a3 cs : Addr}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt)
    (hheap : Hide (LoopHeap g σ0 σ hp (sel g i.toInt.toNat) acctV xrefV lastV))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ tcbV
      (g.trec i.toInt.toNat)))
    (hT : σ.heap hp.T = some (.plain "Cbact04c$TranRecord" fsT))
    (h1h : σa.heap a1 = some (.str (spJ 50))) (h1n : σ.next ≤ σa.next)
    (h1f : ∀ x, x < σ.next → σa.heap x = σ.heap x)
    (h2h : σb.heap a2 = some (.str (spJ 50))) (h2n : σa.next ≤ σb.next)
    (h2f : ∀ x, x < σa.next → σb.heap x = if x = hp.T then some (.plain "Cbact04c$TranRecord"
      (Fields.set fsT ("Cbact04c$TranRecord", "tranMerchantName") (.ref a1))) else σa.heap x)
    (h3h : σc.heap a3 = some (.str (spJ 10))) (h3n : σb.next ≤ σc.next)
    (h3f : ∀ x, x < σb.next → σc.heap x = if x = hp.T then some (.plain "Cbact04c$TranRecord"
      (Fields.set (Fields.set fsT ("Cbact04c$TranRecord", "tranMerchantName") (.ref a1))
        ("Cbact04c$TranRecord", "tranMerchantCity") (.ref a2))) else σb.heap x)
    (h3i : σc.inits = σ.inits)
    (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some tcbV)
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f11 : fr'.get 11 = some (.long (BitVec.ofInt 64 (amtOf g i.toInt.toNat))))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64 (totOf g i.toInt.toNat))))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (kOf g i.toInt.toNat))))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV)
    (hrate : rateOf g i.toInt.toNat ≠ 0)
    (hset : Hide (TranSet σ hp.T 7 (tvals g i.toInt.toNat)))
    (hcs : σ.heap cs = some (.str (cp037Str (Model.xCard (sel g i.toInt.toNat).xref)))) :
    J232 g g.args σ0 fr' ((σc.setObj hp.T (.plain "Cbact04c$TranRecord"
      (Fields.set (Fields.set (Fields.set fsT ("Cbact04c$TranRecord", "tranMerchantName") (.ref a1))
        ("Cbact04c$TranRecord", "tranMerchantCity") (.ref a2))
        ("Cbact04c$TranRecord", "tranMerchantZip") (.ref a3)))).setObj hp.T
      (.plain "Cbact04c$TranRecord"
        (Fields.set (Fields.set (Fields.set (Fields.set fsT
          ("Cbact04c$TranRecord", "tranMerchantName") (.ref a1))
          ("Cbact04c$TranRecord", "tranMerchantCity") (.ref a2))
          ("Cbact04c$TranRecord", "tranMerchantZip") (.ref a3))
          ("Cbact04c$TranRecord", "tranCardNum") (.ref cs)))) := by
  have hTn : hp.T < σ.next := State.lt_next_of_heap hT
  have hTc := h3f hp.T (by jomega)
  rw [if_pos rfl] at hTc
  exact j232_core hn hi0 hlocs f22 f6 f4 f5 f3 f11 f12 f14 f25 f16 f17 htcb hheap hrate hset hT hcs
    h1h h1n h1f h2h h2n h2f h3h h3n h3f (heap_setObj_self' (heap_setObj_self' hTc))
    (fun x hx => by rw [heap_setObj_other hx, heap_setObj_other hx])
    (by rw [State.next_setObj, State.next_setObj]) h3i

end EquivLean.Modernize.Cbact04c.Java

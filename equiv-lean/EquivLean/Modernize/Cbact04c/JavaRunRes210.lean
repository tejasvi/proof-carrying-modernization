import EquivLean.Modernize.Cbact04c.JavaRunRes199

/-!
# CBACT04C → Java, `run`: the transaction object (statements 210–241)

* `loopHeap_setT`: a field write to the transaction object `T` keeps the loop's heap invariant when
  `TranOk` holds after it;
* `tranSet_succ`: writing field `m` with the value of the record's field `m` extends `TranSet`;
* `encode_zpadJ`: the CP037 text of an unsigned DISPLAY number is its zero-padded digits.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- The CP037 text of an unsigned DISPLAY number. -/
theorem encode_zpadJ {fmt : Cobol.NumFmt} (hu : fmt.usage = .display) (hs : fmt.signed = false)
    (hd : 0 < fmt.digits) (v : Int) :
    cp037Str (Cobol.encodeNum {} fmt v) = zpadJ v.natAbs fmt.digits := by
  rw [cp037Str_eq_map, text_unsigned hu hs hd, zpad_jline]

theorem cp037Str_append (x y : List UInt8) : cp037Str (x ++ y) = cp037Str x ++ cp037Str y := by
  simp [cp037Str]

set_option maxRecDepth 100000 in
theorem cp037Unit_space : cp037Unit 64 = space := by decide

theorem cp037Str_sp (n : Nat) : cp037Str (Model.sp n) = spJ n := by
  simp only [cp037Str, Model.sp, spJ, List.map_replicate, cp037Unit_space]

theorem keysRC_nodup : keysRC.Nodup := by decide

/-! ## Writes to the transaction object -/

theorem not_T_of_cls {σ : State} {T x : Addr} {fsT : List (FieldKey × Value)} {c : ClassName}
    {fs : List (FieldKey × Value)} (hT : σ.heap T = some (.plain "Cbact04c$TranRecord" fsT))
    (hx : σ.heap x = some (.plain c fs)) (hc : c ≠ "Cbact04c$TranRecord") : x ∉ [T] := by
  intro hm
  rw [List.mem_singleton] at hm
  subst hm
  rw [hT] at hx
  cases hx
  exact hc rfl

/-- Writing the transaction object keeps the heap invariant (given `TranOk` after the write). -/
theorem coreHeap_setT {g : G} {σ0 σ : State} {h : Hp} {s : Model.St} {M : List Addr}
    {fs fs' : List (FieldKey × Value)} (hc : CoreHeap g σ0 σ h s M)
    (hT : σ.heap h.T = some (.plain "Cbact04c$TranRecord" fs))
    (hok : TranOk (σ.setObj h.T (.plain "Cbact04c$TranRecord" fs')) h.T) :
    CoreHeap g σ0 (σ.setObj h.T (.plain "Cbact04c$TranRecord" fs')) h s M := by
  obtain ⟨hg0, hin, hfr, hres, hdisp, hw, hr, ht, htr, hp, hcl⟩ := hc
  have ha : Agree σ (σ.setObj h.T (.plain "Cbact04c$TranRecord" fs')) [h.T] :=
    agree_setObj_mem (agree_refl σ [h.T]) (List.mem_singleton_self _) _
  have hn : NoStr σ [h.T] := by
    intro w hw' st hst
    rw [List.mem_singleton] at hw'
    subst hw'
    rw [hT] at hst
    cases hst
  have hnot : ∀ x : Addr, x ≠ h.T → x ∉ [h.T] := fun x hx hm => hx (List.mem_singleton.1 hm)
  obtain ⟨fsR, hR, -⟩ := id hres
  obtain ⟨dxs, dm, hld, -⟩ := id hdisp
  obtain ⟨wxs, wm, hlw, -, hwM⟩ := id hw
  obtain ⟨rxs, rm, hlr, -⟩ := id hr
  obtain ⟨axs, hA, -⟩ := id ht
  obtain ⟨h0r, h0d, h0w, h0l, h0A, h0T, -⟩ := id hfr
  refine ⟨grows_setObj hg0 h0T, inits_of_eq rfl hin, hfr,
    resAt_agree hres ha (not_T_of_cls hT hR (by decide)),
    dispAt_agree hdisp ha hn (hnot _ (ne_of_heap_list_plain hld hT).symm),
    ?_, recsAt_agree hr ha hn (hnot _ (ne_of_heap_list_plain hlr hT).symm) (fun a hm => ?_),
    tableAt_agree ht ha hn (fun hm => ?_) (fun a hm => ?_),
    hok, jstrAt_agree hp ha hn, jstrAt_agree hcl ha hn⟩
  · -- the write list: no element is `T`
    obtain ⟨wxs', wm', hlw', hww, hwM'⟩ := hw
    refine ⟨wxs', wm', ?_, forall2_jrecAt_agree ha hn hww (fun v hv a hva hm => ?_), hwM'⟩
    · rw [ha.2 _ (State.lt_next_of_heap hlw') (hnot _ (ne_of_heap_list_plain hlw' hT).symm), hlw']
    · rw [List.mem_singleton] at hm
      exact hwM' v hv a hva (by rw [hm]; exact List.mem_singleton_self _)
  · rw [List.mem_singleton] at hm
    subst hm
    exact Or.inr (fun fs'' he => by rw [hT] at he; simp at he)
  · rw [List.mem_singleton] at hm
    rw [hm, hT] at hA
    cases hA
  · rw [List.mem_singleton] at hm
    subst hm
    exact Or.inr (fun fs'' he => by rw [hT] at he; simp at he)

/-- Writing the transaction object keeps the loop's heap invariant. -/
theorem loopHeap_setT {g : G} {σ0 σ : State} {h : Hp} {s : Model.St} {acctV xrefV lastV : Value}
    {fs fs' : List (FieldKey × Value)} (hL : LoopHeap g σ0 σ h s acctV xrefV lastV)
    (hT : σ.heap h.T = some (.plain "Cbact04c$TranRecord" fs))
    (hok : TranOk (σ.setObj h.T (.plain "Cbact04c$TranRecord" fs')) h.T) :
    LoopHeap g σ0 (σ.setObj h.T (.plain "Cbact04c$TranRecord" fs')) h s acctV xrefV lastV := by
  obtain ⟨hc, hacct, hxref, hlast, hfr⟩ := hL
  have ha : Agree σ (σ.setObj h.T (.plain "Cbact04c$TranRecord" fs')) [h.T] :=
    agree_setObj_mem (agree_refl σ [h.T]) (List.mem_singleton_self _) _
  have hn : NoStr σ [h.T] := by
    intro w hw' st hst
    rw [List.mem_singleton] at hw'
    subst hw'
    rw [hT] at hst
    cases hst
  refine ⟨coreHeap_setT hc hT hok, fun hs => ?_, fun hs => ?_, jstrAt_agree hlast ha hn, hfr⟩
  · have hr := hacct hs
    obtain ⟨x, fsx, hx, hxh, -⟩ := id hr
    subst hx
    exact jrecAt_agree hr ha hn (not_T_of_cls hT hxh (by decide))
  · have hr := hxref hs
    obtain ⟨x, fsx, hx, hxh, -⟩ := id hr
    subst hx
    exact jrecAt_agree hr ha hn (not_T_of_cls hT hxh (by decide))

/-- A write to a field other than the description and the filler keeps `TranOk`. -/
theorem tranOk_set {σ : State} {T : Addr} {fs : List (FieldKey × Value)} {k : String} {v : Value}
    (h : TranOk σ T) (hT : σ.heap T = some (.plain "Cbact04c$TranRecord" fs))
    (hk : k ∈ keysRC) (hd : k ≠ "tranDesc") (hf : k ≠ "filler1") :
    TranOk (σ.setObj T (.plain "Cbact04c$TranRecord" (Fields.set fs ("Cbact04c$TranRecord", k) v))) T := by
  obtain ⟨fs0, h1, h2, ⟨d, s, h3, h4, h5, h6⟩, ⟨f, h7, h8⟩⟩ := h
  rw [hT] at h1
  cases h1
  have hdT : d ≠ T := by intro e; subst e; rw [hT] at h4; cases h4
  have hfT : f ≠ T := by intro e; subst e; rw [hT] at h8; cases h8
  refine ⟨_, heap_setObj_self' hT, fun k' hk' => ?_, ⟨d, s, ?_, by rw [heap_setObj_other hdT, h4], h5,
    h6⟩, ⟨f, ?_, by rw [heap_setObj_other hfT, h8]⟩⟩
  · rw [fields_get_set]
    split
    · exact ⟨v, rfl⟩
    · exact h2 k' hk'
  · rw [fields_get_set, if_neg (by intro e; exact hd (congrArg Prod.snd e).symm)]; exact h3
  · rw [fields_get_set, if_neg (by intro e; exact hf (congrArg Prod.snd e).symm)]; exact h7

/-- **Field `m` of the transaction written** with a value that holds the record's field `m` (`k`
the field's name, `hfr`: not among the first `m`, by `decide` for a given `m`). -/
theorem tranSet_succ {σ σ' : State} {T : Addr} {fs : List (FieldKey × Value)} {m : Nat}
    {vals : List FV} {k : String} {w : Value} (hs : StrKeep σ σ')
    (h : TranSet σ T m vals) (hT : σ.heap T = some (.plain "Cbact04c$TranRecord" fs))
    (hm : m < 14) (hlen : vals.length = 14)
    (hfm : (TranRecord.fields.getD m default).jname = k)
    (hfr : k ∉ (TranRecord.fields.take m).map (·.jname))
    (hσ' : σ'.heap T = some (.plain "Cbact04c$TranRecord" (Fields.set fs ("Cbact04c$TranRecord", k) w)))
    (hnew : jFieldAt σ' "Cbact04c$TranRecord" (Fields.set fs ("Cbact04c$TranRecord", k) w)
      (TranRecord.fields.getD m default) (vals.getD m default)) :
    TranSet σ' T (m + 1) vals := by
  obtain ⟨fs0, h1, h2⟩ := h
  rw [hT] at h1
  cases h1
  refine ⟨_, hσ', ?_⟩
  have hfl : TranRecord.fields.length = 14 := by decide
  rw [List.take_add_one, List.take_add_one]
  rw [List.getElem?_eq_getElem (by omega : m < TranRecord.fields.length),
    List.getElem?_eq_getElem (by omega : m < vals.length)]
  simp only [Option.toList_some]
  refine forall2_append ?_ (forall2_jfield_set_other hs h2 hfr)
  have e1 : TranRecord.fields[m]'(by omega) = TranRecord.fields.getD m default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have e2 : vals[m]'(by omega) = vals.getD m default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [e1, e2]
  exact hnew

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-- The heap invariant across a stretch that changes only the transaction object `T` (and
allocates), given `TranOk` after it. -/
theorem coreHeap_agreeT {g : G} {σ0 σ σ' : State} {h : Hp} {s : Model.St} {M : List Addr}
    {fs : List (FieldKey × Value)} (hc : CoreHeap g σ0 σ h s M)
    (hT : σ.heap h.T = some (.plain "Cbact04c$TranRecord" fs)) (ha : Agree σ σ' [h.T])
    (hok : TranOk σ' h.T) (hi : σ'.inits = σ.inits) : CoreHeap g σ0 σ' h s M := by
  obtain ⟨hg0, hin, hfr, hres, hdisp, hw, hr, ht, htr, hp, hcl⟩ := hc
  have hn : NoStr σ [h.T] := by
    intro w hw' st hst
    rw [List.mem_singleton] at hw'
    subst hw'
    rw [hT] at hst
    cases hst
  have hnot : ∀ x : Addr, x ≠ h.T → x ∉ [h.T] := fun x hx hm => hx (List.mem_singleton.1 hm)
  obtain ⟨fsR, hR, -⟩ := id hres
  obtain ⟨dxs, dm, hld, -⟩ := id hdisp
  obtain ⟨rxs, rm, hlr, -⟩ := id hr
  obtain ⟨axs, hA, -⟩ := id ht
  obtain ⟨h0r, h0d, h0w, h0l, h0A, h0T, -⟩ := id hfr
  have hg0' : Grows σ0 σ' := ⟨Nat.le_trans hg0.1 ha.1, fun x hx => by
    rw [ha.2 x (Nat.lt_of_lt_of_le hx hg0.1) (hnot x (Nat.ne_of_lt (Nat.lt_of_lt_of_le hx h0T))),
      hg0.2 x hx]⟩
  refine ⟨hg0', inits_of_eq hi hin, hfr,
    resAt_agree hres ha (not_T_of_cls hT hR (by decide)),
    dispAt_agree hdisp ha hn (hnot _ (ne_of_heap_list_plain hld hT).symm),
    ?_, recsAt_agree hr ha hn (hnot _ (ne_of_heap_list_plain hlr hT).symm) (fun a hm => ?_),
    tableAt_agree ht ha hn (fun hm => ?_) (fun a hm => ?_),
    hok, jstrAt_agree hp ha hn, jstrAt_agree hcl ha hn⟩
  · obtain ⟨wxs', wm', hlw', hww, hwM'⟩ := hw
    refine ⟨wxs', wm', ?_, forall2_jrecAt_agree ha hn hww (fun v hv a hva hm => ?_), hwM'⟩
    · rw [ha.2 _ (State.lt_next_of_heap hlw') (hnot _ (ne_of_heap_list_plain hlw' hT).symm), hlw']
    · rw [List.mem_singleton] at hm
      exact hwM' v hv a hva (by rw [hm]; exact List.mem_singleton_self _)
  · rw [List.mem_singleton] at hm
    subst hm
    exact Or.inr (fun fs'' he => by rw [hT] at he; simp at he)
  · rw [List.mem_singleton] at hm
    rw [hm, hT] at hA
    cases hA
  · rw [List.mem_singleton] at hm
    subst hm
    exact Or.inr (fun fs'' he => by rw [hT] at he; simp at he)

theorem loopHeap_agreeT {g : G} {σ0 σ σ' : State} {h : Hp} {s : Model.St} {acctV xrefV lastV : Value}
    {fs : List (FieldKey × Value)} (hL : LoopHeap g σ0 σ h s acctV xrefV lastV)
    (hT : σ.heap h.T = some (.plain "Cbact04c$TranRecord" fs)) (ha : Agree σ σ' [h.T])
    (hok : TranOk σ' h.T) (hi : σ'.inits = σ.inits) :
    LoopHeap g σ0 σ' h s acctV xrefV lastV := by
  obtain ⟨hc, hacct, hxref, hlast, hfr⟩ := hL
  have hn : NoStr σ [h.T] := by
    intro w hw' st hst
    rw [List.mem_singleton] at hw'
    subst hw'
    rw [hT] at hst
    cases hst
  refine ⟨coreHeap_agreeT hc hT ha hok hi, fun hs => ?_, fun hs => ?_, jstrAt_agree hlast ha hn, hfr⟩
  · have hr := hacct hs
    obtain ⟨x, fsx, hx, hxh, -⟩ := id hr
    subst hx
    exact jrecAt_agree hr ha hn (not_T_of_cls hT hxh (by decide))
  · have hr := hxref hs
    obtain ⟨x, fsx, hx, hxh, -⟩ := id hr
    subst hx
    exact jrecAt_agree hr ha hn (not_T_of_cls hT hxh (by decide))

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxRecDepth 100000 in
theorem cp037Str_01 : cp037Str [240, 241] = [48#16, 49#16] := by decide

set_option maxRecDepth 100000 in
theorem cp037Str_system : cp037Str CardDemo.Cbact04c.systemSrc = JStr.ofString "System    " := by
  decide

theorem jstrAt_alloc2 {σ : State} {o1 o2 : Obj} {v : Value} {str : JStr} (h : JStrAt σ v str) :
    JStrAt ((σ.alloc o1).snd.alloc o2).snd v str := jstrAt_alloc (jstrAt_alloc h)

theorem heap_alloc2_old {σ : State} {o1 o2 : Obj} {x : Addr} {o : Obj} (h : σ.heap x = some o) :
    ((σ.alloc o1).snd.alloc o2).snd.heap x = some o :=
  heap_of_grows (grows_trans (grows_alloc _ _) (grows_alloc _ _)) h

theorem tranId_text (parm : List UInt8) {k : Nat} (hk : k < 1000000) :
    cp037Str (parm ++ Cobol.encodeNum {} CardDemo.Cbact04c.WS_TRANID_SUFFIX.fmt (k : Int)) =
      cp037Str parm ++ zpadJ k 6 := by
  rw [cp037Str_append, encode_zpadJ (by decide) (by decide) (by decide)]
  rfl

/-- **Id, type, category, source set; the description's head built** (statements 210–216): the cut
point 217. -/
theorem j217_of {g : G} {σ0 σ σ2 : State} {fr' : Frame} {i : I32} {hp : Hp}
    {tcbV acctV xrefV lastV tidV : Value} {fsT : List (FieldKey × Value)} {R HEAD : JStr}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some tcbV)
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f11 : fr'.get 11 = some (.long (BitVec.ofInt 64 (amtOf g i.toInt.toNat))))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64 (totOf g i.toInt.toNat))))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (kOf g i.toInt.toNat))))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV) (f27 : fr'.get 27 = some (.ref (σ2.next + 1)))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ tcbV
      (g.trec i.toInt.toNat)))
    (hheap : Hide (LoopHeap g σ0 σ hp (sel g i.toInt.toNat) acctV xrefV lastV))
    (hrate : rateOf g i.toInt.toNat ≠ 0)
    (htid : Hide (JStrAt σ tidV (cp037Str g.parm ++ zpadJ (kOf g i.toInt.toNat) 6)))
    (hT : σ.heap hp.T = some (.plain "Cbact04c$TranRecord" fsT))
    (hag : Agree σ σ2 [hp.T]) (hi2 : σ2.inits = σ.inits)
    (hT2 : σ2.heap hp.T = some (.plain "Cbact04c$TranRecord"
      (Fields.set (Fields.set (Fields.set (Fields.set fsT ("Cbact04c$TranRecord", "tranId") tidV)
        ("Cbact04c$TranRecord", "tranTypeCd") (.ref σ.next)) ("Cbact04c$TranRecord", "tranCatCd")
        (.long 5#64)) ("Cbact04c$TranRecord", "tranSource") (.ref (σ.next + 1)))))
    (h01 : σ2.heap σ.next = some (.str [48#16, 49#16]))
    (hsys : σ2.heap (σ.next + 1) = some (.str (JStr.ofString "System    ")))
    (hHEAD : HEAD = JStr.ofString "Int. for a/c " ++
      zpadJ (Model.aId (sel g i.toInt.toNat).acct).natAbs 11) :
    J217 g g.args σ0 fr' ((σ2.alloc (.str R)).snd.alloc (.str HEAD)).snd := by
  subst hHEAD
  have hL := Hide.elim hheap
  have hkOf : kOf g i.toInt.toNat < 1000000 := Nat.mod_lt _ (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := hL.1
  have hTstr : ∀ x s, σ.heap x = some (.str s) → x ≠ hp.T := by
    intro x s hx e; subst e; rw [hT] at hx; cases hx
  -- `TranOk` after the writes: keys present, description and filler unchanged
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
    · rw [hag.2 d (State.lt_next_of_heap h4) (fun hm => hTstr d s h4 (List.mem_singleton.1 hm)), h4]
    · simp only [fields_get_set]; simpa using h7
    · rw [hag.2 f (State.lt_next_of_heap h8) (fun hm => hTstr f _ h8 (List.mem_singleton.1 hm)), h8]
  have hL2 := loopHeap_agreeT hL hT hag hok2 hi2
  have hg3 : Grows σ2 ((σ2.alloc (.str R)).snd.alloc (.str (JStr.ofString "Int. for a/c " ++
      zpadJ (Model.aId (sel g i.toInt.toNat).acct).natAbs 11))).snd :=
    grows_trans (grows_alloc _ _) (grows_alloc _ _)
  have hi3 : ((σ2.alloc (.str R)).snd.alloc (.str (JStr.ofString "Int. for a/c " ++
      zpadJ (Model.aId (sel g i.toInt.toNat).acct).natAbs 11))).snd.inits = σ2.inits := by rfl
  have hn2 : NoStr σ [hp.T] := by
    intro w hw' st hst
    rw [List.mem_singleton] at hw'
    subst hw'
    rw [hT] at hst
    cases hst
  have htcb2 : JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ2 tcbV (g.trec i.toInt.toNat) := by
    have hr := Hide.elim htcb
    obtain ⟨x, fsx, hx, hxh, -⟩ := id hr
    subst hx
    exact jrecAt_agree hr hag hn2 (not_T_of_cls hT hxh (by decide))
  refine ⟨i, hp, tcbV, acctV, xrefV, lastV, .ref (σ2.next + 1), ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5,
    Hide.intro (jrecAt_grows hg3 htcb2)⟩, f3, f11, f12, f14, f25, f16, f17,
    Hide.intro (loopHeap_grows hL2 hg3 hi3), hrate⟩, f27, Hide.intro ⟨_, rfl, ?_⟩,
    Hide.intro ⟨_, heap_alloc2_old hT2, ?_⟩⟩
  · rw [State.heap_alloc, ite_eq_left (by simp [State.next_alloc])]
  · -- the four fields
    have htid2 : JStrAt σ2 tidV (cp037Str g.parm ++ zpadJ (kOf g i.toInt.toNat) 6) :=
      jstrAt_agree (Hide.elim htid) hag hn2
    simp only [tvals, Model.tranVals]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
    · refine ⟨tidV, by simp [fields_get_set], ?_⟩
      rw [tranId_text _ hkOf]
      exact jstrAt_alloc2 htid2
    · refine ⟨.ref σ.next, by simp [fields_get_set], σ.next, rfl, ?_⟩
      rw [heap_alloc2_old h01, cp037Str_01]
    · show Fields.get _ _ = _
      simp [fields_get_set]
    · refine ⟨.ref (σ.next + 1), by simp [fields_get_set], σ.next + 1, rfl, ?_⟩
      rw [heap_alloc2_old hsys, cp037Str_system]

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-- `TranSet` survives a stretch that changes only `T`, keeping the fields already set. -/
theorem tranSet_agree {σ σ2 : State} {T : Addr} {m : Nat} {vals : List FV}
    {fs fs2 : List (FieldKey × Value)} (h : TranSet σ T m vals)
    (hT : σ.heap T = some (.plain "Cbact04c$TranRecord" fs)) (ha : Agree σ σ2 [T])
    (hT2 : σ2.heap T = some (.plain "Cbact04c$TranRecord" fs2))
    (hk : ∀ k ∈ (TranRecord.fields.take m).map (·.jname), Fields.get fs2 ("Cbact04c$TranRecord", k) =
      Fields.get fs ("Cbact04c$TranRecord", k)) : TranSet σ2 T m vals := by
  obtain ⟨fs0, h1, h2⟩ := h
  rw [hT] at h1
  cases h1
  have hn : NoStr σ [T] := by
    intro w hw' st hst
    rw [List.mem_singleton] at hw'
    subst hw'
    rw [hT] at hst
    cases hst
  refine ⟨fs2, hT2, ?_⟩
  have hs : StrKeep σ σ2 := by
    intro a s ha'
    rw [ha.2 a (State.lt_next_of_heap ha') (fun hm => by
      rw [List.mem_singleton] at hm; subst hm; rw [hT] at ha'; cases ha'), ha']
  exact forall2_jfield_copy hs h2 (fun f hf => hk f.jname (List.mem_map_of_mem hf))

/-- One more field of `T` holds the record's value (no state change). -/
theorem tranSet_extend {σ : State} {T : Addr} {m : Nat} {vals : List FV}
    {fs : List (FieldKey × Value)} (h : TranSet σ T m vals)
    (hT : σ.heap T = some (.plain "Cbact04c$TranRecord" fs)) (hm : m < 14) (hlen : vals.length = 14)
    (hnew : jFieldAt σ "Cbact04c$TranRecord" fs (TranRecord.fields.getD m default)
      (vals.getD m default)) : TranSet σ T (m + 1) vals := by
  obtain ⟨fs0, h1, h2⟩ := h
  rw [hT] at h1
  cases h1
  refine ⟨_, hT, ?_⟩
  have hfl : TranRecord.fields.length = 14 := by decide
  rw [List.take_add_one, List.take_add_one]
  rw [List.getElem?_eq_getElem (by omega : m < TranRecord.fields.length),
    List.getElem?_eq_getElem (by omega : m < vals.length)]
  simp only [Option.toList_some]
  refine forall2_append ?_ h2
  have e1 : TranRecord.fields[m]'(by omega) = TranRecord.fields.getD m default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have e2 : vals[m]'(by omega) = vals.getD m default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [e1, e2]
  exact hnew

theorem tvals_length (g : G) (n : Nat) : (tvals g n).length = 14 := by
  simp [tvals, Model.tranVals]

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxRecDepth 100000 in
theorem cp037Str_descHead : cp037Str CardDemo.Cbact04c.descHead = JStr.ofString "Int. for a/c " := by
  decide

theorem desc_text (id : Int) :
    cp037Str (CardDemo.Cbact04c.descHead ++ Cobol.encodeNum {} CardDemo.Cbact04c.ACCT_ID.fmt id ++
      Model.sp 76) = JStr.ofString "Int. for a/c " ++ zpadJ id.natAbs 11 ++ spJ 76 := by
  rw [cp037Str_append, cp037Str_append, cp037Str_descHead, encode_zpadJ (by decide) (by decide)
    (by decide), cp037Str_sp]
  try rfl

/-- **Description, amount, merchant id set** (statements 217–223): the cut point 224. -/
theorem j224_of {g : G} {σ0 σ σ2 : State} {fr' : Frame} {i : I32} {hp : Hp}
    {tcbV acctV xrefV lastV : Value} {fsT : List (FieldKey × Value)} {dn : Addr}
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
    (hset : Hide (TranSet σ hp.T 4 (tvals g i.toInt.toNat)))
    (hT : σ.heap hp.T = some (.plain "Cbact04c$TranRecord" fsT))
    (hag : Agree σ σ2 [hp.T]) (hi2 : σ2.inits = σ.inits)
    (hT2 : σ2.heap hp.T = some (.plain "Cbact04c$TranRecord"
      (Fields.set (Fields.set (Fields.set fsT ("Cbact04c$TranRecord", "tranDesc") (.ref dn))
        ("Cbact04c$TranRecord", "tranAmt") (.long (BitVec.ofInt 64 (amtOf g i.toInt.toNat))))
        ("Cbact04c$TranRecord", "tranMerchantId") (.long 0#64))))
    (hdn : σ2.heap dn = some (.str (JStr.ofString "Int. for a/c " ++
      zpadJ (Model.aId (sel g i.toInt.toNat).acct).natAbs 11 ++ spJ 76))) :
    J224 g g.args σ0 fr' σ2 := by
  have hL := Hide.elim hheap
  obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := hL.1
  have hTstr : ∀ x s, σ.heap x = some (.str s) → x ∉ [hp.T] := by
    intro x s hx hm; rw [List.mem_singleton] at hm; subst hm; rw [hT] at hx; cases hx
  have hok2 : TranOk σ2 hp.T := by
    obtain ⟨fs0, h1, h2, -, ⟨f, h7, h8⟩⟩ := htr
    rw [hT] at h1
    cases h1
    refine ⟨_, hT2, fun k hk => ?_, ⟨dn, _, by simp [fields_get_set], hdn, ?_, ?_⟩, ⟨f, ?_, ?_⟩⟩
    · simp only [fields_get_set]
      split
      · exact ⟨_, rfl⟩
      split
      · exact ⟨_, rfl⟩
      split
      · exact ⟨_, rfl⟩
      · exact h2 k hk
    · simp [zpadJ_length, spJ_length]
    · rw [List.drop_left' (by simp [zpadJ_length])]
    · simp only [fields_get_set]; simpa using h7
    · rw [hag.2 f (State.lt_next_of_heap h8) (hTstr f _ h8), h8]
  have hL2 := loopHeap_agreeT hL hT hag hok2 hi2
  have hn2 : NoStr σ [hp.T] := fun w hw' st hst => hTstr w st hst hw'
  have htcb2 : JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ2 tcbV (g.trec i.toInt.toNat) := by
    have hr := Hide.elim htcb
    obtain ⟨x, fsx, hx, hxh, -⟩ := id hr
    subst hx
    exact jrecAt_agree hr hag hn2 (not_T_of_cls hT hxh (by decide))
  have hk4 : (TranRecord.fields.take 4).map (·.jname) =
      ["tranId", "tranTypeCd", "tranCatCd", "tranSource"] := by decide
  have hs4 := tranSet_agree (Hide.elim hset) hT hag hT2 (by
    rw [hk4]
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> simp [fields_get_set])
  have hl := tvals_length g i.toInt.toNat
  have hs5 := tranSet_extend hs4 hT2 (by decide) hl (by
    refine ⟨.ref dn, by simp [fields_get_set], dn, rfl, ?_⟩
    try simp only [tvals, Model.tranVals, List.getD_cons_succ, List.getD_cons_zero]
    rw [desc_text, hdn])
  have hs6 := tranSet_extend hs5 hT2 (by decide) hl (by
    show Fields.get _ _ = _
    simp [fields_get_set, tvals, Model.tranVals])
  have hs7 := tranSet_extend hs6 hT2 (by decide) hl (by
    show Fields.get _ _ = _
    simp [fields_get_set, tvals, Model.tranVals])
  exact ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, Hide.intro htcb2⟩, f3,
    f11, f12, f14, f25, f16, f17, Hide.intro hL2, hrate⟩, Hide.intro hs7⟩

end EquivLean.Modernize.Cbact04c.Java

namespace EquivLean.Modernize.Cbact04c.Java

/-- A state that agrees with `σ` outside `T`, from `jvc`'s description of its heap below a bound. -/
theorem agree_of_heapFn {σ σ2 : State} {T : Addr} {n : Nat} {H : Addr → Option Obj}
    (hn : σ.next ≤ n) (hle : n ≤ σ2.next) (hR : ∀ x, x < n → σ2.heap x = H x)
    (hHo : ∀ x, x < σ.next → x ≠ T → H x = σ.heap x) : Agree σ σ2 [T] :=
  ⟨Nat.le_trans hn hle, fun x hx hxT => by
    rw [hR x (Nat.lt_of_lt_of_le hx hn)]
    exact hHo x hx (fun e => hxT (by rw [e]; exact List.mem_singleton_self _))⟩

/-- `j217_of` with the post-state given by `jvc`'s heap description. -/
theorem j217_of' {g : G} {σ0 σ σ2 : State} {fr' : Frame} {i : I32} {hp : Hp}
    {tcbV acctV xrefV lastV tidV : Value} {fsT : List (FieldKey × Value)} {R HEAD : JStr}
    {H : Addr → Option Obj}
    (hn : i.toInt.toNat < g.tcat.length) (hi0 : 0 ≤ i.toInt) (hlocs : Locs g hp fr')
    (f22 : fr'.get 22 = some (.int (i + 1#32))) (f6 : fr'.get 6 = some tcbV)
    (f4 : fr'.get 4 = some (.int 0#32)) (f5 : fr'.get 5 = some (.int 0#32))
    (f3 : fr'.get 3 = some (.int 0#32))
    (f11 : fr'.get 11 = some (.long (BitVec.ofInt 64 (amtOf g i.toInt.toNat))))
    (f12 : fr'.get 12 = some (.long (BitVec.ofInt 64 (totOf g i.toInt.toNat))))
    (f14 : fr'.get 14 = some (.long (BitVec.ofNat 64 (kOf g i.toInt.toNat))))
    (f25 : fr'.get 25 = some lastV) (f16 : fr'.get 16 = some acctV)
    (f17 : fr'.get 17 = some xrefV) (f27 : fr'.get 27 = some (.ref (σ2.next + 1)))
    (htcb : Hide (JRecAt TranCatBalRecord "Cbact04c$TranCatBalRecord" σ tcbV
      (g.trec i.toInt.toNat)))
    (hheap : Hide (LoopHeap g σ0 σ hp (sel g i.toInt.toNat) acctV xrefV lastV))
    (hrate : rateOf g i.toInt.toNat ≠ 0)
    (htid : Hide (JStrAt σ tidV (cp037Str g.parm ++ zpadJ (kOf g i.toInt.toNat) 6)))
    (hT : σ.heap hp.T = some (.plain "Cbact04c$TranRecord" fsT))
    (hle : σ.next + 1 + 1 ≤ σ2.next) (hR : ∀ x, x < σ.next + 1 + 1 → σ2.heap x = H x)
    (hi2 : σ2.inits = σ.inits)
    (hHo : ∀ x, x < σ.next → x ≠ hp.T → H x = σ.heap x)
    (hHT : H hp.T = some (.plain "Cbact04c$TranRecord"
      (Fields.set (Fields.set (Fields.set (Fields.set fsT ("Cbact04c$TranRecord", "tranId") tidV)
        ("Cbact04c$TranRecord", "tranTypeCd") (.ref σ.next)) ("Cbact04c$TranRecord", "tranCatCd")
        (.long 5#64)) ("Cbact04c$TranRecord", "tranSource") (.ref (σ.next + 1)))))
    (hH0 : H σ.next = some (.str [48#16, 49#16]))
    (hHs : H (σ.next + 1) = some (.str (JStr.ofString "System    ")))
    (hHEAD : HEAD = JStr.ofString "Int. for a/c " ++
      zpadJ (Model.aId (sel g i.toInt.toNat).acct).natAbs 11) :
    J217 g g.args σ0 fr' ((σ2.alloc (.str R)).snd.alloc (.str HEAD)).snd := by
  have hTlt := State.lt_next_of_heap hT
  have hT' : hp.T < σ.next + 1 + 1 := by jomega
  exact j217_of hn hi0 hlocs f22 f6 f4 f5 f3 f11 f12 f14 f25 f16 f17 f27 htcb hheap hrate htid hT
    (agree_of_heapFn (n := σ.next + 1 + 1) (by jomega) hle hR hHo) hi2
    (by rw [hR hp.T hT']; exact hHT) (by rw [hR σ.next (by jomega)]; exact hH0)
    (by rw [hR (σ.next + 1) (by jomega)]; exact hHs) hHEAD

end EquivLean.Modernize.Cbact04c.Java

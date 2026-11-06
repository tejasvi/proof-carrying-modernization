import EquivLean.Modernize.Cbact04c.Every.JavaRunResDflt

/-!
# CBACT04C → Java, `run`: statements 184–195 (the `DEFAULT` disclosure group)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- **The `DEFAULT` group has a record**: its rate (statements 184–188, the cut point 196). -/
theorem run_seg184_found (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J184 g g.args σ0 fr σ)
    (c185 : cuts.lookup 185 = none) (c186 : cuts.lookup 186 = none)
    (c187 : cuts.lookup 187 = none) (c188 : cuts.lookup 188 = none)
    (c196 : cuts.lookup 196 = some (J196 g g.args σ0))
    (hc : ∀ i : I32, fr.get 22 = some (.int (i + 1#32)) → defDisc g (g.trec i.toInt.toNat) ≠ []) :
    RunWPc g σ0 cuts 184 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ts, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, f3,
    f12, f14, f25, f16, f17, f28, hts, f11, hheap, hm⟩ := h
  have hdf := hc i f22
  have hvt := trec_valid hpre hn
  obtain ⟨et4, xs4, ha4, hlen4, hds, hv4⟩ := discArr_of_pre hpre (Hide.elim hheap).1.1
  clear hpre hc
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  obtain ⟨fsy, tyA, fiA, hyh, -, ht1, htyA, ht2, -, -, -, -, -, hc0, hc1, -, -, -, -⟩ :=
    tcb_facts (Hide.elim htcb) hvt
  -- the `DEFAULT` record
  obtain ⟨jd, hjd⟩ : ∃ jd, g.discs.findIdx? (fun d => Model.dGrp d == Model.defaultGrp &&
      Model.dType d == Model.tType (g.trec i.toInt.toNat) &&
      Model.dCat d == Model.tCat (g.trec i.toInt.toNat)) = some jd := by
    cases hf : g.discs.findIdx? (fun d => Model.dGrp d == Model.defaultGrp &&
        Model.dType d == Model.tType (g.trec i.toInt.toNat) &&
        Model.dCat d == Model.tCat (g.trec i.toInt.toNat)) with
    | none => exact absurd (defDisc_nil hf) hdf
    | some jd => exact ⟨jd, rfl⟩
  -- the state after the literal `"DEFAULT   "`
  have hgs' : (σ.alloc (.str [68#16, 69#16, 70#16, 65#16, 85#16, 76#16, 84#16, 32#16, 32#16,
      32#16])).2.heap σ.next = some (.str (cp037Str Model.defaultGrp)) := by
    rw [State.heap_alloc, if_pos rfl, cp037Str_defaultGrp]
  have ha4' := heap_of_grows (grows_alloc σ (.str [68#16, 69#16, 70#16, 65#16, 85#16, 76#16, 84#16,
    32#16, 32#16, 32#16])) ha4
  have hts' := heap_of_grows (grows_alloc σ (.str [68#16, 69#16, 70#16, 65#16, 85#16, 76#16, 84#16,
    32#16, 32#16, 32#16])) hts
  have hds' := forall2_mono (fun _ _ h => jrecAt_grows (grows_alloc σ (.str [68#16, 69#16, 70#16,
    65#16, 85#16, 76#16, 84#16, 32#16, 32#16, 32#16])) h) hds
  have hdidx := discIdx_disc ha4' hgs' hts' hds' hv4 hc0 hc1 hjd
  obtain ⟨hjl, -, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hjd
  have hxl := Forall2.length_eq hds
  have hjx : jd < xs4.length := by omega
  have hjv : (BitVec.ofNat 32 jd).toInt = (jd : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  have hrel := forall2_getElem hds' jd hjx
  obtain ⟨dk, fsk, hdkE, hdkh, hfk⟩ := jrec_obj hrel
  have hpresk := present_keys disGroupRecord_jnames hfk
  have hdk : xs4[jd]? = some (.ref dk) := by rw [List.getElem?_eq_getElem hjx, hdkE]
  have hdkh0 : σ.heap dk = some (.plain "Cbact04c$DisGroupRecord" fsk) := by
    have hne : dk ≠ σ.next := by
      intro e
      rw [e, State.heap_alloc, if_pos rfl] at hdkh
      cases hdkh
    rwa [State.heap_alloc, if_neg hne] at hdkh
  have hlenv : (BitVec.ofNat 32 g.discs.length).toInt = (xs4.length : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  have hpre' := Hide.intro (⟨hlen4, hlenv, discArr_of hds' hv4⟩ :
    xs4.length < 2147483648 ∧ (BitVec.ofNat 32 g.discs.length).toInt = (xs4.length : Int) ∧
      DiscArr (σ.alloc (.str [68#16, 69#16, 70#16, 65#16, 85#16, 76#16, 84#16, 32#16, 32#16,
        32#16])).2 xs4)
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hds'' := Hide.intro hds'
  have hjd' := Hide.intro hjd
  have hm' := Hide.intro hm
  have hheap' := Hide.intro (loopHeap_grows (Hide.elim hheap) (grows_alloc σ (.str [68#16, 69#16,
    70#16, 65#16, 85#16, 76#16, 84#16, 32#16, 32#16, 32#16])) rfl)
  have htcb' := Hide.intro (jrecAt_grows (grows_alloc σ (.str [68#16, 69#16, 70#16, 65#16, 85#16,
    76#16, 84#16, 32#16, 32#16, 32#16])) (Hide.elim htcb))
  clear hds hds' hjd hrel hfk hv4 hxl hjl hlen4 hlenv hm hvt ha4 hts
  generalize hcatE : BitVec.ofInt 64 (Model.tCat (g.trec i.toInt.toNat)) = cat at f11 ht2 hdidx
  have hcatE' := Hide.intro hcatE
  clear hcatE
  unfold RunWPc
  jvc [runSpecG, runC, findDiscSig, copyDisSig, Grows]
  all_goals first
    -- `findDisc`'s precondition
    | (obtain ⟨hl4, hlv, harr⟩ := Hide.elim hpre'
       exact ⟨g.a4, _, σ.next, ts, _, _, cat, et4, xs4, rfl, ha4', hlv, hl4, hgs', hts', harr⟩)
    -- `copyDis`'s precondition
    | exact ⟨fsk, hdkh0, hpresk⟩
    | skip
  have hcatE := Hide.elim hcatE'
  subst hcatE
  apply j196_of_default hn hi0 hstop
  case htcb => exact Hide.elim htcb'
  case hheap => exact Hide.elim hheap'
  case hm => exact Hide.elim hm'
  case hds => exact Hide.elim hds''
  case hjd => exact Hide.elim hjd'
  case hdk => exact hdk
  case hdc => assumption
  case hkc => assumption
  case hg =>
    refine ⟨by simp only [State.next_alloc]; jomega, fun x hx => ?_⟩
    simp only [State.next_alloc] at hx
    chain_simp
  case hi => assumption
  case hlocs => locs_tac
  all_goals first
    | (frame_simp [f3, f12, f14, f25, f16, f17, f22, f6, f4, f5]; done)
    | (frame_simp []; done)

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
/-- **The `DEFAULT` group has no record either**: the run abends (statements 184–185, 189–195). -/
theorem run_seg184_missing (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreG g g.args σ0) (h : J184 g g.args σ0 fr σ)
    (c185 : cuts.lookup 185 = none) (c189 : cuts.lookup 189 = none)
    (c190 : cuts.lookup 190 = none) (c191 : cuts.lookup 191 = none)
    (c192 : cuts.lookup 192 = none) (c193 : cuts.lookup 193 = none)
    (c194 : cuts.lookup 194 = none) (c195 : cuts.lookup 195 = none)
    (hc : ∀ i : I32, fr.get 22 = some (.int (i + 1#32)) → defDisc g (g.trec i.toInt.toNat) = []) :
    RunWPc g σ0 cuts 184 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ts, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, f3,
    f12, f14, f25, f16, f17, f28, hts, f11, hheap, hm⟩ := h
  have hdf := hc i f22
  have hvt := trec_valid hpre hn
  have hin := inFacts_of_pre hpre
  obtain ⟨et4, xs4, ha4, hlen4, hds, hv4⟩ := discArr_of_pre hpre (Hide.elim hheap).1.1
  clear hpre hc
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  obtain ⟨fsy, tyA, fiA, hyh, -, ht1, htyA, ht2, -, -, -, -, -, hc0, hc1, -, -, -, -⟩ :=
    tcb_facts (Hide.elim htcb) hvt
  -- no `DEFAULT` record
  have hjd : g.discs.findIdx? (fun d => Model.dGrp d == Model.defaultGrp &&
      Model.dType d == Model.tType (g.trec i.toInt.toNat) &&
      Model.dCat d == Model.tCat (g.trec i.toInt.toNat)) = none := by
    cases hf : g.discs.findIdx? (fun d => Model.dGrp d == Model.defaultGrp &&
        Model.dType d == Model.tType (g.trec i.toInt.toNat) &&
        Model.dCat d == Model.tCat (g.trec i.toInt.toNat)) with
    | none => rfl
    | some jd =>
      exfalso
      obtain ⟨hjl, hdef⟩ := defDisc_eq hf
      rw [hdef] at hdf
      exact hin.discs_ne _ (List.getElem_mem hjl) hdf
  have hgs' : (σ.alloc (.str [68#16, 69#16, 70#16, 65#16, 85#16, 76#16, 84#16, 32#16, 32#16,
      32#16])).2.heap σ.next = some (.str (cp037Str Model.defaultGrp)) := by
    rw [State.heap_alloc, if_pos rfl, cp037Str_defaultGrp]
  have ha4' := heap_of_grows (grows_alloc σ (.str [68#16, 69#16, 70#16, 65#16, 85#16, 76#16, 84#16,
    32#16, 32#16, 32#16])) ha4
  have hts' := heap_of_grows (grows_alloc σ (.str [68#16, 69#16, 70#16, 65#16, 85#16, 76#16, 84#16,
    32#16, 32#16, 32#16])) hts
  have hds' := forall2_mono (fun _ _ h => jrecAt_grows (grows_alloc σ (.str [68#16, 69#16, 70#16,
    65#16, 85#16, 76#16, 84#16, 32#16, 32#16, 32#16])) h) hds
  have hdidx := discIdx_none ha4' hgs' hts' hds' hv4 hc0 hc1 hjd
  have hxl := Forall2.length_eq hds
  have hlenv : (BitVec.ofNat 32 g.discs.length).toInt = (xs4.length : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  have hpre' := Hide.intro (⟨hlen4, hlenv, discArr_of hds' hv4⟩ :
    xs4.length < 2147483648 ∧ (BitVec.ofNat 32 g.discs.length).toInt = (xs4.length : Int) ∧
      DiscArr (σ.alloc (.str [68#16, 69#16, 70#16, 65#16, 85#16, 76#16, 84#16, 32#16, 32#16,
        32#16])).2 xs4)
  -- the result object and the display list
  have hfnd := found_of_loopHeap (Hide.elim hheap)
  obtain ⟨-, hinit, -, hres, hdisp, -⟩ := (Hide.elim hheap).1
  obtain ⟨fsR, hR, hRd, hRw, hRr, hRa⟩ := hres
  obtain ⟨dxs, dm, hld, -⟩ := hdisp
  have hrl : hp.res ≠ hp.ld := by intro e; rw [e, hld] at hR; cases hR
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hout := out_default_missing hin hn hstop hfnd.1 hfnd.2 hm hdf
  have hout' := Hide.intro hout
  clear hds hds' hjd hv4 hxl hlen4 hlenv hvt ha4 hts hout hfnd hin
  generalize hcatE : BitVec.ofInt 64 (Model.tCat (g.trec i.toInt.toNat)) = cat at f11 ht2 hdidx
  have hcatE' := Hide.intro hcatE
  clear hcatE
  unfold RunWPc
  jvc [runSpecG, runC, findDiscSig, Grows, evalDynamic, concatRecipe, Native.valueOfArg,
    Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, Native.primStr, JType.isRef, inlineFuel]
  all_goals first
    -- `findDisc`'s precondition
    | (obtain ⟨hl4, hlv, harr⟩ := Hide.elim hpre'
       exact ⟨g.a4, _, σ.next, ts, _, _, cat, et4, xs4, rfl, ha4', hlv, hl4, hgs', hts', harr⟩)
    | skip
  apply runPost_abend (Hide.elim hheap).1 hld hR
  case hout => exact Hide.elim hout'
  case hld' => chain_simp
  case hR' => chain_simp
  case hag =>
    refine ⟨by simp only [State.next_setObj, State.next_alloc]; jomega, fun x hx hw => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
    obtain ⟨hw1, hw2⟩ := hw
    chain_simp
  case hvs =>
    refine .cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ .nil))
    all_goals chain_simp
    all_goals simp only [jline]
    all_goals first | rfl | decide

end EquivLean.Modernize.Cbact04c.Java

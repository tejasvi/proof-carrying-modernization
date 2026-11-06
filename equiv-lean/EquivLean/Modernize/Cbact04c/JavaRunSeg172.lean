import EquivLean.Modernize.Cbact04c.JavaRunRes172

/-!
# CBACT04C → Java, `run`: statements 172–179 (the disclosure group record read and copied)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg172 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (hpre : RunPreG g g.args σ0)
    (h : J172 g g.args σ0 fr σ)
    (c173 : cuts.lookup 173 = none) (c174 : cuts.lookup 174 = none)
    (c175 : cuts.lookup 175 = none) (c176 : cuts.lookup 176 = none)
    (c177 : cuts.lookup 177 = none) (c178 : cuts.lookup 178 = none)
    (c179 : cuts.lookup 179 = none) (c196 : cuts.lookup 196 = some (J196 g g.args σ0)) :
    RunWPc g σ0 cuts 172 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, f3, f12, f14,
    f25, f16, f17, hheap⟩ := h
  have hin := inFacts_of_pre hpre
  have hst := stInv_st hin i.toInt.toNat
  have hvt := trec_valid hpre hn
  have hmemT : g.trec i.toInt.toNat ∈ g.tcat := by
    simp only [G.trec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem _
  have hst2 := stInv_stSel hst hvt (hin.dom.2 _ hmemT).1
  have hl2 := stSel_lastId g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)
  obtain ⟨et4, xs4, ha4, hlen4, hds, hv4⟩ := discArr_of_pre hpre (Hide.elim hheap).1.1
  clear hpre
  obtain ⟨jd, hjd⟩ := disc_exists hin hst2 hmemT hl2
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  obtain ⟨fsy, tyA, fiA, hyh, -, ht1, htyA, ht2, -, -, -, -, -, hc0, hc1, -, -, -, -⟩ :=
    tcb_facts (Hide.elim htcb) hvt
  -- the account object's group
  have hsome : (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).lastId.isSome := by
    rw [hl2]; rfl
  have hacc := (Hide.elim hheap).2.1 hsome
  have hva := acct_valid hst2 hl2
  obtain ⟨ac, fsa, hacV, hac, hfa⟩ := jrec_obj hacc
  obtain ⟨gref, hgf, hgs⟩ := jfield_str hfa hva (i := 11) (by decide) (j := false) (by decide)
  rw [show (AccountRecord.fields.getD 11 default).jname = "acctGroupId" from rfl] at hgf
  subst hacV
  -- `findDisc`'s result
  have hdidx := discIdx_disc ha4 hgs htyA hds hv4 hc0 hc1 hjd
  obtain ⟨hjl, -, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hjd
  have hxl := Forall2.length_eq hds
  have hjx : jd < xs4.length := by omega
  have hjv : (BitVec.ofNat 32 jd).toInt = (jd : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  have hrel := forall2_getElem hds jd hjx
  obtain ⟨dk, fsk, hdkE, hdkh, hfk⟩ := jrec_obj hrel
  have hpresk := present_keys disGroupRecord_jnames hfk
  have hdk : xs4[jd]? = some (.ref dk) := by rw [List.getElem?_eq_getElem hjx, hdkE]
  -- `findDisc`'s precondition (closed after `jvc`)
  have hkey : ∃ x ∈ xs4, discKeyOf σ x = some (cp037Str (Model.aGrp
      (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).acct),
      cp037Str (Model.tType (g.trec i.toInt.toNat)), BitVec.ofInt 64 (Model.tCat (g.trec i.toInt.toNat))) :=
    ⟨_, List.getElem_mem hjx, (disc_key_iff hrel (hv4 _ (List.getElem_mem hjl)) _ _ hc0 hc1).2
      (List.findIdx?_eq_some_iff_getElem.1 hjd).2.1⟩
  have hlenv : (BitVec.ofNat 32 g.discs.length).toInt = (xs4.length : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  have hpre' := Hide.intro (⟨hlen4, hlenv, discArr_of hds hv4, hkey⟩ :
    xs4.length < 2147483648 ∧ (BitVec.ofNat 32 g.discs.length).toInt = (xs4.length : Int) ∧
      DiscArr σ xs4 ∧ _)
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hds' := Hide.intro hds
  have hjd' := Hide.intro hjd
  clear hds hjd hrel hfk hkey hst hst2 hin hvt hmemT hl2 hsome hacc hva hfa hv4 hxl hjl hlen4 hlenv
  generalize BitVec.ofInt 64 (Model.tCat (g.trec i.toInt.toNat)) = cat at ht2 hdidx hpre'
  unfold RunWPc
  jvc [runSpecG, runC, findDiscSig, copyDisSig, Grows]
  all_goals first
    -- `findDisc`'s precondition
    | (obtain ⟨hl4, hlv, harr, hk⟩ := Hide.elim hpre'
       exact ⟨g.a4, _, gref, tyA, _, _, cat, et4, xs4, rfl, ha4, hlv, hl4, hgs, htyA, harr, hk⟩)
    -- the cut point 196
    | (refine j196_of_copy hn hi0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htcb hheap hds' (Hide.elim hjd')
         hdk ‹_› ‹_› ⟨‹_›, ‹_›⟩ ‹_›
       all_goals first
         | (locs_tac; done)
         | (frame_simp [f3, f12, f14, f25, f16, f17, f22, f6, f4, f5]; done)
         | skip)
    | skip

end EquivLean.Modernize.Cbact04c.Java

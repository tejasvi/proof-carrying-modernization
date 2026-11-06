import EquivLean.Modernize.Cbact04c.JavaRunRes108

/-!
# CBACT04C → Java, `run`: statements 108–112 (the posted account stored into the table copy)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_seg108 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (hpre : RunPreG g g.args σ0)
    (h : J108 g g.args σ0 fr σ)
    (c109 : cuts.lookup 109 = none) (c110 : cuts.lookup 110 = none)
    (c111 : cuts.lookup 111 = none) (c112 : cuts.lookup 112 = none)
    (c113 : cuts.lookup 113 = some (J113 g g.args σ0)) :
    RunWPc g σ0 cuts 108 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, hsome, hne, f3, f14, f16,
    hcore, hpst⟩ := h
  have hst := stInv_st (inFacts_of_pre hpre) i.toInt.toNat
  obtain ⟨-, -, hlenG, -⟩ := hpre.lens
  clear hpre
  obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨hacc0, -, hexg, hid0, hid1⟩ := hst.2.2.2.1 id hid
  have hex' := exists_aId_of_map hst.1 hexg
  have hacid : Model.aId (g.st i.toInt.toNat).acct = id := by
    rw [hacc0]; exact (Model.findAcct_spec _ id hex').2
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  -- the posted account object
  obtain ⟨ac, fsp, hacV, hac, hfp⟩ := jrec_obj (Hide.elim hpst)
  subst hacV
  have hvp := valid_posted (acct_valid hst hid) hst.2.2.2.2.1 hst.2.2.2.2.2.1
  have hpres := present_keys accountRecord_jnames hfp
  have hkey : Fields.get fsp ("Cbact04c$AccountRecord", "acctId") =
      some (.long (BitVec.ofInt 64 id)) := by
    rw [← hacid, ← Model.aId_posted _ (g.st i.toInt.toNat).total]
    exact jfield_num hfp hvp (i := 0) (by decide) (fmt := {digits := 11}) (by decide)
  -- the table copy, the `Result`, the rewrite list
  obtain ⟨-, hinit, -, hres, -, -, hrw, htab, -⟩ := Hide.elim hcore
  obtain ⟨axs, hA, haa, -⟩ := htab
  simp only [disp1] at haa
  obtain ⟨fsR, hR, -, -, hRr, -⟩ := hres
  obtain ⟨rxs, rm, hlr, -, -⟩ := hrw
  have hvalid : ∀ a ∈ (g.st i.toInt.toNat).accts, AccountRecord.Valid a := hst.2.2.1
  have harr := acctArr_of haa hvalid
  have hkm := acct_key_mem haa hvalid hex'
  have hlenS : (g.st i.toInt.toNat).accts.length = g.accts.length := by
    have := congrArg List.length hst.1
    simpa using this
  have hlenA : axs.length < 2147483648 := by rw [Forall2.length_eq haa]; omega
  obtain ⟨j, hj⟩ : ∃ j, (g.st i.toInt.toNat).accts.findIdx? (fun a => Model.aId a == id) = some j := by
    cases hf : (g.st i.toInt.toNat).accts.findIdx? (fun a => Model.aId a == id) with
    | none =>
      rw [List.findIdx?_eq_none_iff] at hf
      obtain ⟨a, ha, he⟩ := hex'
      have := hf a ha
      simp [he] at this
    | some j => exact ⟨j, rfl⟩
  have hjlen : j < axs.length := by
    rw [Forall2.length_eq haa]
    exact (List.findIdx?_eq_some_iff_getElem.1 hj).1
  have hidx := acctIdx_table hA haa hvalid hid0 hid1 hj
  have hjv : (BitVec.ofNat 32 j).toInt = (j : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  have hresA : hp.res ≠ hp.A := by intro e; rw [e, hA] at hR; cases hR
  have hlrA : hp.lr ≠ hp.A := by intro e; rw [e, hA] at hlr; cases hlr
  have hacA : ac ≠ hp.A := by intro e; rw [e, hA] at hac; cases hac
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hj' := Hide.intro hj
  have hex'' := Hide.intro hex'
  have hacid' := Hide.intro hacid
  have hsome' := Hide.intro hsome
  have hst' := Hide.intro hst
  have harr' := Hide.intro harr
  clear hj hex' hacid hst hfp hvp hacc0 hexg hvalid haa hid0 hid1 harr hsome hlenS
  generalize BitVec.ofInt 64 id = key at hkey hidx hkm
  have hkm' := Hide.intro hkm
  clear hkm
  have hneH := Hide.intro hne
  clear hne
  unfold RunWPc
  jvc [runSpecG, runC, findAcctSig, copyAcctSig, Grows]
  all_goals first
    -- `findAcct`'s precondition
    | exact ⟨hp.A, key, _, axs, rfl, hA, hlenA, Hide.elim harr', Hide.elim hkm'⟩
    -- the cut point 113
    | (refine j113_of_store hn hi0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ htcb hcore hpst (Hide.elim hsome')
         (Hide.elim hneH) (Hide.elim hacid') (Hide.elim hj') hac hA hacA ‹_› ‹_› ⟨‹_›, ‹_›⟩ ‹_›
       all_goals first
         | (locs_tac; done)
         | (frame_simp [f3, f14, f16, f22, f6, f4, f5]; done)
         | skip)
    | skip

end EquivLean.Modernize.Cbact04c.Java

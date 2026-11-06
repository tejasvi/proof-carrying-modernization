-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermSeg172d.lean (sha256 11cc10ec4ee30371...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunSeg172d
import EquivLean.Modernize.Cbact04c.Every.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg172d`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg172_dflt (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576) (hpre : RunPreG g g.args σ0)
    (h : J172 g g.args σ0 fr σ)
    (c173 : cuts.lookup 173 = none) (c174 : cuts.lookup 174 = none)
    (c175 : cuts.lookup 175 = none) (c176 : cuts.lookup 176 = none)
    (c180 : cuts.lookup 180 = none) (c181 : cuts.lookup 181 = none)
    (c182 : cuts.lookup 182 = none) (c183 : cuts.lookup 183 = none)
    (c184 : cuts.lookup 184 = some (fun fr' σ' => runVs B 184 g.args σ0 fr' σ' < runVs B 172 g.args σ0 fr σ))
    (hc : ∀ i : I32, fr.get 22 = some (.int (i + 1#32)) →
      grpMissing g (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat))
        (g.trec i.toInt.toNat) = true) :
    RunThinWPc g σ0 cuts 172 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, f3, f12, f14,
    f25, f16, f17, hheap⟩ := h
  have hin := inFacts_of_pre hpre
  have hst := stInv_st hin i.toInt.toNat hstop
  have hvt := trec_valid hpre hn
  have hmemT : g.trec i.toInt.toNat ∈ g.tcat := by
    simp only [G.trec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem _
  have hl2 := stSel_lastId g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)
  have hsome0 : (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).lastId.isSome := by
    rw [hl2]; rfl
  have hacc0 := jrecAt_ne_nil ((Hide.elim hheap).2.1 hsome0) (by decide)
  have hst2 := stInv_stSel hst hvt (hex_of_found hin hstop hacc0)
  have hdne := hin.discs_ne
  have hnm := hc i f22
  obtain ⟨et4, xs4, ha4, hlen4, hds, hv4⟩ := discArr_of_pre hpre (Hide.elim hheap).1.1
  clear hpre
  have hjd : g.discs.findIdx? (fun d => Model.dGrp d ==
      Model.aGrp (stSel g.xrefs (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).acct &&
      Model.dType d == Model.tType (g.trec i.toInt.toNat) &&
      Model.dCat d == Model.tCat (g.trec i.toInt.toNat)) = none := by
    unfold grpMissing at hnm
    rw [findRateO_eq, Option.isNone_map, Option.isNone_iff_eq_none, List.find?_eq_none] at hnm
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    have := hnm x hx
    simpa using this
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
  -- `findDisc`'s result: no record of the group
  have hdidx := discIdx_none ha4 hgs htyA hds hv4 hc0 hc1 hjd
  have hxl := Forall2.length_eq hds
  have hlenv : (BitVec.ofNat 32 g.discs.length).toInt = (xs4.length : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  have hpre' := Hide.intro (⟨hlen4, hlenv, discArr_of hds hv4⟩ :
    xs4.length < 2147483648 ∧ (BitVec.ofNat 32 g.discs.length).toInt = (xs4.length : Int) ∧
      DiscArr σ xs4)
  obtain ⟨-, -, -, hres, hdisp, -⟩ := (Hide.elim hheap).1
  obtain ⟨fsR, hR, hRd, hRw, hRr, hRa⟩ := hres
  obtain ⟨dxs, dm, hld, -⟩ := hdisp
  have hrl : hp.res ≠ hp.ld := by intro e; rw [e, hld] at hR; cases hR
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hds' := Hide.intro hds
  have hnm' := Hide.intro hnm
  clear hds hjd hst hst2 hin hvt hmemT hl2 hsome hacc hva hfa hv4 hxl hlen4 hlenv hnm hc
  generalize hcatE : BitVec.ofInt 64 (Model.tCat (g.trec i.toInt.toNat)) = cat at ht2 hdidx hpre'
  have hcatE' := Hide.intro hcatE
  clear hcatE
  unfold RunThinWPc
  jvc [runSpecG, runC, findDiscSig, Grows, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java

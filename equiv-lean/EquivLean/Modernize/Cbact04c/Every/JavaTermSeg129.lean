-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermSeg129.lean (sha256 4a63fe56620bca14...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunSeg129
import EquivLean.Modernize.Cbact04c.Every.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg129`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg129_found (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576) (hpre : RunPreG g g.args σ0)
    (h : J129 g g.args σ0 fr σ)
    (c130 : cuts.lookup 130 = none) (c131 : cuts.lookup 131 = none)
    (c132 : cuts.lookup 132 = none) (c133 : cuts.lookup 133 = none)
    (c145 : cuts.lookup 145 = none) (c146 : cuts.lookup 146 = none)
    (c147 : cuts.lookup 147 = none) (c148 : cuts.lookup 148 = some (fun fr' σ' => runVs B 148 g.args σ0 fr' σ' < runVs B 129 g.args σ0 fr σ))
    (hc : ∀ i : I32, fr.get 22 = some (.int (i + 1#32)) →
      ∃ a ∈ (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).accts,
        Model.aId a = Model.tAcct (g.trec i.toInt.toNat)) :
    RunThinWPc g σ0 cuts 129 fr σ := by
  obtain ⟨i, hp, tcbV, lastV, ⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, hne, f3, f12, f14, f11, f25,
    hlast, hcore⟩ := h
  have hin := inFacts_of_pre hpre
  have hst := stInv_st hin i.toInt.toNat hstop
  obtain ⟨-, -, hlenG, -⟩ := hpre.lens
  have hvt := trec_valid hpre hn
  clear hpre
  obtain ⟨y, fs, hy, -, -⟩ := jrec_obj (Hide.elim htcb)
  subst hy
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  obtain ⟨fsy, tyA, fiA, hyh, ht0, -, -, -, -, -, -, hr0, hr1, -, -, -, -, -, -⟩ :=
    tcb_facts (Hide.elim htcb) hvt
  -- the table after the rewrite, its account with the record's id
  obtain ⟨hidsR, hvalR⟩ := stRw_table hst (g.trec i.toInt.toNat)
  have hmemT : g.trec i.toInt.toNat ∈ g.tcat := by
    simp only [G.trec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    exact List.getElem_mem _
  have hexR := hc i f22
  obtain ⟨hg0, hinit, -, -, -, -, -, ⟨axs, hA, haa, -⟩, -⟩ := Hide.elim hcore
  have harr := acctArr_of haa hvalR
  have hkm := acct_key_mem haa hvalR hexR
  have hlenS : (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).accts.length = g.accts.length := by
    have := congrArg List.length hidsR
    simpa using this
  have hlenA : axs.length < 2147483648 := by rw [Forall2.length_eq haa]; omega
  obtain ⟨j, hj⟩ : ∃ j, (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).accts.findIdx?
      (fun a => Model.aId a == Model.tAcct (g.trec i.toInt.toNat)) = some j := by
    cases hf : (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).accts.findIdx?
        (fun a => Model.aId a == Model.tAcct (g.trec i.toInt.toNat)) with
    | none =>
      rw [List.findIdx?_eq_none_iff] at hf
      obtain ⟨a, ha, he⟩ := hexR
      have := hf a ha
      simp [he] at this
    | some j => exact ⟨j, rfl⟩
  have hjlen : j < axs.length := by
    rw [Forall2.length_eq haa]
    exact (List.findIdx?_eq_some_iff_getElem.1 hj).1
  have hidx := acctIdx_table hA haa hvalR hr0 hr1 hj
  have hjv : (BitVec.ofNat 32 j).toInt = (j : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> omega
  -- the account object at `j`
  have hre := forall2_getElem haa j hjlen
  obtain ⟨e, fse, hej, hxe, hfe⟩ := jrec_obj hre
  have hpres := present_keys accountRecord_jnames hfe
  have he : axs[j]? = some (.ref e) := by rw [List.getElem?_eq_getElem hjlen, hej]
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hj' := Hide.intro hj
  have harr' := Hide.intro harr
  clear hj hre hfe hvalR hidsR hexR haa hst hin hvt hmemT hg0 harr hlenS
  generalize haE : BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)) = a at f11 ht0 hidx hkm
  have haE' := Hide.intro haE
  have hkm' := Hide.intro hkm
  clear haE hkm
  have hneH := Hide.intro hne
  clear hne
  unfold RunThinWPc
  jvc [runSpecG, runC, findAcctSig, copyAcctSig, Grows, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java

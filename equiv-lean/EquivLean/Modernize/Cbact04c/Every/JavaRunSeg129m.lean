import EquivLean.Modernize.Cbact04c.Every.JavaRunResAbend

/-!
# CBACT04C → Java, `run`: statements 129–147 (the new account read and copied)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg129_missing (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (hpre : RunPreG g g.args σ0)
    (h : J129 g g.args σ0 fr σ)
    (c130 : cuts.lookup 130 = none) (c134 : cuts.lookup 134 = none) (c135 : cuts.lookup 135 = none)
    (c136 : cuts.lookup 136 = none) (c137 : cuts.lookup 137 = none) (c138 : cuts.lookup 138 = none)
    (c139 : cuts.lookup 139 = none) (c140 : cuts.lookup 140 = none) (c141 : cuts.lookup 141 = none)
    (c142 : cuts.lookup 142 = none) (c143 : cuts.lookup 143 = none) (c144 : cuts.lookup 144 = none)
    (hc : ∀ i : I32, fr.get 22 = some (.int (i + 1#32)) →
      ¬ ∃ a ∈ (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).accts,
        Model.aId a = Model.tAcct (g.trec i.toInt.toNat)) :
    RunWPc g σ0 cuts 129 fr σ := by
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
  have hno := hc i f22
  obtain ⟨hg0, hinit, -, hres, hdisp, -, -, ⟨axs, hA, haa, -⟩, -⟩ := Hide.elim hcore
  obtain ⟨fsR, hR, hRd, hRw, hRr, hRa⟩ := hres
  obtain ⟨dxs, dm, hld, -⟩ := hdisp
  have hrl : hp.res ≠ hp.ld := by intro e; rw [e, hld] at hR; cases hR
  have harr := acctArr_of haa hvalR
  have hlenS : (stRw (g.st i.toInt.toNat) (g.trec i.toInt.toNat)).accts.length = g.accts.length := by
    have := congrArg List.length hidsR
    simpa using this
  have hlenA : axs.length < 2147483648 := by rw [Forall2.length_eq haa]; omega
  have hidx := acctIdx_missing hA haa hvalR hr0 hr1 hno
  have hta := toInt_ofInt64 (v := Model.tAcct (g.trec i.toInt.toNat)) (by omega) (by omega)
  have ba : -9223372036854775808 < (BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat))).toInt := by
    rw [hta]; omega
  have hta' := Hide.intro hta
  have hno' := Hide.intro hno
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have harr' := Hide.intro harr
  clear hvalR hidsR haa hst hin hvt hmemT hg0 harr hlenS hno hta
  generalize haE : BitVec.ofInt 64 (Model.tAcct (g.trec i.toInt.toNat)) = a at f11 ht0 hidx ba
  have haE' := Hide.intro haE
  clear haE
  have hneH := Hide.intro hne
  clear hne
  unfold RunWPc
  jvc [runSpecG, runC, findAcctSig, fmtUSig, Grows, evalDynamic, concatRecipe, Native.valueOfArg,
    Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, Native.primStr, JType.isRef, inlineFuel]
  all_goals first
    -- `findAcct`'s precondition
    | exact ⟨hp.A, a, _, axs, rfl, hA, hlenA, Hide.elim harr'⟩
    | skip
  -- the abend: the outputs of the model's abend
  have haE := Hide.elim haE'
  subst haE
  apply runPost_abend (Hide.elim hcore) hld hR
  case hout => exact out_acct_missing hn hstop (Hide.elim hneH) (Hide.elim hno')
  case hld' => chain_simp
  case hR' => chain_simp
  case hag =>
    refine ⟨by simp only [State.next_setObj, State.next_alloc]; jomega, fun x hx hw => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw
    obtain ⟨hw1, hw2⟩ := hw
    chain_simp
  case hvs =>
    refine .cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ (.cons ⟨_, rfl, ?_⟩ .nil)))
    all_goals chain_simp
    all_goals simp only [jline, List.map_append, zpad_jline, Hide.elim hta', txt_accountNotFound]
    all_goals first | rfl | decide

end EquivLean.Modernize.Cbact04c.Java

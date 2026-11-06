import EquivLean.Modernize.Cbstm03b.Java.Term.Trnx

/-!
# CBSTM03B → Java, termination: `xrefProc`

As `trnxProc` (`Term.Trnx`): no loop, the calls of `status2` and `fit` answered by `seqCalleesF`; the run is
split by the operation, the file's flags, the OPEN outcome (element 1 of the outcomes array) and the position.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-- The termination paths of `xrefProc` from statement `pc`. -/
@[irreducible] def xrefTWP (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPT Gen.prog seqCalleesF.env 1)
    Gen.Cbstm03b.«xrefProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»
    [] (fun _ => True) 200 pc fr σ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem xref_tentry (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddXref oe st q opv oeM s a).pre args σ0) :
    xrefTWP 0 (Frame.init true args) σ0 := by
  obtain ⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩ := hpre
  obtain ⟨fs, hst, -, ⟨⟨x1, g1, m1⟩, -, -⟩, -, -⟩ := stateAtM_iff.1 hS
  obtain ⟨o1, fs1, l, et, xs, rfl, ho1, hopen, hrecs, hl, hlen, hrecsF, hposlt, hpos, heof⟩ := m1
  obtain ⟨q', fsq, dd, op, rc, key, kl, fldt, sdd, sop, src, skey, sfl, hqq, hq, ha, hdl, hol, hrl, hkl, hkl1, hkl2,
    hfl, gdd, jdd, gop, jop, grc, jrc, gkey, jkey, gkl, gfl, jfl⟩ := areaAt_of hA hVa
  cases hqq
  obtain ⟨fsq0, hq0, hopv⟩ := hopA
  rw [hq] at hq0
  cases hq0
  rw [gop] at hopv
  cases hopv
  obtain ⟨xop, rfl, hxop⟩ := jop
  obtain ⟨b, rfl⟩ : ∃ b, op = [b] := by
    match op, hol with
    | [b], _ => exact ⟨b, rfl⟩
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩ := hI
  have hsq : st ≠ q := ne_of_cls hst hq (by decide)
  have hso : st ≠ o1 := ne_of_cls hst ho1 (by decide)
  have hqo : q ≠ o1 := ne_of_cls hq ho1 (by decide)
  have hlt_st := State.lt_next_of_heap hst
  have hlt_q := State.lt_next_of_heap hq
  have hlt_o1 := State.lt_next_of_heap ho1
  have hxl : xs.length = s.xref.recs.length := Forall2.length_eq hrecsF
  clear hS hA hsep hK
  by_cases hbO : b = opOpen
  · subst hbO
    rw [op_texts.1] at hxop
    cases hb : s.xref.isOpen
    · rw [hb] at hopen
      obtain ⟨eta, ys, hoe, hys, hysv⟩ := hE
      obtain ⟨e0, e1, e2, e3, rfl⟩ : ∃ e0 e1 e2 e3, ys = [e0, e1, e2, e3] := by
        match ys, hys with
        | [e0, e1, e2, e3], _ => exact ⟨e0, e1, e2, e3, rfl⟩
      rcases hysv 1 (by decide) with ⟨he1, hoe1⟩ | ⟨ob, c, he1, hob, hc, hoe1⟩
      · simp only [List.getD_cons_succ, List.getD_cons_zero] at he1
        subst he1
        simp only [xrefTWP]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      · simp only [List.getD_cons_succ, List.getD_cons_zero] at he1
        subst he1
        simp only [xrefTWP]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
    · rw [hb] at hopen
      simp only [xrefTWP]
      jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
  · by_cases hbR : b = opRead
    · subst hbR
      rw [op_texts.2.1] at hxop
      cases hb : s.xref.isOpen
      · rw [hb] at hopen
        simp only [xrefTWP]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      · rw [hb] at hopen
        cases he : s.xref.eof
        · rw [he] at heof
          rcases Nat.lt_or_ge s.xref.pos s.xref.recs.length with hp | hp
          · have hvr : Model.FdXreffileRec.Valid (s.xref.recs[s.xref.pos]'hp) := hV.2.1 _ (List.getElem_mem hp)
            have hxp : s.xref.pos < xs.length := by rw [hxl]; exact hp
            have hjr := (Glue.forall2_iff.1 hrecsF).2 s.xref.pos hxp
            rw [List.getD_eq_getElem _ _ hxp, List.getD_eq_getElem _ _ hp] at hjr
            obtain ⟨xr, fsr, c, d, sc, sd, hxv, hxr, hr2, hc, hd, gc, jc, gd, jd⟩ := xrefRecAt_of hjr hvr
            obtain ⟨xsc, rfl, hxsc⟩ := jc
            obtain ⟨xsd, rfl, hxsd⟩ := jd
            have hxe : xs[s.xref.pos]? = some (.ref xr) := by rw [List.getElem?_eq_getElem hxp, hxv]
            clear hjr hvr hr2 hrecsF hV
            simp only [xrefTWP]
            set_option jimple.modelContracts true in
              jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split, StrOk, cp037Str_length, argText]
          · simp only [xrefTWP]
            jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
        · rw [he] at heof
          simp only [xrefTWP]
          jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
    · by_cases hbC : b = opClose
      · subst hbC
        rw [op_texts.2.2.2] at hxop
        cases hb : s.xref.isOpen
        · rw [hb] at hopen
          simp only [xrefTWP]
          jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
        · rw [hb] at hopen
          simp only [xrefTWP]
          jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      · have hnO : ¬ (cp037Str [b] = JStr.ofString "O") := by rw [← op_texts.1]; exact op_ne_text hbO
        have hnR : ¬ (cp037Str [b] = JStr.ofString "R") := by rw [← op_texts.2.1]; exact op_ne_text hbR
        have hnC : ¬ (cp037Str [b] = JStr.ofString "C") := by rw [← op_texts.2.2.2]; exact op_ne_text hbC
        simp only [xrefTWP]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]

/-! ## Termination -/

theorem xref_tvc (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) :
    TermVC Gen.prog seqCalleesF.env (fun _ => 0) 1 1 xrefProcRef (procSpecG ddXref oe st q opv oeM s a) [] 200 := by
  refine ⟨Gen.Cbstm03b.«xrefProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)», rfl,
    fun args σ0 hpre => ⟨?_, fun p hp => nomatch hp⟩⟩
  rw [SpecEnv.below_const _ _ (by decide)]
  have h := xref_tentry oe st q opv oeM s a args σ0 hpre
  unfold xrefTWP at h
  exact h

/-- `xrefProc` terminates, for the contract with fixed ghost values. -/
theorem xrefG_term (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) :
    ∀ args σ, (procSpecG ddXref oe st q opv oeM s a).pre args σ → MTerm Gen.prog xrefProcRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) seqCalleesF_validT seqCalleesF_term (xref_tvc oe st q opv oeM s a)

/-- **`xrefProc` terminates** on every input of `procSpec ddXref`. -/
theorem xref_term : ∀ args σ, (procSpec ddXref).pre args σ → MTerm Gen.prog xrefProcRef args σ := by
  intro args σ hpre
  obtain ⟨oe, st, q, opv, oeM, s, a, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpre
  exact xrefG_term oe st q opv oeM s a args σ ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

set_option maxHeartbeats 4000000 in
theorem xref_cterm : ContractTerm Gen.prog xrefProcSig (procSpec ddXref) := by jcontract_term [xref_term]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.xref_tentry
#print axioms EquivLean.Modernize.Cbstm03b.Java.xref_cterm

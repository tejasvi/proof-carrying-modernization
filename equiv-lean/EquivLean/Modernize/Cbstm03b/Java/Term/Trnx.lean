import EquivLean.Modernize.Cbstm03b.Java.TrnxFin
import EquivLean.Modernize.Cbstm03b.Java.Term.Helpers

/-!
# CBSTM03B → Java, termination: `trnxProc`

`trnxProc` has no loop: its termination VC (`TermVC`, no cut point) is its symbolic run with the postcondition
`True`, the calls of `status2` and `fit` answered by their contracts with fresh results (`seqCalleesF`), which
hold (`status2F_vc`, `fitF_vc`) and terminate (`Term.Helpers`). The run is split as `trnx_entry`'s (the
operation, the file's flags, the OPEN outcome, the position).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-! ## The callee contracts -/

theorem status2F_satT : Sat Gen.prog status2Ref status2SpecF := status2F_vc.sat
theorem fitF_satT : Sat Gen.prog fitRef fitSpecF := fitF_vc.sat

set_option maxHeartbeats 4000000 in
theorem status2F_okT : ContractOK Gen.prog status2Sig status2SpecF := by jcontract_ok [status2F_satT]
set_option maxHeartbeats 4000000 in
theorem fitF_okT : ContractOK Gen.prog fitSig fitSpecF := by jcontract_ok [fitF_satT]

theorem seqCalleesF_validT : Valid Gen.prog seqCalleesF.env := by
  apply Contracts.valid_of_ok
  simp only [seqCalleesF, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨status2F_okT, fitF_okT⟩

theorem seqCalleesF_term :
    ∀ sig S, (seqCalleesF.env.below (fun _ => 0) 1) sig = some S → ContractTerm Gen.prog sig S :=
  Contracts.term_of_ok (by
    simp only [seqCalleesF, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨status2F_cterm, fitF_cterm⟩) _ _

/-! ## The paths -/

/-- The termination paths of `trnxProc` from statement `pc`. -/
@[irreducible] def trnxTWP (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPT Gen.prog seqCalleesF.env 1)
    Gen.Cbstm03b.«trnxProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»
    [] (fun _ => True) 200 pc fr σ

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem trnx_tentry (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddTrnx oe st q opv oeM s a).pre args σ0) :
    trnxTWP 0 (Frame.init true args) σ0 := by
  obtain ⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩ := hpre
  obtain ⟨fs, hst, ⟨⟨x1, g1, m1⟩, -, -⟩, -, -, -⟩ := stateAtM_iff.1 hS
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
  have hxl : xs.length = s.trnx.recs.length := Forall2.length_eq hrecsF
  clear hS hA hsep hK
  by_cases hbO : b = opOpen
  · subst hbO
    rw [op_texts.1] at hxop
    cases hb : s.trnx.isOpen
    · rw [hb] at hopen
      obtain ⟨eta, ys, hoe, hys, hysv⟩ := hE
      obtain ⟨e0, e1, e2, e3, rfl⟩ : ∃ e0 e1 e2 e3, ys = [e0, e1, e2, e3] := by
        match ys, hys with
        | [e0, e1, e2, e3], _ => exact ⟨e0, e1, e2, e3, rfl⟩
      rcases hysv 0 (by decide) with ⟨he0, hoe0⟩ | ⟨ob, c, he0, hob, hc, hoe0⟩
      · simp only [List.getD_cons_zero] at he0
        subst he0
        simp only [trnxTWP]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      · simp only [List.getD_cons_zero] at he0
        subst he0
        simp only [trnxTWP]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
    · rw [hb] at hopen
      simp only [trnxTWP]
      jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
  · by_cases hbR : b = opRead
    · subst hbR
      rw [op_texts.2.1] at hxop
      cases hb : s.trnx.isOpen
      · rw [hb] at hopen
        simp only [trnxTWP]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      · rw [hb] at hopen
        cases he : s.trnx.eof
        · rw [he] at heof
          rcases Nat.lt_or_ge s.trnx.pos s.trnx.recs.length with hp | hp
          · have hvr : Model.FdTrnxfileRec.Valid (s.trnx.recs[s.trnx.pos]'hp) := hV.1 _ (List.getElem_mem hp)
            have hxp : s.trnx.pos < xs.length := by rw [hxl]; exact hp
            have hjr := (Glue.forall2_iff.1 hrecsF).2 s.trnx.pos hxp
            rw [List.getD_eq_getElem _ _ hxp, List.getD_eq_getElem _ _ hp] at hjr
            obtain ⟨xr, fsr, c, i, d, sc, si, sd, hxv, hxr, hr2, hc, hi, hd, gc, jc, gi, ji, gd, jd⟩ :=
              trnxRecAt_of hjr hvr
            obtain ⟨xsc, rfl, hxsc⟩ := jc
            obtain ⟨xsi, rfl, hxsi⟩ := ji
            obtain ⟨xsd, rfl, hxsd⟩ := jd
            have hxe : xs[s.trnx.pos]? = some (.ref xr) := by rw [List.getElem?_eq_getElem hxp, hxv]
            clear hjr hvr hr2 hrecsF hV
            simp only [trnxTWP]
            set_option jimple.modelContracts true in
              jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split, StrOk, cp037Str_length, argText]
          · simp only [trnxTWP]
            jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
        · rw [he] at heof
          simp only [trnxTWP]
          jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
    · by_cases hbC : b = opClose
      · subst hbC
        rw [op_texts.2.2.2] at hxop
        cases hb : s.trnx.isOpen
        · rw [hb] at hopen
          simp only [trnxTWP]
          jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
        · rw [hb] at hopen
          simp only [trnxTWP]
          jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      · have hnO : ¬ (cp037Str [b] = JStr.ofString "O") := by rw [← op_texts.1]; exact op_ne_text hbO
        have hnR : ¬ (cp037Str [b] = JStr.ofString "R") := by rw [← op_texts.2.1]; exact op_ne_text hbR
        have hnC : ¬ (cp037Str [b] = JStr.ofString "C") := by rw [← op_texts.2.2.2]; exact op_ne_text hbC
        simp only [trnxTWP]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]

/-! ## Termination -/

theorem trnx_tvc (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) :
    TermVC Gen.prog seqCalleesF.env (fun _ => 0) 1 1 trnxProcRef (procSpecG ddTrnx oe st q opv oeM s a) [] 200 := by
  refine ⟨Gen.Cbstm03b.«trnxProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)», rfl,
    fun args σ0 hpre => ⟨?_, fun p hp => nomatch hp⟩⟩
  rw [SpecEnv.below_const _ _ (by decide)]
  have h := trnx_tentry oe st q opv oeM s a args σ0 hpre
  unfold trnxTWP at h
  exact h

/-- `trnxProc` terminates, for the contract with fixed ghost values. -/
theorem trnxG_term (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) :
    ∀ args σ, (procSpecG ddTrnx oe st q opv oeM s a).pre args σ → MTerm Gen.prog trnxProcRef args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) seqCalleesF_validT seqCalleesF_term (trnx_tvc oe st q opv oeM s a)

/-- **`trnxProc` terminates** on every input of `procSpec ddTrnx`. -/
theorem trnx_term : ∀ args σ, (procSpec ddTrnx).pre args σ → MTerm Gen.prog trnxProcRef args σ := by
  intro args σ hpre
  obtain ⟨oe, st, q, opv, oeM, s, a, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hpre
  exact trnxG_term oe st q opv oeM s a args σ ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

set_option maxHeartbeats 4000000 in
theorem trnx_cterm : ContractTerm Gen.prog trnxProcSig (procSpec ddTrnx) := by jcontract_term [trnx_term]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.trnx_tentry
#print axioms EquivLean.Modernize.Cbstm03b.Java.trnx_cterm

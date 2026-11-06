import EquivLean.Modernize.Cbstm03b.Java.TrnxFin
import EquivLean.Modernize.Cbstm03b.Java.TrnxModel
import EquivLean.Modernize.Cbstm03b.Java.HFresh

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

@[irreducible] def trnxWP (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog seqCalleesF.env 1)
    Gen.Cbstm03b.«trnxProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»
    (Invariants.inst [] args σ0) ((procSpecG ddTrnx oe st q opv oeM s a).post args σ0) 200 pc fr σ

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 → l1.length = l2.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [forall2_length h]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem trnx_entry (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddTrnx oe st q opv oeM s a).pre args σ0) :
    trnxWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  obtain ⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩ := hpre
  have hS' := hS
  have hA' := hA
  obtain ⟨fs, hst, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, ⟨z1, n1, t1⟩⟩, pX, pC, pA⟩ := stateAtM_iff.1 hS
  have m1' := m1
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
  obtain ⟨zs, rfl, hzs⟩ := t1
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
  have hxl : xs.length = s.trnx.recs.length := forall2_length hrecsF
  have hkept : Kept (StateAtM σ0 st s ∧ SepM σ0 st ∧
      JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a ∧ Model.LkM03bArea.Valid a ∧
      σ0.heap st = some (.plain "Cbstm03b$State" fs) ∧ σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) ∧
      FileAtM "Cbstm03b$TrnxFile" "Cbstm03b$FdTrnxfileRec" FdTrnxfileRec σ0 (.ref o1) s.trnx ∧
      σ0.heap o1 = some (.plain "Cbstm03b$TrnxFile" fs1) ∧
      Fields.get fs ("Cbstm03b$State", "trnxFile") = some (.ref o1) ∧
      Fields.get fs ("Cbstm03b$State", "fdTrnxfileRec") = some y1 ∧
      JRecAt FdTrnxfileRec "Cbstm03b$FdTrnxfileRec" σ0 y1 s.trnxRec) :=
    Kept.intro ⟨hS', hsep, hA', hVa, hst, hq, m1', ho1, g1, k1, j1⟩
  clear hS' hA' m1' hS hA
  have hop : Model.aOp a = b := by rw [ha]; rfl
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
        simp only [trnxWP, procSpecG, Spec.of, callT_open00 hdd hop hb hoe0]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
        all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
        · closeT_state
        · closeT_sep
        · closeT_area
      · simp only [List.getD_cons_zero] at he0
        subst he0
        simp only [trnxWP, procSpecG, Spec.of, callT_openErr hdd hop hb hoe0]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
        all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
        · closeS_state
        · closeS_sep
        · closeS_area
    · rw [hb] at hopen
      simp only [trnxWP, procSpecG, Spec.of, callT_open41 hdd hop hb]
      jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
      · closeS_state
      · closeS_sep
      · closeS_area
  · by_cases hbR : b = opRead
    · subst hbR
      rw [op_texts.2.1] at hxop
      cases hb : s.trnx.isOpen
      · rw [hb] at hopen
        simp only [trnxWP, procSpecG, Spec.of, callT_read47 hdd hop hb]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
        all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
        · closeS_state
        · closeS_sep
        · closeS_area
      · rw [hb] at hopen
        cases he : s.trnx.eof
        · rw [he] at heof
          rcases Nat.lt_or_ge s.trnx.pos s.trnx.recs.length with hp | hp
          · have hr : s.trnx.recs[s.trnx.pos]? = some (s.trnx.recs[s.trnx.pos]'hp) := List.getElem?_eq_getElem hp
            have hvr : Model.FdTrnxfileRec.Valid (s.trnx.recs[s.trnx.pos]'hp) := hV.1 _ (List.getElem_mem hp)
            have hxp : s.trnx.pos < xs.length := by rw [hxl]; exact hp
            have hjr := (Glue.forall2_iff.1 hrecsF).2 s.trnx.pos hxp
            rw [List.getD_eq_getElem _ _ hxp, List.getD_eq_getElem _ _ hp] at hjr
            obtain ⟨xr, fsr, c, i, d, sc, si, sd, hxv, hxr, hr2, hc, hi, hd, gc, jc, gi, ji, gd, jd⟩ :=
              trnxRecAt_of hjr hvr
            obtain ⟨xsc, rfl, hxsc⟩ := jc
            obtain ⟨xsi, rfl, hxsi⟩ := ji
            obtain ⟨xsd, rfl, hxsd⟩ := jd
            have hxe : xs[s.trnx.pos]? = some (.ref xr) := by rw [List.getElem?_eq_getElem hxp, hxv]
            simp only [trnxWP, procSpecG, Spec.of, callT_read00 hdd hop hb he hr]
            set_option jimple.modelContracts true in jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split, StrOk, cp037Str_length, argText]
            all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
            · refine (finT_ex hS hsep hst (by keepsT_tac) ?_).1
              refine ⟨_, by hsimpK; try rfl, fun k h1 h2 => by simp only [Fields.get_set, if_neg h1, if_neg h2],
                ⟨_, by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; exact g1,
                  fileAtM_upd' m1 ho1 (by keepsT_tac) ((away_chgT _).mono (by decide)) (by hsimpK; try rfl) (by fields_close)
                    (by fields_close) (by fields_close) (by omega) (by fields_close)⟩,
                ⟨_, by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl,
                  trnxRecAt_mk (by hsimpK; try rfl) (by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl)
                    (jstrAt_keeps (by keepsT_tac) (away_chgT _) ⟨xsc, rfl, hxsc⟩)
                    (by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl)
                    (jstrAt_keeps (by keepsT_tac) (away_chgT _) ⟨xsi, rfl, hxsi⟩)
                    (by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl)
                    (jstrAt_keeps (by keepsT_tac) (away_chgT _) ⟨xsd, rfl, hxsd⟩)⟩,
                ⟨_, by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl, _, rfl, ?_⟩⟩
              rw [status_text, ← st_lits.1]
              hsimpK
            · exact finT_sep hS hsep hst (by keepsT_tac) ((away_chgT _).mono (by decide)) (by hsimpK; try rfl)
                (fun k h1 h2 => by simp only [Fields.get_set, if_neg h1, if_neg h2])
            · refine area_rc_fldt hA hVa hq (by keepsT_tac) (away_chgT _) (by hsimpK; try rfl)
                (fun k h1 h2 => by simp only [Fields.get_set, if_neg h1, if_neg h2]) (by simp; try rfl) ⟨_, rfl, ?_⟩
                (by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl) ⟨_, rfl, ?_⟩
              · rw [stBytes_text, ← st_lits.1]
                hsimpK
              · rw [← trnx_fldt hc hi hd]
                hsimpK
                assumption
          · simp only [trnxWP, procSpecG, Spec.of, callT_read10 hdd hop hb he hp]
            jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
            all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
            · closeT_state
            · closeT_sep
            · closeT_area
        · rw [he] at heof
          simp only [trnxWP, procSpecG, Spec.of, callT_read46 hdd hop hb he]
          jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
          all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
          · closeS_state
          · closeS_sep
          · closeS_area
    · by_cases hbC : b = opClose
      · subst hbC
        rw [op_texts.2.2.2] at hxop
        cases hb : s.trnx.isOpen
        · rw [hb] at hopen
          simp only [trnxWP, procSpecG, Spec.of, callT_close42 hdd hop hb]
          jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
          all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
          · closeS_state
          · closeS_sep
          · closeS_area
        · rw [hb] at hopen
          simp only [trnxWP, procSpecG, Spec.of, callT_close00 hdd hop hb]
          jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
          all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
          · closeT_state
          · closeT_sep
          · closeT_area
      · have hnO : ¬ (cp037Str [b] = JStr.ofString "O") := by rw [← op_texts.1]; exact op_ne_text hbO
        have hnR : ¬ (cp037Str [b] = JStr.ofString "R") := by rw [← op_texts.2.1]; exact op_ne_text hbR
        have hnC : ¬ (cp037Str [b] = JStr.ofString "C") := by rw [← op_texts.2.2.2]; exact op_ne_text hbC
        have hcall := callT_other (oeM := oeM) (s := s) hdd (by rw [hop]; exact hbO) (by rw [hop]; exact hbR)
          (by rw [hop]; exact hbC)
        simp only [trnxWP, procSpecG, Spec.of, hcall]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
        all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
        · exact stateAtM_keepS hS (by keepsS_tac) (by hsimp)
        · exact sepM_keepS hS hsep (by keepsS_tac) (by hsimp)
        · exact area_rc hA hVa hq (by keepsS_tac) (away_chgS _) (by hsimp; try rfl) (fun k h => get_set_other h)
            get_set_same (jstrAt_keeps (by keepsS_tac) (away_chgS _) ⟨zs, rfl, hzs⟩)

end EquivLean.Modernize.Cbstm03b.Java

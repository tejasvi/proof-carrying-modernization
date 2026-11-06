import EquivLean.Modernize.Cbstm03b.Java.XrefWP

/-!
# CBSTM03B → Java: `xrefProc`

`xref_vc`: for every choice of ghost values, `xrefProc`'s verification conditions against `procSpecG ddXref`
(`procSpec ddXref` of `Iface.lean` with its ghost values fixed), no invariants, fuel 200, callees answered by
`seqCalleesF` (`status2` and `fit` with fresh results; depth 1: `FdXreffileRec.<init>` inlined). `xref_sat`:
`procSpec ddXref` from it (`procSpec_of_ghost`). The paths, as for `trnxProc`: `OPEN` (`xref_open`), a `READ` other
than a record read (`xref_read_rest`), `CLOSE` and another operation (`xref_cother`), the record read
(`xref_read00`); the model's call on each path is `XrefModel.lean`'s, the end of each path `XrefFin.lean`'s.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- The `OPEN` paths. -/
theorem xref_open (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddXref oe st q opv oeM s a).pre args σ0) (hO : Model.aOp a = opOpen) :
    xrefWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  obtain ⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩ := hpre
  have hS' := hS
  have hA' := hA
  obtain ⟨fs, hst, pT, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, ⟨z1, n1, t1⟩⟩, pC, pA⟩ := stateAtM_iff.1 hS
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
  have hxl : xs.length = s.xref.recs.length := forall2_lengthX hrecsF
  have hkept : Kept (StateAtM σ0 st s ∧ SepM σ0 st ∧
      JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a ∧ Model.LkM03bArea.Valid a ∧
      σ0.heap st = some (.plain "Cbstm03b$State" fs) ∧ σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) ∧
      FileAtM "Cbstm03b$XrefFile" "Cbstm03b$FdXreffileRec" FdXreffileRec σ0 (.ref o1) s.xref ∧
      σ0.heap o1 = some (.plain "Cbstm03b$XrefFile" fs1) ∧
      Fields.get fs ("Cbstm03b$State", "xrefFile") = some (.ref o1) ∧
      Fields.get fs ("Cbstm03b$State", "fdXreffileRec") = some y1 ∧
      JRecAt FdXreffileRec "Cbstm03b$FdXreffileRec" σ0 y1 s.xrefRec) :=
    Kept.intro ⟨hS', hsep, hA', hVa, hst, hq, m1', ho1, g1, k1, j1⟩
  clear hS' hA' m1' hS hA
  have hop : Model.aOp a = b := by rw [ha]; rfl
  have hbO : b = opOpen := hop.symm.trans hO
  clear hO
  subst hbO
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
      simp only [xrefWP, procSpecG, Spec.of, callX_open00 hdd hop hb hoe1]
      jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
      · closeX_state
      · closeX_sep
      · closeX_area
    · simp only [List.getD_cons_succ, List.getD_cons_zero] at he1
      subst he1
      simp only [xrefWP, procSpecG, Spec.of, callX_openErr hdd hop hb hoe1]
      jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
      · closeXS_state
      · closeXS_sep
      · closeS_area
  · rw [hb] at hopen
    simp only [xrefWP, procSpecG, Spec.of, callX_open41 hdd hop hb]
    jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
    all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
    · closeXS_state
    · closeXS_sep
    · closeS_area

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- The `READ` paths other than a record read. -/
theorem xref_read_rest (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddXref oe st q opv oeM s a).pre args σ0) (hR : Model.aOp a = opRead)
    (hnot : ¬ (s.xref.isOpen = true ∧ s.xref.eof = false ∧ s.xref.pos < s.xref.recs.length)) :
    xrefWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  obtain ⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩ := hpre
  have hS' := hS
  have hA' := hA
  obtain ⟨fs, hst, pT, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, ⟨z1, n1, t1⟩⟩, pC, pA⟩ := stateAtM_iff.1 hS
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
  have hxl : xs.length = s.xref.recs.length := forall2_lengthX hrecsF
  have hkept : Kept (StateAtM σ0 st s ∧ SepM σ0 st ∧
      JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a ∧ Model.LkM03bArea.Valid a ∧
      σ0.heap st = some (.plain "Cbstm03b$State" fs) ∧ σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) ∧
      FileAtM "Cbstm03b$XrefFile" "Cbstm03b$FdXreffileRec" FdXreffileRec σ0 (.ref o1) s.xref ∧
      σ0.heap o1 = some (.plain "Cbstm03b$XrefFile" fs1) ∧
      Fields.get fs ("Cbstm03b$State", "xrefFile") = some (.ref o1) ∧
      Fields.get fs ("Cbstm03b$State", "fdXreffileRec") = some y1 ∧
      JRecAt FdXreffileRec "Cbstm03b$FdXreffileRec" σ0 y1 s.xrefRec) :=
    Kept.intro ⟨hS', hsep, hA', hVa, hst, hq, m1', ho1, g1, k1, j1⟩
  clear hS' hA' m1' hS hA
  have hop : Model.aOp a = b := by rw [ha]; rfl
  have hbR : b = opRead := hop.symm.trans hR
  clear hR
  subst hbR
  rw [op_texts.2.1] at hxop
  cases hb : s.xref.isOpen
  · rw [hb] at hopen
    clear hnot
    simp only [xrefWP, procSpecG, Spec.of, callX_read47 hdd hop hb]
    jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
    all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
    · closeXS_state
    · closeXS_sep
    · closeS_area
  · rw [hb] at hopen
    cases he : s.xref.eof
    · rw [he] at heof
      rcases Nat.lt_or_ge s.xref.pos s.xref.recs.length with hp | hp
      · exact absurd ⟨hb, he, hp⟩ hnot
      · clear hnot
        simp only [xrefWP, procSpecG, Spec.of, callX_read10 hdd hop hb he hp]
        jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
        all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
        · closeX_state
        · closeX_sep
        · closeX_area
    · rw [he] at heof
      clear hnot
      simp only [xrefWP, procSpecG, Spec.of, callX_read46 hdd hop hb he]
      jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
      · closeXS_state
      · closeXS_sep
      · closeS_area

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- The `CLOSE` paths and another operation. -/
theorem xref_cother (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddXref oe st q opv oeM s a).pre args σ0) (hO : Model.aOp a ≠ opOpen)
    (hR : Model.aOp a ≠ opRead) :
    xrefWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  obtain ⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩ := hpre
  have hS' := hS
  have hA' := hA
  obtain ⟨fs, hst, pT, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, ⟨z1, n1, t1⟩⟩, pC, pA⟩ := stateAtM_iff.1 hS
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
  have hxl : xs.length = s.xref.recs.length := forall2_lengthX hrecsF
  have hkept : Kept (StateAtM σ0 st s ∧ SepM σ0 st ∧
      JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a ∧ Model.LkM03bArea.Valid a ∧
      σ0.heap st = some (.plain "Cbstm03b$State" fs) ∧ σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) ∧
      FileAtM "Cbstm03b$XrefFile" "Cbstm03b$FdXreffileRec" FdXreffileRec σ0 (.ref o1) s.xref ∧
      σ0.heap o1 = some (.plain "Cbstm03b$XrefFile" fs1) ∧
      Fields.get fs ("Cbstm03b$State", "xrefFile") = some (.ref o1) ∧
      Fields.get fs ("Cbstm03b$State", "fdXreffileRec") = some y1 ∧
      JRecAt FdXreffileRec "Cbstm03b$FdXreffileRec" σ0 y1 s.xrefRec) :=
    Kept.intro ⟨hS', hsep, hA', hVa, hst, hq, m1', ho1, g1, k1, j1⟩
  clear hS' hA' m1' hS hA
  have hop : Model.aOp a = b := by rw [ha]; rfl
  have hbO : ¬ b = opOpen := fun h => hO (hop.trans h)
  have hbR : ¬ b = opRead := fun h => hR (hop.trans h)
  clear hO hR
  by_cases hbC : b = opClose
  · subst hbC
    rw [op_texts.2.2.2] at hxop
    cases hb : s.xref.isOpen
    · rw [hb] at hopen
      simp only [xrefWP, procSpecG, Spec.of, callX_close42 hdd hop hb]
      jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
      · closeXS_state
      · closeXS_sep
      · closeS_area
    · rw [hb] at hopen
      simp only [xrefWP, procSpecG, Spec.of, callX_close00 hdd hop hb]
      jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
      all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
      · closeX_state
      · closeX_sep
      · closeX_area
  · have hnO : ¬ (cp037Str [b] = JStr.ofString "O") := by rw [← op_texts.1]; exact op_ne_text hbO
    have hnR : ¬ (cp037Str [b] = JStr.ofString "R") := by rw [← op_texts.2.1]; exact op_ne_text hbR
    have hnC : ¬ (cp037Str [b] = JStr.ofString "C") := by rw [← op_texts.2.2.2]; exact op_ne_text hbC
    have hcall := callX_other (oeM := oeM) (s := s) hdd (by rw [hop]; exact hbO) (by rw [hop]; exact hbR)
      (by rw [hop]; exact hbC)
    simp only [xrefWP, procSpecG, Spec.of, hcall]
    jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split]
    all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
    · exact stateAtM_keepS hS (by keepsS_tac) (by hsimp)
    · exact sepM_keepS hS hsep (by keepsS_tac) (by hsimp)
    · exact area_rc hA hVa hq (by keepsS_tac) (away_chgS _) (by hsimp; try rfl) (fun k h => get_set_other h)
        get_set_same (jstrAt_keeps (by keepsS_tac) (away_chgS _) ⟨zs, rfl, hzs⟩)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- The record read (`READ` of an open file before its end, at a record). -/
theorem xref_read00 (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddXref oe st q opv oeM s a).pre args σ0) (hR : Model.aOp a = opRead)
    (hb : s.xref.isOpen = true) (he : s.xref.eof = false) (hp : s.xref.pos < s.xref.recs.length) :
    xrefWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  obtain ⟨rfl, hE, hS, hsep, hA, hV, hVa, hK, hdd, hopA, hI⟩ := hpre
  have hS' := hS
  have hA' := hA
  obtain ⟨fs, hst, pT, ⟨⟨x1, g1, m1⟩, ⟨y1, k1, j1⟩, ⟨z1, n1, t1⟩⟩, pC, pA⟩ := stateAtM_iff.1 hS
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
  have hxl : xs.length = s.xref.recs.length := forall2_lengthX hrecsF
  have hkept : Kept (StateAtM σ0 st s ∧ SepM σ0 st ∧
      JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ0 (.ref q) a ∧ Model.LkM03bArea.Valid a ∧
      σ0.heap st = some (.plain "Cbstm03b$State" fs) ∧ σ0.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) ∧
      FileAtM "Cbstm03b$XrefFile" "Cbstm03b$FdXreffileRec" FdXreffileRec σ0 (.ref o1) s.xref ∧
      σ0.heap o1 = some (.plain "Cbstm03b$XrefFile" fs1) ∧
      Fields.get fs ("Cbstm03b$State", "xrefFile") = some (.ref o1) ∧
      Fields.get fs ("Cbstm03b$State", "fdXreffileRec") = some y1 ∧
      JRecAt FdXreffileRec "Cbstm03b$FdXreffileRec" σ0 y1 s.xrefRec) :=
    Kept.intro ⟨hS', hsep, hA', hVa, hst, hq, m1', ho1, g1, k1, j1⟩
  clear hS' hA' m1' hS hA
  have hop : Model.aOp a = b := by rw [ha]; rfl
  have hbR : b = opRead := hop.symm.trans hR
  clear hR
  subst hbR
  rw [op_texts.2.1] at hxop
  rw [hb] at hopen
  rw [he] at heof
  have hr : s.xref.recs[s.xref.pos]? = some (s.xref.recs[s.xref.pos]'hp) := List.getElem?_eq_getElem hp
  have hvr : Model.FdXreffileRec.Valid (s.xref.recs[s.xref.pos]'hp) := hV.2.1 _ (List.getElem_mem hp)
  have hxp : s.xref.pos < xs.length := by rw [hxl]; exact hp
  have hjr := (Glue.forall2_iff.1 hrecsF).2 s.xref.pos hxp
  rw [List.getD_eq_getElem _ _ hxp, List.getD_eq_getElem _ _ hp] at hjr
  obtain ⟨xr, fsr, c, d, sc, sd, hxv, hxr, hr2, hc, hd, gc, jc, gd, jd⟩ := xrefRecAt_of hjr hvr
  obtain ⟨xsc, rfl, hxsc⟩ := jc
  obtain ⟨xsd, rfl, hxsd⟩ := jd
  have hxe : xs[s.xref.pos]? = some (.ref xr) := by rw [List.getElem?_eq_getElem hxp, hxv]
  simp only [xrefWP, procSpecG, Spec.of, callX_read00 hdd hop hb he hr]
  set_option jimple.modelContracts true in jvc [ite_nat_ne, seqCalleesF, status2Sig, fitSig, grows_split, StrOk, cp037Str_length, argText]
  all_goals obtain ⟨hS, hsep, hA, hVa, hst, hq, m1, ho1, g1, k1, j1⟩ := Kept.elim ‹Kept _›
  · refine (finX_ex hS hsep hst (by keepsX_tac) ?_).1
    refine ⟨_, by hsimpK; try rfl, fun k h1 h2 => by simp only [Fields.get_set, if_neg h1, if_neg h2],
      ⟨_, by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; exact g1,
        fileAtM_upd' m1 ho1 (by keepsX_tac) ((away_chgX _).mono (by decide)) (by hsimpK; try rfl) (by fields_close)
          (by fields_close) (by fields_close) (by omega) (by fields_close)⟩,
      ⟨_, by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl,
        xrefRecAt_mk (by hsimpK; try rfl) (by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl)
          (jstrAt_keeps (by keepsX_tac) (away_chgX _) ⟨xsc, rfl, hxsc⟩)
          (by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl)
          (jstrAt_keeps (by keepsX_tac) (away_chgX _) ⟨xsd, rfl, hxsd⟩)⟩,
      ⟨_, by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl, _, rfl, ?_⟩⟩
    rw [status_text, ← st_lits.1]
    hsimpK
  · exact finX_sep hS hsep hst (by keepsX_tac) ((away_chgX _).mono (by decide)) (by hsimpK; try rfl)
      (fun k h1 h2 => by simp only [Fields.get_set, if_neg h1, if_neg h2])
  · refine area_rc_fldt hA hVa hq (by keepsX_tac) (away_chgX _) (by hsimpK; try rfl)
      (fun k h1 h2 => by simp only [Fields.get_set, if_neg h1, if_neg h2]) (by simp; try rfl) ⟨_, rfl, ?_⟩
      (by simp (config := {decide := true}) only [Fields.get_set, ↓reduceIte]; try rfl) ⟨_, rfl, ?_⟩
    · rw [stBytes_text, ← st_lits.1]
      hsimpK
    · rw [← xref_fldt hc hd]
      hsimpK
      assumption

/-- The entry paths. -/
theorem xref_entry (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State)
    (hpre : (procSpecG ddXref oe st q opv oeM s a).pre args σ0) :
    xrefWP oe st q opv oeM s a args σ0 0 (Frame.init true args) σ0 := by
  by_cases hO : Model.aOp a = opOpen
  · exact xref_open oe st q opv oeM s a args σ0 hpre hO
  by_cases hR : Model.aOp a = opRead
  · by_cases h0 : s.xref.isOpen = true ∧ s.xref.eof = false ∧ s.xref.pos < s.xref.recs.length
    · exact xref_read00 oe st q opv oeM s a args σ0 hpre hR h0.1 h0.2.1 h0.2.2
    · exact xref_read_rest oe st q opv oeM s a args σ0 hpre hR h0
  · exact xref_cother oe st q opv oeM s a args σ0 hpre hO hR

/-- **`xrefProc`'s verification conditions**, for every choice of ghost values. -/
theorem xref_vc (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) :
    MethodVC Gen.prog seqCalleesF.env 1 xrefProcRef (procSpecG ddXref oe st q opv oeM s a) [] 200 := by
  refine ⟨Gen.Cbstm03b.«xrefProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»,
    rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · have h := xref_entry oe st q opv oeM s a args σ0 hpre
    unfold xrefWP at h
    have hs : xrefProcRef.decl.mods.isStatic = true := rfl
    simp only [hs, Invariants.inst, List.map_nil, List.lookup_nil] at h ⊢
    -- `exact h` would compare the two (equal) terms by unfolding the method's statements
    exact (by assumption)
  · intro p hp
    simp only [Invariants.inst, List.map_nil] at hp
    cases hp

/-- `procSpec ddXref` (`Iface.lean`) for `xrefProc`, given its callees' contracts. -/
theorem xref_sat (hV : Valid Gen.prog seqCalleesF.env) : Sat Gen.prog xrefProcRef (procSpec ddXref) :=
  procSpec_of_ghost fun oe st q opv oeM s a => MethodVC.sat_of_valid hV (xref_vc oe st q opv oeM s a)

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.xref_vc
#print axioms EquivLean.Modernize.Cbstm03b.Java.xref_sat

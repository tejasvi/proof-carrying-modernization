import EquivLean.Modernize.Cbstm03b.Java.AcctPre

/-!
# CBSTM03B → Java, `acctProc`: `CLOSE` (operation `"C"`)

An open file is closed (status `00`); a closed one is left as it is (status `42`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem acct_close_open {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0)
    (hop : Model.aOp a = opClose) (hopen : s.acct.isOpen = true) :
    acctWP oe st q opv oeM s a σ0 0 (Frame.init true [.ref oe, .ref st, .ref q, opv]) σ0 := by
  obtain ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, hop4, hrec4, hl, hlen, hrs, hp, hpos, heof, gr, hr, gs, hq, hxop, hopv, hb, g2, g3, g4', g5, g6,
    n1, n2, n3, hI0, hF⟩ := pre_fin hpre
  subst hopv
  rw [hop] at hb
  subst hb
  rw [op_texts.2.2.2] at hxop
  rw [hopen] at hop4
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  clear hpre hrec4 hl hlen hrs g4' g5
  simp only [acctWP, procSpecG, Spec.of]
  jvc [acctInv, acctCallees, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, Grows, n1, n2, n3, n1', n2',
    n3']
  all_goals unfold FinCtx at hF
  all_goals obtain ⟨hS, hSep, hE, hV, hK, hdd, hI, hA, hVa, m4, hr', mr, hnr, gr', js, ha, ldd, lrc, lkey, hkl1,
    hkl2, lfl, g1, j1, g2', j2, j3, g4', j4, g5, g6', j6, n4, n5, n6, lst, lo4, lq, lfdr, haw0, hawr⟩ := hF
  · rw [call_close_open hdd hop hopen]
    refine state_fin (fs' := Fields.set fs ("Cbstm03b$State", "acctfileStatus") (.ref (σ0.next + 1 + 1 + 1)))
      hS hst ho4 hq hr ?hk ?hst ?hrest ⟨⟨.ref o4, ?g4, ?m4⟩, ⟨.ref fdr, ?gr, ?mr⟩,
        ⟨.ref (σ0.next + 1 + 1 + 1), ?gs, ?js⟩⟩
    case hk => keeps_tac
    case hst => hsimp [n2]
    case hrest => exact fun k _ _ h3 => get_set_ne _ (fun e => h3 (Prod.mk.inj e).2)
    case g4 => rw [get_set_ne _ (by decide +kernel)]; exact g4
    case gr => rw [get_set_ne _ (by decide +kernel)]; exact gr
    case mr => exact jRecAt_same (by keeps_tac) haw0 (by hsimp [n4, n5, n6]) mr
    case gs => exact get_set_eq _ _ _
    case js => rw [status_text, ← lit_texts.1]; exact ⟨_, rfl, by hsimp⟩
    case m4 =>
      refine acctFile_fin (fs4' := Fields.set fs4 ("Cbstm03b$AcctFile", "open") (Value.int 0#32)) m4 hnr hst ho4
        hq hr ?_ ?_ (get_set_ne _ (by decide +kernel)) (by rw [get_set_eq]; rfl)
        (by rw [get_set_ne _ (by decide +kernel)]; exact hpos) (by rw [get_set_ne _ (by decide +kernel)]; exact heof)
        rfl hp
      · keeps_tac
      · hsimp [n1', n3]
  · refine sepM_fin (fs' := Fields.set fs ("Cbstm03b$State", "acctfileStatus") (.ref (σ0.next + 1 + 1 + 1)))
      (fs4' := Fields.set fs4 ("Cbstm03b$AcctFile", "open") (Value.int 0#32)) (fdr' := fdr)
      hS hSep hst ho4 hq hr g4 gr ?hk ?hst (fun k _ _ h3 => get_set_ne _ (fun e => h3 (Prod.mk.inj e).2))
      (by rw [get_set_ne _ (by decide +kernel)]; exact g4) (by rw [get_set_ne _ (by decide +kernel)]; exact gr)
      (Or.inl rfl) ?h4 (get_set_ne _ (by decide +kernel))
    case hk => keeps_tac
    case hst => hsimp [n2]
    case h4 => hsimp [n1', n3]
  · rw [call_close_open hdd hop hopen, ha]
    refine area_fin (rc' := stBytes 0) (fldt' := fldt) (src' := .ref (σ0.next + 1 + 1 + 1)) (sfl' := sfl)
      (fsq' := Fields.set fsq ("Cbstm03b$LkM03bArea", "lkM03bRc") (.ref (σ0.next + 1 + 1 + 1)))
      ?hk haw0 ?hq g1 j1 g2' j2 g4' j4 g5
      (get_set_ne _ (by decide +kernel)) (get_set_ne _ (by decide +kernel)) (get_set_ne _ (by decide +kernel))
      (get_set_ne _ (by decide +kernel)) (get_set_eq _ _ _) ?j3
      (by rw [get_set_ne _ (by decide +kernel)]; exact g6) (jstrAt_keeps ?hk2 haw0 j6)
    case hk => keeps_tac
    case hq => hsimp
    case j3 => rw [stBytes_text, ← lit_texts.1]; exact ⟨_, rfl, by hsimp⟩
    case hk2 => keeps_tac

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem acct_close_shut {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0)
    (hop : Model.aOp a = opClose) (hshut : s.acct.isOpen = false) :
    acctWP oe st q opv oeM s a σ0 0 (Frame.init true [.ref oe, .ref st, .ref q, opv]) σ0 := by
  obtain ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, hop4, hrec4, hl, hlen, hrs, hp, hpos, heof, gr, hr, gs, hq, hxop, hopv, hb, g2, g3, g4', g5, g6,
    n1, n2, n3, hI0, hF⟩ := pre_fin hpre
  subst hopv
  rw [hop] at hb
  subst hb
  rw [op_texts.2.2.2] at hxop
  have hop4' := hop4
  rw [hshut] at hop4
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  clear hpre hrec4 hl hlen hrs g4' g5
  simp only [acctWP, procSpecG, Spec.of]
  jvc [acctInv, acctCallees, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, Grows, n1, n2, n3, n1', n2',
    n3']
  all_goals unfold FinCtx at hF
  all_goals obtain ⟨hS, hSep, hE, hV, hK, hdd, hI, hA, hVa, m4, hr', mr, hnr, gr', js, ha, ldd, lrc, lkey, hkl1,
    hkl2, lfl, g1, j1, g2', j2, j3, g4', j4, g5, g6', j6, n4, n5, n6, lst, lo4, lq, lfdr, haw0, hawr⟩ := hF
  · rw [call_close_shut hdd hop hshut]
    refine state_fin (fs' := Fields.set fs ("Cbstm03b$State", "acctfileStatus") (.ref (σ0.next + 1 + 1 + 1)))
      hS hst ho4 hq hr ?hk ?hst ?hrest ⟨⟨.ref o4, ?g4, ?m4⟩, ⟨.ref fdr, ?gr, ?mr⟩,
        ⟨.ref (σ0.next + 1 + 1 + 1), ?gs, ?js⟩⟩
    case hk => keeps_tac
    case hst => hsimp [n2]
    case hrest => exact fun k _ _ h3 => get_set_ne _ (fun e => h3 (Prod.mk.inj e).2)
    case g4 => rw [get_set_ne _ (by decide +kernel)]; exact g4
    case gr => rw [get_set_ne _ (by decide +kernel)]; exact gr
    case mr => exact jRecAt_same (by keeps_tac) haw0 (by hsimp [n4, n5, n6]) mr
    case gs => exact get_set_eq _ _ _
    case js => rw [status_text, ← lit_texts.2.2.1]; exact ⟨_, rfl, by hsimp⟩
    case m4 =>
      refine acctFile_fin (fs4' := fs4) m4 hnr hst ho4 hq hr ?_ ?_ rfl hop4' hpos heof rfl hp
      · keeps_tac
      · hsimp [n1', n3, ho4]
  · refine sepM_fin (fs' := Fields.set fs ("Cbstm03b$State", "acctfileStatus") (.ref (σ0.next + 1 + 1 + 1)))
      (fs4' := fs4) (fdr' := fdr)
      hS hSep hst ho4 hq hr g4 gr ?hk ?hst (fun k _ _ h3 => get_set_ne _ (fun e => h3 (Prod.mk.inj e).2))
      (by rw [get_set_ne _ (by decide +kernel)]; exact g4) (by rw [get_set_ne _ (by decide +kernel)]; exact gr)
      (Or.inl rfl) ?h4 rfl
    case hk => keeps_tac
    case hst => hsimp [n2]
    case h4 => hsimp [n1', n3, ho4]
  · rw [call_close_shut hdd hop hshut, ha]
    refine area_fin (rc' := stBytes 42) (fldt' := fldt) (src' := .ref (σ0.next + 1 + 1 + 1)) (sfl' := sfl)
      (fsq' := Fields.set fsq ("Cbstm03b$LkM03bArea", "lkM03bRc") (.ref (σ0.next + 1 + 1 + 1)))
      ?hk haw0 ?hq g1 j1 g2' j2 g4' j4 g5
      (get_set_ne _ (by decide +kernel)) (get_set_ne _ (by decide +kernel)) (get_set_ne _ (by decide +kernel))
      (get_set_ne _ (by decide +kernel)) (get_set_eq _ _ _) ?j3
      (by rw [get_set_ne _ (by decide +kernel)]; exact g6) (jstrAt_keeps ?hk2 haw0 j6)
    case hk => keeps_tac
    case hq => hsimp
    case j3 => rw [stBytes_text, ← lit_texts.2.2.1]; exact ⟨_, rfl, by hsimp⟩
    case hk2 => keeps_tac

end EquivLean.Modernize.Cbstm03b.Java.AcctP

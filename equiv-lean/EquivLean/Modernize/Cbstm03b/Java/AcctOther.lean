import EquivLean.Modernize.Cbstm03b.Java.AcctPre

/-!
# CBSTM03B → Java, `acctProc`: another operation

The return code is set from the file status; nothing else changes.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem acct_other {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0)
    (h1 : Model.aOp a ≠ opOpen) (h2 : Model.aOp a ≠ opReadK) (h3 : Model.aOp a ≠ opClose) :
    acctWP oe st q opv oeM s a σ0 0 (Frame.init true [.ref oe, .ref st, .ref q, opv]) σ0 := by
  obtain ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, hop4, hrec4, hl, hlen, hrs, hp, hpos, heof, gr, hr, gs, hq, hxop, hopv, hb, g2, g3, g4', g5, g6,
    n1, n2, n3, hI0, hF⟩ := pre_fin hpre
  subst hopv
  have h1' := h1
  have h2' := h2
  have h3' := h3
  obtain ⟨xsv, esv, hxsv⟩ := hF.js
  subst esv
  rw [hb] at h1 h2 h3
  have e1 : (JStr.ofString "O" = cp037Str [b]) = False :=
    eq_false (fun e => h1 (List.singleton_inj.1 (cp037Str_inj (e.symm.trans op_texts.1.symm))))
  have e2 : (JStr.ofString "K" = cp037Str [b]) = False :=
    eq_false (fun e => h2 (List.singleton_inj.1 (cp037Str_inj (e.symm.trans op_texts.2.2.1.symm))))
  have e3 : (JStr.ofString "C" = cp037Str [b]) = False :=
    eq_false (fun e => h3 (List.singleton_inj.1 (cp037Str_inj (e.symm.trans op_texts.2.2.2.symm))))
  have e1' : (cp037Str [b] = JStr.ofString "O") = False :=
    eq_false (fun e => h1 (List.singleton_inj.1 (cp037Str_inj (e.trans op_texts.1.symm))))
  have e2' : (cp037Str [b] = JStr.ofString "K") = False :=
    eq_false (fun e => h2 (List.singleton_inj.1 (cp037Str_inj (e.trans op_texts.2.2.1.symm))))
  have e3' : (cp037Str [b] = JStr.ofString "C") = False :=
    eq_false (fun e => h3 (List.singleton_inj.1 (cp037Str_inj (e.trans op_texts.2.2.2.symm))))
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  clear hpre hrec4 hl hlen hrs g4' g5 h1 h2 h3 hb
  simp only [acctWP, procSpecG, Spec.of]
  jvc [acctInv, acctCallees, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, Grows, n1, n2, n3, n1', n2',
    n3', e1, e2, e3, e1', e2', e3']
  all_goals unfold FinCtx at hF
  all_goals obtain ⟨hS, hSep, hE, hV, hK, hdd, hI, hA, hVa, m4, hr', mr, hnr, gr', js, ha, ldd, lrc, lkey, hkl1,
    hkl2, lfl, g1, j1, g2', j2, j3, g4', j4, g5, g6', j6, n4, n5, n6, lst, lo4, lq, lfdr, haw0, hawr⟩ := hF
  · rw [call_other hdd h1' h2' h3']
    refine state_fin (fs' := fs) hS hst ho4 hq hr ?hk ?hst (fun _ _ _ _ => rfl)
      ⟨⟨.ref o4, g4, ?m4⟩, ⟨.ref fdr, gr, ?mr⟩, ⟨.ref xsv, gs, ?js⟩⟩
    case hk => keeps_tac
    case hst => hsimp [n2, hst]
    case mr => exact jRecAt_same (by keeps_tac) haw0 (by hsimp [n6]) mr
    case js => exact jstrAt_keeps (by keeps_tac) haw0 js
    case m4 =>
      refine acctFile_fin (fs4' := fs4) m4 hnr hst ho4 hq hr ?_ ?_ rfl hop4 hpos heof rfl hp
      · keeps_tac
      · hsimp [n3, ho4]
  · refine sepM_fin (fs' := fs) (fs4' := fs4) (fdr' := fdr)
      hS hSep hst ho4 hq hr g4 gr ?hk ?hst (fun _ _ _ _ => rfl) g4 gr (Or.inl rfl) ?h4 rfl
    case hk => keeps_tac
    case hst => hsimp [n2, hst]
    case h4 => hsimp [n3, ho4]
  · rw [call_other hdd h1' h2' h3', ha]
    refine area_fin (rc' := s.acctSt.map ebcdicOfLatin1) (fldt' := fldt) (src' := .ref xsv) (sfl' := sfl)
      (fsq' := Fields.set fsq ("Cbstm03b$LkM03bArea", "lkM03bRc") (.ref xsv))
      ?hk haw0 ?hq g1 j1 g2' j2 g4' j4 g5
      (get_set_ne _ (by decide +kernel)) (get_set_ne _ (by decide +kernel)) (get_set_ne _ (by decide +kernel))
      (get_set_ne _ (by decide +kernel)) (get_set_eq _ _ _) (jstrAt_keeps ?hk3 haw0 js)
      (by rw [get_set_ne _ (by decide +kernel)]; exact g6) (jstrAt_keeps ?hk2 haw0 j6)
    case hk => keeps_tac
    case hq => hsimp
    case hk2 => keeps_tac
    case hk3 => keeps_tac

end EquivLean.Modernize.Cbstm03b.Java.AcctP

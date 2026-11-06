import EquivLean.Modernize.Cbstm03b.Java.AcctPre

/-!
# CBSTM03B → Java, `acctProc`: the key loop (statement 33)

A digit at a time (`jkey`); at the end the FD record object gets the key value in place; a closed file gives
status `47`, an open one starts the search (`J65`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

theorem keyText_length_le {a : List EquivLean.Cobol.Rec.FVal} {dd op rc key fldt : List UInt8} {kl : Int}
    (ha : a = [.str dd, .str op, .str rc, .str key, .num kl, .str fldt]) (lkey : key.length = 25) :
    (keyText a).length ≤ 25 := by
  subst ha
  simp only [keyText, cp037Str_length, List.length_take, Model.aKey, Model.strOf, List.getD_eq_getElem?_getD,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, lkey]
  exact Nat.min_le_right _ _

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem acct_loop {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0)
    (fr : Frame) (σ : State) (hJ : J33 oe st q a σ0 fr σ) :
    acctWP oe st q opv oeM s a σ0 33 fr σ := by
  obtain ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, hop4, hrec4, hl, hlen, hrs, hp, hpos, heof, gr, hr, gs, hq, hxop, hopv, hb, g2, g3, g4', g5, g6,
    n1, n2, n3, hI0, hF⟩ := pre_fin hpre
  obtain ⟨hopK, ⟨f18, f17, f0, f3⟩, kp, i, f11, hkp, f1, f8, hi, hg, hinit, hstat⟩ := hJ
  have hF' := hF
  unfold FinCtx at hF'
  obtain ⟨-, -, -, hV, -, -, -, -, -, -, -, mr, -, -, -, ha, -, -, lkey, -, -, -, -, -, -, -, -, -, -, -, -, -,
    n4, n5, n6, -, -, -, -, -, -⟩ := hF'
  obtain ⟨xr, fsr', n0, d0, sd0, exr, hxr, hrec0, hn0, hn1, hd0, gid, gdata, jdata⟩ :=
    acctRecAt_of mr hV.2.2.2.2.2.2.2.1
  cases exr
  rw [hr] at hxr
  cases hxr
  have hlenK := keyText_length_le ha lkey
  have hi25 : i ≤ 25 := Nat.le_trans hi hlenK
  have ht1 := toInt32_ofNat (n := (keyText a).length) (by omega)
  have ht2 := toInt32_ofNat (n := i) (by omega)
  have hmod : i % 4294967296 = i := Nat.mod_eq_of_lt (by omega)
  have f3' := f3 fs hst
  rw [g4] at f3'
  have hst1 : σ.heap st = some (.plain "Cbstm03b$State" fs) := by rw [hg.2 st (State.lt_next_of_heap hst), hst]
  have ho41 : σ.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4) := by
    rw [hg.2 o4 (State.lt_next_of_heap ho4), ho4]
  have hr1 : σ.heap fdr = some (.plain "Cbstm03b$FdAcctfileRec" fsr) := by
    rw [hg.2 fdr (State.lt_next_of_heap hr), hr]
  have hq1 : σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) := by rw [hg.2 q (State.lt_next_of_heap hq), hq]
  have hl1 : σ.heap l = some (.array et xs) := by rw [hg.2 l (State.lt_next_of_heap hl), hl]
  have hI1 : σ.initOf "Cbstm03b" = .done := by rw [State.initOf_eq_of_inits hinit]; exact hI0
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  have n4' := n4.symm
  have n5' := n5.symm
  have n6' := n6.symm
  have hH := hid_intro (And.intro hst <| And.intro ho4 <| And.intro hr <| And.intro hq <| And.intro hinit <|
    And.intro hstat <| And.intro hrec0 <| And.intro jdata <| And.intro f1 <| And.intro f8 <| And.intro hi <|
    And.intro f11 hkp)
  clear hpre hlen hrs f3 hst ho4 hr hq hl hI0 hxop hV mr hrec0 hn0 hn1 hd0 jdata ha lkey hopv hb hinit hstat
  simp only [acctWP, procSpecG, Spec.of]
  jvc [acctInv, acctCallees, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, Grows, n1, n2, n3, n1', n2',
    n3', n4, n5, n6, n4', n5', n6']
  all_goals obtain ⟨hst, ho4, hr, hq, hinit, hstat, hrec0, jdata, f1', f8', hi', f11', hkp'⟩ := hid_elim hH
  all_goals unfold FinCtx at hF
  all_goals obtain ⟨hS, hSep, hE, hV, hK, hdd, hI, hA, hVa, m4, hr', mr, hnr, gr', js, ha, ldd, lrc, lkey, hkl1,
    hkl2, lfl, g1, j1, g2', j2, j3, g4', j4, g5, g6', j6, n4, n5, n6, lst, lo4, lq, lfdr, haw0, hawr⟩ := hF
  all_goals have hk1 : Keeps (AccA st o4 q fdr) σ0 σ := keeps_of_grows ⟨left, right⟩
  all_goals have hval := acctVal_keyVal hK hopK hdd ha lkey
  -- status 47 (file closed): the post
  · rw [call_key_shut hdd hopK (by assumption)]
    refine state_fin (fs' := Fields.set fs ("Cbstm03b$State", "acctfileStatus") (.ref σ.next))
      hS hst ho4 hq hr ?hk ?hst ?hrest ⟨⟨.ref o4, ?g4, ?m4⟩, ⟨.ref fdr, ?gr, ?mr⟩, ⟨.ref σ.next, ?gs, ?js⟩⟩
    case hk => keeps_tac
    case hst => hsimp [n2, n4.symm, hst1]
    case hrest => exact fun k _ _ h3 => get_set_ne _ (fun e => h3 (Prod.mk.inj e).2)
    case g4 => rw [get_set_ne _ (by decide +kernel)]; exact g4
    case gr => rw [get_set_ne _ (by decide +kernel)]; exact gr
    case mr =>
      rw [hrec0]
      refine acctRecAt_mk (fs := Fields.set fsr ("Cbstm03b$FdAcctfileRec", "fdAcctId")
          (.long (BitVec.ofNat 64 (jkey (keyText a))))) ?_ ?_
        (by rw [get_set_ne _ (by decide +kernel)]; exact gdata) (jstrAt_keeps (by keeps_tac) haw0 jdata)
      · hsimp [n4, n6, n4.symm, n6.symm]
      · rw [get_set_eq, hval, BitVec.ofInt_natCast]; rfl
    case gs => exact get_set_eq _ _ _
    case js => rw [status_text, ← lit_texts.2.2.2.1]; exact ⟨_, rfl, by hsimp⟩
    case m4 =>
      refine acctFile_fin (fs4' := fs4) m4 hnr hst ho4 hq hr ?_ ?_ rfl hop4 hpos heof rfl hp
      · keeps_tac
      · hsimp [n1', n3, n5', ho41]
  · refine sepM_fin (fs' := Fields.set fs ("Cbstm03b$State", "acctfileStatus") (.ref σ.next))
      (fs4' := fs4) (fdr' := fdr)
      hS hSep hst ho4 hq hr g4 gr ?hk ?hst (fun k _ _ h3 => get_set_ne _ (fun e => h3 (Prod.mk.inj e).2))
      (by rw [get_set_ne _ (by decide +kernel)]; exact g4) (by rw [get_set_ne _ (by decide +kernel)]; exact gr)
      (Or.inl rfl) ?h4 rfl
    case hk => keeps_tac
    case hst => hsimp [n2, n4.symm, hst1]
    case h4 => hsimp [n1', n3, n5', ho41]
  · rw [call_key_shut hdd hopK (by assumption), ha]
    refine area_fin (rc' := stBytes 47) (fldt' := fldt) (src' := .ref σ.next) (sfl' := sfl)
      (fsq' := Fields.set fsq ("Cbstm03b$LkM03bArea", "lkM03bRc") (.ref σ.next))
      ?hk haw0 ?hq g1 j1 g2' j2 g4' j4 g5
      (get_set_ne _ (by decide +kernel)) (get_set_ne _ (by decide +kernel)) (get_set_ne _ (by decide +kernel))
      (get_set_ne _ (by decide +kernel)) (get_set_eq _ _ _) ?j3
      (by rw [get_set_ne _ (by decide +kernel)]; exact g6) (jstrAt_keeps ?hk2 haw0 j6)
    case hk => keeps_tac
    case hq => hsimp
    case j3 => rw [stBytes_text, ← lit_texts.2.2.2.1]; exact ⟨_, rfl, by hsimp⟩
    case hk2 => keeps_tac
  -- the search begins
  · unfold J65
    refine ⟨hopK, by assumption, ⟨?_, ?_, ?_, fun fs' h => ?_⟩, 0, ?_, ?_, Nat.zero_le _,
      fun _ h => absurd h (Nat.not_lt_zero _), fun fs' fdr' fsr' h1 h2 h3 => ?_, hinit, hstat⟩
    · simp [Frame.get_setLocal, f18]
    · simp [Frame.get_setLocal, f17]
    · simp [Frame.get_setLocal, f0]
    · rw [hst] at h; cases h; simp [Frame.get_setLocal, f3', g4]
    · simp [Frame.get_setLocal]; try decide
    · simp [Frame.get_setLocal]
    · rw [hst] at h1
      cases h1
      rw [gr] at h2
      cases h2
      rw [hr] at h3
      cases h3
      exact ⟨keeps_trans (keeps_of_grows ⟨left, right⟩) (keeps_setObj _ rfl), by hsimp <;> rfl⟩
  -- one more character
  all_goals
    unfold J33
    refine ⟨hopK, ⟨?_, ?_, ?_, fun fs' h => ?_⟩, kp, i + 1, ?_, hkp, ?_, ?_, ?_, ⟨left, right⟩, hinit, hstat⟩
    · simp [Frame.get_setLocal, f18]
    · simp [Frame.get_setLocal, f17]
    · simp [Frame.get_setLocal, f0]
    · rw [hst] at h; cases h; simp [Frame.get_setLocal, f3', g4]
    · simp [Frame.get_setLocal, f11]
    · rw [Frame.get_setLocal, if_neg (show (1 : Nat) ≠ 8 by decide), Frame.get_setLocal, if_pos rfl]
      have hc : i < (keyText a).length := by assumption
      rw [jkey_succ_bv _ _ _ (List.getElem?_eq_getElem hc) _ ?_]
      first
      | (rw [jdig_low (c := (keyText a)[i]'hc) (by assumption)]; decide)
      | (rw [jdig_high (c := (keyText a)[i]'hc) (by assumption)]; decide)
      | (rw [jdig_mid (c := (keyText a)[i]'hc) (by assumption) (by assumption)]
         exact toLong_digit _ (Nat.not_lt.1 (by assumption)) (Nat.not_lt.1 (by assumption)))
    · rw [Frame.get_setLocal, if_pos rfl, ofNat_succ32]
    · omega

end EquivLean.Modernize.Cbstm03b.Java.AcctP

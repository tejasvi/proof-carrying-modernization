import EquivLean.Modernize.Cbstm03b.Java.AcctFoundL

/-!
# CBSTM03B → Java, `acctProc`: the search finds record `j` (statement 65)

Status `00`; the file is positioned after record `j`; the FD record object is a fresh copy of record `j`;
`LK-M03B-FLDT` is the record's text (`zeroPad(id, 11) + fit(data, 289)`, padded to 1000).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

set_option jimple.modelContracts true in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem acct_search_found {oe st q : Addr} {opv : Value} {oeM : Model.OpenErrs} {s : Model.StM}
    {a : List EquivLean.Cobol.Rec.FVal} {σ0 : State}
    (hpre : (procSpecG ddAcct oe st q opv oeM s a).pre [.ref oe, .ref st, .ref q, opv] σ0)
    (fr : Frame) (σ : State) (hJ : J65 oe st q s a σ0 fr σ)
    (hcase : ∀ j, fr.get 10 = some (.int (BitVec.ofNat 32 j)) → j ≤ s.acct.recs.length →
      j < s.acct.recs.length ∧ Model.numOf ((s.acct.recs.getD j []).getD 0 default) = (keyVal a : Int)) :
    acctWP oe st q opv oeM s a σ0 65 fr σ := by
  obtain ⟨fs, fs4, fsr, fsq, o4, fdr, xop, l, sv, et, xs, dd, rc, key, fldt, b, kl, sdd, src, skey, sfl,
    hst, g4, ho4, hop4, hrec4, hl, hlen, hrs, hp, hpos, heof, gr, hr, gs, hq, hxop, hopv, hb, g2, g3, g4', g5, g6,
    n1, n2, n3, hI0, hF⟩ := pre_fin hpre
  obtain ⟨hopK, hopen, ⟨f18, f17, f0, f3⟩, j', f8, f10, hj, hnm, hfd, hinit, hstat⟩ := hJ
  obtain ⟨hjl, hm⟩ := hcase j' f10 hj
  clear hcase
  obtain ⟨hkf, hfdr⟩ := hfd fs fdr fsr hst gr hr
  have hF' := hF
  unfold FinCtx at hF'
  obtain ⟨-, -, -, hV, -, -, -, -, -, -, -, mr, hnr, -, -, ha, -, -, lkey, -, -, -, -, -, -, -, -, -, -, -, -, -,
    n4, n5, n6, -, -, -, -, -, -⟩ := hF'
  obtain ⟨y, fsy, nj, dj, sdj, hjx, ey, hy, hrj, hnj0, hnj1, hdj, gyid, gydata, jyd, nyf⟩ :=
    rec_at hrs hV.2.2.2.1 hnr ho4 hrec4 hl j' hjl
  have hxl := forall2_length hrs
  have nlf : l ≠ fdr := fun e => by rw [e, hr] at hl; cases hl
  have f3' := f3 fs hst
  rw [g4] at f3'
  have hst1 : σ.heap st = some (.plain "Cbstm03b$State" fs) := by
    rw [hkf.2 st (State.lt_next_of_heap hst) n4.symm, hst]
  have ho41 : σ.heap o4 = some (.plain "Cbstm03b$AcctFile" fs4) := by
    rw [hkf.2 o4 (State.lt_next_of_heap ho4) n5.symm, ho4]
  have hq1 : σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) := by
    rw [hkf.2 q (State.lt_next_of_heap hq) n6.symm, hq]
  have hl1 : σ.heap l = some (.array et xs) := by rw [hkf.2 l (State.lt_next_of_heap hl) nlf, hl]
  have hy1 : σ.heap y = some (.plain "Cbstm03b$FdAcctfileRec" fsy) := by
    rw [hkf.2 y (State.lt_next_of_heap hy) nyf, hy]
  have hI1 : σ.initOf "Cbstm03b" = .done := by rw [State.initOf_eq_of_inits hinit]; exact hI0
  have hIF : σ.initOf "Cbstm03b$FdAcctfileRec" = .done := by
    rw [State.initOf_eq_of_inits hinit]
    unfold FinCtx at hF; exact hF.2.2.2.2.2.2.1.2.2.2.2.2.2.1
  have htj := toInt32_ofNat (n := j') (by omega)
  have htl := toInt32_ofNat (n := xs.length) hlen
  have hmodj : j' % 4294967296 = j' := Nat.mod_eq_of_lt (by omega)
  have hnjk : nj = (keyVal a : Int) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some, hrj] at hm
    simpa [Model.numOf] using hm
  subst hnjk
  rw [BitVec.ofInt_natCast] at gyid
  have hkv : (BitVec.ofNat 64 (keyVal a)).toInt = (keyVal a : Int) := by
    have := jkey_lt (keyText a)
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
    have e : keyVal a % 2 ^ 64 = keyVal a := Nat.mod_eq_of_lt (by unfold keyVal; omega)
    rw [e]
    split
    · rfl
    · unfold keyVal at *; omega
  have hkv0 : 0 ≤ (BitVec.ofNat 64 (keyVal a)).toInt := by rw [hkv]; omega
  obtain ⟨xd, exd, hxd⟩ := id jyd
  subst exd
  have nxf : xd ≠ fdr := fun e => by rw [e] at hxd; rw [hxd] at hr; cases hr
  have hxd1 : σ.heap xd = some (.str (cp037Str dj)) := by rw [hkf.2 xd (State.lt_next_of_heap hxd) nxf, hxd]
  have hdj32 : (cp037Str dj).length < 2147483648 := by rw [cp037Str_length, hdj]; decide
  have nxs : xd ≠ st := fun e => by rw [e] at hxd; rw [hxd] at hst; cases hst
  have nxo : xd ≠ o4 := fun e => by rw [e] at hxd; rw [hxd] at ho4; cases ho4
  have n1' := n1.symm
  have n2' := n2.symm
  have n3' := n3.symm
  have hH := hid_intro (And.intro hst <| And.intro ho4 <| And.intro hr <| And.intro hq <| And.intro hinit <|
    And.intro hstat <| And.intro hkf <| And.intro hnm <| And.intro hxl <| And.intro hrj <| And.intro jyd <|
    And.intro hkv hm)
  clear hpre hrs f3 hst ho4 hr hq hl hI0 hxop hV mr ha lkey hopv hb hinit hstat hkf hfd hnm hxl hy jyd hrj hnr
    hkv hm hxd
  simp only [acctWP, procSpecG, Spec.of]
  jvc [acctInv, acctCallees, status2Sig, fitSig, keySubSig, spacesSig, zeroPadSig, Grows, n1, n2, n3, n1', n2',
    n3', n4, n5, n6, StrOk, argText]
  · simp [zpadStr_length]
  all_goals rename_i σa wa hwa hna hha hia hsa hfa1 hfa2 hra1 hra2 σb wb hwb hnb hhb hib hsb hfb1 hfb2 hrb1 hrb2 σc hwc hnc hhc hfc1 hrc1 hc1 hc2 hc3 hc4
  all_goals obtain ⟨hst, ho4, hr, hq, hinit, hstat, hkf, hnm, hxl, hrj, jyd, hkv, hm⟩ := hid_elim hH
  all_goals unfold FinCtx at hF
  all_goals obtain ⟨hS, hSep, hE, hV, hK, hdd, hI, hA, hVa, m4, hr', mr, hnr, gr', js, ha, ldd, lrc, lkey, hkl1,
    hkl2, lfl, g1, j1, g2', j2, j3, g4', j4, g5, g6', j6, n4, n5, n6, lst, lo4, lq, lfdr, haw0, hawr⟩ := hF
  all_goals
    have hval := acctVal_keyVal hK hopK hdd ha lkey
    have hcall := call_key_found (oeM := oeM) hdd hopK hopen hjl (by rw [hval]; exact hm)
      (fun i hi => by rw [hval]; exact hnm i hi)
    have hgj : s.acct.recs.getD j' [] = [.num (keyVal a : Int), .str dj] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some, hrj]
    rw [hgj] at hcall
    -- the objects of the final state, through the three contract calls
    have hk01 := hkf.1
    have hσ : ∀ x, x < σ0.next → x ≠ st → x ≠ o4 → x ≠ fdr → σc.heap x = σ0.heap x := by
      intro x hx h1 h2 h3
      have hx' : x < σ.next := Nat.lt_of_lt_of_le hx hk01
      rw [← hkf.2 x hx h3]
      hsimp [hhc, hhb, hha, h1, h2]
    have hc4' : σc.heap o4 = some (.plain "Cbstm03b$AcctFile" (Fields.set (Fields.set fs4
        ("Cbstm03b$AcctFile", "pos") (.int (BitVec.ofNat 32 j' + 1#32))) ("Cbstm03b$AcctFile", "eof")
        (.int 0#32))) := by
      hsimp [hhc, hhb, hha, n1']
    have hcst : σc.heap st = some (.plain "Cbstm03b$State"
        (Fields.set fs ("Cbstm03b$State", "fdAcctfileRec") (.ref (σ.next + 1)))) := by
      hsimp [hhc, hhb, hha]
    have hcq : σc.heap q = some (.plain "Cbstm03b$LkM03bArea" fsq) := by
      rw [hσ q lq n2.symm n3.symm n6.symm, hq]
    obtain ⟨xd', exd', hxd'⟩ := jyd
    cases exd'
    have hcxd : σc.heap xd = some (.str (cp037Str dj)) := by
      rw [hσ xd (State.lt_next_of_heap hxd') nxs nxo nxf, hxd']
    have hcfd : σc.heap (σ.next + 1) = some (.plain "Cbstm03b$FdAcctfileRec"
        (Fields.set (Fields.set [(("Cbstm03b$FdAcctfileRec", "fdAcctId"), Value.long 0#64),
          (("Cbstm03b$FdAcctfileRec", "fdAcctData"), Value.null)] ("Cbstm03b$FdAcctfileRec", "fdAcctId")
          (.long (BitVec.ofNat 64 (keyVal a)))) ("Cbstm03b$FdAcctfileRec", "fdAcctData") (.ref xd))) := by
      hsimp [hhc, hhb, hha]
    have hc00 : σc.heap σ.next = some (.str (JStr.ofString "00")) := by
      hsimp [hhc, hhb, hha]
    have nwq : w ≠ q := fun e => by rw [e, hcq] at hwc; cases hwc
    have nws : w ≠ st := fun e => by rw [e, hcst] at hwc; cases hwc
    have hcw : σc.heap w =
        some (.str (fixStr (zpadStr (keyVal a) 11 ++ fixStr (cp037Str dj) 289) 1000)) := by
      rw [hwc]; hsimp [nxs, nxo, Option.getD_some]
    have hσc : σ0.next ≤ σc.next := Nat.le_trans hk01 (Nat.le_trans (Nat.le_trans (Nat.le_succ_of_le
      (Nat.le_succ _)) hna) (Nat.le_trans hnb (Nat.le_trans (Nat.le_succ_of_le (Nat.le_succ _)) hnc)))
    have hkc : Keeps (AccA st o4 q fdr) σ0 σc := ⟨hσc, fun x hx hA => by
      simp only [AccA, not_or] at hA
      obtain ⟨h1, h2, h3, h4⟩ := hA
      exact hσ x hx h1 h2 h4⟩
    have nxq : xd ≠ q := fun e => by rw [e] at hxd'; rw [hxd'] at hq; cases hq
    have hvj : Model.FdAcctfileRec.Valid [.num (keyVal a : Int), .str dj] := by
      have := hV.2.2.2.1 _ (List.getElem_mem hjl); rw [hrj] at this; exact this
    have hj31 : j' + 1 < 2147483648 := by omega
    first
    | (rw [hcall]
       refine state_fin (fs' := Fields.set (Fields.set fs ("Cbstm03b$State", "fdAcctfileRec") (.ref (σ.next + 1)))
           ("Cbstm03b$State", "acctfileStatus") (.ref σ.next))
         hS hst ho4 hq hr ?hk ?hst ?hrest ⟨⟨.ref o4, ?g4, ?m4⟩, ⟨.ref (σ.next + 1), ?gr, ?mr⟩,
           ⟨.ref σ.next, ?gs, ?js⟩⟩
       case hk => keeps_tac
       case hst => hsimp [n2]
       case hrest =>
         exact fun k _ h2 h3 => by
           rw [get_set_ne _ (fun e => h3 (Prod.mk.inj e).2), get_set_ne _ (fun e => h2 (Prod.mk.inj e).2)]
       case g4 => rw [get_set_ne _ (by decide +kernel), get_set_ne _ (by decide +kernel)]; exact g4
       case gr => rw [get_set_ne _ (by decide +kernel), get_set_eq]
       case mr =>
         refine acctRecAt_mk (fs := Fields.set (Fields.set [(("Cbstm03b$FdAcctfileRec", "fdAcctId"), Value.long 0#64),
             (("Cbstm03b$FdAcctfileRec", "fdAcctData"), Value.null)] ("Cbstm03b$FdAcctfileRec", "fdAcctId")
             (.long (BitVec.ofNat 64 (keyVal a)))) ("Cbstm03b$FdAcctfileRec", "fdAcctData") (.ref xd)) ?_ ?_
           (get_set_eq _ _ _) ⟨xd, rfl, ?_⟩
         · hsimp [hcfd]
         · rw [get_set_ne _ (by decide +kernel), get_set_eq, BitVec.ofInt_natCast]
         · hsimp [hcxd, nxs, nxq]
       case gs => exact get_set_eq _ _ _
       case js => rw [status_text, ← lit_texts.1]; exact ⟨_, rfl, by hsimp [hc00]⟩
       case m4 =>
         refine acctFile_fin (fs4' := Fields.set (Fields.set fs4 ("Cbstm03b$AcctFile", "pos")
             (.int (BitVec.ofNat 32 j' + 1#32))) ("Cbstm03b$AcctFile", "eof") (.int 0#32)) m4 hnr hst ho4 hq hr ?_ ?_
           (by rw [get_set_ne _ (by decide +kernel), get_set_ne _ (by decide +kernel)])
           (by rw [get_set_ne _ (by decide +kernel), get_set_ne _ (by decide +kernel)]; exact hop4)
           (by rw [get_set_ne _ (by decide +kernel), get_set_eq, ofNat_succ32])
           (by rw [get_set_eq]; rfl) rfl hj31
         · keeps_tac
         · hsimp [hc4', n1', n3])
    | (refine sepM_fin (fs' := Fields.set (Fields.set fs ("Cbstm03b$State", "fdAcctfileRec") (.ref (σ.next + 1)))
           ("Cbstm03b$State", "acctfileStatus") (.ref σ.next))
         (fs4' := Fields.set (Fields.set fs4 ("Cbstm03b$AcctFile", "pos")
             (.int (BitVec.ofNat 32 j' + 1#32))) ("Cbstm03b$AcctFile", "eof") (.int 0#32)) (fdr' := σ.next + 1)
         hS hSep hst ho4 hq hr g4 gr ?hk ?hst
         (fun k _ h2 h3 => by
           rw [get_set_ne _ (fun e => h3 (Prod.mk.inj e).2), get_set_ne _ (fun e => h2 (Prod.mk.inj e).2)])
         (by rw [get_set_ne _ (by decide +kernel), get_set_ne _ (by decide +kernel)]; exact g4)
         (by rw [get_set_ne _ (by decide +kernel), get_set_eq]) (Or.inr (Nat.le_succ_of_le hk01)) ?h4
         (by rw [get_set_ne _ (by decide +kernel), get_set_ne _ (by decide +kernel)])
       case hk => keeps_tac
       case hst => hsimp [n2]
       case h4 => hsimp [hc4', n1', n3])
    | (have hset : Model.setFldt (Model.setRc a (stBytes 0))
           (Model.FdAcctfileRec.encode [.num (keyVal a : Int), .str dj]) = [.str dd, .str [b], .str (stBytes 0),
           .str key, .num kl, .str (intoBuf (Model.FdAcctfileRec.encode [.num (keyVal a : Int), .str dj]))] := by
         rw [ha]; rfl
       rw [hcall, hset]
       refine area_fin (rc' := stBytes 0)
         (fldt' := intoBuf (Model.FdAcctfileRec.encode [.num (keyVal a : Int), .str dj])) (src' := .ref σ.next)
         (sfl' := .ref w) (fsq' := Fields.set (Fields.set fsq ("Cbstm03b$LkM03bArea", "lkM03bFldt") (.ref w))
           ("Cbstm03b$LkM03bArea", "lkM03bRc") (.ref σ.next))
         ?hk haw0 ?hq g1 j1 g2' j2 g4' j4 g5
         (by rw [get_set_ne _ (by decide +kernel), get_set_ne _ (by decide +kernel)])
         (by rw [get_set_ne _ (by decide +kernel), get_set_ne _ (by decide +kernel)])
         (by rw [get_set_ne _ (by decide +kernel), get_set_ne _ (by decide +kernel)])
         (by rw [get_set_ne _ (by decide +kernel), get_set_ne _ (by decide +kernel)])
         (get_set_eq _ _ _) ?j3 (by rw [get_set_ne _ (by decide +kernel), get_set_eq]) ?j6
       case hk => keeps_tac
       case hq => hsimp
       case j3 => rw [stBytes_text, ← lit_texts.1]; exact ⟨_, rfl, by hsimp [hc00]⟩
       case j6 => rw [fldt_text _ _ hvj hdj]; exact ⟨_, rfl, by hsimp [hcw, nwq, nws]⟩)

end EquivLean.Modernize.Cbstm03b.Java.AcctP

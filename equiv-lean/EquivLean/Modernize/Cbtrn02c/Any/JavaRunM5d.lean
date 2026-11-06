import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5c
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5q
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5r
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5e
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM4v
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM3v
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2y

/-!
# CBTRN02C → Java: `postTransaction` from cut point 36 to the end

Segment 36 → 39: `updateTcatbal` (the category balance updated: `W` for `postCat`); 39 → 40:
`updateAccount` (`W` for `postAcc`); 40 → end: `writeTransaction` (a new id: `W` for `Model.St.post`,
`false`; a written id: `WAb` for `dupSt`, `true`).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- `PtWPc` is the symbolic execution against `postTransactionSpec`'s postcondition. -/
theorem PtWPc_eq (args : List Value) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) :
    PtWPc args σ0 cuts pc fr σ = bodyWP Gen.prog (callWP Gen.prog ptCallees.env 0) ptBody cuts
      (postTransactionSpec.post args σ0) 80 pc fr σ := by
  unfold PtWPc ptPost
  rfl

theorem initOf_of_inits {σ σ0 : State} (h : σ.inits = σ0.inits) (c : ClassName) :
    σ.initOf c = σ0.initOf c := by
  simp only [State.initOf, h]

theorem inits_of {σ σ0 : State} (h : σ.inits = σ0.inits) (hI : Inits σ0) : Inits σ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hI
  exact ⟨by rw [initOf_of_inits h]; exact i1, by rw [initOf_of_inits h]; exact i2,
    by rw [initOf_of_inits h]; exact i3, by rw [initOf_of_inits h]; exact i4,
    by rw [initOf_of_inits h]; exact i5, by rw [initOf_of_inits h]; exact i6,
    by rw [initOf_of_inits h]; exact i7, by rw [initOf_of_inits h]; exact i8⟩

/-- `tranWs` is not a string and not one of the other records. -/
theorem wT_facts {σ : State} {A : Addrs} {s : Model.St} (hW : W σ A s) :
    ∃ fs, σ.heap A.wT = some (.plain trCls fs) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨fs, h, -⟩, -⟩ := hW
  exact ⟨fs, h⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem pt_seg36 (p : PG) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : PtFacts σ0 p) (h36 : Pt36 p.args σ0 fr σ)
    (c37 : cuts.lookup 37 = none) (c38 : cuts.lookup 38 = none)
    (c39 : cuts.lookup 39 = some (Pt39 p.args σ0)) :
    PtWPc p.args σ0 cuts 36 fr σ := by
  have hkeep36 := Hide.intro h36
  obtain ⟨hL, hW, hfr, hin, hst, htw⟩ := h36 p rfl hP
  have hP' := hP
  obtain ⟨hW0, hMV, hd, htv, hx, hxv, ha, hfa, hcs, hcd, hlen, hI, hAd⟩ := hP'
  obtain ⟨f4, f2, f8, f5, f1, f11, f0, f6, f7⟩ := hL
  obtain ⟨fsT, hwT⟩ := wT_facts hW0
  have hS : NoStr σ0 [p.A.wT] := by
    intro a ha' t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    rw [ha', hwT] at ht; cases ht
  have hd1 : JRecAt DalytranRecord dalCls σ (.ref p.d) p.t := by
    refine jrecAt_frame hd hfr hS ?_
    rintro x hx' hm
    cases hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    obtain ⟨y, fs, hy, hyo, -⟩ := hd
    cases hy
    rw [hm, hwT] at hyo
    simp only [Option.some.injEq, Obj.plain.injEq] at hyo
    exact absurd hyo.1 (by decide)
  have hx1 : JRecAt CardXrefRecord xrCls σ (.ref p.A.wX) p.x := by
    refine jrecAt_frame hx hfr hS ?_
    rintro x hx' hm
    cases hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    obtain ⟨y, fs, hy, hyo, -⟩ := hx
    cases hy
    rw [hm, hwT] at hyo
    simp only [Option.some.injEq, Obj.plain.injEq] at hyo
    exact absurd hyo.1 (by decide)
  have hI1 := inits_of hin hI
  have hpre := utPre_of hW hMV hd1 htv hx1 hxv hlen.1 hI1
  have hkeepP := Hide.intro hpre
  clear hpre hW hd1 hx1 hfr htw hW0 hMV hd htv hx hxv ha hfa hcs hcd hlen hI hAd hS hwT hst hP
  unfold PtWPc
  jvc [ptCallees, updateTcatbalSig, updateTcatbalSpec, Grows, narrow_long, narrow_cls, PG.args]
  · exact Hide.elim hkeepP
  · rename_i σ1 hcr hup hi1 _
    intro p' hargs hP2
    have hargs0 := hargs
    simp only [PG.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨er, ed, ecs, ewX, ewA, ewC, ewT, eaD, elC, elK⟩ := hargs
    obtain ⟨hL', hW', hfr', hin', hst', htw'⟩ := (Hide.elim hkeep36) p' hargs0 hP2
    obtain ⟨hW0', hMV', hd', htv', hx', hxv', -, -, -, -, hlen', -, -⟩ := hP2
    obtain ⟨fsT', hwT'⟩ := wT_facts hW0'
    have hS' : NoStr σ0 [p'.A.wT] := by
      intro a ha' t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rw [ha', hwT'] at ht; cases ht
    have hd1' : JRecAt DalytranRecord dalCls σ (.ref p'.d) p'.t := by
      refine jrecAt_frame hd' hfr' hS' ?_
      rintro x hx'' hm
      cases hx''
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      obtain ⟨y, fs, hy, hyo, -⟩ := hd'
      cases hy
      rw [hm, hwT'] at hyo
      simp only [Option.some.injEq, Obj.plain.injEq] at hyo
      exact absurd hyo.1 (by decide)
    have hx1' : JRecAt CardXrefRecord xrCls σ (.ref p'.A.wX) p'.x := by
      refine jrecAt_frame hx' hfr' hS' ?_
      rintro x hx'' hm
      cases hx''
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      obtain ⟨y, fs, hy, hyo, -⟩ := hx'
      cases hy
      rw [hm, hwT'] at hyo
      simp only [Option.some.injEq, Obj.plain.injEq] at hyo
      exact absurd hyo.1 (by decide)
    have hnot := wT_not_mem hW'
    have hNS := noStr_W hW'
    simp only [er, ed, ewX, ewC, elC] at hcr hup
    rcases Int.lt_or_le (utIdx σ p'.d p'.A.wX p'.A.lC) 0 with hn | hp
    · obtain ⟨sD, ⟨m1, hD'⟩, hsD, y1, y2, fsC', hwC', f0, f1, f2, f3, f4, ⟨m2, hC'⟩, fs1, hy1, hs1,
        ⟨m3, hCW'⟩, fs2, hy2, hs2, hn1, hn2, -, hnD, hfS⟩ := hcr hn
      obtain ⟨hW1, hfr1⟩ := w39_create hW' hMV' hd1' htv' hx1' hxv' hlen' hn hD' hsD hwC' f0 f1 f2 f3
        f4 hC' hy1 hs1 hCW' hy2 hs2 hn1 hn2 hnD hfS
      exact pt39_body hL' hW1 hfr' hfr1 (by simp)
        (fun hm => hnot (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
          rcases hm with h | h | h | h <;> simp [h]))
        (hNS.mono (by simp [PtMod])) hi1 (left.trans hst') htw'
    · obtain ⟨y1, y2, fsA, hfa, hwC', ⟨m2, hC'⟩, fs1, hy1, hs1, ⟨m3, hCR'⟩, fs2, hy2, hs2, hn1, hn2, -,
        hfS⟩ := hup hp
      obtain ⟨hW1, hfr1⟩ := w39_update hW' hMV' hd1' htv' hx1' hxv' hlen' hp hfa hwC' hC' hy1 hs1 hCR'
        hy2 hs2 hn1 hn2 hfS
      exact pt39_body hL' hW1 hfr' hfr1 (by simp)
        (fun hm => hnot (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
          rcases hm with h | h | h <;> simp [h]))
        (hNS.mono (by simp [PtMod])) hi1 (left.trans hst') htw'

theorem postCat_accts (s : Model.St) (t x : List EquivLean.Cobol.Rec.FVal) :
    (postCat s t x).accts = s.accts := by
  unfold postCat; split <;> rfl

theorem postCat_acctRW (s : Model.St) (t x : List EquivLean.Cobol.Rec.FVal) :
    (postCat s t x).acctRW = s.acctRW := by
  unfold postCat; split <;> rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem pt_seg39 (p : PG) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : PtFacts σ0 p) (h39 : Pt39 p.args σ0 fr σ)
    (c40 : cuts.lookup 40 = some (Pt40 p.args σ0)) :
    PtWPc p.args σ0 cuts 39 fr σ := by
  have hkeep39 := Hide.intro h39
  obtain ⟨hL, hW, hfr, hin, hst, htw⟩ := h39 p rfl hP
  have hP' := hP
  obtain ⟨hW0, hMV, hd, htv, hx, hxv, ha, hfa, hcs, hcd, hlen, hI, hAd⟩ := hP'
  obtain ⟨f4, f2, f8, f5, f1, f11, f0, f6, f7⟩ := hL
  have hNS0 := noStr_W hW0
  have hS : NoStr σ0 [p.A.wT, p.A.wC, p.A.lC, p.A.lD, p.A.lCW, p.A.lCR] :=
    hNS0.mono (by simp [PtMod])
  have hnotA := wA_not_mem hW0
  have hnotD := d_not_mem hW0 hd
  have hd1 : JRecAt DalytranRecord dalCls σ (.ref p.d) p.t :=
    jrecAt_frame hd hfr hS (fun y hy hm => by cases hy; exact hnotD hm)
  have ha1 : JRecAt AccountRecord acCls σ (.ref p.A.wA) p.a :=
    jrecAt_frame ha hfr hS (fun y hy hm => by cases hy; exact hnotA.1 hm)
  have hAd1 : ∃ xs, σ.heap p.A.aD = some (.array (.cls acCls) xs) := by
    obtain ⟨xs, hxs⟩ := hAd
    exact ⟨xs, hfr.heap hxs hnotA.2⟩
  have hI1 := inits_of hin hI
  have ham : p.a ∈ p.s.accts := List.mem_of_find?_eq_some hfa
  have hav : AccountRecord.Valid p.a := hMV.1 p.a ham
  have hpre := uaPre_of hW (MV_postCat hMV htv hxv) hAd1 hd1 htv ha1 hav
    ⟨p.a, by rw [postCat_accts]; exact ham, rfl⟩ hI1
  have hkeepP := Hide.intro hpre
  clear hpre hW hd1 ha1 hAd1 hfr htw hW0 hMV hd htv hx hxv ha hfa hcs hcd hlen hI hAd hS hst hP
    hNS0 hnotA hnotD ham hav
  unfold PtWPc
  jvc [ptCallees, updateAccountSig, updateAccountSpec, Grows, narrow_long, narrow_cls, PG.args]
  · obtain ⟨r', d', wA', aD', fsR, fsd, fsA, lAR, amt, bal, cc, cdb, id, xsA, ys, m, hargs, hR, hRk, hd,
      hamt, hA, hall, hbal, hcc, hcd, hid, haD, hlen, hsh, hne, hidx, hlAR, n1, n2, n3, n4, n5, i1,
      i2⟩ := Hide.elim hkeepP
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
    exact ⟨fsR, hR, fsd, fsA, lAR, hRk, hd, ⟨amt, hamt⟩, hA, hall, ⟨bal, hbal⟩, ⟨cc, hcc⟩, ⟨cdb, hcd⟩,
      id, hid, xsA, haD, hlen, hsh, hne, hidx, ⟨ys, m, hlAR⟩, n1, n2, n3, n4, n5⟩
  · rename_i _ σ1 hpost
    intro p' hargs hP2
    have hargs0 := hargs
    simp only [PG.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨er, ed, ecs, ewX, ewA, ewC, ewT, eaD, elC, elK⟩ := hargs
    obtain ⟨hL', hW', hfr', hin', hst', htw'⟩ := (Hide.elim hkeep39) p' hargs0 hP2
    obtain ⟨hW0', hMV', hd', htv', hx', hxv', ha', hfa', -, -, hlen', -, -⟩ := hP2
    have hNS0' := noStr_W hW0'
    have hS' : NoStr σ0 [p'.A.wT, p'.A.wC, p'.A.lC, p'.A.lD, p'.A.lCW, p'.A.lCR] :=
      hNS0'.mono (by simp [PtMod])
    have hnotA' := wA_not_mem hW0'
    have hnotD' := d_not_mem hW0' hd'
    have hd1' : JRecAt DalytranRecord dalCls σ (.ref p'.d) p'.t :=
      jrecAt_frame hd' hfr' hS' (fun y hy hm => by cases hy; exact hnotD' hm)
    have ha1' : JRecAt AccountRecord acCls σ (.ref p'.A.wA) p'.a :=
      jrecAt_frame ha' hfr' hS' (fun y hy hm => by cases hy; exact hnotA'.1 hm)
    have ham' : p'.a ∈ p'.s.accts := List.mem_of_find?_eq_some hfa'
    have hav' := hMV'.1 p'.a ham'
    obtain ⟨hwA', y1, hD', y2, fs1, hy1, hs1, ⟨m', hAR'⟩, fs2, hy2, hs2, hn1, hn2, -, hfS, hi1, hs1',
      -⟩ := hpost p'.A.r p'.d p'.A.wA p'.A.aD er ed ewA eaD
    have hlenA : (postCat p'.s p'.t p'.x).acctRW.length + 1 < 2147483648 := by
      rw [postCat_acctRW]; exact hlen'.2.2.2.2.1
    obtain ⟨hW1, hfr1⟩ := w40_of hW' (MV_postCat hMV' htv' hxv') hd1' htv' ha1' hav'
      (by rw [postCat_accts]; exact ham') hlenA hwA' hD' hy1 hs1 hAR' hy2 hs2 hn1 hn2 hfS
    have hnotT := wT_not_mem hW'
    exact pt40_body hL' hW1 hfr' hfr1
      (fun hm => hnotT (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
        rcases hm with h | h | h <;> simp [h]))
      ((noStr_W hW').mono (by simp [PtMod])) hi1 (hs1'.trans hst') htw' ⟨_, hD'⟩

theorem tranVals_head {t : List EquivLean.Cobol.Rec.FVal} (htv : DalytranRecord.Valid t)
    (clk : List UInt8) : t ≠ [] ∧ ∃ b0 rest, Model.tranVals t clk = .str b0 :: rest := by
  obtain ⟨id, ty, cat, src, desc, amt, merch, mname, mcity, mzip, card, orig, proc, fill, rfl, -⟩ :=
    Glue.tran_shape htv
  exact ⟨by simp, id, _, rfl⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem pt_seg40 (p : PG) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : PtFacts σ0 p) (h40 : Pt40 p.args σ0 fr σ) (c41 : cuts.lookup 41 = none) :
    PtWPc p.args σ0 cuts 40 fr σ := by
  have hkeep40 := Hide.intro h40
  obtain ⟨hL, hW, hfr, hin, hst, htw, -⟩ := h40 p rfl hP
  have hP' := hP
  obtain ⟨hW0, hMV, hd, htv, hx, hxv, ha, hfa, hcs, hcd, hlen, hI, hAd⟩ := hP'
  obtain ⟨f4, f2, f8, f5, f1, f11, f0, f6, f7⟩ := hL
  obtain ⟨-, b0, rest, htve⟩ := tranVals_head htv p.clk
  rw [htve] at htw
  have hI1 := inits_of hin hI
  have hpre := wtPreX_of hW htw hI1
  have hkeepP := Hide.intro hpre
  clear hpre hW hfr htw hW0 hMV hd htv hx hxv ha hfa hcs hcd hlen hI hAd hst hP htve
  unfold PtWPc
  jvc [ptCallees, writeTransactionSig, writeTransactionSpecX, Grows, narrow_long, narrow_cls, PG.args]
  · obtain ⟨r', wT', lK', fsR, lT, lD, fsT, sId, idcs, ks, mK, ts, mT, ds, mD, hargs, hR, hRT, hRD,
      ⟨ab, hab⟩, hT, hallT, hid, hsId, hlK, hlen, hsh, hlT, hlD, hnd, i1, i2, i3⟩ := Hide.elim hkeepP
    simp only [List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl⟩ := hargs
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true] at hnd
    obtain ⟨⟨n1, n2⟩, n3⟩ := hnd
    exact ⟨fsR, hR, lT, hRT, lD, hRD, ⟨ab, hab⟩, fsT, hT, hallT, sId, hid, ⟨idcs, hsId⟩, ks, ⟨mK, hlK⟩,
      hlen, hsh, ⟨ts, mT, hlT⟩, ⟨ds, mD, hlD⟩, ⟨n1, n2⟩, n3⟩
  · rename_i v σ1 hnodup hdup hi1 _
    unfold ptPost
    simp only [postTransactionSpec, Spec.of]
    intro p' hargs hP2
    have hargs0 := hargs
    simp only [PG.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
    obtain ⟨er, ed, ecs, ewX, ewA, ewC, ewT, eaD, elC, elK⟩ := hargs
    obtain ⟨hL', hW', hfr', hin', hst', htw', hAd40'⟩ := (Hide.elim hkeep40) p' hargs0 hP2
    obtain ⟨hW0', hMV', hd', htv', hx', hxv', ha', hfa', -, -, hlen', -, -⟩ := hP2
    obtain ⟨hne', b0', rest', htve'⟩ := tranVals_head htv' p'.clk
    rw [htve'] at htw'
    simp only [er, ewT, elK] at hnodup hdup
    refine ⟨fun hn => ?_, fun hm => ?_, hi1, left.trans hst'⟩
    · have hn' : tidJ (.str b0' :: rest') ∉
          (postAcc (postCat p'.s p'.t p'.x) p'.t p'.a).tranW.map tidJ := by
        rw [← htve', postAcc_postCat_tranW, tidJ_mem_iff hne']; exact hn
      obtain ⟨hv, ⟨mK', hK'⟩, y, ⟨mT', hT'⟩, hy, fsy, hyo, hsame, hfS⟩ :=
        hnodup (wtIdx_neg hW' htw' hn')
      have hlenT : (postAcc (postCat p'.s p'.t p'.x) p'.t p'.a).tranW.length + 1 < 2147483648 := by
        rw [postAcc_postCat_tranW]; exact hlen'.2.2.2.2.2
      obtain ⟨hW1, hfr1⟩ := w41_tran hW' htw' hK' hT' hy hyo hsame hfS hlenT
      rw [← htve'] at hW1
      refine ⟨by rw [hv]; rfl, ?_, ?_, ?_⟩
      · rw [post_eq]; exact hW1
      · exact FrameS.trans (hfr'.mono (by simp [PtMod])) (hfr1.mono (by simp [PtMod]))
      · obtain ⟨xs, hxs⟩ := hAd40'
        obtain ⟨-, -, ⟨xT, mT, hT0, -⟩, -, -, -, -, -, -, ⟨xk, mk, hK0, -⟩, -⟩ := hW'
        refine ⟨xs, hfr1.heap hxs ?_⟩
        intro hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with h | h
        · rw [h, hK0] at hxs; cases hxs
        · rw [h, hT0] at hxs; cases hxs
    · have hm' : tidJ (.str b0' :: rest') ∈
          (postAcc (postCat p'.s p'.t p'.x) p'.t p'.a).tranW.map tidJ := by
        rw [← htve', postAcc_postCat_tranW, tidJ_mem_iff hne']; exact hm
      obtain ⟨hv, y1, y2, y3, ⟨mD', hD'⟩, h1, h2, h3, hr, -, -, -, hfS⟩ :=
        hdup (wtIdx_nonneg hW' htw' hm')
      have hlenD : (postAcc (postCat p'.s p'.t p'.x) p'.t p'.a).disp.length + 3 < 2147483648 := by
        have := postAcc_postCat_disp p'.s p'.t p'.x p'.a
        have := hlen'.2.2.2.1
        omega
      exact ⟨by rw [hv]; rfl, wab_of hW' hD' h1 h2 h3 hr hfS hlenD⟩

theorem ptInv_lookup_none (args : List Value) (σ0 : State) (k : Nat) (h1 : k ≠ 36) (h2 : k ≠ 39)
    (h3 : k ≠ 40) : (ptInv.inst args σ0).lookup k = none := by
  apply lookup_none_of
  simp only [ptInv, Invariants.inst, List.map, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  exact ⟨fun e => h1 e.symm, fun e => h2 e.symm, fun e => h3 e.symm⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem postTransaction_vc :
    MethodVC Gen.prog ptCallees.env 0 postTransactionRef postTransactionSpec ptInv 80 := by
  refine ⟨ptBody, rfl, ?_⟩
  intro args σ0 hpre
  obtain ⟨p, rfl, hP⟩ := hpre
  have hnone : ∀ k, k ≠ 36 → k ≠ 39 → k ≠ 40 → (ptInv.inst p.args σ0).lookup k = none :=
    fun k h1 h2 h3 => ptInv_lookup_none p.args σ0 k h1 h2 h3
  refine ⟨?_, ?_⟩
  · have h0 : (ptInv.inst p.args σ0).lookup 0 = none := rfl
    simp only [h0]
    dsimp only [jground]
    rw [← PtWPc_eq]
    exact pt_entry p σ0 _ hP (fun k h1 h2 => hnone k (by omega) (by omega) (by omega)) rfl
  · intro q hq fr σ hI
    rw [← PtWPc_eq]
    simp only [ptInv, Invariants.inst, List.map, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact pt_seg36 p σ0 _ fr σ hP hI (hnone 37 (by omega) (by omega) (by omega))
        (hnone 38 (by omega) (by omega) (by omega)) rfl
    · exact pt_seg39 p σ0 _ fr σ hP hI rfl
    · exact pt_seg40 p σ0 _ fr σ hP hI (hnone 41 (by omega) (by omega) (by omega))

set_option maxHeartbeats 0 in
theorem db2TimestampF_ok : ContractOK Gen.prog db2TimestampSig db2TimestampSpecF := by
  jcontract_ok [db2TimestampF_sat]

theorem postTransaction_sat : Sat Gen.prog postTransactionRef postTransactionSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro c hc
    simp only [ptCallees, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact db2TimestampF_ok
    · exact updateTcatbal_ok
    · exact updateAccount_ok
    · exact writeTransactionX_ok)) postTransaction_vc

set_option maxHeartbeats 0 in
theorem postTransaction_ok : ContractOK Gen.prog postTransactionSig postTransactionSpec := by
  jcontract_ok [postTransaction_sat]

end EquivLean.Modernize.Cbtrn02c.Java

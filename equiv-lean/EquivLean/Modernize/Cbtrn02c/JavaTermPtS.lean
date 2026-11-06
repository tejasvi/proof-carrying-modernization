-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermPtS.lean (sha256 6e52b71922273ba8...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5d
import EquivLean.Modernize.Cbtrn02c.JavaTermDefsH

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunM5d`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem pt_tseg36 (p : PG) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : PtFacts σ0 p) (h36 : Pt36 p.args σ0 fr σ)
    (c37 : cuts.lookup 37 = none) (c38 : cuts.lookup 38 = none)
    (c39 : cuts.lookup 39 = some (fun fr' σ' => ptVs 39 p.args σ0 fr' σ' < ptVs 36 p.args σ0 fr σ)) :
    PtThinWPc p.args σ0 cuts 36 fr σ := by
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
  unfold PtThinWPc
  jvc [ptCallees, updateTcatbalSig, updateTcatbalSpec, Grows, narrow_long, narrow_cls, PG.args, ptVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem pt_tseg39 (p : PG) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : PtFacts σ0 p) (h39 : Pt39 p.args σ0 fr σ)
    (c40 : cuts.lookup 40 = some (fun fr' σ' => ptVs 40 p.args σ0 fr' σ' < ptVs 39 p.args σ0 fr σ)) :
    PtThinWPc p.args σ0 cuts 39 fr σ := by
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
  unfold PtThinWPc
  jvc [ptCallees, updateAccountSig, updateAccountSpec, Grows, narrow_long, narrow_cls, PG.args, ptVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem pt_tseg40 (p : PG) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : PtFacts σ0 p) (h40 : Pt40 p.args σ0 fr σ) (c41 : cuts.lookup 41 = none) :
    PtThinWPc p.args σ0 cuts 40 fr σ := by
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
  unfold PtThinWPc
  jvc [ptCallees, writeTransactionSig, writeTransactionSpecX, Grows, narrow_long, narrow_cls, PG.args, ptVs]

end EquivLean.Modernize.Cbtrn02c.Java

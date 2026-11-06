-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermUtB.lean (sha256 83f29c3e2d615437...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM4
import EquivLean.Modernize.Cbtrn02c.JavaTermDefsH

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunM4`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_tseg41 (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : UtPre σ0 r d wX wC lC) (hn : utIdx σ0 d wX lC < 0)
    (h41 : ut41 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr σ)
    (hc : ∀ k, 42 ≤ k → k ≤ 50 → cuts.lookup k = none) (c68 : cuts.lookup 68 = none) :
    UtThinWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 41 fr σ := by
  obtain ⟨-, f5, f2, f8, f0, f6, f3, f11, f4, hin, hst, hio, ⟨sD, m1, hDl, hsD, hsD0⟩,
    ⟨fsC', hC', g0, g1, g2, g3, g4, gall⟩, hfr⟩ := h41 r d wX wC lC rfl hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have hrD : refField σ0 r dispKey = lD := refField_of hR hRD
  rw [hrD] at hDl hfr
  have e1 : lng σ0 wX xAcctKey = acct := by simp [lng, fld, fieldsOf, hX, hXA]
  have e2 : fld σ0 d dTypeKey = .ref sty := by simp [fld, fieldsOf, hd, hdT]
  have e3 : lng σ0 d dCatKey = cd := by simp [lng, fld, fieldsOf, hd, hdC]
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd'
  obtain ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, -⟩ := hnd'
  have hDC : lD ≠ wC := by intro h; rw [h, hC] at hlD; cases hlD
  have hS : ∀ z ∈ [lD, wC], ∀ t, σ0.heap z ≠ some (.str t) := by
    intro z hz t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · rw [hlD] at ht; cases ht
    · rw [hC] at ht; cases ht
  have hrec : ∀ v ∈ xs, ∀ y, v = .ref y → y ∉ [lD, wC] := by
    intro v hv y hvy hm
    obtain ⟨y', fs, a, ts, tcs, c, hv', hy, -⟩ := hshC v hv
    rw [hvy] at hv'; cases hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [hlD] at hy; cases hy
    · exact hnC v hv hvy
  have hlC1 : σ.heap lC = some (.list .arrayList xs m) :=
    hfr.heap hlC (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                     exact ⟨fun h => n3 h.symm, fun h => by rw [h, hC] at hlC; cases hlC⟩)
  have hR1 : σ.heap r = some (.plain "Cbtrn02c$Result" fsR) :=
    hfr.heap hR (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                    exact ⟨fun h => (by rw [h, hlD] at hR; cases hR), fun h => (by rw [h, hC] at hR; simp at hR)⟩)
  have hlW1 : σ.heap lCW = some (.list .arrayList ws mW) :=
    hfr.heap hlW (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
                     exact ⟨fun h => n1 h.symm, fun h => by rw [h, hC] at hlW; cases hlW⟩)
  have hsty1 : σ.heap sty = some (.str tyS) :=
    hfr.heap hsty (fun hm => hS sty hm tyS hsty)
  have hsh1 : TcatShapes σ xs := tcatShapes_frame hfr hshC hrec hS
  have hneg41 : firstIdx (tcMatch σ (lng σ0 wX xAcctKey) (argText σ (.ref sty)) (lng σ0 d dCatKey))
      (listOf σ lC) < 0 := by
    have ea : argText σ (.ref sty) = argText σ0 (.ref sty) := by
      simp only [argText, strOfV, hsty1, hsty]
    rw [ea, listOf_of hlC1, firstIdx_tcMatch_frame hfr hshC hrec hS]
    unfold utIdx at hn
    rw [e2, listOf_of hlC] at hn
    exact hn
  have hkeep := Hide.intro (And.intro hDl (And.intro hsD (And.intro hsD0 hfr)))
  clear hDl hsD hfr h41
  have c42 := hc 42 (by omega) (by omega)
  have c43 := hc 43 (by omega) (by omega)
  have c44 := hc 44 (by omega) (by omega)
  have c45 := hc 45 (by omega) (by omega)
  have c46 := hc 46 (by omega) (by omega)
  have c47 := hc 47 (by omega) (by omega)
  have c48 := hc 48 (by omega) (by omega)
  have c49 := hc 49 (by omega) (by omega)
  have c50 := hc 50 (by omega) (by omega)
  clear hc
  unfold UtThinWPc
  jvc [utCallees, findTcatbalSig, findTcatbalSpecF, findTcatbalSpec, copyTcatSig, copyTcatSpecF,
    abendSig, abendSpec, Grows, narrow_long, narrow_cls, utVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_tseg21_pos (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : UtPre σ0 r d wX wC lC) (hp : 0 ≤ utIdx σ0 d wX lC)
    (h21 : ut21 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr σ)
    (hc : ∀ k, 51 ≤ k → k ≤ 58 → cuts.lookup k = none)
    (c59 : cuts.lookup 59 = some (fun fr' σ' => utVs 59 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr' σ' < utVs 21 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr σ)) :
    UtThinWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 21 fr σ := by
  obtain ⟨f5, f2, f8, f0, f6, hin, hst, hio, -, hpos⟩ := h21 r d wX wC lC rfl hP
  obtain ⟨f14, f9, fsA, hkeys, rfl⟩ := hpos hp
  have hP' := hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have hlo : listOf σ0 lC = xs := listOf_of hlC
  have hlt := firstIdx_lt (tcMatch σ0 (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
    (lng σ0 d dCatKey)) xs
  have hidxlt : (utIdx σ0 d wX lC).toNat < xs.length := by
    have hp2 := hp
    unfold utIdx at hp2 ⊢; rw [hlo] at hp2 ⊢; omega
  obtain ⟨y, fsy, b, hyx, hyh, hyall, hyb⟩ := hallX _ (List.getElem_mem hidxlt)
  obtain ⟨y', fs', a, ts, tcs, c, hv, hy', ha, ht, hts, hcd'⟩ := hshC _ (List.getElem_mem hidxlt)
  have hdC : d ≠ wC := by intro h; rw [h, hC] at hd; simp at hd
  have hXC : wX ≠ wC := by intro h; rw [h, hC] at hX; simp at hX
  have hRC : r ≠ wC := by intro h; rw [h, hC] at hR; simp at hR
  rw [hyx] at hv
  have ey : y' = y := (Value.ref.inj hv).symm
  subst ey
  have efs : fs' = fsy := by
    have e := hy'.symm.trans hyh
    simp only [Option.some.injEq, Obj.plain.injEq, true_and] at e
    exact e
  subst efs
  have hrec : utRec σ0 d wX lC = y' := by
    unfold utRec
    rw [hlo, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidxlt, Option.getD_some, hyx]
    rfl
  have hkeys' : ∀ k ∈ tcKeys, Fields.get fsA k = Fields.get fs' k := by
    intro k hk
    have := hkeys k hk
    unfold utRec at hrec
    rw [hrec, fieldsOf_of hyh] at this
    exact this
  have hfa : Fields.get fsA tcAcctKey = some (.long a) := by rw [hkeys' _ (by simp [tcKeys]), ha]
  have hft : Fields.get fsA tcTypeKey = some (.ref ts) := by rw [hkeys' _ (by simp [tcKeys]), ht]
  have hfc : Fields.get fsA tcCdKey = some (.long c) := by rw [hkeys' _ (by simp [tcKeys]), hcd']
  have hfb : Fields.get fsA tcBalKey = some (.long b) := by rw [hkeys' _ (by simp [tcKeys]), hyb]
  have ea : lng σ0 y' tcAcctKey = a := by simp [lng, fld, fieldsOf, hyh, ha]
  have et : fld σ0 y' tcTypeKey = .ref ts := by simp [fld, fieldsOf, hyh, ht]
  have ec : lng σ0 y' tcCdKey = c := by simp [lng, fld, fieldsOf, hyh, hcd']
  have eb : lng σ0 y' tcBalKey = b := by simp [lng, fld, fieldsOf, hyh, hyb]
  have e4 : lng σ0 d dAmtKey = amt := by simp [lng, fld, fieldsOf, hd, hdA]
  have hkeep := Hide.intro hkeys
  clear hkeys h21 hP' hpos
  have c51 := hc 51 (by omega) (by omega)
  have c52 := hc 52 (by omega) (by omega)
  have c53 := hc 53 (by omega) (by omega)
  have c54 := hc 54 (by omega) (by omega)
  have c55 := hc 55 (by omega) (by omega)
  have c56 := hc 56 (by omega) (by omega)
  have c57 := hc 57 (by omega) (by omega)
  have c58 := hc 58 (by omega) (by omega)
  clear hc
  unfold UtThinWPc
  jvc [utCallees, Grows, narrow_long, narrow_cls, utVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_tseg59 (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : UtPre σ0 r d wX wC lC) (hp : 0 ≤ utIdx σ0 d wX lC)
    (h59 : ut59 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr σ)
    (hc : ∀ k, 60 ≤ k → k ≤ 68 → cuts.lookup k = none) :
    UtThinWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 59 fr σ := by
  obtain ⟨-, f5, f2, f8, f0, f6, f3, f11, f4, f9, hin, hst, hio, fsA, hkeys, hwC, hfr⟩ :=
    h59 r d wX wC lC rfl hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have hlo : listOf σ0 lC = xs := listOf_of hlC
  have hp2 : 0 ≤ firstIdx (tcMatch σ0 (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
      (lng σ0 d dCatKey)) xs := by
    have := hp; unfold utIdx at this; rwa [hlo] at this
  have hlt := firstIdx_lt (tcMatch σ0 (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
    (lng σ0 d dCatKey)) xs
  have hidxlt : (firstIdx (tcMatch σ0 (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
      (lng σ0 d dCatKey)) xs).toNat < xs.length := by omega
  obtain ⟨y, fsy, b, hyx, hyh, hyall, hyb⟩ := hallX _ (List.getElem_mem hidxlt)
  have hm := firstIdx_get hp2 (by rw [List.getElem?_eq_getElem hidxlt, hyx])
  obtain ⟨y', fs', a, ts, tcs, c, hv, hy', ha, ht, hts, hcd'⟩ := hshC _ (List.getElem_mem hidxlt)
  rw [hyx] at hv
  have ey : y' = y := (Value.ref.inj hv).symm
  subst ey
  have efs : fs' = fsy := by
    have e := hy'.symm.trans hyh
    simp only [Option.some.injEq, Obj.plain.injEq, true_and] at e
    exact e
  subst efs
  obtain ⟨eA, eT, eC⟩ := tcMatch_key hy' ha ht hts hcd' hm
  have hrec : utRec σ0 d wX lC = y' := by
    unfold utRec utIdx
    rw [hlo, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidxlt, Option.getD_some, hyx]
    rfl
  have ea : lng σ0 y' tcAcctKey = a := by simp [lng, fld, fieldsOf, hy', ha]
  have et : fld σ0 y' tcTypeKey = .ref ts := by simp [fld, fieldsOf, hy', ht]
  have ec : lng σ0 y' tcCdKey = c := by simp [lng, fld, fieldsOf, hy', hcd']
  rw [hrec, ea, eA] at f3
  rw [hrec, et] at f11
  rw [hrec, ec, eC] at f4
  have hallA : AllSome tcKeys fsA :=
    allSome_of_same (fun k hk => by rw [hkeys k hk, hrec, fieldsOf_of hy']) hyall
  -- the objects the rest reads, in the cut state
  have hCs : ∀ z ∈ [wC], ∀ t, σ0.heap z ≠ some (.str t) := by
    intro z hz t ht'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rw [hz, hC] at ht'; cases ht'
  have hrecS : ∀ v ∈ xs, ∀ y, v = .ref y → y ∉ [wC] := by
    intro v hv y hvy hm'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
    subst hm'; exact hnC v hv hvy
  have hlC1 := hfr.heap hlC (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                                intro h; rw [h, hC] at hlC; cases hlC)
  have hR1 := hfr.heap hR (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                              intro h; rw [h, hC] at hR; simp at hR)
  have hlR1 := hfr.heap hlR (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                                intro h; rw [h, hC] at hlR; cases hlR)
  have hts1 := hfr.heap hts (fun hm' => hCs ts hm' tcs hts)
  have hsh1 : TcatShapes σ xs := tcatShapes_frame hfr hshC hrecS hCs
  have hidx59 : firstIdx (tcMatch σ (lng σ0 wX xAcctKey) (argText σ (.ref ts)) (lng σ0 d dCatKey))
      (listOf σ lC) = utIdx σ0 d wX lC := by
    have e1 : argText σ (.ref ts) = argText σ0 (.ref ts) := by
      simp only [argText, strOfV, hts1, hts]
    have e2 : argText σ0 (.ref ts) = argText σ0 (fld σ0 d dTypeKey) := by
      rw [← eT]; simp only [argText, strOfV, hts, Option.getD_some]
    rw [e1, e2, listOf_of hlC1, firstIdx_tcMatch_frame hfr hshC hrecS hCs]
    unfold utIdx
    rw [hlo]
  have hu1 : utIdx σ0 d wX lC < xs.length := by unfold utIdx; rw [hlo]; exact hlt
  clear ea ec eA eC et hrec hm
  have hkeep := Hide.intro (And.intro hkeys hfr)
  clear hkeys hfr h59
  have c60 := hc 60 (by omega) (by omega)
  have c61 := hc 61 (by omega) (by omega)
  have c62 := hc 62 (by omega) (by omega)
  have c63 := hc 63 (by omega) (by omega)
  have c64 := hc 64 (by omega) (by omega)
  have c65 := hc 65 (by omega) (by omega)
  have c66 := hc 66 (by omega) (by omega)
  have c67 := hc 67 (by omega) (by omega)
  have c68 := hc 68 (by omega) (by omega)
  clear hc
  unfold UtThinWPc
  jvc [utCallees, findTcatbalSig, findTcatbalSpecF, findTcatbalSpec, copyTcatSig, copyTcatSpecF,
    abendSig, abendSpec, Grows, narrow_long, narrow_cls, utVs]

end EquivLean.Modernize.Cbtrn02c.Java

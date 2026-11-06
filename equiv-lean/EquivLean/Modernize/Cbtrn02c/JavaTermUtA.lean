-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermUtA.lean (sha256 aa1c616275acf2a8...); only the module root renamed.
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
theorem ut_tentry_neg (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (hP : UtPre σ0 r d wX wC lC)
    (hn : utIdx σ0 d wX lC < 0)
    (c1 : cuts.lookup 1 = none) (c2 : cuts.lookup 2 = none) (c3 : cuts.lookup 3 = none)
    (c4 : cuts.lookup 4 = none) (c5 : cuts.lookup 5 = none) (c6 : cuts.lookup 6 = none)
    (c7 : cuts.lookup 7 = none) (c8 : cuts.lookup 8 = none) (c9 : cuts.lookup 9 = none)
    (c10 : cuts.lookup 10 = none) (c11 : cuts.lookup 11 = none) (c12 : cuts.lookup 12 = none)
    (c13 : cuts.lookup 13 = none) (c14 : cuts.lookup 14 = none) (c15 : cuts.lookup 15 = none)
    (c16 : cuts.lookup 16 = none) (c17 : cuts.lookup 17 = none)
    (c21 : cuts.lookup 21 = some (fun _ _ => True)) :
    UtThinWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 0
      (Frame.init true [.ref r, .ref d, .ref wX, .ref wC, .ref lC]) σ0 := by
  have hP' := hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have hn' : firstIdx (tcMatch σ0 acct (argText σ0 (.ref sty)) cd) xs < 0 := by
    have e1 : lng σ0 wX xAcctKey = acct := by simp [lng, fld, fieldsOf, hX, hXA]
    have e2 : fld σ0 d dTypeKey = .ref sty := by simp [fld, fieldsOf, hd, hdT]
    have e3 : lng σ0 d dCatKey = cd := by simp [lng, fld, fieldsOf, hd, hdC]
    have e4 : listOf σ0 lC = xs := listOf_of hlC
    unfold utIdx at hn
    rw [e1, e2, e3, e4] at hn
    exact hn
  have hlo : listOf σ0 lC = xs := listOf_of hlC
  unfold UtThinWPc
  jvc [utCallees, findTcatbalSig, findTcatbalSpecF, findTcatbalSpec,
    padNumSig, padNumSpec, Grows, narrow_long, narrow_cls, evalDynamic, concatRecipe,
    Native.valueOfArg, valueOfObj_eq, valueOfObjN_ref, Native.nObjStr, Native.primStr, JType.isRef,
    jstrLitT, utVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_tentry_pos (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (hP : UtPre σ0 r d wX wC lC)
    (hp : 0 ≤ utIdx σ0 d wX lC)
    (c1 : cuts.lookup 1 = none) (c2 : cuts.lookup 2 = none) (c3 : cuts.lookup 3 = none)
    (c4 : cuts.lookup 4 = none) (c5 : cuts.lookup 5 = none) (c6 : cuts.lookup 6 = none)
    (c7 : cuts.lookup 7 = none) (c8 : cuts.lookup 8 = none) (c9 : cuts.lookup 9 = none)
    (c10 : cuts.lookup 10 = none) (c18 : cuts.lookup 18 = none) (c19 : cuts.lookup 19 = none)
    (c20 : cuts.lookup 20 = none)
    (c21 : cuts.lookup 21 = some (fun _ _ => True)) :
    UtThinWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 0
      (Frame.init true [.ref r, .ref d, .ref wX, .ref wC, .ref lC]) σ0 := by
  have hP' := hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have e1 : lng σ0 wX xAcctKey = acct := by simp [lng, fld, fieldsOf, hX, hXA]
  have e2 : fld σ0 d dTypeKey = .ref sty := by simp [fld, fieldsOf, hd, hdT]
  have e3 : lng σ0 d dCatKey = cd := by simp [lng, fld, fieldsOf, hd, hdC]
  have hlo : listOf σ0 lC = xs := listOf_of hlC
  have hp' : 0 ≤ firstIdx (tcMatch σ0 acct (argText σ0 (.ref sty)) cd) xs := by
    unfold utIdx at hp
    rw [e1, e2, e3, hlo] at hp
    exact hp
  have hlt := firstIdx_lt (tcMatch σ0 acct (argText σ0 (.ref sty)) cd) xs
  have hidxlt : (firstIdx (tcMatch σ0 acct (argText σ0 (.ref sty)) cd) xs).toNat < xs.length := by
    omega
  obtain ⟨y, fsy, by0, hyx, hyh, hyall, hyb⟩ := hallX _ (List.getElem_mem hidxlt)
  have hget : xs[(firstIdx (tcMatch σ0 acct (argText σ0 (.ref sty)) cd) xs).toNat]? = some (.ref y) := by
    rw [List.getElem?_eq_getElem hidxlt, hyx]
  have hyC : y ≠ wC := by
    intro h; subst h
    exact hnC _ (List.getElem_mem hidxlt) hyx
  unfold UtThinWPc
  jvc [utCallees, findTcatbalSig, findTcatbalSpecF, findTcatbalSpec, assignTcatSig, assignTcatSpecF,
    Grows, narrow_long, narrow_cls, utVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem ut_tseg21_neg (r d wX wC lC : Addr) (σ0 : State) (cuts : Cuts) (fr : Frame) (σ : State)
    (hP : UtPre σ0 r d wX wC lC) (hn : utIdx σ0 d wX lC < 0)
    (h21 : ut21 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr σ)
    (hc : ∀ k, 22 ≤ k → k ≤ 40 → cuts.lookup k = none)
    (c41 : cuts.lookup 41 = some (fun fr' σ' => utVs 41 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr' σ' < utVs 21 [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 fr σ)) :
    UtThinWPc [.ref r, .ref d, .ref wX, .ref wC, .ref lC] σ0 cuts 21 fr σ := by
  obtain ⟨f5, f2, f8, f0, f6, hin, hst, hio, hneg, -⟩ := h21 r d wX wC lC rfl hP
  obtain ⟨f14, sD, m1, hDl, hsD, hsD0, hfr⟩ := hneg hn
  have hP' := hP
  obtain ⟨fsR, fsd, fsX, fsC, lD, lCW, lCR, sty, tyS, cd, amt, acct, xs, ds, ws, rs, m, mD, mW, mR,
    hR, hRD, hRW, hRR, hd, hdT, hsty, htyl, hdC, hdA, hX, hXA, hC, hallC, hlC, hshC, hlenC, hnC,
    hallX, hlD, hlW, hlR, hnd, hacct, hcd, i1, i2⟩ := hP
  have hrD : refField σ0 r dispKey = lD := refField_of hR hRD
  rw [hrD] at hDl hfr
  have hlist : ∀ {z c fs}, σ0.heap z = some (.plain c fs) → z ∉ [lD] := by
    intro z c fs hz hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm; rw [hlD] at hz; cases hz
  have hd1 := hfr.heap hd (hlist hd)
  have hX1 := hfr.heap hX (hlist hX)
  have hC1 := hfr.heap hC (hlist hC)
  have hsD1 : σ.heap sD = some (.str (noCatJ (lng σ0 wX xAcctKey) (argText σ0 (fld σ0 d dTypeKey))
      (lng σ0 d dCatKey))) := hsD
  have hkeep := Hide.intro (And.intro hDl (And.intro hsD1 (And.intro hfr hsD0)))
  have e1 : lng σ0 wX xAcctKey = acct := by simp [lng, fld, fieldsOf, hX, hXA]
  have e2 : fld σ0 d dTypeKey = .ref sty := by simp [fld, fieldsOf, hd, hdT]
  have e3 : lng σ0 d dCatKey = cd := by simp [lng, fld, fieldsOf, hd, hdC]
  have e4 : lng σ0 d dAmtKey = amt := by simp [lng, fld, fieldsOf, hd, hdA]
  have e5 : fieldsOf σ0 wC = fsC := fieldsOf_of hC
  obtain ⟨q0, pq0⟩ := Option.isSome_iff_exists.1 (hallC tcAcctKey (by simp [tcKeys]))
  obtain ⟨q1, pq1⟩ := Option.isSome_iff_exists.1 (hallC tcTypeKey (by simp [tcKeys]))
  obtain ⟨q2, pq2⟩ := Option.isSome_iff_exists.1 (hallC tcCdKey (by simp [tcKeys]))
  obtain ⟨q3, pq3⟩ := Option.isSome_iff_exists.1 (hallC tcBalKey (by simp [tcKeys]))
  have hsDC : sD ≠ wC := by intro h; rw [h, hC1] at hsD1; cases hsD1
  have hDC : lD ≠ wC := by intro h; rw [h, hC] at hlD; cases hlD
  have hsDlt : sD < σ.next := State.lt_next_of_heap hsD1
  have hlDlt : lD < σ.next := State.lt_next_of_heap hDl
  clear hDl hsD hfr hsD1 h21 hP' hneg
  have c22 := hc 22 (by omega) (by omega)
  have c23 := hc 23 (by omega) (by omega)
  have c24 := hc 24 (by omega) (by omega)
  have c25 := hc 25 (by omega) (by omega)
  have c26 := hc 26 (by omega) (by omega)
  have c27 := hc 27 (by omega) (by omega)
  have c28 := hc 28 (by omega) (by omega)
  have c29 := hc 29 (by omega) (by omega)
  have c30 := hc 30 (by omega) (by omega)
  have c31 := hc 31 (by omega) (by omega)
  have c32 := hc 32 (by omega) (by omega)
  have c33 := hc 33 (by omega) (by omega)
  have c34 := hc 34 (by omega) (by omega)
  have c35 := hc 35 (by omega) (by omega)
  have c36 := hc 36 (by omega) (by omega)
  have c37 := hc 37 (by omega) (by omega)
  have c38 := hc 38 (by omega) (by omega)
  have c39 := hc 39 (by omega) (by omega)
  have c40 := hc 40 (by omega) (by omega)
  clear hc
  unfold UtThinWPc
  jvc [utCallees, spacesSig, spacesSpec, Grows, narrow_long, narrow_cls, utVs]

end EquivLean.Modernize.Cbtrn02c.Java

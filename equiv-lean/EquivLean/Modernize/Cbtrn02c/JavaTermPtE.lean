-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermPtE.lean (sha256 8a20d8556ca7e249...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5c
import EquivLean.Modernize.Cbtrn02c.JavaTermDefsH

/-!
# CBTRN02C → Java, termination: thin twins of `JavaRunM5c`

The statements and preambles of the originals over the thin cut list (each cut assertion
a variant comparison, the entry's `True`), calls by `callWPThin` (`callWPT` without the
callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem pt_tentry (p : PG) (σ0 : State) (cuts : Cuts) (hP : PtFacts σ0 p)
    (hcut : ∀ k, 1 ≤ k → k ≤ 35 → cuts.lookup k = none)
    (c36 : cuts.lookup 36 = some (fun _ _ => True)) :
    PtThinWPc p.args σ0 cuts 0 (Frame.init true p.args) σ0 := by
  have hP' := Hide.intro hP
  obtain ⟨hW, hMV, hd, htv, hx, hxv, ha, hfa, hcs, hcd, hlen, hI, hAd⟩ := hP
  obtain ⟨hR, hD, hT, hRj, hCW, hAR, hCR, hA, hC, hK, hwX, hwA, hwC, hwT, hfC, hfT, hnd⟩ := hW
  obtain ⟨fsT, hto, hkT⟩ := hwT
  obtain ⟨fsF, svF, htoF, hfF, hsvF⟩ := hfT
  obtain ⟨u0, p0⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranId") (by decide))
  obtain ⟨u1, p1⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranTypeCd") (by decide))
  obtain ⟨u2, p2⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranCatCd") (by decide))
  obtain ⟨u3, p3⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranSource") (by decide))
  obtain ⟨u4, p4⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranDesc") (by decide))
  obtain ⟨u5, p5⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranAmt") (by decide))
  obtain ⟨u6, p6⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranMerchantId") (by decide))
  obtain ⟨u7, p7⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranMerchantName") (by decide))
  obtain ⟨u8, p8⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranMerchantCity") (by decide))
  obtain ⟨u9, p9⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranMerchantZip") (by decide))
  obtain ⟨u10, p10⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranCardNum") (by decide))
  obtain ⟨u11, p11⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranOrigTs") (by decide))
  obtain ⟨u12, p12⟩ := Option.isSome_iff_exists.1 (hkT ("Cbtrn02c$TranRecord", "tranProcTs") (by decide))
  obtain ⟨⟨d', fsd, s0, s1, s3, s4, s7, s8, s9, s10, s11, s12, s13, hde, hdo, g0, t0, g1, t1, g2, g3, t3,
    g4, t4, g5, g6, g7, t7, g8, t8, g9, t9, g10, t10, g11, t11, g12, t12, g13, t13⟩, -⟩ :=
    dalobj_of_rec hd htv
  have ed : d' = p.d := (Value.ref.inj hde).symm
  subst ed
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
    b20, hclk⟩ := clk21 hcd.1
  obtain ⟨csA, hcsA, hcsH⟩ := hcs
  have ecs : csA = p.cs := (Value.ref.inj hcsA).symm
  subst ecs
  rw [hclk] at hcsH
  simp only [cp037Str, List.map_cons, List.map_nil] at hcsH
  have hdT : p.d ≠ p.A.wT := by intro h; rw [h, hto] at hdo; simp at hdo
  have hcT : p.cs ≠ p.A.wT := by intro h; rw [h, hto] at hcsH; cases hcsH
  obtain ⟨i1, -, -, -, -, -, -, i8⟩ := hI
  have c1 := hcut 1 (by omega) (by omega)
  have c2 := hcut 2 (by omega) (by omega)
  have c3 := hcut 3 (by omega) (by omega)
  have c4 := hcut 4 (by omega) (by omega)
  have c5 := hcut 5 (by omega) (by omega)
  have c6 := hcut 6 (by omega) (by omega)
  have c7 := hcut 7 (by omega) (by omega)
  have c8 := hcut 8 (by omega) (by omega)
  have c9 := hcut 9 (by omega) (by omega)
  have c10 := hcut 10 (by omega) (by omega)
  have c11 := hcut 11 (by omega) (by omega)
  have c12 := hcut 12 (by omega) (by omega)
  have c13 := hcut 13 (by omega) (by omega)
  have c14 := hcut 14 (by omega) (by omega)
  have c15 := hcut 15 (by omega) (by omega)
  have c16 := hcut 16 (by omega) (by omega)
  have c17 := hcut 17 (by omega) (by omega)
  have c18 := hcut 18 (by omega) (by omega)
  have c19 := hcut 19 (by omega) (by omega)
  have c20 := hcut 20 (by omega) (by omega)
  have c21 := hcut 21 (by omega) (by omega)
  have c22 := hcut 22 (by omega) (by omega)
  have c23 := hcut 23 (by omega) (by omega)
  have c24 := hcut 24 (by omega) (by omega)
  have c25 := hcut 25 (by omega) (by omega)
  have c26 := hcut 26 (by omega) (by omega)
  have c27 := hcut 27 (by omega) (by omega)
  have c28 := hcut 28 (by omega) (by omega)
  have c29 := hcut 29 (by omega) (by omega)
  have c30 := hcut 30 (by omega) (by omega)
  have c31 := hcut 31 (by omega) (by omega)
  have c32 := hcut 32 (by omega) (by omega)
  have c33 := hcut 33 (by omega) (by omega)
  have c34 := hcut 34 (by omega) (by omega)
  have c35 := hcut 35 (by omega) (by omega)
  have efF : fsF = fsT := by
    have e := htoF.symm.trans hto
    simp only [Option.some.injEq, Obj.plain.injEq, true_and] at e
    exact e
  subst efF
  have hkeep := Hide.intro (And.intro hdo (And.intro hcsH (And.intro hfF hsvF)))
  clear hcut hR hD hT hRj hCW hAR hCR hA hC hK hwX hwA hwC hfC hnd hMV hx hxv ha hfa hlen hd hAd
  unfold PtThinWPc
  jvc [ptCallees, db2TimestampSig, db2TimestampSpecF, db2TimestampSpec, Grows, narrow_long, narrow_cls,
    PG.args, ptVs]

end EquivLean.Modernize.Cbtrn02c.Java

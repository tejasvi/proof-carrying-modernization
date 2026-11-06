import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5b
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM5p
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunSigs
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunMF
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunWA
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunTW
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunTac
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunM2xs

/-!
# CBTRN02C → Java: `postTransaction` satisfies its contract (entry to cut point 36)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

def ptCallees : Contracts :=
  [(db2TimestampSig, db2TimestampSpecF), (updateTcatbalSig, updateTcatbalSpec),
   (updateAccountSig, updateAccountSpec), (writeTransactionSig, writeTransactionSpecX)]

abbrev ptBody := Gen.Cbtrn02c.«postTransaction(Cbtrn02c$Result,Cbtrn02c$DalytranRecord,java.lang.String,Cbtrn02c$CardXrefRecord,Cbtrn02c$AccountRecord,Cbtrn02c$TranCatBalRecord,Cbtrn02c$TranRecord,Cbtrn02c$AccountRecord[],java.util.List,java.util.List)»

/-- The postcondition of `postTransaction`, folded. -/
def ptPost (args : List Value) (σ0 : State) : Outcome → Prop := postTransactionSpec.post args σ0

attribute [irreducible] ptPost

/-- Symbolic execution of `postTransaction`'s body from `pc` against the cut list `cuts`. -/
def PtWPc (args : List Value) (σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog ptCallees.env 0) ptBody cuts (ptPost args σ0) 80 pc fr σ

attribute [irreducible] PtWPc

/-- `chain_simp` without the closing `rfl` (whose defeq check can run away on big texts). -/
macro "chain_simp0" : tactic => `(tactic| (
  try simp only [State.next_alloc, State.next_setObj] at *
  simp (config := { decide := true }) (disch := jomega) only [State.heap_alloc, State.heap_setObj,
    State.next_alloc, State.next_setObj, ite_true, ite_false, reduceIte, addr_eq_false, addr_lt_true,
    jstrLitT, State.initOf_alloc, State.initOf_setObj, List.cons_append, List.nil_append,
    List.append_assoc, Frame.get_setLocal, *]))

theorem clk21 {clk : List UInt8} (h : clk.length = 21) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 : UInt8,
      clk = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
        b20] := by
  match clk, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20], _ =>
    exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20,
      rfl⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 20000000 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem pt_entry (p : PG) (σ0 : State) (cuts : Cuts) (hP : PtFacts σ0 p)
    (hcut : ∀ k, 1 ≤ k → k ≤ 35 → cuts.lookup k = none)
    (c36 : cuts.lookup 36 = some (Pt36 p.args σ0)) :
    PtWPc p.args σ0 cuts 0 (Frame.init true p.args) σ0 := by
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
  unfold PtWPc
  jvc [ptCallees, db2TimestampSig, db2TimestampSpecF, db2TimestampSpec, Grows, narrow_long, narrow_cls,
    PG.args]
  obtain ⟨hdo', hcsH', hfF', hsvF'⟩ := Hide.elim hkeep
  intro p' hargs hP2
  simp only [PG.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨er, ed, ecs, ewX, ewA, ewC, ewT, eaD, elC, elK⟩ := hargs
  replace er := er.symm
  replace ed := ed.symm
  replace ecs := ecs.symm
  replace ewX := ewX.symm
  replace ewA := ewA.symm
  replace ewC := ewC.symm
  replace ewT := ewT.symm
  replace eaD := eaD.symm
  replace elC := elC.symm
  replace elK := elK.symm
  obtain ⟨hW2, -, hd2, htv2, -, -, -, -, hcs2, -, -, -, -⟩ := hP2
  -- the clock is `p.clk`
  have hclk2 : p'.clk = p.clk := by
    obtain ⟨y, hy, hyh⟩ := hcs2
    have ey : y = p.cs := by rw [← ecs]; exact (Value.ref.inj hy).symm
    subst ey
    rw [hcsH'] at hyh
    simp only [Option.some.injEq, Obj.str.injEq] at hyh
    rw [hclk]
    apply cp037Str_inj
    rw [← hyh]
    simp only [cp037Str, List.map_cons, List.map_nil]
  rw [ed] at hd2
  rw [hclk2]
  obtain ⟨sF, hsFe, hsF⟩ := hsvF'
  rw [hsFe] at hfF'
  have hsFT : sF ≠ p.A.wT := by intro h; rw [h, htoF] at hsF; cases hsF
  have hwTlt : p.A.wT < σ0.next := State.lt_next_of_heap htoF
  have hsFlt : sF < σ0.next := State.lt_next_of_heap hsF
  have hdlt : p.d < σ0.next := State.lt_next_of_heap hdo'
  have hdb : db2J [cp037Unit b0, cp037Unit b1, cp037Unit b2, cp037Unit b3, cp037Unit b4, cp037Unit b5,
      cp037Unit b6, cp037Unit b7, cp037Unit b8, cp037Unit b9, cp037Unit b10, cp037Unit b11,
      cp037Unit b12, cp037Unit b13, cp037Unit b14, cp037Unit b15, cp037Unit b16, cp037Unit b17,
      cp037Unit b18, cp037Unit b19, cp037Unit b20] = cp037Str (CardDemo.Cbtrn02c.db2ts p.clk) := by
    rw [hclk, ← db2J_cp037]
    simp only [cp037Str, List.map_cons, List.map_nil]
  have hwT : w ≠ p.A.wT := by
    intro h
    rename State.heap _ w = some (Obj.str _) => hwS
    rw [h] at hwS
    simp (disch := jomega) only [*, eq_self_iff_true, ite_true, reduceIte] at hwS <;> cases hwS
  refine ⟨⟨by frame_simp [er], by frame_simp [ed], by frame_simp [ewX], by frame_simp [ewA],
      by frame_simp [ewC], by frame_simp [ewT], by frame_simp [eaD], by frame_simp [elC],
      by frame_simp [elK]⟩, ?_, ?_, by cls_simp; assumption, by cls_simp; assumption, ?_⟩
  · refine W_setT hW2 ?_ ⟨_, by chain_simp, by (repeat apply allSome_set); exact hkT⟩
      ⟨_, .ref sF, by chain_simp, by fget_simp; exact hfF', sF, rfl, by chain_simp⟩
    refine ⟨by simp only [State.next_setObj] at *; jomega, fun z hz hzS => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, ewT] at hzS
    chain_simp
  · rw [ewT]
    refine ⟨by simp only [State.next_setObj] at *; jomega, fun z hz hzS => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hzS
    chain_simp
  · rw [ewT]
    refine tranws_rec (jrecAt_frame (S := [p.A.wT]) hd2 ?_ ?_ ?_) htv2 (by chain_simp) (by chain_simp)
      (by fget_simp; rw [g0]) (by fget_simp; rw [g1]) (by fget_simp; rw [g2]) (by fget_simp; rw [g3])
      (by fget_simp; rw [g4]) (by fget_simp; rw [g5]) (by fget_simp; rw [g6]) (by fget_simp; rw [g7])
      (by fget_simp; rw [g8]) (by fget_simp; rw [g9]) (by fget_simp; rw [g10]) (by fget_simp; rw [g11])
      (by fget_simp; try rfl) (by chain_simp0; simp only [argText, strOfV]; chain_simp0; simp only [Option.getD_some]; rw [hdb, hclk])
      (by fget_simp; exact hfF') ⟨sF, rfl, by chain_simp⟩
    · refine ⟨by simp only [State.next_setObj] at *; jomega, fun z hz hzS => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzS
      chain_simp
    · intro z hz t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rw [hz, htoF] at ht; cases ht
    · intro x hx hxS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hxS
      cases hx
      exact hdT hxS

end EquivLean.Modernize.Cbtrn02c.Java

import EquivLean.Modernize.Cbstm03a.Java.Run2.Steps2

/-! # CBSTM03A → Java `run`, the load loop: statements 100–110 at the last record (`seqRead` "10", to 113) -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space GrowsK Kept keeps_trans grows_split
  fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

attribute [-jsimp] List.take_succ
attribute [local irreducible] SlotsAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem seg100E (g : RunG) (args : List Value) (σ0 : State) (p : LP)
    (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct) (o3 : p.trct < p.st1)
    (hxl : p.xs.length = g.R1.length) (hxl3 : p.xs.length < 2147483648) (hlast : p.k + 1 = g.R1.length)
    (hk1i : (BitVec.ofNat 32 (p.k + 1)).toInt = (p.k + 1 : Int)) (hfin : p.fin) :
    ∀ fr' σ', A100 p fr' σ' → segWP g args σ0 (cuts113 g args σ0 p) 40 100 fr' σ' := by
  intro fr' σ' h
  obtain ⟨⟨hfk, hI0, h11, ht1, h16, h24, h1, hst1, hyh, vsm, hmem⟩, ⟨hsl, htr, h18, h17⟩, xc, h32, hxc⟩ := h
  unfold segWP
  jvc [runCallees, cuts113, cuts0, runInv, runSpecG, trnxTextSig, xrefTextSig,
    custTextSig, acctTextSig, spacesSig, fixSig, repeatSig, seqReadSig, setTrctSig, getTrctSig, cardOffSig,
    tranOffSig, memWriteSig, memReadSig, abendSig, createStatementSig, writeTransSig, stmtSig, htmlSig,
    ebcCompareSig, decodeZonedSig, trunc11Sig, fmtZSig, seqReadSpec, fixSpecI, abendSpec, seqCode, seqStArr,
    keeps_split, grows_split, StrOk, argText, ite_nat_ne, fixStr_length]
  all_goals
    obtain ⟨K0, I0', S0', L0⟩ := Kept.elim hfk
    have hA : ArrOnly (fun y => y = p.st1) σ' := fun y (hy0 : y = p.st1) => by subst hy0; exact ⟨_, _, hst1⟩
    unfold A113 FrameK TabAt
    exact ⟨Kept.intro ⟨keeps_trans K0 (by keeps_peel), left.trans I0', right.trans S0',
        sameLocs_step L0 (fun i a b _ _ _ _ _ _ _ _ _ => by simp only [Frame.get_setLocal, a, b, if_false])⟩,
      (initOf_of_inits left _).trans hI0, by simp [Frame.get_setLocal, h16], by simp [Frame.get_setLocal, h24],
      ⟨slotsAt_keeps (by keeps_peel) hA hsl (Nat.ne_of_lt (Nat.lt_trans o2 o3)),
      heap_keeps' (A := fun y => y = p.st1) (by keeps_peel) htr (Nat.ne_of_lt o3),
      by simp [Frame.get_setLocal, h18], by simp [Frame.get_setLocal, h17]⟩, hfin⟩

end EquivLean.Modernize.Cbstm03a.Java.Seg2

#print axioms EquivLean.Modernize.Cbstm03a.Java.Seg2.seg100E

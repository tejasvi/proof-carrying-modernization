import EquivLean.Modernize.Cbstm03a.Java.Run2.Steps2

/-! # CBSTM03A → Java `run`, the load loop: statements 113–116 (the last card's count stored, the cross-reference
loop's state) -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space GrowsK Kept keeps_trans grows_split
  fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

attribute [-jsimp] List.take_succ
attribute [local irreducible] SlotsAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem seg4 (g : RunG) (args : List Value) (σ0 : State) (p : LP) (res ld ls lh t2 t3k t3 t4 : Addr)
    (hko : Kept (Orig g σ0 p res ld ls lh t2 t3k t3 t4))
    (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct) (o3 : p.trct < p.st1) (hF : Kept (p.fin → p.k + 1 = g.R1.length)) :
    ∀ fr' σ', A113 p fr' σ' → segWP g args σ0 (cuts0 g args σ0) 40 113 fr' σ' := by
  intro fr' σ' h
  obtain ⟨hfk, hI0, h16, h24, ⟨hsl, htr, h18, h17⟩, hfin⟩ := h
  have htl : p.L.trct.length = 51 :=
    (ldStep_trct_length p.s p.r).trans (Kept.elim hko).2.2.2.2.2.2.2.2.2.1
  unfold segWP
  jvc [runCallees, cuts0, runInv, runSpecG, trnxTextSig, xrefTextSig,
    custTextSig, acctTextSig, spacesSig, fixSig, repeatSig, seqReadSig, setTrctSig, getTrctSig, cardOffSig,
    tranOffSig, memWriteSig, memReadSig, abendSig, createStatementSig, writeTransSig, stmtSig, htmlSig,
    ebcCompareSig, decodeZonedSig, trunc11Sig, fmtZSig, setTrctSpec, keeps_split, ite_nat_ne]
  all_goals
    rename_i σ2 a4 a3 a2 a1 a0 f0 hf0
    obtain ⟨K0, I0', S0', L0⟩ := Kept.elim hfk
    have hA : ArrOnly (fun y => y = p.trct) σ' := fun y (hy0 : y = p.trct) => by subst hy0; exact ⟨_, _, htr⟩
    refine close117' (Kept.elim hko) o2 o3 (Kept.elim hF hfin) (keeps_trans K0 (by keeps_peel)) (left.trans I0')
      (right.trans S0')
      (sameLocs_step L0 (fun i _ b _ d e _ _ _ _ _ _ => by simp only [Frame.get_setLocal, b, d, e, if_false]))
      (slotsAt_keeps (by keeps_peel) hA hsl (Nat.ne_of_lt o2)) ?_ (by simp [Frame.get_setLocal]) ?_ K0.1
      (by simp [Frame.get_setLocal]) (by simp [Frame.get_setLocal]) (by simp [Frame.get_setLocal, h18, ldFin])
    · rw [State.heap_alloc_of_lt (Nat.lt_of_lt_of_le (State.lt_next_of_heap htr) a2)]
      exact a4
    · rw [State.heap_alloc, if_pos a0.symm]
      rfl

end EquivLean.Modernize.Cbstm03a.Java.Seg2

#print axioms EquivLean.Modernize.Cbstm03a.Java.Seg2.seg4

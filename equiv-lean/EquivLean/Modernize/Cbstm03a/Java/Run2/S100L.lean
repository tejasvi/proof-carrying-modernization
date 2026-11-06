import EquivLean.Modernize.Cbstm03a.Java.Run2.Orig

/-! # CBSTM03A → Java `run`, the load loop: statements 100–108 when a record is left (`seqRead` "00", the next
record read and cut, back at the loop head) -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space GrowsK Kept keeps_trans grows_split
  fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

attribute [-jsimp] List.take_succ
attribute [local irreducible] SlotsAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem seg100L (g : RunG) (args : List Value) (σ0 : State) (p : LP) (res ld ls lh t2 t3k t3 t4 : Addr)
    (hko : Kept (Orig g σ0 p res ld ls lh t2 t3k t3 t4))
    (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct) (o3 : p.trct < p.st1)
    (hxl : p.xs.length = g.R1.length) (hxl2 : g.R1.length < 2147483648) (hy : p.xs[p.k + 1]? = some (.ref p.y))
    (hyl : p.ty.length = 350) (hk1 : p.k + 1 < g.R1.length)
    (hxl3 : p.xs.length < 2147483648)
    (hk1i : (BitVec.ofNat 32 (p.k + 1)).toInt = (p.k + 1 : Int))
    (hk1n : (BitVec.ofNat 32 (p.k + 1)).toNat = p.k + 1)
    (hty : Kept (p.ty = g.T1.getD (p.k + 1) [])) :
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
    rename_i σ1 w0 a11 a10 a9 a8 a7 a6 a5 r5 f4 f3 f2 f1 hf2 hf1 c1 c0 hr0 σ3 a4 a3 a2 a1 a0 f0 hf0
    obtain ⟨K0, I0', S0', L0⟩ := Kept.elim hfk
    have hk8 := keepsK_elim a8
    have hyne : p.y ≠ p.st1 := fun e => by rw [e, hst1] at hyh; cases hyh
    have hy1 : σ1.heap p.y = some (.str p.ty) := heap_keeps' hk8 hyh hyne
    obtain ⟨hlt, hy'⟩ := List.getElem?_eq_some_iff.mp hy
    have hyn : p.y ≠ σ1.next := Nat.ne_of_lt (Nat.lt_of_lt_of_le (State.lt_next_of_heap hyh) hk8.1)
    simp only [hy', if_neg hyn, hy1, Option.getD_some] at a3 ⊢
    have hcnd : (BitVec.ofNat 32 (p.k + 1)).toInt < (p.xs.length : Int) := by
      rw [hk1i, hxl]; exact_mod_cast hk1
    simp only [hcnd, if_true] at a9
    have hA : ArrOnly (fun y => y = p.st1) σ' := fun y (hy0 : y = p.st1) => by subst hy0; exact ⟨_, _, hst1⟩
    refine close80' (Kept.elim hko) o2 o3 (keeps_trans K0 (by keeps_peel)) (left.trans I0') (right.trans S0')
      (sameLocs_step L0 (fun i n1 n2 n3 _ _ _ _ _ _ _ _ => by simp only [Frame.get_setLocal, n1, n2, n3, if_false]))
      (slotsAt_keeps (by keeps_peel) hA hsl (Nat.ne_of_lt (Nat.lt_trans o2 o3)))
      (heap_keeps' (A := fun y => y = p.st1) (by keeps_peel) htr (Nat.ne_of_lt o3)) ?_ hk1 ?_
      ⟨xc, by simp [Frame.get_setLocal, h32], by
        rw [ldStep_save]; exact str_keeps (A := fun y => y = p.st1) (by keeps_peel) hA hxc⟩
      (by simp [Frame.get_setLocal, h18]) (by simp [Frame.get_setLocal, h17])
    · rw [← bv32_succ]
      exact heap_keeps' (A := fun _ => False) (by keeps_peel) a9 id
    · refine ⟨σ3.next, by rw [Frame.get_setLocal, if_pos rfl], ?_⟩
      rw [State.heap_alloc, if_pos rfl, R1_getD g (by rw [T1_length, ← R1_length]; exact hk1), ← Kept.elim hty]
      simp [sub]

end EquivLean.Modernize.Cbstm03a.Java.Seg2

#print axioms EquivLean.Modernize.Cbstm03a.Java.Seg2.seg100L

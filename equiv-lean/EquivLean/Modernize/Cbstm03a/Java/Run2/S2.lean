import EquivLean.Modernize.Cbstm03a.Java.Run2.Steps2

/-! # CBSTM03A → Java `run`, the load loop: statements 88–91 (a new card: `setTrct`, the counters) -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space GrowsK Kept keeps_trans grows_split
  fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

attribute [-jsimp] List.take_succ
attribute [local irreducible] SlotsAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem seg2 (g : RunG) (args : List Value) (σ0 : State) (p : LP)
    (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct) (o3 : p.trct < p.st1) (hne : Kept (¬ p.s.save = sub p.r 0 16)) :
    ∀ fr' σ', A88 p fr' σ' → segWP g args σ0 (cuts92 g args σ0 p) 40 88 fr' σ' := by
  intro fr' σ' h
  obtain ⟨⟨hfk, hI0, h11, ht1, h16, h24, h1, hst1, hyh, vsm, hmem⟩, ⟨xc, xi, xr, h36, hxc, h34, hxi, h33, hxr⟩,
    ⟨hsl, htr, h18, h17⟩, htl⟩ := h
  unfold segWP
  jvc [runCallees, cuts92, cuts95, cuts98, cuts100, cuts113, cuts0, runInv, runSpecG, trnxTextSig, xrefTextSig,
    custTextSig, acctTextSig, spacesSig, fixSig, repeatSig, seqReadSig, setTrctSig, getTrctSig, cardOffSig,
    tranOffSig, memWriteSig, memReadSig, abendSig, createStatementSig, writeTransSig, stmtSig, htmlSig,
    ebcCompareSig, decodeZonedSig, trunc11Sig, fmtZSig, setTrctSpec, keeps_split, ite_nat_ne]
  all_goals
    rename_i σ2 a4 a3 a2 a1 a0 f0 hf0
    obtain ⟨c1, c2, c3⟩ := ldStep_diff_cr (Kept.elim hne)
    have key := trctStep (fr2 := ((fr'.setLocal 18 (.long (p.s.cr + 1#64))).setLocal 18
        (.long (BitVec.srem (p.s.cr + 1#64) 10000#64))).setLocal 17 (.long 1#64)) o0 o2 o3
      ⟨hfk, hI0, h11, ht1, h16, h24, h1, hst1, hyh, vsm, hmem⟩
      ⟨xc, xi, xr, h36, hxc, h34, hxi, h33, hxr⟩ hsl htr a3 left right
      (fun i n1 n2 => by simp only [Frame.get_setLocal, n1, n2, if_false])
    unfold A92 TabAt
    exact ⟨key.1, key.2.1, key.2.2, by rw [c3]; exact a4, by rw [c1]; simp [Frame.get_setLocal],
      by rw [c2]; simp [Frame.get_setLocal]⟩

end EquivLean.Modernize.Cbstm03a.Java.Seg2

#print axioms EquivLean.Modernize.Cbstm03a.Java.Seg2.seg2

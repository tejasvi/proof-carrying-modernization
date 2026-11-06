import EquivLean.Modernize.Cbstm03a.Java.Run2.Steps
import EquivLean.Modernize.Cbstm03a.Java.Run2.Bounds

/-! # CBSTM03A → Java `run`, the load loop: statements 98–99 (the transaction rest written, `saveCard`) -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space GrowsK Kept)

namespace EquivLean.Modernize.Cbstm03a.Java.Seg2

attribute [-jsimp] List.take_succ
attribute [local irreducible] SlotsAt

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem seg98 (g : RunG) (args : List Value) (σ0 : State) (p : LP)
    (o0 : p.t1 < p.mem) (o2 : p.mem < p.trct) (o3 : p.trct < p.st1)
    (hl2 : (sub p.r 32 350).length = 318) (hoff : -2147483648 < (tranOffJ p.L.cr p.L.tr + 16).toInt)
    (hc0 : 0 ≤ p.L.cr.toInt) (hc1 : p.L.cr.toInt < 10000) (ht0 : 0 ≤ p.L.tr.toInt) (ht1 : p.L.tr.toInt < 10000) (hT0 : -3674 ≤ (tranOffJ p.L.cr p.L.tr).toInt) (hT1 : (tranOffJ p.L.cr p.L.tr).toInt < 100000000) :
    ∀ fr' σ', A98 p fr' σ' → segWP g args σ0 (cuts100 g args σ0 p) 40 98 fr' σ' := by
  intro fr' σ' h
  obtain ⟨⟨hfk, hI0, h11, ht1, h16, h24, h1, hst1, hy, vsm, hmem⟩, ⟨xc, xi, xr, h36, hxc, h34, hxi, h33, hxr⟩,
    ⟨hsl, htr, h18, h17⟩, h19⟩ := h
  unfold segWP
  jvc [runCallees, cuts100, cuts113, cuts0, runInv, runSpecG, trnxTextSig, xrefTextSig,
    custTextSig, acctTextSig, spacesSig, fixSig, repeatSig, seqReadSig, setTrctSig, getTrctSig, cardOffSig,
    tranOffSig, memWriteSig, memReadSig, abendSig, createStatementSig, writeTransSig, stmtSig, htmlSig,
    ebcCompareSig, decodeZonedSig, trunc11Sig, fmtZSig, cardOffSpec, tranOffSpec, memWriteSpec, keeps_split,
    ite_nat_ne]
  all_goals
    first
      | exact hoff
      | exact bm_lb (by omega) (by omega)
      | exact close100 o0 o2 o3 ⟨hfk, hI0, h11, ht1, h16, h24, h1, hst1, hy, vsm, hmem⟩
          ⟨xc, xi, xr, h36, hxc, h34, hxi, h33, hxr⟩ htr h18 h17 ‹KeepsK _ _ _› ‹_› ‹_› ‹SlotsAt _ _ _›
          (fun i _ hi2 => by simp only [Frame.get_setLocal, if_neg hi2])
          (by rw [Frame.get_setLocal, if_pos rfl]) hxc

end EquivLean.Modernize.Cbstm03a.Java.Seg2

#print axioms EquivLean.Modernize.Cbstm03a.Java.Seg2.seg98

import EquivLean.Modernize.Cbact04c.JavaRunResInit
import EquivLean.Modernize.Cbact04c.JavaRunSpecEqs

/-!
# CBACT04C → Java, `run`: statements 63–69 (the transaction object's other strings, its constructor)
-/

open Jimple EquivLean.Cobol.Rec


namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_seg63 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (h : JI63 g g.args σ0 fr σ)
    (c64 : cuts.lookup 64 = none) (c65 : cuts.lookup 65 = none) (c66 : cuts.lookup 66 = none)
    (c67 : cuts.lookup 67 = none) (c68 : cuts.lookup 68 = none) (c69 : cuts.lookup 69 = none)
    (c70 : cuts.lookup 70 = some (JI70 g g.args σ0)) :
    RunWPc g σ0 cuts 63 fr σ := by
  obtain ⟨res, ld, lw, lr, A, acctV, T, d, ⟨f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41, ht,
    hres, hdisp, hw, hr, hr0, hd0, hw0, hl0, hA0, hd1, hd2, hd3, hg, hin⟩, f16, f38, hT0,
    ⟨fs, hT, hk⟩, f28, hd, ⟨v25, f25⟩, ⟨v26, f26⟩, ⟨v27, f27⟩, ⟨v29, f29⟩, v17, f17⟩ := h
  obtain ⟨k1, hk1⟩ := hk "tranId" (by decide)
  obtain ⟨k2, hk2⟩ := hk "tranTypeCd" (by decide)
  obtain ⟨k3, hk3⟩ := hk "tranCatCd" (by decide)
  obtain ⟨k4, hk4⟩ := hk "tranSource" (by decide)
  obtain ⟨k5, hk5⟩ := hk "tranDesc" (by decide)
  obtain ⟨k6, hk6⟩ := hk "tranAmt" (by decide)
  obtain ⟨k7, hk7⟩ := hk "tranMerchantId" (by decide)
  obtain ⟨k8, hk8⟩ := hk "tranMerchantName" (by decide)
  obtain ⟨k9, hk9⟩ := hk "tranMerchantCity" (by decide)
  obtain ⟨k10, hk10⟩ := hk "tranMerchantZip" (by decide)
  obtain ⟨k11, hk11⟩ := hk "tranCardNum" (by decide)
  obtain ⟨k12, hk12⟩ := hk "tranOrigTs" (by decide)
  obtain ⟨k13, hk13⟩ := hk "tranProcTs" (by decide)
  obtain ⟨k14, hk14⟩ := hk "filler1" (by decide)
  have hg' := Hide.intro hg
  have hin' := Hide.intro hin
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hin
  have hT' := Hide.intro hT
  have hd' := Hide.intro hd
  clear hg hk
  unfold RunWPc
  jvc [runSpecG, runC, inlineFuel, Grows, spacesSig, spacesSpec, ctorRCSig, ctorRCF]
  spec_eqs!
  apply ji70_of (acctV := acctV) (v17 := v17) ht hres hdisp hw hr hr0 hd0 hw0 hl0 hA0 hd1 hd2 hd3
    (Hide.elim hg') (Hide.elim hin')
    hT0 (Hide.elim hT') (Hide.elim hd')
  case h1n => assumption
  case h1f => assumption
  case h2n => assumption
  case h2f => assumption
  case h3n => assumption
  case h3f => assumption
  case h4n => assumption
  case h4f => assumption
  case h5n => assumption
  case h5f => assumption
  case h6n => assumption
  case h6f => assumption
  case hw6 => assumption
  case hcT => assumption
  case hk =>
    intro k hk
    simp only [keysTR, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, by assumption⟩
  case hdesc => assumption
  case hfil => assumption
  case hcf => assumption
  case hcn => assumption
  case hci => assumption
  all_goals frame_simp [f1, f36, f40, f8, f37, f24, f10, f19, f20, f21, f41, f16, f38, f17]

end EquivLean.Modernize.Cbact04c.Java

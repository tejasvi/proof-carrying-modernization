import EquivLean.Modernize.Cbstm03a.Java.Clinit.VCa
import EquivLean.Modernize.Cbstm03a.Java.Clinit.VCb
import EquivLean.Modernize.Cbstm03a.Java.Clinit.VCc

/-! `<clinit>`'s verification conditions, assembled: the entry path by the class's initialization state,
then one run per cut point (`CbAClinit.VCa`, `CbAClinit.VCb`, `CbAClinit.VCc`). -/

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
/-- The verification conditions of `<clinit>` against its contract, with the contract table `clinitT`
(itself) answering the nested run of `<clinit>`. -/
theorem clinit_vc : MethodVC Gen.prog clinitT.env 0 clinitRef clinitSpec clinitInv 100 := by
  refine ⟨_, rfl, fun args σ0 _ => ⟨?_, ?_⟩⟩
  · show bodyWP Gen.prog (callWP Gen.prog clinitT.env 0) Gen.Cbstm03a.«<clinit>()» (clinitInv.inst args σ0)
      (clinitSpec.post args σ0) 100 0 (Frame.init true args) σ0
    cases h : σ0.initOf "Cbstm03a"
    · exact entry_none_vc args σ0 h
    · exact entry_done_vc args σ0 h
    · exact entry_failed_vc args σ0 h
  · intro p hp
    simp only [Invariants.inst, clinitInv, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact fun fr σ h => cut1_vc args σ0 fr σ h
    · exact fun fr σ h => cut13_vc args σ0 fr σ h
    · exact fun fr σ h => cut25_vc args σ0 fr σ h
    · exact fun fr σ h => cut33_vc args σ0 fr σ h
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store0_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store16_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store32_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store48_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store64_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store80_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store96_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store112_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store128_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store144_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store160_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store176_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store192_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store208_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store224_vc args σ0 fr σ a ha hh hσ
    · intro fr σ h
      obtain ⟨a, ha, hh, hσ⟩ := h
      exact store240_vc args σ0 fr σ a ha hh hσ

end EquivLean.Modernize.Cbstm03a.Java

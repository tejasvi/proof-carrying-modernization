-- Termination package by JimpleLean's session: TermPk/Cbtrn01c/JavaTermInit.lean (sha256 5219e67bc7071b9d...); only the module root renamed.
import EquivLean.Modernize.Cbtrn01c.JavaRunInit
import EquivLean.Modernize.Cbtrn01c.JavaTermDefs

/-!
# CBTRN01C → Java, termination: thin twin of `run_seg22` (`JavaRunInit`)

The statement and the preamble of the original, the cut assertions the variants (`runVs`),
calls by `callWPT` without preconditions (`callWPThin`); variant goals by the program variant closer.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple EquivLean.Modernize.TermCommon

namespace EquivLean.Modernize.Cbtrn01c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg22 (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (fr : Frame) (σ : State)
    (h : J22 a1 a3 a5 (runArgs a1 a2 a3 a4 a5 a6) σ0 fr σ) :
    RunThinWP a1 a2 a3 a4 a5 a6 vals1 vals3 vals5 σ0 22 fr σ := by

  obtain ⟨r8, res, l, f10, f35, f4, f9, f11, f1, hr8, ⟨s20, f20, h20⟩, ⟨s21, f21, h21⟩,
    ⟨s22, f22, h22⟩, ⟨s23, f23, h23⟩, ⟨s24, f24, h24⟩, ⟨s25, f25, h25⟩, ⟨s26, f26, h26⟩,
    ⟨s27, f27, h27⟩, ⟨s28, f28, h28⟩, ⟨s29, f29, h29⟩, ⟨s30, f30, h30⟩, hres, hlist, hres0, hl0,
    hr80, hrl, hg, hinit⟩ := h
  obtain ⟨fsR, hR1, hR2, hR3⟩ := hres
  obtain ⟨ys, m, hl, hD⟩ := hlist
  have hrr8 : res ≠ r8 := by intro h; subst h; rw [hR1] at hr8; simp [dalCls] at hr8
  have hlr8 : l ≠ r8 := by intro h; subst h; rw [hl] at hr8; simp at hr8
  have hs20 : s20 ≠ r8 := by intro h; subst h; rw [h20] at hr8; simp at hr8
  have hs27 : s27 ≠ r8 := by intro h; subst h; rw [h27] at hr8; simp at hr8
  have hg' := Hide.intro hg
  have hR1' := Hide.intro hR1
  have hl' := Hide.intro hl
  clear hg hR1 hl
  unfold RunThinWP
  jvc [runInv, runSpecG, callees, spacesSig, digitsSig, formatDalytranSig, spacesSpec, runArgs,
    inlineFuel, fields_get_cons, fields_get_nil, jstrLitT, SpAt, dalCls, dalFields0]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip
  all_goals cbtrn01c_variant

end EquivLean.Modernize.Cbtrn01c.Java

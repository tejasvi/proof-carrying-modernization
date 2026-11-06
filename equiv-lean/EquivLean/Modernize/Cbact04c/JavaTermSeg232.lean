-- Termination package by JimpleLean's session: TermPk/Cbact04c/JavaTermSeg232.lean (sha256 a276ff367d0b6111...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.JavaRunSeg232
import EquivLean.Modernize.Cbact04c.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg232`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem run_tseg232 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J232 g g.args σ0 fr σ)
    (c233 : cuts.lookup 233 = none) (c234 : cuts.lookup 234 = none) (c235 : cuts.lookup 235 = none)
    (c236 : cuts.lookup 236 = none) (c237 : cuts.lookup 237 = none) (c238 : cuts.lookup 238 = none)
    (c239 : cuts.lookup 239 = none) (c240 : cuts.lookup 240 = none) (c241 : cuts.lookup 241 = none)
    (c242 : cuts.lookup 242 = some (fun fr' σ' => runVs B 242 g.args σ0 fr' σ' < runVs B 232 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 232 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb⟩, f3, f11,
    f12, f14, f25, f16, f17, hheap, hrate⟩, hset⟩ := h
  have hcl := clk_len_of_pre hpre
  clear hpre
  obtain ⟨fsT, hT, hset11⟩ := Hide.elim hset
  have hL := Hide.elim hheap
  obtain ⟨-, -, -, -, -, -, -, -, htr, -, hclk⟩ := hL.1
  obtain ⟨c, hcV, hch⟩ := hclk
  obtain ⟨fs0, hT0, hTk, -, -⟩ := id htr
  rw [hT] at hT0
  cases hT0
  obtain ⟨w11, hw11⟩ := hTk "tranOrigTs" (by decide)
  obtain ⟨w12, hw12⟩ := hTk "tranProcTs" (by decide)
  have hinit : Inits σ := hL.1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  rw [hcV] at f24
  have hT' := Hide.intro hT
  have hset11' := Hide.intro hset11
  have htr' := Hide.intro htr
  clear hset11 htr hTk hset hL
  unfold RunThinWPc
  jvc [runSpecG, runC, Grows, fields_get_set, narrow_cls, narrow_long, cp037Str_len, evalDynamic,
    concatRecipe, Native.valueOfArg, Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, Native.primStr,
    JType.isRef, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java

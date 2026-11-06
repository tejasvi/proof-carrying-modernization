-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermSeg217.lean (sha256 e42734d8c0ca9907...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunSeg217
import EquivLean.Modernize.Cbact04c.Every.JavaTermDefs

/-!
# CBACT04C → Java, termination: thin twins of `JavaRunSeg217`

The statements and preambles of the originals; the cut assertions the variants (`runVs`),
calls by `callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
set_option jimple.trace true in
theorem run_tseg217 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts) (B : Nat) (hB1 : 2147483648 < B) (hB2 : B < 8589934576)
    (hpre : RunPreG g g.args σ0) (h : J217 g g.args σ0 fr σ)
    (c218 : cuts.lookup 218 = none) (c219 : cuts.lookup 219 = none) (c220 : cuts.lookup 220 = none)
    (c221 : cuts.lookup 221 = none) (c222 : cuts.lookup 222 = none) (c223 : cuts.lookup 223 = none)
    (c224 : cuts.lookup 224 = some (fun fr' σ' => runVs B 224 g.args σ0 fr' σ' < runVs B 217 g.args σ0 fr σ)) :
    RunThinWPc g σ0 cuts 217 fr σ := by
  obtain ⟨i, hp, tcbV, acctV, xrefV, lastV, headV, ⟨⟨hn, hi0, hlocs, f22, f6, f4, f5, htcb, hstop⟩, f3, f11,
    f12, f14, f25, f16, f17, hheap, hrate⟩, f27, hhead, hset⟩ := h
  clear hpre
  -- the transaction object: its fields so far, its description (100 characters, 76 spaces at the end)
  obtain ⟨fsT, hT, hset4⟩ := Hide.elim hset
  have htr : TranOk σ hp.T := by
    obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := (Hide.elim hheap).1
    exact htr
  obtain ⟨fs0, hT0, hTk, ⟨d, s, hd, hds, hsl, hsd⟩, -⟩ := id htr
  rw [hT] at hT0
  cases hT0
  obtain ⟨w4, hw4⟩ := hTk "tranDesc" (by decide)
  obtain ⟨w5, hw5⟩ := hTk "tranAmt" (by decide)
  obtain ⟨w6, hw6⟩ := hTk "tranMerchantId" (by decide)
  -- the description's head
  obtain ⟨hd0, hhV, hhs⟩ := Hide.elim hhead
  subst hhV
  generalize hHE : JStr.ofString "Int. for a/c " ++
    zpadJ (Model.aId (sel g i.toInt.toNat).acct).natAbs 11 = H at hhs
  have hHl : H.length = 24 := by rw [← hHE]; simp [zpadJ_length]
  have hinit : Inits σ := (Hide.elim hheap).1.2.1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := hinit
  have hlocs' := Hide.intro hlocs
  obtain ⟨f1, f36, f40, f8, f37, f10, f19, f20, f21, f41, f38, f26, f24⟩ := hlocs
  have hHE' := Hide.intro hHE
  have hset4' := Hide.intro hset4
  have htr' := Hide.intro htr
  have hT' := Hide.intro hT
  clear hHE hset4 htr hTk hset hhead
  unfold RunThinWPc
  jvc [runSpecG, runC, evalDynamic, concatRecipe, Native.valueOfArg, fields_get_set, narrow_cls,
    narrow_long, runVs, upAt]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbact04c.Java

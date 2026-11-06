import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunAsm
import EquivLean.Modernize.Cbtrn02c.Any.JavaProof

/-!
# CBTRN02C → Java on any input: `run` satisfies `runSpec`

The inputs `run`'s precondition reads off the heap fix the model run (`runIn_det`), so the
contract for those inputs (`run_satG`) gives `runSpec`'s postcondition.
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Any.Java

/-- **`run` satisfies its contract on any input.** -/
theorem run_sat : Sat Cbtrn02c.Java.Gen.prog runRef runSpec := by
  intro args σ o hpre hm
  obtain ⟨v1, v2, v3, v4, clk, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  have hin0 := hin
  obtain ⟨a1, a2, a3, a4, cs, hargs, -⟩ := hin0
  have hpreG : Cbtrn02c.Java.RunPreGX ⟨a1, a2, a3, a4, cs, v1, v2, v3, v4, clk⟩ args σ := by
    refine ⟨hargs, ?_, ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩⟩
    rw [hargs] at hin
    exact hin
  have hpost := Cbtrn02c.Java.run_satG ⟨a1, a2, a3, a4, cs, v1, v2, v3, v4, clk⟩ args σ o hpreG hm
  cases o with
  | normal r σ' =>
    intro w1 w2 w3 w4 clk' hin'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Cbtrn02c.Java.runIn_det hin hin'
    exact hpost
  | exc e σ' => exact hpost
  | wrong m => exact hpost

/-- **CBTRN02C → Java on any input.** -/
theorem java : Statement := statement_of_sat run_sat

end EquivLean.Modernize.Cbtrn02c.Any.Java

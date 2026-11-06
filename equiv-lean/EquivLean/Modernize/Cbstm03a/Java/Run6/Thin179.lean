import EquivLean.Modernize.Cbstm03a.Java.Run6.ThinExit
import EquivLean.Modernize.Cbstm03a.Java.Run6.ThinBody

/-!
# CBSTM03A → Java `run`: the thin paths from statement 179 (`label37`, the transactions loop)

The variant `runVar` decreases on both paths of the transactions loop: to the cards loop (statement 168,
`crJmp + 1`, `Seg6.t179_exit` with `Seg6.var179_exit`) and back to statement 179 (`trJmp + 1`, `Seg6.t179_body`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem run_thin179 (g : RunG) : RunThinCut g 179 inv179 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨res, ld, ls, lh, L, oc, j, crJmp, total, n, pF, cnt, trJmp, acc0, hX, -, -, -, h17, h21, -,
    hc1, hc2, -, h19, hcnt, h22, ht1, ht2, -, -⟩ := hI
  by_cases hgt : cnt.toInt < trJmp.toInt
  · have hLB := Seg6.xctx_bounded hX
    have hcr := hLB.2.1
    have h18 : fr.get 18 = some (.long L.cr) := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e18, -⟩ := hX
      exact e18
    exact Seg6.t179_exit g args σ0 fr σ crJmp cnt trJmp _ h17 h19 h22 hgt
      (Seg6.Kp.intro fun fr' hf17 hf =>
        Seg6.var179_exit hf hf17 h17 h18 h19 h22 (by omega) (by omega) hc2 hgt ht2)
  · exact Seg6.t179_body g args σ0 hpre fr σ res ld ls lh L oc j crJmp total cnt trJmp hX h17 h21 hc1 hc2 h19
      hcnt h22 ht1 (by omega)

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin179

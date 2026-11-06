import EquivLean.Modernize.Cbstm03a.Java.Run6.Exit
import EquivLean.Modernize.Cbstm03a.Java.Run6.Body

/-!
# CBSTM03A → Java `run`: the paths from statement 179 (`label37`, the transactions loop)

The transactions loop of card number `crJmp` (`cnt` transactions, `trJmp` next): `trJmp > cnt` leaves to the
cards loop (statement 168, `crJmp + 1`, `Seg6.c179_exit`); otherwise the body reads transaction `trJmp` of the
table (`tranOff`, `memRead`), decodes its amount, writes its lines (`writeTrans`), adds the amount to the total
(`trunc11`) and comes back with `trJmp + 1` (`Seg6.c179_body`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

theorem run_cut179_vc (g : RunG) : RunCutVC g 179 inv179 := by
  intro args σ0 hpre fr σ hI
  obtain ⟨res, ld, ls, lh, L, oc, j, crJmp, total, n, pF, cnt, trJmp, acc0, hX, hj, hM, h32, h17, h21, hT,
    hc1, hc2, hcn, h19, hcnt, h22, ht1, ht2, hacc, hcards⟩ := hI
  by_cases hgt : cnt.toInt < trJmp.toInt
  · exact Seg6.c179_exit g args σ0 fr σ crJmp cnt trJmp h17 h19 h22 hgt
      (Seg6.Kp.intro fun fr' hf17 hf hf21 =>
        Seg6.inv168_of_exit hX hj hM h32 h21 hT hc1 hc2 hcn hcnt ht2 hacc hcards hgt fr' hf17 hf hf21)
  · exact Seg6.c179_body g args σ0 hpre fr σ res ld ls lh L oc j crJmp total n pF cnt trJmp acc0 hX hj hM h32
      h17 h21 hT hc1 hc2 hcn h19 hcnt h22 ht1 ht2 hacc hcards (by omega)

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_cut179_vc

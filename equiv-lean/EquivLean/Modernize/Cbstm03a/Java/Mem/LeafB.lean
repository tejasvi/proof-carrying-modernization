import EquivLean.Modernize.Cbstm03a.Java.Mem.Lem

/-!
# CBSTM03A → Java, table memory: the slot geometry

`slotStart`, `slotIndex`: the machine arithmetic is the natural-number geometry (`slotSt`, `slotIdx`) on the
operands' ranges (`Lem.lean`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)
open EquivLean.Modernize.Cbstm03a.Java.Mem

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem slotStart_vc : MethodVC Gen.prog (fun _ => none) 0 slotStartRef slotStartSpec [] 30 := by
  jverify [slotStartSpec, slotSt, srem11_eq_zero_iff]
  all_goals first
    | exact slotStart_eq0 _ (by assumption)
    | exact slotStart_eq1 _ (by assumption) (by assumption)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem slotIndex_vc : MethodVC Gen.prog (fun _ => none) 0 slotIndexRef slotIndexSpec [] 30 := by
  jverify [slotIndexSpec, slotIdx, l2i_srem3356_toInt]
  all_goals first
    | exact slotIndex_eq0 _ (by assumption) (by assumption)
    | exact slotIndex_eq1 _ (by assumption) (by assumption) (by assumption)

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.slotStart_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.slotIndex_vc

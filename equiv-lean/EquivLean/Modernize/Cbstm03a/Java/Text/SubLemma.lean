import EquivLean.Modernize.Cbstm03a.Java.Iface3

open Jimple

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem sub_16_65 (tr : JStr) (h : 65 ≤ tr.length) : sub tr 16 65 = [tr[16], tr[17], tr[18], tr[19], tr[20], tr[21], tr[22], tr[23], tr[24], tr[25], tr[26], tr[27], tr[28], tr[29], tr[30], tr[31], tr[32], tr[33], tr[34], tr[35], tr[36], tr[37], tr[38], tr[39], tr[40], tr[41], tr[42], tr[43], tr[44], tr[45], tr[46], tr[47], tr[48], tr[49], tr[50], tr[51], tr[52], tr[53], tr[54], tr[55], tr[56], tr[57], tr[58], tr[59], tr[60], tr[61], tr[62], tr[63], tr[64]] := by
  simp (disch := omega) only [sub, List.take_succ, List.take_zero, List.getElem?_eq_getElem, Option.toList_some,
    List.nil_append, List.cons_append, List.singleton_append, List.drop_succ_cons, List.drop_zero,
    List.append_assoc]

end EquivLean.Modernize.Cbstm03a.Java.Txt

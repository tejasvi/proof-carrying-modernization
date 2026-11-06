import EquivLean.Modernize.Cbstm03a.Java.Mem.Lem

/-!
# CBSTM03A → Java, table memory: the leaf methods

`cardOff`, `tranOff`, `slotLen`, `getTrct`, `setTrct`, `seqRead` (no callees, no loops).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)
open EquivLean.Modernize.Cbstm03a.Java.Mem

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem cardOff_vc : MethodVC Gen.prog (fun _ => none) 0 cardOffRef cardOffSpec [] 20 := by
  jverify [cardOffSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem tranOff_vc : MethodVC Gen.prog (fun _ => none) 0 tranOffRef tranOffSpec [] 20 := by
  jverify [tranOffSpec]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem slotLen_vc : MethodVC Gen.prog (fun _ => none) 0 slotLenRef slotLenSpec [] 20 := by
  jverify [slotLenSpec, slotLn, srem11_eq_zero_iff]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem getTrct_vc : MethodVC Gen.prog (fun _ => none) 0 getTrctRef getTrctSpec [] 30 := by
  jverify [getTrctSpec, trctGet, l2i_sub_one_toInt, l2i_sub_one_toNat, l2i_zero_toInt, l2i_fifty_toInt]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem setTrct_vc : MethodVC Gen.prog (fun _ => none) 0 setTrctRef setTrctSpec [] 30 := by
  jverify [setTrctSpec, trctSet, Keeps, l2i_sub_one_toInt, l2i_sub_one_toNat, l2i_zero_toInt, l2i_fifty_toInt]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
theorem seqRead_vc : MethodVC Gen.prog (fun _ => none) 0 seqReadRef seqReadSpec [] 30 := by
  jverify [seqReadSpec, seqCode, seqStArr, Keeps]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.cardOff_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.tranOff_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.slotLen_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.getTrct_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.setTrct_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.seqRead_vc

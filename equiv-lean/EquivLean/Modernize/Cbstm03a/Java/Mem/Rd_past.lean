import EquivLean.Modernize.Cbstm03a.Java.Mem.RdDefs

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mem

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.modelContracts true in
theorem rd_past (args : List Value) (σ0 : State) (hpre : memReadSpec.pre args σ0) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (n : I32) (vs : List Value) (sb : Addr) (pos : I32) (t : JStr)
    (ha : args = [.ref a, .long off, .int n]) (h : RdAt σ0 fr σ a off n vs sb pos t)
    (hx : pos.toInt < n.toInt) (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt)
    (hpast : 171156 ≤ off.toInt + pos.toInt) : rdWP args σ0 6 fr σ := by
  simp only [rdWP]
  jvc [ite_nat_ne, memReadInv, rdInv6, RdAt, rdCallees, Grows, memReadSpec, spacesSpecI]
  all_goals exact rd_past_c _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›

end EquivLean.Modernize.Cbstm03a.Java.Mem
#print axioms EquivLean.Modernize.Cbstm03a.Java.Mem.rd_past

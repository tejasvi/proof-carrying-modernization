import EquivLean.Modernize.Cbstm03a.Java.Mem.RdDefs

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mem

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
set_option jimple.modelContracts true in
/-- From the loop head past the slot read (statement 38): slot, offset and count of an in-range position. -/
theorem rd_pre (args : List Value) (σ0 : State) (hpre : memReadSpec.pre args σ0) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (n : I32) (vs : List Value) (sb : Addr) (pos : I32) (t : JStr)
    (ha : args = [.ref a, .long off, .int n]) (h : RdAt σ0 fr σ a off n vs sb pos t)
    (hx : pos.toInt < n.toInt) (ho : (off + JInt.toLong pos).toInt = off.toInt + pos.toInt)
    (hon : (off + JInt.toLong pos).toNat = (off.toInt + pos.toInt).toNat)
    (hin0 : 0 ≤ off.toInt + pos.toInt) (hin1 : off.toInt + pos.toInt < 171156)
    (hjm : (off.toInt + pos.toInt).toNat < 171156)
    (hi : slotIdx (off.toInt + pos.toInt).toNat < 561)
    (hw0 : slotSt (slotIdx (off.toInt + pos.toInt).toNat) ≤ (off.toInt + pos.toInt).toNat)
    (hw1 : (off.toInt + pos.toInt).toNat <
      slotSt (slotIdx (off.toInt + pos.toInt).toNat) + slotLn (slotIdx (off.toInt + pos.toInt).toNat))
    (hwi : (JLong.toInt (off + JInt.toLong pos - BitVec.ofNat 64 (slotSt (slotIdx (off.toInt + pos.toInt).toNat)))).toInt =
      off.toInt + pos.toInt - (slotSt (slotIdx (off.toInt + pos.toInt).toNat) : Int)) :
    rdWP args σ0 6 fr σ := by
  simp only [rdWP]
  jvc [ite_nat_ne, memReadInv, rdInv6, rdInv38, RdAt, Rd38At, rdCallees, Grows, memReadSpec, spacesSpecI,
    slotIndexSpec, slotLenSpec, slotStartSpec, ofNat32_slotIdx_toNat, ofNat32_slotIdx_toInt, ofNat32_slotLn_toInt]
  all_goals exact rd_take_pos _ ‹_› ‹_›

end EquivLean.Modernize.Cbstm03a.Java.Mem
#print axioms EquivLean.Modernize.Cbstm03a.Java.Mem.rd_pre

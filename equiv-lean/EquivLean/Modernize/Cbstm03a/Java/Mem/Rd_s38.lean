import EquivLean.Modernize.Cbstm03a.Java.Mem.RdDefs

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mem

set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
set_option jimple.modelContracts true in
/-- From the slot read (statement 38), a string slot: its characters, back at the loop head. -/
theorem rd_s38 (args : List Value) (σ0 : State) (hpre : memReadSpec.pre args σ0) (fr : Frame) (σ : State)
    (a : Addr) (off : I64) (n : I32) (vs : List Value) (sb : Addr) (pos ix wv tk : I32) (cv : Value) (t : JStr)
    (ha : args = [.ref a, .long off, .int n]) (h : Rd38At σ0 fr σ a off n vs sb pos ix wv tk cv t)
    (x : Addr) (c : JStr) (hcv : cv = .ref x) (hc : σ.heap x = some (.str c)) (hc0 : σ0.heap x = some (.str c))
    (hcl : c.length = slotLn (slotIdx (off.toInt + pos.toInt).toNat))
    (hw0 : slotSt (slotIdx (off.toInt + pos.toInt).toNat) ≤ (off.toInt + pos.toInt).toNat) : rdWP args σ0 38 fr σ := by
  simp only [rdWP]
  jvc [ite_nat_ne, memReadInv, rdInv6, rdInv38, RdAt, Rd38At, rdCallees, Grows, memReadSpec, spacesSpecI]
  all_goals first
    | exact rd_str_c2 _ _ _ _ _ _ _ ‹_› ‹_› ‹_› hc0 hcl ‹_› ‹_› (by omega)
    | omega

end EquivLean.Modernize.Cbstm03a.Java.Mem

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mem.rd_s38

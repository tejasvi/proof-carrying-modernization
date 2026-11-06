import EquivLean.Modernize.Cbstm03a.Java.Mem.RdDefs

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mem

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
set_option jimple.modelContracts true in
theorem rd_entry (args : List Value) (σ0 : State) (hpre : memReadSpec.pre args σ0) :
    rdWP args σ0 0 (Frame.init true args) σ0 := by
  obtain ⟨a, off, n, m, rfl, hs, hoff, hnb, hinit⟩ := hpre
  obtain ⟨vs, ha, hlen, -⟩ := hs
  simp only [rdWP]
  jvc [ite_nat_ne, memReadInv, rdInv6, RdAt, rdCallees, memRd_zero, Grows]


end EquivLean.Modernize.Cbstm03a.Java.Mem

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mem.rd_entry

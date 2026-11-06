import EquivLean.Modernize.Cbstm03a.Java.Mw.Defs

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Mw

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The entry path: `pos = 0`, `n = s.length()`, the loop head. -/
theorem mw_entry (args : List Value) (σ0 : State) (hpre : memWriteSpec.pre args σ0) :
    mwWPc args σ0 [] 120 0 (Frame.init true args) σ0 := by
  obtain ⟨a, off, x, m, t, rfl, hs, hx, htl, hoff, hinit⟩ := hpre
  have hK := memK_init σ0 a off t
  clear hs
  unfold mwWPc
  jvc [memWriteInv, mwInv5, MwAt, mwCallees]

end EquivLean.Modernize.Cbstm03a.Java.Mw

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.mw_entry

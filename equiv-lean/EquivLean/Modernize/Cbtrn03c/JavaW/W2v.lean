import EquivLean.Modernize.Cbtrn03c.JavaW.W2a
import EquivLean.Modernize.Cbtrn03c.JavaW.W2b
import EquivLean.Modernize.Cbtrn03c.JavaW.W2c

/-!
# CBTRN03C → Java: `writePageTotals` from its segments
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

theorem writePageTotals_vcG (w ld lr : Addr) (v : WsV) :
    MethodVC Gen.prog totalsCallees.env 0 writePageTotalsRef (writePageTotalsSpecG w ld lr v)
      (writePageTotalsInv w ld lr v) 80 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wpt_entry w ld lr v args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [writePageTotalsInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact wpt_seg1 w ld lr v args σ0 fr σ hI
  · exact wpt_seg2 w ld lr v args σ0 fr σ hI

theorem writePageTotals_satG (w ld lr : Addr) (v : WsV) :
    Sat Gen.prog writePageTotalsRef (writePageTotalsSpecG w ld lr v) :=
  MethodVC.sat_of_valid totalsCallees_valid (writePageTotals_vcG w ld lr v)

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.writePageTotals_satG

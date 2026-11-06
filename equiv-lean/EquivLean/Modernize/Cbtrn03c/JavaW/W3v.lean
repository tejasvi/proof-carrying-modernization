import EquivLean.Modernize.Cbtrn03c.JavaW.W3a
import EquivLean.Modernize.Cbtrn03c.JavaW.W3b

/-!
# CBTRN03C → Java: `writeAccountTotals`, `writeGrandTotals` from their segments
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

theorem writeAccountTotals_vcG (w ld lr : Addr) (v : WsV) :
    MethodVC Gen.prog totalsCallees.env 0 writeAccountTotalsRef
      (writeAccountTotalsSpecG w ld lr v) (writeAccountTotalsInv w ld lr v) 80 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wat_entry w ld lr v args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [writeAccountTotalsInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact wat_seg1 w ld lr v args σ0 fr σ hI
  · exact wat_seg2 w ld lr v args σ0 fr σ hI

theorem writeAccountTotals_satG (w ld lr : Addr) (v : WsV) :
    Sat Gen.prog writeAccountTotalsRef (writeAccountTotalsSpecG w ld lr v) :=
  MethodVC.sat_of_valid totalsCallees_valid (writeAccountTotals_vcG w ld lr v)

theorem writeGrandTotals_vcG (w ld lr : Addr) (v : WsV) :
    MethodVC Gen.prog totalsCallees.env 0 writeGrandTotalsRef
      (writeGrandTotalsSpecG w ld lr v) (writeGrandTotalsInv w ld lr v) 80 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wgt_entry w ld lr v args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [writeGrandTotalsInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  subst hp
  exact wgt_seg1 w ld lr v args σ0 fr σ hI

theorem writeGrandTotals_satG (w ld lr : Addr) (v : WsV) :
    Sat Gen.prog writeGrandTotalsRef (writeGrandTotalsSpecG w ld lr v) :=
  MethodVC.sat_of_valid totalsCallees_valid (writeGrandTotals_vcG w ld lr v)

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.writeAccountTotals_satG
#print axioms EquivLean.Modernize.Cbtrn03c.Java.writeGrandTotals_satG

import EquivLean.Modernize.Cbtrn03c.JavaW.W4a
import EquivLean.Modernize.Cbtrn03c.JavaW.W4b
import EquivLean.Modernize.Cbtrn03c.JavaW.W4c

/-!
# CBTRN03C → Java: `writeHeaders`, `writeDetail` from their segments
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Java

theorem writeHeaders_vcG (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) :
    MethodVC Gen.prog linesCallees.env 0 writeHeadersRef (writeHeadersSpecG w ld lr v xs xe rs re)
      (writeHeadersInv w ld lr v rs re) 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wh_entry w ld lr v xs xe rs re args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [writeHeadersInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact wh_seg1 w ld lr v xs xe rs re args σ0 fr σ hI
  · exact wh_seg2 w ld lr v xs xe rs re args σ0 fr σ hI
  · exact wh_seg2a w ld lr v xs xe rs re args σ0 fr σ hI
  · exact wh_seg2b w ld lr v xs xe rs re args σ0 fr σ hI
  · exact wh_seg3 w ld lr v xs xe rs re args σ0 fr σ hI
  · exact wh_seg4 w ld lr v xs xe rs re args σ0 fr σ hI

theorem writeHeaders_satG (w ld lr : Addr) (v : WsV) (xs xe : Addr) (rs re : JStr) :
    Sat Gen.prog writeHeadersRef (writeHeadersSpecG w ld lr v xs xe rs re) :=
  MethodVC.sat_of_valid linesCallees_valid (writeHeaders_vcG w ld lr v xs xe rs re)

theorem writeDetail_vcG (w ld lr : Addr) (v : WsV) (c yx cx : Addr)
    (t : List EquivLean.Cobol.Rec.FVal) (ys cs : JStr) :
    MethodVC Gen.prog linesCallees.env 0 writeDetailRef
      (writeDetailSpecG w ld lr v c yx cx t ys cs) (writeDetailInv w ld lr v c yx cx t ys cs) 120 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨wd_entry w ld lr v c yx cx t ys cs args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [writeDetailInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact wd_segA w ld lr v c yx cx t ys cs args σ0 fr σ hI
  · exact wd_segB w ld lr v c yx cx t ys cs args σ0 fr σ hI
  · exact wd_seg1 w ld lr v c yx cx t ys cs args σ0 fr σ hI

theorem writeDetail_satG (w ld lr : Addr) (v : WsV) (c yx cx : Addr)
    (t : List EquivLean.Cobol.Rec.FVal) (ys cs : JStr) :
    Sat Gen.prog writeDetailRef (writeDetailSpecG w ld lr v c yx cx t ys cs) :=
  MethodVC.sat_of_valid linesCallees_valid (writeDetail_vcG w ld lr v c yx cx t ys cs)

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.writeHeaders_satG
#print axioms EquivLean.Modernize.Cbtrn03c.Java.writeDetail_satG

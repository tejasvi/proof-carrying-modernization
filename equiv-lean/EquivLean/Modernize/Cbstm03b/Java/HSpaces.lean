import EquivLean.Modernize.Cbstm03b.Java.Base

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03b.Java

/-- At the loop head (statement 4): the builder holds `i` spaces. Locals: `i0` 0, `i1` 1, `$r0` 2. -/
def spacesInv : Invariants := [(4, fun args σ0 fr σ => ∀ n : I32, args = [.int n] →
  ∃ sb i, fr.get 0 = some (.int n) ∧ fr.get 1 = some (.int i) ∧ fr.get 2 = some (.ref sb) ∧
    σ.heap sb = some (.builder "java.lang.StringBuilder" (fixStr [] i.toInt.toNat)) ∧
    0 ≤ i.toInt ∧ i.toInt ≤ n.toInt ∧ σ0.next ≤ sb ∧ Grows σ0 σ ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem spaces_vc : MethodVC Gen.prog (fun _ => none) 0 spacesRef spacesSpec spacesInv 60 := by
  jverify [ite_nat_ne, spacesSpec, spacesInv, Grows, fixStr]

end EquivLean.Modernize.Cbstm03b.Java

#print axioms EquivLean.Modernize.Cbstm03b.Java.spaces_vc

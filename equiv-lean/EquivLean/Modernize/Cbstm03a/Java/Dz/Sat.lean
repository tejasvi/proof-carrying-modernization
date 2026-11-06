import EquivLean.Modernize.Cbstm03a.Java.Dz.C5
import EquivLean.Modernize.Cbstm03a.Java.Dz.C7
import EquivLean.Modernize.Cbstm03a.Java.Dz.C16
import EquivLean.Modernize.Cbstm03a.Java.Dz.C57
import EquivLean.Modernize.Cbstm03a.Java.Dz.Entry

/-!
# CBSTM03A → Java: `decodeZoned`'s contract

`Dz.decodeZoned_vc`: the `MethodVC` of `decodeZoned` against `decodeZonedSpec` with cbA-num's invariants, from the
entry path and the paths of the four cut points. `decodeZoned_sat`: its contract (it calls no method of the
program, so the contract table is empty).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

open Dz

set_option maxRecDepth 20000 in
theorem Dz.decodeZoned_vc :
    MethodVC Gen.prog (fun _ => none) 0 decodeZonedRef decodeZonedSpec decodeZonedInv 80 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · have e := dz_entry args σ0 hpre
    unfold dzWP at e
    exact e
  · intro p hp fr σ hI
    simp only [decodeZonedInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · have e := dz_c5 args σ0 hpre fr σ hI; unfold dzWP at e; exact e
    · have e := dz_c7 args σ0 hpre fr σ hI; unfold dzWP at e; exact e
    · have e := dz_c16 args σ0 hpre fr σ hI; unfold dzWP at e; exact e
    · have e := dz_c57 args σ0 hpre fr σ hI; unfold dzWP at e; exact e

/-- **`decodeZoned`'s contract**: the value of the zoned text modulo `2 ^ 64`, the state unchanged. -/
theorem decodeZoned_sat : Sat Gen.prog decodeZonedRef decodeZonedSpec :=
  MethodVC.sat_of_valid (valid_none _) Dz.decodeZoned_vc

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.Dz.decodeZoned_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.decodeZoned_sat

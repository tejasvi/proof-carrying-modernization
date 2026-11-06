import EquivLean.Modernize.Cbstm03a.Java.Mw.Entry
import EquivLean.Modernize.Cbstm03a.Java.Mw.Exit
import EquivLean.Modernize.Cbstm03a.Java.Mw.Skip
import EquivLean.Modernize.Cbstm03a.Java.Mw.Chain

/-!
# CBSTM03A → Java: `memWrite` satisfies its contract

The verification conditions (`MethodVC`, fuel 600, one cut point at the loop head) from the segments: the entry path
(`mw_entry`) and, at the loop head, by cases: `pos ≥ n` (`mw_exit`), `off + pos < 0` (`mw_skip`),
`off + pos ≥ MEM_SZ` (`mw_past`), a slot write (`mw_slot`). Linked against the callee contracts `mwCallees`
(`spaces`, `slotIndex`, `slotLen`, `slotStart`: the interface contracts of `CbANum.Iface1` and `CbAMem.Iface2`).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps space)

namespace EquivLean.Modernize.Cbstm03a.Java

namespace Mw

/-- From the loop head, by cases. -/
theorem mw_loop (args : List Value) (σ0 : State) (hpre : memWriteSpec.pre args σ0) (fr : Frame) (σ : State)
    (hI : mwInv5 args σ0 fr σ) : mwWPc args σ0 [] 600 5 fr σ := by
  obtain ⟨a, off, x, m0, t0, ha, hm0, -, -, -, -⟩ := hpre
  obtain ⟨t, pos, n, h⟩ := hI a off x ha
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, -, -, hoff, hp0, hpo, -, -⟩ := h'
  rcases Int.lt_or_le pos.toInt n.toInt with hx | hx
  · have ho := o_toInt off pos hoff hp0 hpo
    by_cases hneg : off.toInt + pos.toInt < 0
    · exact mwWPc_fuel _ σ0 [] (by decide) 5 fr σ (mw_skip args σ0 fr σ a off x t pos n ha h hx ho hneg)
    by_cases hpast : 171156 ≤ off.toInt + pos.toInt
    · exact mwWPc_fuel _ σ0 [] (by decide) 5 fr σ (mw_past args σ0 fr σ a off x t pos n ha h hx ho hpast)
    subst ha
    exact mw_slot σ0 a off x m0 hm0 fr σ t pos n h hx ho (by omega) (by omega)
  · exact mwWPc_fuel _ σ0 [] (by decide) 5 fr σ (mw_exit args σ0 fr σ a off x t pos n ha h hx)


set_option maxRecDepth 8000 in
/-- `memWrite`'s verification conditions. -/
theorem memWrite_vc : MethodVC Gen.prog mwCallees.env 0 memWriteRef memWriteSpec memWriteInv 600 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, ?_⟩⟩
  · show bodyWP Gen.prog (callWP Gen.prog mwCallees.env 0)
      Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)»
      (memWriteInv.inst args σ0) (memWriteSpec.post args σ0) 600 0 (Frame.init true args) σ0
    have h := mwWPc_fuel args σ0 [] (by decide : 120 ≤ 600) 0 _ _ (mw_entry args σ0 hpre)
    unfold mwWPc at h
    exact h
  · intro p hp fr σ hI
    simp only [memWriteInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    subst hp
    have h := mw_loop args σ0 hpre fr σ hI
    unfold mwWPc at h
    exact h

end Mw

open Mw in
/-- **`memWrite` satisfies `memWriteSpec`**, given the contracts of its callees. -/
theorem memWrite_sat (hV : Valid Gen.prog mwCallees.env) : Sat Gen.prog memWriteRef memWriteSpec :=
  MethodVC.sat_of_valid hV memWrite_vc

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.Mw.memWrite_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.memWrite_sat

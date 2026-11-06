import EquivLean.Modernize.Cbtrn03c.JavaTop.PeEntry
import EquivLean.Modernize.Cbtrn03c.JavaTop.PeCall1
import EquivLean.Modernize.Cbtrn03c.JavaTop.PeCall2
import EquivLean.Modernize.Cbtrn03c.JavaTop.Glue1

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processEnd` from its segments; its model contract
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

theorem pe_vc (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St) :
    MethodVC Gen.prog peCallees.env 0 peRef (peSpecG w ld lr c d t s) (peInv w ld lr d t s) 100 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨pe_entry w ld lr c d t s args σ0 hpre, ?_⟩⟩
  intro p hp fr σ hI
  simp only [peInv, Invariants.inst, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl
  · exact pe_call1 w ld lr c d t s args σ0 fr σ hI
  · exact pe_call2 w ld lr c d t s args σ0 fr σ hI

/-- **`processEnd` performs `Model.eofTail`** (given the callees' contracts). -/
theorem pe_sat (hV : Valid Gen.prog peCallees.env) : Sat Gen.prog peRef processEndSpecM := by
  intro args σ o hpre hx
  obtain ⟨w, ld, lr, c, d, s, t, hargs, hws, htf, hvt, hi1, hi2⟩ := hpre
  have key : ∀ w' ld' lr' c' d' s' t', args = [.ref w', .ref c'] → WsRel σ w' ld' lr' d' s' →
      TranFields σ c' t' → TranRecord.Valid t' → (peSpecG w' ld' lr' c' d' t' s').post args σ o :=
    fun w' ld' lr' c' d' s' t' h1 h2 h3 h4 =>
      MethodVC.sat_of_valid hV (pe_vc w' ld' lr' c' d' t' s') args σ o
        ⟨h1, h2, h3, tamt_bound h4, hi1, hi2⟩ hx
  cases o with
  | normal r σ' => exact fun w' ld' lr' c' d' s' t' h1 h2 h3 h4 => key w' ld' lr' c' d' s' t' h1 h2 h3 h4
  | exc e σ' => exact key w ld lr c d s t hargs hws htf hvt
  | wrong m => exact key w ld lr c d s t hargs hws htf hvt

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pe_sat

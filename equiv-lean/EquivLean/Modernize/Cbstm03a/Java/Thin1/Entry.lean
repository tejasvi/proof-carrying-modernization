import EquivLean.Modernize.Cbstm03a.Java.RunTerm

/-!
# CBSTM03A → Java: `run`'s thin entry path (statements 0 … 12; the cut point asserts nothing)
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run_thin_entry (g : RunG) : RunThinEntry g := by
  intro args σ0 hpre
  obtain ⟨hargs, ⟨et1, xs1, hh1, hl1, hf1⟩, h2, h3, h4, ⟨hcpi, hcpa⟩, hinit⟩ := hpre
  subst hargs
  clear hf1 h2 h3 h4 hcpa
  jvc [runCallees, runInv]

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin_entry

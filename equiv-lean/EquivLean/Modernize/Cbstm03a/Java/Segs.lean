import EquivLean.Modernize.Cbstm03a.Java.RunTotal
import EquivLean.Modernize.Cbstm03a.Java.Run1.C52F
import EquivLean.Modernize.Cbstm03a.Java.Run2.Run80
import EquivLean.Modernize.Cbstm03a.Java.Run3.C117
import EquivLean.Modernize.Cbstm03a.Java.Run3.C140
import EquivLean.Modernize.Cbstm03a.Java.Run3.T140
import EquivLean.Modernize.Cbstm03a.Java.Run5.C153
import EquivLean.Modernize.Cbstm03a.Java.Run5.C168
import EquivLean.Modernize.Cbstm03a.Java.Run6.Cut179
import EquivLean.Modernize.Cbstm03a.Java.Run6.Thin179
import EquivLean.Modernize.Cbstm03a.Java.Run7.T153
import EquivLean.Modernize.Cbstm03a.Java.Thin1.Entry
import EquivLean.Modernize.Cbstm03a.Java.Thin1.C12
import EquivLean.Modernize.Cbstm03a.Java.Thin1.C24
import EquivLean.Modernize.Cbstm03a.Java.Thin1.C37
import EquivLean.Modernize.Cbstm03a.Java.Thin2.T117
import EquivLean.Modernize.Cbstm03a.Java.Thin3.T52
import EquivLean.Modernize.Cbstm03a.Java.Thin3.T80

/-!
# CBSTM03A → Java: `run`'s segments assembled

`run_segs`: the eleven partial-correctness segments (`RunSegs g`) for every ghost value. `run_thin_segs_of`: the
eleven thin (termination) segments, given cut point 168's.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

/-- **The verification conditions of `run`, all segments.** -/
theorem run_segs (g : RunG) : RunSegs g :=
  ⟨run_entry_vc g, run_cut12_vc g, run_cut24_vc g, run_cut37_vc g, run_cut52_vc g, run_cut80_vc g,
   run_cut117_vc g, run_cut140_vc g, run_cut153_vc g, run_cut168_vc g, run_cut179_vc g⟩

/-- `run`'s `MethodVC` against `runSpecG g`, for every ghost value. -/
theorem run_vc (g : RunG) : MethodVC Gen.prog runCallees.env 1 runRefA (runSpecG g) (runInv g) 300 :=
  run_vc_of g (run_segs g)

set_option maxRecDepth 20000 in
/-- The thin segments, given cut point 168's. -/
theorem run_thin_segs_of (h168 : ∀ g, RunThinCut g 168 inv168) (g : RunG) : RunThinSegs g :=
  ⟨run_thin_entry g, run_thin12 g, run_thin24 g, run_thin37 g, run_thin52 g, run_thin80 g, run_thin117 g,
   run_thin140 g, run_thin153 g, h168 g, run_thin179 g⟩

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_segs
#print axioms EquivLean.Modernize.Cbstm03a.Java.run_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin_segs_of

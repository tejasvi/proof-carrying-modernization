import EquivLean.Modernize.Cbtrn03c.JavaTop.Link
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalleesOK
import EquivLean.Modernize.Cbtrn03c.JavaW.WsM2
import EquivLean.Modernize.Cbtrn03c.JavaW.W5v

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: the generated statement

`run`'s contract (`Top.run_sat_of_leaves`, the top layer: `run`, `processDetail`, `processEnd`)
from the leaf contracts: the helpers' (`JavaTop/Cal*.lean`) and the working-state writers'
(`JavaW/WsM*.lean`, `JavaW/W5v.lean`, by cir-repin); then `statement_of_sat` (`JavaProof.lean`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

/-- `Cbtrn03c.run` satisfies `runSpec`. -/
theorem run_sat : Sat Gen.prog runRef runSpec :=
  Top.run_sat_of_leaves Top.zoned_ok Top.add11_ok writePageTotalsM_ok writeGrandTotalsM_ok
    writeAccountTotalsM_ok writeTransactionReportM_ok Top.tranRecordText_ok Top.findXref_ok
    Top.ioStatusLine_ok Top.findTranType_ok Top.findTranCat_ok Top.digits_ok Top.spaces_ok
    Top.blankTran_ok Top.compareEbcdicC_ok

/-- **CBTRN03C → Java, every input.** -/
theorem java : Statement := statement_of_sat run_sat

end EquivLean.Modernize.Cbtrn03c.Java

#print axioms EquivLean.Modernize.Cbtrn03c.Java.java

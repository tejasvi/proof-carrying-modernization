import EquivLean.Modernize.Cbtrn03c.JavaTop.CalSpaces
import EquivLean.Modernize.Cbtrn03c.JavaTop.TopLib2

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: the contract of `ioStatusLine` (the status `"23"` of a failed keyed read)

`ioStatusLine("23")`: `FILE STATUS IS: NNNN0023` (the numeric branch: `"00"`, then the status),
verified directly on `ioStatusLineSpecT`.  As cir-repin's `T3/Rec.lean`.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

abbrev ioStatusLineRef : MethodRef := Gen.Cbtrn03c.«ioStatusLine(java.lang.String)».ref

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ioStatusLine_vc :
    MethodVC Gen.prog (fun _ => none) 0 ioStatusLineRef ioStatusLineSpecT [] 60 := by
  jverify [ioStatusLineSpecT, Agree, jstrLit, txtLit, jline, valueOfArg_char, Native.valueOfArg,
    JType.isRef]

theorem ioStatusLine_sat : Sat Gen.prog ioStatusLineRef ioStatusLineSpecT := ioStatusLine_vc.sat

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

set_option maxHeartbeats 0 in
theorem ioStatusLine_ok : ContractOK Gen.prog ioStatusLineSig ioStatusLineSpecT := by
  jcontract_ok [Cal.ioStatusLine_sat]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.ioStatusLine_ok

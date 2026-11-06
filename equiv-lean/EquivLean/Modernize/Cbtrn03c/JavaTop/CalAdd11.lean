import EquivLean.Modernize.Cbtrn03c.JavaTop.Pe

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: the contract of `add11` (cir-repin's `add11Spec`, verified directly)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

abbrev add11Ref : MethodRef := Gen.Cbtrn03c.«add11(long,long)».ref

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem add11_vc : MethodVC Gen.prog (fun _ => none) 0 add11Ref add11SpecT [] 20 := by
  jverify [add11SpecT]

theorem add11_sat : Sat Gen.prog add11Ref add11SpecT := add11_vc.sat

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

set_option maxHeartbeats 0 in
theorem add11_ok : ContractOK Gen.prog add11Sig add11SpecT := by
  jcontract_ok [Cal.add11_sat]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.add11_ok

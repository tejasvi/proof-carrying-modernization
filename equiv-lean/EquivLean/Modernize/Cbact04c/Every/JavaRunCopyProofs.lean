import EquivLean.Modernize.Cbact04c.Every.JavaRunCopySpecs

/-!
# CBACT04C → Java: the record copies satisfy their contracts

Each copy reads the fields of its argument and calls the constructor (answered by its contract).
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

theorem targets_special {P : Program} {sig : MethodSig} {m : MethodRef}
    (h : P.selectSpecial sig = .jimple m) (hb : m.decl.body.isSome = true) : Targets P sig m :=
  ⟨Or.inr (Or.inl h), hb⟩

def copyTcbC : Contracts := [(ctorTCSig, ctorTCSpec)]
def copyXrefC : Contracts := [(ctorXCSig, ctorXCSpec)]
def copyAcctC : Contracts := [(ctorACSig, ctorACSpec)]
def copyDisC : Contracts := [(ctorDCSig, ctorDCSpec)]
def copyTranC : Contracts := [(ctorRCSig, ctorRCSpec)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem copyTcb_vc : MethodVC Gen.prog copyTcbC.env 0 copyTcbRef
    (copySpec "Cbact04c$TranCatBalRecord" keysTC) [] 40 := by
  jverify [copySpec, keysTC, copyTcbC, ctorTCSig, ctorTCSpec, Grows, fields_get_cons,
    fields_get_nil]
  all_goals (first | exact targets_special rfl rfl | skip)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem copyXref_vc : MethodVC Gen.prog copyXrefC.env 0 copyXrefRef
    (copySpec "Cbact04c$CardXrefRecord" keysXC) [] 40 := by
  jverify [copySpec, keysXC, copyXrefC, ctorXCSig, ctorXCSpec, Grows, fields_get_cons,
    fields_get_nil]
  all_goals (first | exact targets_special rfl rfl | skip)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem copyDis_vc : MethodVC Gen.prog copyDisC.env 0 copyDisRef
    (copySpec "Cbact04c$DisGroupRecord" keysDC) [] 40 := by
  jverify [copySpec, keysDC, copyDisC, ctorDCSig, ctorDCSpec, Grows, fields_get_cons,
    fields_get_nil]
  all_goals (first | exact targets_special rfl rfl | skip)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem copyAcct_vc : MethodVC Gen.prog copyAcctC.env 0 copyAcctRef
    (copySpec "Cbact04c$AccountRecord" keysAC) [] 40 := by
  jverify [copySpec, keysAC, copyAcctC, ctorACSig, ctorACSpec, Grows, fields_get_cons,
    fields_get_nil]
  all_goals (first | exact targets_special rfl rfl | skip)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem copyTran_vc : MethodVC Gen.prog copyTranC.env 0 copyTranRef
    (copySpec "Cbact04c$TranRecord" keysRC) [] 40 := by
  jverify [copySpec, keysRC, copyTranC, ctorRCSig, ctorRCSpec, Grows, fields_get_cons,
    fields_get_nil]
  all_goals (first | exact targets_special rfl rfl | skip)

end EquivLean.Modernize.Cbact04c.Java

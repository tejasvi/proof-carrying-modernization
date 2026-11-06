-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermCtors.lean (sha256 6ef27e5957bdd680...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunCopyProofs
import Jimple.TermSplit
import EquivLean.Modernize.Cbact04c.Every.JavaRunCtorProofs

/-!
# CBACT04C → Java on every input, termination: the record constructors and copies (thin VCs)

The thin twins of the `MethodVC`s of `Every.JavaRunCtorProofs` and `Every.JavaRunCopyProofs`: the
long constructors' cut points (`ctorAC`: 19, 23, 27; `ctorRC`: 20, 24, 28) are straight-line
(variants decreasing along the body); the others have none. As `EquivLean.Modernize.Cbact04c.JavaTermCtors`,
which this package cannot import (the `Every` sources redeclare the narrow proof's names).
-/

open Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-- `ctorAC`'s straight-line cut points 19, 23, 27. -/
def ctorACVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat :=
  if pc = 19 then 3 else if pc = 23 then 2 else if pc = 27 then 1 else 0

/-- `ctorRC`'s straight-line cut points 20, 24, 28. -/
def ctorRCVs (pc : Nat) (_ : List Value) (_ : State) (_ : Frame) (_ : State) : Nat :=
  if pc = 20 then 3 else if pc = 24 then 2 else if pc = 28 then 1 else 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorTC_thin :
    ThinVC Gen.prog (fun _ => none) 0 ctorTCRef ctorTCSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [ctorTCSpec, fields_get_set, fields_get_cons, fields_get_nil, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorXC_thin :
    ThinVC Gen.prog (fun _ => none) 0 ctorXCRef ctorXCSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [ctorXCSpec, fields_get_set, fields_get_cons, fields_get_nil, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorDC_thin :
    ThinVC Gen.prog (fun _ => none) 0 ctorDCRef ctorDCSpec [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [ctorDCSpec, fields_get_set, fields_get_cons, fields_get_nil, narrow_long, narrow_cls]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorAC_thin :
    ThinVC Gen.prog (fun _ => none) 0 ctorACRef ctorACSpec ctorACInv ctorACVs 40 := by
  jthin [ctorACSpec, ctorACInv, ctorACInv19, ctorACInv23, ctorACInv27, fields_get_set,
    fields_get_cons, fields_get_nil, narrow_long, narrow_cls, ctorACVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem ctorRC_thin :
    ThinVC Gen.prog (fun _ => none) 0 ctorRCRef ctorRCSpec ctorRCInv ctorRCVs 40 := by
  jthin [ctorRCSpec, ctorRCInv, ctorRCInv20, ctorRCInv24, ctorRCInv28, fields_get_set,
    fields_get_cons, fields_get_nil, narrow_long, narrow_cls, ctorRCVs]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem copyTcb_thin :
    ThinVC Gen.prog copyTcbC.env 0 copyTcbRef (copySpec "Cbact04c$TranCatBalRecord" keysTC) [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [copySpec, keysTC, copyTcbC, ctorTCSig, ctorTCSpec, Grows, fields_get_cons,
    fields_get_nil]
  all_goals (first | exact targets_special rfl rfl | skip)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem copyXref_thin :
    ThinVC Gen.prog copyXrefC.env 0 copyXrefRef (copySpec "Cbact04c$CardXrefRecord" keysXC) [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [copySpec, keysXC, copyXrefC, ctorXCSig, ctorXCSpec, Grows, fields_get_cons,
    fields_get_nil]
  all_goals (first | exact targets_special rfl rfl | skip)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem copyDis_thin :
    ThinVC Gen.prog copyDisC.env 0 copyDisRef (copySpec "Cbact04c$DisGroupRecord" keysDC) [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [copySpec, keysDC, copyDisC, ctorDCSig, ctorDCSpec, Grows, fields_get_cons,
    fields_get_nil]
  all_goals (first | exact targets_special rfl rfl | skip)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem copyAcct_thin :
    ThinVC Gen.prog copyAcctC.env 0 copyAcctRef (copySpec "Cbact04c$AccountRecord" keysAC) [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [copySpec, keysAC, copyAcctC, ctorACSig, ctorACSpec, Grows, fields_get_cons,
    fields_get_nil]
  all_goals (first | exact targets_special rfl rfl | skip)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem copyTran_thin :
    ThinVC Gen.prog copyTranC.env 0 copyTranRef (copySpec "Cbact04c$TranRecord" keysRC) [] (fun _ _ _ _ _ => 0) 40 := by
  jthin [copySpec, keysRC, copyTranC, ctorRCSig, ctorRCSpec, Grows, fields_get_cons,
    fields_get_nil]
  all_goals (first | exact targets_special rfl rfl | skip)

end EquivLean.Modernize.Cbact04c.Java

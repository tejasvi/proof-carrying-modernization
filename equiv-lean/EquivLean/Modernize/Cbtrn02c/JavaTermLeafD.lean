-- Termination package by JimpleLean's session: TermPk/Cbtrn02c/JavaTermLeafD.lean (sha256 7ede35b972cf5b1b...); only the module root renamed.
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS1
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunS2
import EquivLean.Modernize.TermCommon

/-!
# CBTRN02C → Java, termination: thin VCs of the searches

The thin twins of `findXref_vc`, `findAccount_vc` (`JavaRunS1`), `findTcatbal_vc`, `findKey_vc`
(`JavaRunS2`). Each counts its index `i` up while it is below the array length or list size (an
`int`): variant `2^31 - i`.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- `findXref`: `2^31 - i` (local `i` 3). -/
def findXrefVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 3 with
  | some (.int i) => (2147483648 - i.toInt).toNat
  | _ => 0

/-- `findAccount`: `2^31 - i` (local `i` 4). -/
def findAccountVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 4 with
  | some (.int i) => (2147483648 - i.toInt).toNat
  | _ => 0

/-- `findTcatbal`: `2^31 - i` (local `i` 7). -/
def findTcatbalVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 7 with
  | some (.int i) => (2147483648 - i.toInt).toNat
  | _ => 0

/-- `findKey`: `2^31 - i` (local `i` 2). -/
def findKeyVar (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 2 with
  | some (.int i) => (2147483648 - i.toInt).toNat
  | _ => 0

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findXref_thin :
    ThinVC Gen.prog (fun _ => none) 0 findXrefRef findXrefSpec findXrefInv (fun _ => findXrefVar) 40 := by
  jthin [findXrefSpec, findXrefInv, XrefShapes, noMatch_zero, findXrefVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findAccount_thin :
    ThinVC Gen.prog (fun _ => none) 0 findAccountRef findAccountSpec findAccountInv
      (fun _ => findAccountVar) 40 := by
  jthin [findAccountSpec, findAccountInv, AcctShapes, noMatch_zero, findAccountVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findTcatbal_thin :
    ThinVC Gen.prog (fun _ => none) 0 findTcatbalRef findTcatbalSpec findTcatbalInv
      (fun _ => findTcatbalVar) 40 := by
  jthin [findTcatbalSpec, findTcatbalInv, TcatShapes, noMatch_zero, findTcatbalVar]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem findKey_thin :
    ThinVC Gen.prog (fun _ => none) 0 findKeyRef findKeySpec findKeyInv (fun _ => findKeyVar) 40 := by
  jthin [findKeySpec, findKeyInv, StrShapes, noMatch_zero, findKeyVar]

end EquivLean.Modernize.Cbtrn02c.Java

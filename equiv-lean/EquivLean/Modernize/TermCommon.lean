-- Termination package by JimpleLean's session: TermPk/Common.lean (sha256 9811b76cbbce29f7...); only the module root renamed.
import Jimple.TermSplit

/-!
# Termination packages: common definitions

`intAt fr j`, the `int` in local `j` as a natural number, for variants.
-/

open Jimple

namespace EquivLean.Modernize.TermCommon

/-- The `int` in local `j` as a natural number (`0` if there is none). -/
def intAt (fr : Frame) (j : Nat) : Nat :=
  match fr.get j with
  | some (.int v) => v.toNat
  | _ => 0

end EquivLean.Modernize.TermCommon

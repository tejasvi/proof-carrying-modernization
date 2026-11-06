-- Termination package by JimpleLean's session: TermPk/Cbact04c/Every/JavaTermDefs.lean (sha256 0b51f36db3a85058...); only the module root renamed.
import EquivLean.Modernize.Cbact04c.Every.JavaRunRunDefs
import Jimple.TermSplit

/-!
# CBACT04C → Java on every input: definitions for the termination of `run`

As `EquivLean.Modernize.Cbact04c.JavaTermDefs` for the narrow proof, with the `DEFAULT` retry's cut point 184
(between 172 and 196). The split VC (`Jimple.TermVC.of_thin`) with `run_vc`'s invariants
(`runInvE`) and a variant per cut point (`runVs`). Counters are `int` locals counting up, measured
by `upAt` (`2^31 - v`, at most `2^32`): the account-table copy loop (statement 28, local 18), the
read loop (statement 85, local 22: `i` at the head, `i + 1` inside an iteration) and the
cross-reference search (statement 148, local 23). The copy loop and the statements before the read
loop lie above `2^66`; inside an iteration the read loop's measure is weighted by `2^33`, above
every offset of the iteration's cut points (which decrease along the body; those before the search
lie `B > 2^31` above it).

(The `Every` sources reuse the names of the narrow proof, so this package cannot import the narrow
one: its definitions are repeated here.)
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact04c.Java

/-- `2^31 - v` for the `int` `v` in local `j`, as a natural number (`0` if there is none). -/
def upAt (fr : Frame) (j : Nat) : Nat :=
  match fr.get j with
  | some (.int v) => (2147483648 - v.toInt).toNat
  | _ => 0

/-- The variants of `run`'s cut points, the offset `B` of the statements before the
    cross-reference search a parameter (`2^31 < B < 2^33 - 16`; `run_thin` takes `2^32`): as a
    literal it made `simp` rewrite `x + 4294967308 < x + 4294967309` by `Nat.lt_add_one`, through
    offset unification, which the kernel then checked in unary. Written with `if` on the cut
    point, not by matching on the literals (a match on `242` unfolds unary). -/
def runVs (B pc : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  if pc = 10 then 73786976299133173768
  else if pc = 28 then 73786976294838206471 + upAt fr 18
  else if pc = 38 then 73786976294838206470
  else if pc = 42 then 73786976294838206469
  else if pc = 47 then 73786976294838206468
  else if pc = 57 then 73786976294838206467
  else if pc = 63 then 73786976294838206466
  else if pc = 70 then 73786976294838206465
  else if pc = 85 then 8589934592 * upAt fr 22
  else if pc = 90 then 8589934592 * upAt fr 22 + B + 16
  else if pc = 97 then 8589934592 * upAt fr 22 + B + 15
  else if pc = 102 then 8589934592 * upAt fr 22 + B + 14
  else if pc = 108 then 8589934592 * upAt fr 22 + B + 13
  else if pc = 113 then 8589934592 * upAt fr 22 + B + 12
  else if pc = 125 then 8589934592 * upAt fr 22 + B + 11
  else if pc = 129 then 8589934592 * upAt fr 22 + B + 10
  else if pc = 148 then 8589934592 * upAt fr 22 + 10 + upAt fr 23
  else if pc = 172 then 8589934592 * upAt fr 22 + 9
  else if pc = 184 then 8589934592 * upAt fr 22 + 8
  else if pc = 196 then 8589934592 * upAt fr 22 + 7
  else if pc = 199 then 8589934592 * upAt fr 22 + 6
  else if pc = 210 then 8589934592 * upAt fr 22 + 5
  else if pc = 217 then 8589934592 * upAt fr 22 + 4
  else if pc = 224 then 8589934592 * upAt fr 22 + 3
  else if pc = 232 then 8589934592 * upAt fr 22 + 2
  else if pc = 242 then 8589934592 * upAt fr 22 + 1
  else 0

/-- The thin paths of `run` from `pc` against a cut list `cuts` given by its lookups (as
    `RunWPc`): calls by `callWPThin`, postcondition `True`. -/
def RunThinWPc (_g : G) (_σ0 : State) (cuts : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog runC.env 1) runBody cuts (fun _ => True) 60 pc fr σ

attribute [irreducible] RunThinWPc

end EquivLean.Modernize.Cbact04c.Java

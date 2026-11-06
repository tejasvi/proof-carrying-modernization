-- Termination package by JimpleLean's session: TermPk/Cbact01c/JavaTermDefs.lean (sha256 bec72712b0550e62...); only the module root renamed.
import EquivLean.Modernize.Cbact01c.JavaRunState
import EquivLean.Modernize.TermCommon

/-!
# CBACT01C → Java: definitions for the termination of `run`

The split VC (`Jimple.TermVC.of_thin`) with `run_vc`'s invariant (`runInv10`, statement 10) and the
variant `runVar`: twice the records not yet read (of at most `2^31`), plus one until `endOfFile`
(local 11) is set; `pos` is local 7.
-/

open Jimple EquivLean EquivLean.Jimple EquivLean.Jimple.Spec EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbact01c.Java

/-- The read loop's measure (statement 10). -/
def runVar (fr : Frame) : Nat :=
  match fr.get 7, fr.get 11 with
  | some (.int i), some (.int z) => 2 * (2147483648 - i.toInt).toNat + (if z = 0 then 1 else 0)
  | _, _ => 0

/-- The variants of `run`'s cut points (one: statement 10). -/
def runVs (_ : Nat) (_ : List Value) (_ : Jimple.State) (fr : Frame) (_ : Jimple.State) : Nat := runVar fr

/-- The thin paths of `run` from cut point `pc`: calls by `callWPThin`, the next cut point's
    variant below the value at `(pc, fr, σ)`. -/
def RunThinWP (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal))
    (pc : Nat) (fr : Frame) (σ : Jimple.State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog (runEnv σ0) 1) runBody
    ((runInv σ0 a vals).map fun q => (q.1, fun fr' σ' => runVs q.1 [.ref a] σ0 fr' σ' < runVs pc [.ref a] σ0 fr σ))
    (fun _ => True) 200 pc fr σ

/-- The thin entry path of `run` (cut assertions trivial). -/
def RunThinWP0 (σ0 : Jimple.State) (a : Addr) (vals : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog (runEnv σ0) 1) runBody
    ((runInv σ0 a vals).map fun p => (p.1, fun _ _ => True)) (fun _ => True) 200 0
    (Frame.init true [.ref a]) σ0

attribute [irreducible] RunThinWP RunThinWP0

end EquivLean.Modernize.Cbact01c.Java

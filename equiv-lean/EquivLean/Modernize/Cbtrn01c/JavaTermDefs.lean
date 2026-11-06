-- Termination package by JimpleLean's session: TermPk/Cbtrn01c/JavaTermDefs.lean (sha256 8d2337ca24807b4c...); only the module root renamed.
import EquivLean.Modernize.Cbtrn01c.JavaRunState
import EquivLean.Modernize.TermCommon

/-!
# CBTRN01C → Java: definitions for the termination of `run`

The split VC (`Jimple.TermVC.of_thin`): `run_vc`'s invariants with a variant per cut point,
lexicographic in the read loop's measure (`outerV`: twice the records not yet read, plus one until
the end-of-file flag is set) and the search index, the cross-reference search above the account
search. Counters are `int` locals below `2^31`; the weight `2^33` is above every search term.
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple EquivLean.Modernize.TermCommon

namespace EquivLean.Modernize.Cbtrn01c.Java

/-- The read loop's measure (`dalPos` local 17, the end-of-file flag local 7). -/
def outerV (fr : Frame) : Nat := 2 * (2147483648 - intAt fr 17) + (1 - intAt fr 7)

/-- The variants of `run`'s cut points 22, 29, 60, 92 (search indices locals 16 and 18). Written with
    `if` on the cut point, not by matching on the literals (a match on `92` unfolds unary). -/
def runVs (pc : Nat) (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  if pc = 22 then 8589934592 * 4294967298
  else if pc = 29 then 8589934592 * outerV fr
  else if pc = 60 then 8589934592 * outerV fr + 2147483650 + (2147483648 - intAt fr 16)
  else if pc = 92 then 8589934592 * outerV fr + (2147483648 - intAt fr 18) + 1
  else 0

/-- A variant goal left by `jvc`: the variants unfolded, the frame read through the facts of the
    context, `omega`. -/
macro "cbtrn01c_variant" : tactic => `(tactic|
  ((try simp (config := { decide := true }) only [runVs, outerV, intAt, Frame.get_setLocal,
     BitVec.toNat_add, BitVec.toNat_ofNat, ite_true, ite_false, *] at ⊢) <;>
   (jnorm_lits; omega)))

/-- The thin paths of `run` from cut point `pc`: calls by `callWPThin`, the next cut point's
    variant below the value at `(pc, fr, σ)`. -/
def RunThinWP (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog callees.env 1) runBody
    ((runInv a1 a3 a5 vals1 vals3 vals5).map fun q => (q.1, fun fr' σ' =>
      runVs q.1 (runArgs a1 a2 a3 a4 a5 a6) σ0 fr' σ' < runVs pc (runArgs a1 a2 a3 a4 a5 a6) σ0 fr σ))
    (fun _ => True) 60 pc fr σ

/-- The thin entry path of `run` (cut assertions trivial). -/
def RunThinWP0 (a1 a2 a3 a4 a5 a6 : Addr) (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal))
    (σ0 : State) : Prop :=
  bodyWP Gen.prog (callWPThin Gen.prog callees.env 1) runBody
    ((runInv a1 a3 a5 vals1 vals3 vals5).map fun p => (p.1, fun _ _ => True))
    (fun _ => True) 60 0 (Frame.init true (runArgs a1 a2 a3 a4 a5 a6)) σ0

attribute [irreducible] RunThinWP RunThinWP0

end EquivLean.Modernize.Cbtrn01c.Java

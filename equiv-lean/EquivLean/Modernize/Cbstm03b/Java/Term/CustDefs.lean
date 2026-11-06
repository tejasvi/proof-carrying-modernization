import EquivLean.Modernize.Cbstm03b.Java.Term.KCallees

/-!
# CBSTM03B → Java, termination of `custProc`: definitions

`custProc`'s keyed read searches the file's records (statement 49: `i5 < recs.length`, local 8). Its termination
VC is proved directly (`TermVC`, calls answered by `custCalleesT`), with an invariant of its own at the loop head:
the locals the rest of the method reads, the FD record object `y0` (its key field a string), and the heap of the
entry state kept everywhere but at `y0` (`Keeps`). The variant is `2^31 - i5`.

The termination VC is stated for `kSpecT`: `procSpecG`'s precondition with the State object's file and FD record
objects (`o1`, `y0`) named.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-- The State object's file and FD record objects `o1`, `y0` (fields `fk`, `rk`). -/
def KGhost (fk rk : String) (σ : State) (st o1 y0 : Addr) : Prop :=
  ∃ fsS, σ.heap st = some (.plain "Cbstm03b$State" fsS) ∧ Fields.get fsS ("Cbstm03b$State", fk) = some (.ref o1) ∧
    Fields.get fsS ("Cbstm03b$State", rk) = some (.ref y0)

/-- `procSpecG dd` with the objects `KGhost` names (postcondition `True`: termination only). -/
def kSpecT (dd : List UInt8) (fk rk : String) (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (o1 y0 : Addr) : Spec :=
  ⟨fun args σ => (procSpecG dd oe st q opv oeM s a).pre args σ ∧ KGhost fk rk σ st o1 y0, fun _ _ _ => True⟩

/-- At `custProc`'s loop head (statement 49). Locals: `r2` (area) 0, `r4` (file) 1, `r1` (State) 3, `$i0` (the
record found, `-1`) 6, `i5` 8. -/
def custInvT (st q o1 y0 : Addr) (_ : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ i m fsY z idS, fr.get 0 = some (.ref q) ∧ fr.get 1 = some (.ref o1) ∧ fr.get 3 = some (.ref st) ∧
    fr.get 6 = some (.int m) ∧ fr.get 8 = some (.int i) ∧ m.toInt < 0 ∧ 0 ≤ i.toInt ∧
    σ.heap y0 = some (.plain "Cbstm03b$FdCustfileRec" fsY) ∧
    Fields.get fsY ("Cbstm03b$FdCustfileRec", "fdCustId") = some (.ref z) ∧ σ.heap z = some (.str idS) ∧
    Keeps (fun x => x = y0) σ0 σ ∧ σ.inits = σ0.inits

/-- The search loop's variant: `2^31 - i5`. -/
def custVarT (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 8 with
  | some (.int i) => (2147483648 - i.toInt).toNat
  | _ => 0

def custCutsT (st q o1 y0 : Addr) : TermCuts := [(49, custInvT st q o1 y0, custVarT)]

/-- The termination paths of `custProc` from statement `pc`, with the cut assertions `I`. -/
@[irreducible] def custTWP (I : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPT Gen.prog custCalleesT.env 1)
    Gen.Cbstm03b.«custProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»
    I (fun _ => True) 200 pc fr σ

end EquivLean.Modernize.Cbstm03b.Java

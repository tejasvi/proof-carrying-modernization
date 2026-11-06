import EquivLean.Modernize.Cbstm03b.Java.Term.CustDefs

/-!
# CBSTM03B → Java, termination of `acctProc`: definitions

`acctProc`'s keyed read has two loops: over the key's characters (statement 33: `$i0 < keyPart.length()`, local 8)
and over the file's records (statement 65: `i18 < recs.length`, local 10). Its termination VC is proved directly
(`TermVC`, calls answered by `acctCalleesT`), with invariants of its own at the loop heads (as `custProc`'s: the
locals the rest of the method reads and the entry heap kept but at the FD record object `y0`; at the first loop the
key part, a string of at most 25 characters, and `y0` as at the entry; at the second `y0` with a `long` key). The
variants: `2^32 + 2^31 - $i0` at the first loop head (above every value at the second), `2^31 - i18` at the second.

Locals: `r2` (area) 0, `$l4` 1, `r4` (file) 3, `$i0` 8, `i18` 10, `r3` (the key part) 11, `r1` (State) 17.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-- At `acctProc`'s first loop head (statement 33): the key part and the position in it. -/
def acctInv33 (st q o1 y0 : Addr) (_ : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ i v xk ks, fr.get 0 = some (.ref q) ∧ fr.get 3 = some (.ref o1) ∧ fr.get 17 = some (.ref st) ∧
    fr.get 8 = some (.int i) ∧ fr.get 1 = some (.long v) ∧ fr.get 11 = some (.ref xk) ∧
    σ.heap xk = some (.str ks) ∧ ks.length ≤ 25 ∧ 0 ≤ i.toInt ∧ σ.heap y0 = σ0.heap y0 ∧
    Keeps (fun x => x = y0) σ0 σ ∧ σ.inits = σ0.inits

/-- At `acctProc`'s second loop head (statement 65): the position in the records, no record found (`$i0 < 0`), the FD
record object `y0` with a `long` key. -/
def acctInv65 (st q o1 y0 : Addr) (_ : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ i m fsY v, fr.get 0 = some (.ref q) ∧ fr.get 3 = some (.ref o1) ∧ fr.get 17 = some (.ref st) ∧
    fr.get 8 = some (.int m) ∧ fr.get 10 = some (.int i) ∧ m.toInt < 0 ∧ 0 ≤ i.toInt ∧
    σ.heap y0 = some (.plain "Cbstm03b$FdAcctfileRec" fsY) ∧
    Fields.get fsY ("Cbstm03b$FdAcctfileRec", "fdAcctId") = some (.long v) ∧
    Keeps (fun x => x = y0) σ0 σ ∧ σ.inits = σ0.inits

/-- The first loop's variant: `2^32 + 2^31 - $i0`. -/
def acctVar33 (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 8 with
  | some (.int i) => (6442450944 - i.toInt).toNat
  | _ => 0

/-- The second loop's variant: `2^31 - i18`. -/
def acctVar65 (_ : List Value) (_ : State) (fr : Frame) (_ : State) : Nat :=
  match fr.get 10 with
  | some (.int i) => (2147483648 - i.toInt).toNat
  | _ => 0

def acctCutsT (st q o1 y0 : Addr) : TermCuts :=
  [(33, acctInv33 st q o1 y0, acctVar33), (65, acctInv65 st q o1 y0, acctVar65)]

/-- The termination paths of `acctProc` from statement `pc`, with the cut assertions `I`. -/
@[irreducible] def acctTWP (I : Cuts) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWPT Gen.prog acctCalleesT.env 1)
    Gen.Cbstm03b.«acctProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»
    I (fun _ => True) 200 pc fr σ

end EquivLean.Modernize.Cbstm03b.Java

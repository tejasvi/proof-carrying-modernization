import EquivLean.Modernize.Cbstm03b.Java.AcctBase

/-!
# CBSTM03B → Java, `acctProc`: the loop invariants

For fixed ghost values (`procSpecG`). Locals: `r2` 0 (area), `$l4` 1 (key value), `r4` 3 (ACCTFILE object),
`$i0` 8 (index; `-1` in the search), `i18` 10 (search index), `r3` 11 (key text), `r1` 17 (State), `r0` 18 (OPEN
outcomes).

* statement 33, the key loop: `i` characters of the key text read, `$l4 = jkey` of them; the heap has only grown;
* statement 65, the search: the first `j` records do not match; the FD record object holds the key value.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java.AcctP

open EquivLean.Modernize.Cbstm03b.Java

/-- The key text the loop reads: the first `LK-M03B-KEY-LN` characters of `LK-M03B-KEY`. -/
def keyText (a : List EquivLean.Cobol.Rec.FVal) : JStr :=
  cp037Str ((Model.aKey a).take (Model.aKeyLn a).toNat)

/-- The key loop's value. -/
def keyVal (a : List EquivLean.Cobol.Rec.FVal) : Nat := jkey (keyText a)

/-- The locals every path keeps: the arguments and the ACCTFILE object of the entry State. -/
def Locals (oe st q : Addr) (σ0 : State) (fr : Frame) : Prop :=
  fr.get 18 = some (.ref oe) ∧ fr.get 17 = some (.ref st) ∧ fr.get 0 = some (.ref q) ∧
    ∀ fs, σ0.heap st = some (.plain "Cbstm03b$State" fs) → fr.get 3 = Fields.get fs ("Cbstm03b$State", "acctFile")

/-- Statement 33, the head of the key loop. -/
def J33 (oe st q : Addr) (a : List EquivLean.Cobol.Rec.FVal) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  Model.aOp a = opReadK ∧ Locals oe st q σ0 fr ∧
  ∃ (kp : Addr) (i : Nat), fr.get 11 = some (.ref kp) ∧ σ.heap kp = some (.str (keyText a)) ∧
    fr.get 1 = some (.long (BitVec.ofNat 64 (jkey ((keyText a).take i)))) ∧
    fr.get 8 = some (.int (BitVec.ofNat 32 i)) ∧ i ≤ (keyText a).length ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- Statement 65, the head of the search: records `0 … j-1` do not match; the FD record object (in place) holds
the key value. -/
def J65 (oe st q : Addr) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal) (σ0 : State) (fr : Frame)
    (σ : State) : Prop :=
  Model.aOp a = opReadK ∧ s.acct.isOpen = true ∧ Locals oe st q σ0 fr ∧
  ∃ j : Nat, fr.get 8 = some (.int (BitVec.ofInt 32 (-1))) ∧ fr.get 10 = some (.int (BitVec.ofNat 32 j)) ∧
    j ≤ s.acct.recs.length ∧
    (∀ i, i < j → Model.numOf ((s.acct.recs.getD i []).getD 0 default) ≠ (keyVal a : Int)) ∧
    (∀ fs fdr fsr, σ0.heap st = some (.plain "Cbstm03b$State" fs) →
      Fields.get fs ("Cbstm03b$State", "fdAcctfileRec") = some (.ref fdr) →
      σ0.heap fdr = some (.plain "Cbstm03b$FdAcctfileRec" fsr) →
      Keeps (fun y => y = fdr) σ0 σ ∧
      σ.heap fdr = some (.plain "Cbstm03b$FdAcctfileRec"
        (Fields.set fsr ("Cbstm03b$FdAcctfileRec", "fdAcctId") (.long (BitVec.ofNat 64 (keyVal a)))))) ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics

/-- The invariants of `acctProc` for fixed ghost values. -/
def acctInv (oe st q : Addr) (s : Model.StM) (a : List EquivLean.Cobol.Rec.FVal) : Invariants :=
  [(33, fun _ σ0 fr σ => J33 oe st q a σ0 fr σ), (65, fun _ σ0 fr σ => J65 oe st q s a σ0 fr σ)]

/-- The paths of `acctProc` from statement `pc`, for fixed ghost values (irreducible: tactics that put the goal
in weak head normal form would run the method). -/
@[irreducible] def acctWP (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog acctCallees.env 1)
    Gen.Cbstm03b.«acctProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»
    ((acctInv oe st q s a).inst [.ref oe, .ref st, .ref q, opv] σ0)
    ((procSpecG ddAcct oe st q opv oeM s a).post [.ref oe, .ref st, .ref q, opv] σ0) 200 pc fr σ

end EquivLean.Modernize.Cbstm03b.Java.AcctP

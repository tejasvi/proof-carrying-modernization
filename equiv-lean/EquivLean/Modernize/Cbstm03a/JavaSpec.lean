import EquivLean.Modernize.Cbstm03a.JavaStatement
import EquivLean.Modernize.Cbstm03a.Model

/-!
# CBSTM03A → Java: the contract of `run`

`runSpec`: for inputs in the statement's domain, `Cbstm03a.run` returns a `Result` holding the
outputs of `Model.run` (`Model.lean`):
- `displays`: the displayed lines as UTF-16 strings (`jline`);
- `stmtFileWrites`: the 80-character `STMT-FILE` lines as UTF-16 strings;
- `htmlFileWrites`: the 100-character `HTML-FILE` lines as UTF-16 strings;
- `abended` = 1 exactly when the run abended (`CUSTFILE` or `ACCTFILE` key not found).

`JavaProof.lean` derives the generated statement from this contract.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbstm03a.Java

/-- A line of code points as a Java string (UTF-16 units). -/
def jline (l : List Nat) : JStr := l.map (BitVec.ofNat 16)

/-- The inputs of `run`: the four files as arrays of record objects, valid field values in the
statement's domain. -/
def RunIn (args : List Jimple.Value) (σ : Jimple.State)
    (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  ∃ a1 a2 a3 a4, args = [.ref a1, .ref a2, .ref a3, .ref a4] ∧
    TrnxFileAt σ a1 vals1 ∧ XrefFileAt σ a2 vals2 ∧
    CustFileAt σ a3 vals3 ∧ AcctFileAt σ a4 vals4 ∧
    (∀ v ∈ vals1, TrnxRecord.Valid v) ∧ (∀ v ∈ vals2, CardXrefRecord.Valid v) ∧
    (∀ v ∈ vals3, CustomerRecord.Valid v) ∧ (∀ v ∈ vals4, AccountRecord.Valid v) ∧
    EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4 ∧
    vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 27

/-- The contract of `Cbstm03a.run` (partial correctness). -/
def runSpec : Spec := Spec.of
  (fun args σ => ∃ vals1 vals2 vals3 vals4, RunIn args σ vals1 vals2 vals3 vals4 ∧
     ClinitRan Gen.prog "Cbstm03a" σ ∧ σ.initOf "Cbstm03a$Result" = .done ∧
     σ.initOf "Cbstm03a$AccountRecord" = .done ∧ σ.initOf "Cbstm03a$CardXrefRecord" = .done ∧
     σ.initOf "Cbstm03a$CustomerRecord" = .done ∧ σ.initOf "Cbstm03a$TrnxRecord" = .done)
  (fun args σ r σ' => ∀ vals1 vals2 vals3 vals4,
     RunIn args σ vals1 vals2 vals3 vals4 →
     let o := Model.run vals1 vals2 vals3 vals4
     ∃ res fs l k xs mods lw1 kw1 ws1 mw1 lw2 kw2 ws2 mw2, r = some (.ref res) ∧
       σ'.heap res = some (.plain "Cbstm03a$Result" fs) ∧
       Fields.get fs ("Cbstm03a$Result", "displays") = some (.ref l) ∧
       σ'.heap l = some (.list k xs mods) ∧
       Forall2 (JStrAt σ') xs (o.disp.map jline) ∧
       Fields.get fs ("Cbstm03a$Result", "stmtFileWrites") = some (.ref lw1) ∧
       σ'.heap lw1 = some (.list kw1 ws1 mw1) ∧
       Forall2 (JStrAt σ') ws1 (o.stmtWrites.map jline) ∧
       Fields.get fs ("Cbstm03a$Result", "htmlFileWrites") = some (.ref lw2) ∧
       σ'.heap lw2 = some (.list kw2 ws2 mw2) ∧
       Forall2 (JStrAt σ') ws2 (o.htmlWrites.map jline) ∧
       Fields.get fs ("Cbstm03a$Result", "abended") = some (.int (if o.abended then 1 else 0)))

end EquivLean.Modernize.Cbstm03a.Java

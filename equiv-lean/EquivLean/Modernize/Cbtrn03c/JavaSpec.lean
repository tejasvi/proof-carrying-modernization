import EquivLean.Modernize.Cbtrn03c.JavaStatement
import EquivLean.Modernize.Cbtrn03c.Model

/-!
# CBTRN03C → Java: the contract of `run`

`runSpec`: for valid input records, `Cbtrn03c.run` returns a `Result` holding the outputs of
`Model.run`:
- the displayed lines as UTF-16 strings;
- the report records written, as record objects holding the model's field values;
- `abended` = 1 exactly when the model's run abends.

It covers every valid input, the abends and the early stop included; the domain enters only in
`statement_of_sat`, which derives the generated statement from this contract.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java

/-- A line of code points as a Java string (UTF-16 units). -/
def jline (l : List Nat) : JStr := l.map (BitVec.ofNat 16)

/-- The inputs of `run`: the five files as arrays of record objects with valid field values. -/
def RunIn (args : List Jimple.Value) (σ : Jimple.State)
    (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  ∃ a1 a2 a3 a4 a5, args = [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5] ∧
    TransactFileAt σ a1 vals1 ∧ XrefFileAt σ a2 vals2 ∧ TrantypeFileAt σ a3 vals3 ∧
    TrancatgFileAt σ a4 vals4 ∧ DateParmsFileAt σ a5 vals5 ∧
    (∀ v ∈ vals1, TranRecord.Valid v) ∧ (∀ v ∈ vals2, CardXrefRecord.Valid v) ∧
    (∀ v ∈ vals3, TranTypeRecord.Valid v) ∧ (∀ v ∈ vals4, TranCatRecord.Valid v) ∧
    (∀ v ∈ vals5, WsDateparmRecord.Valid v)

/-- The contract of `Cbtrn03c.run` (partial correctness).  `Cbtrn03c` initialized is the
`initOf` conjunct of the statement's `ClinitRan`. -/
def runSpec : Spec := Spec.of
  (fun args σ => ∃ vals1 vals2 vals3 vals4 vals5, RunIn args σ vals1 vals2 vals3 vals4 vals5 ∧
     σ.initOf "Cbtrn03c" = .done ∧ σ.initOf "Cbtrn03c$Result" = .done ∧
     σ.initOf "Cbtrn03c$Ws" = .done ∧ σ.initOf "Cbtrn03c$TranRecord" = .done ∧
     σ.initOf "Cbtrn03c$CardXrefRecord" = .done ∧ σ.initOf "Cbtrn03c$TranTypeRecord" = .done ∧
     σ.initOf "Cbtrn03c$TranCatRecord" = .done ∧ σ.initOf "Cbtrn03c$WsDateparmRecord" = .done ∧
     σ.initOf "Cbtrn03c$FdReptfileRec" = .done)
  (fun args σ r σ' => ∀ vals1 vals2 vals3 vals4 vals5,
     RunIn args σ vals1 vals2 vals3 vals4 vals5 →
     let o := Model.run vals1 vals2 vals3 vals4 vals5
     ∃ res fs l k xs mods lw kw ws mw, r = some (.ref res) ∧
       σ'.heap res = some (.plain "Cbtrn03c$Result" fs) ∧
       Fields.get fs ("Cbtrn03c$Result", "displays") = some (.ref l) ∧
       σ'.heap l = some (.list k xs mods) ∧ Forall2 (JStrAt σ') xs (o.disp.map jline) ∧
       Fields.get fs ("Cbtrn03c$Result", "reportFileWrites") = some (.ref lw) ∧
       σ'.heap lw = some (.list kw ws mw) ∧
       Forall2 (JRecAt FdReptfileRec "Cbtrn03c$FdReptfileRec" σ') ws o.writes ∧
       Fields.get fs ("Cbtrn03c$Result", "abended") = some (.int (if o.abended then 1 else 0)))

end EquivLean.Modernize.Cbtrn03c.Java

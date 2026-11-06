import EquivLean.Modernize.Cbact04c.JavaStatement
import EquivLean.Modernize.Cbact04c.Model

/-!
# CBACT04C → Java: the contract of `run`

`runSpec`: for inputs in the statement's domain, `Cbact04c.run` returns a `Result` holding the
outputs of `Model.run`:
- the displayed lines as UTF-16 strings;
- the transactions written, as `TranRecord` objects holding the model's field values;
- the accounts rewritten, as `AccountRecord` objects;
- `abended` = 0.

`JavaProof.lean` derives the generated statement from this contract.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbact04c.Java

/-- A line of code points as a Java string (UTF-16 units). -/
def jline (l : List Nat) : JStr := l.map (BitVec.ofNat 16)

/-- The inputs of `run`: the four files as arrays of record objects, the linkage record, the
clock text; valid field values in the statement's domain. -/
def RunIn (args : List Jimple.Value) (σ : Jimple.State) (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal))
    (link1 : List EquivLean.Cobol.Rec.FVal) (clk : List UInt8) : Prop :=
  ∃ a1 a2 a3 a4 p1 cs, args = [.ref a1, .ref a2, .ref a3, .ref a4, .ref p1, .ref cs] ∧
    TcatbalFileAt σ a1 vals1 ∧ XrefFileAt σ a2 vals2 ∧ AccountFileAt σ a3 vals3 ∧
    DiscgrpFileAt σ a4 vals4 ∧ JRecAt ExternalParms "Cbact04c$ExternalParms" σ (.ref p1) link1 ∧
    JStrAt σ (.ref cs) (cp037Str clk) ∧ clk.length = 21 ∧
    (∀ v ∈ vals1, TranCatBalRecord.Valid v) ∧ (∀ v ∈ vals2, CardXrefRecord.Valid v) ∧
    (∀ v ∈ vals3, AccountRecord.Valid v) ∧ (∀ v ∈ vals4, DisGroupRecord.Valid v) ∧
    ExternalParms.Valid link1 ∧ Domain vals1 vals2 vals3 vals4 link1

/-- The contract of `Cbact04c.run` (partial correctness). -/
def runSpec : Spec := Spec.of
  (fun args σ => ∃ vals1 vals2 vals3 vals4 link1 clk, RunIn args σ vals1 vals2 vals3 vals4 link1 clk ∧
     σ.initOf "Cbact04c" = .done ∧ σ.initOf "Cbact04c$Result" = .done ∧
     σ.initOf "Cbact04c$AccountRecord" = .done ∧ σ.initOf "Cbact04c$CardXrefRecord" = .done ∧
     σ.initOf "Cbact04c$DisGroupRecord" = .done ∧ σ.initOf "Cbact04c$TranCatBalRecord" = .done ∧
     σ.initOf "Cbact04c$ExternalParms" = .done ∧ σ.initOf "Cbact04c$TranRecord" = .done)
  (fun args σ r σ' => ∀ vals1 vals2 vals3 vals4 link1 clk,
     RunIn args σ vals1 vals2 vals3 vals4 link1 clk →
     let o := Model.run vals1 vals2 vals3 vals4 (Model.parmOf link1) clk
     ∃ res fs l k xs mods lw kw ws mw lr kr rs mr, r = some (.ref res) ∧
       σ'.heap res = some (.plain "Cbact04c$Result" fs) ∧
       Fields.get fs ("Cbact04c$Result", "displays") = some (.ref l) ∧
       σ'.heap l = some (.list k xs mods) ∧ Forall2 (JStrAt σ') xs (o.disp.map jline) ∧
       Fields.get fs ("Cbact04c$Result", "transactFileWrites") = some (.ref lw) ∧
       σ'.heap lw = some (.list kw ws mw) ∧
       Forall2 (JRecAt TranRecord "Cbact04c$TranRecord" σ') ws o.writes ∧
       Fields.get fs ("Cbact04c$Result", "accountFileRewrites") = some (.ref lr) ∧
       σ'.heap lr = some (.list kr rs mr) ∧
       Forall2 (JRecAt AccountRecord "Cbact04c$AccountRecord" σ') rs o.rewrites ∧
       Fields.get fs ("Cbact04c$Result", "abended") = some (.int 0))

end EquivLean.Modernize.Cbact04c.Java

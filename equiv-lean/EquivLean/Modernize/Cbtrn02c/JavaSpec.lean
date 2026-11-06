import EquivLean.Modernize.Cbtrn02c.JavaStatement
import EquivLean.Modernize.Cbtrn02c.Model

/-!
# CBTRN02C → Java: the contract of `run`

`runSpec`: for inputs in the statement's domain, `Cbtrn02c.run` returns a `Result` holding the
outputs of `Model.run`:
- the displayed lines as UTF-16 strings;
- the records written to TRANSACT, DALYREJS and TCATBAL and rewritten in ACCOUNT and TCATBAL, as
  record objects holding the model's field values;
- `returnCode` = the model's RETURN-CODE, `abended` = 0.

`JavaProof.lean` derives the generated statement from this contract.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- A line of code points as a Java string (UTF-16 units). -/
def jline (l : List Nat) : JStr := l.map (BitVec.ofNat 16)

/-- The inputs of `run`: the four files as arrays of record objects and the clock text; valid
field values in the statement's domain. -/
def RunIn (args : List Jimple.Value) (σ : Jimple.State)
    (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)) (clk : List UInt8) : Prop :=
  ∃ a1 a2 a3 a4 cs, args = [.ref a1, .ref a2, .ref a3, .ref a4, .ref cs] ∧
    DalytranFileAt σ a1 vals1 ∧ XrefFileAt σ a2 vals2 ∧ AccountFileAt σ a3 vals3 ∧
    TcatbalFileAt σ a4 vals4 ∧ JStrAt σ (.ref cs) (cp037Str clk) ∧ CurrentDate clk ∧
    (∀ v ∈ vals1, DalytranRecord.Valid v) ∧ (∀ v ∈ vals2, CardXrefRecord.Valid v) ∧
    (∀ v ∈ vals3, AccountRecord.Valid v) ∧ (∀ v ∈ vals4, TranCatBalRecord.Valid v) ∧
    Domain vals1 vals2 vals3 vals4

/-- The list in field `f` of a `Result` holds record objects of schema `s` (class `cls`) with
the field values `vals`. -/
def ListOf (σ : Jimple.State) (fs : List (FieldKey × Jimple.Value)) (f : String) (s : Schema)
    (cls : ClassName) (vals : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  ∃ lw kw ws mw, Fields.get fs ("Cbtrn02c$Result", f) = some (.ref lw) ∧
    σ.heap lw = some (.list kw ws mw) ∧ Forall2 (JRecAt s cls σ) ws vals

/-- The contract of `Cbtrn02c.run` (partial correctness). -/
def runSpec : Spec := Spec.of
  (fun args σ => ∃ vals1 vals2 vals3 vals4 clk, RunIn args σ vals1 vals2 vals3 vals4 clk ∧
     σ.initOf "Cbtrn02c" = .done ∧ σ.initOf "Cbtrn02c$Result" = .done ∧
     σ.initOf "Cbtrn02c$AccountRecord" = .done ∧ σ.initOf "Cbtrn02c$CardXrefRecord" = .done ∧
     σ.initOf "Cbtrn02c$DalytranRecord" = .done ∧ σ.initOf "Cbtrn02c$TranCatBalRecord" = .done ∧
     σ.initOf "Cbtrn02c$RejectRecord" = .done ∧ σ.initOf "Cbtrn02c$TranRecord" = .done)
  (fun args σ r σ' => ∀ vals1 vals2 vals3 vals4 clk,
     RunIn args σ vals1 vals2 vals3 vals4 clk →
     let o := Model.run vals1 vals2 vals3 vals4 clk
     ∃ res fs l k xs mods, r = some (.ref res) ∧
       σ'.heap res = some (.plain "Cbtrn02c$Result" fs) ∧
       Fields.get fs ("Cbtrn02c$Result", "displays") = some (.ref l) ∧
       σ'.heap l = some (.list k xs mods) ∧ Forall2 (JStrAt σ') xs (o.disp.map jline) ∧
       ListOf σ' fs "transactFileWrites" TranRecord "Cbtrn02c$TranRecord" o.tranW ∧
       ListOf σ' fs "dalyrejsFileWrites" RejectRecord "Cbtrn02c$RejectRecord" o.rejW ∧
       ListOf σ' fs "tcatbalFileWrites" TranCatBalRecord "Cbtrn02c$TranCatBalRecord" o.catW ∧
       ListOf σ' fs "accountFileRewrites" AccountRecord "Cbtrn02c$AccountRecord" o.acctRW ∧
       ListOf σ' fs "tcatbalFileRewrites" TranCatBalRecord "Cbtrn02c$TranCatBalRecord" o.catRW ∧
       Fields.get fs ("Cbtrn02c$Result", "returnCode") = some (.int (BitVec.ofInt 32 o.rc)) ∧
       Fields.get fs ("Cbtrn02c$Result", "abended") = some (.int 0))

end EquivLean.Modernize.Cbtrn02c.Java

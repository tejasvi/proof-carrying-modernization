import EquivLean.Modernize.Cbact01c.JavaStatement
import EquivLean.Modernize.Cbact01c.Model

/-!
# CBACT01C → Java: the contract of `run`

`runSpec`: for an account file of record objects with valid field values, `Cbact01c.run` returns
a `Result` holding the outputs of `Model.run`:
- the displayed lines as UTF-16 strings;
- the records written to OUT-FILE, as record objects holding the model's field values;
- the records written to ARRY-FILE, as record objects with the `OCCURS` items in arrays
  (`JRecOccAt`) holding the model's field values (storage order, occurrences expanded);
- the records written to VBRC-FILE, as strings (the code points of the record's bytes);
- `abended` = 0.

`JavaProof.lean` derives the generated statement from this contract.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbact01c.Java

/-- A line of code points as a Java string (UTF-16 units). -/
def jline (l : List Nat) : JStr := l.map (BitVec.ofNat 16)

/-- The input of `run`: the account file as an array of record objects with valid field values. -/
def RunIn (args : List Jimple.Value) (σ : Jimple.State)
    (vals : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  ∃ a, args = [.ref a] ∧ AcctfileFileAt σ a vals ∧ ∀ v ∈ vals, AccountRecord.Valid v

/-- The list in field `f` of a `Result` holds strings with the lines `ls`. -/
def LinesOf (σ : Jimple.State) (fs : List (FieldKey × Jimple.Value)) (f : String)
    (ls : List (List Nat)) : Prop :=
  ∃ lw kw ws mw, Fields.get fs ("Cbact01c$Result", f) = some (.ref lw) ∧
    σ.heap lw = some (.list kw ws mw) ∧ Forall2 (JStrAt σ) ws (ls.map jline)

/-- The list in field `f` of a `Result` holds record objects of schema `s` (class `cls`) with
the field values `vals`. -/
def ListOf (σ : Jimple.State) (fs : List (FieldKey × Jimple.Value)) (f : String) (s : Schema)
    (cls : ClassName) (vals : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  ∃ lw kw ws mw, Fields.get fs ("Cbact01c$Result", f) = some (.ref lw) ∧
    σ.heap lw = some (.list kw ws mw) ∧ Forall2 (JRecAt s cls σ) ws vals

/-- The same for records with `OCCURS` items held in arrays. -/
def ListOccOf (σ : Jimple.State) (fs : List (FieldKey × Jimple.Value)) (f : String) (s : Schema)
    (cls : ClassName) (vals : List (List EquivLean.Cobol.Rec.FVal)) : Prop :=
  ∃ lw kw ws mw, Fields.get fs ("Cbact01c$Result", f) = some (.ref lw) ∧
    σ.heap lw = some (.list kw ws mw) ∧ Forall2 (JRecOccAt s cls σ) ws vals

/-- The contract of `Cbact01c.run` (partial correctness). -/
def runSpec : Spec := Spec.of
  (fun args σ => ∃ vals, RunIn args σ vals ∧
     σ.initOf "Cbact01c" = .done ∧ σ.initOf "Cbact01c$Result" = .done ∧
     σ.initOf "Cbact01c$AccountRecord" = .done ∧ σ.initOf "Cbact01c$ArrArrayRec" = .done ∧
     σ.initOf "Cbact01c$OutAcctRec" = .done)
  (fun args σ r σ' => ∀ vals, RunIn args σ vals →
     let o := Model.run vals
     ∃ res fs, r = some (.ref res) ∧ σ'.heap res = some (.plain "Cbact01c$Result" fs) ∧
       LinesOf σ' fs "displays" o.disp ∧
       ListOf σ' fs "outFileWrites" OutAcctRec "Cbact01c$OutAcctRec" o.outWrites ∧
       ListOccOf σ' fs "arryFileWrites" ArrArrayRec "Cbact01c$ArrArrayRec" o.arryWrites ∧
       LinesOf σ' fs "vbrcFileWrites" o.vbrcWrites ∧
       Fields.get fs ("Cbact01c$Result", "abended") = some (.int 0))

end EquivLean.Modernize.Cbact01c.Java

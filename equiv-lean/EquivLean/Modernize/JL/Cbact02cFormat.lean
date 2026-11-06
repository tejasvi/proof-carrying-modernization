-- Copied from JimpleLean (frozen snapshot ~/jimplelean_work/snapshots/JimpleLean-20261025T2312Z,
-- Examples/CardDemo/Cbact02cFormat.lean); proved by JimpleLean's own session.  Only the imports, the
-- program (`CB`, the same Jimple files, is equiv-lean's generated
-- `EquivLean.Modernize.Cbact02c.Java.Gen`) and the namespace differ (tools/modernize/import_jl.py).
/-
  Examples/CardDemo/Cbact02cFormat.lean

  `Cbact02c.formatCard(CardRecord)`: the record's line, against the contracts of `fix` and
  `zeroPad`. No loop.
-/
import EquivLean.Modernize.JL.Cbact02cFix
import EquivLean.Modernize.JL.Cbact02cHelpers

open Jimple

namespace EquivLean.Modernize.JL

def cardCls : ClassName := "Cbact02c$CardRecord"

/-- Field `f` of the record object at `c` (`null` if absent). -/
def fieldOf (σ : State) (c : Addr) (f : String) : Value :=
  match σ.heap c with
  | some (.plain _ fs) => (Fields.get fs (cardCls, f)).getD .null
  | _ => .null

/-- A `long` field of the record object at `c`. -/
def fieldLong (σ : State) (c : Addr) (f : String) : I64 :=
  match fieldOf σ c f with
  | .long x => x
  | _ => 0

/-- The line `formatCard` builds for the record at `c`. -/
def cardLine (σ : State) (c : Addr) : JStr :=
  fixStr (argText σ (fieldOf σ c "cardNum")) 16 ++ zpadStr (fieldLong σ c "cardAcctId").toNat 11 ++
    zpadStr (fieldLong σ c "cardCvvCd").toNat 3 ++
    fixStr (argText σ (fieldOf σ c "cardEmbossedName")) 50 ++
    fixStr (argText σ (fieldOf σ c "cardExpiraionDate")) 10 ++
    fixStr (argText σ (fieldOf σ c "cardActiveStatus")) 1 ++
    fixStr (argText σ (fieldOf σ c "filler1")) 59

/-- String field `f` of a record holds a string (of `int` length). -/
def StrField (σ : State) (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ x s, Fields.get fs (cardCls, f) = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

/-- `long` field `f` of a record holds a non-negative value. -/
def LongField (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ a : I64, Fields.get fs (cardCls, f) = some (.long a) ∧ 0 ≤ a.toInt

/-- A record as `formatCard` reads it (as the records of a CardDemo file are): its string fields
    hold strings, its `long` fields non-negative values. -/
def CardOk (σ : State) (c : Addr) : Prop :=
  ∃ fs, σ.heap c = some (.plain cardCls fs) ∧ StrField σ fs "cardNum" ∧ LongField fs "cardAcctId" ∧
    LongField fs "cardCvvCd" ∧ StrField σ fs "cardEmbossedName" ∧ StrField σ fs "cardExpiraionDate" ∧
    StrField σ fs "cardActiveStatus" ∧ StrField σ fs "filler1"

def fixSig : MethodSig :=
  ⟨"Cbact02c", .cls "java.lang.String", "fix", [.cls "java.lang.String", .prim .int]⟩
def zeroPadSig : MethodSig :=
  ⟨"Cbact02c", .cls "java.lang.String", "zeroPad", [.prim .long, .prim .int]⟩

/-- The callee contracts of `formatCard`. -/
def fcCallees : Contracts := [(fixSig, fixSpec), (zeroPadSig, zeroPadSpec)]

abbrev formatCardRef : MethodRef := EquivLean.Modernize.Cbact02c.Java.Gen.Cbact02c.«formatCard(Cbact02c$CardRecord)».ref

def formatCardSpec : Spec := Spec.of
  (fun args σ => ∃ c, args = [.ref c] ∧ CardOk σ c ∧ σ.initOf "Cbact02c" = .done)
  (fun args σ r σ' => ∀ c, args = [.ref c] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (cardLine σ c)) ∧ σ.next ≤ x ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.trace true in
theorem formatCard_vc : MethodVC EquivLean.Modernize.Cbact02c.Java.Gen.prog fcCallees.env 0 formatCardRef formatCardSpec [] 80 := by
  jverify [ite_nat_ne, formatCardSpec, fcCallees, fixSig, zeroPadSig, fixSpec, zeroPadSpec, CardOk, StrField,
    LongField, StrOk, cardLine, fieldOf, fieldLong, argText, Grows, cardCls]

end EquivLean.Modernize.JL

#print axioms EquivLean.Modernize.JL.formatCard_vc

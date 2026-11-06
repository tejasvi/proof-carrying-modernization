import EquivLean.Modernize.Cbtrn01c.JavaRunZoned

/-!
# CBTRN01C → Java: `formatDalytran`

The record's line: its string fields and the digits of its numeric fields (`digits`, and
`signedZoned` for the amount), against the contracts of `digits` and `signedZoned`. No loop.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn01c.Java

theorem signedZoned_sat : Sat Gen.prog signedZonedRef signedZonedSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [szCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact digits_ok)) signedZoned_vc

def signedZonedSig : MethodSig :=
  ⟨"Cbtrn01c", .cls "java.lang.String", "signedZoned", [.prim .long, .prim .int]⟩

set_option maxHeartbeats 0 in
theorem signedZoned_ok : ContractOK Gen.prog signedZonedSig signedZonedSpec := by
  jcontract_ok [signedZoned_sat]

def dalCls : ClassName := "Cbtrn01c$DalytranRecord"

/-- Field `f` of the record object at `c` (`null` if absent). -/
def fieldOf (σ : State) (c : Addr) (f : String) : Value :=
  match σ.heap c with
  | some (.plain _ fs) => (Fields.get fs (dalCls, f)).getD .null
  | _ => .null

/-- A `long` field of the record object at `c`. -/
def fieldLong (σ : State) (c : Addr) (f : String) : I64 :=
  match fieldOf σ c f with
  | .long x => x
  | _ => 0

/-- The text of a string value (`""` for `null` and non-strings). -/
def argText (σ : State) (v : Value) : JStr := (strOf σ v).getD []

/-- The line `formatDalytran` builds for the record at `c`. -/
def dalLine (σ : State) (c : Addr) : JStr :=
  argText σ (fieldOf σ c "dalytranId") ++ argText σ (fieldOf σ c "dalytranTypeCd") ++
  zpadJ (fieldLong σ c "dalytranCatCd").toInt.natAbs 4 ++
  argText σ (fieldOf σ c "dalytranSource") ++ argText σ (fieldOf σ c "dalytranDesc") ++
  szJ (fieldLong σ c "dalytranAmt") 11 ++
  zpadJ (fieldLong σ c "dalytranMerchantId").toInt.natAbs 9 ++
  argText σ (fieldOf σ c "dalytranMerchantName") ++ argText σ (fieldOf σ c "dalytranMerchantCity") ++
  argText σ (fieldOf σ c "dalytranMerchantZip") ++ argText σ (fieldOf σ c "dalytranCardNum") ++
  argText σ (fieldOf σ c "dalytranOrigTs") ++ argText σ (fieldOf σ c "dalytranProcTs") ++
  argText σ (fieldOf σ c "filler1")

/-- String field `f` of a record holds a string. -/
def StrField (σ : State) (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ x s, Fields.get fs (dalCls, f) = some (.ref x) ∧ σ.heap x = some (.str s)

/-- `long` field `f` of a record holds a value other than `Long.MIN_VALUE`. -/
def LongField (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ a : I64, Fields.get fs (dalCls, f) = some (.long a) ∧ -9223372036854775808 < a.toInt

/-- A record as `formatDalytran` reads it. -/
def DalOk (σ : State) (c : Addr) : Prop :=
  ∃ fs, σ.heap c = some (.plain dalCls fs) ∧ StrField σ fs "dalytranId" ∧
    StrField σ fs "dalytranTypeCd" ∧ LongField fs "dalytranCatCd" ∧
    StrField σ fs "dalytranSource" ∧ StrField σ fs "dalytranDesc" ∧ LongField fs "dalytranAmt" ∧
    LongField fs "dalytranMerchantId" ∧ StrField σ fs "dalytranMerchantName" ∧
    StrField σ fs "dalytranMerchantCity" ∧ StrField σ fs "dalytranMerchantZip" ∧
    StrField σ fs "dalytranCardNum" ∧ StrField σ fs "dalytranOrigTs" ∧
    StrField σ fs "dalytranProcTs" ∧ StrField σ fs "filler1"

def fdCallees : Contracts := [(digitsSig, digitsSpec), (signedZonedSig, signedZonedSpec)]

abbrev formatDalytranRef : MethodRef :=
  Gen.Cbtrn01c.«formatDalytran(Cbtrn01c$DalytranRecord)».ref

def formatDalytranSpec : Spec := Spec.of
  (fun args σ => ∃ c, args = [.ref c] ∧ DalOk σ c ∧ σ.initOf "Cbtrn01c" = .done)
  (fun args σ r σ' => ∀ c, args = [.ref c] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (dalLine σ c)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧
       σ'.initOf "Cbtrn01c" = σ.initOf "Cbtrn01c")

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem formatDalytran_vc :
    MethodVC Gen.prog fdCallees.env 0 formatDalytranRef formatDalytranSpec [] 80 := by
  jverify [formatDalytranSpec, fdCallees, digitsSig, signedZonedSig, digitsSpec, signedZonedSpec,
    DalOk, StrField, LongField, dalLine, fieldOf, fieldLong, argText, Grows, dalCls,
    Native.valueOfArg, Native.valueOfObj, Native.valueOfObjN, Native.nObjStr, Native.primStr,
    JType.isRef]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn01c.Java

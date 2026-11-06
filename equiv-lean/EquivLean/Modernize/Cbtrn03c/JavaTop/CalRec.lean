import EquivLean.Modernize.Cbtrn03c.JavaTop.CalZoned
import EquivLean.Modernize.Cbtrn03c.JavaTop.CalFind

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: the contract of `tranRecordText`

`tranRecordText(t)`: the record's text (its string fields, the digits of `TRAN-CAT-CD` and
`TRAN-MERCHANT-ID`, the zoned amount), against the contracts of `digits` and `zoned`.  Ported from
cir-repin's `T3/Rec.lean` (a new string, `Agree` as the frame); then the model's DISPLAY line
(`Glue.tran_cps`): the record's fields as `TranFields` gives them, the numeric fields' texts
(`text_unsigned`, `Glue.amt_cps`).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

def tranCls : ClassName := "Cbtrn03c$TranRecord"

/-- String field `f` of a transaction record holds a string. -/
def StrF (σ : State) (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ x s, Fields.get fs (tranCls, f) = some (.ref x) ∧ σ.heap x = some (.str s)

/-- `long` field `f` of a transaction record holds a value other than `Long.MIN_VALUE`. -/
def LongF (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ a : I64, Fields.get fs (tranCls, f) = some (.long a) ∧ -9223372036854775808 < a.toInt

/-- A transaction record as `tranRecordText` reads it. -/
def TranOk (σ : State) (c : Addr) : Prop :=
  ∃ fs, σ.heap c = some (.plain tranCls fs) ∧ StrF σ fs "tranId" ∧ StrF σ fs "tranTypeCd" ∧
    LongF fs "tranCatCd" ∧ StrF σ fs "tranSource" ∧ StrF σ fs "tranDesc" ∧ LongF fs "tranAmt" ∧
    LongF fs "tranMerchantId" ∧ StrF σ fs "tranMerchantName" ∧ StrF σ fs "tranMerchantCity" ∧
    StrF σ fs "tranMerchantZip" ∧ StrF σ fs "tranCardNum" ∧ StrF σ fs "tranOrigTs" ∧
    StrF σ fs "tranProcTs" ∧ StrF σ fs "filler1"

/-- The text `tranRecordText` builds for the record at `c`. -/
def tranText (σ : State) (c : Addr) : JStr :=
  fieldStr σ tranCls "tranId" (.ref c) ++ fieldStr σ tranCls "tranTypeCd" (.ref c) ++
  zpadJ (fieldLongV σ tranCls "tranCatCd" (.ref c)).toInt.natAbs 4 ++
  fieldStr σ tranCls "tranSource" (.ref c) ++ fieldStr σ tranCls "tranDesc" (.ref c) ++
  zonedJ (fieldLongV σ tranCls "tranAmt" (.ref c)) 11 ++
  zpadJ (fieldLongV σ tranCls "tranMerchantId" (.ref c)).toInt.natAbs 9 ++
  fieldStr σ tranCls "tranMerchantName" (.ref c) ++ fieldStr σ tranCls "tranMerchantCity" (.ref c) ++
  fieldStr σ tranCls "tranMerchantZip" (.ref c) ++ fieldStr σ tranCls "tranCardNum" (.ref c) ++
  fieldStr σ tranCls "tranOrigTs" (.ref c) ++ fieldStr σ tranCls "tranProcTs" (.ref c) ++
  fieldStr σ tranCls "filler1" (.ref c)

abbrev tranRecordTextRef : MethodRef :=
  Gen.Cbtrn03c.«tranRecordText(Cbtrn03c$TranRecord)».ref

def trCallees : Contracts := [(digitsSig, digitsSpec), (zonedSig, zonedSpec)]

/-- `tranRecordText` (cir-repin's `tranRecordTextSpec`, a new string, `Agree` as the frame). -/
def tranRecordTextSpec : Spec := Spec.of
  (fun args σ => ∃ c, args = [.ref c] ∧ TranOk σ c ∧ σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ c, args = [.ref c] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (tranText σ c)) ∧ σ.next ≤ x ∧
       σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem tranRecordText_vc :
    MethodVC Gen.prog trCallees.env 0 tranRecordTextRef tranRecordTextSpec [] 80 := by
  jverify [tranRecordTextSpec, trCallees, digitsSig, zonedSig, digitsSpec, zonedSpec, TranOk, StrF,
    LongF, tranText, fieldStr, fieldLongV, argText, Agree, tranCls, Native.valueOfArg,
    Native.primStr, JType.isRef]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | (intro h; subst h; jomega)
    | skip

theorem tranRecordText_sat : Sat Gen.prog tranRecordTextRef tranRecordTextSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    simp only [trCallees, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true]
    exact ⟨digitsC_ok, zonedC_ok⟩)) tranRecordText_vc

end EquivLean.Modernize.Cbtrn03c.Java.Top.Cal

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.Cal.tranRecordText_sat

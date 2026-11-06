import EquivLean.Modernize.Cbtrn02c.Any.JavaRunF

/-!
# CBTRN02C → Java: `dalytranText`

`dalytranText(d)`: the 350 characters of the daily transaction record at `c` (`dtLine σ c`): each
alphanumeric field fitted to its length, the numeric fields as digits (`padNum`) or signed zoned
(`zonedSigned`).  Cut points right after each call (the builder so far, the string just returned)
keep each path to one call.
-/

open Jimple

namespace EquivLean.Modernize.Cbtrn02c.Java

def fitSig : MethodSig := ⟨"Cbtrn02c", .cls "java.lang.String", "fit", [.cls "java.lang.String", .prim .int]⟩
def zonedSignedSig : MethodSig :=
  ⟨"Cbtrn02c", .cls "java.lang.String", "zonedSigned", [.prim .long, .prim .int]⟩

set_option maxHeartbeats 0 in
theorem fitF_ok : ContractOK Gen.prog fitSig fitSpecF := by jcontract_ok [fitF_sat]

theorem zonedSigned_sat : Sat Gen.prog zonedSignedRef zonedSignedSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [szCallees, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    exact padNum_ok)) zonedSigned_vc
set_option maxHeartbeats 0 in
theorem zonedSigned_ok : ContractOK Gen.prog zonedSignedSig zonedSignedSpec := by
  jcontract_ok [zonedSigned_sat]

def dtCls : ClassName := "Cbtrn02c$DalytranRecord"

/-- Field `f` of the record object at `c` (`null` if absent). -/
def fieldOf (σ : State) (c : Addr) (f : String) : Value :=
  match σ.heap c with
  | some (.plain _ fs) => (Fields.get fs (dtCls, f)).getD .null
  | _ => .null

/-- A `long` field of the record object at `c`. -/
def fieldLong (σ : State) (c : Addr) (f : String) : I64 :=
  match fieldOf σ c f with
  | .long x => x
  | _ => 0

/-- String field `f` of a record holds a string (shorter than `2^31`). -/
def StrField (σ : State) (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ x s, Fields.get fs (dtCls, f) = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

/-- `long` field `f` of a record holds a value other than `Long.MIN_VALUE`. -/
def LongField (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ a : I64, Fields.get fs (dtCls, f) = some (.long a) ∧ -9223372036854775808 < a.toInt

/-- A daily transaction record as `dalytranText` reads it. -/
def DalOk (σ : State) (c : Addr) : Prop :=
  ∃ fs, σ.heap c = some (.plain dtCls fs) ∧ StrField σ fs "dalytranId" ∧
    StrField σ fs "dalytranTypeCd" ∧
    LongField fs "dalytranCatCd" ∧
    StrField σ fs "dalytranSource" ∧
    StrField σ fs "dalytranDesc" ∧
    LongField fs "dalytranAmt" ∧
    LongField fs "dalytranMerchantId" ∧
    StrField σ fs "dalytranMerchantName" ∧
    StrField σ fs "dalytranMerchantCity" ∧
    StrField σ fs "dalytranMerchantZip" ∧
    StrField σ fs "dalytranCardNum" ∧
    StrField σ fs "dalytranOrigTs" ∧
    StrField σ fs "dalytranProcTs" ∧
    StrField σ fs "filler1"

/-- The text `dalytranText` builds for the record at `c`. -/
def dtLine (σ : State) (c : Addr) : JStr :=
  fitJ (argText σ (fieldOf σ c "dalytranId")) 16 ++
  fitJ (argText σ (fieldOf σ c "dalytranTypeCd")) 2 ++
  zpadJ (fieldLong σ c "dalytranCatCd").toInt.natAbs 4 ++
  fitJ (argText σ (fieldOf σ c "dalytranSource")) 10 ++
  fitJ (argText σ (fieldOf σ c "dalytranDesc")) 100 ++
  szJ (fieldLong σ c "dalytranAmt") 11 ++
  zpadJ (fieldLong σ c "dalytranMerchantId").toInt.natAbs 9 ++
  fitJ (argText σ (fieldOf σ c "dalytranMerchantName")) 50 ++
  fitJ (argText σ (fieldOf σ c "dalytranMerchantCity")) 50 ++
  fitJ (argText σ (fieldOf σ c "dalytranMerchantZip")) 10 ++
  fitJ (argText σ (fieldOf σ c "dalytranCardNum")) 16 ++
  fitJ (argText σ (fieldOf σ c "dalytranOrigTs")) 26 ++
  fitJ (argText σ (fieldOf σ c "dalytranProcTs")) 26 ++
  fitJ (argText σ (fieldOf σ c "filler1")) 20

abbrev dalytranTextRef : MethodRef := Gen.Cbtrn02c.«dalytranText(Cbtrn02c$DalytranRecord)».ref

def dtCallees : Contracts := [(fitSig, fitSpecF), (padNumSig, padNumSpec), (zonedSignedSig, zonedSignedSpec)]

def dalytranTextSpec : Spec := Spec.of
  (fun args σ => ∃ c, args = [.ref c] ∧ DalOk σ c ∧ σ.initOf "Cbtrn02c" = .done)
  (fun args σ r σ' => ∀ c, args = [.ref c] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (dtLine σ c)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics ∧ σ'.initOf "Cbtrn02c" = σ.initOf "Cbtrn02c")

/-- Right after a call: the builder holds the text of the fields before, local 3 the string the
call returned. -/
def dtCut (pre ret : State → Addr → JStr) : List Value → State → Frame → State → Prop :=
  fun args σ0 fr σ => ∀ c, args = [.ref c] →
    ∃ s, fr.get 0 = some (.ref c) ∧ fr.get 1 = some (.ref σ0.next) ∧ fr.get 3 = some (.ref s) ∧
      σ.heap s = some (.str (ret σ0 c)) ∧
      σ.heap σ0.next = some (.builder "java.lang.StringBuilder" (pre σ0 c)) ∧
      Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧
      σ.initOf "Cbtrn02c" = σ0.initOf "Cbtrn02c" ∧ σ0.initOf "Cbtrn02c" = .done

def dtRet0 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "dalytranId")) 16
def dtRet1 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "dalytranTypeCd")) 2
def dtRet2 (σ : State) (c : Addr) : JStr := zpadJ (fieldLong σ c "dalytranCatCd").toInt.natAbs 4
def dtRet3 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "dalytranSource")) 10
def dtRet4 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "dalytranDesc")) 100
def dtRet5 (σ : State) (c : Addr) : JStr := szJ (fieldLong σ c "dalytranAmt") 11
def dtRet6 (σ : State) (c : Addr) : JStr := zpadJ (fieldLong σ c "dalytranMerchantId").toInt.natAbs 9
def dtRet7 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "dalytranMerchantName")) 50
def dtRet8 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "dalytranMerchantCity")) 50
def dtRet9 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "dalytranMerchantZip")) 10
def dtRet10 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "dalytranCardNum")) 16
def dtRet11 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "dalytranOrigTs")) 26
def dtRet12 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "dalytranProcTs")) 26
def dtRet13 (σ : State) (c : Addr) : JStr := fitJ (argText σ (fieldOf σ c "filler1")) 20
def dtPre2 (σ : State) (c : Addr) : JStr := dtRet0 σ c ++ dtRet1 σ c
def dtPre5 (σ : State) (c : Addr) : JStr := dtRet0 σ c ++ dtRet1 σ c ++ dtRet2 σ c ++ dtRet3 σ c ++ dtRet4 σ c
def dtPre8 (σ : State) (c : Addr) : JStr := dtRet0 σ c ++ dtRet1 σ c ++ dtRet2 σ c ++ dtRet3 σ c ++ dtRet4 σ c ++ dtRet5 σ c ++ dtRet6 σ c ++ dtRet7 σ c
def dtPre11 (σ : State) (c : Addr) : JStr := dtRet0 σ c ++ dtRet1 σ c ++ dtRet2 σ c ++ dtRet3 σ c ++ dtRet4 σ c ++ dtRet5 σ c ++ dtRet6 σ c ++ dtRet7 σ c ++ dtRet8 σ c ++ dtRet9 σ c ++ dtRet10 σ c

def dtInv : Invariants :=
  [(11, dtCut dtPre2 dtRet2),
   (20, dtCut dtPre5 dtRet5),
   (29, dtCut dtPre8 dtRet8),
   (38, dtCut dtPre11 dtRet11)]

theorem dtLine_eq_cut (σ : State) (c : Addr) :
    dtLine σ c = dtPre11 σ c ++ dtRet11 σ c ++ dtRet12 σ c ++ dtRet13 σ c := by
  simp only [dtLine, dtPre11, dtRet0, dtRet1, dtRet2, dtRet3, dtRet4, dtRet5, dtRet6, dtRet7, dtRet8, dtRet9, dtRet10, dtRet11, dtRet12, dtRet13, List.append_assoc]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem dalytranText_vc :
    MethodVC Gen.prog dtCallees.env 0 dalytranTextRef dalytranTextSpec dtInv 40 := by
  jverify [dalytranTextSpec, dtCallees, fitSig, fitSpecF, padNumSig, padNumSpec, zonedSignedSig,
    zonedSignedSpec, dtInv, dtCut, dtPre2, dtPre5, dtPre8, dtPre11, dtRet0, dtRet1, dtRet2, dtRet3, dtRet4, dtRet5, dtRet6, dtRet7, dtRet8, dtRet9, dtRet10, dtRet11, dtRet12, dtRet13,
    dtLine_eq_cut, DalOk, StrField, LongField, fieldOf, fieldLong, argText, strOfV, Grows, dtCls,
    Native.valueOfArg, valueOfObj_eq, valueOfObjN_ref, JType.isRef, List.append_assoc]

end EquivLean.Modernize.Cbtrn02c.Java

/-
  Examples/CardDemo/Cbcus01cFormat.lean

  `Cbcus01c.fmtRecord(CustomerRecord)`: the record's line (19 fields), against the contracts of
  `fmtNum` and `fit`. No loop.
-/
import Examples.CardDemo.Cbcus01cHelpers

open Jimple

namespace Examples.CardDemo

def custCls : ClassName := "Cbcus01c$CustomerRecord"

/-- Field `f` of the customer record object at `c` (`null` if absent). -/
def cfieldOf (σ : State) (c : Addr) (f : String) : Value :=
  match σ.heap c with
  | some (.plain _ fs) => (Fields.get fs (custCls, f)).getD .null
  | _ => .null

/-- A `long` field of the customer record object at `c`. -/
def cfieldLong (σ : State) (c : Addr) (f : String) : I64 :=
  match cfieldOf σ c f with
  | .long x => x
  | _ => 0

/-- The text of string field `f`, cut or padded to `n` characters. -/
def ctext (σ : State) (c : Addr) (f : String) (n : Nat) : JStr := fixStr (argText σ (cfieldOf σ c f)) n

/-- The line `fmtRecord` builds for the customer record at `c`. Irreducible: proofs about
    `run` keep it folded and carry it across states with `custLine_frame`. -/
@[irreducible] def custLine (σ : State) (c : Addr) : JStr :=
  zpadStr (cfieldLong σ c "custId").toNat 9 ++ ctext σ c "custFirstName" 25 ++
    ctext σ c "custMiddleName" 25 ++ ctext σ c "custLastName" 25 ++ ctext σ c "custAddrLine1" 50 ++
    ctext σ c "custAddrLine2" 50 ++ ctext σ c "custAddrLine3" 50 ++ ctext σ c "custAddrStateCd" 2 ++
    ctext σ c "custAddrCountryCd" 3 ++ ctext σ c "custAddrZip" 10 ++ ctext σ c "custPhoneNum1" 15 ++
    ctext σ c "custPhoneNum2" 15 ++ zpadStr (cfieldLong σ c "custSsn").toNat 9 ++
    ctext σ c "custGovtIssuedId" 20 ++ ctext σ c "custDobYyyyMmDd" 10 ++
    ctext σ c "custEftAccountId" 10 ++ ctext σ c "custPriCardHolderInd" 1 ++
    zpadStr (cfieldLong σ c "custFicoCreditScore").toNat 3 ++ ctext σ c "filler1" 168

/-- String field `f` of a customer record holds a string (of `int` length). -/
def CStrField (σ : State) (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ x s, Fields.get fs (custCls, f) = some (.ref x) ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

/-- `long` field `f` of a customer record holds a non-negative value. -/
def CLongField (fs : List (FieldKey × Value)) (f : String) : Prop :=
  ∃ a : I64, Fields.get fs (custCls, f) = some (.long a) ∧ 0 ≤ a.toInt

/-- A customer record as `fmtRecord` reads it (as the records of the customer file are).
    Irreducible, like `custLine` (`CustOk.mono`). -/
@[irreducible] def CustOk (σ : State) (c : Addr) : Prop :=
  ∃ fs, σ.heap c = some (.plain custCls fs) ∧ CLongField fs "custId" ∧
    CStrField σ fs "custFirstName" ∧ CStrField σ fs "custMiddleName" ∧
    CStrField σ fs "custLastName" ∧ CStrField σ fs "custAddrLine1" ∧
    CStrField σ fs "custAddrLine2" ∧ CStrField σ fs "custAddrLine3" ∧
    CStrField σ fs "custAddrStateCd" ∧ CStrField σ fs "custAddrCountryCd" ∧
    CStrField σ fs "custAddrZip" ∧ CStrField σ fs "custPhoneNum1" ∧
    CStrField σ fs "custPhoneNum2" ∧ CLongField fs "custSsn" ∧
    CStrField σ fs "custGovtIssuedId" ∧ CStrField σ fs "custDobYyyyMmDd" ∧
    CStrField σ fs "custEftAccountId" ∧ CStrField σ fs "custPriCardHolderInd" ∧
    CLongField fs "custFicoCreditScore" ∧ CStrField σ fs "filler1"

/-! ### The record and its line in a later state (`jframe`) -/

theorem cfieldOf_agree {σ σ' : State} {c : Addr} {o : Obj} (hc : σ.heap c = some o)
    (ha : Agree σ σ') (f : String) : cfieldOf σ' c f = cfieldOf σ c f := by
  unfold cfieldOf; rw [ha c (State.lt_next_of_heap hc)]

theorem cfieldLong_agree {σ σ' : State} {c : Addr} {o : Obj} (hc : σ.heap c = some o)
    (ha : Agree σ σ') (f : String) : cfieldLong σ' c f = cfieldLong σ c f := by
  unfold cfieldLong; rw [cfieldOf_agree hc ha]

theorem ctext_agree {σ σ' : State} {c : Addr} {fs : List (FieldKey × Value)}
    (hc : σ.heap c = some (.plain custCls fs)) (ha : Agree σ σ') {f : String}
    (hf : CStrField σ fs f) (n : Nat) : ctext σ' c f n = ctext σ c f n := by
  obtain ⟨x, s, hfx, hx, -⟩ := hf
  unfold ctext
  rw [cfieldOf_agree hc ha]
  have e : cfieldOf σ c f = .ref x := by simp [cfieldOf, hc, hfx]
  rw [e]
  unfold argText strOf
  rw [ha x (State.lt_next_of_heap hx)]

theorem CStrField.mono {σ σ' : State} {fs : List (FieldKey × Value)} {f : String}
    (h : CStrField σ fs f) (ha : Agree σ σ') : CStrField σ' fs f := by
  obtain ⟨x, s, h1, h2, h3⟩ := h
  exact ⟨x, s, h1, by rw [ha x (State.lt_next_of_heap h2), h2], h3⟩

@[jframe] theorem CustOk.mono {σ σ' : State} {c : Addr} (h : CustOk σ c) (ha : Agree σ σ') :
    CustOk σ' c := by
  unfold CustOk at h ⊢
  obtain ⟨fs, hc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := h
  exact ⟨fs, by rw [ha c (State.lt_next_of_heap hc), hc], h1, h2.mono ha, h3.mono ha, h4.mono ha,
    h5.mono ha, h6.mono ha, h7.mono ha, h8.mono ha, h9.mono ha, h10.mono ha, h11.mono ha,
    h12.mono ha, h13, h14.mono ha, h15.mono ha, h16.mono ha, h17.mono ha, h18, h19.mono ha⟩

@[jframe] theorem custLine_frame {σ σ' : State} {c : Addr} (h : CustOk σ c) (ha : Agree σ σ') :
    custLine σ' c = custLine σ c := by
  unfold CustOk at h
  obtain ⟨fs, hc, -, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -, h14, h15, h16, h17, -,
    h19⟩ := h
  unfold custLine
  simp only [cfieldLong_agree hc ha, ctext_agree hc ha h2, ctext_agree hc ha h3,
    ctext_agree hc ha h4, ctext_agree hc ha h5, ctext_agree hc ha h6, ctext_agree hc ha h7,
    ctext_agree hc ha h8, ctext_agree hc ha h9, ctext_agree hc ha h10, ctext_agree hc ha h11,
    ctext_agree hc ha h12, ctext_agree hc ha h14, ctext_agree hc ha h15, ctext_agree hc ha h16,
    ctext_agree hc ha h17, ctext_agree hc ha h19]

/-- The callee contracts of `fmtRecord`. -/
def frCallees : Contracts := [(cuFmtNumSig, zeroPadSpec), (cuFitSig, fitSpec)]

abbrev cuFmtRecordRef : MethodRef := CU.Cbcus01c.«fmtRecord(Cbcus01c$CustomerRecord)».ref

def fmtRecordSpec : Spec := Spec.of
  (fun args σ => ∃ c, args = [.ref c] ∧ CustOk σ c ∧ σ.initOf "Cbcus01c" = .done)
  (fun args σ r σ' => ∀ c, args = [.ref c] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (custLine σ c)) ∧ σ.next ≤ x ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem cu_fmtRecord_vc : MethodVC CU.prog frCallees.env 0 cuFmtRecordRef fmtRecordSpec [] 120 := by
  jverify [ite_nat_ne, fmtRecordSpec, frCallees, cuFmtNumSig, cuFitSig, CustOk, CStrField, CLongField, StrOk,
    custLine, ctext, cfieldOf, cfieldLong, argText, Grows, custCls]

end Examples.CardDemo

#print axioms Examples.CardDemo.cu_fmtRecord_vc

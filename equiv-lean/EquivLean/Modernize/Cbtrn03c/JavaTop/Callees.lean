import EquivLean.Modernize.Cbtrn03c.JavaTop.Run

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java, top layer: the helper contracts the top layer calls

Stated for the top layer's use: results as model values where the model has them, premises only
where a call is made at a cut of its own (the premise is then a hypothesis of the call's state)
or right at a method's entry (`tranRecordText`, statement 6 of `processDetail`: `TranFieldsI`, a
folded copy of `TranFields` that `jvc` leaves alone).  Each follows from cir-repin's contract of
the same method (`T3/*.lean`) by the rule of consequence and the glue lemmas (to do at assembly).
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

/-- `TranFields`, folded: a premise `jvc` matches against a hypothesis (it destructures
`TranFields` itself in the segments that read the record's fields). -/
@[irreducible] def TranFieldsI (σ : State) (c : Addr) (t : List EquivLean.Cobol.Rec.FVal) : Prop :=
  TranFields σ c t

theorem TranFieldsI.intro {σ : State} {c : Addr} {t : List EquivLean.Cobol.Rec.FVal}
    (h : TranFields σ c t) : TranFieldsI σ c t := by unfold TranFieldsI; exact h

/-! ## Signatures -/

def spacesSig : MethodSig := ⟨"Cbtrn03c", .cls "java.lang.String", "spaces", [.prim .int]⟩
def blankTranSig : MethodSig := ⟨"Cbtrn03c", .cls "Cbtrn03c$TranRecord", "blankTran", []⟩
def compareEbcdicSig : MethodSig :=
  ⟨"Cbtrn03c", .prim .int, "compareEbcdic", [.cls "java.lang.String", .cls "java.lang.String"]⟩
def tranRecordTextSig : MethodSig :=
  ⟨"Cbtrn03c", .cls "java.lang.String", "tranRecordText", [.cls "Cbtrn03c$TranRecord"]⟩
def ioStatusLineSig : MethodSig :=
  ⟨"Cbtrn03c", .cls "java.lang.String", "ioStatusLine", [.cls "java.lang.String"]⟩
def digitsSig : MethodSig :=
  ⟨"Cbtrn03c", .cls "java.lang.String", "digits", [.prim .long, .prim .int]⟩
def findXrefSig : MethodSig :=
  ⟨"Cbtrn03c", .prim .int, "findXref", [.array (.cls "Cbtrn03c$CardXrefRecord"), .cls "java.lang.String"]⟩
def findTranTypeSig : MethodSig :=
  ⟨"Cbtrn03c", .prim .int, "findTranType",
    [.array (.cls "Cbtrn03c$TranTypeRecord"), .cls "java.lang.String"]⟩
def findTranCatSig : MethodSig :=
  ⟨"Cbtrn03c", .prim .int, "findTranCat",
    [.array (.cls "Cbtrn03c$TranCatRecord"), .cls "java.lang.String", .prim .long]⟩

/-! ## Strings and records -/

/-- `spaces(n)`: `n` spaces (the CP037 text of `n` EBCDIC spaces), a new string. -/
def spacesSpecT : Spec := Spec.of
  (fun args σ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt ∧ σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (cp037Str (Model.sp n.toInt.toNat))) ∧
       σ.next ≤ x ∧ σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `blankTran()`: a new record holding the record area's initial contents. -/
def blankTranSpecT : Spec := Spec.of
  (fun args σ => args = [] ∧ σ.initOf "Cbtrn03c" = .done ∧ σ.initOf tranC = .done)
  (fun args σ r σ' => args = [] →
     ∃ x, r = some (.ref x) ∧ TranFields σ' x Model.tran0 ∧ σ.next ≤ x ∧ σ.next ≤ σ'.next ∧
       Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- The comparison's result as Java returns it. -/
def ordI : Ordering → I32
  | .lt => -1#32
  | .eq => 0#32
  | .gt => 1#32

/-- The text of a string argument (`""` for `null` and for a non-string). -/
def argText (σ : State) (v : Value) : JStr := (strOf σ v).getD []

/-- The EBCDIC bytes of a Java string (CP037). -/
def ebcBytes (s : JStr) : List UInt8 := s.map fun u => Model.ebc u.toNat

/-- `compareEbcdic(a, b)` on CP037 texts of equal length: the model's `cmpB` of their bytes (the
postcondition without premises: the arguments are new strings at the call).  (For a character
above 255 the Java `ebcdic` gives `0x6F` and the model's `ebc` 0: the texts are CP037 ones.) -/
def compareEbcdicSpecC : Spec := Spec.of
  (fun args σ => ∃ (xa xb : Addr) (ba bb : List UInt8), args = [.ref xa, .ref xb] ∧
     σ.heap xa = some (.str (cp037Str ba)) ∧ σ.heap xb = some (.str (cp037Str bb)) ∧
     ba.length = bb.length ∧ ba.length < 2147483648 ∧ σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ (xa xb : Addr), args = [.ref xa, .ref xb] →
     r = some (.int (ordI (Model.cmpB (ebcBytes (argText σ (.ref xa)))
       (ebcBytes (argText σ (.ref xb)))))) ∧
     σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `tranRecordText(t)`: the record's DISPLAY line. -/
def tranRecordTextSpecT : Spec := Spec.of
  (fun args σ => ∃ c t, args = [.ref c] ∧ TranFieldsI σ c t ∧ TranRecord.Valid t ∧
     σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ c t, args = [.ref c] → TranFieldsI σ c t → TranRecord.Valid t →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (jline (Model.TranRecord.textS t))) ∧
       σ.next ≤ x ∧ σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `ioStatusLine("23")`. -/
def ioStatusLineSpecT : Spec := Spec.of
  (fun args σ => ∃ y, args = [.ref y] ∧ σ.heap y = some (.str (JStr.ofString "23")) ∧
     σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ y, args = [.ref y] →
     ∃ x, r = some (.ref x) ∧
       σ'.heap x = some (.str (jline (Model.txt "FILE STATUS IS: NNNN0023"))) ∧
       σ.next ≤ x ∧ σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `digits(v, n)`: the `n` low digits of `|v|`. -/
def digitsSpecT : Spec := Spec.of
  (fun args σ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧
     -9223372036854775808 < v.toInt ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 18 ∧ σ.initOf "Cbtrn03c" = .done)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (jline (Model.digs n.toInt.toNat v.toInt))) ∧
       σ.next ≤ x ∧ σ.next ≤ σ'.next ∧ Agree σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-! ## The keyed lookups (called at cuts of their own) -/

/-- The index of the first element with `p` (`-1` if none). -/
def findIdx {α : Type} (p : α → Bool) (l : List α) : Int :=
  match l.findIdx? p with
  | some i => i
  | none => -1

def xrefIdx (xs : List (List EquivLean.Cobol.Rec.FVal)) (k : List UInt8) : Int :=
  findIdx (fun x => Model.xCard x == k) xs
def typeIdx (ys : List (List EquivLean.Cobol.Rec.FVal)) (k : List UInt8) : Int :=
  findIdx (fun y => Model.yType y == k) ys
def catIdx (cs : List (List EquivLean.Cobol.Rec.FVal)) (k : List UInt8) (n : Int) : Int :=
  findIdx (fun c => Model.cType c == k && Model.cCat c == n) cs

def findXrefSpecT : Spec := Spec.of
  (fun args σ => ∃ a y xs k, args = [.ref a, .ref y] ∧ XrefFileAt σ a xs ∧
     (∀ v ∈ xs, CardXrefRecord.Valid v) ∧ σ.heap y = some (.str (cp037Str k)))
  (fun args σ r σ' => ∀ a y xs k, args = [.ref a, .ref y] → XrefFileAt σ a xs →
     (∀ v ∈ xs, CardXrefRecord.Valid v) → σ.heap y = some (.str (cp037Str k)) →
     r = some (.int (BitVec.ofInt 32 (xrefIdx xs k))) ∧ σ' = σ)

def findTranTypeSpecT : Spec := Spec.of
  (fun args σ => ∃ a y ys k, args = [.ref a, .ref y] ∧ TrantypeFileAt σ a ys ∧
     (∀ v ∈ ys, TranTypeRecord.Valid v) ∧ σ.heap y = some (.str (cp037Str k)))
  (fun args σ r σ' => ∀ a y ys k, args = [.ref a, .ref y] → TrantypeFileAt σ a ys →
     (∀ v ∈ ys, TranTypeRecord.Valid v) → σ.heap y = some (.str (cp037Str k)) →
     r = some (.int (BitVec.ofInt 32 (typeIdx ys k))) ∧ σ' = σ)

def findTranCatSpecT : Spec := Spec.of
  (fun args σ => ∃ a y cs k, ∃ v : I64, args = [.ref a, .ref y, .long v] ∧
     TrancatgFileAt σ a cs ∧ (∀ x ∈ cs, TranCatRecord.Valid x) ∧
     σ.heap y = some (.str (cp037Str k)) ∧ v.toInt.natAbs < 10000)
  (fun args σ r σ' => ∀ a y cs k (v : I64), args = [.ref a, .ref y, .long v] →
     TrancatgFileAt σ a cs → (∀ x ∈ cs, TranCatRecord.Valid x) →
     σ.heap y = some (.str (cp037Str k)) →
     r = some (.int (BitVec.ofInt 32 (catIdx cs k v.toInt))) ∧ σ' = σ)

end EquivLean.Modernize.Cbtrn03c.Java.Top

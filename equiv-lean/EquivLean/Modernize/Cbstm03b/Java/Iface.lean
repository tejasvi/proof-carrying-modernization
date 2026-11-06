import EquivLean.Modernize.Cbstm03b.JavaProof

/-!
# CBSTM03B → Java: the contracts of `call`'s callees

`runSpec` (`JavaProof.lean`) is proved from per-method contracts, linked bottom-up:

* the string helpers: `spaces(n)` (`n` spaces), `zeroPad(v, n)` (the last `n` decimal digits of `v ≥ 0`),
  `fit(s, n)` (`s` cut or space-padded to `n` characters; `null` as `""`), `status2(c)` (the two digits of a
  status `0 ≤ c < 100`) and `keySub(area)` (the first `k` characters of `LK-M03B-KEY`, `k` from `LK-M03B-KEY-LN`);
  the texts are JimpleLean's CardDemo ones (`fixStr`, `zpadStr`);
* the four file procedures `trnxProc`, `xrefProc`, `custProc`, `acctProc` (`procSpec dd`): `runSpec`'s contract for
  an area whose DD name is `dd`, the operation (the area's `lkM03bOper` string) passed as a fourth argument.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

/-! ## Texts (JimpleLean's CardDemo examples) -/

/-- The heap only grows: objects that existed are unchanged. -/
def Grows (σ σ' : State) : Prop := σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → σ'.heap x = σ.heap x

def space : JChar := BitVec.ofNat 16 32

/-- The text of a string argument: its characters, `""` for `null` (and for a non-string). -/
def argText (σ : State) (v : Value) : JStr := (strOf σ v).getD []

/-- A string argument: `null`, or a string (of `int` length, as every Java string). -/
def StrOk (σ : State) (v : Value) : Prop :=
  v = .null ∨ ∃ x s, v = .ref x ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

/-- `fixStr s n`: the first `n` characters of `s`, padded with spaces to `n`. -/
def fixStr (s : JStr) : Nat → JStr
  | 0 => []
  | i + 1 => fixStr s i ++ [s.getD i space]

/-- The digit `d` as a character. -/
def digitChar (d : Nat) : JChar := BitVec.ofNat 16 (48 + d)

/-- `zpadStr c m`: the last `m` decimal digits of `c`, zero-padded. -/
def zpadStr (c : Nat) : Nat → JStr
  | 0 => []
  | m + 1 => zpadStr (c / 10) m ++ [digitChar (c % 10)]

/-- The two characters of status `c`. -/
def stChars (c : Nat) : JStr := [digitChar (c / 10 % 10), digitChar (c % 10)]

/-! ## The helpers -/

abbrev spacesRef : MethodRef := Gen.Cbstm03b.«spaces(int)».ref
abbrev zeroPadRef : MethodRef := Gen.Cbstm03b.«zeroPad(long,int)».ref
abbrev fitRef : MethodRef := Gen.Cbstm03b.«fit(java.lang.String,int)».ref
abbrev status2Ref : MethodRef := Gen.Cbstm03b.«status2(int)».ref
abbrev keySubRef : MethodRef := Gen.Cbstm03b.«keySub(Cbstm03b$LkM03bArea)».ref

def spacesSig : MethodSig := ⟨"Cbstm03b", .cls "java.lang.String", "spaces", [.prim .int]⟩
def zeroPadSig : MethodSig := ⟨"Cbstm03b", .cls "java.lang.String", "zeroPad", [.prim .long, .prim .int]⟩
def fitSig : MethodSig := ⟨"Cbstm03b", .cls "java.lang.String", "fit", [.cls "java.lang.String", .prim .int]⟩
def status2Sig : MethodSig := ⟨"Cbstm03b", .cls "java.lang.String", "status2", [.prim .int]⟩
def keySubSig : MethodSig := ⟨"Cbstm03b", .cls "java.lang.String", "keySub", [.cls "Cbstm03b$LkM03bArea"]⟩

def spacesSpec : Spec := Spec.of
  (fun args _ => ∃ n : I32, args = [.int n] ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ n : I32, args = [.int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr [] n.toInt.toNat)) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def zeroPadSpec : Spec := Spec.of
  (fun args _ => ∃ (v : I64) (n : I32), args = [.long v, .int n] ∧ 0 ≤ v.toInt ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ (v : I64) (n : I32), args = [.long v, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (zpadStr v.toNat n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def fitSpec : Spec := Spec.of
  (fun args σ => ∃ sv n, args = [sv, .int n] ∧ StrOk σ sv ∧ 0 ≤ n.toInt)
  (fun args σ r σ' => ∀ sv n, args = [sv, .int n] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (fixStr (argText σ sv) n.toInt.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `status2(c)` for a status `0 ≤ c < 100`: its two decimal digits. -/
def status2Spec : Spec := Spec.of
  (fun args _ => ∃ c : I32, args = [.int c] ∧ 0 ≤ c.toInt ∧ c.toInt < 100)
  (fun args σ r σ' => ∀ c : I32, args = [.int c] →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (stChars c.toNat)) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-- `keySub(area)`: the first `LK-M03B-KEY-LN` characters of `LK-M03B-KEY` (none for a length `≤ 0`, all 25
for a longer one). -/
def keySubSpec : Spec := Spec.of
  (fun args σ => ∃ q a, args = [.ref q] ∧ JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ (.ref q) a ∧
     Model.LkM03bArea.Valid a)
  (fun args σ r σ' => ∀ q a, args = [.ref q] → JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ (.ref q) a →
     Model.LkM03bArea.Valid a →
     ∃ x, r = some (.ref x) ∧ σ'.heap x = some (.str (cp037Str ((Model.aKey a).take (Model.aKeyLn a).toNat))) ∧
       Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

/-! ## The file procedures -/

abbrev trnxProcRef : MethodRef :=
  Gen.Cbstm03b.«trnxProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)».ref
abbrev xrefProcRef : MethodRef :=
  Gen.Cbstm03b.«xrefProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)».ref
abbrev custProcRef : MethodRef :=
  Gen.Cbstm03b.«custProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)».ref
abbrev acctProcRef : MethodRef :=
  Gen.Cbstm03b.«acctProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)».ref

def procParams : List JType :=
  [.array (.cls "java.lang.Integer"), .cls "Cbstm03b$State", .cls "Cbstm03b$LkM03bArea", .cls "java.lang.String"]

def trnxProcSig : MethodSig := ⟨"Cbstm03b", .void, "trnxProc", procParams⟩
def xrefProcSig : MethodSig := ⟨"Cbstm03b", .void, "xrefProc", procParams⟩
def custProcSig : MethodSig := ⟨"Cbstm03b", .void, "custProc", procParams⟩
def acctProcSig : MethodSig := ⟨"Cbstm03b", .void, "acctProc", procParams⟩

/-- `opv` is the area's `lkM03bOper` field (as `call` reads it). -/
def OpAt (σ : Jimple.State) (q : Addr) (opv : Jimple.Value) : Prop :=
  ∃ fs, σ.heap q = some (.plain "Cbstm03b$LkM03bArea" fs) ∧
    Fields.get fs ("Cbstm03b$LkM03bArea", "lkM03bOper") = some opv

/-- **A file procedure** `xxxProc(openErrors, st, area, op)` for the DD name `dd`: `runSpec`'s contract for an
area whose DD name is `dd`, with the area's operation string as the fourth argument. -/
def procSpec (dd : List UInt8) : Spec := Spec.of
  (fun args σ => ∃ oe st q opv oeM s a, args = [.ref oe, .ref st, .ref q, opv] ∧ EnvAtM σ oe oeM ∧
     StateAtM σ st s ∧ SepM σ st ∧ JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ (.ref q) a ∧
     Glue.ValidSt s ∧ Model.LkM03bArea.Valid a ∧ Glue.KeyOk a ∧ Model.aDd a = dd ∧ OpAt σ q opv ∧ InitsDone σ)
  (fun args σ r σ' => ∀ oe st q opv oeM s a, args = [.ref oe, .ref st, .ref q, opv] → EnvAtM σ oe oeM →
     StateAtM σ st s → SepM σ st → JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ (.ref q) a →
     Glue.ValidSt s → Model.LkM03bArea.Valid a → Glue.KeyOk a → Model.aDd a = dd → OpAt σ q opv →
     InitsDone σ →
     r = none ∧ StateAtM σ' st (Model.call oeM s a).1 ∧ SepM σ' st ∧
       JRecAt Model.LkM03bArea "Cbstm03b$LkM03bArea" σ' (.ref q) (Model.call oeM s a).2)

/-! ## The callee contracts of each method -/

def seqCallees : Contracts := [(status2Sig, status2Spec), (fitSig, fitSpec)]
def custCallees : Contracts :=
  [(status2Sig, status2Spec), (fitSig, fitSpec), (keySubSig, keySubSpec), (spacesSig, spacesSpec)]
def acctCallees : Contracts :=
  [(status2Sig, status2Spec), (fitSig, fitSpec), (keySubSig, keySubSpec), (spacesSig, spacesSpec),
    (zeroPadSig, zeroPadSpec)]
def callCallees : Contracts :=
  [(trnxProcSig, procSpec ddTrnx), (xrefProcSig, procSpec ddXref), (custProcSig, procSpec ddCust),
    (acctProcSig, procSpec ddAcct)]

end EquivLean.Modernize.Cbstm03b.Java

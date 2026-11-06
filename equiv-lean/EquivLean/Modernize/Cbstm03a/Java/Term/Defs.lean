import EquivLean.Modernize.Cbstm03a.JavaGen
import EquivLean.Modernize.Cbstm03b.Java.TrnxFin

/-!
# CBSTM03A → Java, termination: shared definitions

Method references and signatures of `Cbstm03a`'s helpers, and the frame every termination contract of this
package promises: `GrowsT σ σ'` (no object of `σ` changes, class initialization and statics unchanged). The
termination contracts (`…SpecT`) have minimal preconditions and frame postconditions only; they are proved here
(`MethodVC`s with this package's own invariants), independently of the helpers' functional contracts.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows)

namespace EquivLean.Modernize.Cbstm03a.Java.Term

/-- No object of `σ` changes; class initialization states and static fields are unchanged. -/
def GrowsT (σ σ' : State) : Prop := Grows σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics

/-- A string result of length `k`: a new string object. -/
def StrResL (σ : State) (r : Option Value) (σ' : State) (k : Nat) : Prop :=
  ∃ x s, r = some (.ref x) ∧ σ.next ≤ x ∧ σ'.heap x = some (.str s) ∧ s.length = k

/-- A string argument: `null` or a string of `int` length. -/
def StrArg (σ : State) (v : Value) : Prop :=
  v = .null ∨ ∃ x s, v = .ref x ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

/-- A non-null string argument of `int` length. -/
def StrArgN (σ : State) (v : Value) : Prop :=
  ∃ x s, v = .ref x ∧ σ.heap x = some (.str s) ∧ s.length < 2147483648

abbrev pow10Ref : MethodRef := Gen.Cbstm03a.«pow10(int)».ref
abbrev repeatRef : MethodRef := Gen.Cbstm03a.«repeat(char,int)».ref
abbrev spacesRef : MethodRef := Gen.Cbstm03a.«spaces(int)».ref
abbrev zeroPadRef : MethodRef := Gen.Cbstm03a.«zeroPad(long,int)».ref
abbrev fixRef : MethodRef := Gen.Cbstm03a.«fix(java.lang.String,int)».ref
abbrev decodeZonedRef : MethodRef := Gen.Cbstm03a.«decodeZoned(java.lang.String)».ref
abbrev fmtZRef : MethodRef := Gen.Cbstm03a.«fmtZ(long)».ref
abbrev zuRef : MethodRef := Gen.Cbstm03a.«zu(long,int)».ref
abbrev zsRef : MethodRef := Gen.Cbstm03a.«zs(long,int)».ref
abbrev fmtCurrBalRef : MethodRef := Gen.Cbstm03a.«fmtCurrBal(long)».ref
abbrev ebcRef : MethodRef := Gen.Cbstm03a.«ebc(char)».ref
abbrev ebcCompareRef : MethodRef := Gen.Cbstm03a.«ebcCompare(java.lang.String,java.lang.String)».ref
abbrev memReadRef : MethodRef := Gen.Cbstm03a.«memRead(java.lang.String[],long,int)».ref
abbrev memWriteRef : MethodRef := Gen.Cbstm03a.«memWrite(java.lang.String[],long,java.lang.String)».ref

def pow10Sig : MethodSig := ⟨"Cbstm03a", .prim .long, "pow10", [.prim .int]⟩
def repeatSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "repeat", [.prim .char, .prim .int]⟩
def spacesSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "spaces", [.prim .int]⟩
def zeroPadSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "zeroPad", [.prim .long, .prim .int]⟩
def fixSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "fix", [.cls "java.lang.String", .prim .int]⟩
def decodeZonedSig : MethodSig := ⟨"Cbstm03a", .prim .long, "decodeZoned", [.cls "java.lang.String"]⟩
def fmtZSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "fmtZ", [.prim .long]⟩
def zuSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "zu", [.prim .long, .prim .int]⟩
def zsSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "zs", [.prim .long, .prim .int]⟩
def fmtCurrBalSig : MethodSig := ⟨"Cbstm03a", .cls "java.lang.String", "fmtCurrBal", [.prim .long]⟩
def ebcSig : MethodSig := ⟨"Cbstm03a", .prim .int, "ebc", [.prim .char]⟩
def ebcCompareSig : MethodSig :=
  ⟨"Cbstm03a", .prim .int, "ebcCompare", [.cls "java.lang.String", .cls "java.lang.String"]⟩
def memReadSig : MethodSig :=
  ⟨"Cbstm03a", .cls "java.lang.String", "memRead", [.array (.cls "java.lang.String"), .prim .long, .prim .int]⟩
def memWriteSig : MethodSig :=
  ⟨"Cbstm03a", .void, "memWrite", [.array (.cls "java.lang.String"), .prim .long, .cls "java.lang.String"]⟩

/-- Termination of a method from its thin twin (`TermVC.of_thin`), its callees answered by the contracts of the
    closed table `T` (all of rank 0), which hold and terminate. -/
theorem mterm_of_thin {T : Contracts} {d : Nat} {m : MethodRef} {S : Spec} {I : Invariants}
    {vs : Nat → List Value → State → Frame → State → Nat} {fuel : Nat}
    (hok : ∀ p ∈ T, ContractOK Gen.prog p.1 p.2) (hterm : ∀ p ∈ T, ContractTerm Gen.prog p.1 p.2)
    (hV : MethodVC Gen.prog T.env d m S I fuel) (hT : ThinVC Gen.prog T.env d m S I vs fuel) :
    ∀ args σ, S.pre args σ → MTerm Gen.prog m args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Contracts.valid_of_ok hok) (Contracts.term_of_ok hterm _ _)
    (TermVC.of_thin (SpecEnv.below_const _ _ (by decide)) hV hT)

/-- A method verified against the contracts of the closed table `T`, which hold, satisfies its contract. -/
theorem sat_of_table {T : Contracts} {d : Nat} {m : MethodRef} {S : Spec} {I : Invariants} {fuel : Nat}
    (hok : ∀ p ∈ T, ContractOK Gen.prog p.1 p.2) (hV : MethodVC Gen.prog T.env d m S I fuel) :
    Sat Gen.prog m S :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok hok) hV

end EquivLean.Modernize.Cbstm03a.Java.Term

namespace EquivLean.Modernize.Cbstm03a.Java.Term

/-- Class `Cbstm03a` is initialized (static calls of its methods run no initializer). -/
abbrev InitA (σ : State) : Prop := σ.initOf "Cbstm03a" = .done

end EquivLean.Modernize.Cbstm03a.Java.Term

namespace EquivLean.Modernize.Cbstm03a.Java.Term

/-- A character (zero-extended) against an `int` constant, as a comparison of naturals (for the symbolic
    executor's case splits). -/
theorem setWidth32_eq_ofNat (c : BitVec 16) (k : Nat) :
    (BitVec.setWidth 32 c = BitVec.ofNat 32 k) ↔ c.toNat = k % 4294967296 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := c.isLt
  simp only [Nat.reducePow] at *
  constructor <;> intro h <;> omega

end EquivLean.Modernize.Cbstm03a.Java.Term


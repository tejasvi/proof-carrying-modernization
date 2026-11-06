/-
  Examples/Mainframe.lean

  A COBOL-to-Java rewrite verified against the COBOL semantics of `Jimple/Cobol.lean`.
  Each method of `examples_java/mainframe/src/Interest.java` replaces one COBOL statement;
  its contract says that the Java method returns what the COBOL statement stores, and that
  it throws exactly when COBOL raises the size error condition. The proofs run on the Jimple
  that Soot 4.7.1 produced from `javac --release 8` bytecode
  (`examples_java/mainframe/jimple`), and the only proof step is `jverify` with the COBOL
  definitions to unfold.
-/
import Jimple

open Jimple Cobol

jimple_import "examples_java/mainframe/jimple" as MF

namespace Examples.Mainframe

/-- The method of class `cls` named `name`. -/
def mref (P : Program) (cls name : String) : MethodRef :=
  ⟨cls, ((P.classes.find? (·.name == cls)).bind fun d => d.methods.find? (·.name == name)).get!⟩

/-! ### `COMPUTE ... ROUNDED ... ON SIZE ERROR` -/

/-- `05 INT PIC S9(5)V99.` -/
def intPic : Pic := ⟨5, 2, true⟩

/-- `COMPUTE INT ROUNDED = BAL * RATE / 1200 ON SIZE ERROR ...`: the value stored into `INT`,
    or `none` for the size error. -/
def interestCobol (bal rate : Rat) : Option Rat := intPic.compute true (bal * rate / 1200)

/-- `monthlyInterest(bal, rate)` returns the value COBOL stores into `INT`, and throws an
    `ArithmeticException` exactly when COBOL raises the size error. -/
def monthlyInterestSpec : Spec := Spec.of
  (fun args σ => ∃ a b d e, args = [.ref a, .ref b] ∧ σ.heap a = some (.dec d) ∧
     σ.heap b = some (.dec e))
  (fun args σ r σ' => ∀ a b d e, args = [.ref a, .ref b] → σ.heap a = some (.dec d) →
     σ.heap b = some (.dec e) →
     ∃ c z, r = some (.ref c) ∧ σ'.heap c = some (.dec z) ∧
       interestCobol d.toRat e.toRat = some z.toRat)
  (fun args σ x σ' => ∀ a b d e, args = [.ref a, .ref b] → σ.heap a = some (.dec d) →
     σ.heap b = some (.dec e) →
     interestCobol d.toRat e.toRat = none ∧
       ∃ fs, σ'.heap x = some (.plain "java.lang.ArithmeticException" fs))

set_option maxRecDepth 8000 in
theorem monthlyInterest_ok :
    MethodVC MF.prog (fun _ => none) 0 (mref MF.prog "Interest" "monthlyInterest")
      monthlyInterestSpec [] 80 := by
  jverify [interestCobol, intPic]

/-- The rewrite is faithful: on every terminating run, `monthlyInterest` returns exactly what
    the COBOL statement stores, or throws exactly when COBOL raises the size error. -/
theorem monthlyInterest_sat :
    Sat MF.prog (mref MF.prog "Interest" "monthlyInterest") monthlyInterestSpec :=
  monthlyInterest_ok.sat

/-! ### `COMPUTE` without `ROUNDED` and without `ON SIZE ERROR` into an unsigned item -/

/-- `05 NET PIC 9(5)V99.` -/
def netPic : Pic := ⟨5, 2, false⟩

/-- `COMPUTE NET = GROSS * (100 - DISC) / 100`: the excess fraction digits are truncated, the
    excess high-order digits and the sign dropped. -/
def netCobol (gross disc : Rat) : Rat := netPic.computeNoSizeErr false (gross * (100 - disc) / 100)

/-- `netAmount(gross, disc)` returns the value COBOL stores into `NET`. -/
def netAmountSpec : Spec := Spec.of
  (fun args σ => ∃ a b d e, args = [.ref a, .ref b] ∧ σ.heap a = some (.dec d) ∧
     σ.heap b = some (.dec e))
  (fun args σ r σ' => ∀ a b d e, args = [.ref a, .ref b] → σ.heap a = some (.dec d) →
     σ.heap b = some (.dec e) →
     ∃ c z, r = some (.ref c) ∧ σ'.heap c = some (.dec z) ∧ z.toRat = netCobol d.toRat e.toRat)

set_option maxRecDepth 8000 in
theorem netAmount_ok :
    MethodVC MF.prog (fun _ => none) 0 (mref MF.prog "Interest" "netAmount") netAmountSpec [] 80 := by
  jverify [netCobol, netPic]

end Examples.Mainframe

#print axioms Examples.Mainframe.monthlyInterest_ok
#print axioms Examples.Mainframe.monthlyInterest_sat
#print axioms Examples.Mainframe.netAmount_ok

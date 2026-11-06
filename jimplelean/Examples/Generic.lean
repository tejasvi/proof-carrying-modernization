/-
  Examples/Generic.lean

  Contracts that need no input: `genericSpec P m` says that `m`, called with typed arguments
  in a typed state (`Jimple/Generic.lean`), returns normally or throws only exceptions it
  declares, and never leaves what the semantics models. `jverify_generic` proves it with no
  annotation, or stops exactly at the inputs that break it.
-/
import Jimple

open Jimple

jimple_import "examples_java/hello/jimple" as Gx

namespace Examples.Generic

/-- The method of class `cls` named `name`. -/
def mref (P : Program) (cls name : String) : MethodRef :=
  ⟨cls, ((P.classes.find? (·.name == cls)).bind fun d => d.methods.find? (·.name == name)).get!⟩

/-- `Hello.safeDiv(int, int)` throws no exception at all, for every pair of `int`s: its own
    `try`/`catch` absorbs the division by zero. -/
theorem safeDiv_generic : MethodVC Gx.prog (fun _ => none) 0 (mref Gx.prog "Hello" "safeDiv")
    (genericSpec Gx.prog (mref Gx.prog "Hello" "safeDiv")) [] 60 := by
  jverify_generic

/-! `Item.price()` returns `unit.multiply(BigDecimal.valueOf(qty))`. With `genericSpec` alone,
    `jverify_generic` proves every path except one, and leaves exactly that goal:
    `Fields.get fs ("Item", "unit") = some Value.null ⊢ False` — the method throws a
    `NullPointerException` when the field `unit` is `null`. With that case excluded, the proof
    goes through. -/

/-- The receiver's field `unit` is set. -/
def unitSet (args : List Value) (σ : State) : Prop :=
  ∀ a fs, args = [.ref a] → σ.heap a = some (.plain "Item" fs) → Fields.get fs ("Item", "unit") ≠ some .null

theorem price_generic : MethodVC Gx.prog (fun _ => none) 0 (mref Gx.prog "Item" "price")
    (genericSpecWith Gx.prog (mref Gx.prog "Item" "price") unitSet) [] 60 := by
  jverify_generic [unitSet]

/-- Running a method on concrete arguments (class initialization included). -/
def showOutcome : Option Outcome → String
  | some (.normal (some (.int x)) _) => s!"returns {x.toInt}"
  | some (.normal _ _) => "returns"
  | some (.exc _ _) => "throws"
  | some (.wrong m) => s!"wrong: {m}"
  | none => "out of fuel"

/-- info: "returns -1" -/
#guard_msgs in
#eval showOutcome (runMethod Gx.prog (mref Gx.prog "Hello" "safeDiv") [.int 7, .int 0] State.empty)

/-! ### Failures in Java terms

The goal left without `unitSet` names the input that breaks the contract: an `Item` whose
`unit` is `null`. Running `price` on it with Soot's line numbers (`jimple_lines`, from
`-keep-line-number -print-tags`) reports the failure as a Java source position. -/

jimple_import "examples_java/hello/jimple_lines" as GxL

/--
info: Item.price() throws java.lang.NullPointerException at line 9
path: Item.price() lines 9
-/
#guard_msgs in
#eval
  let (a, σ) := State.empty.alloc
    (.plain "Item" [(("Item", "unit"), .null), (("Item", "qty"), .int 3)])
  IO.println (report GxL.prog (mref GxL.prog "Item" "price") [.ref a] σ)

end Examples.Generic

#print axioms Examples.Generic.safeDiv_generic
#print axioms Examples.Generic.price_generic

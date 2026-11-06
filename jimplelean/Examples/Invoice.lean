/-
  Examples/Invoice.lean

  Business logic over library collections and `BigDecimal`, with an interface and dynamic
  dispatch: `examples_java/hello/src/Hello.java` (classes `Priced`, `Item`, `Hello`), as
  compiled by `javac --release 8` and converted by Soot 4.7.1 (`examples_java/hello/jimple`).

  * `Item.price()` returns `unit × qty` — stated in ℚ via `BigDec.toRat`;
  * `Hello.total(List<Priced>)` iterates the list through `java.util.Iterator`, calls the
    interface method `Priced.price()` on each element and accumulates with
    `BigDecimal.add`; its contract says the result is exactly `Σ price(x)` in ℚ;
  * `invoice_valid`: both contracts hold for every execution (the interface contract is
    discharged for every implementing class, here `Item`).
  The only manual proof input is the loop invariant of `total`.
-/
import Jimple

open Jimple

jimple_import "examples_java/hello/jimple" as H

namespace Examples.Invoice


/-- Mathematical model of `Priced.price()` for the program's only implementation `Item`. -/
def priceOf (σ : State) (v : Value) : Rat :=
  match v with
  | .ref a =>
    match σ.heap a with
    | some (.plain "Item" fs) =>
      match Fields.get fs ("Item", "unit"), Fields.get fs ("Item", "qty") with
      | some (.ref u), some (.int q) =>
        match σ.heap u with
        | some (.dec d) => d.toRat * q.toInt
        | _ => 0
      | _, _ => 0
    | _ => 0
  | _ => 0

/-- An `Item` object with a `BigDecimal` unit price and an `int` quantity. -/
def ItemAt (σ : State) (a : Addr) : Prop :=
  ∃ fs u d q, σ.heap a = some (.plain "Item" fs) ∧ Fields.get fs ("Item", "unit") = some (.ref u) ∧
    σ.heap u = some (.dec d) ∧ Fields.get fs ("Item", "qty") = some (.int q)

/-- Only fresh objects were allocated; nothing that existed was changed. -/
def Grows (σ σ' : State) : Prop := σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → σ'.heap x = σ.heap x

def pricedPrice : MethodSig := ⟨"Priced", .cls "java.math.BigDecimal", "price", []⟩

def pricedSpec : Spec := Spec.of
  (fun args σ => ∃ a, args = [.ref a] ∧ ItemAt σ a)
  (fun args σ r σ' => ∀ a, args = [.ref a] →
     ∃ b e, r = some (.ref b) ∧ σ'.heap b = some (.dec e) ∧ e.toRat = priceOf σ (.ref a) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)


def mref (P : Program) (cls name : String) : MethodRef :=
  ⟨cls, ((P.classes.find? (·.name == cls)).bind fun d => d.methods.find? (·.name == name)).get!⟩

def totalSpec : Spec := Spec.of
  (fun args σ => ∃ l k xs m, args = [.ref l] ∧ σ.heap l = some (.list k xs m) ∧
     ∀ x ∈ xs, ∃ a, x = .ref a ∧ ItemAt σ a)
  (fun args σ r σ' => ∀ l k xs m, args = [.ref l] → σ.heap l = some (.list k xs m) →
     ∃ b e, r = some (.ref b) ∧ σ'.heap b = some (.dec e) ∧ e.toRat = (xs.map (priceOf σ)).sum)

def totalInv : Invariants := [(3, fun args σ0 fr σ => ∀ l k xs m, args = [.ref l] →
  σ0.heap l = some (.list k xs m) →
  ∃ it acc i d, fr.get 3 = some (.ref l) ∧ fr.get 4 = some (.ref it) ∧ fr.get 2 = some (.ref acc) ∧
    σ.heap it = some (.iter l .list [] i m) ∧ σ.heap acc = some (.dec d) ∧ i ≤ xs.length ∧
    d.toRat = ((xs.take i).map (priceOf σ0)).sum ∧ Grows σ0 σ ∧ σ0.next ≤ it ∧
    σ.inits = σ0.inits ∧ σ.statics = σ0.statics)]


def totalSig : MethodSig := ⟨"Hello", .cls "java.math.BigDecimal", "total", [.cls "java.util.List"]⟩

/-- The verified contracts of the program fragment. -/
def contracts : Contracts := [(pricedPrice, pricedSpec), (totalSig, totalSpec)]

def ann : Annotations := Annotations.ofList [(("Hello", "total"), totalInv, 40)] 40

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- Both contracts hold for every execution: `Item.price` implements `Priced.price`, and
    `Hello.total` returns the exact sum of the prices of the list's items. -/
theorem invoice_valid : Valid H.prog contracts.env := by
  apply Contracts.valid (d := 0) (Ann := ann)
  jcontracts [contracts, ann, ItemAt, priceOf, Grows, pricedSpec, pricedPrice, totalSpec, totalInv, totalSig]

end Examples.Invoice

#print axioms Examples.Invoice.invoice_valid

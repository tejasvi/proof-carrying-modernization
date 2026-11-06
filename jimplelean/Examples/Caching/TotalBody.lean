/-
  Examples/Caching/TotalBody.lean

  `Hello.total` (a loop over a `List<Priced>` calling the interface method `Priced.price`) in
  every program that contains `Hello`, `Item` and `Priced`, against the contract of
  `Priced.price` only.
-/
import Examples.Caching.SafeDivBody
import Examples.Caching.Classes.Item
import Examples.Caching.Classes.Priced

open Jimple

namespace Examples.Caching

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

def ItemAt (σ : State) (a : Addr) : Prop :=
  ∃ fs u d q, σ.heap a = some (.plain "Item" fs) ∧ Fields.get fs ("Item", "unit") = some (.ref u) ∧
    σ.heap u = some (.dec d) ∧ Fields.get fs ("Item", "qty") = some (.int q)

def Grows (σ σ' : State) : Prop := σ.next ≤ σ'.next ∧ ∀ x, x < σ.next → σ'.heap x = σ.heap x

def pricedPrice : MethodSig := ⟨"Priced", .cls "java.math.BigDecimal", "price", []⟩

def pricedSpec : Spec := Spec.of
  (fun args σ => ∃ a, args = [.ref a] ∧ ItemAt σ a)
  (fun args σ r σ' => ∀ a, args = [.ref a] →
     ∃ b e, r = some (.ref b) ∧ σ'.heap b = some (.dec e) ∧ e.toRat = priceOf σ (.ref a) ∧ Grows σ σ' ∧
       σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

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

def totalCallees : Contracts := [(pricedPrice, pricedSpec)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem total_body : BodyVC (Contains · [HH.Hello, HItem.Item, HPriced.Priced]) totalCallees.env 0
    HH.Hello.«total(java.util.List)».ref totalSpec totalInv 40 := by
  jverify_body [Contains, totalCallees, ItemAt, priceOf, Grows, pricedSpec, pricedPrice]

end Examples.Caching

#print axioms Examples.Caching.total_body

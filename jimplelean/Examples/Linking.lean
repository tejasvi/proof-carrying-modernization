/-
  Examples/Linking.lean

  Bottom-up verification, one contract at a time (the program and the contracts are those of
  `Examples/Invoice.lean`). `Priced.price` — with its implementation `Item.price` — is verified
  on its own; `Hello.total` is verified against the contract of `Priced.price`, never looking
  at `Item.price`. `ContractVC.ok`, `Contracts.valid_of_ok` and `MethodVC.sat_of_valid` link the
  two proofs. Each proof can be checked (and cached) independently of the other's body.
-/
import Examples.Invoice

open Jimple Examples.Invoice

namespace Examples.Linking

/-- `Priced.price` holds for every implementation in the program (here `Item.price`). -/
theorem priced_ok : ContractOK H.prog pricedPrice pricedSpec := by
  have h : Valid H.prog (Contracts.env [(pricedPrice, pricedSpec)]) := by
    apply Contracts.valid (d := 0) (Ann := ann)
    jcontracts [ann, ItemAt, priceOf, Grows, pricedSpec, pricedPrice]
  exact (valid_iff_contractOK.mp h) pricedPrice pricedSpec (by simp [Contracts.env, List.lookup])

/-- The callee contracts of `Hello.total`. -/
def totalCallees : Contracts := [(pricedPrice, pricedSpec)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
/-- `Hello.total` against its callee's contract only. -/
theorem total_vc : MethodVC H.prog totalCallees.env 0 (mref H.prog "Hello" "total") totalSpec
    totalInv 40 := by
  jverify [totalCallees, ItemAt, priceOf, Grows, pricedSpec, pricedPrice]

/-- Linked: `Hello.total` returns the exact sum of the prices, for every terminating run. -/
theorem total_sat : Sat H.prog (mref H.prog "Hello" "total") totalSpec :=
  MethodVC.sat_of_valid (Contracts.valid_of_ok (by
    intro p hp
    simp only [totalCallees, List.mem_singleton] at hp
    subst hp
    exact priced_ok)) total_vc

end Examples.Linking

#print axioms Examples.Linking.priced_ok
#print axioms Examples.Linking.total_vc
#print axioms Examples.Linking.total_sat

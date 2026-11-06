/-
  Examples/Caching/PriceBody.lean

  `Item.price` against the interface contract of `Priced.price`, in every program that contains
  `Item` (and shadows no library class).
-/
import Examples.Caching.TotalBody

open Jimple

namespace Examples.Caching

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem price_body : BodyVC (Contains · [HItem.Item]) (fun _ => none) 0 HItem.Item.«price()».ref
    pricedSpec [] 20 := by
  jverify_body [Contains, ItemAt, priceOf, Grows, pricedSpec]

end Examples.Caching

#print axioms Examples.Caching.price_body

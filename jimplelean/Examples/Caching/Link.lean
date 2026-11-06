/-
  Examples/Caching/Link.lean

  The link step. The program is assembled from per-class imports (`jimple_program`); each body
  proof (`MaxBody`, `SafeDivBody`, `PriceBody`, `TotalBody`) was checked once, for every
  program containing its classes, and is instantiated here. Bottom-up: `Item.price` gives the
  interface contract of `Priced.price` (`ContractOK`), which `Hello.total` was verified
  against.
-/
import Examples.Caching.MaxBody
import Examples.Caching.PriceBody

open Jimple Examples.Caching

jimple_program BB HH HItem HPriced as Whole

namespace Examples.Caching

/-- The assembled program contains any of its classes (and shadows no library class). -/
theorem whole_contains (cs : List ClassDecl) (h : ∀ d ∈ cs, Whole.prog.findClass d.name = some d) :
    Contains Whole.prog cs := Contains.of_check (by decide) h

theorem max_sat : Sat Whole.prog BB.Basics.«max(int,int)».ref maxSpec :=
  max_body.sat trivial (valid_none _)

theorem safeDiv_sat : Sat Whole.prog HH.Hello.«safeDiv(int,int)».ref safeDivSpec :=
  safeDiv_body.sat (whole_contains _ (by intro d hd; simp at hd; subst hd; rfl)) (valid_none _)

theorem price_sat : Sat Whole.prog HItem.Item.«price()».ref pricedSpec :=
  price_body.sat (whole_contains _ (by intro d hd; simp at hd; subst hd; rfl)) (valid_none _)

/-- The contract of a static method needs only its body (no subclass owes it anything). -/
theorem max_ok : ContractOK Whole.prog BB.Basics.«max(int,int)».ref.sig maxSpec := by
  jcontract_ok [max_sat]

/-- The interface contract holds: `Item.price` is the only implementation; the interface
    method itself is abstract. -/
theorem priced_ok : ContractOK Whole.prog pricedPrice pricedSpec := by
  jcontract_ok [price_sat]

theorem total_sat : Sat Whole.prog HH.Hello.«total(java.util.List)».ref totalSpec :=
  total_body.sat (whole_contains _ (by
      intro d hd
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> rfl))
    (Contracts.valid_of_ok (by
      intro p hp
      simp only [totalCallees, List.mem_singleton] at hp
      subst hp
      exact priced_ok))

end Examples.Caching

#print axioms Examples.Caching.max_sat
#print axioms Examples.Caching.safeDiv_sat
#print axioms Examples.Caching.max_ok
#print axioms Examples.Caching.priced_ok
#print axioms Examples.Caching.total_sat

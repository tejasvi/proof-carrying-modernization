/-
  Examples/Caching/GenericBody.lean

  Generic contracts (`Jimple/Generic.lean`) proved once per method, for every program that
  contains the method's class. `genericSpec P m` refers to the program (argument and heap
  typing), so the statement is `BodyVCP`, whose contract and callee contracts are taken in each
  program. The proof looks only at the method's class, however large the program is; linking
  instantiates it like a `BodyVC` proof.
-/
import Examples.Caching.Link

open Jimple

namespace Examples.Caching

/-- `Hello.safeDiv(int, int)` throws nothing, in every program containing `Hello`. -/
theorem safeDiv_generic_body : BodyVCP (Contains · [HH.Hello]) (fun _ _ => none) 0
    HH.Hello.«safeDiv(int,int)».ref (genericSpec · HH.Hello.«safeDiv(int,int)».ref) [] 60 := by
  jverify_generic_body

/-- The receiver's field `unit` is set (see `Examples/Generic.lean`). The receiver may be of
    any subclass of `Item` in a program that is not fixed. -/
def unitSet (args : List Value) (σ : State) : Prop :=
  ∀ a c fs, args = [.ref a] → σ.heap a = some (.plain c fs) → Fields.get fs ("Item", "unit") ≠ some .null

/-- `Item.price()` throws nothing when `unit` is set, in every program containing `Item`. -/
theorem price_generic_body : BodyVCP (Contains · [HItem.Item]) (fun _ _ => none) 0
    HItem.Item.«price()».ref (fun P => genericSpecWith P HItem.Item.«price()».ref unitSet) [] 60 := by
  jverify_generic_body [unitSet]

/-- Linked into the assembled program of `Link.lean`. -/
theorem safeDiv_generic_sat : Sat Whole.prog HH.Hello.«safeDiv(int,int)».ref
    (genericSpec Whole.prog HH.Hello.«safeDiv(int,int)».ref) :=
  safeDiv_generic_body.sat (whole_contains _ (by intro d hd; simp at hd; subst hd; rfl)) (valid_none _)

end Examples.Caching

#print axioms Examples.Caching.safeDiv_generic_body
#print axioms Examples.Caching.price_generic_body
#print axioms Examples.Caching.safeDiv_generic_sat

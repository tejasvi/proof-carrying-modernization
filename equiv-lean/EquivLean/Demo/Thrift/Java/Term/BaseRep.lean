-- Termination package by JimpleLean's session: TermT4/BaseRep.lean (sha256 ce7eb9388052bc9d...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Term.BaseCp

/-!
# Thrift → Java (T4), termination: working transports have concrete classes

A method that makes a protocol call after another one needs, at the second call, the premise of the
callee's termination: the transport object's class is concrete (`TConc`). The protocol contracts do not
say that a protocol call keeps the transport object's class (their frames `PFrame`, `RFrame`, `WFrame`
leave the transport object open; only the transport's own `TFrame` keeps its class), so `TConc` at the
caller's entry does not carry over to the second call. These methods
take the premise `TRepConc` instead: every object the transport representation calls a working
transport (`R.inv`) has a concrete class. With `CPAt` it gives `TConc` in any state (`tconc_of_cpAt`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The premise: every working transport object has a concrete class. -/
def TRepConc (P : Program) (R : TRep) : Prop :=
  ∀ σ t c fst, R.inv σ t → σ.heap t = some (.plain c fst) → P.concrete c = true

theorem tconc_of_cpAt {P : Program} {R : TRep} {σ : State} {p t tmp : Addr} {rest : List Value}
    (hR : TRepConc P R) (h : CPAt P R σ p t tmp) : TConc P (.ref p :: rest) σ := by
  obtain ⟨fs, xs, c, fst, hp, htr, -, -, -, ht, -, -, hinv, -⟩ := h
  exact tconc_intro hp htr ht (hR σ t c fst hinv ht)

/-- `TCompactProtocol` is concrete: a protocol call on `this` is answered by its contract. -/
theorem concrete_cp {P : Program} (h : P.findClass cpCls = some cpC) : P.concrete cpCls = true := by
  unfold Program.concrete Program.lookup
  rw [h]
  all_goals rfl

end EquivLean.Demo.Thrift.Java

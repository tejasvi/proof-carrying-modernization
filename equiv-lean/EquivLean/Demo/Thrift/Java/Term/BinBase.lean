-- Termination package by JimpleLean's session: TermT4/BinBase.lean (sha256 4ca66b7f47862882...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Bp
import EquivLean.Demo.Thrift.Java.Term.Base

/-!
# Thrift → Java (T4), termination: the premise for the binary protocol

`TConcAt` (`Base`) names a `TCompactProtocol` object; `BConcAt` is the same premise for a
`TBinaryProtocol` object `p` (`BPAt`): its transport object `t` (field `trans_`) has a concrete class.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The premise: the transport object `t` (field `trans_` of the binary protocol object `p`) has a
    concrete class. -/
def BConcAt (P : Program) (σ : State) (p : Addr) : Prop :=
  ∃ fs t c fst, σ.heap p = some (.plain bpCls fs) ∧ Fields.get fs (tpCls, "trans_") = some (.ref t) ∧
    σ.heap t = some (.plain c fst) ∧ P.concrete c = true

/-- The premise on a binary protocol method's arguments (the protocol object first). -/
def BConc (P : Program) (args : List Value) (σ : State) : Prop :=
  ∃ p rest, args = .ref p :: rest ∧ BConcAt P σ p

end EquivLean.Demo.Thrift.Java

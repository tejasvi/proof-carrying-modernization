-- Termination package by JimpleLean's session: TermT4/Base.lean (sha256 0ccf60969117acff...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Cp
import Jimple.TermSplitX

/-!
# Thrift → Java (T4), termination: the premise and the transport

The transport is abstract (`TRep`, `tContracts`): its methods' termination is a hypothesis, as their
contracts are (`TransportTerm`). A virtual call answered by a contract needs the receiver's runtime class
to be concrete; the transport object's class is the one fact the T4 preconditions do not state, so each
termination theorem takes it as a premise (`TConcAt`): an object of an abstract class has no instance in a
run of the JVM.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The premise: the transport object `t` (field `trans_` of the protocol object `p`) has a concrete
    class. -/
def TConcAt (P : Program) (σ : State) (p : Addr) : Prop :=
  ∃ fs t c fst, σ.heap p = some (.plain cpCls fs) ∧ Fields.get fs (tpCls, "trans_") = some (.ref t) ∧
    σ.heap t = some (.plain c fst) ∧ P.concrete c = true

/-- The premise on a protocol method's arguments (the protocol object first). -/
def TConc (P : Program) (args : List Value) (σ : State) : Prop :=
  ∃ p rest, args = .ref p :: rest ∧ TConcAt P σ p

/-- The extra callee premises for the transport contracts: none (a transport call's receiver class is
    checked at the call itself). -/
def noX : MethodSig → List Value → State → Prop := fun _ _ _ => True

/-- The transport's methods terminate under their contracts (a hypothesis, like their contracts). -/
def TransportTerm (P : Program) (R : TRep) : Prop :=
  ∀ sig S, (tContracts R).env sig = some S → ContractTerm P sig S

theorem transportTerm_noX {P : Program} {R : TRep} (h : TransportTerm P R) :
    ∀ sig S, (tContracts R).env sig = some S → ContractTerm P sig (S.strengthen (noX sig)) :=
  fun sig S hs => ContractTerm.mono (h sig S hs) fun _ _ hp => hp.1

end EquivLean.Demo.Thrift.Java

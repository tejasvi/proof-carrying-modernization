import EquivLean.Modernize.Cbstm03b.Java.XrefFin
import EquivLean.Modernize.Cbstm03b.Java.XrefModel
import EquivLean.Modernize.Cbstm03b.Java.HFresh

/-! # CBSTM03B → Java: `xrefProc`'s weakest precondition, kept folded -/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open CardDemo.Cbstm03b (ddTrnx ddXref ddCust ddAcct opOpen opRead opReadK opClose stBytes intoBuf)

namespace EquivLean.Modernize.Cbstm03b.Java

@[irreducible] def xrefWP (oe st q : Addr) (opv : Value) (oeM : Model.OpenErrs) (s : Model.StM)
    (a : List EquivLean.Cobol.Rec.FVal) (args : List Value) (σ0 : State) (pc : Nat) (fr : Frame) (σ : State) : Prop :=
  bodyWP Gen.prog (callWP Gen.prog seqCalleesF.env 1)
    Gen.Cbstm03b.«xrefProc(java.lang.Integer[],Cbstm03b$State,Cbstm03b$LkM03bArea,java.lang.String)»
    (Invariants.inst [] args σ0) ((procSpecG ddXref oe st q opv oeM s a).post args σ0) 200 pc fr σ

theorem forall2_lengthX {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 → l1.length = l2.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [forall2_lengthX h]

end EquivLean.Modernize.Cbstm03b.Java

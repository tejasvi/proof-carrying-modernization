import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunH3

/-!
# CBTRN02C → Java: `run`'s exit (statement 83)

`J83X`: all transactions processed and none stopped the run; the counters (hidden with the state,
so that the symbolic execution of the exit keeps them opaque).
-/

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

/-- **The exit** (statement 83): all transactions processed, the run not stopped. -/
def J83X (g : G) (_args : List Value) (σ0 : State) (fr : Frame) (σ : State) : Prop :=
  ∃ (A : Addrs) (tx rej : I64),
    Locs65 g A fr ∧ fr.get 9 = some (.long tx) ∧ fr.get 10 = some (.long rej) ∧
    Hide (tx = BitVec.ofNat 64 (g.trans.length % 1000000000) ∧
      rej = BitVec.ofNat 64 ((g.st g.trans.length).rejects % 1000000000) ∧
      g.stx g.trans.length = ⟨g.st g.trans.length, false⟩ ∧
      W σ A (g.st g.trans.length) ∧ MV (g.st g.trans.length) ∧ Fresh σ0 A) ∧
    Grows σ0 σ ∧ σ.inits = σ0.inits ∧ σ.statics = σ0.statics

end EquivLean.Modernize.Cbtrn02c.Java

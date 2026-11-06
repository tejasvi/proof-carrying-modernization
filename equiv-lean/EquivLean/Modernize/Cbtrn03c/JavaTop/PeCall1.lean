import EquivLean.Modernize.Cbtrn03c.JavaTop.Pe

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processEnd`, the call of `writePageTotals` (statement 20, to the cut at 21)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] WsRel KeepsNonWs TranFields

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pe_call1 (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hI : fr.get 1 = some (.ref w) ∧ WsRel σ w ld lr d (peS1 s t) ∧ KeepsNonWs σ0 σ ∧
      σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf fdC = .done) :
    peWP w ld lr c d t s args σ0 20 fr σ := by
  jvc [peWP, peSpecG, peInv, peCallees, zonedSig, add11Sig, writePageTotalsSig,
    writeGrandTotalsSig, writePageTotalsSpecM, writeGrandTotalsSpecM, wsStepSpec]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pe_call1

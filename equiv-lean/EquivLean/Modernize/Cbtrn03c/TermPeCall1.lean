-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermPeCall1.lean (sha256 57c9215157bc159a...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.PeCall1
import EquivLean.Modernize.Cbtrn03c.JavaTermDefs

/-!
# Termination: thin twins of `PeCall1`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

set_option jimple.modelContracts true
open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

attribute [local irreducible] WsRel KeepsNonWs TranFields

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pe_call1_t (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hI : fr.get 1 = some (.ref w) ∧ WsRel σ w ld lr d (peS1 s t) ∧ KeepsNonWs σ0 σ ∧
      σ.inits = σ0.inits ∧ σ.statics = σ0.statics ∧ σ0.initOf "Cbtrn03c" = .done ∧
      σ0.initOf fdC = .done) :
    peThinWP w ld lr c d t s args σ0 20 fr σ := by

  jvc [peThinWP, peSpecG, peInv, peCallees, zonedSig, add11Sig, writePageTotalsSig,
    writeGrandTotalsSig, writePageTotalsSpecM, writeGrandTotalsSpecM, wsStepSpec, lineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java.Top

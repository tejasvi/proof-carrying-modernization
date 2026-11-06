-- Termination package by JimpleLean's session: TermPk/Cbtrn03c/TermPeEntry.lean (sha256 1bc036fbde6ded62...); only the module root renamed.
import EquivLean.Modernize.Cbtrn03c.JavaTop.PeEntry
import EquivLean.Modernize.Cbtrn03c.JavaTermDefs

/-!
# Termination: thin twins of `PeEntry`

The statements and preambles of the originals; the cut assertions the variants, calls by
`callWPThin` (`callWPT` without the callee preconditions, which `MethodVC` checks).
-/

set_option jimple.modelContracts true
open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top


set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pe_entry_t (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (args : List Value) (σ0 : State) (hpre : (peSpecG w ld lr c d t s).pre args σ0) :
    peThinWP0 w ld lr c d t s args σ0 := by

  jvc [ite_nat_ne, peThinWP0, peSpecG, peInv, peCallees, zonedSig, add11Sig, writePageTotalsSig,
    writeGrandTotalsSig, zonedSpecT, add11SpecT, WsRel, TranFields, SFld, LFld, KeepsNonWs, StrMono,
    Agree, StOk, peS1, Model.dsp, jline, wsC, fdC, tranC, add11_ofInt,
    natAbs_trunc11_lt, BitVec.toInt_ofInt, toInt_ofInt64_small, txtLit, Native.valueOfArg, JType.isRef,
    add11_ofInt', StrsAt_append2, StrsAt_append3, lineVs]
  all_goals first
    | exact ⟨Or.inl rfl, rfl⟩
    | skip

end EquivLean.Modernize.Cbtrn03c.Java.Top

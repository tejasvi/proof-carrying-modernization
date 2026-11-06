import EquivLean.Modernize.Cbtrn03c.JavaTop.Pe

set_option jimple.modelContracts true

/-!
# CBTRN03C → Java: `processEnd`, entry segment (statements 0–19, to the cut at 20)
-/

open Jimple EquivLean.Cobol.Rec EquivLean.Jimple

namespace EquivLean.Modernize.Cbtrn03c.Java.Top

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem pe_entry (w ld lr c : Addr) (d t : List EquivLean.Cobol.Rec.FVal) (s : Model.St)
    (args : List Value) (σ0 : State) (hpre : (peSpecG w ld lr c d t s).pre args σ0) :
    peWP w ld lr c d t s args σ0 0 (Frame.init true args) σ0 := by
  jvc [ite_nat_ne, peWP, peSpecG, peInv, peCallees, zonedSig, add11Sig, writePageTotalsSig,
    writeGrandTotalsSig, zonedSpecT, add11SpecT, WsRel, TranFields, SFld, LFld, KeepsNonWs, StrMono,
    Agree, StOk, peS1, Model.dsp, jline, wsC, fdC, tranC, add11_ofInt,
    natAbs_trunc11_lt, BitVec.toInt_ofInt, toInt_ofInt64_small, txtLit, Native.valueOfArg, JType.isRef,
    add11_ofInt', StrsAt_append2, StrsAt_append3]

end EquivLean.Modernize.Cbtrn03c.Java.Top

#print axioms EquivLean.Modernize.Cbtrn03c.Java.Top.pe_entry

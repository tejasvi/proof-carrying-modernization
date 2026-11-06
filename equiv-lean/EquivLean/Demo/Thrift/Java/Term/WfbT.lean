-- Termination package by JimpleLean's session: TermT4/WfbT.lean (sha256 1fe20c5a3b04c641...); only the module root renamed.
import EquivLean.Demo.Thrift.Java.Wfb
import EquivLean.Demo.Thrift.Java.Term.BaseRep

/-!
# Thrift → Java (T4), termination: `TCompactProtocol.writeFieldBeginInternal(TField, byte)` (thin VC)

The thin twin of `wfb_body`, against `Γ4`. One cut point (statement 32), no loop. The callee premises
`gctX` are none but for `getCompactType(byte)`: its contract has the precondition `False` (the type
override `-1` is excluded), so its premise is `False` too, and the thin VC drops that path as `wfb_body`
does (`wfb_neg1`); a thin VC without it would follow the call into an arbitrary state.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

/-- The callee premises of `writeFieldBeginInternal`: `False` for `getCompactType(byte)`, none
    otherwise. -/
def gctX (sig : MethodSig) (_ : List Value) (_ : State) : Prop := sig = gctSig → False

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wfb_thin (R : TRep) : ∀ P, Contains P [cpC, tpC, ttC, tpeC, teC, twC, trC, tfC] →
    ThinVCX P (Γ4 P R) gctX 2 wfbRef (wfbSpecI P R) (wfbInv P R) (fun _ _ _ _ _ => 0) 200 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    try dsimp only
    jvc_body [Contains, CPAt, ClassOK, wfbSpecI, wfbInv, FieldIdAt, LastAt, Γ4, Γ2, wbdSig, wi16Sig,
      gctSig, rv32Sig, wv32Sig, gctSpec, wbdN, wi16N, Program.selectVirtual, tc_write, tc_readAll,
      tc_getBytesRemainingInBuffer, tc_getBuffer, tc_getBufferPosition, tc_consumeBuffer,
      tc_checkReadBytesAvailable, tc_none, TFrame, PFrame, ttCls, cpCls, tpCls, tfCls, gctX]
    all_goals first
      | assumption
      | exact concrete_cp (by assumption)
      | exact (wfb_neg1 ‹_›).elim
      | exact fun h => absurd h (by decide)
      | skip

end EquivLean.Demo.Thrift.Java

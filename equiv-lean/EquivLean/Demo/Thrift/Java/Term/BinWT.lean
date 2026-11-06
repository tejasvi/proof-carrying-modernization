-- Termination package by JimpleLean's session: TermT4/BinWT.lean (sha256 e39f3c81766fec97...); the module root and ac65118's bwi16 names renamed.
import EquivLean.Demo.Thrift.Java.BinW
import EquivLean.Demo.Thrift.Java.Term.BinBase

/-!
# Thrift → Java (T4), termination: `TBinaryProtocol.writeI16/writeI32/writeI64` (thin VCs)

The thin twins of `bwi16_body`, `wi32_body`, `wi64_body`: their invariants (one cut point each, the
load of `trans_`, on no loop: the variant is constant), the premise `BConc` (the transport's class is
concrete). `writeI16`'s are named `bwi16_*`, apart from the compact protocol's `writeI16(short)`.
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem bwi16_thin (R : TRep) : ThinVCPX (Contains · [bpC, tpC, ttC])
    (fun _ => (tContracts R).env) (fun _ => noX) 0 bwi16Ref
    (fun P => (bwi16SpecI P R).strengthen (BConc P)) wi16Inv (fun _ _ _ _ _ => 0) 60 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, BConc, BConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, tContracts, BPAt, PFrame, bwi16SpecI, wi16Inv, writeSpec, writeSig, ttCls,
      bpCls, tpCls, noX]
    all_goals first | assumption | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wi32_thin (R : TRep) : ThinVCPX (Contains · [bpC, tpC, ttC])
    (fun _ => (tContracts R).env) (fun _ => noX) 0 wi32Ref
    (fun P => (wi32SpecI P R).strengthen (BConc P)) wi32Inv (fun _ _ _ _ _ => 0) 60 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, BConc, BConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, tContracts, BPAt, PFrame, wi32SpecI, wi32Inv, writeSpec, writeSig, ttCls,
      bpCls, tpCls, noX]
    all_goals first | assumption | skip

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
set_option jimple.modelContracts true in
theorem wi64_thin (R : TRep) : ThinVCPX (Contains · [bpC, tpC, ttC])
    (fun _ => (tContracts R).env) (fun _ => noX) 0 wi64Ref
    (fun P => (wi64SpecI P R).strengthen (BConc P)) wi64Inv (fun _ _ _ _ _ => 0) 80 := by
  intro P hF
  refine ThinVCX.mk rfl (fun _ _ => rfl) ?_ ?_
  all_goals
    intro args σ0 hpre
    simp only [Spec.strengthen, BConc, BConcAt] at hpre
    obtain ⟨hpre, p0, rest0, hargs0, fs0, t0, c0, fst0, hp0, htr0, ht0, hc0⟩ := hpre
    dsimp only
    jvc_body [Contains, tContracts, BPAt, PFrame, wi64SpecI, wi64Inv, writeSpec, writeSig, ttCls,
      bpCls, tpCls, noX]
    all_goals first | assumption | skip

end EquivLean.Demo.Thrift.Java

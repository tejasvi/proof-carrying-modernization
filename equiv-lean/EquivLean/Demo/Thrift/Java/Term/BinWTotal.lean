-- Termination package by JimpleLean's session: TermT4/BinWTotal.lean (sha256 39bc6a8496fd8f9a...); the module root and ac65118's bwi16 names renamed.
import EquivLean.Demo.Thrift.Java.Term.BinWT

/-!
# Thrift → Java (T4): `TBinaryProtocol.writeI16/writeI32/writeI64` terminate, and are totally correct

From the partial-correctness VCs (`bwi16_body`, `wi32_body`, `wi64_body`) and their thin twins
(`TermVC.of_thinX`), against the transport contracts and, as hypotheses like them, the transport's
termination (`TransportTerm`); premise: the transport's class is concrete (`BConc`).
-/

open Jimple

namespace EquivLean.Demo.Thrift.Java

theorem bwi16_termI (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((bwi16SpecI P R).strengthen (BConc P)).pre args σ → MTerm P bwi16Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (BConc P) (bwi16_body R P hF)) (bwi16_thin R P hF))

/-- **`writeI16(short)` terminates** on every input of its contract whose transport has a concrete
    class. -/
theorem bwi16_term (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wi16Spec P R).pre args σ → BConc P args σ → MTerm P bwi16Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, n, hargs, hBP⟩ := hpre
  exact bwi16_termI R hF hV hT args σ ⟨⟨p, t, tmp, n, hargs, hBP, BPAtH.intro hBP⟩, hc⟩

/-- **`writeI16(short)`, total correctness.** -/
theorem bwi16_total (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wi16Spec P R).pre args σ → BConc P args σ →
      (∃ o, MExec P bwi16Ref args σ o) ∧ ∀ o, MExec P bwi16Ref args σ o → (wi16Spec P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(bwi16_term R hF hV hT args σ hpre hc).run, fun o ho => wi16_sat R hF hV args σ o hpre ho⟩

theorem wi32_termI (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((wi32SpecI P R).strengthen (BConc P)).pre args σ → MTerm P wi32Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (BConc P) (wi32_body R P hF)) (wi32_thin R P hF))

/-- **`writeI32(int)` terminates** on every input of its contract whose transport has a concrete
    class. -/
theorem wi32_term (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wi32Spec P R).pre args σ → BConc P args σ → MTerm P wi32Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, n, hargs, hBP⟩ := hpre
  exact wi32_termI R hF hV hT args σ ⟨⟨p, t, tmp, n, hargs, hBP, BPAtH.intro hBP⟩, hc⟩

/-- **`writeI32(int)`, total correctness.** -/
theorem wi32_total (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wi32Spec P R).pre args σ → BConc P args σ →
      (∃ o, MExec P wi32Ref args σ o) ∧ ∀ o, MExec P wi32Ref args σ o → (wi32Spec P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(wi32_term R hF hV hT args σ hpre hc).run, fun o ho => wi32_sat R hF hV args σ o hpre ho⟩

theorem wi64_termI (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, ((wi64SpecI P R).strengthen (BConc P)).pre args σ → MTerm P wi64Ref args σ :=
  TermVC.mterm (rank := fun _ => 0) (r := 1) (Valid.strengthen noX hV)
    (SpecEnv.strengthen_term (transportTerm_noX hT) _ _)
    (TermVC.of_thinX (SpecEnv.strengthen_below_const _ _ _ (by decide))
      (MethodVC.strengthen (BConc P) (wi64_body R P hF)) (wi64_thin R P hF))

/-- **`writeI64(long)` terminates** on every input of its contract whose transport has a concrete
    class. -/
theorem wi64_term (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wi64Spec P R).pre args σ → BConc P args σ → MTerm P wi64Ref args σ := by
  intro args σ hpre hc
  obtain ⟨p, t, tmp, n, hargs, hBP⟩ := hpre
  exact wi64_termI R hF hV hT args σ ⟨⟨p, t, tmp, n, hargs, hBP, BPAtH.intro hBP⟩, hc⟩

/-- **`writeI64(long)`, total correctness.** -/
theorem wi64_total (R : TRep) {P : Program} (hF : Contains P [bpC, tpC, ttC])
    (hV : Valid P (tContracts R).env) (hT : TransportTerm P R) :
    ∀ args σ, (wi64Spec P R).pre args σ → BConc P args σ →
      (∃ o, MExec P wi64Ref args σ o) ∧ ∀ o, MExec P wi64Ref args σ o → (wi64Spec P R).post args σ o :=
  fun args σ hpre hc =>
    ⟨(wi64_term R hF hV hT args σ hpre hc).run, fun o ho => wi64_sat R hF hV args σ o hpre ho⟩

end EquivLean.Demo.Thrift.Java

#print axioms EquivLean.Demo.Thrift.Java.bwi16_total
#print axioms EquivLean.Demo.Thrift.Java.wi32_total
#print axioms EquivLean.Demo.Thrift.Java.wi64_total

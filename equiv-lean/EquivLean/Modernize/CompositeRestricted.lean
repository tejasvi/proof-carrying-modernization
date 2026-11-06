import EquivLean.Modernize.Cbact04c.JavaTermRun

/-!
# Composite migration statement for restricted CBACT04C → Java

Separated from `EquivLean.Modernize.Composite` because the restricted `Cbact04c.Java` helper
modules and `Cbact04c.Every.Java` helper modules share internal declaration names.
-/

open Cobol EquivLean.Cobol.Rec
open Jimple EquivLean.Jimple

namespace EquivLean.Modernize.Cbact04c.Java

theorem java_composite :
    ∀ (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, TranCatBalRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, AccountRecord.Valid v) →
      (∀ v ∈ vals4, DisGroupRecord.Valid v) →
      ∀ (link1 : List EquivLean.Cobol.Rec.FVal), ExternalParms.Valid link1 →
      ∀ (clk : List UInt8), CurrentDate clk →
      KsdsValid CardDemo.Cbact04c 1 (vals1.map TranCatBalRecord.encode) →
      KsdsValid CardDemo.Cbact04c 2 (vals2.map CardXrefRecord.encode) →
      KsdsValid CardDemo.Cbact04c 3 (vals3.map AccountRecord.encode) →
      KsdsValid CardDemo.Cbact04c 4 (vals4.map DisGroupRecord.encode) →
      EquivLean.Modernize.Cbact04c.Domain vals1 vals2 vals3 vals4 link1 →
      vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 27 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length < n →
      ∀ (σ : Jimple.State) (a1 a2 a3 a4 p1 cs : Addr),
      TcatbalFileAt σ a1 vals1 →
      XrefFileAt σ a2 vals2 →
      AccountFileAt σ a3 vals3 →
      DiscgrpFileAt σ a4 vals4 →
      JRecAt ExternalParms "Cbact04c$ExternalParms" σ (.ref p1) link1 →
      JStrAt σ (.ref cs) (cp037Str clk) →
      σ.initOf "Cbact04c" = .done →
      σ.initOf "Cbact04c$Result" = .done →
      σ.initOf "Cbact04c$AccountRecord" = .done →
      σ.initOf "Cbact04c$CardXrefRecord" = .done →
      σ.initOf "Cbact04c$DisGroupRecord" = .done →
      σ.initOf "Cbact04c$TranCatBalRecord" = .done →
      σ.initOf "Cbact04c$ExternalParms" = .done →
      σ.initOf "Cbact04c$TranRecord" = .done →
      let args := [.ref a1, .ref a2, .ref a3, .ref a4, .ref p1, .ref cs]
      let c := EquivLean.Cobol.run CardDemo.Cbact04c { clock := fun _ => clk } (n + 60)
        (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
          [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
           (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])
      Safe c ∧ MTerm Gen.prog runRef args σ ∧
        ((∃ o, MExec Gen.prog runRef args σ o) ∧
          ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o) ∧
        Sim Rel (Call.mk Gen.prog runRef args σ) c := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 link1 hl clk hc hk1 hk2 hk3 hk4 hD hjb n hn σ
    a1 a2 a3 a4 p1 cs hin1 hin2 hin3 hin4 hlink hclk hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8
  obtain ⟨hstop, -⟩ := Glue.cobol_outputs vals1 vals2 vals3 vals4 link1 clk
    hv1 hv2 hv3 hv4 hl hc hk1 hD n (by omega)
  rw [← initMem_eq] at hstop
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbact04c { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
        [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
         (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok, hstop]; rfl
  have hin : RunIn [.ref a1, .ref a2, .ref a3, .ref a4, .ref p1, .ref cs] σ vals1 vals2 vals3
      vals4 link1 clk :=
    ⟨a1, a2, a3, a4, p1, cs, rfl, hin1, hin2, hin3, hin4, hlink, hclk, hc.1, hv1, hv2, hv3, hv4,
      hl, hD⟩
  have hpre : runSpec.pre [.ref a1, .ref a2, .ref a3, .ref a4, .ref p1, .ref cs] σ :=
    ⟨vals1, vals2, vals3, vals4, link1, clk, hin, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩
  exact ⟨hsafe, run_term _ σ hpre, run_total _ σ hpre,
    java vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 link1 hl clk hc hk1 hk2 hk3 hk4 hD hjb n hn σ
      a1 a2 a3 a4 p1 cs hin1 hin2 hin3 hin4 hlink hclk hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8⟩

end EquivLean.Modernize.Cbact04c.Java

#print axioms EquivLean.Modernize.Cbact04c.Java.java_composite

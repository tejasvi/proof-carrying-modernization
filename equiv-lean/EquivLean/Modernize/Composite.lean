import EquivLean.Modernize.Cbact01c.RustRun
import EquivLean.Modernize.Cbact01c.JavaTermLink
import EquivLean.Modernize.Cbact02c.RustRun
import EquivLean.Modernize.Cbact02c.JavaTermJL
import EquivLean.Modernize.Cbact03c.RustRun
import EquivLean.Modernize.Cbact03c.JavaTermJL
import EquivLean.Modernize.Cbact04c.RustRun
import EquivLean.Modernize.Cbact04c.Every.RustRun
import EquivLean.Modernize.Cbact04c.Every.JavaTermRun
import EquivLean.Modernize.Cbcus01c.RustRun
import EquivLean.Modernize.Cbcus01c.JavaTermJL
import EquivLean.Modernize.Cbtrn01c.RustRun
import EquivLean.Modernize.Cbtrn01c.JavaTermRun
import EquivLean.Modernize.Cbtrn02c.RustRun
import EquivLean.Modernize.Cbtrn02c.JavaTermRun
import EquivLean.Modernize.Cbtrn02c.Any.RustRun
import EquivLean.Modernize.Cbtrn02c.Any.JavaRun
import EquivLean.Modernize.Cbtrn03c.RustRun
import EquivLean.Modernize.Cbtrn03c.JavaTermLink
import EquivLean.Modernize.Cbstm03b.RustRun
import EquivLean.Modernize.Cbstm03b.JavaRun
import EquivLean.Modernize.Cbstm03a.RustRun
import EquivLean.Modernize.Cbstm03a.JavaRun

/-!
# Composite migration statements (safety + normal termination + equivalence/simulation)

For each migrated CardDemo program, a single composite theorem combining the generated statement
with explicit source safety and target termination/totality, built directly from the proved
theorems with no new proof search:

* **Rust (`rust_composite`):** under the hypotheses of `Rust.Statement`, the COBOL run is `Safe`
  (`EquivLean.Cobol.Ok`), the Rust run returns normally (`∃ out, run … = .ok out`, no panic or
  divergence), and `Equiv Rel (run …) (EquivLean.Cobol.run …)` holds.
* **Java (`java_composite`):** under the hypotheses of `Java.Statement`, the COBOL run is `Safe`,
  every execution of the Java method terminates (`MTerm`, and at least one execution exists and
  every execution satisfies `runSpec.post`), and `Sim Rel (Call.mk …) (EquivLean.Cobol.run …)`
  holds.

The restricted CBACT04C Java theorem is in `EquivLean.Modernize.CompositeRestricted` (its helper
modules share names with `Cbact04c.Every.Java`).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std
open Jimple EquivLean.Jimple

namespace EquivLean.Modernize

/-- From two-way equivalence `Equiv R r c` and a normal Rust return `r = .ok out`, the COBOL run
`c` is `Safe` (`Equiv.safe_iff`), the Rust run returns normally, and `Equiv R r c` holds. -/
theorem rust_composite_of_equiv_ok {α : Type}
    {R : Except Error α → Signal × Cobol.State → Prop}
    {r : Result α} {c : EquivLean.Cobol.Exec}
    (heq : Equiv R r c) (hok : ∃ out, r = .ok out) :
    Safe c ∧ (∃ out, r = .ok out) ∧ Equiv R r c :=
  let ⟨out, hout⟩ := hok
  ⟨heq.safe_iff.1 ⟨.ok out, hout⟩, hok, heq⟩

/-- From COBOL safety `Safe c`, `Sim R call c`, and `MTerm` + total correctness of `call`, package
all four claims into a single conjunction. -/
theorem java_composite_of {R : Out → Signal × Cobol.State → Prop}
    {P : Jimple.Program} {m : MethodRef} {args : List Jimple.Value} {σ : Jimple.State}
    {S : Spec} {c : EquivLean.Cobol.Exec}
    (hsafe : Safe c) (hsim : Sim R (Call.mk P m args σ) c)
    (hterm : MTerm P m args σ)
    (htot : (∃ o, MExec P m args σ o) ∧ ∀ o, MExec P m args σ o → S.post args σ o) :
    Safe c ∧ MTerm P m args σ ∧
      ((∃ o, MExec P m args σ o) ∧ ∀ o, MExec P m args σ o → S.post args σ o) ∧
      Sim R (Call.mk P m args σ) c :=
  ⟨hsafe, hterm, htot, hsim⟩

/-! ## 1. CBACT01C -/

namespace Cbact01c.Rust

theorem rust_composite :
    ∀ (vals1 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, AccountRecord.Valid v) →
      vals1.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length < n →
      ∀ (s1 : Slice cbact01c.AccountRecord),
      AcctfileFileOf s1 vals1 →
      let c := EquivLean.Cobol.run CardDemo.Cbact01c
        { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
        (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)])
      Safe c ∧ (∃ out, cbact01c.run s1 = .ok out) ∧ Equiv Rel (cbact01c.run s1) c := by
  intro vals1 hv1 hb n hn s1 hs1
  obtain ⟨out, hrun, -⟩ := run_spec s1 vals1 hs1 hv1 hb
  exact rust_composite_of_equiv_ok (rust vals1 hv1 hb n hn s1 hs1) ⟨out, hrun⟩

end Cbact01c.Rust

namespace Cbact01c.Java

theorem java_composite :
    ∀ (vals1 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, AccountRecord.Valid v) →
      vals1.length < 2 ^ 27 →
      ∀ n : Nat, vals1.length < n →
      ∀ (σ : Jimple.State) (a1 : Addr),
      AcctfileFileAt σ a1 vals1 →
      σ.initOf "Cbact01c" = .done →
      σ.initOf "Cbact01c$Result" = .done →
      σ.initOf "Cbact01c$AccountRecord" = .done →
      σ.initOf "Cbact01c$ArrArrayRec" = .done →
      σ.initOf "Cbact01c$OutAcctRec" = .done →
      let c := EquivLean.Cobol.run CardDemo.Cbact01c
        { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
        (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)])
      Safe c ∧ MTerm Gen.prog runRef [.ref a1] σ ∧
        ((∃ o, MExec Gen.prog runRef [.ref a1] σ o) ∧
          ∀ o, MExec Gen.prog runRef [.ref a1] σ o → runSpec.post [.ref a1] σ o) ∧
        Sim Rel (Call.mk Gen.prog runRef [.ref a1] σ) c := by
  intro vals1 hv1 hjb n hn σ a1 hin1 hi1 hi2 hi3 hi4 hi5
  obtain ⟨hstop, -⟩ := Glue.cobol_outputs vals1 hv1 n hn
  rw [← initMem_eq] at hstop
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbact01c
      { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
      (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok, hstop]; rfl
  have hpre : runSpec.pre [.ref a1] σ := ⟨vals1, ⟨a1, rfl, hin1, hv1⟩, hi1, hi2, hi3, hi4, hi5⟩
  exact java_composite_of hsafe (java vals1 hv1 hjb n hn σ a1 hin1 hi1 hi2 hi3 hi4 hi5)
    (run_term [.ref a1] σ hpre) (run_total [.ref a1] σ hpre)

end Cbact01c.Java

/-! ## 2. CBACT02C -/

namespace Cbact02c.Rust

theorem rust_composite :
    ∀ (vals1 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, CardRecord.Valid v) →
      vals1.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length < n →
      ∀ (s1 : Slice cbact02c.CardRecord),
      CardfileFileOf s1 vals1 →
      let c := EquivLean.Cobol.run CardDemo.Cbact02c {} (n + 20)
        (CardDemo.Cbact02c.initState initMem [(1, vals1.map CardRecord.encode)])
      Safe c ∧ (∃ out, cbact02c.run s1 = .ok out) ∧ Equiv Rel (cbact02c.run s1) c := by
  intro vals1 hv1 hb n hn s1 hs1
  obtain ⟨out, hrun, -⟩ := run_spec s1 vals1 hs1 hv1 hb
  exact rust_composite_of_equiv_ok (rust vals1 hv1 hb n hn s1 hs1) ⟨out, hrun⟩

end Cbact02c.Rust

namespace Cbact02c.Java

theorem java_composite :
    ∀ (vals1 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, CardRecord.Valid v) →
      vals1.length < 2 ^ 27 →
      ∀ n : Nat, vals1.length < n →
      ∀ (σ : Jimple.State) (a1 : Addr),
      CardfileFileAt σ a1 vals1 →
      σ.initOf "Cbact02c" = .done →
      σ.initOf "Cbact02c$Result" = .done →
      σ.initOf "Cbact02c$CardRecord" = .done →
      let c := EquivLean.Cobol.run CardDemo.Cbact02c {} (n + 20)
        (CardDemo.Cbact02c.initState initMem [(1, vals1.map CardRecord.encode)])
      Safe c ∧ MTerm Gen.prog runRef [.ref a1] σ ∧
        ((∃ o, MExec Gen.prog runRef [.ref a1] σ o) ∧
          ∀ o, MExec Gen.prog runRef [.ref a1] σ o → runSpec.post [.ref a1] σ o) ∧
        Sim Rel (Call.mk Gen.prog runRef [.ref a1] σ) c := by
  intro vals1 hv hjb n hn σ a1 hin hi1 hi2 hi3
  have hm : initMem.size = 323 := by rw [initMem_size, CardDemo.Cbact02c.memSize_eq]
  have hlen : ∀ r ∈ vals1.map CardRecord.encode, r.length = 150 := by
    intro r hr; obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode cardRecord_contig (hv v hv')
  obtain ⟨hstop, _⟩ := CardDemo.Cbact02c.cbact02c_lists initMem hm
    (vals1.map CardRecord.encode) n hlen (by simpa using hn)
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbact02c {} (n + 20)
      (CardDemo.Cbact02c.initState initMem [(1, vals1.map CardRecord.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok, hstop]; rfl
  have hpre : runSpec.pre [.ref a1] σ := ⟨a1, vals1, rfl, hin, hv, hi1, hi2, hi3⟩
  exact java_composite_of hsafe (java vals1 hv hjb n hn σ a1 hin hi1 hi2 hi3)
    (run_term [.ref a1] σ hpre) (run_total [.ref a1] σ hpre)

end Cbact02c.Java

/-! ## 3. CBACT03C -/

namespace Cbact03c.Rust

theorem rust_composite :
    ∀ (vals1 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, CardXrefRecord.Valid v) →
      vals1.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length < n →
      ∀ (s1 : Slice cbact03c.CardXrefRecord),
      XreffileFileOf s1 vals1 →
      let c := EquivLean.Cobol.run CardDemo.Cbact03c {} (n + 20)
        (CardDemo.Cbact03c.initState initMem [(1, vals1.map CardXrefRecord.encode)])
      Safe c ∧ (∃ out, cbact03c.run s1 = .ok out) ∧ Equiv Rel (cbact03c.run s1) c := by
  intro vals1 hv1 hb n hn s1 hs1
  obtain ⟨out, hrun, -⟩ := run_spec s1 vals1 hs1 hv1 hb
  exact rust_composite_of_equiv_ok (rust vals1 hv1 hb n hn s1 hs1) ⟨out, hrun⟩

end Cbact03c.Rust

namespace Cbact03c.Java

theorem java_composite :
    ∀ (vals1 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, CardXrefRecord.Valid v) →
      vals1.length < 2 ^ 27 →
      ∀ n : Nat, vals1.length < n →
      ∀ (σ : Jimple.State) (a1 : Addr),
      XreffileFileAt σ a1 vals1 →
      σ.initOf "Cbact03c" = .done →
      σ.initOf "Cbact03c$Result" = .done →
      σ.initOf "Cbact03c$CardXrefRecord" = .done →
      σ.initOf "Cbact03c$State" = .done →
      let c := EquivLean.Cobol.run CardDemo.Cbact03c {} (n + 20)
        (CardDemo.Cbact03c.initState initMem [(1, vals1.map CardXrefRecord.encode)])
      Safe c ∧ MTerm Gen.prog runRef [.ref a1] σ ∧
        ((∃ o, MExec Gen.prog runRef [.ref a1] σ o) ∧
          ∀ o, MExec Gen.prog runRef [.ref a1] σ o → runSpec.post [.ref a1] σ o) ∧
        Sim Rel (Call.mk Gen.prog runRef [.ref a1] σ) c := by
  intro vals1 hv hjb n hn σ a1 hin hi1 hi2 hi3 hi4
  have hm : initMem.size = 123 := by rw [initMem_size, CardDemo.Cbact03c.memSize_eq]
  have hlen : ∀ r ∈ vals1.map CardXrefRecord.encode, r.length = 50 := by
    intro r hr; obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode cardXrefRecord_contig (hv v hv')
  obtain ⟨hstop, _⟩ := CardDemo.Cbact03c.cbact03c_lists initMem hm
    (vals1.map CardXrefRecord.encode) n hlen (by simpa using hn)
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbact03c {} (n + 20)
      (CardDemo.Cbact03c.initState initMem [(1, vals1.map CardXrefRecord.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok, hstop]; rfl
  have hpre : runSpec.pre [.ref a1] σ := ⟨a1, vals1, rfl, hin, hv, hi1, hi2, hi3, hi4⟩
  exact java_composite_of hsafe (java vals1 hv hjb n hn σ a1 hin hi1 hi2 hi3 hi4)
    (run_term [.ref a1] σ hpre) (run_total [.ref a1] σ hpre)

end Cbact03c.Java

/-! ## 4. CBACT04C (Every and restricted Rust) -/

namespace Cbact04c.Every.Rust

theorem rust_composite :
    ∀ (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, TranCatBalRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, AccountRecord.Valid v) →
      (∀ v ∈ vals4, DisGroupRecord.Valid v) →
      ∀ (link1 : List EquivLean.Cobol.Rec.FVal), ExternalParms.Valid link1 →
      ∀ (clk : List UInt8), CurrentDate clk →
      EquivLean.Modernize.Cbact04c.Every.Domain vals1 vals2 vals3 vals4 link1 →
      vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length < n →
      ∀ (s1 : Slice cbact04c_t.TranCatBalRecord) (s2 : Slice cbact04c_t.CardXrefRecord)
        (s3 : Slice cbact04c_t.AccountRecord) (s4 : Slice cbact04c_t.DisGroupRecord)
        (q1 : cbact04c_t.ExternalParms) (rclk : Std.Array Std.U8 21#usize),
      TcatbalFileOf s1 vals1 →
      XrefFileOf s2 vals2 →
      AccountFileOf s3 vals3 →
      DiscgrpFileOf s4 vals4 →
      ExternalParms.vals q1 = link1 →
      rclk.val.map (·.val) = rustLine clk →
      let c := EquivLean.Cobol.run CardDemo.Cbact04c { clock := fun _ => clk } (n + 60)
        (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
          [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
           (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])
      Safe c ∧ (∃ out, cbact04c_t.run s1 s2 s3 s4 q1 rclk = .ok out) ∧
        Equiv Rel (cbact04c_t.run s1 s2 s3 s4 q1 rclk) c := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 link1 hl clk hc hD hb n hn s1 s2 s3 s4 q1 rclk
    hs1 hs2 hs3 hs4 hq1 hclk
  obtain ⟨out, hrun, -⟩ := run_spec s1 s2 s3 s4 q1 rclk vals1 vals2 vals3 vals4 link1 clk
    hs1 hs2 hs3 hs4 hq1 hclk hc.1 hv1 hv2 hv3 hv4 hl hD hb
  exact rust_composite_of_equiv_ok
    (rust vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 link1 hl clk hc hD hb n hn
      s1 s2 s3 s4 q1 rclk hs1 hs2 hs3 hs4 hq1 hclk) ⟨out, hrun⟩

end Cbact04c.Every.Rust

namespace Cbact04c.Every.Java

theorem java_composite :
    ∀ (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, TranCatBalRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, AccountRecord.Valid v) →
      (∀ v ∈ vals4, DisGroupRecord.Valid v) →
      ∀ (link1 : List EquivLean.Cobol.Rec.FVal), ExternalParms.Valid link1 →
      ∀ (clk : List UInt8), CurrentDate clk →
      EquivLean.Modernize.Cbact04c.Every.Domain vals1 vals2 vals3 vals4 link1 →
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
      Safe c ∧ MTerm Cbact04c.Java.Gen.prog runRef args σ ∧
        ((∃ o, MExec Cbact04c.Java.Gen.prog runRef args σ o) ∧
          ∀ o, MExec Cbact04c.Java.Gen.prog runRef args σ o → runSpec.post args σ o) ∧
        Sim Rel (Call.mk Cbact04c.Java.Gen.prog runRef args σ) c := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 link1 hl clk hc hD hjb n hn σ a1 a2 a3 a4 p1 cs
    hin1 hin2 hin3 hin4 hlink hclk hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8
  obtain ⟨hsig, -⟩ := Glue.cobol_outputs vals1 vals2 vals3 vals4 link1 clk
    hv1 hv2 hv3 hv4 hl hc hD n (by omega)
  rw [← initMem_eq] at hsig
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbact04c { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
        [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
         (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok]
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  have hin : RunIn [.ref a1, .ref a2, .ref a3, .ref a4, .ref p1, .ref cs] σ vals1 vals2 vals3
      vals4 link1 clk :=
    ⟨a1, a2, a3, a4, p1, cs, rfl, hin1, hin2, hin3, hin4, hlink, hclk, hc.1, hv1, hv2, hv3, hv4,
      hl, hD⟩
  have hpre : runSpec.pre [.ref a1, .ref a2, .ref a3, .ref a4, .ref p1, .ref cs] σ :=
    ⟨vals1, vals2, vals3, vals4, link1, clk, hin, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩
  exact java_composite_of hsafe
    (java vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 link1 hl clk hc hD hjb n hn σ
      a1 a2 a3 a4 p1 cs hin1 hin2 hin3 hin4 hlink hclk hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8)
    (run_term _ σ hpre) (run_total _ σ hpre)

end Cbact04c.Every.Java

namespace Cbact04c.Rust

theorem rust_composite :
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
      vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length < n →
      ∀ (s1 : Slice cbact04c_t.TranCatBalRecord) (s2 : Slice cbact04c_t.CardXrefRecord)
        (s3 : Slice cbact04c_t.AccountRecord) (s4 : Slice cbact04c_t.DisGroupRecord)
        (q1 : cbact04c_t.ExternalParms) (rclk : Std.Array Std.U8 21#usize),
      TcatbalFileOf s1 vals1 →
      XrefFileOf s2 vals2 →
      AccountFileOf s3 vals3 →
      DiscgrpFileOf s4 vals4 →
      ExternalParms.vals q1 = link1 →
      rclk.val.map (·.val) = rustLine clk →
      let c := EquivLean.Cobol.run CardDemo.Cbact04c { clock := fun _ => clk } (n + 60)
        (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
          [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
           (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])
      Safe c ∧ (∃ out, cbact04c_t.run s1 s2 s3 s4 q1 rclk = .ok out) ∧
        Equiv Rel (cbact04c_t.run s1 s2 s3 s4 q1 rclk) c := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 link1 hl clk hc hk1 hk2 hk3 hk4 hD hb n hn
    s1 s2 s3 s4 q1 rclk hs1 hs2 hs3 hs4 hq1 hclk
  obtain ⟨out, hrun, -⟩ := run_spec s1 s2 s3 s4 q1 rclk vals1 vals2 vals3 vals4 link1 clk
    hs1 hs2 hs3 hs4 hq1 hclk hc.1 hv1 hv2 hv3 hv4 hl hD hb
  exact rust_composite_of_equiv_ok
    (rust vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 link1 hl clk hc hk1 hk2 hk3 hk4 hD hb n hn
      s1 s2 s3 s4 q1 rclk hs1 hs2 hs3 hs4 hq1 hclk) ⟨out, hrun⟩

end Cbact04c.Rust

/-! ## 5. CBCUS01C -/

namespace Cbcus01c.Rust

theorem rust_composite :
    ∀ (vals1 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, CustomerRecord.Valid v) →
      vals1.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length < n →
      ∀ (s1 : Slice cbcus01c.CustomerRecord),
      CustfileFileOf s1 vals1 →
      let c := EquivLean.Cobol.run CardDemo.Cbcus01c {} (n + 20)
        (CardDemo.Cbcus01c.initState initMem [(1, vals1.map CustomerRecord.encode)])
      Safe c ∧ (∃ out, cbcus01c.run s1 = .ok out) ∧ Equiv Rel (cbcus01c.run s1) c := by
  intro vals1 hv1 hb n hn s1 hs1
  obtain ⟨out, hrun, -⟩ := run_spec s1 vals1 hs1 hv1 hb
  exact rust_composite_of_equiv_ok (rust vals1 hv1 hb n hn s1 hs1) ⟨out, hrun⟩

end Cbcus01c.Rust

namespace Cbcus01c.Java

theorem java_composite :
    ∀ (vals1 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, CustomerRecord.Valid v) →
      vals1.length < 2 ^ 27 →
      ∀ n : Nat, vals1.length < n →
      ∀ (σ : Jimple.State) (a1 : Addr),
      CustfileFileAt σ a1 vals1 →
      σ.initOf "Cbcus01c" = .done →
      σ.initOf "Cbcus01c$Result" = .done →
      σ.initOf "Cbcus01c$CustomerRecord" = .done →
      let c := EquivLean.Cobol.run CardDemo.Cbcus01c {} (n + 20)
        (CardDemo.Cbcus01c.initState initMem [(1, vals1.map CustomerRecord.encode)])
      Safe c ∧ MTerm Gen.prog runRef [.ref a1] σ ∧
        ((∃ o, MExec Gen.prog runRef [.ref a1] σ o) ∧
          ∀ o, MExec Gen.prog runRef [.ref a1] σ o → runSpec.post [.ref a1] σ o) ∧
        Sim Rel (Call.mk Gen.prog runRef [.ref a1] σ) c := by
  intro vals1 hv hjb n hn σ a1 hin hi1 hi2 hi3
  have hm : initMem.size = 1023 := by rw [initMem_size, CardDemo.Cbcus01c.memSize_eq]
  have hlen : ∀ r ∈ vals1.map CustomerRecord.encode, r.length = 500 := by
    intro r hr; obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode customerRecord_contig (hv v hv')
  obtain ⟨hstop, _⟩ := CardDemo.Cbcus01c.cbcus01c_lists initMem hm
    (vals1.map CustomerRecord.encode) n hlen (by simpa using hn)
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbcus01c {} (n + 20)
      (CardDemo.Cbcus01c.initState initMem [(1, vals1.map CustomerRecord.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok, hstop]; rfl
  have hpre : runSpec.pre [.ref a1] σ := ⟨a1, vals1, rfl, hin, hv, hi1, hi2, hi3⟩
  exact java_composite_of hsafe (java vals1 hv hjb n hn σ a1 hin hi1 hi2 hi3)
    (run_term [.ref a1] σ hpre) (run_total [.ref a1] σ hpre)

end Cbcus01c.Java

/-! ## 6. CBTRN01C -/

namespace Cbtrn01c.Rust

theorem rust_composite :
    ∀ (vals1 vals2 vals3 vals4 vals5 vals6 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, DalytranRecord.Valid v) →
      (∀ v ∈ vals2, FdCustfileRec.Valid v) →
      (∀ v ∈ vals3, CardXrefRecord.Valid v) →
      (∀ v ∈ vals4, FdCardfileRec.Valid v) →
      (∀ v ∈ vals5, AccountRecord.Valid v) →
      (∀ v ∈ vals6, FdTranfileRec.Valid v) →
      vals1.length + vals2.length + vals3.length + vals4.length + vals5.length + vals6.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length + vals5.length + vals6.length < n →
      ∀ (s1 : Slice cbtrn01c.DalytranRecord) (s2 : Slice cbtrn01c.FdCustfileRec)
        (s3 : Slice cbtrn01c.CardXrefRecord) (s4 : Slice cbtrn01c.FdCardfileRec)
        (s5 : Slice cbtrn01c.AccountRecord) (s6 : Slice cbtrn01c.FdTranfileRec),
      DalytranFileOf s1 vals1 →
      CustomerFileOf s2 vals2 →
      XrefFileOf s3 vals3 →
      CardFileOf s4 vals4 →
      AccountFileOf s5 vals5 →
      TransactFileOf s6 vals6 →
      let c := EquivLean.Cobol.run CardDemo.Cbtrn01c {} (n + 40)
        (CardDemo.Cbtrn01c.initState initMem
          [(1, vals1.map DalytranRecord.encode), (2, vals2.map FdCustfileRec.encode),
           (3, vals3.map CardXrefRecord.encode), (4, vals4.map FdCardfileRec.encode),
           (5, vals5.map AccountRecord.encode), (6, vals6.map FdTranfileRec.encode)])
      Safe c ∧ (∃ out, cbtrn01c.run s1 s2 s3 s4 s5 s6 = .ok out) ∧
        Equiv Rel (cbtrn01c.run s1 s2 s3 s4 s5 s6) c := by
  intro vals1 vals2 vals3 vals4 vals5 vals6 hv1 hv2 hv3 hv4 hv5 hv6 hb n hn
    s1 s2 s3 s4 s5 s6 hs1 hs2 hs3 hs4 hs5 hs6
  obtain ⟨out, hrun, -⟩ := run_spec s1 s2 s3 s4 s5 s6 vals1 vals3 vals5 hs1 hs3 hs5 hv1 hv3 hv5
    (by omega) (by omega) (by omega)
  exact rust_composite_of_equiv_ok
    (rust vals1 vals2 vals3 vals4 vals5 vals6 hv1 hv2 hv3 hv4 hv5 hv6 hb n hn
      s1 s2 s3 s4 s5 s6 hs1 hs2 hs3 hs4 hs5 hs6) ⟨out, hrun⟩

end Cbtrn01c.Rust

namespace Cbtrn01c.Java

theorem java_composite :
    ∀ (vals1 vals2 vals3 vals4 vals5 vals6 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, DalytranRecord.Valid v) →
      (∀ v ∈ vals2, FdCustfileRec.Valid v) →
      (∀ v ∈ vals3, CardXrefRecord.Valid v) →
      (∀ v ∈ vals4, FdCardfileRec.Valid v) →
      (∀ v ∈ vals5, AccountRecord.Valid v) →
      (∀ v ∈ vals6, FdTranfileRec.Valid v) →
      vals1.length + vals2.length + vals3.length + vals4.length + vals5.length + vals6.length < 2 ^ 27 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length + vals5.length + vals6.length < n →
      ∀ (σ : Jimple.State) (a1 a2 a3 a4 a5 a6 : Addr),
      DalytranFileAt σ a1 vals1 →
      CustomerFileAt σ a2 vals2 →
      XrefFileAt σ a3 vals3 →
      CardFileAt σ a4 vals4 →
      AccountFileAt σ a5 vals5 →
      TransactFileAt σ a6 vals6 →
      σ.initOf "Cbtrn01c" = .done →
      σ.initOf "Cbtrn01c$Result" = .done →
      σ.initOf "Cbtrn01c$AccountRecord" = .done →
      σ.initOf "Cbtrn01c$CardXrefRecord" = .done →
      σ.initOf "Cbtrn01c$DalytranRecord" = .done →
      σ.initOf "Cbtrn01c$FdCardfileRec" = .done →
      σ.initOf "Cbtrn01c$FdCustfileRec" = .done →
      σ.initOf "Cbtrn01c$FdTranfileRec" = .done →
      let args := [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5, .ref a6]
      let c := EquivLean.Cobol.run CardDemo.Cbtrn01c {} (n + 40)
        (CardDemo.Cbtrn01c.initState initMem
          [(1, vals1.map DalytranRecord.encode), (2, vals2.map FdCustfileRec.encode),
           (3, vals3.map CardXrefRecord.encode), (4, vals4.map FdCardfileRec.encode),
           (5, vals5.map AccountRecord.encode), (6, vals6.map FdTranfileRec.encode)])
      Safe c ∧ MTerm Gen.prog runRef args σ ∧
        ((∃ o, MExec Gen.prog runRef args σ o) ∧
          ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o) ∧
        Sim Rel (Call.mk Gen.prog runRef args σ) c := by
  intro vals1 vals2 vals3 vals4 vals5 vals6 hv1 hv2 hv3 hv4 hv5 hv6 hjb n hn σ
    a1 a2 a3 a4 a5 a6 hin1 hin2 hin3 hin4 hin5 hin6 hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8
  have hm : initMem.size = 3441 := by rw [initMem_size, CardDemo.Cbtrn01c.memSize_eq]
  have htr : ∀ t ∈ vals1.map DalytranRecord.encode, t.length = 350 := by
    intro r hr; obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode dalytranRecord_contig (hv1 v hv')
  have hac : ∀ a ∈ vals5.map AccountRecord.encode, a.length = 300 := by
    intro r hr; obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode accountRecord_contig (hv5 v hv')
  have hxeq : vals3.map CardXrefRecord.encode =
      (vals3.map Model.xrefOf).map CardDemo.Cbtrn01c.Xref.bytes := by
    rw [List.map_map]
    exact List.map_congr_left fun x hx => (Model.xrefOf_bytes (hv3 x hx)).1.symm
  have hxv : ∀ x ∈ vals3.map Model.xrefOf, x.valid := by
    intro x hx; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact (Model.xrefOf_bytes (hv3 y hy)).2
  obtain ⟨hstop, _⟩ := CardDemo.Cbtrn01c.cbtrn01c_verifies_all initMem hm
    (vals1.map DalytranRecord.encode) htr (vals3.map Model.xrefOf) hxv
    (vals5.map AccountRecord.encode) hac (vals2.map FdCustfileRec.encode)
    (vals4.map FdCardfileRec.encode) (vals6.map FdTranfileRec.encode) n
    (by simp only [List.length_map]; omega)
  rw [← hxeq] at hstop
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbtrn01c {} (n + 40)
      (CardDemo.Cbtrn01c.initState initMem
        [(1, vals1.map DalytranRecord.encode), (2, vals2.map FdCustfileRec.encode),
         (3, vals3.map CardXrefRecord.encode), (4, vals4.map FdCardfileRec.encode),
         (5, vals5.map AccountRecord.encode), (6, vals6.map FdTranfileRec.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok, hstop]; rfl
  have hpre : runSpec.pre [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5, .ref a6] σ :=
    ⟨a1, a2, a3, a4, a5, a6, vals1, vals3, vals5, rfl, hin1, hin3, hin5, hv1, hv3, hv5,
      hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩
  exact java_composite_of hsafe
    (java vals1 vals2 vals3 vals4 vals5 vals6 hv1 hv2 hv3 hv4 hv5 hv6 hjb n hn σ
      a1 a2 a3 a4 a5 a6 hin1 hin2 hin3 hin4 hin5 hin6 hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8)
    (run_term _ σ hpre) (run_total _ σ hpre)

end Cbtrn01c.Java

/-! ## 7. CBTRN02C (Any and restricted Rust) -/

namespace Cbtrn02c.Any.Rust

theorem rust_composite :
    ∀ (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, DalytranRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, AccountRecord.Valid v) →
      (∀ v ∈ vals4, TranCatBalRecord.Valid v) →
      ∀ (clk : List UInt8), CurrentDate clk →
      EquivLean.Modernize.Cbtrn02c.Any.Domain vals1 vals2 vals3 vals4 →
      vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length < n →
      ∀ (s1 : Slice cbtrn02c.DalytranRecord) (s2 : Slice cbtrn02c.CardXrefRecord)
        (s3 : Slice cbtrn02c.AccountRecord) (s4 : Slice cbtrn02c.TranCatBalRecord)
        (rclk : Std.Array Std.U8 21#usize),
      DalytranFileOf s1 vals1 →
      XrefFileOf s2 vals2 →
      AccountFileOf s3 vals3 →
      TcatbalFileOf s4 vals4 →
      rclk.val.map (·.val) = rustLine clk →
      let c := EquivLean.Cobol.run CardDemo.Cbtrn02c { clock := fun _ => clk } (n + 60)
        (CardDemo.Cbtrn02c.initState initMem
          [(1, vals1.map DalytranRecord.encode), (3, vals2.map CardXrefRecord.encode),
           (5, vals3.map AccountRecord.encode), (6, vals4.map TranCatBalRecord.encode)])
      Safe c ∧ (∃ out, cbtrn02c.run s1 s2 s3 s4 rclk = .ok out) ∧
        Equiv Rel (cbtrn02c.run s1 s2 s3 s4 rclk) c := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 clk hc hD hb n hn s1 s2 s3 s4 rclk
    hs1 hs2 hs3 hs4 hclk
  obtain ⟨out, hrun, -⟩ := run_spec s1 s2 s3 s4 rclk vals1 vals2 vals3 vals4 clk
    hs1 hs2 hs3 hs4 hclk hc hv1 hv2 hv3 hv4 hD hb
  exact rust_composite_of_equiv_ok
    (rust vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 clk hc hD hb n hn
      s1 s2 s3 s4 rclk hs1 hs2 hs3 hs4 hclk) ⟨out, hrun⟩

end Cbtrn02c.Any.Rust

namespace Cbtrn02c.Any.Java

theorem java_composite :
    ∀ (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, DalytranRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, AccountRecord.Valid v) →
      (∀ v ∈ vals4, TranCatBalRecord.Valid v) →
      ∀ (clk : List UInt8), CurrentDate clk →
      EquivLean.Modernize.Cbtrn02c.Any.Domain vals1 vals2 vals3 vals4 →
      vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 27 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length < n →
      ∀ (σ : Jimple.State) (a1 a2 a3 a4 cs : Addr),
      DalytranFileAt σ a1 vals1 →
      XrefFileAt σ a2 vals2 →
      AccountFileAt σ a3 vals3 →
      TcatbalFileAt σ a4 vals4 →
      JStrAt σ (.ref cs) (cp037Str clk) →
      ClinitRan EquivLean.Modernize.Cbtrn02c.Java.Gen.prog "Cbtrn02c" σ →
      σ.initOf "Cbtrn02c$Result" = .done →
      σ.initOf "Cbtrn02c$AccountRecord" = .done →
      σ.initOf "Cbtrn02c$CardXrefRecord" = .done →
      σ.initOf "Cbtrn02c$DalytranRecord" = .done →
      σ.initOf "Cbtrn02c$TranCatBalRecord" = .done →
      σ.initOf "Cbtrn02c$RejectRecord" = .done →
      σ.initOf "Cbtrn02c$TranRecord" = .done →
      let args := [.ref a1, .ref a2, .ref a3, .ref a4, .ref cs]
      let c := EquivLean.Cobol.run CardDemo.Cbtrn02c { clock := fun _ => clk } (n + 60)
        (CardDemo.Cbtrn02c.initState initMem
          [(1, vals1.map DalytranRecord.encode), (3, vals2.map CardXrefRecord.encode),
           (5, vals3.map AccountRecord.encode), (6, vals4.map TranCatBalRecord.encode)])
      Safe c ∧ MTerm EquivLean.Modernize.Cbtrn02c.Java.Gen.prog runRef args σ ∧
        ((∃ o, MExec EquivLean.Modernize.Cbtrn02c.Java.Gen.prog runRef args σ o) ∧
          ∀ o, MExec EquivLean.Modernize.Cbtrn02c.Java.Gen.prog runRef args σ o →
            runSpec.post args σ o) ∧
        Sim Rel (Call.mk EquivLean.Modernize.Cbtrn02c.Java.Gen.prog runRef args σ) c := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 clk hc hD hjb n hn σ a1 a2 a3 a4 cs
    hin1 hin2 hin3 hin4 hclk hcl hi2 hi3 hi4 hi5 hi6 hi7 hi8
  obtain ⟨hsig, -⟩ := Glue.cobol_outputs vals1 vals2 vals3 vals4 clk hv1 hv2 hv3 hv4 hc hD n (by omega)
  rw [← initMem_eq] at hsig
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbtrn02c { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbtrn02c.initState initMem
        [(1, vals1.map DalytranRecord.encode), (3, vals2.map CardXrefRecord.encode),
         (5, vals3.map AccountRecord.encode), (6, vals4.map TranCatBalRecord.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok]
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  have hin : RunIn [.ref a1, .ref a2, .ref a3, .ref a4, .ref cs] σ vals1 vals2 vals3 vals4 clk :=
    ⟨a1, a2, a3, a4, cs, rfl, hin1, hin2, hin3, hin4, hclk, hc, hv1, hv2, hv3, hv4, hD, hjb⟩
  have hpre : runSpec.pre [.ref a1, .ref a2, .ref a3, .ref a4, .ref cs] σ :=
    ⟨vals1, vals2, vals3, vals4, clk, hin, hcl.1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩
  exact java_composite_of hsafe
    (java vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 clk hc hD hjb n hn σ a1 a2 a3 a4 cs
      hin1 hin2 hin3 hin4 hclk hcl hi2 hi3 hi4 hi5 hi6 hi7 hi8)
    (run_term _ σ hpre) (run_total _ σ hpre)

end Cbtrn02c.Any.Java

namespace Cbtrn02c.Rust

theorem rust_composite :
    ∀ (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, DalytranRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, AccountRecord.Valid v) →
      (∀ v ∈ vals4, TranCatBalRecord.Valid v) →
      ∀ (clk : List UInt8), CurrentDate clk →
      EquivLean.Modernize.Cbtrn02c.Domain vals1 vals2 vals3 vals4 →
      vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length < n →
      ∀ (s1 : Slice cbtrn02c.DalytranRecord) (s2 : Slice cbtrn02c.CardXrefRecord)
        (s3 : Slice cbtrn02c.AccountRecord) (s4 : Slice cbtrn02c.TranCatBalRecord)
        (rclk : Std.Array Std.U8 21#usize),
      DalytranFileOf s1 vals1 →
      XrefFileOf s2 vals2 →
      AccountFileOf s3 vals3 →
      TcatbalFileOf s4 vals4 →
      rclk.val.map (·.val) = rustLine clk →
      let c := EquivLean.Cobol.run CardDemo.Cbtrn02c { clock := fun _ => clk } (n + 60)
        (CardDemo.Cbtrn02c.initState initMem
          [(1, vals1.map DalytranRecord.encode), (3, vals2.map CardXrefRecord.encode),
           (5, vals3.map AccountRecord.encode), (6, vals4.map TranCatBalRecord.encode)])
      Safe c ∧ (∃ out, cbtrn02c.run s1 s2 s3 s4 rclk = .ok out) ∧
        Equiv Rel (cbtrn02c.run s1 s2 s3 s4 rclk) c := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 clk hc hD hb n hn s1 s2 s3 s4 rclk
    hs1 hs2 hs3 hs4 hclk
  obtain ⟨out, hrun, -⟩ := run_spec s1 s2 s3 s4 rclk vals1 vals2 vals3 vals4 clk
    hs1 hs2 hs3 hs4 hclk hc hv1 hv2 hv3 hv4 hD hb
  exact rust_composite_of_equiv_ok
    (rust vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 clk hc hD hb n hn
      s1 s2 s3 s4 rclk hs1 hs2 hs3 hs4 hclk) ⟨out, hrun⟩

end Cbtrn02c.Rust

/-! ## 8. CBTRN03C -/

namespace Cbtrn03c.Rust

theorem rust_composite :
    ∀ (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, TranRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, TranTypeRecord.Valid v) →
      (∀ v ∈ vals4, TranCatRecord.Valid v) →
      (∀ v ∈ vals5, WsDateparmRecord.Valid v) →
      EquivLean.Modernize.Cbtrn03c.Domain vals1 vals2 vals3 vals4 vals5 →
      vals1.length + vals2.length + vals3.length + vals4.length + vals5.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length + vals5.length < n →
      ∀ (s1 : Slice cbtrn03c.TranRecord) (s2 : Slice cbtrn03c.CardXrefRecord)
        (s3 : Slice cbtrn03c.TranTypeRecord) (s4 : Slice cbtrn03c.TranCatRecord)
        (s5 : Slice cbtrn03c.WsDateparmRecord),
      TransactFileOf s1 vals1 →
      XrefFileOf s2 vals2 →
      TrantypeFileOf s3 vals3 →
      TrancatgFileOf s4 vals4 →
      DateParmsFileOf s5 vals5 →
      let c := EquivLean.Cobol.run CardDemo.Cbtrn03c {} (n + 60)
        (CardDemo.Cbtrn03c.initState initMem
          [(1, vals1.map TranRecord.encode), (2, vals2.map CardXrefRecord.encode),
           (3, vals3.map TranTypeRecord.encode), (4, vals4.map TranCatRecord.encode),
           (6, vals5.map (fun r => WsDateparmRecord.encode r ++ List.replicate 59 64))])
      Safe c ∧ (∃ out, cbtrn03c.run s1 s2 s3 s4 s5 = .ok out) ∧
        Equiv Rel (cbtrn03c.run s1 s2 s3 s4 s5) c := by
  intro vals1 vals2 vals3 vals4 vals5 hv1 hv2 hv3 hv4 hv5 hD hb n hn s1 s2 s3 s4 s5
    hs1 hs2 hs3 hs4 hs5
  obtain ⟨out, hrun, -⟩ := run_spec s1 s2 s3 s4 s5 vals1 vals2 vals3 vals4 vals5
    hs1 hs2 hs3 hs4 hs5 hv1 hv2 hv3 hv4 hv5 hD hb
  exact rust_composite_of_equiv_ok
    (rust vals1 vals2 vals3 vals4 vals5 hv1 hv2 hv3 hv4 hv5 hD hb n hn
      s1 s2 s3 s4 s5 hs1 hs2 hs3 hs4 hs5) ⟨out, hrun⟩

end Cbtrn03c.Rust

namespace Cbtrn03c.Java

theorem java_composite :
    ∀ (vals1 vals2 vals3 vals4 vals5 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, TranRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, TranTypeRecord.Valid v) →
      (∀ v ∈ vals4, TranCatRecord.Valid v) →
      (∀ v ∈ vals5, WsDateparmRecord.Valid v) →
      EquivLean.Modernize.Cbtrn03c.Domain vals1 vals2 vals3 vals4 vals5 →
      vals1.length + vals2.length + vals3.length + vals4.length + vals5.length < 2 ^ 27 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length + vals5.length < n →
      ∀ (σ : Jimple.State) (a1 a2 a3 a4 a5 : Addr),
      TransactFileAt σ a1 vals1 →
      XrefFileAt σ a2 vals2 →
      TrantypeFileAt σ a3 vals3 →
      TrancatgFileAt σ a4 vals4 →
      DateParmsFileAt σ a5 vals5 →
      ClinitRan Gen.prog "Cbtrn03c" σ →
      σ.initOf "Cbtrn03c$Result" = .done →
      σ.initOf "Cbtrn03c$CardXrefRecord" = .done →
      σ.initOf "Cbtrn03c$TranCatRecord" = .done →
      σ.initOf "Cbtrn03c$TranRecord" = .done →
      σ.initOf "Cbtrn03c$TranTypeRecord" = .done →
      σ.initOf "Cbtrn03c$WsDateparmRecord" = .done →
      σ.initOf "Cbtrn03c$FdReptfileRec" = .done →
      σ.initOf "Cbtrn03c$Ws" = .done →
      let args := [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5]
      let c := EquivLean.Cobol.run CardDemo.Cbtrn03c {} (n + 60)
        (CardDemo.Cbtrn03c.initState initMem
          [(1, vals1.map TranRecord.encode), (2, vals2.map CardXrefRecord.encode),
           (3, vals3.map TranTypeRecord.encode), (4, vals4.map TranCatRecord.encode),
           (6, vals5.map (fun r => WsDateparmRecord.encode r ++ List.replicate 59 64))])
      Safe c ∧ MTerm Gen.prog runRef args σ ∧
        ((∃ o, MExec Gen.prog runRef args σ o) ∧
          ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o) ∧
        Sim Rel (Call.mk Gen.prog runRef args σ) c := by
  intro vals1 vals2 vals3 vals4 vals5 hv1 hv2 hv3 hv4 hv5 hD hjb n hn σ a1 a2 a3 a4 a5
    hin1 hin2 hin3 hin4 hin5 hcl hi2 hi3 hi4 hi5 hi6 hi7 hi8 hi9
  obtain ⟨hsig, -⟩ := Glue.cobol_outputs vals1 vals2 vals3 vals4 vals5 hv1 hv2 hv3 hv4 hv5 hD n (by omega)
  rw [← initMem_eq] at hsig
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbtrn03c {} (n + 60)
      (CardDemo.Cbtrn03c.initState initMem
        [(1, vals1.map TranRecord.encode), (2, vals2.map CardXrefRecord.encode),
         (3, vals3.map TranTypeRecord.encode), (4, vals4.map TranCatRecord.encode),
         (6, vals5.map (fun r => WsDateparmRecord.encode r ++ List.replicate 59 64))])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok]
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  have hin : RunIn [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5] σ vals1 vals2 vals3 vals4 vals5 :=
    ⟨a1, a2, a3, a4, a5, rfl, hin1, hin2, hin3, hin4, hin5, hv1, hv2, hv3, hv4, hv5⟩
  have hpre : runSpec.pre [.ref a1, .ref a2, .ref a3, .ref a4, .ref a5] σ :=
    ⟨vals1, vals2, vals3, vals4, vals5, hin, hcl.1, hi2, hi9, hi5, hi3, hi6, hi4, hi7, hi8⟩
  exact java_composite_of hsafe
    (java vals1 vals2 vals3 vals4 vals5 hv1 hv2 hv3 hv4 hv5 hD hjb n hn σ a1 a2 a3 a4 a5
      hin1 hin2 hin3 hin4 hin5 hcl hi2 hi3 hi4 hi5 hi6 hi7 hi8 hi9)
    (run_term _ σ hpre) (run_total _ σ hpre)

end Cbtrn03c.Java

/-! ## 9. CBSTM03B (subprogram, per-call) -/

namespace Cbstm03b.Rust

open CardDemo.Cbstm03b (Files opReadK ddCust ddAcct LK_M03B_KEY_LN st0)

theorem rust_composite :
    ∀ (env : Env) (m : Mem) (_ : m.size = 2248) (fs : Files) (k v : Int)
      (_ : ∀ r ∈ fs.trnx.recs, r.length = 350)
      (_ : ∀ r ∈ fs.xref.recs, r.length = 50)
      (_ : ∀ r ∈ fs.cust.recs, r.length = 500)
      (_ : ∀ r ∈ fs.acct.recs, r.length = 300)
      (_ : m.read 1216 1 = [opReadK] → (m.read 1208 8 = ddCust ∨ m.read 1208 8 = ddAcct) →
        decodeNum {} LK_M03B_KEY_LN.fmt (m.read 1244 4) = some k ∧ 1 ≤ k ∧ k ≤ 25)
      (_ : m.read 1216 1 = [opReadK] → m.read 1208 8 = ddAcct →
        decodeNum {} { digits := k.toNat } (m.read 1219 k.toNat) = some v)
      (_ : EquivLean.Modernize.Cbstm03b.Domain env m fs k v)
      (oe : Std.Array (Option Std.U8) 4#usize) (st : cbstm03b.State) (q1 : cbstm03b.LkM03bArea),
      EnvRel oe env → StateRel st (st0 m fs) → LkM03bAreaRel q1 (st0 m fs).mem →
      let c := EquivLean.Cobol.run CardDemo.Cbstm03b env 50 (st0 m fs)
      Safe c ∧ (∃ out, cbstm03b.call oe st q1 = .ok out) ∧
        Equiv Rel (cbstm03b.call oe st q1) c := by
  intro env m hm fs k v h1 h2 h3 h4 hK hA hD oe st q1 hE hS hR
  obtain ⟨st', q', hcall, -⟩ := call_spec oe st q1 (callHyp_of hK hD hE hS hR)
  exact rust_composite_of_equiv_ok
    (rust env m hm fs k v h1 h2 h3 h4 hK hA hD oe st q1 hE hS hR) ⟨(st', q'), hcall⟩

end Cbstm03b.Rust

namespace Cbstm03b.Java

open CardDemo.Cbstm03b (Files opReadK ddCust ddAcct LK_M03B_KEY_LN st0)

theorem java_composite :
    ∀ (env : Env) (m : Mem) (_ : m.size = 2248) (fs : Files) (k v : Int)
      (_ : ∀ r ∈ fs.trnx.recs, r.length = 350)
      (_ : ∀ r ∈ fs.xref.recs, r.length = 50)
      (_ : ∀ r ∈ fs.cust.recs, r.length = 500)
      (_ : ∀ r ∈ fs.acct.recs, r.length = 300)
      (_ : m.read 1216 1 = [opReadK] → (m.read 1208 8 = ddCust ∨ m.read 1208 8 = ddAcct) →
        decodeNum {} LK_M03B_KEY_LN.fmt (m.read 1244 4) = some k ∧ 1 ≤ k ∧ k ≤ 25)
      (_ : m.read 1216 1 = [opReadK] → m.read 1208 8 = ddAcct →
        decodeNum {} { digits := k.toNat } (m.read 1219 k.toNat) = some v)
      (_ : EquivLean.Modernize.Cbstm03b.Domain env m fs k v)
      (σ : Jimple.State) (oe st q1 : Addr),
      EnvAt σ oe env → StateAt σ st (st0 m fs) → LkM03bAreaAt σ q1 (st0 m fs).mem →
      σ.initOf "Cbstm03b" = .done →
      σ.initOf "Cbstm03b$State" = .done →
      σ.initOf "Cbstm03b$TrnxFile" = .done →
      σ.initOf "Cbstm03b$XrefFile" = .done →
      σ.initOf "Cbstm03b$CustFile" = .done →
      σ.initOf "Cbstm03b$AcctFile" = .done →
      σ.initOf "Cbstm03b$FdAcctfileRec" = .done →
      σ.initOf "Cbstm03b$FdCustfileRec" = .done →
      σ.initOf "Cbstm03b$FdTrnxfileRec" = .done →
      σ.initOf "Cbstm03b$FdXreffileRec" = .done →
      σ.initOf "Cbstm03b$LkM03bArea" = .done →
      let args := [.ref oe, .ref st, .ref q1]
      let c := EquivLean.Cobol.run CardDemo.Cbstm03b env 50 (st0 m fs)
      Safe c ∧ MTerm Gen.prog callRef args σ ∧
        ((∃ o, MExec Gen.prog callRef args σ o) ∧
          ∀ o, MExec Gen.prog callRef args σ o → runSpec.post args σ o) ∧
        Sim (Rel st q1) (Call.mk Gen.prog callRef args σ) c := by
  intro env m hm fs k v h1 h2 h3 h4 hK hA hD σ oe st q1 hE hS hR
    i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11
  obtain ⟨s, hsm, hsr⟩ := stateAt_to_model hS
  have hsep := stateAt_sep hS
  have ⟨a, haj, hav, haa⟩ := hR
  have hR' : Glue.LkM03bAreaRel a m := ⟨hav, haa⟩
  have hE' : Glue.EnvRel (fun id => env.openError id .input) env := fun _ _ => rfl
  have hval := Glue.validSt_of_stateRel hsr
  have hkey := Glue.keyOk_of hR' hK hA hD
  have hinit : InitsDone σ := ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11⟩
  obtain ⟨hgo, -⟩ := Glue.call_run env m hm fs k v hK hA _ s a hE' hsr hR'
  have hsafe : Safe (EquivLean.Cobol.run CardDemo.Cbstm03b env 50 (st0 m fs)) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok, hgo]; rfl
  have hpre : runSpec.pre [.ref oe, .ref st, .ref q1] σ :=
    ⟨oe, st, q1, fun id => env.openError id .input, s, a, rfl, envAt_model hE, hsm, hsep, haj,
      hval, hav, hkey, hinit⟩
  exact java_composite_of hsafe
    (java env m hm fs k v h1 h2 h3 h4 hK hA hD σ oe st q1 hE hS hR
      i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11)
    (java_terminates _ σ hpre) (java_total _ σ hpre)

end Cbstm03b.Java

/-! ## 10. CBSTM03A (full batch statement generator, inlining CBSTM03B) -/

namespace Cbstm03a.Rust

theorem rust_composite :
    ∀ (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, TrnxRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, CustomerRecord.Valid v) →
      (∀ v ∈ vals4, AccountRecord.Valid v) →
      EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4 →
      vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 28 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length < n →
      ∀ (s1 : Slice cbstm03a.TrnxRecord) (s2 : Slice cbstm03a.CardXrefRecord)
        (s3 : Slice cbstm03a.CustomerRecord) (s4 : Slice cbstm03a.AccountRecord),
      TrnxFileOf s1 vals1 →
      XrefFileOf s2 vals2 →
      CustFileOf s3 vals3 →
      AcctFileOf s4 vals4 →
      let c := EquivLean.Cobol.run Cobol.Stm.Stm { addrSpace := Cobol.Stm.asp } (n + 100)
        (Cobol.Stm.Stm.initState initMem
          [(3, vals1.map TrnxRecord.encode), (4, vals2.map CardXrefRecord.encode),
           (5, vals3.map CustomerRecord.encode), (6, vals4.map AccountRecord.encode)])
      Safe c ∧ (∃ out, cbstm03a.run s1 s2 s3 s4 = .ok out) ∧
        Equiv Rel (cbstm03a.run s1 s2 s3 s4) c := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 hD hb n hn s1 s2 s3 s4 hs1 hs2 hs3 hs4
  obtain ⟨out, hrun, -⟩ := run_spec s1 s2 s3 s4 vals1 vals2 vals3 vals4
    hs1 hs2 hs3 hs4 hv1 hv2 hv3 hv4 hD hb
  exact rust_composite_of_equiv_ok
    (rust vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 hD hb n hn s1 s2 s3 s4 hs1 hs2 hs3 hs4)
    ⟨out, hrun⟩

end Cbstm03a.Rust

namespace Cbstm03a.Java

theorem java_composite :
    ∀ (vals1 vals2 vals3 vals4 : List (List EquivLean.Cobol.Rec.FVal)),
      (∀ v ∈ vals1, TrnxRecord.Valid v) →
      (∀ v ∈ vals2, CardXrefRecord.Valid v) →
      (∀ v ∈ vals3, CustomerRecord.Valid v) →
      (∀ v ∈ vals4, AccountRecord.Valid v) →
      EquivLean.Modernize.Cbstm03a.Domain vals1 vals2 vals3 vals4 →
      vals1.length + vals2.length + vals3.length + vals4.length < 2 ^ 27 →
      ∀ n : Nat, vals1.length + vals2.length + vals3.length + vals4.length < n →
      ∀ (σ : Jimple.State) (a1 a2 a3 a4 : Addr),
      TrnxFileAt σ a1 vals1 →
      XrefFileAt σ a2 vals2 →
      CustFileAt σ a3 vals3 →
      AcctFileAt σ a4 vals4 →
      ClinitRan Gen.prog "Cbstm03a" σ →
      σ.initOf "Cbstm03a$Result" = .done →
      σ.initOf "Cbstm03a$AccountRecord" = .done →
      σ.initOf "Cbstm03a$CardXrefRecord" = .done →
      σ.initOf "Cbstm03a$CustomerRecord" = .done →
      σ.initOf "Cbstm03a$TrnxRecord" = .done →
      let args := [.ref a1, .ref a2, .ref a3, .ref a4]
      let c := EquivLean.Cobol.run Cobol.Stm.Stm { addrSpace := Cobol.Stm.asp } (n + 100)
        (Cobol.Stm.Stm.initState initMem
          [(3, vals1.map TrnxRecord.encode), (4, vals2.map CardXrefRecord.encode),
           (5, vals3.map CustomerRecord.encode), (6, vals4.map AccountRecord.encode)])
      Safe c ∧ MTerm Gen.prog runRef args σ ∧
        ((∃ o, MExec Gen.prog runRef args σ o) ∧
          ∀ o, MExec Gen.prog runRef args σ o → runSpec.post args σ o) ∧
        Sim Rel (Call.mk Gen.prog runRef args σ) c := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 hD hjb n hn σ a1 a2 a3 a4
    hin1 hin2 hin3 hin4 hi1 hi2 hi3 hi4 hi5 hi6
  obtain ⟨hsig, -⟩ := Glue.cobol_outputs vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 hD n (by omega)
  rw [← initMem_eq] at hsig
  have hsafe : Safe (EquivLean.Cobol.run Cobol.Stm.Stm { addrSpace := Cobol.Stm.asp } (n + 100)
      (Cobol.Stm.Stm.initState initMem
        [(3, vals1.map TrnxRecord.encode), (4, vals2.map CardXrefRecord.encode),
         (5, vals3.map CustomerRecord.encode), (6, vals4.map AccountRecord.encode)])) := by
    rw [EquivLean.Cobol.run, EquivLean.Cobol.safe_exec_iff, EquivLean.Cobol.Ok]
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  have hin : RunIn [.ref a1, .ref a2, .ref a3, .ref a4] σ vals1 vals2 vals3 vals4 :=
    ⟨a1, a2, a3, a4, rfl, hin1, hin2, hin3, hin4, hv1, hv2, hv3, hv4, hD, hjb⟩
  have hpre : runSpec.pre [.ref a1, .ref a2, .ref a3, .ref a4] σ :=
    ⟨vals1, vals2, vals3, vals4, hin, hi1, hi2, hi3, hi4, hi5, hi6⟩
  exact java_composite_of hsafe
    (java vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 hD hjb n hn σ a1 a2 a3 a4
      hin1 hin2 hin3 hin4 hi1 hi2 hi3 hi4 hi5 hi6)
    (java_terminates _ σ hpre) (java_total _ σ hpre)

end Cbstm03a.Java

end EquivLean.Modernize

#print axioms EquivLean.Modernize.Cbact01c.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbact01c.Java.java_composite
#print axioms EquivLean.Modernize.Cbact02c.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbact02c.Java.java_composite
#print axioms EquivLean.Modernize.Cbact03c.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbact03c.Java.java_composite
#print axioms EquivLean.Modernize.Cbact04c.Every.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbact04c.Every.Java.java_composite
#print axioms EquivLean.Modernize.Cbact04c.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbcus01c.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbcus01c.Java.java_composite
#print axioms EquivLean.Modernize.Cbtrn01c.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbtrn01c.Java.java_composite
#print axioms EquivLean.Modernize.Cbtrn02c.Any.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbtrn02c.Any.Java.java_composite
#print axioms EquivLean.Modernize.Cbtrn02c.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbtrn03c.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbtrn03c.Java.java_composite
#print axioms EquivLean.Modernize.Cbstm03b.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbstm03b.Java.java_composite
#print axioms EquivLean.Modernize.Cbstm03a.Rust.rust_composite
#print axioms EquivLean.Modernize.Cbstm03a.Java.java_composite

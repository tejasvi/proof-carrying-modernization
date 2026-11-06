import EquivLean.Modernize.Cbtrn02c.Any.JavaSpec
import EquivLean.Modernize.Cbtrn02c.Any.Glue
import EquivLean.Modernize.Cbtrn02c.JavaProof

/-!
# CBTRN02C → Java on any input: from the contract of `run` to the generated statement

* the COBOL side: `Glue.cobol_outputs` (coblean's `cbtrn02c_any`: GOBACK, or abend 999 at a
  repeated transaction id; the displays, the records written to TRANSACT, DALYREJS and TCATBAL and
  rewritten in ACCOUNT and TCATBAL, RETURN-CODE and the abend are `Model.runX`'s);
* the Java side: the contract `runSpec` of `Cbtrn02c.run` (`JavaSpec.lean`: the `Result` holds
  `Model.runX`'s outputs, `abended` is 1 exactly when the model abends);
* the glue: a line of code points is the CP037 text of coblean's bytes (`jline`), a record object
  holds the field values coblean's record decodes to (the restricted proof's lemmas).

`statement_of_sat`: the contract implies the generated `Statement`.
-/

open Cobol EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbtrn02c.Java (jline cp037Str_eq_map forall2_of_map forall2_decode)

namespace EquivLean.Modernize.Cbtrn02c.Any.Java

theorem initMem_eq : initMem = Cbtrn02c.Glue.initMem := rfl

set_option maxRecDepth 20000 in
/-- **The contract of `run` implies the generated statement.** -/
theorem statement_of_sat (hrun : Sat Cbtrn02c.Java.Gen.prog runRef runSpec) : Statement := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 clk hc hD hjb n hn σ a1 a2 a3 a4 cs hin1 hin2 hin3
    hin4 hclk hcl hi2 hi3 hi4 hi5 hi6 hi7 hi8
  obtain ⟨hsig, hdisp, htran, hrej, hcatw, hacct, hcatrw, hrc, habC⟩ :=
    Glue.cobol_outputs vals1 vals2 vals3 vals4 clk hv1 hv2 hv3 hv4 hc hD n (by omega)
  rw [← initMem_eq] at hsig hdisp htran hrej hcatw hacct hcatrw hrc habC
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbtrn02c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbtrn02c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (3, vals2.map CardXrefRecord.encode), (5, vals3.map AccountRecord.encode),
        (6, vals4.map TranCatBalRecord.encode)])) := by
    unfold EquivLean.Cobol.Ok
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  have hin : RunIn [.ref a1, .ref a2, .ref a3, .ref a4, .ref cs] σ vals1 vals2 vals3 vals4 clk :=
    ⟨a1, a2, a3, a4, cs, rfl, hin1, hin2, hin3, hin4, hclk, hc, hv1, hv2, hv3, hv4, hD, hjb⟩
  rw [EquivLean.Cobol.run]
  refine sim_of_sat ((EquivLean.Cobol.safe_exec_iff _).2 hok)
    ((EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩) hrun
    ⟨vals1, vals2, vals3, vals4, clk, hin, hcl.1, hi2, hi3, hi4, hi5, hi6, hi7, hi8⟩ ?_
  intro o ho
  cases o with
  | normal r σ' =>
    obtain ⟨res, fs, l, k, xs, mods, hr, hres, hl', hlist, hpairs,
      ⟨l1, k1, w1, m1, h1a, h1b, h1c⟩, ⟨l2, k2, w2, m2, h2a, h2b, h2c⟩,
      ⟨l3, k3, w3, m3, h3a, h3b, h3c⟩, ⟨l4, k4, w4, m4, h4a, h4b, h4c⟩,
      ⟨l5, k5, w5, m5, h5a, h5b, h5c⟩, hrcj, hab⟩ := ho vals1 vals2 vals3 vals4 clk hin
    refine ⟨σ', res, fs, l, k, xs, mods, by rw [hr], hres, hl', hlist, ?_,
      ⟨l1, k1, w1, m1, h1a, h1b, forall2_decode h1c htran⟩,
      ⟨l2, k2, w2, m2, h2a, h2b, forall2_decode h2c hrej⟩,
      ⟨l3, k3, w3, m3, h3a, h3b, forall2_decode h3c hcatw⟩,
      ⟨l4, k4, w4, m4, h4a, h4b, forall2_decode h4c hacct⟩,
      ⟨l5, k5, w5, m5, h5a, h5b, forall2_decode h5c hcatrw⟩, ?_, ?_⟩
    · rw [← hdisp, List.map_map] at hpairs
      have e : (jline ∘ fun l => l.map cp037Code) = cp037Str := by
        funext bs; simp only [Function.comp_apply, jline, cp037Str_eq_map]
      rw [e] at hpairs
      exact forall2_of_map (R := JStrAt σ') (f := cp037Str) hpairs
    · rw [hrc]
      exact hrcj
    · rw [habC]
      exact hab
  | exc e σ' => simp [runSpec, Spec.of] at ho
  | wrong msg => simp [runSpec, Spec.of] at ho

end EquivLean.Modernize.Cbtrn02c.Any.Java

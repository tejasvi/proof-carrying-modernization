import EquivLean.Modernize.Cbtrn02c.RustSpec
import EquivLean.Modernize.Cbtrn02c.Glue

/-!
# CBTRN02C → Rust: from the equation of `run` to the generated statement

* the COBOL side: `Glue.cobol_outputs` (GOBACK; the displays, the records written to TRANSACT,
  DALYREJS and TCATBAL and rewritten in ACCOUNT and TCATBAL, and RETURN-CODE are `Model.run`'s);
* the Rust side: `RunSpec` (`RustSpec.lean`: `cbtrn02c.run` returns `Model.run`'s outputs, never
  panics, `abended` is false);
* the glue: Latin-1 bytes are the code points of the CP037 text (`rustLine`).

`statement_of_run`: the equation implies the generated `Statement` (an `Equiv`: Aeneas
computations are total and deterministic).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbtrn02c.Rust

theorem initMem_eq : initMem = Glue.initMem := rfl

set_option maxRecDepth 20000 in
/-- **The equation of `run` implies the generated statement.** -/
theorem statement_of_run (h : RunSpec) : Statement := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 clk hc hD hb n hn s1 s2 s3 s4 rclk hs1 hs2 hs3 hs4
    hr
  obtain ⟨out, hrun, hdisp, htran, hrej, hacct, hcatw, hcatrw, hrc, hab⟩ :=
    h s1 s2 s3 s4 rclk vals1 vals2 vals3 vals4 clk hs1 hs2 hs3 hs4 hr hc hv1 hv2 hv3 hv4 hD hb
  obtain ⟨hstop, hdispC, htranC, hrejC, hcatwC, hacctC, hcatrwC, hrcC⟩ :=
    Glue.cobol_outputs vals1 vals2 vals3 vals4 clk hv1 hv2 hv3 hv4 hc hD n (by omega)
  rw [← initMem_eq] at hstop hdispC htranC hrejC hcatwC hacctC hcatrwC hrcC
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbtrn02c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbtrn02c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (3, vals2.map CardXrefRecord.encode), (5, vals3.map AccountRecord.encode),
        (6, vals4.map TranCatBalRecord.encode)])) := by
    unfold EquivLean.Cobol.Ok; rw [hstop]; rfl
  have hrel : Rel (.ok out) (CardDemo.Cbtrn02c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbtrn02c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (3, vals2.map CardXrefRecord.encode), (5, vals3.map AccountRecord.encode),
        (6, vals4.map TranCatBalRecord.encode)])) := by
    refine ⟨out, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdisp, ← hdispC]
      rfl
    · rw [htranC, ← htran, List.map_map]
      rfl
    · rw [hrejC, ← hrej, List.map_map]
      rfl
    · rw [hcatwC, ← hcatw, List.map_map]
      rfl
    · rw [hacctC, ← hacct, List.map_map]
      rfl
    · rw [hcatrwC, ← hcatrw, List.map_map]
      rfl
    · rw [hrc, hrcC]
    · rw [hab, hstop]
      rfl
  rw [hrun, EquivLean.Cobol.run]
  refine ⟨fun _ => ⟨EquivLean.Aeneas.safe_ok _, fun or hor =>
      ⟨CardDemo.Cbtrn02c.run { clock := fun _ => clk } (n + 60)
        (CardDemo.Cbtrn02c.initState initMem [(1, vals1.map DalytranRecord.encode),
          (3, vals2.map CardXrefRecord.encode), (5, vals3.map AccountRecord.encode),
          (6, vals4.map TranCatBalRecord.encode)]), ?_, ?_⟩⟩,
    fun _ => ⟨(EquivLean.Cobol.safe_exec_iff _).2 hok, fun os hos => ⟨.ok out, ?_, ?_⟩⟩⟩
  · exact (EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩
  · rw [(EquivLean.Aeneas.runs_ok_iff _ _).1 hor]
    exact hrel
  · exact (EquivLean.Aeneas.runs_ok_iff _ _).2 rfl
  · obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
    rw [h1]
    exact hrel

end EquivLean.Modernize.Cbtrn02c.Rust

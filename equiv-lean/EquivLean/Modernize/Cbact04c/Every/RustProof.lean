import EquivLean.Modernize.Cbact04c.Every.RustSpec
import EquivLean.Modernize.Cbact04c.Every.Glue

/-!
# CBACT04C → Rust on every input: from the equation of `run` to the generated statement

* the COBOL side: `Glue.cobol_outputs` (coblean's `cbact04c_every`: GOBACK or abend 999; the
  displays, written transactions, rewritten accounts and abend flag are `Model.runE`'s);
* the Rust side: `RunSpec` (`RustSpec.lean`: `cbact04c_t.run` returns `Model.runE`'s outputs,
  never panics);
* the glue: Latin-1 bytes are the code points of the CP037 text (`rustLine`).

`statement_of_run`: the equation implies the generated `Statement` (an `Equiv`: Aeneas
computations are total and deterministic).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbact04c.Every.Rust

theorem initMem_eq : initMem = Cbact04c.Glue.initMem := rfl

set_option maxRecDepth 20000 in
/-- **The equation of `run` implies the generated statement.** -/
theorem statement_of_run (h : RunSpec) : Statement := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 link1 hl clk hc hD hb n hn s1 s2 s3 s4 q1 rclk
    hs1 hs2 hs3 hs4 hq hr
  obtain ⟨out, hrun, hdisp, hwr, hrw, hab⟩ :=
    h s1 s2 s3 s4 q1 rclk vals1 vals2 vals3 vals4 link1 clk hs1 hs2 hs3 hs4 hq hr hc.1
      hv1 hv2 hv3 hv4 hl hD hb
  obtain ⟨hsig, hdispC, hwrC, hrwC, habC⟩ := Glue.cobol_outputs vals1 vals2 vals3 vals4 link1 clk
    hv1 hv2 hv3 hv4 hl hc hD n (by omega)
  rw [← initMem_eq] at hsig hdispC hwrC hrwC habC
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbact04c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
        [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
          (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])) := by
    unfold EquivLean.Cobol.Ok
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  have hrel : Rel (.ok out) (CardDemo.Cbact04c.run { clock := fun _ => clk } (n + 60)
      (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
        [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
          (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)])) := by
    refine ⟨out, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hdisp, ← hdispC]
      rfl
    · rw [hwrC, ← hwr, List.map_map]
      rfl
    · rw [hrwC, ← hrw, List.map_map]
      rfl
    · rw [hab, habC]
  rw [hrun, EquivLean.Cobol.run]
  refine ⟨fun _ => ⟨EquivLean.Aeneas.safe_ok _, fun or hor =>
      ⟨CardDemo.Cbact04c.run { clock := fun _ => clk } (n + 60)
        (CardDemo.Cbact04c.initState (Cobol.Mem.write initMem 1727 (ExternalParms.encode link1))
          [(1, vals1.map TranCatBalRecord.encode), (2, vals2.map CardXrefRecord.encode),
            (3, vals3.map AccountRecord.encode), (4, vals4.map DisGroupRecord.encode)]), ?_, ?_⟩⟩,
    fun _ => ⟨(EquivLean.Cobol.safe_exec_iff _).2 hok, fun os hos => ⟨.ok out, ?_, ?_⟩⟩⟩
  · exact (EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩
  · rw [(EquivLean.Aeneas.runs_ok_iff _ _).1 hor]
    exact hrel
  · exact (EquivLean.Aeneas.runs_ok_iff _ _).2 rfl
  · obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
    rw [h1]
    exact hrel

end EquivLean.Modernize.Cbact04c.Every.Rust

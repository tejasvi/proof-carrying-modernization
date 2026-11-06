import EquivLean.Modernize.Cbtrn03c.RustSpec
import EquivLean.Modernize.Cbtrn03c.Glue

/-!
# CBTRN03C → Rust: from the equation of `run` to the generated statement

* the COBOL side: `Glue.cobol_outputs` (coblean's `cbtrn03c_every` for the inputs built from the
  field values: GOBACK or the abend 999 as `Model.run`'s `abended` says; the displays and the
  report lines written are `Model.run`'s);
* the Rust side: `RunSpec` (`RustSpec.lean`: `cbtrn03c.run` returns `Model.run`'s outputs, never
  panics);
* the glue: Latin-1 bytes are the code points of the CP037 text (`rustLine`).

`statement_of_run`: the equation implies the generated `Statement` (an `Equiv`: Aeneas
computations are total and deterministic).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbtrn03c.Rust

theorem initMem_eq : initMem = Glue.initMem := rfl

set_option maxRecDepth 20000 in
/-- **The equation of `run` implies the generated statement.** -/
theorem statement_of_run (h : RunSpec) : Statement := by
  intro vals1 vals2 vals3 vals4 vals5 hv1 hv2 hv3 hv4 hv5 hD hb n hn s1 s2 s3 s4 s5 hs1 hs2 hs3
    hs4 hs5
  obtain ⟨out, hrun, hdisp, hwr, hab⟩ :=
    h s1 s2 s3 s4 s5 vals1 vals2 vals3 vals4 vals5 hs1 hs2 hs3 hs4 hs5 hv1 hv2 hv3 hv4 hv5 hD hb
  obtain ⟨hsig, hdispC, hwrC, habC⟩ :=
    Glue.cobol_outputs vals1 vals2 vals3 vals4 vals5 hv1 hv2 hv3 hv4 hv5 hD n (by omega)
  rw [← initMem_eq] at hsig hdispC hwrC habC
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbtrn03c.run {} (n + 60)
      (CardDemo.Cbtrn03c.initState initMem [(1, vals1.map TranRecord.encode),
        (2, vals2.map CardXrefRecord.encode), (3, vals3.map TranTypeRecord.encode),
        (4, vals4.map TranCatRecord.encode),
        (6, vals5.map (fun r => WsDateparmRecord.encode r ++ List.replicate 59 64))])) := by
    unfold EquivLean.Cobol.Ok
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  have hrel : Rel (.ok out) (CardDemo.Cbtrn03c.run {} (n + 60)
      (CardDemo.Cbtrn03c.initState initMem [(1, vals1.map TranRecord.encode),
        (2, vals2.map CardXrefRecord.encode), (3, vals3.map TranTypeRecord.encode),
        (4, vals4.map TranCatRecord.encode),
        (6, vals5.map (fun r => WsDateparmRecord.encode r ++ List.replicate 59 64))])) := by
    refine ⟨out, rfl, ?_, ?_, ?_⟩
    · rw [hdisp, ← hdispC]
      rfl
    · rw [hwrC, ← hwr, List.map_map]
      rfl
    · rw [hab, habC]
  rw [hrun, EquivLean.Cobol.run]
  refine ⟨fun _ => ⟨EquivLean.Aeneas.safe_ok _, fun or hor =>
      ⟨CardDemo.Cbtrn03c.run {} (n + 60)
        (CardDemo.Cbtrn03c.initState initMem [(1, vals1.map TranRecord.encode),
          (2, vals2.map CardXrefRecord.encode), (3, vals3.map TranTypeRecord.encode),
          (4, vals4.map TranCatRecord.encode),
          (6, vals5.map (fun r => WsDateparmRecord.encode r ++ List.replicate 59 64))]), ?_, ?_⟩⟩,
    fun _ => ⟨(EquivLean.Cobol.safe_exec_iff _).2 hok, fun os hos => ⟨.ok out, ?_, ?_⟩⟩⟩
  · exact (EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩
  · rw [(EquivLean.Aeneas.runs_ok_iff _ _).1 hor]
    exact hrel
  · exact (EquivLean.Aeneas.runs_ok_iff _ _).2 rfl
  · obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
    rw [h1]
    exact hrel

end EquivLean.Modernize.Cbtrn03c.Rust

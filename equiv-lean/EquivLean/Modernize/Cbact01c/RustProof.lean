import EquivLean.Modernize.Cbact01c.RustSpec
import EquivLean.Modernize.Cbact01c.Glue

/-!
# CBACT01C → Rust: from the equation of `run` to the generated statement

* the COBOL side: `Glue.cobol_outputs` (coblean's `cbact01c_extracts` for the account records
  built from the field values: GOBACK; the displays and the records written to OUT-FILE,
  ARRY-FILE and VBRC-FILE are `Model.run`'s);
* the Rust side: `RunSpec` (`RustSpec.lean`: `cbact01c.run` returns `Model.run`'s outputs, never
  panics, `abended` is false);
* the glue: Latin-1 bytes are the code points of the CP037 text (`rustLine`).

`statement_of_run`: the equation implies the generated `Statement` (an `Equiv`: Aeneas
computations are total and deterministic).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbact01c.Rust

theorem initMem_eq : initMem = Glue.initMem := rfl

set_option maxRecDepth 20000 in
/-- **The equation of `run` implies the generated statement.** -/
theorem statement_of_run (h : RunSpec) : Statement := by
  intro vals1 hv1 hb n hn s1 hs1
  obtain ⟨out, hrun, hdisp, hout, harr, hvb, hab⟩ := h s1 vals1 hs1 hv1 hb
  obtain ⟨hstop, hdispC, houtC, harrC, hvbC⟩ := Glue.cobol_outputs vals1 hv1 n hn
  rw [← initMem_eq] at hstop hdispC houtC harrC hvbC
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbact01c.run
      { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
      (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)])) := by
    unfold EquivLean.Cobol.Ok
    rw [hstop]
    rfl
  have hrel : Rel (.ok out) (CardDemo.Cbact01c.run
      { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
      (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)])) := by
    refine ⟨out, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdisp, ← hdispC]
      rfl
    · rw [houtC, ← hout, List.map_map]
      rfl
    · rw [harrC, ← harr, List.map_map]
      rfl
    · rw [hvb, ← hvbC]
      rfl
    · rw [hab, hstop]
      rfl
  rw [hrun, EquivLean.Cobol.run]
  refine ⟨fun _ => ⟨EquivLean.Aeneas.safe_ok _, fun or hor =>
      ⟨CardDemo.Cbact01c.run { call := Cobol.Ext.cardDemoCalls CardDemo.Cbact01c.cfg } (n + 40)
        (CardDemo.Cbact01c.initState initMem [(1, vals1.map AccountRecord.encode)]), ?_, ?_⟩⟩,
    fun _ => ⟨(EquivLean.Cobol.safe_exec_iff _).2 hok, fun os hos => ⟨.ok out, ?_, ?_⟩⟩⟩
  · exact (EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩
  · rw [(EquivLean.Aeneas.runs_ok_iff _ _).1 hor]
    exact hrel
  · exact (EquivLean.Aeneas.runs_ok_iff _ _).2 rfl
  · obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
    rw [h1]
    exact hrel

end EquivLean.Modernize.Cbact01c.Rust

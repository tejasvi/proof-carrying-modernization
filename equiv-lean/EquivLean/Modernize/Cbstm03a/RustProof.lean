import EquivLean.Modernize.Cbstm03a.RustSpec
import EquivLean.Modernize.Cbstm03a.Glue

/-!
# CBSTM03A → Rust: from the equation of `run` to the generated statement

* the COBOL side: `Glue.cobol_outputs` (`stm_run_sorted`, `stm_run_abort_cust`,
  `stm_run_abort_acct`: GOBACK or abend; the displays after dropping the 11 walk lines, the
  `STMT-FILE` and `HTML-FILE` writes, and `abended` match `Model.run`);
* the Rust side: `RunSpec` (`RustSpec.lean`: `cbstm03a.run` returns `Model.run`'s outputs, never
  panics);
* the glue: Latin-1 bytes are the code points of the CP037 text (`rustLine`).

`statement_of_run`: the equation implies the generated `Statement` (an `Equiv`: Aeneas computations
are total and deterministic).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbstm03a.Rust

theorem initMemRuns_eq : initMemRuns = Glue.initMemRuns := rfl

theorem initMem_eq : initMem = Glue.initMem := by
  unfold initMem Glue.initMem
  rw [initMemRuns_eq]

set_option maxRecDepth 20000 in
/-- **The equation of `run` implies the generated statement.** -/
theorem statement_of_run (h : RunSpec) : Statement := by
  intro vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 hD hb n hn s1 s2 s3 s4 hs1 hs2 hs3 hs4
  obtain ⟨out, hrun, hdisp, hstmt, hhtml, hab⟩ :=
    h s1 s2 s3 s4 vals1 vals2 vals3 vals4 hs1 hs2 hs3 hs4 hv1 hv2 hv3 hv4 hD hb
  obtain ⟨hsig, hdispC, hstmtC, hhtmlC, habC⟩ :=
    Glue.cobol_outputs vals1 vals2 vals3 vals4 hv1 hv2 hv3 hv4 hD n (by omega)
  rw [← initMem_eq] at hsig hdispC hstmtC hhtmlC habC
  have hok : EquivLean.Cobol.Ok (Cobol.Stm.Stm.run { addrSpace := Cobol.Stm.asp } (n + 100)
      (Cobol.Stm.Stm.initState initMem
        [(3, vals1.map TrnxRecord.encode), (4, vals2.map CardXrefRecord.encode),
          (5, vals3.map CustomerRecord.encode), (6, vals4.map AccountRecord.encode)])) := by
    unfold EquivLean.Cobol.Ok
    rcases hsig with hs | hs <;> rw [hs] <;> rfl
  have hrel : Rel (.ok out) (Cobol.Stm.Stm.run { addrSpace := Cobol.Stm.asp } (n + 100)
      (Cobol.Stm.Stm.initState initMem
        [(3, vals1.map TrnxRecord.encode), (4, vals2.map CardXrefRecord.encode),
          (5, vals3.map CustomerRecord.encode), (6, vals4.map AccountRecord.encode)])) := by
    refine ⟨out, rfl, ?_, ?_, ?_, ?_⟩
    · rw [hdisp, ← hdispC]; rfl
    · rw [hstmt, ← hstmtC]; rfl
    · rw [hhtml, ← hhtmlC]; rfl
    · rw [hab, habC]
  rw [hrun, EquivLean.Cobol.run]
  refine ⟨fun _ => ⟨EquivLean.Aeneas.safe_ok _, fun or hor =>
      ⟨Cobol.Stm.Stm.run { addrSpace := Cobol.Stm.asp } (n + 100)
        (Cobol.Stm.Stm.initState initMem
          [(3, vals1.map TrnxRecord.encode), (4, vals2.map CardXrefRecord.encode),
            (5, vals3.map CustomerRecord.encode), (6, vals4.map AccountRecord.encode)]), ?_, ?_⟩⟩,
    fun _ => ⟨(EquivLean.Cobol.safe_exec_iff _).2 hok, fun os hos => ⟨.ok out, ?_, ?_⟩⟩⟩
  · exact (EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩
  · rw [(EquivLean.Aeneas.runs_ok_iff _ _).1 hor]
    exact hrel
  · exact (EquivLean.Aeneas.runs_ok_iff _ _).2 rfl
  · rw [((EquivLean.Cobol.runs_exec_iff _ _).1 hos).1]
    exact hrel

end EquivLean.Modernize.Cbstm03a.Rust

import EquivLean.Modernize.Cbtrn01c.RustStatement
import EquivLean.Modernize.Cbtrn01c.Model

/-!
# CBTRN01C → Rust: from the equation of `run` to the generated statement

* the COBOL side: coblean's `cbtrn01c_verifies_all`, for the records built from the field values;
* the Rust side: `RunSpec`, the equation of `cbtrn01c.run` (it never panics; the `displays` lines
  are those of `Model.displayText`; `abended` is false);
* the glue: `Model.displayText_eq` (the lines are the CP037 texts of coblean's).

`statement_of_run`: the equation implies the generated `Statement` (an `Equiv`: Aeneas
computations are total and deterministic).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbtrn01c.Rust

/-- The equation of `run`. -/
def RunSpec : Prop :=
  ∀ (s1 : Slice cbtrn01c.DalytranRecord) (s2 : Slice cbtrn01c.FdCustfileRec)
    (s3 : Slice cbtrn01c.CardXrefRecord) (s4 : Slice cbtrn01c.FdCardfileRec)
    (s5 : Slice cbtrn01c.AccountRecord) (s6 : Slice cbtrn01c.FdTranfileRec)
    (vals1 vals3 vals5 : List (List EquivLean.Cobol.Rec.FVal)),
    s1.val.map DalytranRecord.vals = vals1 → s3.val.map CardXrefRecord.vals = vals3 →
    s5.val.map AccountRecord.vals = vals5 →
    (∀ v ∈ vals1, DalytranRecord.Valid v) → (∀ v ∈ vals3, CardXrefRecord.Valid v) →
    (∀ v ∈ vals5, AccountRecord.Valid v) →
    vals1.length < 2 ^ 28 → vals3.length < 2 ^ 28 → vals5.length < 2 ^ 28 →
    ∃ out, cbtrn01c.run s1 s2 s3 s4 s5 s6 = .ok out ∧
      out.displays.val.map (fun l => l.val.map (·.val)) = Model.displayText vals1 vals3 vals5 ∧
      out.abended = false

theorem dalytranRecord_eq : DalytranRecord = Model.DalytranRecord := rfl
theorem cardXrefRecord_eq : CardXrefRecord = Model.CardXrefRecord := rfl
theorem accountRecord_eq : AccountRecord = Model.AccountRecord := rfl
theorem initMem_eq : initMem = Model.initMem := rfl

theorem displays_eq : CardDemo.Cbtrn01c.displays = EquivLean.Cobol.Rec.displays := rfl

theorem rustLine_eq_map (bs : List UInt8) : rustLine bs = bs.map cp037Code := rfl

/-- **The equation of `run` implies the generated statement.** -/
theorem statement_of_run (h : RunSpec) : Statement := by
  intro vals1 vals2 vals3 vals4 vals5 vals6 hv1 hv2 hv3 hv4 hv5 hv6 hb n hn s1 s2 s3 s4 s5 s6
    hs1 hs2 hs3 hs4 hs5 hs6
  obtain ⟨out, hrun, hdisp, hab⟩ := h s1 s2 s3 s4 s5 s6 vals1 vals3 vals5 hs1 hs3 hs5 hv1 hv3 hv5
    (by omega) (by omega) (by omega)
  have hm : initMem.size = 3441 := by rw [initMem_size, CardDemo.Cbtrn01c.memSize_eq]
  have htr : ∀ t ∈ vals1.map DalytranRecord.encode, t.length = 350 := by
    intro r hr
    obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode dalytranRecord_contig (hv1 v hv')
  have hac : ∀ a ∈ vals5.map AccountRecord.encode, a.length = 300 := by
    intro r hr
    obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode accountRecord_contig (hv5 v hv')
  have hxeq : vals3.map CardXrefRecord.encode =
      (vals3.map Model.xrefOf).map CardDemo.Cbtrn01c.Xref.bytes := by
    rw [List.map_map]
    exact List.map_congr_left fun x hx => (Model.xrefOf_bytes (hv3 x hx)).1.symm
  have hxv : ∀ x ∈ vals3.map Model.xrefOf, x.valid := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact (Model.xrefOf_bytes (hv3 y hy)).2
  obtain ⟨hstop, hdispC⟩ := CardDemo.Cbtrn01c.cbtrn01c_verifies_all initMem hm
    (vals1.map DalytranRecord.encode) htr (vals3.map Model.xrefOf) hxv
    (vals5.map AccountRecord.encode) hac (vals2.map FdCustfileRec.encode)
    (vals4.map FdCardfileRec.encode) (vals6.map FdTranfileRec.encode) n
    (by simp only [List.length_map]; omega)
  rw [← hxeq] at hstop hdispC
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbtrn01c.run {} (n + 40)
      (CardDemo.Cbtrn01c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (2, vals2.map FdCustfileRec.encode), (3, vals3.map CardXrefRecord.encode),
        (4, vals4.map FdCardfileRec.encode), (5, vals5.map AccountRecord.encode),
        (6, vals6.map FdTranfileRec.encode)])) := by
    rw [EquivLean.Cobol.Ok, hstop]; rfl
  have hrel : Rel (.ok out) (CardDemo.Cbtrn01c.run {} (n + 40)
      (CardDemo.Cbtrn01c.initState initMem [(1, vals1.map DalytranRecord.encode),
        (2, vals2.map FdCustfileRec.encode), (3, vals3.map CardXrefRecord.encode),
        (4, vals4.map FdCardfileRec.encode), (5, vals5.map AccountRecord.encode),
        (6, vals6.map FdTranfileRec.encode)])) := by
    refine ⟨out, rfl, ?_, ?_⟩
    · have e := Model.displayText_eq (trans := vals1) (xs := vals3) (accs := vals5) hv1 hv3 hv5
      rw [← dalytranRecord_eq, ← accountRecord_eq, ← initMem_eq] at e
      rw [hdisp, e, ← displays_eq, hdispC]
      rfl
    · rw [hab, hstop]
      rfl
  rw [hrun, EquivLean.Cobol.run]
  refine ⟨fun _ => ⟨EquivLean.Aeneas.safe_ok _, fun or hor =>
      ⟨CardDemo.Cbtrn01c.run {} (n + 40)
        (CardDemo.Cbtrn01c.initState initMem [(1, vals1.map DalytranRecord.encode),
          (2, vals2.map FdCustfileRec.encode), (3, vals3.map CardXrefRecord.encode),
          (4, vals4.map FdCardfileRec.encode), (5, vals5.map AccountRecord.encode),
          (6, vals6.map FdTranfileRec.encode)]), ?_, ?_⟩⟩,
    fun _ => ⟨(EquivLean.Cobol.safe_exec_iff _).2 hok, fun os hos => ⟨.ok out, ?_, ?_⟩⟩⟩
  · exact (EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩
  · rw [(EquivLean.Aeneas.runs_ok_iff _ _).1 hor]
    exact hrel
  · exact (EquivLean.Aeneas.runs_ok_iff _ _).2 rfl
  · obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
    rw [h1]
    exact hrel

end EquivLean.Modernize.Cbtrn01c.Rust

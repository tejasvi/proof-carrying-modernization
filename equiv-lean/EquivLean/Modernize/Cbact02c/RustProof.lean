import EquivLean.Modernize.Cbact02c.RustStatement

/-!
# CBACT02C → Rust: from the equation of `run` to the generated statement

* the COBOL side: coblean's `cbact02c_lists`, for the records built from the field values;
* the Rust side: `RunSpec`, the equation of `cbact02c.run` (never panics; the `displays` lines are
  the start message, each record's text, the end message; `abended` is false), stated with the
  field texts of `Schema.text` (an alphanumeric field's characters, a numeric field's zero-padded
  digits);
* the glue: a record's text is the CP037 text of its bytes (`Schema.text_eq`).

`statement_of_run`: the equation implies the generated `Statement` (an `Equiv`: Aeneas
computations are total and deterministic).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbact02c.Rust

/-- The start and end messages as Rust bytes (Latin-1 = CP037 text). -/
def startText : List Nat := rustLine CardDemo.Cbact02c.startMsg
def endText : List Nat := rustLine CardDemo.Cbact02c.endMsg

/-- The equation of `run`. -/
def RunSpec : Prop :=
  ∀ (s : Slice cbact02c.CardRecord) (vals : List (List EquivLean.Cobol.Rec.FVal)),
    s.val.map CardRecord.vals = vals → (∀ v ∈ vals, CardRecord.Valid v) → vals.length < 2 ^ 28 →
    ∃ out, cbact02c.run s = .ok out ∧
      out.displays.val.map (fun l => l.val.map (·.val)) =
        startText :: vals.map CardRecord.text ++ [endText] ∧
      out.abended = false

theorem cardRecord_unsigned : ∀ f ∈ CardRecord.fields, UnsignedDisplay f := by decide

theorem displays_eq : CardDemo.Cbact02c.displays = EquivLean.Cobol.Rec.displays := rfl

theorem rustLine_eq_map (bs : List UInt8) : rustLine bs = bs.map cp037Code := rfl

/-- **The equation of `run` implies the generated statement.** -/
theorem statement_of_run (h : RunSpec) : Statement := by
  intro vals1 hv hb n hn s1 hs1
  obtain ⟨out, hrun, hdisp, hab⟩ := h s1 vals1 hs1 hv hb
  have hm : initMem.size = 323 := by rw [initMem_size, CardDemo.Cbact02c.memSize_eq]
  have hlen : ∀ r ∈ vals1.map CardRecord.encode, r.length = 150 := by
    intro r hr
    obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode cardRecord_contig (hv v hv')
  obtain ⟨hstop, hdispC⟩ := CardDemo.Cbact02c.cbact02c_lists initMem hm
    (vals1.map CardRecord.encode) n hlen (by simpa using hn)
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbact02c.run {} (n + 20)
      (CardDemo.Cbact02c.initState initMem [(1, vals1.map CardRecord.encode)])) := by
    rw [EquivLean.Cobol.Ok, hstop]; rfl
  have hrel : Rel (.ok out) (CardDemo.Cbact02c.run {} (n + 20)
      (CardDemo.Cbact02c.initState initMem [(1, vals1.map CardRecord.encode)])) := by
    refine ⟨out, rfl, ?_, ?_⟩
    · rw [hdisp, ← displays_eq, hdispC]
      simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, startText, endText,
        List.cons_append, List.nil_append, List.cons.injEq, List.append_cancel_right_eq, true_and]
      exact List.map_congr_left fun v hv' => by
        simp only [Function.comp_apply, rustLine_eq_map]
        exact (Schema.text_eq cardRecord_unsigned (hv v hv')).symm ▸ rfl
    · rw [hab, hstop]
      rfl
  rw [hrun, EquivLean.Cobol.run]
  refine ⟨fun _ => ⟨EquivLean.Aeneas.safe_ok _, fun or hor =>
      ⟨CardDemo.Cbact02c.run {} (n + 20)
        (CardDemo.Cbact02c.initState initMem [(1, vals1.map CardRecord.encode)]), ?_, ?_⟩⟩,
    fun _ => ⟨(EquivLean.Cobol.safe_exec_iff _).2 hok, fun os hos => ⟨.ok out, ?_, ?_⟩⟩⟩
  · exact (EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩
  · rw [(EquivLean.Aeneas.runs_ok_iff _ _).1 hor]
    exact hrel
  · exact (EquivLean.Aeneas.runs_ok_iff _ _).2 rfl
  · obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
    rw [h1]
    exact hrel

end EquivLean.Modernize.Cbact02c.Rust

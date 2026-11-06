import EquivLean.Modernize.Cbcus01c.RustStatement

/-!
# CBCUS01C → Rust: from the equation of `run` to the generated statement

* the COBOL side: coblean's `cbcus01c_lists`, for the records built from the field values;
* the Rust side: `RunSpec`, the equation of `cbcus01c.run` (never panics; the `displays` lines are
  the start message, each record's text, the end message; `abended` is false), stated with the
  field texts of `Schema.text` (an alphanumeric field's characters, a numeric field's zero-padded
  digits);
* the glue: a record's text is the CP037 text of its bytes (`Schema.text_eq`).

`statement_of_run`: the equation implies the generated `Statement` (an `Equiv`: Aeneas
computations are total and deterministic).
-/

open Cobol EquivLean.Cobol.Rec
open Aeneas Aeneas.Std

namespace EquivLean.Modernize.Cbcus01c.Rust

/-- The start and end messages as Rust bytes (Latin-1 = CP037 text). -/
def startText : List Nat := rustLine CardDemo.Cbcus01c.startMsg
def endText : List Nat := rustLine CardDemo.Cbcus01c.endMsg

/-- The equation of `run`. -/
def RunSpec : Prop :=
  ∀ (s : Slice cbcus01c.CustomerRecord) (vals : List (List EquivLean.Cobol.Rec.FVal)),
    s.val.map CustomerRecord.vals = vals → (∀ v ∈ vals, CustomerRecord.Valid v) → vals.length < 2 ^ 28 →
    ∃ out, cbcus01c.run s = .ok out ∧
      out.displays.val.map (fun l => l.val.map (·.val)) =
        startText :: vals.flatMap (fun v => [CustomerRecord.text v, CustomerRecord.text v]) ++ [endText] ∧
      out.abended = false

theorem customerRecord_unsigned : ∀ f ∈ CustomerRecord.fields, UnsignedDisplay f := by decide

theorem displays_eq : CardDemo.Cbcus01c.displays = EquivLean.Cobol.Rec.displays := rfl

theorem rustLine_eq_map (bs : List UInt8) : rustLine bs = bs.map cp037Code := rfl

/-- **The equation of `run` implies the generated statement.** -/
theorem statement_of_run (h : RunSpec) : Statement := by
  intro vals1 hv hb n hn s1 hs1
  obtain ⟨out, hrun, hdisp, hab⟩ := h s1 vals1 hs1 hv hb
  have hm : initMem.size = 1023 := by rw [initMem_size, CardDemo.Cbcus01c.memSize_eq]
  have hlen : ∀ r ∈ vals1.map CustomerRecord.encode, r.length = 500 := by
    intro r hr
    obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hr
    exact Schema.length_encode customerRecord_contig (hv v hv')
  obtain ⟨hstop, hdispC⟩ := CardDemo.Cbcus01c.cbcus01c_lists initMem hm
    (vals1.map CustomerRecord.encode) n hlen (by simpa using hn)
  have hok : EquivLean.Cobol.Ok (CardDemo.Cbcus01c.run {} (n + 20)
      (CardDemo.Cbcus01c.initState initMem [(1, vals1.map CustomerRecord.encode)])) := by
    rw [EquivLean.Cobol.Ok, hstop]; rfl
  have hrel : Rel (.ok out) (CardDemo.Cbcus01c.run {} (n + 20)
      (CardDemo.Cbcus01c.initState initMem [(1, vals1.map CustomerRecord.encode)])) := by
    refine ⟨out, rfl, ?_, ?_⟩
    · rw [hdisp, ← displays_eq, hdispC]
      simp only [List.map_append, List.map_cons, List.map_nil, startText, endText,
        List.cons_append, List.nil_append, List.cons.injEq, List.append_cancel_right_eq, true_and,
        List.flatMap_map, List.map_flatMap]
      exact flatMap_congr_mem fun v hv' => by
        simp only [rustLine_eq_map,
          Schema.text_eq customerRecord_unsigned (hv v hv')]
    · rw [hab, hstop]
      rfl
  rw [hrun, EquivLean.Cobol.run]
  refine ⟨fun _ => ⟨EquivLean.Aeneas.safe_ok _, fun or hor =>
      ⟨CardDemo.Cbcus01c.run {} (n + 20)
        (CardDemo.Cbcus01c.initState initMem [(1, vals1.map CustomerRecord.encode)]), ?_, ?_⟩⟩,
    fun _ => ⟨(EquivLean.Cobol.safe_exec_iff _).2 hok, fun os hos => ⟨.ok out, ?_, ?_⟩⟩⟩
  · exact (EquivLean.Cobol.runs_exec_iff _ _).2 ⟨rfl, hok⟩
  · rw [(EquivLean.Aeneas.runs_ok_iff _ _).1 hor]
    exact hrel
  · exact (EquivLean.Aeneas.runs_ok_iff _ _).2 rfl
  · obtain ⟨h1, -⟩ := (EquivLean.Cobol.runs_exec_iff _ _).1 hos
    rw [h1]
    exact hrel

end EquivLean.Modernize.Cbcus01c.Rust

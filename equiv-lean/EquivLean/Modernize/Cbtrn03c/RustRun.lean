import EquivLean.Modernize.Cbtrn03c.RustRun10
import EquivLean.Modernize.Cbtrn03c.RustProof

/-!
# CBTRN03C → Rust: the equation of `run`

`run_spec : RunSpec`: `run` displays the start line and the reporting range of the first date
parameter record (the domain has one), then runs the read loop (`run_loop0_spec`) from the model's
state after that line, with the initial record areas.  `rust : Statement`: with the statement side
(`RustProof.statement_of_run`).
-/

open Aeneas Aeneas.Std EquivLean EquivLean.Aeneas
open Cobol EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn03c.Rust
open Cobol.Digits (toDigits)

theorem startL_txt : Model.txt "START OF EXECUTION OF PROGRAM CBTRN03C" = [83, 84, 65, 82, 84, 32,
    79, 70, 32, 69, 88, 69, 67, 85, 84, 73, 79, 78, 32, 79, 70, 32, 80, 82, 79, 71, 82, 65, 77, 32,
    67, 66, 84, 82, 78, 48, 51, 67] := by
  decide

/-- The initial record area holds `Model.tran0`. -/
theorem tran0_vals : TranRecord.vals ⟨Array.repeat 16#usize 32#u8, Array.repeat 2#usize 32#u8,
    0#i64, Array.repeat 10#usize 32#u8, Array.repeat 100#usize 32#u8, 0#i64, 0#i64,
    Array.repeat 50#usize 32#u8, Array.repeat 50#usize 32#u8, Array.repeat 10#usize 32#u8,
    Array.repeat 16#usize 32#u8, Array.repeat 26#usize 32#u8, Array.repeat 26#usize 32#u8,
    Array.repeat 20#usize 32#u8⟩ = Model.tran0 := by
  decide +kernel

/-- The initial cross-reference record area holds `Model.xref0`. -/
theorem xref0_vals : CardXrefRecord.vals ⟨Array.repeat 16#usize 32#u8, 0#i64, 0#i64,
    Array.repeat 14#usize 32#u8⟩ = Model.xref0 := by
  decide +kernel

theorem card0 : (Array.repeat 16#usize 32#u8).val.map ebcU = Model.sp 16 := by
  decide +kernel

set_option maxHeartbeats 20000000 in
/-- **The equation of `run`.** -/
theorem run_spec : RunSpec := by
  intro s1 s2 s3 s4 s5 vals1 vals2 vals3 vals4 vals5 h1 h2 h3 h4 h5 hv1 hv2 hv3 hv4 hv5 hD hL
  subst h1 h2 h3 h4 h5
  unfold Domain at hD
  obtain ⟨_, hpne⟩ := hD
  have hU := usize_max_ge
  have hL1 : s1.val.length < 2 ^ 28 := by simp only [List.length_map] at hL; omega
  have hv1' : ∀ t ∈ s1.val, Model.TranRecord.Valid (TranRecord.vals t) :=
    fun t ht => hv1 _ (List.mem_map.2 ⟨t, ht, rfl⟩)
  have hv2' : ∀ x ∈ s2.val, Model.CardXrefRecord.Valid (CardXrefRecord.vals x) :=
    fun x hx => hv2 _ (List.mem_map.2 ⟨x, hx, rfl⟩)
  obtain ⟨d0, ds', hs5⟩ : ∃ d0 rest, s5.val = d0 :: rest := by
    cases h : s5.val with
    | nil => exact absurd (by simp [h]) hpne
    | cons d0 rest => exact ⟨d0, rest, rfl⟩
  have hlen5 : 0 < s5.val.length := by rw [hs5]; simp
  have hd0 : s5.val[0]'hlen5 = d0 := by simp [hs5]
  dsimp only
  refine exists_ok_of_wp ?_
  unfold cbtrn03c.run
  t03_wp [hlen5, hd0]
  try simp (disch := first | omega | scalar_tac) only [dite_eq_left]
  refine run_loop0_spec s1 s2 s3 s4 _ _ _ _ hv1' hv2' hL1 _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ ?_
  simp only [loopInv]
  refine ⟨Model.dsp Model.init (Model.txt "Reporting from " ++
      Model.cps (Model.dStart (WsDateparmRecord.vals ⟨d0.ws_start_date, d0.filler1,
        d0.ws_end_date⟩)) ++ Model.txt " to " ++
      Model.cps (Model.dEnd (WsDateparmRecord.vals ⟨d0.ws_start_date, d0.filler1,
        d0.ws_end_date⟩))), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, Or.inl ⟨by first | exact trivial | rfl, ?_⟩⟩
  · simp only [alloc.vec.Vec.from_val, List.map_append, List.map_cons, List.map_nil,
      uscalar_ofNat_val, List.nil_append, Model.dsp, Model.init, startL_txt, dStart_vals,
      dEnd_vals, cps_ebcU, List.append_assoc,
      show Model.txt "Reporting from " = [82, 101, 112, 111, 114, 116, 105, 110, 103, 32, 102,
        114, 111, 109, 32] from by decide,
      show Model.txt " to " = [32, 116, 111, 32] from by decide]
  · simp [linesOf, Model.dsp, Model.init]
  · simp [Model.dsp, Model.init]
  · simp [Model.dsp, Model.init]
  · simp [Model.dsp, Model.init]
  · simp [Model.dsp, Model.init]
  · simp [Model.dsp, Model.init, Array.repeat_val]
  · simp [Model.dsp, Model.init, Array.repeat_val]
  · unfold Bnd
    simp [Model.dsp, Model.init]
  · simp only [Model.dsp, Model.init]
    exact card0.symm
  · simp only [Model.dsp, Model.init]
    exact xref0_vals.symm
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp only [uscalar_ofNat_val, List.drop_zero, tran0_vals]
    rw [hs5]
    rfl

/-- **CBTRN03C → Rust**: the generated statement. -/
theorem rust : Statement := statement_of_run run_spec

end EquivLean.Modernize.Cbtrn03c.Rust

#print axioms EquivLean.Modernize.Cbtrn03c.Rust.run_spec
#print axioms EquivLean.Modernize.Cbtrn03c.Rust.rust

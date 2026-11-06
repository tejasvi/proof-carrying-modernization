import EquivLean.Modernize.Cbstm03a.Java.Run5.ThS168
import EquivLean.Modernize.Cbstm03a.Java.Run5.ThTl168

/-!
# CBSTM03A → Java `run`: the thin paths from statement 168 (termination VC of the cards loop's segment)

As for the partial-correctness paths (`CbARun5.C168`): the thin segments `s168t`, `s173t`, `s196t` … `s213t` were
proved with the virtual cut points after them (`MidT`, `TailT k`); `bodyWP_cut_insert` (with the thin handler's
monotonicity `callWPThin_mono`) removes them one by one, the variant bound `v` being the start's `runVar 168`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg5

set_option maxRecDepth 20000 in
/-- **The thin paths from statement 168**: every path to a cut point decreases `runVar`. -/
theorem run_thin168 (g : RunG) : RunThinCut g 168 inv168 := by
  intro args σ0 hpre fr σ hI
  unfold runThinWP
  generalize hv : runVar 168 args σ0 fr σ = v
  have hH := callWPThin_mono Gen.prog runCallees.env 1
  have h0 := s168t g args σ0 hpre fr σ hI v (Nat.le_of_eq hv)
  have h1 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 0) (fun _ => True) 173 rfl (MidT g args σ0 v) 10
    (s173t g args σ0 v) 14 168 fr σ h0
  have h2 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 1) (fun _ => True) 196 rfl (TailT g args σ0 v 0) 8
    (s196t g args σ0 v) _ 168 fr σ h1
  have h3 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 2) (fun _ => True) 199 rfl (TailT g args σ0 v 1) 8
    (s199t g args σ0 v) _ 168 fr σ h2
  have h4 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 3) (fun _ => True) 202 rfl (TailT g args σ0 v 2) 8
    (s202t g args σ0 v) _ 168 fr σ h3
  have h5 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 4) (fun _ => True) 206 rfl (TailT g args σ0 v 3) 8
    (s206t g args σ0 v) _ 168 fr σ h4
  have h6 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 5) (fun _ => True) 207 rfl (TailT g args σ0 v 4) 8
    (s207t g args σ0 v) _ 168 fr σ h5
  have h7 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 6) (fun _ => True) 208 rfl (TailT g args σ0 v 5) 8
    (s208t g args σ0 v) _ 168 fr σ h6
  have h8 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 7) (fun _ => True) 209 rfl (TailT g args σ0 v 6) 8
    (s209t g args σ0 v) _ 168 fr σ h7
  have h9 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 8) (fun _ => True) 210 rfl (TailT g args σ0 v 7) 8
    (s210t g args σ0 v) _ 168 fr σ h8
  have h10 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 9) (fun _ => True) 211 rfl (TailT g args σ0 v 8) 8
    (s211t g args σ0 v) _ 168 fr σ h9
  have h11 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 10) (fun _ => True) 212 rfl (TailT g args σ0 v 9) 8
    (s212t g args σ0 v) _ 168 fr σ h10
  have h12 := bodyWP_cut_insert hH runBodyA (CLt g args σ0 v 11) (fun _ => True) 213 rfl (TailT g args σ0 v 10) 8
    (s213t g args σ0 v) _ 168 fr σ h11
  exact bodyWP_fuel_le hH runBodyA _ _ (by norm_num) 168 fr σ h12

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_thin168

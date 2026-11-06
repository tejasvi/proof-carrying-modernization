import EquivLean.Modernize.Cbstm03a.Java.Run5.S168
import EquivLean.Modernize.Cbstm03a.Java.Run5.Tl168

/-!
# CBSTM03A → Java `run`: the paths from statement 168 (the cards loop of cross-reference record `j`)

The paths from the cards loop's head go through the virtual cut points of `CbARun5.Tail` and `CbARun5.T168`
(173 after `memRead`, 196 … 213 in the statement's tail); `bodyWP_cut_insert` removes them one by one, from the
first: each segment (`s168`, `s173`, `s196` … `s213`) was proved with the cut points after it.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java

open Seg5

set_option maxRecDepth 20000 in
/-- **The paths from statement 168** (the cards loop of record `j`). -/
theorem run_cut168_vc (g : RunG) : RunCutVC g 168 inv168 := by
  intro args σ0 hpre fr σ hI
  have hH := callWP_mono Gen.prog runCallees.env 1
  have h0 := s168 g args σ0 hpre fr σ hI
  have h1 := bodyWP_cut_insert hH runBodyA (CL g args σ0 0) ((runSpecG g).post args σ0) 173 rfl (MidJ g σ0) 10
    (s173 g args σ0) 14 168 fr σ h0
  have h2 := bodyWP_cut_insert hH runBodyA (CL g args σ0 1) ((runSpecG g).post args σ0) 196 rfl (TailJ g σ0 0) 8
    (s196 g args σ0) _ 168 fr σ h1
  have h3 := bodyWP_cut_insert hH runBodyA (CL g args σ0 2) ((runSpecG g).post args σ0) 199 rfl (TailJ g σ0 1) 8
    (s199 g args σ0) _ 168 fr σ h2
  have h4 := bodyWP_cut_insert hH runBodyA (CL g args σ0 3) ((runSpecG g).post args σ0) 202 rfl (TailJ g σ0 2) 8
    (s202 g args σ0) _ 168 fr σ h3
  have h5 := bodyWP_cut_insert hH runBodyA (CL g args σ0 4) ((runSpecG g).post args σ0) 206 rfl (TailJ g σ0 3) 8
    (s206 g args σ0) _ 168 fr σ h4
  have h6 := bodyWP_cut_insert hH runBodyA (CL g args σ0 5) ((runSpecG g).post args σ0) 207 rfl (TailJ g σ0 4) 8
    (s207 g args σ0) _ 168 fr σ h5
  have h7 := bodyWP_cut_insert hH runBodyA (CL g args σ0 6) ((runSpecG g).post args σ0) 208 rfl (TailJ g σ0 5) 8
    (s208 g args σ0) _ 168 fr σ h6
  have h8 := bodyWP_cut_insert hH runBodyA (CL g args σ0 7) ((runSpecG g).post args σ0) 209 rfl (TailJ g σ0 6) 8
    (s209 g args σ0) _ 168 fr σ h7
  have h9 := bodyWP_cut_insert hH runBodyA (CL g args σ0 8) ((runSpecG g).post args σ0) 210 rfl (TailJ g σ0 7) 8
    (s210 g args σ0) _ 168 fr σ h8
  have h10 := bodyWP_cut_insert hH runBodyA (CL g args σ0 9) ((runSpecG g).post args σ0) 211 rfl (TailJ g σ0 8) 8
    (s211 g args σ0) _ 168 fr σ h9
  have h11 := bodyWP_cut_insert hH runBodyA (CL g args σ0 10) ((runSpecG g).post args σ0) 212 rfl
    (TailJ g σ0 9) 8 (s212 g args σ0) _ 168 fr σ h10
  have h12 := bodyWP_cut_insert hH runBodyA (CL g args σ0 11) ((runSpecG g).post args σ0) 213 rfl
    (TailJ g σ0 10) 8 (s213 g args σ0) _ 168 fr σ h11
  unfold runWP
  exact bodyWP_fuel_le hH runBodyA _ _ (by norm_num) 168 fr σ h12

end EquivLean.Modernize.Cbstm03a.Java

#print axioms EquivLean.Modernize.Cbstm03a.Java.run_cut168_vc

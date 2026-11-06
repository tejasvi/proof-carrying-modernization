import EquivLean.Modernize.Cbstm03a.Java.Run5.T168

/-!
# CBSTM03A → Java `run`: the statement's tail (statements 196 … 214), one segment per call on the `Result`

`s196`: `fmtZ(total)`, `repeat('-', 80)`, `stmt`; `s199`: `spaces(56)`, the concatenation `"Total EXP:" … "$" …`,
`stmt`; `s202`: `repeat('*', 32)` twice, the concatenation `… "END OF STATEMENT" …`, `stmt`; `s206` … `s213`: one
`html` with a literal each, the last one back at the cross-reference loop's head (117).
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_trans)
open EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java.Seg5

section Tail

attribute [-simp] List.reduceReplicate

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- `fmtZ`, `repeat('-', 80)`, `stmt`. -/
theorem s196 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 0 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 1) ((runSpecG g).post args σ0)
      8 196 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, h21, -⟩ := hJ
  have h21' := h21 rfl
  have htot' : -9223372036854775808 < total.toInt := by unfold TotOk at htot; omega
  have hT := Kept.intro htot
  clear h21 htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (by grows_tac)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := stmt_post hA (resAtL_grows (xctx_resAtL hX) (by grows_tac))
    exact tail_step hX hj hmodel h7 hinitC (Kept.elim hT)
      (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
        simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
      (keepsRes_trans (keepsRes_of_grows (by grows_tac)) hk') (stmt_line hR' (by assumption) rfl) hi' hs'
      (fun _ => strLoc_after (by assumption) (by simp [Frame.get_setLocal]) (by grows_tac)
        (resAtL_grows (xctx_resAtL hX) (by grows_tac)) hk')

set_option jimple.modelContracts true in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- `spaces(56)`, the concatenation of the total's line, `stmt`. -/
theorem s199 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 1 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 2) ((runSpecG g).post args σ0)
      8 199 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, h32⟩ := hJ
  obtain ⟨xf, hf32, hxf⟩ := h32 rfl
  have hFl := fmtZStr_length total.toInt
  have hT := Kept.intro htot
  clear htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (by grows_tac)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := stmt_post hA (resAtL_grows (xctx_resAtL hX) (by grows_tac))
    exact tail_step hX hj hmodel h7 hinitC (Kept.elim hT)
      (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
        simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
      (keepsRes_trans (keepsRes_of_grows (by grows_tac)) hk') (stmt_line2 hR' rfl) hi' hs'
      (fun h => absurd h (by decide))

set_option jimple.modelContracts true in
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- `repeat('*', 32)` twice, the concatenation of the end line, `stmt`. -/
theorem s202 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 2 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 3) ((runSpecG g).post args σ0)
      8 202 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩ := hJ
  have hT := Kept.intro htot
  clear htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (by grows_tac)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := stmt_post hA (resAtL_grows (xctx_resAtL hX) (by grows_tac))
    exact tail_step hX hj hmodel h7 hinitC (Kept.elim hT)
      (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
        simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
      (keepsRes_trans (keepsRes_of_grows (by grows_tac)) hk') (stmt_line2 hR' rfl) hi' hs'
      (fun h => absurd h (by decide))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s206 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 3 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 4) ((runSpecG g).post args σ0)
      8 206 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩ := hJ
  have hT := Kept.intro htot
  clear htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (grows_alloc _ _)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := html_post hA (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
    exact tail_step hX hj hmodel h7 hinitC (Kept.elim hT) (fun _ _ _ _ _ _ _ _ _ => rfl)
      (keepsRes_trans (keepsRes_of_grows (grows_alloc _ _)) hk') (html_line hR' rfl) hi' hs'
      (fun h => absurd h (by decide))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s207 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 4 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 5) ((runSpecG g).post args σ0)
      8 207 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩ := hJ
  have hT := Kept.intro htot
  clear htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (grows_alloc _ _)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := html_post hA (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
    exact tail_step hX hj hmodel h7 hinitC (Kept.elim hT) (fun _ _ _ _ _ _ _ _ _ => rfl)
      (keepsRes_trans (keepsRes_of_grows (grows_alloc _ _)) hk') (html_line hR' rfl) hi' hs'
      (fun h => absurd h (by decide))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s208 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 5 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 6) ((runSpecG g).post args σ0)
      8 208 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩ := hJ
  have hT := Kept.intro htot
  clear htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (grows_alloc _ _)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := html_post hA (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
    exact tail_step hX hj hmodel h7 hinitC (Kept.elim hT) (fun _ _ _ _ _ _ _ _ _ => rfl)
      (keepsRes_trans (keepsRes_of_grows (grows_alloc _ _)) hk') (html_line hR' rfl) hi' hs'
      (fun h => absurd h (by decide))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s209 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 6 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 7) ((runSpecG g).post args σ0)
      8 209 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩ := hJ
  have hT := Kept.intro htot
  clear htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (grows_alloc _ _)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := html_post hA (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
    exact tail_step hX hj hmodel h7 hinitC (Kept.elim hT) (fun _ _ _ _ _ _ _ _ _ => rfl)
      (keepsRes_trans (keepsRes_of_grows (grows_alloc _ _)) hk') (html_line hR' rfl) hi' hs'
      (fun h => absurd h (by decide))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s210 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 7 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 8) ((runSpecG g).post args σ0)
      8 210 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩ := hJ
  have hT := Kept.intro htot
  clear htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (grows_alloc _ _)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := html_post hA (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
    exact tail_step hX hj hmodel h7 hinitC (Kept.elim hT) (fun _ _ _ _ _ _ _ _ _ => rfl)
      (keepsRes_trans (keepsRes_of_grows (grows_alloc _ _)) hk') (html_line hR' rfl) hi' hs'
      (fun h => absurd h (by decide))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s211 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 8 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 9) ((runSpecG g).post args σ0)
      8 211 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩ := hJ
  have hT := Kept.intro htot
  clear htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (grows_alloc _ _)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := html_post hA (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
    exact tail_step hX hj hmodel h7 hinitC (Kept.elim hT) (fun _ _ _ _ _ _ _ _ _ => rfl)
      (keepsRes_trans (keepsRes_of_grows (grows_alloc _ _)) hk') (html_line hR' rfl) hi' hs'
      (fun h => absurd h (by decide))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem s212 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 9 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 10) ((runSpecG g).post args σ0)
      8 212 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩ := hJ
  have hT := Kept.intro htot
  clear htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (grows_alloc _ _)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := html_post hA (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
    exact tail_step hX hj hmodel h7 hinitC (Kept.elim hT) (fun _ _ _ _ _ _ _ _ _ => rfl)
      (keepsRes_trans (keepsRes_of_grows (grows_alloc _ _)) hk') (html_line hR' rfl) hi' hs'
      (fun h => absurd h (by decide))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The last `html`, back at the cross-reference loop's head. -/
theorem s213 (g : RunG) (args : List Value) (σ0 : State) (fr : Frame) (σ : State) (hJ : TailJ g σ0 10 fr σ) :
    bodyWP Gen.prog (callWP Gen.prog runCallees.env 1) runBodyA (CL g args σ0 11) ((runSpecG g).post args σ0)
      8 213 fr σ := by
  obtain ⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩ := hJ
  have hT := Kept.intro htot
  clear htot
  jvc [runCallees, runInv, runSpecG, CL, tailCuts, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, ite_nat_ne, grows_split, StrOk]
  · obtain ⟨hX, -, -⟩ := Kept.elim hK
    exact ⟨ld, ls, lh, _, _, _, resAtL_or (xctx_resAtL hX) (grows_alloc _ _)⟩
  · rename_i v σ' hA
    obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
    obtain ⟨hR', hk', hi', hs'⟩ := html_post hA (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
    exact tail_last hX hj hmodel (fun _ _ _ _ _ _ _ _ _ => rfl)
      (keepsRes_trans (keepsRes_of_grows (grows_alloc _ _)) hk') (html_line hR' rfl) hi' hs'

end Tail

end EquivLean.Modernize.Cbstm03a.Java.Seg5

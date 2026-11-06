import EquivLean.Modernize.Cbstm03a.Java.Run5.Thin168

/-!
# CBSTM03A → Java `run`, thin VC: the statement's tail, one segment per call on the `Result`

`s196t` … `s213t`: the paths of `s196` … `s213` with the thin handler; each cut point asserts `TailT (k + 1)` (the
partial-correctness facts and the next record's variant below the start's), the last one `runVar 117 < v`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_trans)
open EquivLean.Modernize.Cbstm03a.Java

namespace EquivLean.Modernize.Cbstm03a.Java.Seg5

section Tail

attribute [-simp] List.reduceReplicate

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `fmtZ`, `repeat('-', 80)`, `stmt` (thin). -/
theorem s196t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 0 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 1) (fun _ => True)
      8 196 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, h21, -⟩, hv⟩ := hJ
  have h21' := h21 rfl
  have htot' : -9223372036854775808 < total.toInt := by unfold TotOk at htot; omega
  have hT := Kept.intro (And.intro htot hv)
  clear h21 htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
  obtain ⟨htot, hv⟩ := Kept.elim hT
  obtain ⟨hR', hk', hi', hs'⟩ := stmt_post (by assumption) (resAtL_grows (xctx_resAtL hX) (by grows_tac))
  exact tailT_step hX hj hmodel h7 hinitC htot
    (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
      simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
    (by grows_tac) hk' (stmt_line hR' (by assumption) rfl) hi' hs'
    (fun _ => strLoc_after (by assumption) (by simp [Frame.get_setLocal]) (by grows_tac)
      (resAtL_grows (xctx_resAtL hX) (by grows_tac)) hk') hv

set_option jimple.modelContracts true in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `spaces(56)`, the concatenation of the total's line, `stmt` (thin). -/
theorem s199t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 1 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 2) (fun _ => True)
      8 199 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, h32⟩, hv⟩ := hJ
  obtain ⟨xf, hf32, hxf⟩ := h32 rfl
  have hFl := fmtZStr_length total.toInt
  have hT := Kept.intro (And.intro htot hv)
  clear htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
  obtain ⟨htot, hv⟩ := Kept.elim hT
  obtain ⟨hR', hk', hi', hs'⟩ := stmt_post (by assumption) (resAtL_grows (xctx_resAtL hX) (by grows_tac))
  exact tailT_step hX hj hmodel h7 hinitC htot
    (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
      simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
    (by grows_tac) hk' (stmt_line2 hR' rfl) hi' hs' (fun h => absurd h (by decide)) hv

set_option jimple.modelContracts true in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- `repeat('*', 32)` twice, the concatenation of the end line, `stmt` (thin). -/
theorem s202t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 2 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 3) (fun _ => True)
      8 202 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩, hv⟩ := hJ
  have hT := Kept.intro (And.intro htot hv)
  clear htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
  obtain ⟨htot, hv⟩ := Kept.elim hT
  obtain ⟨hR', hk', hi', hs'⟩ := stmt_post (by assumption) (resAtL_grows (xctx_resAtL hX) (by grows_tac))
  exact tailT_step hX hj hmodel h7 hinitC htot
    (fun k a0 a4 a17 a19 a22 a26 a32 a33 => by
      simp [Frame.get_setLocal, a0, a4, a17, a19, a22, a26, a32, a33])
    (by grows_tac) hk' (stmt_line2 hR' rfl) hi' hs' (fun h => absurd h (by decide)) hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s206t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 3 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 4) (fun _ => True)
      8 206 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩, hv⟩ := hJ
  have hT := Kept.intro (And.intro htot hv)
  clear htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
  obtain ⟨htot, hv⟩ := Kept.elim hT
  obtain ⟨hR', hk', hi', hs'⟩ := html_post (by assumption) (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
  exact tailT_step hX hj hmodel h7 hinitC htot (fun _ _ _ _ _ _ _ _ _ => rfl) (grows_alloc _ _) hk'
    (html_line hR' rfl) hi' hs' (fun h => absurd h (by decide)) hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s207t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 4 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 5) (fun _ => True)
      8 207 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩, hv⟩ := hJ
  have hT := Kept.intro (And.intro htot hv)
  clear htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
  obtain ⟨htot, hv⟩ := Kept.elim hT
  obtain ⟨hR', hk', hi', hs'⟩ := html_post (by assumption) (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
  exact tailT_step hX hj hmodel h7 hinitC htot (fun _ _ _ _ _ _ _ _ _ => rfl) (grows_alloc _ _) hk'
    (html_line hR' rfl) hi' hs' (fun h => absurd h (by decide)) hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s208t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 5 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 6) (fun _ => True)
      8 208 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩, hv⟩ := hJ
  have hT := Kept.intro (And.intro htot hv)
  clear htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
  obtain ⟨htot, hv⟩ := Kept.elim hT
  obtain ⟨hR', hk', hi', hs'⟩ := html_post (by assumption) (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
  exact tailT_step hX hj hmodel h7 hinitC htot (fun _ _ _ _ _ _ _ _ _ => rfl) (grows_alloc _ _) hk'
    (html_line hR' rfl) hi' hs' (fun h => absurd h (by decide)) hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s209t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 6 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 7) (fun _ => True)
      8 209 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩, hv⟩ := hJ
  have hT := Kept.intro (And.intro htot hv)
  clear htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
  obtain ⟨htot, hv⟩ := Kept.elim hT
  obtain ⟨hR', hk', hi', hs'⟩ := html_post (by assumption) (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
  exact tailT_step hX hj hmodel h7 hinitC htot (fun _ _ _ _ _ _ _ _ _ => rfl) (grows_alloc _ _) hk'
    (html_line hR' rfl) hi' hs' (fun h => absurd h (by decide)) hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s210t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 7 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 8) (fun _ => True)
      8 210 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩, hv⟩ := hJ
  have hT := Kept.intro (And.intro htot hv)
  clear htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
  obtain ⟨htot, hv⟩ := Kept.elim hT
  obtain ⟨hR', hk', hi', hs'⟩ := html_post (by assumption) (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
  exact tailT_step hX hj hmodel h7 hinitC htot (fun _ _ _ _ _ _ _ _ _ => rfl) (grows_alloc _ _) hk'
    (html_line hR' rfl) hi' hs' (fun h => absurd h (by decide)) hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s211t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 8 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 9) (fun _ => True)
      8 211 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩, hv⟩ := hJ
  have hT := Kept.intro (And.intro htot hv)
  clear htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
  obtain ⟨htot, hv⟩ := Kept.elim hT
  obtain ⟨hR', hk', hi', hs'⟩ := html_post (by assumption) (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
  exact tailT_step hX hj hmodel h7 hinitC htot (fun _ _ _ _ _ _ _ _ _ => rfl) (grows_alloc _ _) hk'
    (html_line hR' rfl) hi' hs' (fun h => absurd h (by decide)) hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s212t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 9 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 10) (fun _ => True)
      8 212 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩, hv⟩ := hJ
  have hT := Kept.intro (And.intro htot hv)
  clear htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, hj, hmodel⟩ := Kept.elim hK
  obtain ⟨htot, hv⟩ := Kept.elim hT
  obtain ⟨hR', hk', hi', hs'⟩ := html_post (by assumption) (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
  exact tailT_step hX hj hmodel h7 hinitC htot (fun _ _ _ _ _ _ _ _ _ => rfl) (grows_alloc _ _) hk'
    (html_line hR' rfl) hi' hs' (fun h => absurd h (by decide)) hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The last `html`, back at the cross-reference loop's head (thin). -/
theorem s213t (g : RunG) (args : List Value) (σ0 : State) (v : Nat) (fr : Frame) (σ : State)
    (hJ : TailT g args σ0 v 10 fr σ) :
    bodyWP Gen.prog (callWPThin Gen.prog runCallees.env 1) runBodyA (CLt g args σ0 v 11) (fun _ => True)
      8 213 fr σ := by
  obtain ⟨⟨res, ld, ls, lh, L, oc, j, total, hK, h7, hinitC, htot, -, -⟩, hv⟩ := hJ
  have hT := Kept.intro hv
  clear htot hv
  jvc [runCallees, runInv, CLt, tailCutsT, TI, List.drop_succ_cons, List.drop_zero, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, ite_nat_ne, grows_split, StrOk]
  obtain ⟨hX, -, -⟩ := Kept.elim hK
  obtain ⟨-, hk', -, -⟩ := html_post (by assumption) (resAtL_grows (xctx_resAtL hX) (grows_alloc _ _))
  exact tailT_last hX (fun _ _ _ _ _ _ _ _ _ => rfl) (grows_alloc _ _) hk' (Kept.elim hT)

end Tail

end EquivLean.Modernize.Cbstm03a.Java.Seg5

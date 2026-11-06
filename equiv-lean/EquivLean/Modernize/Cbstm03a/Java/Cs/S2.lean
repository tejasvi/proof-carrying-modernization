import EquivLean.Modernize.Cbstm03a.Java.Cs.Seg

/-!
# CBSTM03A → Java: `createStatement`, the concatenations

From a cut point to the cut point before the next call of `stmt`/`html`, whose argument is a new concatenation
(`spaces`, `fix`, `makeConcatWithConstants`).
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s115 (g : G) : CutVC g 115 2 56 LE false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 2 56 (LE g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LE g) := hI.2.1
  obtain ⟨x6, h6a, h6b, h6c⟩ := locsAt_mem hL (p := (6, tAddr1 g)) (by simp [LE])
  clear hI hL
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, spacesSpecI, fixSpecI, repeatSpec, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
      by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte] <;> rfl,
      by simp only [tL3, List.length_append, List.length_replicate]; have := sub_length_le g.c 84 134; omega⟩,
      locsAt_frame (by grows_tac) (locsAt_sub (by simp [LF, LE]) hI.2.1) (by simp [LF, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s118 (g : G) : CutVC g 118 3 56 LF false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 3 56 (LF g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LF g) := hI.2.1
  obtain ⟨x7, h7a, h7b, h7c⟩ := locsAt_mem hL (p := (7, tAddr2 g)) (by simp [LF])
  clear hI hL
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, spacesSpecI, fixSpecI, repeatSpec, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
      by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte] <;> rfl,
      by simp only [tL4, List.length_append, List.length_replicate]; have := sub_length_le g.c 134 184; omega⟩,
      locsAt_frame (by grows_tac) (locsAt_sub (by simp [LG, LF]) hI.2.1) (by simp [LG, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s123 (g : G) : CutVC g 123 6 56 LH false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 6 56 (LH g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LH g) := hI.2.1
  clear hI hL
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, spacesSpecI, fixSpecI, repeatSpec, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
      by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte] <;> rfl,
      by decide +kernel⟩,
      locsAt_frame (by grows_tac) (locsAt_sub (by simp [LH, LH]) hI.2.1) (by simp [LH, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s138 (g : G) : CutVC g 138 12 56 LK false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 12 56 (LK g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LK g) := hI.2.1
  clear hI hL
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, spacesSpecI, fixSpecI, repeatSpec, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
      by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte] <;> rfl,
      by decide +kernel⟩,
      locsAt_frame (by grows_tac) (locsAt_sub (by simp [LK, LK]) hI.2.1) (by simp [LK, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s143 (g : G) : CutVC g 143 14 56 LK false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 14 56 (LK g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LK g) := hI.2.1
  clear hI hL
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, spacesSpecI, fixSpecI, repeatSpec, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
      by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte] <;> rfl,
      by decide +kernel⟩,
      locsAt_frame (by grows_tac) (locsAt_sub (by simp [LK, LK]) hI.2.1) (by simp [LK, Frame.get_setLocal])⟩

end EquivLean.Modernize.Cbstm03a.Java.Cs

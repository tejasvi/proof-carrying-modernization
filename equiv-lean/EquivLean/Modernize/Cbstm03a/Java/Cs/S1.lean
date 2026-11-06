import EquivLean.Modernize.Cbstm03a.Java.Cs.Seg

/-!
# CBSTM03A → Java: `createStatement`, the `para` and `star` calls

From the cut point after an HTML line to the cut point before the next `html` call, whose argument `acctId` (local
13) now holds a `para`/`star` line.
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s72 (g : G) : CutVC g 72 1 23 LD false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 23 (LD g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hLD : LocsAt σ fr (LD g) := hI.2.1
  obtain ⟨x6, h6a, h6b, h6c⟩ := hLD.1
  obtain ⟨x7, h7a, h7b, h7c⟩ := hLD.2.1
  obtain ⟨x15, h15a, h15b, h15c⟩ := hLD.2.2.1
  obtain ⟨x16, h16a, h16b, h16c⟩ := hLD.2.2.2.1
  obtain ⟨x17, h17a, h17b, h17c⟩ := hLD.2.2.2.2.1
  obtain ⟨x18, h18a, h18b, h18c⟩ := hLD.2.2.2.2.2.1
  obtain ⟨x19, h19a, h19b, h19c⟩ := hLD.2.2.2.2.2.2.1
  clear hI hLD
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, paraSpec, starSpec, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (by simp)
    exact ⟨⟨w, by simp [Frame.get_setLocal], heap_str_eq (by assumption) (by rw [paraStr_eq]; rfl),
      by simp [tPara2, paraT, starT]⟩, locsAt_frame (by grows_tac) hI.2.1 (by simp [LD, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s74 (g : G) : CutVC g 74 1 24 LD false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 24 (LD g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hLD : LocsAt σ fr (LD g) := hI.2.1
  obtain ⟨x6, h6a, h6b, h6c⟩ := hLD.1
  obtain ⟨x7, h7a, h7b, h7c⟩ := hLD.2.1
  obtain ⟨x15, h15a, h15b, h15c⟩ := hLD.2.2.1
  obtain ⟨x16, h16a, h16b, h16c⟩ := hLD.2.2.2.1
  obtain ⟨x17, h17a, h17b, h17c⟩ := hLD.2.2.2.2.1
  obtain ⟨x18, h18a, h18b, h18c⟩ := hLD.2.2.2.2.2.1
  obtain ⟨x19, h19a, h19b, h19c⟩ := hLD.2.2.2.2.2.2.1
  clear hI hLD
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, paraSpec, starSpec, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (by simp)
    exact ⟨⟨w, by simp [Frame.get_setLocal], heap_str_eq (by assumption) (by rw [paraStr_eq]; rfl),
      by simp [tPara3, paraT, starT]⟩, locsAt_frame (by grows_tac) hI.2.1 (by simp [LD, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s76 (g : G) : CutVC g 76 1 25 LD false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 25 (LD g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hLD : LocsAt σ fr (LD g) := hI.2.1
  obtain ⟨x6, h6a, h6b, h6c⟩ := hLD.1
  obtain ⟨x7, h7a, h7b, h7c⟩ := hLD.2.1
  obtain ⟨x15, h15a, h15b, h15c⟩ := hLD.2.2.1
  obtain ⟨x16, h16a, h16b, h16c⟩ := hLD.2.2.2.1
  obtain ⟨x17, h17a, h17b, h17c⟩ := hLD.2.2.2.2.1
  obtain ⟨x18, h18a, h18b, h18c⟩ := hLD.2.2.2.2.2.1
  obtain ⟨x19, h19a, h19b, h19c⟩ := hLD.2.2.2.2.2.2.1
  clear hI hLD
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, paraSpec, starSpec, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (by simp)
    exact ⟨⟨w, by simp [Frame.get_setLocal], heap_str_eq (by assumption) (by rw [paraStr_eq]; rfl),
      by simp [tPara4, paraT, starT]⟩, locsAt_frame (by grows_tac) hI.2.1 (by simp [LD, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s87 (g : G) : CutVC g 87 1 35 LD false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 35 (LD g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hLD : LocsAt σ fr (LD g) := hI.2.1
  obtain ⟨x6, h6a, h6b, h6c⟩ := hLD.1
  obtain ⟨x7, h7a, h7b, h7c⟩ := hLD.2.1
  obtain ⟨x15, h15a, h15b, h15c⟩ := hLD.2.2.1
  obtain ⟨x16, h16a, h16b, h16c⟩ := hLD.2.2.2.1
  obtain ⟨x17, h17a, h17b, h17c⟩ := hLD.2.2.2.2.1
  obtain ⟨x18, h18a, h18b, h18c⟩ := hLD.2.2.2.2.2.1
  obtain ⟨x19, h19a, h19b, h19c⟩ := hLD.2.2.2.2.2.2.1
  clear hI hLD
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, paraSpec, starSpec, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (by simp)
    exact ⟨⟨w, by simp [Frame.get_setLocal], heap_str_eq (by assumption) (by rw [starStr_eq]; rfl),
      by simp [tStar1, paraT, starT]⟩, locsAt_frame (by grows_tac) hI.2.1 (by simp [LD, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s89 (g : G) : CutVC g 89 1 36 LD false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 36 (LD g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hLD : LocsAt σ fr (LD g) := hI.2.1
  obtain ⟨x6, h6a, h6b, h6c⟩ := hLD.1
  obtain ⟨x7, h7a, h7b, h7c⟩ := hLD.2.1
  obtain ⟨x15, h15a, h15b, h15c⟩ := hLD.2.2.1
  obtain ⟨x16, h16a, h16b, h16c⟩ := hLD.2.2.2.1
  obtain ⟨x17, h17a, h17b, h17c⟩ := hLD.2.2.2.2.1
  obtain ⟨x18, h18a, h18b, h18c⟩ := hLD.2.2.2.2.2.1
  obtain ⟨x19, h19a, h19b, h19c⟩ := hLD.2.2.2.2.2.2.1
  clear hI hLD
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, paraSpec, starSpec, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (by simp)
    exact ⟨⟨w, by simp [Frame.get_setLocal], heap_str_eq (by assumption) (by rw [starStr_eq]; rfl),
      by simp [tStar2, paraT, starT]⟩, locsAt_frame (by grows_tac) hI.2.1 (by simp [LD, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem s91 (g : G) : CutVC g 91 1 37 LD false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 37 (LD g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hLD : LocsAt σ fr (LD g) := hI.2.1
  obtain ⟨x6, h6a, h6b, h6c⟩ := hLD.1
  obtain ⟨x7, h7a, h7b, h7c⟩ := hLD.2.1
  obtain ⟨x15, h15a, h15b, h15c⟩ := hLD.2.2.1
  obtain ⟨x16, h16a, h16b, h16c⟩ := hLD.2.2.2.1
  obtain ⟨x17, h17a, h17b, h17c⟩ := hLD.2.2.2.2.1
  obtain ⟨x18, h18a, h18b, h18c⟩ := hLD.2.2.2.2.2.1
  obtain ⟨x19, h19a, h19b, h19c⟩ := hLD.2.2.2.2.2.2.1
  clear hI hLD
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, paraSpec, starSpec, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (by simp)
    exact ⟨⟨w, by simp [Frame.get_setLocal], heap_str_eq (by assumption) (by rw [starStr_eq]; rfl),
      by simp [tStar3, paraT, starT]⟩, locsAt_frame (by grows_tac) hI.2.1 (by simp [LD, Frame.get_setLocal])⟩

end EquivLean.Modernize.Cbstm03a.Java.Cs

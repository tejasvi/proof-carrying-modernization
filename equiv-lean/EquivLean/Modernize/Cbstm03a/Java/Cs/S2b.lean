import EquivLean.Modernize.Cbstm03a.Java.Cs.Seg

/-!
# CBSTM03A → Java: `createStatement`, the concatenations with literal recipes

From a cut point to the cut point before the next call of `stmt`/`html`, whose argument is a new concatenation
(`spaces`, `fix`, `makeConcatWithConstants`).
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

attribute [local irreducible] tStAcctId tStFico tAcctId tStCurrBal fixStr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s30 (g : G) : CutVC g 30 1 10 LA true := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 10 (LA g) true σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LA g) := hI.2.1
  obtain ⟨x13, h13a, h13b, h13c⟩ := locsAt_mem hL (p := (13, tAcctId g)) (by simp [LA])
  clear hI hL
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, spacesSpecI, fixSpecI, repeatSpec, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
      by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte, tH3, tAcctId] <;> rfl,
      by have : (jl "<h3>Statement for Account Number: ").length + (jl "</h3>").length < 1000 := (by decide +kernel); simp only [tH3, List.length_append, fixStr_length] <;> omega⟩,
      locsAt_frame (by grows_tac) (locsAt_sub (by simp [LA, LA]) hI.2.1) (by simp [LA, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s128 (g : G) : CutVC g 128 8 56 LH false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 8 56 (LH g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LH g) := hI.2.1
  obtain ⟨x17, h17a, h17b, h17c⟩ := locsAt_mem hL (p := (17, tStAcctId g)) (by simp [LH])
  clear hI hL
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, spacesSpecI, fixSpecI, repeatSpec, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
      by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte, tL9, tStAcctId] <;> rfl,
      by have : (jl "Account ID         :").length < 1000 := (by decide +kernel); simp only [tL9, List.length_append, fixStr_length, List.length_replicate] <;> omega⟩,
      locsAt_frame (by grows_tac) (locsAt_sub (by simp [LI, LH]) hI.2.1) (by simp [LI, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s131 (g : G) : CutVC g 131 9 56 LI false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 9 56 (LI g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LI g) := hI.2.1
  obtain ⟨x18, h18a, h18b, h18c⟩ := locsAt_mem hL (p := (18, tStCurrBal g)) (by simp [LI])
  clear hI hL
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, spacesSpecI, fixSpecI, repeatSpec, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
      by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte, tL10, tStCurrBal] <;> rfl,
      by have : (jl "Current Balance    :").length < 1000 := (by decide +kernel); simp only [tL10, fmtCurrBalI, List.length_append, EquivLean.Modernize.Cbstm03b.Java.zpadStr_length, List.length_replicate, List.length_cons, List.length_nil] <;> omega⟩,
      locsAt_frame (by grows_tac) (locsAt_sub (by simp [LJ, LI]) hI.2.1) (by simp [LJ, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s134 (g : G) : CutVC g 134 10 56 LJ false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 10 56 (LJ g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LJ g) := hI.2.1
  obtain ⟨x19, h19a, h19b, h19c⟩ := locsAt_mem hL (p := (19, tStFico g)) (by simp [LJ])
  clear hI hL
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, spacesSpecI, fixSpecI, repeatSpec, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_ (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
      by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte, tL11, tStFico] <;> rfl,
      by have : (jl "FICO Score         :").length < 1000 := (by decide +kernel); simp only [tL11, List.length_append, fixStr_length, List.length_replicate] <;> omega⟩,
      locsAt_frame (by grows_tac) (locsAt_sub (by simp [LK, LJ]) hI.2.1) (by simp [LK, Frame.get_setLocal])⟩

end EquivLean.Modernize.Cbstm03a.Java.Cs

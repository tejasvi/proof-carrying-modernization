import EquivLean.Modernize.Cbstm03a.Java.Cs.Seg

/-!
# CBSTM03A → Java: `createStatement`, the dashes and the name line

From the cut point after the last HTML line to the cut point before the second statement line: `dashes`
(`repeat`), `spaces(5)` and the name line `stName + spaces(5)`.
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

attribute [local irreducible] tStName tStAdd3 tStAcctId tStFico tStCurrBal fixStr

theorem heap_of_grows {σ σ' : State} {x : Addr} {o : Obj} (h : σ.heap x = some o) (hg : Grows σ σ') :
    σ'.heap x = some o := by
  rw [hg.2 x (State.lt_next_of_heap h), h]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem s111 (g : G) : CutVC g 111 1 56 LD false := by
  intro args σ0 _ fr σ hI
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 56 (LD g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LD g) := hI.2.1
  obtain ⟨x15, h15a, h15b, h15c⟩ := locsAt_mem hL (p := (15, tStName g)) (by simp [LD])
  clear hI hL
  unfold wp
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, spacesSpecI, fixSpecI, repeatSpec, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_
      (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact locsAt_sub (L := (3, tL2 g) :: (21, tDashes) :: LD g) (by simp [LE114, LE, LD])
      ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
        by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte, tL2, tStName] <;> rfl,
        by simp only [tL2, stNameT, List.length_append, List.length_replicate, fixStr_length] <;> omega⟩,
       ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, heap_str_eq (heap_of_grows (by assumption) (by grows_tac)) (by rfl),
        by decide +kernel⟩,
       locsAt_frame (by grows_tac) hI.2.1 (by simp [LD, Frame.get_setLocal])⟩

end EquivLean.Modernize.Cbstm03a.Java.Cs

import EquivLean.Modernize.Cbstm03a.Java.Cs.B44

/-!
# CBSTM03A → Java: `createStatement`, the address builder (statements 54 … 65)

`a3 = new StringBuilder()` (`p54a`), the eight `app` calls, `a3.toString()` and `fix(…, 80)` (`p54b`).
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans fixStr_length heap_grows)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

/-- The address builder's text after the eight `app` calls, `fix`ed: the third address line's text. -/
theorem ad_eq (g : G) :
    fixStr (appStr (appStr (appStr (appStr (appStr (appStr (appStr (appStr [] 80 (tAddr3 g)
      (some (JStr.ofString " "))) 80 (JStr.ofString " ") none) 80 (tState g) (some (JStr.ofString " "))) 80
      (JStr.ofString " ") none) 80 (tCountry g) (some (JStr.ofString " "))) 80 (JStr.ofString " ") none) 80
      (tZip g) (some (JStr.ofString " "))) 80 (JStr.ofString " ") none) 80 = tStAdd3 g := by
  simp only [appStr80]
  rfl

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem p54a (g : G) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hI : cut g 1 22 LB true args σ0 fr σ) :
    bodyWP Gen.prog csH body ((56, bcut g 1 22 LB true 24 [] args σ0) :: (inv g).inst args σ0)
      ((specG g).post args σ0) 10 54 fr σ := by
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 22 (LB g) true σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  clear hI
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, grows_split]
  all_goals
    rw [bcut_unfold]
    have hI := Kept.elim hK
    have hg := grows_newB σ (.plain "java.lang.StringBuilder" []) (.builder "java.lang.StringBuilder" [])
    refine ⟨cutI_next hI hg (by simp [Frame.get_setLocal]) rfl rfl
      (locsAt_frame hg hI.2.1 (by simp [LB, Frame.get_setLocal]))
      (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h),
      σ.next, by simp [Frame.get_setLocal], ?_, hI.1.2.2.1.1, by simp⟩
    rw [State.heap_setObj_of_lt (by rw [State.next_alloc]; exact Nat.lt_succ_self _)]
    simp

attribute [local irreducible] appStr tAddr3 tState tCountry tZip fixStr

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem p54b (g : G) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hB : bcut g 1 22 LB true 24 (appStr (appStr (appStr (appStr (appStr (appStr (appStr (appStr [] 80 (tAddr3 g)
      (some (JStr.ofString " "))) 80 (JStr.ofString " ") none) 80 (tState g) (some (JStr.ofString " "))) 80
      (JStr.ofString " ") none) 80 (tCountry g) (some (JStr.ofString " "))) 80 (JStr.ofString " ") none) 80
      (tZip g) (some (JStr.ofString " "))) 80 (JStr.ofString " ") none) args σ0 fr σ) :
    bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) 10 64 fr σ := by
  rw [bcut_unfold] at hB
  have hK : Kept (CutI g 1 22 (LB g) true σ0 fr σ) := Kept.intro hB.1
  have hres := hB.1.1.1
  have hini := hB.1.1.2.2.2.2.2
  obtain ⟨d, hk, hd, hd0, hbl⟩ := hB.2
  clear hB
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, fixSpecI, StrOk, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_
      (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact locsAt_sub (L := (16, tStAdd3 g) :: LB g) (by simp [LC, LB])
      ⟨⟨w, by simp [Frame.get_setLocal], heap_str_eq (by assumption) (ad_eq g),
        by simp only [tStAdd3, stAdd3T, fixStr_length]; omega⟩,
       locsAt_frame (by grows_tac) hI.2.1 (by simp [LB, Frame.get_setLocal])⟩

end EquivLean.Modernize.Cbstm03a.Java.Cs

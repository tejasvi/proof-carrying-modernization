import EquivLean.Modernize.Cbstm03a.Java.Cs.Build

/-!
# CBSTM03A → Java: `createStatement`, the name builder (statements 44 … 53)

`nm = new StringBuilder()` (`p44a`), the six `app` calls (`bcut_app_ll`, `bcut_app_lit`), `nm.toString()` and
`fix(…, 75)` (`p44b`), with virtual cut points after each statement up to 52.
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans fixStr_length heap_grows)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

theorem grows_newB (σ : State) (o o' : Obj) : Grows σ ((σ.alloc o).2.setObj σ.next o') :=
  ⟨by rw [State.next_setObj, State.next_alloc]; exact Nat.le_succ _, fun x hx => by
    rw [State.heap_setObj, ite_eq_right_iff.mpr (fun h => absurd h (Nat.ne_of_lt hx)), State.heap_alloc_of_lt hx]⟩

theorem appStr75 (b src : JStr) (d : Option JStr) : appStr b 75 src d = appT b 75 src d :=
  appStr_eq_appT b 75 (by decide) src d

theorem appStr80 (b src : JStr) (d : Option JStr) : appStr b 80 src d = appT b 80 src d :=
  appStr_eq_appT b 80 (by decide) src d

/-- The name builder's text after the six `app` calls, `fix`ed: the name line's text. -/
theorem nm_eq (g : G) :
    fixStr (appStr (appStr (appStr (appStr (appStr (appStr [] 75 (tFirst g) (some (JStr.ofString " "))) 75
      (JStr.ofString " ") none) 75 (tMiddle g) (some (JStr.ofString " "))) 75 (JStr.ofString " ") none) 75
      (tLast g) (some (JStr.ofString " "))) 75 (JStr.ofString " ") none) 75 = tStName g := by
  simp only [appStr75]
  rfl

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem p44a (g : G) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hI : cut g 1 22 LA true args σ0 fr σ) :
    bodyWP Gen.prog csH body ((46, bcut g 1 22 LA true 23 [] args σ0) :: (inv g).inst args σ0)
      ((specG g).post args σ0) 10 44 fr σ := by
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 22 (LA g) true σ0 fr σ) := Kept.intro hI
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
      (locsAt_frame hg hI.2.1 (by simp [LA, Frame.get_setLocal]))
      (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h),
      σ.next, by simp [Frame.get_setLocal], ?_, hI.1.2.2.1.1, by simp⟩
    rw [State.heap_setObj_of_lt (by rw [State.next_alloc]; exact Nat.lt_succ_self _)]
    simp

attribute [local irreducible] appStr tFirst tMiddle tLast fixStr

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem p44b (g : G) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hB : bcut g 1 22 LA true 23 (appStr (appStr (appStr (appStr (appStr (appStr [] 75 (tFirst g)
      (some (JStr.ofString " "))) 75 (JStr.ofString " ") none) 75 (tMiddle g) (some (JStr.ofString " "))) 75
      (JStr.ofString " ") none) 75 (tLast g) (some (JStr.ofString " "))) 75 (JStr.ofString " ") none) args σ0 fr σ) :
    bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) 20 52 fr σ := by
  rw [bcut_unfold] at hB
  have hK : Kept (CutI g 1 22 (LA g) true σ0 fr σ) := Kept.intro hB.1
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
    exact locsAt_sub (L := (15, tStName g) :: LA g) (by simp [LB, LA])
      ⟨⟨w, by simp [Frame.get_setLocal], heap_str_eq (by assumption) (nm_eq g),
        by simp only [tStName, stNameT, fixStr_length]; omega⟩,
       locsAt_frame (by grows_tac) hI.2.1 (by simp [LA, Frame.get_setLocal])⟩

end EquivLean.Modernize.Cbstm03a.Java.Cs

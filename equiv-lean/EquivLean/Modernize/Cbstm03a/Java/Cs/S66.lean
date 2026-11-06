import EquivLean.Modernize.Cbstm03a.Java.Cs.Entry
import EquivLean.Modernize.Cbstm03a.Java.Cs.Num

/-!
# CBSTM03A → Java: `createStatement`, the paths from the cut point 66 to 71

`stAcctId`, `stCurrBal` (`fmtCurrBal` of `currBal`), `stFico`, `l23Name` (the first 50 characters of the name
line) and the first `para` line.
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans fixStr_length heap_grows)

attribute [-simp] List.reduceReplicate
attribute [local simp high] EquivLean.Modernize.Cbstm03a.Java.Cs.take_eq_takeK
attribute [local simp] EquivLean.Modernize.Cbstm03a.Java.Cs.length_takeK

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

theorem heapG {σ σ' : State} {x : Addr} {o : Obj} (h : σ.heap x = some o) (hg : Grows σ σ') :
    σ'.heap x = some o := heap_grows hg h

theorem sub_a_len {g : G} (h : 24 ≤ g.a.length) : (sub g.a 12 24).length = 12 := by
  unfold sub
  simp only [List.length_drop, List.length_take]
  omega

theorem stCurrBal_eq {g : G} (h : 24 ≤ g.a.length) :
    currStr (BitVec.ofInt 64 (zonedVal (sub g.a 12 24))).toInt = tStCurrBal g := by
  rw [toInt_ofInt_zoned (sub_a_len h), currStr_eq, zonedVal_eq]
  rfl

/-- The live locals at the virtual cut points 67 … 70. -/
def L67 (g : G) : List (Nat × JStr) := (17, tStAcctId g) :: LC g
def L68 (g : G) : List (Nat × JStr) := (18, tStCurrBal g) :: L67 g
def L69 (g : G) : List (Nat × JStr) := (19, tStFico g) :: L68 g
def L70 (g : G) : List (Nat × JStr) := (20, sub (tStName g) 0 50) :: L69 g

attribute [local irreducible] tStName tAcctId tFico tStAdd3 tAddr1 tAddr2 fixStr
attribute [local irreducible] currStr zonedVal
attribute [-simp] BitVec.toInt_ofInt

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem q66 (g : G) (args : List Value) (σ0 : State) (hpre : (specG g).pre args σ0) (fr : Frame) (σ : State)
    (hI : cut g 1 22 LC true args σ0 fr σ) :
    bodyWP Gen.prog csH body ((67, cut g 1 22 L67 true args σ0) :: (inv g).inst args σ0)
      ((specG g).post args σ0) 5 66 fr σ := by
  have ha1 := hpre.2.2.2.2.2.2.1
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 22 (LC g) true σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (LC g) := hI.2.1
  obtain ⟨x13, h13a, h13b, h13c⟩ := locsAt_mem hL (p := (13, tAcctId g)) (by simp [LC, L69, L68, L67, LC])
  clear hI hL hpre
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, fixSpecI, fmtCurrBalSpec, paraSpec, StrOk, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_
      (fun h => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, heap_str_eq (by assumption) (by simp only [tStAcctId, tAcctId]), by simp only [tStAcctId, fixStr_length]; omega⟩,
      locsAt_frame (by grows_tac) hI.2.1 (by simp [LC, L69, L68, L67, LC, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem q67 (g : G) (args : List Value) (σ0 : State) (hpre : (specG g).pre args σ0) (fr : Frame) (σ : State)
    (hI : cut g 1 22 L67 true args σ0 fr σ) :
    bodyWP Gen.prog csH body ((68, cut g 1 22 L68 false args σ0) :: (inv g).inst args σ0)
      ((specG g).post args σ0) 5 67 fr σ := by
  have ha1 := hpre.2.2.2.2.2.2.1
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 22 (L67 g) true σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (L67 g) := hI.2.1
  have hz : -9223372036854775808 < (BitVec.ofInt 64 (zonedVal (sub g.a 12 24))).toInt := by
    rw [toInt_ofInt_zoned (sub_a_len ha1)]
    have := zonedVal_natAbs_lt (sub g.a 12 24)
    rw [sub_a_len ha1, show (10 : Nat) ^ 12 = 1000000000000 from rfl] at this
    omega
  have hb0 : fr.get 0 = some (.long (BitVec.ofInt 64 (zonedVal (sub g.a 12 24)))) := hI.2.2 rfl
  clear hI hL hpre
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, fixSpecI, fmtCurrBalSpec, paraSpec, StrOk, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_
      (fun h => by cases h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, heap_str_eq (by assumption) (stCurrBal_eq ha1), by simp only [tStCurrBal, fmtCurrBalI, List.length_append, EquivLean.Modernize.Cbstm03b.Java.zpadStr_length, List.length_cons, List.length_nil]; omega⟩,
      locsAt_frame (by grows_tac) hI.2.1 (by simp [L67, L69, L68, L67, LC, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem q68 (g : G) (args : List Value) (σ0 : State) (hpre : (specG g).pre args σ0) (fr : Frame) (σ : State)
    (hI : cut g 1 22 L68 false args σ0 fr σ) :
    bodyWP Gen.prog csH body ((69, cut g 1 22 L69 false args σ0) :: (inv g).inst args σ0)
      ((specG g).post args σ0) 5 68 fr σ := by
  have ha1 := hpre.2.2.2.2.2.2.1
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 22 (L68 g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (L68 g) := hI.2.1
  obtain ⟨x12, h12a, h12b, h12c⟩ := locsAt_mem hL (p := (12, tFico g)) (by simp [L68, L69, L68, L67, LC])
  clear hI hL hpre
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, fixSpecI, fmtCurrBalSpec, paraSpec, StrOk, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_
      (fun h => by cases h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, heap_str_eq (by assumption) (by simp only [tStFico, tFico]), by simp only [tStFico, fixStr_length]; omega⟩,
      locsAt_frame (by grows_tac) hI.2.1 (by simp [L68, L69, L68, L67, LC, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem q69 (g : G) (args : List Value) (σ0 : State) (hpre : (specG g).pre args σ0) (fr : Frame) (σ : State)
    (hI : cut g 1 22 L69 false args σ0 fr σ) :
    bodyWP Gen.prog csH body ((70, cut g 1 22 L70 false args σ0) :: (inv g).inst args σ0)
      ((specG g).post args σ0) 5 69 fr σ := by
  have ha1 := hpre.2.2.2.2.2.2.1
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 22 (L69 g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (L69 g) := hI.2.1
  obtain ⟨x15, h15a, h15b, h15c⟩ := locsAt_mem hL (p := (15, tStName g)) (by simp [L69, L69, L68, L67, LC])
  have hl15 : (tStName g).length = 75 := by unfold tStName stNameT; simp only [fixStr_length]
  clear hI hL hpre
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, fixSpecI, fmtCurrBalSpec, paraSpec, StrOk, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) rfl rfl ?_
      (fun h => by cases h)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte, sub, take_eq_takeK, List.drop_zero] <;> rfl, by have := sub_length_le (tStName g) 0 50; omega⟩,
      locsAt_frame (by grows_tac) hI.2.1 (by simp [L69, L69, L68, L67, LC, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem q70 (g : G) (args : List Value) (σ0 : State) (hpre : (specG g).pre args σ0) (fr : Frame) (σ : State)
    (hI : cut g 1 22 L70 false args σ0 fr σ) :
    bodyWP Gen.prog csH body ((inv g).inst args σ0)
      ((specG g).post args σ0) 5 70 fr σ := by
  have ha1 := hpre.2.2.2.2.2.2.1
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 1 22 (L70 g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (L70 g) := hI.2.1
  obtain ⟨x20, h20a, h20b, h20c⟩ := locsAt_mem hL (p := (20, sub (tStName g) 0 50)) (by simp [L70, L69, L68, L67, LC])
  clear hI hL hpre
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, fixSpecI, fmtCurrBalSpec, paraSpec, StrOk, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_
      (fun h => by cases h)
    exact locsAt_sub (L := (13, tPara1 g) :: LD g) (by simp [LD71, LD, LD, L69, L68, L67, LC])
      ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, heap_str_eq (by assumption) (by rw [paraStr_eq]; simp only [tPara1, tStName, sub, take_eq_takeK, List.drop_zero]), by simp only [tPara1, paraT, fixStr_length]; omega⟩,
       locsAt_frame (by grows_tac) (locsAt_sub (by simp [LD, L70, L69, L68, L67, LC]) hI.2.1)
        (by simp [LD, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
theorem s66 (g : G) : CutVC g 66 1 22 LC true := by
  intro args σ0 hpre fr σ hI
  unfold wp
  have h70 : ∀ fr σ, cut g 1 22 L70 false args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) 40 70 fr σ :=
    fun fr σ h => bodyWP_fuel_le csH_mono body _ _ (by decide : 5 ≤ 40) 70 fr σ (q70 g args σ0 hpre fr σ h)
  have h69 : ∀ fr σ, cut g 1 22 L69 false args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 40) 69 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 70 rfl _ 40 h70 5 69 fr σ (q69 g args σ0 hpre fr σ h)
  have h68 : ∀ fr σ, cut g 1 22 L68 false args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 45) 68 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 69 rfl _ 45 h69 5 68 fr σ (q68 g args σ0 hpre fr σ h)
  have h67 : ∀ fr σ, cut g 1 22 L67 true args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 50) 67 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 68 rfl _ 50 h68 5 67 fr σ (q67 g args σ0 hpre fr σ h)
  exact bodyWP_cut_insert csH_mono body _ _ 67 rfl _ 55 h67 5 66 fr σ (q66 g args σ0 hpre fr σ hI)

end EquivLean.Modernize.Cbstm03a.Java.Cs

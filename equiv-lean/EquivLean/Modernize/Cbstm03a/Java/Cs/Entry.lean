import EquivLean.Modernize.Cbstm03a.Java.Cs.VCut

/-!
# CBSTM03A → Java: `createStatement`, the entry path

From the entry to the cut point before the first statement line, in three parts with virtual cut points at 13
(the substrings of the customer text done) and 16 (`acctId`, `currBal` done): the parameters, the substrings
of the customer and account texts, `currBal` (`decodeZoned`), and the first line (`repeat`, concatenation).
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space Kept GrowsK grows_split
  growsK_elim grows_refl grows_trans keeps_refl keeps_trans fixStr_length heap_grows)

attribute [-simp] List.reduceReplicate

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

/-- `List.take`, folded: the substrings stay `takeK` terms in the symbolic run (not lists of elements). -/
@[irreducible] def takeK (n : Nat) (l : JStr) : JStr := l.take n

theorem take_eq_takeK (n : Nat) (l : JStr) : l.take n = takeK n l := by unfold takeK; rfl

theorem length_takeK (n : Nat) (l : JStr) : (takeK n l).length = min n l.length := by unfold takeK; simp

end EquivLean.Modernize.Cbstm03a.Java.Cs

attribute [local simp high] EquivLean.Modernize.Cbstm03a.Java.Cs.take_eq_takeK
attribute [local simp] EquivLean.Modernize.Cbstm03a.Java.Cs.length_takeK

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

/-- `Grows σ0 σ` for a state built from `σ0` by allocations and callees (`GrowsK`); reflexivity last. -/
macro "grows_tac2" : tactic => `(tactic| repeat (first | refine grows_al ?_ | refine grows_k ?_ (by assumption) | exact grows_refl _))

/-- The substrings of the customer text (locals 3 … 12). -/
def LS (g : G) : List (Nat × JStr) :=
  [(3, tFirst g), (4, tMiddle g), (5, tLast g), (6, tAddr1 g), (7, tAddr2 g), (8, tAddr3 g), (9, tState g),
   (10, tCountry g), (11, tZip g), (12, tFico g)]

/-- The live locals at the virtual cut point 13: the account text and the substrings of the customer text. -/
def L13 (g : G) : List (Nat × JStr) := (2, g.a) :: LS g

theorem cutI_entry {g : G} {L : List (Nat × JStr)} {bal : Bool} {σ0 σ : State} {fr : Frame}
    (hR : ResAtL σ0 g.res g.ld g.ls g.lh g.disp g.st g.ht g.ab) (hg : Grows σ0 σ)
    (h22 : fr.get 22 = some (.ref g.res)) (hin : σ.inits = σ0.inits) (hst : σ.statics = σ0.statics)
    (hini : σ0.initOf "Cbstm03a" = .done) (hL : LocsAt σ fr L)
    (hb : bal = true → fr.get 0 = some (.long (BitVec.ofInt 64 (zonedVal (sub g.a 12 24))))) :
    CutI g 0 0 L bal σ0 fr σ := by
  refine ⟨⟨h22, ?_, keepsRes_of_grows hg, hin, hst, ?_⟩, hL, hb⟩
  · simp only [List.take_zero, List.append_nil]
    exact resAtL_grows hR hg
  · unfold State.initOf at hini ⊢
    rw [hin]
    exact hini

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem entA (g : G) (args : List Value) (σ0 : State) (hpre : (specG g).pre args σ0) :
    bodyWP Gen.prog csH body ((13, cut g 0 0 L13 false args σ0) :: (inv g).inst args σ0) ((specG g).post args σ0)
      20 0 (Frame.init true args) σ0 := by
  have hK : Kept (ResAtL σ0 g.res g.ld g.ls g.lh g.disp g.st g.ht g.ab) := Kept.intro hpre.2.1
  have h0 := hpre.1
  have hxc := hpre.2.2.1
  have hxa := hpre.2.2.2.1
  have hc1 := hpre.2.2.2.2.1
  have hc2 := hpre.2.2.2.2.2.1
  have ha1 := hpre.2.2.2.2.2.2.1
  have ha2 := hpre.2.2.2.2.2.2.2.1
  have hini := hpre.2.2.2.2.2.2.2.2
  clear hpre
  subst h0
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, decodeZonedSpec, repeatSpec, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    refine cutI_entry (Kept.elim hK) (by grows_tac2) (by simp [Frame.get_setLocal]) rfl rfl hini ?_ (fun h => by cases h)
    exact ⟨⟨g.xa, by simp [Frame.get_setLocal], heap_grows (by grows_tac2) hxa, ha2⟩,
        ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by hsimpK <;> simp only [tFirst, sub, take_eq_takeK],
          by have := sub_length_le g.c 9 34; simp only [tFirst]; omega⟩
        ,
        ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by hsimpK <;> simp only [tMiddle, sub, take_eq_takeK],
          by have := sub_length_le g.c 34 59; simp only [tMiddle]; omega⟩
        ,
        ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by hsimpK <;> simp only [tLast, sub, take_eq_takeK],
          by have := sub_length_le g.c 59 84; simp only [tLast]; omega⟩
        ,
        ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by hsimpK <;> simp only [tAddr1, sub, take_eq_takeK],
          by have := sub_length_le g.c 84 134; simp only [tAddr1]; omega⟩
        ,
        ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by hsimpK <;> simp only [tAddr2, sub, take_eq_takeK],
          by have := sub_length_le g.c 134 184; simp only [tAddr2]; omega⟩
        ,
        ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by hsimpK <;> simp only [tAddr3, sub, take_eq_takeK],
          by have := sub_length_le g.c 184 234; simp only [tAddr3]; omega⟩
        ,
        ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by hsimpK <;> simp only [tState, sub, take_eq_takeK],
          by have := sub_length_le g.c 234 236; simp only [tState]; omega⟩
        ,
        ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by hsimpK <;> simp only [tCountry, sub, take_eq_takeK],
          by have := sub_length_le g.c 236 239; simp only [tCountry]; omega⟩
        ,
        ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by hsimpK <;> simp only [tZip, sub, take_eq_takeK],
          by have := sub_length_le g.c 239 249; simp only [tZip]; omega⟩
        ,
        ⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl, by hsimpK <;> simp only [tFico, sub, take_eq_takeK],
          by have := sub_length_le g.c 329 332; simp only [tFico]; omega⟩
        , trivial⟩

end EquivLean.Modernize.Cbstm03a.Java.Cs
namespace EquivLean.Modernize.Cbstm03a.Java.Cs

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem entB (g : G) (args : List Value) (σ0 : State) (hpre : (specG g).pre args σ0) (fr : Frame) (σ : State)
    (hI : cut g 0 0 L13 false args σ0 fr σ) :
    bodyWP Gen.prog csH body ((16, cut g 0 0 LA true args σ0) :: (inv g).inst args σ0) ((specG g).post args σ0)
      20 13 fr σ := by
  have ha1 := hpre.2.2.2.2.2.2.1
  clear hpre
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 0 0 (L13 g) false σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  have hL : LocsAt σ fr (L13 g) := hI.2.1
  obtain ⟨x2, h2a, h2b, h2c⟩ := hL.1
  clear hI hL
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, decodeZonedSpec, repeatSpec, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac2) (by simp [Frame.get_setLocal]) rfl rfl ?_
      (fun _ => by simp only [Frame.get_setLocal, ↓reduceIte, sub, take_eq_takeK])
    exact locsAt_sub (L := (13, tAcctId g) :: LS g) (by simp [LA, LS])
      ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
        by hsimpK <;> simp only [tAcctId, sub, take_eq_takeK, List.drop_zero],
        by have := sub_length_le g.a 0 11; simp only [tAcctId]; omega⟩,
       locsAt_frame (by grows_tac2) hI.2.1.2 (by simp [LS, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
set_option jimple.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem entC (g : G) (args : List Value) (σ0 : State) (fr : Frame) (σ : State)
    (hI : cut g 0 0 LA true args σ0 fr σ) :
    bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) 20 16 fr σ := by
  rw [cut_unfold] at hI
  have hK : Kept (CutI g 0 0 (LA g) true σ0 fr σ) := Kept.intro hI
  have hres := hI.1.1
  have hini := hI.1.2.2.2.2.2
  clear hI
  jvc [inv, csCallees, stmtSig, htmlSig, fixSig, spacesSig, repeatSig, appSig, paraSig, starSig, fmtCurrBalSig,
    decodeZonedSig, decodeZonedSpec, repeatSpec, StrNN, grows_split, argText, strOf]
  all_goals
    rw [cut_unfold]
    have hI := Kept.elim hK
    refine cutI_next hI (by grows_tac2) (by simp [Frame.get_setLocal]) (by assumption) (by assumption) ?_
      (fun _ => by simp only [Frame.get_setLocal, ↓reduceIte]; exact hI.2.2 rfl)
    exact ⟨⟨_, by simp only [Frame.get_setLocal, ↓reduceIte] <;> rfl,
      by simp only [State.heap_alloc, State.next_alloc, ↓reduceIte] <;> rfl,
      by decide +kernel⟩,
      locsAt_frame (by grows_tac2) hI.2.1 (by simp [LA, Frame.get_setLocal])⟩

set_option maxRecDepth 20000 in
/-- The entry path, from the parts with the virtual cut points 13 and 16. -/
theorem entry_vc (g : G) : EntryVC g := by
  intro args σ0 hpre
  unfold wp
  exact bodyWP_cut_insert csH_mono body _ _ 13 rfl (cut g 0 0 L13 false args σ0) 40
    (fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 16 rfl (cut g 0 0 LA true args σ0) 20
      (fun fr σ h => entC g args σ0 fr σ h) 20 13 fr σ (entB g args σ0 hpre fr σ h))
    20 0 _ σ0 (entA g args σ0 hpre)

end EquivLean.Modernize.Cbstm03a.Java.Cs

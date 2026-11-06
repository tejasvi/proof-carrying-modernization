import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunX
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL5

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem keysOf_tcat' : keysOf TranCatBalRecord tcCls = tcKeys := by decide

theorem toNat_zero32'' : (0#32 : BitVec 32).toInt.toNat = 0 := by decide

theorem initOf_of_inits3 {σ σ0 : State} (h : σ.inits = σ0.inits) (c : ClassName) :
    σ.initOf c = σ0.initOf c := by
  simp only [State.initOf, h]

theorem allSome_of_jrec' {s : Schema} {cls : ClassName} {σ : State} {a : Addr}
    {vals : List EquivLean.Cobol.Rec.FVal} {fs : List (FieldKey × Value)}
    (h : JRecAt s cls σ (.ref a) vals) (ha : σ.heap a = some (.plain cls fs)) :
    AllSome (keysOf s cls) fs := by
  intro k hk
  simp only [keysOf, List.mem_map] at hk
  obtain ⟨f, hf, rfl⟩ := hk
  exact jrecAt_isSome h ha f hf

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
set_option pp.maxSteps 3000 in
set_option pp.deepTerms false in
theorem run_seg22 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreGX g g.args σ0) (h : J22 g g.args σ0 fr σ)
    (c23 : cuts.lookup 23 = none) (c24 : cuts.lookup 24 = none) (c25 : cuts.lookup 25 = none)
    (c26 : cuts.lookup 26 = none) (c27 : cuts.lookup 27 = none) (c28 : cuts.lookup 28 = none)
    (c29 : cuts.lookup 29 = none) (c30 : cuts.lookup 30 = none) (c31 : cuts.lookup 31 = none)
    (c32 : cuts.lookup 32 = none) (c33 : cuts.lookup 33 = none) (c34 : cuts.lookup 34 = none)
    (c22 : cuts.lookup 22 = some (J22 g g.args σ0)) (c35 : cuts.lookup 35 = some (J35 g g.args σ0)) :
    RunWPcX g σ0 cuts 22 fr σ := by
  obtain ⟨-, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨b1, b2, b3, b4, b5, hargs, -, -, -, ⟨et4, xs4, h4, hl4, hf4⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨i, c, f32, f0, f2, f16, f31, f8, f11, f15, hi0, hil, hH, hnext, hg, hinits, hstat, hinit⟩ := h
  have hg' := Hide.intro hg
  have hlen4 := forall2_length hf4
  have h4' := heap_of_grows hg h4
  obtain ⟨hR, hL, hTab, ⟨xs, m, hc, hF, hB⟩, hc9⟩ := Hide.elim hH
  have hR' := Hide.intro hR
  have hL' := Hide.intro hL
  have hTab' := Hide.intro hTab
  have hF' := Hide.intro hF
  have hB' := Hide.intro hB
  have hclt : c < σ.next := State.lt_next_of_heap hc
  clear hR hL hTab hB hH
  by_cases hcnd : (g.cats.length : Int) ≤ i.toInt
  · -- the list complete: `lK`, `xrefWs` (statements 29–34)
    have hiE : i.toInt.toNat = g.cats.length := by omega
    have hiX : σ.initOf "Cbtrn02c$CardXrefRecord" = .done := by rw [initOf_of_inits3 hinits]; exact i4
    clear hf4 hF hg
    unfold RunWPcX
    jvc [runCX, inlineFuel, G.args, Grows, spacesSigT, spacesSpec, ctorXRSig, ctorXRSpec,
      fields_get_cons, fields_get_nil]
    rename_i σA hX _
    obtain ⟨hX1, hX2, hX3, hX4, hX5, -⟩ := hX (σ.next + 1) _ _ _ _ _ rfl rfl rfl rfl rfl (by chain_simp)
    have hgA : Grows σ σA := by grows_tac
    refine ⟨c, σ.next, σ.next + 1, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_,
      Hide.intro ⟨⟨(Hide.elim hR').grows hgA, (Hide.elim hL').grows hgA,
        (tabDone_of_init (Hide.elim hTab')).grows hgA,
        (catDone_of ⟨xs, m, hc, by rw [← hiE]; exact Hide.elim hF', Hide.elim hB'⟩).grows hgA,
        ⟨0, by chain_simp⟩, hc9, hclt⟩,
        wsobj_of_setFields hX1 (by decide) (by simp)⟩,
      Nat.lt_succ_self _, grows_trans (Hide.elim hg') hgA, hX4, hX5, ?_⟩
    any_goals (frame_simp [f32, f0, f16, f31, f8, f11]; done)
    rw [initOf_of_inits3 hX4]
  · -- one more category record copied
    have hn : i.toInt.toNat < xs4.length := by omega
    have hrec := forall2_get hf4 _ hn (by omega)
    obtain ⟨y, fs, hy, hyh, -⟩ := id hrec
    rw [hy] at hrec
    have hall : AllSome tcKeys fs := by
      rw [← keysOf_tcat']; exact allSome_of_jrec' hrec hyh
    have hget : xs4[i.toInt.toNat]? = some (.ref y) := by
      rw [List.getElem?_eq_getElem hn, hy]
    have hyh' := heap_of_grows hg hyh
    have hrec' := Hide.intro hrec
    have hiT : σ.initOf "Cbtrn02c$TranCatBalRecord" = .done := by rw [initOf_of_inits3 hinits]; exact i6
    clear hf4 hF hrec hg
    unfold RunWPcX
    jvc [runCX, inlineFuel, G.args, Grows, copyTcatSigT, copyTcatSpecF]
    rename_i σ1 x hxn hxh hsame hn1 hfr1 hin1 _ _ _
    have hg1 : Grows σ σ1 := ⟨hn1, hfr1⟩
    rw [fieldsOf_of hyh', ← keysOf_tcat'] at hsame
    have hlt : i.toInt < 2147483647 := by omega
    have hidx := toNat_succ32 hi0 hlt
    have hgy := jrecAt_grows (Hide.elim hrec') (Hide.elim hg')
    have hc1 : σ1.heap c = σ.heap c := hfr1 c hclt
    have hnp : ∀ c' fs, σ1.heap c ≠ some (.plain c' fs) := by intro c' fs h; rw [hc1, hc] at h; cases h
    have hns : ∀ t, σ1.heap c ≠ some (.str t) := by intro t h; rw [hc1, hc] at h; cases h
    refine ⟨i + 1#32, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Hide.intro ⟨((Hide.elim hR').grows hg1).setObj8 (by jomega),
        ((Hide.elim hL').grows hg1).setObj8 (by jomega),
        ((Hide.elim hTab').grows hg1).setObj_list hc9 hnp hns, ?_, hc9⟩, ?_,
      grows_setObj' (grows_trans (Hide.elim hg') hg1) (by jomega) _, ?_, ?_, ?_⟩
    any_goals (frame_simp [f32, f0, f2, f16, f31, f8, f11]; done)
    · rw [toInt_succ32 hi0 hlt]; omega
    · rw [toInt_succ32 hi0 hlt]; omega
    · rw [hidx]
      exact catList_step (by omega) hc (Hide.elim hF') (Hide.elim hB') hgy hyh' hxh hsame hxn hnext hg1
    · simp only [State.next_setObj]; jomega
    · cls_simp; rw [hin1]
    · cls_simp; rw [‹σ1.statics = σ0.statics›]
    · cls_simp; rw [‹σ1.initOf "Cbtrn02c" = InitSt.done›, i1]

end EquivLean.Modernize.Cbtrn02c.Java

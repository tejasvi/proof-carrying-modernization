import EquivLean.Modernize.Cbtrn02c.Any.JavaRunRunX
import EquivLean.Modernize.Cbtrn02c.Any.JavaRunPL5

open Jimple EquivLean.Cobol.Rec

namespace EquivLean.Modernize.Cbtrn02c.Java

theorem keysOf_acct' : keysOf AccountRecord acCls = acKeys := by decide

theorem toNat_zero32' : (0#32 : BitVec 32).toInt.toNat = 0 := by decide

theorem allSome_of_jrec {s : Schema} {cls : ClassName} {σ : State} {a : Addr}
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
theorem run_seg12 (g : G) (σ0 : State) (fr : Frame) (σ : State) (cuts : Cuts)
    (hpre : RunPreGX g g.args σ0) (h : J12 g g.args σ0 fr σ)
    (c13 : cuts.lookup 13 = none) (c14 : cuts.lookup 14 = none) (c15 : cuts.lookup 15 = none)
    (c16 : cuts.lookup 16 = none) (c17 : cuts.lookup 17 = none) (c18 : cuts.lookup 18 = none)
    (c19 : cuts.lookup 19 = none) (c20 : cuts.lookup 20 = none) (c21 : cuts.lookup 21 = none)
    (c12 : cuts.lookup 12 = some (J12 g g.args σ0)) (c22 : cuts.lookup 22 = some (J22 g g.args σ0)) :
    RunWPcX g σ0 cuts 12 fr σ := by
  obtain ⟨-, hin, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hpre
  obtain ⟨b1, b2, b3, b4, b5, hargs, -, -, ⟨et3, xs3, h3, hl3, hf3⟩, -⟩ := hin
  simp only [G.args, List.cons.injEq, Value.ref.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs
  obtain ⟨i, f32, f0, f7, f2, f16, f31, f8, f15, hi0, hil, hH, hnext, hg, hinits, hstat, hinit⟩ := h
  have hg' := Hide.intro hg
  have hlen3 := forall2_length hf3
  have h3' := heap_of_grows hg h3
  obtain ⟨hR, hL, ys, hT, hF, hB⟩ := Hide.elim hH
  have hR' := Hide.intro hR
  have hL' := Hide.intro hL
  have hF' := Hide.intro hF
  have hB' := Hide.intro hB
  have hys : ys.length = i.toInt.toNat := by
    rw [forall2_length hF, List.length_take]; omega
  have hiA : σ.initOf "Cbtrn02c$AccountRecord" = .done := by
    rw [show σ.initOf "Cbtrn02c$AccountRecord" = σ0.initOf "Cbtrn02c$AccountRecord" by
      simp only [State.initOf, hinits]]
    exact i3
  clear hR hL hB
  by_cases hc : (g.accts.length : Int) ≤ i.toInt
  · clear hf3 hF
    have hiE : i.toInt.toNat = g.accts.length := by omega
    clear hg
    unfold RunWPcX
    jvc [runCX, inlineFuel, G.args, Grows]
    have hg1 : Grows σ ((σ.alloc (Obj.plain "java.util.ArrayList" [])).snd.setObj σ.next
        (Obj.list ListKind.arrayList [] 0)) :=
      grows_setObj' (grows_alloc' (grows_refl σ) _) (Nat.le_refl _) _
    refine ⟨0#32, σ.next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, by simp,
      Hide.intro ⟨(Hide.elim hR').grows hg1, (Hide.elim hL').grows hg1, ?_,
        ⟨[], 0, by chain_simp, by rw [toNat_zero32', List.take_zero]; exact .nil, by simp⟩, hnext⟩,
      ?_, grows_trans (Hide.elim hg') hg1, ?_, ?_, ?_⟩
    any_goals (frame_simp [f32, f0, f2, f16, f31, f8]; done)
    · rw [← hiE]; exact (TabInit.grows ⟨ys, hT, Hide.elim hF', Hide.elim hB'⟩ hg1)
    · simp only [State.next_alloc, State.next_setObj]; jomega
    · cls_simp; exact hinits
    · cls_simp; exact hstat
    · cls_simp; exact hinit
  · have hn : i.toInt.toNat < xs3.length := by omega
    have hrec := forall2_get hf3 _ hn (by omega)
    obtain ⟨y, fs, hy, hyh, -⟩ := id hrec
    rw [hy] at hrec
    have hall : AllSome acKeys fs := by
      rw [← keysOf_acct']; exact allSome_of_jrec hrec hyh
    have hget : xs3[i.toInt.toNat]? = some (.ref y) := by
      rw [List.getElem?_eq_getElem hn, hy]
    have hyh' := heap_of_grows hg hyh
    have hrec' := Hide.intro hrec
    clear hf3 hF hrec
    clear hg
    unfold RunWPcX
    jvc [runCX, inlineFuel, G.args, Grows, copyAccountSigT, copyAccountSpecF]
    rename_i σ1 x hxn hxh hsame hn1 hfr1 hin1 _ _ _ _ _
    have hg1 : Grows σ σ1 := ⟨hn1, hfr1⟩
    rw [fieldsOf_of hyh', ← keysOf_acct'] at hsame
    have hlt : i.toInt < 2147483647 := by omega
    have hidx := toNat_succ32 hi0 hlt
    have hgy : JRecAt AccountRecord acCls σ (.ref y) g.accts[i.toInt.toNat] :=
      jrecAt_grows (Hide.elim hrec') (Hide.elim hg')
    refine ⟨i + 1#32, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Hide.intro ⟨((Hide.elim hR').grows hg1).setObj8 (Nat.le_refl _),
        ((Hide.elim hL').grows hg1).setObj8 (Nat.le_refl _), ?_⟩, ?_,
      grows_setObj' (grows_trans (Hide.elim hg') hg1) (by jomega) _, ?_, ?_, ?_⟩
    any_goals (frame_simp [f32, f0, f7, f2, f16, f31, f8]; done)
    · rw [toInt_succ32 hi0 hlt]; omega
    · rw [toInt_succ32 hi0 hlt]; omega
    · rw [hidx]
      exact tabInit_step2 (by omega) hys hT (Hide.elim hF') (Hide.elim hB') hgy hyh' hxh hsame hxn hnext hg1
    · simp only [State.next_setObj]; jomega
    · cls_simp; rw [hin1]
    · cls_simp; rw [‹σ1.statics = σ0.statics›]
    · cls_simp; rw [‹σ1.initOf "Cbtrn02c" = InitSt.done›, i1]

end EquivLean.Modernize.Cbtrn02c.Java

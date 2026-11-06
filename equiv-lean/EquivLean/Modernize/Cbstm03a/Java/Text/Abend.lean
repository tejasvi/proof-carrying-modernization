import EquivLean.Modernize.Cbstm03a.Java.Text.Lib2

/-!
# CBSTM03A → Java: `abend`

Verified for every fixed choice of ghost values (`abendSpecG`; no callees), then its contract of `Iface3`.
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space Kept GrowsK grows_split Keeps
  keeps_refl keeps_trans keeps_setObj keeps_alloc keeps_of_grows keeps_setObj' keeps_alloc' keeps_grows'
  growsK_elim)

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

attribute [-simp] List.reduceReplicate

theorem forall2_append {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β} {c : List α} {d : List β}, Forall2 R a b → Forall2 R c d → Forall2 R (a ++ c) (b ++ d)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h1 h2, h => .cons h1 (forall2_append h2 h)

def abendSpecG (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (mv rv : Value) (m c : JStr) :
    Spec := Spec.of
  (fun args σ => args = [.ref res, mv, rv] ∧ ResAtL σ res ld ls lh disp st ht ab ∧ JStrAt σ mv m ∧
     JStrAt σ rv c ∧ σ.initOf "Cbstm03a" = .done)
  (fun _ σ r σ' => r = some (.ref res) ∧
     ResAtL σ' res ld ls lh (disp ++ [argText σ mv, jl "RETURN CODE: " ++ argText σ rv, jl "ABENDING PROGRAM"])
       st ht true ∧
     KeepsRes res ld ls lh σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

theorem rc_text (c : JStr) : JStr.ofString "RETURN CODE: " ++ c =
    82#16 :: 69#16 :: 84#16 :: 85#16 :: 82#16 :: 78#16 :: 32#16 :: 67#16 :: 79#16 :: 68#16 :: 69#16 :: 58#16 ::
      32#16 :: c := by
  rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem abend_vc (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (mv rv : Value) (m c : JStr) :
    MethodVC Gen.prog (fun _ => none) 0 abendRef (abendSpecG res ld ls lh disp st ht ab mv rv m c) [] 60 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩⟩
  obtain ⟨h0, hR, ⟨xm, hmv, hxm⟩, ⟨xr, hrv, hxr⟩, hI⟩ := hpre
  have hK : Kept (ResAtL σ0 res ld ls lh disp st ht ab) := Kept.intro hR
  obtain ⟨fs, hres, gd, gs, gh, gab, n1, n2, n3, ⟨xd, md, hld, -⟩, -, -⟩ := hR
  simp only [abendSpecG, Spec.of]
  jvc [ite_nat_ne]
  all_goals have hR := Kept.elim hK
  all_goals have hxml := State.lt_next_of_heap hxm
  all_goals have hxrl := State.lt_next_of_heap hxr
  all_goals have hrl := State.lt_next_of_heap hres
  all_goals have hldl := State.lt_next_of_heap hld
  · obtain ⟨fs0, hres0, -, -, -, -, -, -, -, ⟨xd0, md0, hld0, fd⟩, Ls, Lh⟩ := hR
    rw [hres] at hres0
    obtain ⟨⟩ := hres0
    rw [hld] at hld0
    obtain ⟨⟩ := hld0
    have hS : ∀ y s, σ0.heap y = some (.str s) → ¬ In2 res ld y := not_in2_of_str hres hld
    have hlsr : ls ≠ res := ne_of_heap (listAt_heap Ls).choose_spec.choose_spec hres (by intro h; cases h)
    have hlhr : lh ≠ res := ne_of_heap (listAt_heap Lh).choose_spec.choose_spec hres (by intro h; cases h)
    refine resAtL_of (fs' := Fields.set fs ("Cbstm03a$Result", "abended") (Value.int 1#32)) (Kept.elim hK) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · hsimp
    · simp only [Fields.get_set]; simpa using gd
    · simp only [Fields.get_set]; simpa using gs
    · simp only [Fields.get_set]; simpa using gh
    · simp only [Fields.get_set]; simp
    · refine ⟨xd ++ [.ref xm, .ref (σ0.next + 1), .ref (σ0.next + 1 + 1)], md + 1 + 1 + 1, ?_, forall2_append (forall2_jstr_mono (strMono_of_keeps (A := In2 res ld) (by txt_keeps2) hS) fd)
        (.cons ⟨xm, rfl, ?_⟩ (.cons ⟨σ0.next + 1, rfl, ?_⟩ (.cons ⟨σ0.next + 1 + 1, rfl, ?_⟩ .nil)))⟩
      · hsimp
      · hsimp
        simp [argText, strOf, hxm]
      · hsimp
        simp only [argText, strOf, hxr, Option.getD_some, rc_text]
      · hsimp
    · exact listAt_mono Ls (heap_of_keeps (A := In2 res ld) (by txt_keeps2) (listAt_lt Ls)
        (by rintro (e | e); exact hlsr e; exact n1.symm e)) (strMono_of_keeps (A := In2 res ld) (by txt_keeps2) hS)
    · exact listAt_mono Lh (heap_of_keeps (A := In2 res ld) (by txt_keeps2) (listAt_lt Lh)
        (by rintro (e | e); exact hlhr e; exact n2.symm e)) (strMono_of_keeps (A := In2 res ld) (by txt_keeps2) hS)
  · exact keepsRes_of_keeps (keeps_mono inRes_of_in2 (by txt_keeps2))

theorem abend_sat : Sat Gen.prog abendRef abendSpec := by
  intro args σ o hpre hm
  obtain ⟨res, ld, ls, lh, disp, st, ht, ab, mv, rv, m, c, h0, h1, h2, h3, h4⟩ := hpre
  have hG := MethodVC.sat (abend_vc res ld ls lh disp st ht ab mv rv m c) args σ o ⟨h0, h1, h2, h3, h4⟩ hm
  cases o with
  | normal r σ' =>
    intro res' ld' ls' lh' disp' st' ht' ab' mv' rv' g0 g1
    rw [h0] at g0
    obtain ⟨hr, hm', hr'⟩ : res = res' ∧ mv = mv' ∧ rv = rv' := by simpa using g0
    subst hr hm' hr'
    exact MethodVC.sat (abend_vc res ld' ls' lh' disp' st' ht' ab' mv rv m c) args σ (.normal r σ')
      ⟨h0, g1, h2, h3, h4⟩ hm
  | exc e σ' => exact hG.elim
  | wrong msg => exact hG.elim

end EquivLean.Modernize.Cbstm03a.Java.Txt

#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.abend_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.abend_sat

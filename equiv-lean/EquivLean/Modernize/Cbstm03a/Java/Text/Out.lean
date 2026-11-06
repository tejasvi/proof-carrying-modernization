import EquivLean.Modernize.Cbstm03a.Java.Text.Callees

/-!
# CBSTM03A → Java: `stmt` and `html`

Each is verified for every fixed choice of ghost values (`stmtSpecG`, `htmlSpecG`) against `fix`'s contract, then
gives its contract of `Iface3` (`stmt_sat`, `html_sat`, from the validity of the callee table).
-/

set_option jimple.modelContracts true

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows fixStr zpadStr argText StrOk space Kept GrowsK grows_split Keeps
  keeps_refl keeps_trans keeps_setObj keeps_alloc keeps_of_grows keeps_setObj' keeps_alloc' keeps_grows'
  growsK_elim)

namespace EquivLean.Modernize.Cbstm03a.Java.Txt

attribute [-simp] List.reduceReplicate


def stmtSpecG (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (s : Value) : Spec := Spec.of
  (fun args σ => args = [.ref res, s] ∧ ResAtL σ res ld ls lh disp st ht ab ∧ StrOk σ s ∧
     σ.initOf "Cbstm03a" = .done)
  (fun _ σ r σ' => r = none ∧ ResAtL σ' res ld ls lh disp (st ++ [sl (argText σ s)]) ht ab ∧
     KeepsRes res ld ls lh σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

def htmlSpecG (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (s : Value) : Spec := Spec.of
  (fun args σ => args = [.ref res, s] ∧ ResAtL σ res ld ls lh disp st ht ab ∧ StrOk σ s ∧
     σ.initOf "Cbstm03a" = .done)
  (fun _ σ r σ' => r = none ∧ ResAtL σ' res ld ls lh disp st (ht ++ [hl (argText σ s)]) ab ∧
     KeepsRes res ld ls lh σ σ' ∧ σ'.inits = σ.inits ∧ σ'.statics = σ.statics)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem stmt_vc (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (s : Value) :
    MethodVC Gen.prog outCallees.env 0 stmtRef (stmtSpecG res ld ls lh disp st ht ab s) [] 40 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩⟩
  obtain ⟨rfl, hR, hS, hI⟩ := hpre
  have hK : Kept (ResAtL σ0 res ld ls lh disp st ht ab) := Kept.intro hR
  obtain ⟨fs, hres, gd, gs, gh, gab, n1, n2, n3, -, ⟨xs, ms, hls, -⟩, -⟩ := hR
  simp only [stmtSpecG, Spec.of]
  jvc [ite_nat_ne, outCallees, fixSig, fixSpec, grows_split]
  all_goals have hR := Kept.elim hK
  · exact resAtL_push_st hR hls (growsK_elim (by assumption)) (by assumption)
  · exact keepsRes_of_keeps (by txt_keepsR)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem html_vc (res ld ls lh : Addr) (disp st ht : List JStr) (ab : Bool) (s : Value) :
    MethodVC Gen.prog outCallees.env 0 htmlRef (htmlSpecG res ld ls lh disp st ht ab s) [] 40 := by
  refine ⟨_, rfl, fun args σ0 hpre => ⟨?_, fun p hp => by simp [Invariants.inst] at hp⟩⟩
  obtain ⟨rfl, hR, hS, hI⟩ := hpre
  have hK : Kept (ResAtL σ0 res ld ls lh disp st ht ab) := Kept.intro hR
  obtain ⟨fs, hres, gd, gs, gh, gab, n1, n2, n3, -, -, ⟨xh, mh, hlh, -⟩⟩ := hR
  simp only [htmlSpecG, Spec.of]
  jvc [ite_nat_ne, outCallees, fixSig, fixSpec, grows_split]
  all_goals have hR := Kept.elim hK
  · exact resAtL_push_ht hR hlh (growsK_elim (by assumption)) (by assumption)
  · exact keepsRes_of_keeps (by txt_keepsR)

theorem stmt_sat (hV : Valid Gen.prog outCallees.env) : Sat Gen.prog stmtRef stmtSpec := by
  intro args σ o hpre hm
  obtain ⟨res, ld, ls, lh, disp, st, ht, ab, s, h0, h1, h2, h3⟩ := hpre
  have hG := MethodVC.sat_of_valid hV (stmt_vc res ld ls lh disp st ht ab s) args σ o ⟨h0, h1, h2, h3⟩ hm
  cases o with
  | normal r σ' =>
    intro res' ld' ls' lh' disp' st' ht' ab' s' g0 g1
    rw [h0] at g0
    obtain ⟨hr, hs⟩ : res = res' ∧ s = s' := by simpa using g0
    subst hr hs
    exact MethodVC.sat_of_valid hV (stmt_vc res ld' ls' lh' disp' st' ht' ab' s) args σ (.normal r σ')
      ⟨h0, g1, h2, h3⟩ hm
  | exc e σ' => exact hG.elim
  | wrong msg => exact hG.elim

theorem html_sat (hV : Valid Gen.prog outCallees.env) : Sat Gen.prog htmlRef htmlSpec := by
  intro args σ o hpre hm
  obtain ⟨res, ld, ls, lh, disp, st, ht, ab, s, h0, h1, h2, h3⟩ := hpre
  have hG := MethodVC.sat_of_valid hV (html_vc res ld ls lh disp st ht ab s) args σ o ⟨h0, h1, h2, h3⟩ hm
  cases o with
  | normal r σ' =>
    intro res' ld' ls' lh' disp' st' ht' ab' s' g0 g1
    rw [h0] at g0
    obtain ⟨hr, hs⟩ : res = res' ∧ s = s' := by simpa using g0
    subst hr hs
    exact MethodVC.sat_of_valid hV (html_vc res ld' ls' lh' disp' st' ht' ab' s) args σ (.normal r σ')
      ⟨h0, g1, h2, h3⟩ hm
  | exc e σ' => exact hG.elim
  | wrong msg => exact hG.elim

end EquivLean.Modernize.Cbstm03a.Java.Txt

#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.stmt_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.html_vc
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.stmt_sat
#print axioms EquivLean.Modernize.Cbstm03a.Java.Txt.html_sat

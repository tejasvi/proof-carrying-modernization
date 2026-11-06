import EquivLean.Modernize.Cbstm03a.Java.Cs.B44

/-!
# CBSTM03A → Java: `createStatement`, the paths from the cut point 44 to 54 (the name builder)

The virtual cut points 46 … 52 (after `new`/`<init>` and after each `app` call) composed by `bodyWP_cut_insert`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

abbrev nmB1 (g : G) : JStr := appStr [] 75 (tFirst g) (some (JStr.ofString " "))
abbrev nmB2 (g : G) : JStr := appStr (nmB1 g) 75 (JStr.ofString " ") none
abbrev nmB3 (g : G) : JStr := appStr (nmB2 g) 75 (tMiddle g) (some (JStr.ofString " "))
abbrev nmB4 (g : G) : JStr := appStr (nmB3 g) 75 (JStr.ofString " ") none
abbrev nmB5 (g : G) : JStr := appStr (nmB4 g) 75 (tLast g) (some (JStr.ofString " "))

set_option maxRecDepth 20000 in
theorem s44 (g : G) : CutVC g 44 1 22 LA true := by
  intro args σ0 _ fr σ hI
  unfold wp
  have h52 := p44b g args σ0
  have h51 : ∀ fr σ, bcut g 1 22 LA true 23 (nmB5 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 20) 51 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 52 rfl _ 20 h52 5 51 fr σ
      (bcut_app_lit (n := 4) rfl (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h50 : ∀ fr σ, bcut g 1 22 LA true 23 (nmB4 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 25) 50 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 51 rfl _ 25 h51 5 50 fr σ
      (bcut_app_ll (n := 4) rfl (by simp [LA]) (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h49 : ∀ fr σ, bcut g 1 22 LA true 23 (nmB3 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 30) 49 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 50 rfl _ 30 h50 5 49 fr σ
      (bcut_app_lit (n := 4) rfl (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h48 : ∀ fr σ, bcut g 1 22 LA true 23 (nmB2 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 35) 48 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 49 rfl _ 35 h49 5 48 fr σ
      (bcut_app_ll (n := 4) rfl (by simp [LA]) (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h47 : ∀ fr σ, bcut g 1 22 LA true 23 (nmB1 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 40) 47 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 48 rfl _ 40 h48 5 47 fr σ
      (bcut_app_lit (n := 4) rfl (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h46 : ∀ fr σ, bcut g 1 22 LA true 23 [] args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 45) 46 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 47 rfl _ 45 h47 5 46 fr σ
      (bcut_app_ll (n := 4) rfl (by simp [LA]) (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  exact bodyWP_cut_insert csH_mono body _ _ 46 rfl _ 50 h46 10 44 fr σ (p44a g args σ0 fr σ hI)

end EquivLean.Modernize.Cbstm03a.Java.Cs

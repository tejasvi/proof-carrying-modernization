import EquivLean.Modernize.Cbstm03a.Java.Cs.B54

/-!
# CBSTM03A → Java: `createStatement`, the paths from the cut point 54 to 66 (the address builder)

The virtual cut points 56 … 64 (after `new`/`<init>` and after each `app` call) composed by `bodyWP_cut_insert`.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr zpadStr argText StrOk space)

namespace EquivLean.Modernize.Cbstm03a.Java.Cs

abbrev adB1 (g : G) : JStr := appStr [] 80 (tAddr3 g) (some (JStr.ofString " "))
abbrev adB2 (g : G) : JStr := appStr (adB1 g) 80 (JStr.ofString " ") none
abbrev adB3 (g : G) : JStr := appStr (adB2 g) 80 (tState g) (some (JStr.ofString " "))
abbrev adB4 (g : G) : JStr := appStr (adB3 g) 80 (JStr.ofString " ") none
abbrev adB5 (g : G) : JStr := appStr (adB4 g) 80 (tCountry g) (some (JStr.ofString " "))
abbrev adB6 (g : G) : JStr := appStr (adB5 g) 80 (JStr.ofString " ") none
abbrev adB7 (g : G) : JStr := appStr (adB6 g) 80 (tZip g) (some (JStr.ofString " "))

set_option maxRecDepth 20000 in
theorem s54 (g : G) : CutVC g 54 1 22 LB true := by
  intro args σ0 _ fr σ hI
  unfold wp
  have h64 := p54b g args σ0
  have h63 : ∀ fr σ, bcut g 1 22 LB true 24 (adB7 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 10) 63 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 64 rfl _ 10 h64 5 63 fr σ
      (bcut_app_lit (n := 4) rfl (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h62 : ∀ fr σ, bcut g 1 22 LB true 24 (adB6 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 15) 62 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 63 rfl _ 15 h63 5 62 fr σ
      (bcut_app_ll (n := 4) rfl (by simp [LB]) (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h61 : ∀ fr σ, bcut g 1 22 LB true 24 (adB5 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 20) 61 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 62 rfl _ 20 h62 5 61 fr σ
      (bcut_app_lit (n := 4) rfl (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h60 : ∀ fr σ, bcut g 1 22 LB true 24 (adB4 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 25) 60 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 61 rfl _ 25 h61 5 60 fr σ
      (bcut_app_ll (n := 4) rfl (by simp [LB]) (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h59 : ∀ fr σ, bcut g 1 22 LB true 24 (adB3 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 30) 59 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 60 rfl _ 30 h60 5 59 fr σ
      (bcut_app_lit (n := 4) rfl (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h58 : ∀ fr σ, bcut g 1 22 LB true 24 (adB2 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 35) 58 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 59 rfl _ 35 h59 5 58 fr σ
      (bcut_app_ll (n := 4) rfl (by simp [LB]) (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h57 : ∀ fr σ, bcut g 1 22 LB true 24 (adB1 g) args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 40) 57 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 58 rfl _ 40 h58 5 57 fr σ
      (bcut_app_lit (n := 4) rfl (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  have h56 : ∀ fr σ, bcut g 1 22 LB true 24 [] args σ0 fr σ →
      bodyWP Gen.prog csH body ((inv g).inst args σ0) ((specG g).post args σ0) (5 + 45) 56 fr σ :=
    fun fr σ h => bodyWP_cut_insert csH_mono body _ _ 57 rfl _ 45 h57 5 56 fr σ
      (bcut_app_ll (n := 4) rfl (by simp [LB]) (by decide) (by decide) (by decide) (by decide +kernel) fr σ h)
  exact bodyWP_cut_insert csH_mono body _ _ 56 rfl _ 50 h56 10 54 fr σ (p54a g args σ0 fr σ hI)

end EquivLean.Modernize.Cbstm03a.Java.Cs

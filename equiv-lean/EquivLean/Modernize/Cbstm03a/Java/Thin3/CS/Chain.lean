import EquivLean.Modernize.Cbstm03a.Java.Thin3.CS.J3

/-!
# CBSTM03A → Java, termination of `createStatement`: the paths, from the end back to the entry

`pN`: the termination paths from statement `N` (`WPT (FT N) N`), from the facts at `N`: a computation segment
(`jN`, by `jvc`, up to a virtual cut point, `bodyWP_cutT`), then the calls of `stmt`/`html`/`app` from that point
(the step lemmas), then `p` of the next segment.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

open EquivLean.Modernize.Cbstm03a.Java

/-- The fuel from statement `p`. -/
def FT (p : Nat) : Nat := 4 * (148 - p) + 10

theorem wpt_weaken {n m pc : Nat} {fr : Frame} {σ : State} (h : n ≤ m) (hw : WPT n pc fr σ) :
    bodyWP Gen.prog HT csBody [] (fun _ => True) m pc fr σ :=
  bodyWP_fuelT n m pc fr σ h (by rw [← WPT_eq]; exact hw)

theorem c75 : (BitVec.ofInt 32 75).toInt = 75 := by decide
theorem c80 : (BitVec.ofInt 32 80).toInt = 80 := by decide

set_option hygiene false in
/-- The calls of `html` with a literal argument from the current statement on (`h22`, `hne`, state `σ`, `hJ`). -/
macro "html_lits" : tactic =>
  `(tactic| repeat (refine wpT_html_lit (by rfl) h22 hne (by decide +kernel) hJ ?_; intro σ hJ))

set_option maxRecDepth 20000 in
theorem p147 (_res _ls _lh : Addr) (_hne : _ls ≠ _lh) (fr : Frame) (σ : State) (_hJ : RJ _res _ls _lh σ σ)
    (_h22 : fr.get 22 = some (.ref _res)) (_hK : ∀ p ∈ K138, SLoc σ fr p.1 p.2) : WPT (FT 147) 147 fr σ := by
  rw [WPT_eq]; exact bodyWP_fuelT 2 _ _ _ _ (by decide) (j147 fr σ)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p143 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K138, SLoc σ fr p.1 p.2) : WPT (FT 143) 143 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (8 + FT 145) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 8 143 _ σ
    (j143 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x1, s1, h1a, h1b, h1c⟩ := hK (1, 80) (by decide)
  obtain ⟨x2, s2, h2a, h2b, h2c⟩ := hK (21, 80) (by decide)
  rw [WPT_eq]
  refine wpT_stmt_loc (by rfl) h22 h1a hne (hJ.2.2.2.2 _ _ h1b) (by omega) hJ ?_; intro σ1 hJ1
  refine wpT_stmt_loc (by rfl) h22 h2a hne (hJ1.2.2.2.2 _ _ h2b) (by omega) hJ1 ?_; intro σ2 hJ2
  exact wpt_weaken (by decide) (p147 res ls lh hne fr σ2 (rj_restart hJ2) h22
    (fun p hp => sloc_mono (hK p ((by decide : ∀ q ∈ K138, q ∈ K145) p hp)) hJ2.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p138 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K138, SLoc σ fr p.1 p.2) : WPT (FT 138) 138 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (10 + FT 141) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 10 138 _ σ
    (j138 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x1, s1, h1a, h1b, h1c⟩ := hK (1, 80) (by decide)
  obtain ⟨x2, s2, h2a, h2b, h2c⟩ := hK (21, 80) (by decide)
  rw [WPT_eq]
  refine wpT_stmt_loc (by rfl) h22 h1a hne (hJ.2.2.2.2 _ _ h1b) (by omega) hJ ?_; intro σ1 hJ1
  refine wpT_stmt_loc (by rfl) h22 h2a hne (hJ1.2.2.2.2 _ _ h2b) (by omega) hJ1 ?_; intro σ2 hJ2
  exact wpt_weaken (by decide) (p143 res ls lh hne fr σ2 (rj_restart hJ2) h22
    (fun p hp => sloc_mono (hK p ((by decide : ∀ q ∈ K138, q ∈ K136) p hp)) hJ2.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p134 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K134, SLoc σ fr p.1 p.2) : WPT (FT 134) 134 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (8 + FT 136) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 8 134 _ σ
    (j134 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x1, s1, h1a, h1b, h1c⟩ := hK (1, 80) (by decide)
  obtain ⟨x2, s2, h2a, h2b, h2c⟩ := hK (21, 80) (by decide)
  rw [WPT_eq]
  refine wpT_stmt_loc (by rfl) h22 h1a hne (hJ.2.2.2.2 _ _ h1b) (by omega) hJ ?_; intro σ1 hJ1
  refine wpT_stmt_loc (by rfl) h22 h2a hne (hJ1.2.2.2.2 _ _ h2b) (by omega) hJ1 ?_; intro σ2 hJ2
  exact wpt_weaken (by decide) (p138 res ls lh hne fr σ2 (rj_restart hJ2) h22
    (fun p hp => sloc_mono (hK p ((by decide : ∀ q ∈ K138, q ∈ K136) p hp)) hJ2.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p131 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K131, SLoc σ fr p.1 p.2) : WPT (FT 131) 131 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (8 + FT 133) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 8 131 _ σ
    (j131 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x1, s1, h1a, h1b, h1c⟩ := hK (2, 80) (by decide)
  rw [WPT_eq]
  refine wpT_stmt_loc (by rfl) h22 h1a hne (hJ.2.2.2.2 _ _ h1b) (by omega) hJ ?_; intro σ1 hJ1
  exact wpt_weaken (by decide) (p134 res ls lh hne fr σ1 (rj_restart hJ1) h22
    (fun p hp => sloc_mono (hK p ((by decide : ∀ q ∈ K134, q ∈ K133) p hp)) hJ1.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p128 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K123, SLoc σ fr p.1 p.2) : WPT (FT 128) 128 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (8 + FT 130) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 8 128 _ σ
    (j128 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x1, s1, h1a, h1b, h1c⟩ := hK (7, 80) (by decide)
  rw [WPT_eq]
  refine wpT_stmt_loc (by rfl) h22 h1a hne (hJ.2.2.2.2 _ _ h1b) (by omega) hJ ?_; intro σ1 hJ1
  exact wpt_weaken (by decide) (p131 res ls lh hne fr σ1 (rj_restart hJ1) h22
    (fun p hp => sloc_mono (hK p ((by decide : ∀ q ∈ K131, q ∈ K130) p hp)) hJ1.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p123 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K123, SLoc σ fr p.1 p.2) : WPT (FT 123) 123 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (10 + FT 126) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 10 123 _ σ
    (j123 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x1, s1, h1a, h1b, h1c⟩ := hK (7, 80) (by decide)
  obtain ⟨x2, s2, h2a, h2b, h2c⟩ := hK (21, 80) (by decide)
  rw [WPT_eq]
  refine wpT_stmt_loc (by rfl) h22 h1a hne (hJ.2.2.2.2 _ _ h1b) (by omega) hJ ?_; intro σ1 hJ1
  refine wpT_stmt_loc (by rfl) h22 h2a hne (hJ1.2.2.2.2 _ _ h2b) (by omega) hJ1 ?_; intro σ2 hJ2
  exact wpt_weaken (by decide) (p128 res ls lh hne fr σ2 (rj_restart hJ2) h22
    (fun p hp => sloc_mono (hK p ((by decide : ∀ q ∈ K123, q ∈ K126) p hp)) hJ2.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p118 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K118, SLoc σ fr p.1 p.2) : WPT (FT 118) 118 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (8 + FT 120) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 8 118 _ σ
    (j118 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x1, s1, h1a, h1b, h1c⟩ := hK (7, 80) (by decide)
  obtain ⟨x2, s2, h2a, h2b, h2c⟩ := hK (16, 80) (by decide)
  obtain ⟨x3, s3, h3a, h3b, h3c⟩ := hK (21, 80) (by decide)
  rw [WPT_eq]
  refine wpT_stmt_loc (by rfl) h22 h1a hne (hJ.2.2.2.2 _ _ h1b) (by omega) hJ ?_; intro σ1 hJ1
  refine wpT_stmt_loc (by rfl) h22 h2a hne (hJ1.2.2.2.2 _ _ h2b) (by omega) hJ1 ?_; intro σ2 hJ2
  refine wpT_stmt_loc (by rfl) h22 h3a hne (hJ2.2.2.2.2 _ _ h3b) (by omega) hJ2 ?_; intro σ3 hJ3
  exact wpt_weaken (by decide) (p123 res ls lh hne fr σ3 (rj_restart hJ3) h22
    (fun p hp => sloc_mono (hK p ((by decide : ∀ q ∈ K123, q ∈ K120) p hp)) hJ3.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p115 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K115, SLoc σ fr p.1 p.2) : WPT (FT 115) 115 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (8 + FT 117) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 8 115 _ σ
    (j115 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x1, s1, h1a, h1b, h1c⟩ := hK (6, 80) (by decide)
  rw [WPT_eq]
  refine wpT_stmt_loc (by rfl) h22 h1a hne (hJ.2.2.2.2 _ _ h1b) (by omega) hJ ?_; intro σ1 hJ1
  exact wpt_weaken (by decide) (p118 res ls lh hne fr σ1 (rj_restart hJ1) h22
    (fun p hp => sloc_mono (hK p ((by decide : ∀ q ∈ K118, q ∈ K117) p hp)) hJ1.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p111 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) : WPT (FT 111) 111 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (10 + FT 114) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 10 111 _ σ
    (j111 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x1, s1, h1a, h1b, h1c⟩ := hK (3, 80) (by decide)
  rw [WPT_eq]
  refine wpT_stmt_loc (by rfl) h22 h1a hne (hJ.2.2.2.2 _ _ h1b) (by omega) hJ ?_; intro σ1 hJ1
  exact wpt_weaken (by decide) (p115 res ls lh hne fr σ1 (rj_restart hJ1) h22
    (fun p hp => sloc_mono (hK p ((by decide : ∀ q ∈ K115, q ∈ K114) p hp)) hJ1.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p91 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) : WPT (FT 91) 91 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (4 + FT 92) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 4 91 _ σ
    (j91 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x13, s13, h13a, h13b, h13c⟩ := hK (13, 100) (by decide)
  rw [WPT_eq]
  refine wpT_html_loc (by rfl) h22 h13a hne (hJ.2.2.2.2 _ _ h13b) (by omega) hJ ?_; intro σ hJ
  html_lits
  exact wpt_weaken (by decide) (p111 res ls lh hne fr σ (rj_restart hJ) h22
    (fun p hp => sloc_mono (hK p (List.mem_cons_of_mem _ hp)) hJ.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p89 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) : WPT (FT 89) 89 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (4 + FT 90) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 4 89 _ σ
    (j89 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x13, s13, h13a, h13b, h13c⟩ := hK (13, 100) (by decide)
  rw [WPT_eq]
  refine wpT_html_loc (by rfl) h22 h13a hne (hJ.2.2.2.2 _ _ h13b) (by omega) hJ ?_; intro σ hJ
  html_lits
  exact wpt_weaken (by decide) (p91 res ls lh hne fr σ (rj_restart hJ) h22
    (fun p hp => sloc_mono (hK p (List.mem_cons_of_mem _ hp)) hJ.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p87 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) : WPT (FT 87) 87 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (4 + FT 88) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 4 87 _ σ
    (j87 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x13, s13, h13a, h13b, h13c⟩ := hK (13, 100) (by decide)
  rw [WPT_eq]
  refine wpT_html_loc (by rfl) h22 h13a hne (hJ.2.2.2.2 _ _ h13b) (by omega) hJ ?_; intro σ hJ
  html_lits
  exact wpt_weaken (by decide) (p89 res ls lh hne fr σ (rj_restart hJ) h22
    (fun p hp => sloc_mono (hK p (List.mem_cons_of_mem _ hp)) hJ.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p76 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) : WPT (FT 76) 76 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (4 + FT 77) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 4 76 _ σ
    (j76 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x13, s13, h13a, h13b, h13c⟩ := hK (13, 100) (by decide)
  rw [WPT_eq]
  refine wpT_html_loc (by rfl) h22 h13a hne (hJ.2.2.2.2 _ _ h13b) (by omega) hJ ?_; intro σ hJ
  html_lits
  exact wpt_weaken (by decide) (p87 res ls lh hne fr σ (rj_restart hJ) h22
    (fun p hp => sloc_mono (hK p (List.mem_cons_of_mem _ hp)) hJ.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p74 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) : WPT (FT 74) 74 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (4 + FT 75) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 4 74 _ σ
    (j74 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x13, s13, h13a, h13b, h13c⟩ := hK (13, 100) (by decide)
  rw [WPT_eq]
  refine wpT_html_loc (by rfl) h22 h13a hne (hJ.2.2.2.2 _ _ h13b) (by omega) hJ ?_; intro σ hJ
  html_lits
  exact wpt_weaken (by decide) (p76 res ls lh hne fr σ (rj_restart hJ) h22
    (fun p hp => sloc_mono (hK p (List.mem_cons_of_mem _ hp)) hJ.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p72 (res ls lh : Addr) (hne : ls ≠ lh) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ KE, SLoc σ fr p.1 p.2) : WPT (FT 72) 72 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (4 + FT 73) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 4 72 _ σ
    (j72 res ls lh fr σ fs xs xs2 m m2 hres hls hlh h22 hK hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x13, s13, h13a, h13b, h13c⟩ := hK (13, 100) (by decide)
  rw [WPT_eq]
  refine wpT_html_loc (by rfl) h22 h13a hne (hJ.2.2.2.2 _ _ h13b) (by omega) hJ ?_; intro σ hJ
  html_lits
  exact wpt_weaken (by decide) (p74 res ls lh hne fr σ (rj_restart hJ) h22
    (fun p hp => sloc_mono (hK p (List.mem_cons_of_mem _ hp)) hJ.2.2.2.2))

end EquivLean.Modernize.Cbstm03a.Java.Thin3

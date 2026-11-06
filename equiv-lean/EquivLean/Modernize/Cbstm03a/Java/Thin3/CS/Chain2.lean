import EquivLean.Modernize.Cbstm03a.Java.Thin3.CS.Chain

/-!
# CBSTM03A → Java, termination of `createStatement`: the paths from the entry to the first paragraph line

The phases carrying the account text `a` (for `currBal`) and the builders: statements 64 (the account fields, the
first paragraph), 52 and 44 (the name and address builders, `app` on each), 30 and 16 (the first `html`/`stmt`
lines), 13 and 8 (the substrings), and the entry.
-/

open EquivLean.Cobol.Rec Jimple EquivLean.Jimple
open EquivLean.Modernize.Cbstm03b.Java (Grows Keeps fixStr argText StrOk space fixStr_length)

namespace EquivLean.Modernize.Cbstm03a.Java.Thin3

open EquivLean.Modernize.Cbstm03a.Java

/-- A segment up to a virtual cut point `pb` and the paths from `pb`, as `WPT` (no unfolding of a concrete goal). -/
theorem wpt_cut {n nJ m pc pb : Nat} {fr : Frame} {σ : State} {A : Frame → State → Prop}
    (hseg : bodyWP Gen.prog HT csBody [(pb, A)] (fun _ => True) nJ pc fr σ)
    (hA : ∀ fr σ, A fr σ → WPT m pb fr σ) (hle : nJ + m ≤ n) : WPT n pc fr σ := by
  rw [WPT_eq]
  exact bodyWP_fuelT (nJ + m) n pc fr σ hle
    (bodyWP_cutT (by rfl) (fun fr σ h => by rw [← WPT_eq]; exact hA fr σ h) nJ pc fr σ hseg)

theorem wpt_elim {n pc : Nat} {fr : Frame} {σ : State} (h : WPT n pc fr σ) :
    bodyWP Gen.prog HT csBody [] (fun _ => True) n pc fr σ := by
  rw [WPT_eq] at h; exact h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p64 (res ls lh : Addr) (hne : ls ≠ lh) (a : JStr) (ha : 24 ≤ a.length) (fr : Frame) (σ : State)
    (hJ : RJ res ls lh σ σ) (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K56, SLoc σ fr p.1 p.2)
    (hbal : BalA a fr) (hb : Bld 24 80 fr σ) : WPT (FT 64) 64 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  have hbv : -9223372036854775808 < (BitVec.ofInt 64 (zonedVal (List.drop 12 (List.take 24 a)))).toInt :=
    zoned12_gt (by simp only [List.length_drop, List.length_take]; omega)
  rw [WPT_eq]
  refine bodyWP_fuelT (28 + FT 71) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 28 64 _ σ
    (j5 res ls lh a fr σ fs xs xs2 m m2 hres hls hlh h22 hK hbal hbv hb hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, -⟩ := hV
  obtain ⟨x13, s13, h13a, h13b, h13c⟩ := hK (13, 100) (by decide)
  rw [WPT_eq]
  refine wpT_html_loc (by rfl) h22 h13a hne (hJ.2.2.2.2 _ _ h13b) (by omega) hJ ?_; intro σ hJ
  exact wpt_weaken (by decide) (p72 res ls lh hne fr σ (rj_restart hJ) h22
    (fun p hp => sloc_mono (hK p (List.mem_cons_of_mem _ hp)) hJ.2.2.2.2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p52 (res ls lh : Addr) (hne : ls ≠ lh) (a : JStr) (ha : 24 ≤ a.length) (fr : Frame) (σ : State)
    (hJ : RJ res ls lh σ σ) (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K6, SLoc σ fr p.1 p.2)
    (hbal : BalA a fr) (hb : Bld 23 75 fr σ) : WPT (FT 52) 52 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (16 + FT 56) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 16 52 _ σ
    (j4 res ls lh a fr σ fs xs xs2 m m2 hres hls hlh h22 hK hbal hb hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, hbal, d, b, hd, hb, hbl⟩ := hV
  obtain ⟨x8, s8, h8a, h8b, h8c⟩ := hK (8, 50) (by decide)
  obtain ⟨x9, s9, h9a, h9b, h9c⟩ := hK (9, 2) (by decide)
  obtain ⟨x10, s10, h10a, h10b, h10c⟩ := hK (10, 3) (by decide)
  obtain ⟨x11, s11, h11a, h11b, h11c⟩ := hK (11, 10) (by decide)
  rw [WPT_eq]
  refine wpT_app_loc_lit (by rfl) hd h8a hJ hb (by rw [c80]; decide) (by rw [c80]; omega)
    (hJ.2.2.2.2 _ _ h8b) (by omega) (by decide +kernel) ?_
  intro σ1 b1 hJ1 hb1 hbl1
  refine wpT_app_lit_null (by rfl) hd hJ1 hb1 (by rw [c80]; decide) hbl1 (by decide +kernel) ?_
  intro σ2 b2 hJ2 hb2 hbl2
  refine wpT_app_loc_lit (by rfl) hd h9a hJ2 hb2 (by rw [c80]; decide) hbl2 (hJ2.2.2.2.2 _ _ h9b) (by omega)
    (by decide +kernel) ?_
  intro σ3 b3 hJ3 hb3 hbl3
  refine wpT_app_lit_null (by rfl) hd hJ3 hb3 (by rw [c80]; decide) hbl3 (by decide +kernel) ?_
  intro σ4 b4 hJ4 hb4 hbl4
  refine wpT_app_loc_lit (by rfl) hd h10a hJ4 hb4 (by rw [c80]; decide) hbl4 (hJ4.2.2.2.2 _ _ h10b) (by omega)
    (by decide +kernel) ?_
  intro σ5 b5 hJ5 hb5 hbl5
  refine wpT_app_lit_null (by rfl) hd hJ5 hb5 (by rw [c80]; decide) hbl5 (by decide +kernel) ?_
  intro σ6 b6 hJ6 hb6 hbl6
  refine wpT_app_loc_lit (by rfl) hd h11a hJ6 hb6 (by rw [c80]; decide) hbl6 (hJ6.2.2.2.2 _ _ h11b) (by omega)
    (by decide +kernel) ?_
  intro σ7 b7 hJ7 hb7 hbl7
  refine wpT_app_lit_null (by rfl) hd hJ7 hb7 (by rw [c80]; decide) hbl7 (by decide +kernel) ?_
  intro σ8 b8 hJ8 hb8 hbl8
  exact wpt_weaken (by decide) (p64 res ls lh hne a ha fr σ8 (rj_restart hJ8) h22
    (fun p hp => sloc_mono (hK p hp) hJ8.2.2.2.2) hbal ⟨d, b8, hd, hb8, by rw [c80] at hbl8; simpa using hbl8⟩)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p44 (res ls lh : Addr) (hne : ls ≠ lh) (a : JStr) (ha : 24 ≤ a.length) (fr : Frame) (σ : State)
    (hJ : RJ res ls lh σ σ) (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K16, SLoc σ fr p.1 p.2)
    (hbal : BalA a fr) : WPT (FT 44) 44 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (8 + FT 46) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 8 44 _ σ
    (j3 res ls lh a fr σ fs xs xs2 m m2 hres hls hlh h22 hK hbal hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, hbal, d, b, hd, hb, hbl⟩ := hV
  obtain ⟨x3, s3, h3a, h3b, h3c⟩ := hK (3, 25) (by decide)
  obtain ⟨x4, s4, h4a, h4b, h4c⟩ := hK (4, 25) (by decide)
  obtain ⟨x5, s5, h5a, h5b, h5c⟩ := hK (5, 25) (by decide)
  rw [WPT_eq]
  refine wpT_app_loc_lit (by rfl) hd h3a hJ hb (by rw [c75]; decide) (by rw [c75]; omega)
    (hJ.2.2.2.2 _ _ h3b) (by omega) (by decide +kernel) ?_
  intro σ1 b1 hJ1 hb1 hbl1
  refine wpT_app_lit_null (by rfl) hd hJ1 hb1 (by rw [c75]; decide) hbl1 (by decide +kernel) ?_
  intro σ2 b2 hJ2 hb2 hbl2
  refine wpT_app_loc_lit (by rfl) hd h4a hJ2 hb2 (by rw [c75]; decide) hbl2 (hJ2.2.2.2.2 _ _ h4b) (by omega)
    (by decide +kernel) ?_
  intro σ3 b3 hJ3 hb3 hbl3
  refine wpT_app_lit_null (by rfl) hd hJ3 hb3 (by rw [c75]; decide) hbl3 (by decide +kernel) ?_
  intro σ4 b4 hJ4 hb4 hbl4
  refine wpT_app_loc_lit (by rfl) hd h5a hJ4 hb4 (by rw [c75]; decide) hbl4 (hJ4.2.2.2.2 _ _ h5b) (by omega)
    (by decide +kernel) ?_
  intro σ5 b5 hJ5 hb5 hbl5
  refine wpT_app_lit_null (by rfl) hd hJ5 hb5 (by rw [c75]; decide) hbl5 (by decide +kernel) ?_
  intro σ6 b6 hJ6 hb6 hbl6
  exact wpt_weaken (by decide) (p52 res ls lh hne a ha fr σ6 (rj_restart hJ6) h22
    (fun p hp => sloc_mono (hK p ((by decide : ∀ q ∈ K6, q ∈ K16) p hp)) hJ6.2.2.2.2) hbal
    ⟨d, b6, hd, hb6, by rw [c75] at hbl6; simpa using hbl6⟩)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p30 (res ls lh : Addr) (hne : ls ≠ lh) (a : JStr) (ha : 24 ≤ a.length) (fr : Frame) (σ : State)
    (hJ : RJ res ls lh σ σ) (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K16, SLoc σ fr p.1 p.2)
    (hbal : BalA a fr) : WPT (FT 30) 30 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (8 + FT 32) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 8 30 _ σ
    (j2 res ls lh a fr σ fs xs xs2 m m2 hres hls hlh h22 hK hbal hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, hbal⟩ := hV
  obtain ⟨x2, s2, h2a, h2b, h2c⟩ := hK (2, 100) (by decide)
  rw [WPT_eq]
  refine wpT_html_loc (by rfl) h22 h2a hne (hJ.2.2.2.2 _ _ h2b) (by omega) hJ ?_; intro σ hJ
  html_lits
  exact wpt_weaken (by decide) (p44 res ls lh hne a ha fr σ (rj_restart hJ) h22
    (fun p hp => sloc_mono (hK p (List.mem_cons_of_mem _ hp)) hJ.2.2.2.2) hbal)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p16 (res ls lh : Addr) (hne : ls ≠ lh) (a : JStr) (ha : 24 ≤ a.length) (fr : Frame) (σ : State)
    (hJ : RJ res ls lh σ σ) (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K16, SLoc σ fr p.1 p.2)
    (hbal : BalA a fr) : WPT (FT 16) 16 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (10 + FT 19) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 10 16 _ σ
    (j1c res ls lh a fr σ fs xs xs2 m m2 hres hls hlh h22 hK hbal hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, hbal⟩ := hV
  obtain ⟨x2, s2, h2a, h2b, h2c⟩ := hK (2, 80) (by decide)
  rw [WPT_eq]
  refine wpT_stmt_loc (by rfl) h22 h2a hne (hJ.2.2.2.2 _ _ h2b) (by omega) hJ ?_; intro σ hJ
  html_lits
  exact wpt_weaken (by decide) (p30 res ls lh hne a ha fr σ (rj_restart hJ) h22
    (fun p hp => sloc_mono (hK p (List.mem_cons_of_mem _ hp)) hJ.2.2.2.2) hbal)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p13 (res ls lh xa : Addr) (hne : ls ≠ lh) (a : JStr) (ha : 24 ≤ a.length) (ha' : a.length < 2147483648)
    (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ) (h22 : fr.get 22 = some (.ref res))
    (hK : ∀ p ∈ K13, SLoc σ fr p.1 p.2) (h2 : fr.get 2 = some (.ref xa)) (hxa : σ.heap xa = some (.str a)) :
    WPT (FT 13) 13 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (10 + FT 16) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 10 13 _ σ
    (j1b res ls lh xa a fr σ fs xs xs2 m m2 hres hls hlh h22 hK h2 hxa ha ha' hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, hbal⟩ := hV
  exact p16 res ls lh hne a ha fr σ' hJ h22 hK hbal

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem p8 (res ls lh xc xa : Addr) (hne : ls ≠ lh) (c a : JStr) (hc : 332 ≤ c.length) (ha : 24 ≤ a.length)
    (ha' : a.length < 2147483648) (fr : Frame) (σ : State) (hJ : RJ res ls lh σ σ)
    (h22 : fr.get 22 = some (.ref res)) (hK : ∀ p ∈ K8, SLoc σ fr p.1 p.2) (h1 : fr.get 1 = some (.ref xc))
    (h2 : fr.get 2 = some (.ref xa)) (hxc : σ.heap xc = some (.str c)) (hxa : σ.heap xa = some (.str a)) :
    WPT (FT 8) 8 fr σ := by
  have hJ0 := hJ
  obtain ⟨⟨fs, hres, -, -⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, -⟩ := hJ
  rw [WPT_eq]
  refine bodyWP_fuelT (10 + FT 13) _ _ _ _ (by decide) ?_
  refine bodyWP_cutT (by rfl) (fun fr σ' hV => ?_) 10 8 _ σ
    (j1a2 res ls lh xc xa c a fr σ fs xs xs2 m m2 hres hls hlh h22 hK h1 h2 hxc hxa hc hini)
  rw [← WPT_eq]
  have hJ := rj_va hJ0 hV
  obtain ⟨h22, -, -, -, -, hK, h2, hxa⟩ := hV
  exact p13 res ls lh xa hne a ha ha' fr σ' hJ h22 hK h2 hxa

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The entry**: the termination paths of `createStatement` from its precondition. -/
theorem p0 (args : List Value) (σ0 : State) (hpre : createStatementSpec.pre args σ0) :
    WPT (FT 0) 0 (Frame.init true args) σ0 := by
  obtain ⟨res, ld, ls, lh, disp, st, ht, ab, cv, av, c, a, rfl, hR, ⟨xc, rfl, hxc⟩, ⟨xa, rfl, hxa⟩, hc, hc', ha,
    ha', hini⟩ := hpre
  obtain ⟨fs, hres, -, hfs, hfh, -, -, -, hne, -, ⟨xs, m, hls, -⟩, ⟨xs2, m2, hlh, -⟩⟩ := hR
  have hJ0 : RJ res ls lh σ0 σ0 := ⟨⟨fs, hres, hfs, hfh⟩, ⟨xs, m, hls⟩, ⟨xs2, m2, hlh⟩, hini, fun _ _ h => h⟩
  -- (the frame as a variable: `bodyWP` at a concrete frame and fuel unfolds by `whnf` in elaboration checks)
  generalize hfr : Frame.init true [.ref res, .ref xc, .ref xa] = fr0
  exact wpt_cut (m := FT 8) (j1a res ls lh xc xa c a σ0 fs xs xs2 m m2 hres hls hlh hxc hxa hc fr0 hfr hini)
    (fun fr σ' hV => by
      have hJ := rj_va hJ0 hV
      obtain ⟨h22, -, -, -, -, hK, h1, h2, hxc', hxa'⟩ := hV
      exact p8 res ls lh xc xa hne c a hc ha ha' fr σ' hJ h22 hK h1 h2 hxc' hxa')
    (by decide)

end EquivLean.Modernize.Cbstm03a.Java.Thin3
